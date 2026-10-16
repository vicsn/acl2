"""Call graph of the constraint-generating circuit functions, written into the canvas.

Nodes are the rows of aleovm_circuit_function_formalisation_status.csv. Edges reuse the parser
and the candidate rules of aleovm_circuit_functions_scan.py, which resolves calls by name.
A call becomes an edge only when its callee is determined:

- a typed path (`Group::ternary`, `Self::f`, `A::f` over the network impls), or a trait path
  (`Ternary::ternary(c, &first.x, ..)`) whose arguments are fields of a declared type;
- a method on `self`, or on `self.f` / `other.f` where the struct declares the type of `f`;
- an operator inside a types/ crate that resolves to the function's own type (or Boolean for
  `& | ^`);
- a name with a single constraint-generating implementation.

Every other call goes to a dispatch node named after the call, which lists the candidate
implementations. An `X_assign` function is never an edge source to its own `X` operator: the
operator calls `X_assign`, and the arithmetic inside `X_assign` acts on linear combinations.
The resolved graph must be acyclic; the script exits with status 1 and prints the cycle if not.

Usage: python3 aleovm_circuit_call_graph.py <snarkVM>/circuit [status.csv] [canvas.tsx]
"""

import csv
import json
import os
import re
import sys
from collections import defaultdict

import aleovm_circuit_functions_scan as S

HERE = os.path.dirname(os.path.abspath(__file__))
STATUS_CSV = os.path.join(HERE, "aleovm_circuit_function_formalisation_status.csv")
CANVAS = os.path.join(HERE, "aleovm_circuit_call_graph.canvas.tsx")
BEGIN = "// BEGIN GENERATED DATA"
END = "// END GENERATED DATA"
FLAG_COLS = ["FUN-SPEC", "R1CS-SPEC", "PFCS-SPEC", "R1CS-SAMPLES", "R1CS-SOUND", "R1CS-COMPLETE"]
WRAPPERS = {"Option", "Vec", "Box", "IndexMap", "Rc", "Arc", "RefCell", "PhantomData", "HashMap", "BTreeMap"}


def rust_files(root):
    for dp, dn, fn in os.walk(root):
        dn[:] = [d for d in dn if d not in ("tests", "benches", "target", "examples")]
        for f in fn:
            if f.endswith(".rs") and f != "tests.rs" and not f.endswith("_tests.rs"):
                yield os.path.join(dp, f)


def scan(root):
    defs, fields = [], defaultdict(dict)
    for p in rust_files(root):
        raw = S.strip_comments_and_strings(open(p, encoding="utf-8").read())
        S.scan_items(S.remove_macro_bodies(S.remove_test_items(raw)), os.path.relpath(p, root), defs)
        for m in re.finditer(r"\bstruct\s+(\w+)\s*(?:<[^{;()]*?>)?\s*(?:where[^{;]*)?\{([^{}]*)\}", raw):
            for fm in re.finditer(r"(?:pub(?:\([^)]*\))?\s+)?(\w+)\s*:\s*([A-Za-z_]\w*)", m.group(2)):
                if fm.group(2) not in WRAPPERS:
                    fields[m.group(1)][fm.group(1)] = fm.group(2)
        for m in re.finditer(r"\bstruct\s+(\w+)\s*(?:<[^{;()]*?>)?\s*\(([^;]*?)\)\s*;", raw):
            for i, part in enumerate(re.split(r",(?![^<]*>)", m.group(2))):
                tm = re.match(r"\s*(?:pub(?:\([^)]*\))?\s+)?([A-Za-z_]\w*)", part)
                if tm and tm.group(1) not in WRAPPERS:
                    fields[m.group(1)][str(i)] = tm.group(1)
    for d in defs:
        d["direct"], d["paths"], d["methods"], d["self_methods"], d["free"], d["ops"] = S.analyse_body(d["body"])
        d["crate"] = S.crate_of(d["path"])
    return defs, fields


def key(d):
    return (d["crate"], d["type"], d["trait"], d["name"])


def build(root, status_csv):
    defs, fields = scan(root)
    by_name, by_type_name = defaultdict(list), defaultdict(list)
    for d in defs:
        by_name[d["name"]].append(d)
        by_type_name[(d["type"], d["name"])].append(d)
        if d["trait"]:
            by_type_name[(d["trait"], d["name"])].append(d)

    def eligible(d):
        if d["trait"] in S.NON_GENERATING_TRAITS or d["name"] in S.NON_GENERATING_NAMES:
            return False
        if d["type"] == "LinearCombination":
            return False
        return not (d["crate"] == "environment" and d["type"] in S.ENV_INFRA_TYPES)

    # Same candidate rules as the fixpoint in aleovm_circuit_functions_scan.main.
    def candidates(d):
        out = []
        for q, name in d["paths"]:
            if (name in S.PRIMITIVES and q[0].isupper()) or name in S.NON_GENERATING_NAMES:
                continue
            if q == "Self" or (q, name) == ("From", "from"):
                c = by_type_name.get((d["type"], name), []) or (by_name.get(name, []) if q == "Self" else [])
            elif (q, name) in by_type_name:
                c = by_type_name[(q, name)]
            elif q[0].isupper() and len(q) > 1 and not re.fullmatch(r"[A-Z]", q):
                c = []
            else:
                c = by_name.get(name, [])
            out.append((f"{q}::{name}", c))
        own_or_any = lambda n: by_type_name.get((d["type"], n)) or by_name.get(n, [])
        for n, c in ([(n, by_name.get(n, [])) for n in d["methods"] + d["free"]] +
                     [(n, own_or_any(n)) for n in d["self_methods"]]):
            if n not in S.NON_GENERATING_NAMES:
                out.append((n, c))
        for op in (d["ops"] if d["crate"] != "environment" else []):
            names = S.OPERATOR_METHODS[op]
            own = [c for n in names for c in by_type_name.get((d["type"], n), [])]
            if op.rstrip("=") in ("&", "|", "^"):
                own += [c for n in names for c in by_type_name.get(("Boolean", n), [])]
            c = own or ([] if d["crate"].startswith("types/") else [c for n in names for c in by_name.get(n, [])])
            out.append(("op " + op.replace("unary", "unary "), c))
        return out

    for d in defs:
        if d["crate"] == "environment" and d["trait"] == "Environment" and d["name"] in S.PRIMITIVES:
            d["direct"] = d["direct"] or ["primitive"]
        elif not eligible(d):
            d["direct"] = []
    gen = {id(d): bool(d["direct"]) for d in defs}
    via = {id(d): set() for d in defs}
    changed = True
    while changed:
        changed = False
        for d in defs:
            if (gen[id(d)] and via[id(d)]) or not eligible(d):
                continue
            reasons = {r for r, c in candidates(d) if any(gen[id(x)] for x in c if x is not d)}
            if reasons - via[id(d)]:
                via[id(d)] |= reasons
                gen[id(d)] = True
                changed = True

    with open(status_csv, newline="") as f:
        status = {(r["crate"], r["type"], r["trait"], r["function"]): r for r in csv.DictReader(f)}
    scanned = {key(d) for d in defs if gen[id(d)]}
    missing = sorted(k for k in status if k not in scanned)
    if missing:
        print("status rows the scan does not find as constraint-generating:", missing)

    edges, disp = defaultdict(set), {}
    for d in defs:
        if not gen[id(d)] or key(d) not in status:
            continue
        body = S.CLOSURE_RE.sub(" ", d["body"])
        methods = set(d["methods"]) | set(d["self_methods"])
        for r, c in candidates(d):
            if r not in via[id(d)]:
                continue
            ks = sorted({key(x) for x in c if x is not d and gen[id(x)] and key(x) in status} - {key(d)})
            if not ks:
                continue
            if "::" in r:
                q, name = r.split("::")
                typed = [k for k in ks if k[1] == q]
                if q == "Self" or len(ks) == 1 or re.fullmatch(r"[A-Z]", q):
                    hit = ks
                elif typed:
                    hit = typed
                else:
                    hit = set()
                    for m in re.finditer(r"\b%s\s*::\s*%s\s*\(([^;]*?)\)\s*[;,)]" % (q, name), body):
                        for fm in re.finditer(r"\b\w+\.(\w+)\b(?!\s*\()", m.group(1)):
                            ty = fields.get(d["type"], {}).get(fm.group(1))
                            hit |= {k for k in ks if ty and k[1] == ty}
                    hit = sorted(hit)
                if hit:
                    edges[key(d)].update(hit)
                else:
                    disp[(key(d), r)] = ks
            elif len(ks) == 1:
                edges[key(d)].add(ks[0])
            elif r.startswith("op "):
                own = [k for k in ks if k[1] in (d["type"], "Boolean")]
                if d["crate"].startswith("types/") and own:
                    edges[key(d)].update(own)
                else:
                    disp[(key(d), r)] = ks
            else:
                unresolved = r not in methods
                if r in methods:
                    for m in re.finditer(r"([\w.()&]+?)\s*\.\s*%s\s*(?:::\s*<[^;{}]*?>\s*)?\(" % re.escape(r), body):
                        mm = re.fullmatch(r"(self|other)(?:\.(\w+))?", m.group(1).lstrip("(&").rstrip(")"))
                        ty = None
                        if mm and mm.group(2) is None:
                            ty = d["type"] if mm.group(1) == "self" or d["trait"] else None
                        elif mm:
                            ty = fields.get(d["type"], {}).get(mm.group(2))
                        if ty == "Self":
                            ty = d["type"]
                        hit = [k for k in ks if ty and ty in (k[1], k[2])]
                        if hit:
                            edges[key(d)].update(hit)
                        else:
                            unresolved = True
                if unresolved:
                    disp[(key(d), r)] = ks
    for s in list(edges):
        for t in list(edges[s]):
            if s[1] == t[1] and s[3] == t[3] + "_assign" and s in edges.get(t, ()):
                edges[s].discard(t)
    return status, edges, disp


def find_cycle(nodes, edges):
    color, stack = {}, []

    def dfs(v):
        color[v] = 1
        stack.append(v)
        for w in sorted(edges.get(v, ())):
            if color.get(w) == 1:
                return stack[stack.index(w):] + [w]
            if w not in color:
                c = dfs(w)
                if c:
                    return c
        stack.pop()
        color[v] = 2
        return None

    sys.setrecursionlimit(10000)
    for v in nodes:
        if v not in color:
            c = dfs(v)
            if c:
                return c
    return None


def node_row(k, r):
    flags = "".join("x" if r.get(c) == "excluded" else (r.get(c) or "0") for c in FLAG_COLS)
    loc = r["file"].replace("circuit/", "", 1) + ":" + r["line"]
    return [k[0], k[1], k[2], k[3], flags, r.get("R1CS-SOUND-IF", ""), r.get("R1CS-COMPLETE-IF", ""), loc]


def render(status, edges, disp):
    nodes = sorted(status)
    ids = {k: i for i, k in enumerate(nodes)}
    names = sorted({r for _, r in disp})
    did = {r: i for i, r in enumerate(names)}
    impls = defaultdict(set)
    for (_, r), ks in disp.items():
        impls[r].update(ids[k] for k in ks)
    dump = lambda x: json.dumps(x, ensure_ascii=False, separators=(",", ":"))
    lines = [BEGIN + " by aleovm_circuit_call_graph.py; do not edit by hand.", "const DATA: Raw = {", "  n: ["]
    lines += [f"    {dump(node_row(k, status[k]))}," for k in nodes]
    lines += ["  ],", "  e: ["]
    for s in nodes:
        if edges.get(s):
            lines.append("    " + ",".join(dump([ids[s], ids[t]]) for t in sorted(edges[s], key=ids.get)) + ",")
    lines += ["  ],", "  d: ["]
    lines += [f"    {dump([r, sorted(impls[r])])}," for r in names]
    lines += ["  ],", "  de: ["]
    by_caller = defaultdict(list)
    for (s, r) in disp:
        by_caller[ids[s]].append(did[r])
    for s in sorted(by_caller):
        lines.append("    " + ",".join(dump([s, j]) for j in sorted(by_caller[s])) + ",")
    lines += ["  ],", "};", END]
    return "\n".join(lines)


def main(root, status_csv=STATUS_CSV, canvas=CANVAS):
    status, edges, disp = build(root, status_csv)
    cycle = find_cycle(sorted(status), edges)
    if cycle:
        print("resolved call graph has a cycle:", " -> ".join(f"{k[1]}::{k[3]}" for k in cycle))
        sys.exit(1)
    text = open(canvas, encoding="utf-8").read()
    a, b = text.index(BEGIN), text.index(END) + len(END)
    with open(canvas, "w", encoding="utf-8") as f:
        f.write(text[:a] + render(status, edges, disp) + text[b:])
    print(f"{len(status)} functions, {sum(len(v) for v in edges.values())} resolved calls, "
          f"{len(disp)} name-only calls to {len({r for _, r in disp})} dispatch nodes")


if __name__ == "__main__":
    main(*sys.argv[1:4])
