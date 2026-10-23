"""Syntactic scan of snarkVM's circuit crates for constraint-generating functions.

A function *directly* generates constraints if its body calls an environment
constraint primitive (enforce / assert / assert_eq / assert_neq). It generates
constraints *indirectly* if it calls (by path or method name) or applies an
overloaded operator that resolves to a constraint-generating function.
Resolution is by name, so the indirect classification over-approximates.

Rows are generic over input types: impls that differ only in reference /
ownership or generic arguments (e.g. Mul<Field> for Field, Mul<&Field> for
&Field) are merged into one row per (crate, type, trait, function).

The component-level task columns come from the hand-maintained ACL2_MODELS map;
FUN-SPEC is additionally set from aleovm_circuit_function_funspec_map.tsv, which maps
rows to their specs in books/projects/aleo/vm/circuits/fun-specs. R1CS-SOUND-IF and
MANUAL-CONSTRAINTS is 1 for
functions that call a primitive directly. R1CS-SOUND-IF and
R1CS-COMPLETE-IF are copied from aleovm_circuit_function_circspec_map.tsv. They are not
0/1 flags. STATUS is "verified" when soundness holds (R1CS-SOUND is 1 or R1CS-SOUND-IF
is non-empty) and completeness holds (R1CS-COMPLETE is 1 or R1CS-COMPLETE-IF is non-empty).

Usage: python3 aleovm_circuit_functions_scan.py <snarkVM>/circuit aleovm_circuit_function_formalisation_status.csv
"""

import csv
import os
import re
import sys
from collections import defaultdict

PRIMITIVES = ("enforce", "assert", "assert_eq", "assert_neq")
OPERATOR_METHODS = {
    "*": ["mul"], "*=": ["mul_assign", "mul"], "/": ["div"], "/=": ["div_assign", "div"],
    "%": ["rem"], "%=": ["rem_assign", "rem"], "+": ["add"], "+=": ["add_assign", "add"],
    "-": ["sub"], "-=": ["sub_assign", "sub"], "&": ["bitand"], "&=": ["bitand_assign", "bitand"],
    "|": ["bitor"], "|=": ["bitor_assign", "bitor"], "^": ["bitxor"], "^=": ["bitxor_assign", "bitxor"],
    "<<": ["shl"], "<<=": ["shl_assign", "shl"], ">>": ["shr"], ">>=": ["shr_assign", "shr"],
    "unary!": ["not"], "unary-": ["neg"],
}
# Impls of these traits never add constraints (ejection, formatting, parsing, metrics, typing).
NON_GENERATING_TRAITS = {"Eject", "Display", "Debug", "Parser", "FromStr", "Metrics", "OutputMode", "Clone",
                         "Default", "PartialEq", "Eq", "Hash", "TypeName", "SizeInBits", "SizeInDataBits",
                         "ToTypeName", "Serialize", "Deserialize"}
# Calls with these names never add constraints (constants are evaluated natively by the environment).
NON_GENERATING_NAMES = {"eject_value", "eject_mode", "eject", "is_constant", "is_public", "is_private", "constant",
                        "fmt", "parse", "clone", "type_name", "size_in_bits", "size_in_data_bits", "count",
                        "output_mode", "mode", "halt", "scope", "new_variable", "new_witness",
                        "json_escape", "sample_file_component", "lc_sample_json",
                        "scope_sample_json", "maybe_write_scope_sample"}
# Environment-crate infrastructure: builds linear combinations / R1CS bookkeeping, but only the
# Environment primitives themselves add constraints.
ENV_INFRA_TYPES = {"LinearCombination", "Variable", "R1CS", "Assignment", "AssignmentLC", "AssignmentVariable",
                   "Constraint", "Count", "Measurement", "Counter", "UpdatableCount", "Arguments", "Mode",
                   "CircuitType", "Converter", "u64", "Circuit", "CanaryCircuit", "TestnetCircuit"}
CONSOLE_PATH = re.compile(r"\b(console|BaseField|ScalarField|Network|Affine|Projective|snarkvm_console\w*|"
                          r"snarkvm_fields|snarkvm_curves|std|core|alloc|itertools|indexmap)\s*::")
# Unsupported circuit types, left out of the status table. StringType::new halts on the host when
# the byte length does not fit in u32 instead of emitting an unsatisfiable R1CS, so it cannot meet
# R1CS-COMPLETE (books/projects/aleo/vm/circuits/fun-specs/README.md). The AleoCanaryV0 and
# AleoTestnetV0 networks are out of scope; AleoV0 is the formalised network.
UNSUPPORTED_TYPES = {"StringType", "AleoCanaryV0", "AleoTestnetV0"}
# Rows that the syntactic scan flags but that are not circuits. The two proc-macro helpers rewrite
# Rust syntax at compile time. `public` builds a public Identifier or ProgramID from a host value
# and emits no constraint. ProgramID is only constant or public, so no circuit constrains the
# fields `to_fields` reads and its output is fixed by the public input.
NOT_CIRCUITS = {("environment", "", "", "recursively_replace_self"), ("environment", "", "", "rename_selfs"),
                ("program", "Identifier", "", "public"), ("program", "ProgramID", "", "public"),
                ("program", "ProgramID", "ToFields", "to_fields")}
STD_TYPES = {"F", "Vec", "String", "Box", "Option", "Result", "IndexMap", "IndexSet", "HashMap", "BTreeMap",
              "Rc", "Arc", "RefCell", "OnceCell", "Cow", "Iterator", "PhantomData"}

# ACL2 counterparts in books/projects/aleo/vm/circuits, generic over input types, with the
# component-level task flags FUN-SPEC, R1CS-SPEC, PFCS-SPEC, R1CS-SAMPLES, R1CS-SOUND, R1CS-COMPLETE.
ACL2_MODELS = {
    ("Boolean", "new"): ("111111", "r1cs/boolean-check (iff bitp); pfcs/boolean-assert; bit constraints checked in samples/field-from-bits-le-new"),
    ("Boolean", "bitand"): ("111111", "r1cs/boolean-and (bitand, iff); pfcs/boolean-and; samples/boolean"),
    ("Boolean", "bitand_assign"): ("111111", "r1cs/boolean-and (bitand, iff); pfcs/boolean-and; samples/boolean"),
    ("Boolean", "bitor"): ("111111", "r1cs/boolean-or (bitor, iff); pfcs/boolean-or; samples/boolean"),
    ("Boolean", "bitor_assign"): ("111111", "r1cs/boolean-or (bitor, iff); pfcs/boolean-or; samples/boolean"),
    ("Boolean", "bitxor"): ("111111", "r1cs/boolean-xor (bitxor, iff); pfcs/boolean-xor; samples/boolean"),
    ("Boolean", "bitxor_assign"): ("111111", "r1cs/boolean-xor (bitxor, iff); pfcs/boolean-xor; samples/boolean"),
    ("Boolean", "nand"): ("111111", "r1cs/boolean-nand (bitnand, iff); pfcs/boolean-nand; samples/boolean"),
    ("Boolean", "nor"): ("111111", "r1cs/boolean-nor (bitnor, iff); pfcs/boolean-nor; samples/boolean"),
    ("Boolean", "ternary"): ("111111", "r1cs/if (if-gadget-to-if); pfcs/boolean-if; samples/boolean (ternary)"),
    ("Boolean", "is_equal"): ("111111", "samples/boolean is.eq via r1cs/boolean-xor; pfcs/boolean-eq"),
    ("Boolean", "is_not_equal"): ("111111", "samples/boolean is.neq via r1cs/boolean-xor; pfcs/boolean-neq"),
    ("Boolean", "is_less_than_or_equal_constant"): ("010110", "r1cs/bits-lte-const (soundness); checked against field-from_bits_le_diff_const sample (minus final assertion)"),
    ("Boolean", "assert_less_than_or_equal_constant"): ("010010", "r1cs/bits-lte-const-check (soundness)"),
    ("Field", "mul"): ("111111", "r1cs/field-mul (iff); pfcs/field-mul; samples/field-mul"),
    ("Field", "mul_assign"): ("111111", "r1cs/field-mul (iff); pfcs/field-mul; samples/field-mul"),
    ("Field", "square"): ("111111", "r1cs/field-square (iff); pfcs/field-square; samples/field-square"),
    ("Field", "inverse"): ("111111", "r1cs/field-inverse (spec with error case); pfcs/field-inv-checked; samples/field-inverse"),
    ("Field", "inv"): ("111111", "r1cs/field-inverse; pfcs/field-inv-checked; samples/field-inverse"),
    ("Field", "div"): ("111111", "r1cs/field-div (field-div-spec, soundness incl. error); pfcs/field-div-checked; samples/field-div"),
    ("Field", "div_assign"): ("111111", "r1cs/field-div; pfcs/field-div-checked; samples/field-div"),
    ("Field", "div_unchecked"): ("111001", "r1cs/field-div-unchecked (soundness); pfcs/field-div-unchecked (iff). div_unchecked JSON sample not checked"),
    ("Field", "is_not_equal"): ("111111", "r1cs/field-neq (soundness) + samples/field-neq; pfcs/field-neq (sound+complete)"),
    ("Field", "is_equal"): ("111011", "pfcs/field-eq (sound+complete); r1cs via field-neq with negated output. Equal sample not checked"),
    ("Field", "ternary"): ("111111", "r1cs/field-ternary (soundness); pfcs/field-if (iff); samples/field-ternary"),
    ("Field", "is_less_than"): ("010110", "r1cs/field-lt (soundness); samples/field-compare-new"),
    ("Field", "write_bits_le"): ("010110", "r1cs/field-to-bits (soundness); samples/field-to-bits-le-new"),
    ("Field", "from_bits_le"): ("010110", "r1cs/field-from-bits (soundness); samples/field-from-bits-le-new"),
    ("Field", "pow"): ("110110", "spec pfield::pow; r1cs/field-pow, field-pow-bits(-const), field-const-pow(-bits) (soundness); samples/field-pow"),
    ("Field", "square_root"): ("010010", "r1cs/field-square-root (soundness, inline spec y*y=x, y<=(p-1)/2)"),
    ("Integer", "new"): ("111011", "r1cs/boolean-check gadget-list (iff bit-listp, width-generic); pfcs/boolean-assert-all. Integer samples only in git-lfs zips"),
    ("Integer", "add_checked"): ("010010", "r1cs/unsigned-small-add(-checked)(-opt), signed-small-add-checked (soundness)"),
    ("Integer", "add_wrapped"): ("010010", "r1cs/unsigned-small-add-wrapped, signed-small-add-wrapped (soundness)"),
    ("Integer", "sub_checked"): ("010010", "r1cs/unsigned-small-sub(-checked)(-opt)(-const-var), signed-small-sub-checked(-const-var) (soundness)"),
    ("Integer", "sub_wrapped"): ("010000", "r1cs/unsigned-small-sub-wrapped(-const-var), signed-small-sub-wrapped(-const-var) (soundness)"),
    ("Integer", "abs_checked"): ("010010", "r1cs/signed-small-abs-checked (soundness)"),
    ("Integer", "abs_wrapped"): ("010010", "r1cs/signed-small-abs-wrapped (soundness)"),
    ("Integer", "neg"): ("010010", "r1cs/signed-small-neg (soundness)"),
    ("Integer", "is_not_equal"): ("010010", "r1cs/unsigned-small-neq(-opt), signed-small-neq(-opt) (soundness)"),
    ("Integer", "ternary"): ("010011", "r1cs/integer-ternary (correctness, iff)"),
    ("Integer", "bitand"): ("110011", "r1cs/integer-and (bitand-list, iff). Only Boolean samples checked"),
    ("Integer", "bitand_assign"): ("110011", "r1cs/integer-and (bitand-list, iff)"),
    ("Integer", "bitor"): ("110011", "r1cs/integer-or (bitor-list, iff)"),
    ("Integer", "bitor_assign"): ("110011", "r1cs/integer-or (bitor-list, iff)"),
    ("Integer", "bitxor"): ("110011", "r1cs/integer-xor (bitxor-list, iff)"),
    ("Integer", "bitxor_assign"): ("110011", "r1cs/integer-xor (bitxor-list, iff)"),
    ("Integer", "mul_checked"): ("000000", "partial: r1cs/unsigned-small/medium-mul-checked (unsigned only, no 128-bit); signed missing"),
    ("Integer", "mul_wrapped"): ("000000", "partial: r1cs/unsigned-small-mul-wrapped, signed-small-mul-wrapped (product must fit the field: no 128-bit)"),
    ("Integer", "mul_and_check"): ("000000", "partial: r1cs/unsigned-small-mul-and-check (unsigned only)"),
    ("Integer", "unsigned_division_via_witness"): ("000000", "partial: r1cs/unsigned-small-div, unsigned-medium-div (Euclidean soundness); 128-bit not covered"),
    ("Integer", "is_less_than"): ("000000", "partial: r1cs/unsigned-small-lt (unsigned only); signed missing"),
}
KEYWORDS = {"if", "while", "for", "match", "return", "loop", "in", "as", "let", "mut", "ref", "move",
            "else", "where", "impl", "fn", "pub", "use", "mod", "struct", "enum", "trait", "type",
            "const", "static", "unsafe", "async", "await", "dyn", "crate", "super", "self", "Some",
            "None", "Ok", "Err", "box"}


def strip_comments_and_strings(src):
    out, i, n = [], 0, len(src)

    def blank(s):
        return "".join("\n" if c == "\n" else " " for c in s)

    while i < n:
        c = src[i]
        if src.startswith("//", i):
            j = src.find("\n", i)
            j = n if j < 0 else j
            out.append(blank(src[i:j])); i = j
        elif src.startswith("/*", i):
            depth, j = 1, i + 2
            while j < n and depth:
                if src.startswith("/*", j): depth += 1; j += 2
                elif src.startswith("*/", j): depth -= 1; j += 2
                else: j += 1
            out.append(blank(src[i:j])); i = j
        elif re.match(r'(b?r#*")', src[i:i + 4]) and (i == 0 or not (src[i - 1].isalnum() or src[i - 1] == "_")):
            m = re.match(r'b?r(#*)"', src[i:])
            hashes = m.group(1)
            end = src.find('"' + hashes, i + len(m.group(0)))
            end = n if end < 0 else end + 1 + len(hashes)
            out.append('""' + blank(src[i + 2:end])); i = end
        elif c == '"' or (c == "b" and src.startswith('b"', i) and (i == 0 or not src[i - 1].isalnum())):
            j = i + (2 if c == "b" else 1)
            while j < n and src[j] != '"':
                j += 2 if src[j] == "\\" else 1
            out.append('""' + blank(src[i + 2:j + 1])); i = j + 1
        elif c == "'":
            m = re.match(r"'(\\u\{[0-9a-fA-F]+\}|\\.|[^\\'])'", src[i:])
            if m:
                out.append("' '" + blank(m.group(0)[3:])); i += len(m.group(0))
            else:
                out.append(c); i += 1
        else:
            out.append(c); i += 1
    return "".join(out)


def match_delim(text, start, open_c="{", close_c="}"):
    depth = 0
    for j in range(start, len(text)):
        if text[j] == open_c:
            depth += 1
        elif text[j] == close_c:
            depth -= 1
            if depth == 0:
                return j
    return len(text) - 1


def blank_range(text, a, b):
    return text[:a] + "".join("\n" if ch == "\n" else " " for ch in text[a:b + 1]) + text[b + 1:]


def remove_test_items(text):
    for m in list(re.finditer(r"#\[cfg\((?:all\()?test\b[^\]]*\]", text))[::-1]:
        j = m.end()
        while True:
            k = re.match(r"\s*#\[[^\]]*\]", text[j:])
            if not k:
                break
            j += k.end()
        semi, brace = text.find(";", j), text.find("{", j)
        if brace >= 0 and (semi < 0 or brace < semi):
            text = blank_range(text, m.start(), match_delim(text, brace))
        elif semi >= 0:
            text = blank_range(text, m.start(), semi)
    return text


def remove_macro_bodies(text, names=("witness", "witness_mode", "count", "output_mode", "assert_count",
                                     "assert_output_mode", "debug_assert", "debug_assert_eq")):
    for name in names:
        for m in list(re.finditer(r"\b%s!\s*\(" % name, text))[::-1]:
            p = text.find("(", m.start())
            text = blank_range(text, p + 1, match_delim(text, p, "(", ")") - 1)
    return text


def strip_generics(s):
    out, depth = [], 0
    for ch in s:
        if ch == "<": depth += 1
        elif ch == ">": depth = max(0, depth - 1)
        elif depth == 0: out.append(ch)
    return "".join(out)


def base_name(s):
    s = strip_generics(s).strip()
    s = re.sub(r"^(&\s*('\w+\s*)?(mut\s+)?)+", "", s).strip()
    s = re.sub(r"^dyn\s+", "", s)
    m = re.findall(r"[A-Za-z_]\w*", s.split("::")[-1]) if s else []
    if s.startswith("("):
        return "(" + ",".join(base_name(x) for x in s.strip("()").split(",") if x.strip()) + ")"
    if s.startswith("["):
        return "[" + base_name(s.strip("[]").split(";")[0]) + "]"
    return m[0] if m else s


def parse_impl_header(h):
    h = h.strip()
    if h.startswith("<"):
        depth = 0
        for k, ch in enumerate(h):
            if ch == "<": depth += 1
            elif ch == ">":
                depth -= 1
                if depth == 0:
                    h = h[k + 1:]; break
    h = re.split(r"\bwhere\b", h)[0]
    flat = strip_generics(h)
    if re.search(r"\bfor\b", flat):
        idx, depth = None, 0
        for k in range(len(h)):
            if h[k] == "<": depth += 1
            elif h[k] == ">": depth -= 1
            elif depth == 0 and re.match(r"\bfor\b", h[k:]) and (k == 0 or not h[k - 1].isalnum()):
                idx = k; break
        trait, typ = h[:idx], h[idx + 3:]
        return base_name(trait), base_name(typ)
    return "", base_name(h)


def scan_items(text, path, defs):
    pos, n = 0, len(text)
    item_re = re.compile(r"\b(impl|trait|fn|mod)\b")
    def walk(start, end, ctx):
        i = start
        while True:
            m = item_re.search(text, i, end)
            if not m:
                return
            kw = m.group(1)
            if m.start() > 0 and (text[m.start() - 1].isalnum() or text[m.start() - 1] in "_."):
                i = m.end(); continue
            if kw == "mod":
                mm = re.match(r"mod\s+\w+\s*([{;])", text[m.start():])
                if mm and mm.group(1) == "{":
                    b = text.find("{", m.start())
                    e = match_delim(text, b)
                    walk(b + 1, e, ctx); i = e + 1
                else:
                    i = m.end()
                continue
            if kw in ("impl", "trait"):
                b = text.find("{", m.end())
                s = text.find(";", m.end())
                if b < 0 or (0 <= s < b and kw == "trait"):
                    i = m.end(); continue
                header = text[m.end():b]
                e = match_delim(text, b)
                if kw == "impl":
                    trait, typ = parse_impl_header(header)
                    walk(b + 1, e, {"type": typ, "trait": trait})
                else:
                    tname = re.match(r"\s*(\w+)", header)
                    walk(b + 1, e, {"type": "<trait default>", "trait": tname.group(1) if tname else ""})
                i = e + 1
                continue
            fm = re.match(r"fn\s+([A-Za-z_]\w*)", text[m.start():])
            if not fm:
                i = m.end(); continue
            name = fm.group(1)
            j, depth_p, depth_a = m.start() + fm.end(), 0, 0
            body_start = None
            while j < end:
                ch = text[j]
                if ch == "(": depth_p += 1
                elif ch == ")": depth_p -= 1
                elif ch == "<": depth_a += 1
                elif ch == ">" and text[j - 1] != "-": depth_a -= 1
                elif ch == ";" and depth_p == 0:
                    break
                elif ch == "{" and depth_p == 0:
                    body_start = j; break
                j += 1
            if body_start is None:
                i = j + 1; continue
            e = match_delim(text, body_start)
            line = text.count("\n", 0, m.start()) + 1
            defs.append({"path": path, "line": line, "name": name, "type": ctx.get("type", ""),
                         "trait": ctx.get("trait", ""), "sig": " ".join(text[m.start():body_start].split()),
                         "body": text[body_start:e + 1]})
            i = e + 1
    walk(0, n, {})


CLOSURE_RE = re.compile(r"(?:(?<=[(,={;])|(?<==>)|(?<=\bmove)|(?<=\breturn))\s*\|[^|]*\|")


def analyse_body(body):
    b = CLOSURE_RE.sub(" ", body)
    direct = sorted({m.group(1) for m in re.finditer(r"\b[A-Z]\w*\s*::\s*(%s)\s*\(" % "|".join(PRIMITIVES), b)})
    paths = []
    for m in re.finditer(r"\b([A-Za-z_]\w*)\s*(?:<[^<>;{}]*>)?\s*::\s*([a-z_]\w*)\s*(?:::\s*<[^;{}]*?>\s*)?\(", b):
        prefix = b[max(0, m.start() - 80):m.start()]
        chain = re.search(r"((?:[A-Za-z_]\w*\s*(?:<[^<>;{}]*>)?\s*::\s*)*)$", prefix).group(1)
        if CONSOLE_PATH.search(chain + m.group(1) + "::") or m.group(1) in STD_TYPES:
            continue
        paths.append((m.group(1), m.group(2)))
    methods, self_methods = [], []
    for m in re.finditer(r"\.\s*([a-z_]\w*)\s*(?:::\s*<[^;{}]*?>\s*)?\(", b):
        recv = b[max(0, m.start() - 40):m.start()]
        if re.search(r"(linear_combination|\blc)\s*$", recv):
            continue
        if re.search(r"(?<![\w.])\(?&?\s*self\)?\s*$", recv):
            self_methods.append(m.group(1))
        else:
            methods.append(m.group(1))
    free = [m.group(1) for m in re.finditer(r"(?<![.:\w])([a-z_]\w*)\s*\(", b) if m.group(1) not in KEYWORDS]
    ops = set()
    for m in re.finditer(r"(<<=|>>=|<<|>>|[*/%+\-&|^]=?)", b):
        tok, s = m.group(1), m.start()
        if b[s:s + 2] in ("&&", "||", "->") or b[s - 1:s + 1] in ("&&", "||") or b[s:s + 2] == "=>":
            continue
        k = s - 1
        while k >= 0 and b[k] in " \t\n":
            k -= 1
        prev = b[k] if k >= 0 else ""
        nxt = b[m.end():m.end() + 1]
        if tok in ("<<", ">>") and (prev == ":" or nxt in "<>"):
            continue
        after = b[m.end():].lstrip()[:1]
        before = re.search(r"([\w.]+)\s*$", b[:s])
        if after.isdigit() or (before and before.group(1)[:1].isdigit()):
            continue
        if prev and (prev.isalnum() or prev in "_)]"):
            word = re.search(r"([A-Za-z_]\w*)$", b[:k + 1])
            if word and word.group(1) in KEYWORDS - {"self", "Some", "None", "Ok", "Err"}:
                if tok == "-": ops.add("unary-")
                continue
            if tok == "&" and nxt == "&":
                continue
            ops.add(tok)
        elif tok == "-" and nxt != ">":
            ops.add("unary-")
    if re.search(r"(?<![!=<>])!(?![=])\s*[\w(&*]", b) and re.search(r"(?<![\w!])!(?!=)\s*[a-z_(&*]", b):
        ops.add("unary!")
    return direct, paths, methods, self_methods, free, sorted(ops)


def crate_of(rel):
    parts = rel.split(os.sep)
    if parts[0] == "types" and len(parts) > 2:
        return "types/" + parts[1]
    return parts[0]


FUN_SPEC_MAP = os.path.join(os.path.dirname(os.path.abspath(__file__)), "aleovm_circuit_function_funspec_map.tsv")
CIRC_SPEC_MAP = os.path.join(os.path.dirname(os.path.abspath(__file__)), "aleovm_circuit_function_circspec_map.tsv")
CIRC_FLAG_COLS = ["R1CS-SPEC", "PFCS-SPEC", "R1CS-SAMPLES", "R1CS-SOUND", "R1CS-COMPLETE"]
# Not 0/1 flags. Name the prior circuit that discharges a hypothesis of the soundness or
# completeness theorem.
SOUND_IF_COL = "R1CS-SOUND-IF"
COMPLETE_IF_COL = "R1CS-COMPLETE-IF"
# 1 when the function body itself calls an Environment constraint primitive (enforce / assert /
# assert_eq / assert_neq), i.e. writes constraints by hand rather than only through other gadgets.
MANUAL_COL = "MANUAL-CONSTRAINTS"


def load_fun_specs():
    """FUN-SPEC map: (crate, type, trait, function) -> status, ACL2 spec symbol and book under books/."""
    if not os.path.exists(FUN_SPEC_MAP):
        return {}
    with open(FUN_SPEC_MAP, newline="") as f:
        return {(r["crate"], r["type"], r["trait"], r["function"]): r
                for r in csv.DictReader(f, delimiter="\t")}


def load_circ_specs():
    """Circuit-task map. A 1 sets that flag; it does not clear a 1 already recorded in ACL2_MODELS."""
    if not os.path.exists(CIRC_SPEC_MAP):
        return {}
    with open(CIRC_SPEC_MAP, newline="") as f:
        return {(r["crate"], r["type"], r["trait"], r["function"]): r
                for r in csv.DictReader(f, delimiter="\t")}


def main(root, out):
    defs = []
    for dp, dn, fn in os.walk(root):
        dn[:] = [d for d in dn if d not in ("tests", "benches", "target", "examples")]
        for f in fn:
            if not f.endswith(".rs") or f in ("tests.rs",) or f.endswith("_tests.rs"):
                continue
            p = os.path.join(dp, f)
            rel = os.path.relpath(p, root)
            text = open(p, encoding="utf-8").read()
            text = remove_macro_bodies(remove_test_items(strip_comments_and_strings(text)))
            scan_items(text, rel, defs)

    for d in defs:
        d["direct"], d["paths"], d["methods"], d["self_methods"], d["free"], d["ops"] = analyse_body(d["body"])
        d["crate"] = crate_of(d["path"])

    by_name = defaultdict(list)
    by_type_name = defaultdict(list)
    for d in defs:
        by_name[d["name"]].append(d)
        by_type_name[(d["type"], d["name"])].append(d)
        if d["trait"]:
            by_type_name[(d["trait"], d["name"])].append(d)

    def eligible(d):
        if d["trait"] in NON_GENERATING_TRAITS or d["name"] in NON_GENERATING_NAMES:
            return False
        if d["type"] == "LinearCombination":
            return False
        return not (d["crate"] == "environment" and d["type"] in ENV_INFRA_TYPES)

    for d in defs:
        if d["crate"] == "environment" and d["trait"] == "Environment" and d["name"] in PRIMITIVES:
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
            reasons = set()
            for q, name in d["paths"]:
                if (name in PRIMITIVES and q[0].isupper()) or name in NON_GENERATING_NAMES:
                    continue
                if q == "Self" or (q, name) == ("From", "from"):
                    cands = by_type_name.get((d["type"], name), []) or (by_name.get(name, []) if q == "Self" else [])
                elif (q, name) in by_type_name:
                    cands = by_type_name[(q, name)]
                elif q[0].isupper() and len(q) > 1 and q not in ("Self",) and not re.fullmatch(r"[A-Z]", q):
                    cands = []
                else:
                    cands = by_name.get(name, [])
                if any(gen[id(c)] for c in cands if c is not d):
                    reasons.add(f"{q}::{name}")
            def own_or_any(name):
                return by_type_name.get((d["type"], name)) or by_name.get(name, [])

            for name, cands in ([(n, by_name.get(n, [])) for n in d["methods"] + d["free"]] +
                                [(n, own_or_any(n)) for n in d["self_methods"]]):
                if name in NON_GENERATING_NAMES:
                    continue
                if any(gen[id(c)] for c in cands if c is not d):
                    reasons.add(name)
            for op in (d["ops"] if d["crate"] != "environment" else []):
                names = OPERATOR_METHODS[op]
                own = [c for n in names for c in by_type_name.get((d["type"], n), [])]
                if op.rstrip("=") in ("&", "|", "^"):
                    own += [c for n in names for c in by_type_name.get(("Boolean", n), [])]
                # Inside the primitive type crates, operators without an own-type impl act on inner
                # linear combinations / console values, so only own-type operators count there.
                cands = own or ([] if d["crate"].startswith("types/") else
                                [c for n in names for c in by_name.get(n, [])])
                if any(gen[id(c)] for c in cands if c is not d):
                    reasons.add("op " + op.replace("unary", "unary "))
            if reasons - via[id(d)]:
                via[id(d)] |= reasons
                if not gen[id(d)]:
                    gen[id(d)] = True
                changed = True

    rows = defaultdict(list)
    for d in defs:
        if (gen[id(d)] and d["type"] not in UNSUPPORTED_TYPES
                and (d["crate"], d["type"], d["trait"], d["name"]) not in NOT_CIRCUITS):
            rows[(d["crate"], d["type"], d["trait"], d["name"])].append(d)

    def evidence(ds):
        if any(x["direct"] for x in ds):
            return "direct"
        rs = set().union(*(via[id(x)] for x in ds))
        if all(r.startswith("op ") for r in rs):
            return "indirect (operators only)"
        return "indirect (calls)"

    fun_specs = load_fun_specs()
    circ_specs = load_circ_specs()
    with open(out, "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["crate", "type", "trait", "function", "file", "line", "merged_impls",
                    "constraint_source", MANUAL_COL, "primitives", "via", "FUN-SPEC", "R1CS-SPEC", "PFCS-SPEC",
                    "R1CS-SAMPLES", "R1CS-SOUND", "R1CS-COMPLETE", SOUND_IF_COL, COMPLETE_IF_COL,
                    "STATUS", "acl2_counterpart", "fun_spec"])
        for key in sorted(rows, key=lambda k: (k[0], k[1], k[2], k[3])):
            ds = sorted(rows[key], key=lambda x: (x["path"], x["line"]))
            prims = sorted(set().union(*(set(x["direct"]) for x in ds)))
            rs = sorted(set().union(*(via[id(x)] for x in ds)))
            flags, model = ACL2_MODELS.get((key[1], key[3]), ("000000", ""))
            flags = list(flags)
            spec = fun_specs.get(key)
            fun_spec = ""
            if spec and spec["status"] == "spec":
                flags[0] = "1"
                fun_spec = f'{spec["acl2_spec"]} ({spec["book"]})'
            elif spec and spec["status"] == "excluded-hash":
                flags[0] = "excluded"
                fun_spec = "hash internals, abstract in fun-specs/base.lisp"
            circ = circ_specs.get(key)
            sound_if = complete_if = ""
            if circ and flags[0] != "excluded":
                for i, col in enumerate(CIRC_FLAG_COLS, start=1):
                    if circ.get(col) == "1":
                        flags[i] = "1"
                if circ.get("acl2"):
                    model = (model + "; " + circ["acl2"]).strip("; ")
                sound_if = circ.get(SOUND_IF_COL) or ""
                complete_if = circ.get(COMPLETE_IF_COL) or ""
            sound = flags[CIRC_FLAG_COLS.index("R1CS-SOUND") + 1] == "1" or bool(sound_if)
            complete = flags[CIRC_FLAG_COLS.index("R1CS-COMPLETE") + 1] == "1" or bool(complete_if)
            status = "verified" if sound and complete else ""
            w.writerow([key[0], key[1], key[2], key[3], "circuit/" + ds[0]["path"], ds[0]["line"], len(ds),
                        evidence(ds), "1" if prims else "0", " ".join(prims), " ".join(rs[:8]) + (" ..." if len(rs) > 8 else "")]
                       + flags + [sound_if, complete_if, status, model, fun_spec])
    missing = [k for k in ACL2_MODELS if not any((r[1], r[3]) == k for r in rows)]
    if missing:
        print("ACL2 models without a matching constraint-generating function:", missing)
    unmatched = [k for k in fun_specs if k not in rows and k[1] not in UNSUPPORTED_TYPES]
    if unmatched:
        print("FUN-SPEC map entries without a matching constraint-generating function:", unmatched)
    total = len({(d["crate"], d["type"], d["trait"], d["name"]) for d in defs})
    print(f"{len(defs)} fn defs, {total} merged functions, {len(rows)} constraint-generating")


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2])
