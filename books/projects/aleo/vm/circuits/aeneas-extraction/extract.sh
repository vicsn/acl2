#!/bin/sh
# Regenerate circuits.lisp with the pinned Charon and Aeneas ACL2 backend,
# require a byte match, require src/shape.rs to fail, certify the check books,
# and check manifest.tsv against the verified rows of the status CSV.
set -eu

cd "$(dirname "$0")"
REPO=$(git rev-parse --show-toplevel)
IMAGE=ghcr.io/bendyarm/aeneas-acl2-dev:aeneas-23cf8c8_charon-58b7d54_acl2-0612757
EXT=books/projects/aleo/vm/circuits/aeneas-extraction

docker run --rm --platform linux/amd64 \
  -v "$REPO":/ws \
  --entrypoint bash \
  "$IMAGE" -lc "
set -eu
cd /ws/$EXT
mkdir -p /tmp/out
echo '== circuits'
/work/charon/bin/charon rustc --dest-file /tmp/out/circuits.llbc --preset=aeneas --monomorphize -- \
  src/circuits.rs --crate-name=circuits --crate-type=rlib --edition=2021 \
  --allow=unused --allow=non_snake_case
/work/aeneas/bin/aeneas -backend acl2 -use-fuel -loops-to-rec -dest /tmp/out /tmp/out/circuits.llbc
diff -u circuits.lisp /tmp/out/circuits.lisp
cp /work/aeneas/tests/acl2/rust-primitives.lisp rust-primitives.lisp
echo '== shape (expected failure)'
/work/charon/bin/charon rustc --dest-file /tmp/out/shape.llbc --preset=aeneas --monomorphize -- \
  src/shape.rs --crate-name=shape --crate-type=rlib --edition=2021 \
  --allow=unused --allow=non_snake_case
set +e
/work/aeneas/bin/aeneas -backend acl2 -use-fuel -loops-to-rec -dest /tmp/out /tmp/out/shape.llbc
status=\$?
set -e
if [ \"\$status\" -eq 0 ]; then
  echo 'shape.rs extracted; the ACL2 backend was expected to reject the closure' >&2
  exit 1
fi
echo \"shape.rs failed as expected (exit \$status)\"
echo '== certify'
cd /ws
books/build/cert.pl --include-excludes --acl2 /root/acl2/saved_acl2 -j 3 \
  $EXT/check-boolean $EXT/check-field $EXT/check-integer $EXT/check-scalar
"

echo '== manifest'
python3 - "$REPO/aleovm_circuit_function_formalisation_status.csv" manifest.tsv <<'EOF'
import csv, re, sys, glob
key = lambda r: (r['crate'], r['type'], r['trait'], r['function'])
verified = {key(r) for r in csv.DictReader(open(sys.argv[1])) if r['STATUS'] == 'verified'}
rows = list(csv.DictReader(open(sys.argv[2]), delimiter='\t'))
listed = {key(r) for r in rows}
names = set()
for f in glob.glob('check-*.lisp'):
    names |= set(re.findall(r'^\(defcheck ([a-z0-9-]+)', open(f).read(), re.M))
bad = [r['check'] for r in rows
       if re.fullmatch(r'[a-z0-9-]+', r['check']) and r['check'] not in names]
if verified != listed or bad:
    print('missing:', sorted(verified - listed), 'extra:', sorted(listed - verified),
          'unknown checks:', bad, file=sys.stderr)
    sys.exit(1)
print(len(rows), 'verified rows listed')
EOF

echo "extraction matches circuits.lisp and the checks certify"
