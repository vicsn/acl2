#!/bin/sh
# Regenerate boolean.lisp with the pinned Charon and Aeneas ACL2 backend,
# require a byte match, certify the book, and require src/shape.rs to fail.
set -eu

cd "$(dirname "$0")"
IMAGE=ghcr.io/bendyarm/aeneas-acl2-dev:aeneas-23cf8c8_charon-58b7d54_acl2-0612757

docker run --rm --platform linux/amd64 \
  -v "$PWD":/work/try:ro \
  --entrypoint bash \
  "$IMAGE" -lc '
set -eu
mkdir -p /tmp/out
echo "== boolean"
/work/charon/bin/charon rustc --dest-file /tmp/out/boolean.llbc --preset=aeneas -- \
  /work/try/src/boolean.rs --crate-name=boolean --crate-type=rlib --edition=2021 \
  --allow=unused --allow=non_snake_case
/work/aeneas/bin/aeneas -backend acl2 -use-fuel -loops-to-rec -dest /tmp/out /tmp/out/boolean.llbc
diff -u /work/try/boolean.lisp /tmp/out/boolean.lisp
cp /tmp/out/boolean.lisp /work/aeneas/tests/acl2/boolean.lisp
( cd /work/aeneas/tests/acl2 && cert.pl -j 1 boolean )
echo "== shape (expected failure)"
/work/charon/bin/charon rustc --dest-file /tmp/out/shape.llbc --preset=aeneas --monomorphize -- \
  /work/try/src/shape.rs --crate-name=shape --crate-type=rlib --edition=2021 \
  --allow=unused --allow=non_snake_case
set +e
/work/aeneas/bin/aeneas -backend acl2 -use-fuel -loops-to-rec -dest /tmp/out /tmp/out/shape.llbc
status=$?
set -e
if [ "$status" -eq 0 ]; then
  echo "shape.rs extracted; the ACL2 backend was expected to reject the closure" >&2
  exit 1
fi
echo "shape.rs failed as expected (exit $status)"
'

echo "extraction matches boolean.lisp and certifies"
