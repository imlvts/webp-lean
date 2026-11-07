#!/bin/sh
# Stack-safety check of the Lean decoder and metadata reader:
#  1. recursion audit of the emitted C (callgraph.py), from the FFI exports and the CLI main;
#  2. decode + info of large chunk/frame lists and 4096x4096 images on a 256 KiB thread stack.
# Needs cwebp from build/libwebp-tools. Work files go to $WORK (default: a fresh temp dir).
set -eu
here=$(cd "$(dirname "$0")" && pwd)
proj=$(cd "$here/../.." && pwd)
tools=${CWEBP_DIR:-$proj/../build/libwebp-tools}
work=${WORK:-$(mktemp -d)}
stack_kib=${STACK_KIB:-256}
n=${N:-1000000}
(cd "$proj" && lake build WebP:static webp-lean) > "$work/lake.log" 2>&1 || { tail -20 "$work/lake.log"; exit 1; }
python3 -I "$here/callgraph.py" "$proj/.lake/build/ir" webp_lean_decode_impl webp_lean_info_impl _lean_main
prefix=$(cd "$proj" && lean --print-prefix)
cc -O2 -I "$prefix/include" -o "$work/stackcheck" "$here/stackcheck.c" \
  "$proj/.lake/build/lib/libwebp_WebP.a" -L "$prefix/lib/lean" -lleanshared \
  -Wl,-rpath,"$prefix/lib/lean" -lpthread
python3 -I "$here/gen_images.py" pam1 "$work/one.pam"
python3 -I "$here/gen_images.py" pambig "$work/big.pam" 4096
"$tools/cwebp" -quiet -lossless "$work/one.pam" -o "$work/one_lossless.webp"
"$tools/cwebp" -quiet -q 80 "$work/one.pam" -o "$work/one_lossy.webp"
"$tools/cwebp" -quiet -lossless "$work/big.pam" -o "$work/big_lossless.webp"
"$tools/cwebp" -quiet -q 80 "$work/big.pam" -o "$work/big_lossy_alpha.webp"
for k in frames chunks xchunks subchunks; do python3 -I "$here/stress.py" $k $n "$work/$k.webp" "$work"; done
fail=0
for f in frames chunks xchunks subchunks big_lossless big_lossy_alpha; do
  for m in info decode; do
    if out=$("$work/stackcheck" "$stack_kib" $m "$work/$f.webp" 2>&1) && echo "$out" | grep -q ' ok '; then
      echo "ok    $m $f"
    else
      echo "FAIL  $m $f: $(echo "$out" | tail -1)"; fail=1
    fi
  done
done
exit $fail
