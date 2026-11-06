#!/bin/sh
# Builds the Lean static library and the example `webp_lean_info`, linked like the fuzzer:
# libwebp_WebP.a statically, the Lean runtime (libleanshared.so) dynamically.
# Output: webp-lean/.lake/build/c/
set -eu
here=$(cd "$(dirname "$0")" && pwd)
proj=$(dirname "$here")
out="$proj/.lake/build/c"
mkdir -p "$out"
(cd "$proj" && lake build WebP:static)
prefix=$(cd "$proj" && lean --print-prefix)
${CC:-cc} -c -O2 -Wall -I "$prefix/include" -o "$out/webp_lean.o" "$here/webp_lean.c"
${CC:-cc} -c -O2 -Wall -o "$out/webp_lean_info.o" "$here/webp_lean_info.c"
${CC:-cc} -o "$out/webp_lean_info" "$out/webp_lean_info.o" "$out/webp_lean.o" \
  "$proj/.lake/build/lib/libwebp_WebP.a" -L "$prefix/lib/lean" -lleanshared \
  -Wl,-rpath,"$prefix/lib/lean" -lpthread
echo "built $out/webp_lean_info"
