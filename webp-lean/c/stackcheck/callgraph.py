"""Recursion audit of the Lean-emitted C (webp-lean/.lake/build/ir).

Builds the reference graph (direct calls, closures, closed-term initializers) reachable from the
given root symbols and reports every recursive cycle that was not compiled to a loop. Self tail
calls become `goto _start` and are not cycles. Exits 1 if a cycle outside ALLOWED is found.

usage: callgraph.py <ir-dir> <root-symbol>..."""
import collections, pathlib, re, sys

# Recursion whose depth does not depend on list lengths in the input:
ALLOWED = {
    "lp_webp_WebP_Anim_zeros",  # depth log2(canvas bytes) <= 35
    "lp_webp_WebP_Spec_le",     # little-endian read of 2..4 bytes
}

ir, roots = pathlib.Path(sys.argv[1]), sys.argv[2:]
fn_re = re.compile(r'^(?:LEAN_EXPORT |static )?(?:lean_object\*|uint\d+_t|double|size_t|void) '
                   r'(\w+)\([^)]*\)\s*\{', re.M)
ref_re = re.compile(r'\b((?:lp_webp_|l_)\w+)\b')
glob_re = re.compile(r'^static (?:const )?[\w ]+\*? (\w+?)(?:_value)? = (.*);$', re.M)

bodies, consts = {}, collections.defaultdict(set)
for f in ir.rglob('*.c'):
    src = f.read_text()
    starts = [(m.start(), m.group(1)) for m in fn_re.finditer(src)]
    for i, (pos, name) in enumerate(starts):
        end = starts[i + 1][0] if i + 1 < len(starts) else len(src)
        bodies[name] = src[pos:end].split('{', 1)[1]
    for m in glob_re.finditer(src):
        consts[m.group(1)] |= {re.sub(r'_value$', '', x) for x in ref_re.findall(m.group(2))}

def targets(name):
    """Functions a reference to `name` can reach directly."""
    if name in bodies: return [name]
    out = ['_init_' + name] if '_init_' + name in bodies else []
    for x in consts.get(name, ()):
        if x != name: out += targets(x)
    return out

graph = {n: {t for r in set(ref_re.findall(b)) for t in targets(r)} for n, b in bodies.items()}
seen, todo = set(), [r for r in roots if r in bodies]
missing = [r for r in roots if r not in bodies]
if missing: sys.exit(f"roots not found: {missing}")
while todo:
    n = todo.pop()
    if n not in seen:
        seen.add(n); todo += graph[n]

index, low, stack, on, cycles, counter = {}, {}, [], set(), [], [0]
sys.setrecursionlimit(1 << 20)
def visit(v):
    index[v] = low[v] = counter[0]; counter[0] += 1; stack.append(v); on.add(v)
    for w in graph[v]:
        if w not in index: visit(w); low[v] = min(low[v], low[w])
        elif w in on: low[v] = min(low[v], index[w])
    if low[v] == index[v]:
        comp = []
        while True:
            w = stack.pop(); on.discard(w); comp.append(w)
            if w == v: break
        if len(comp) > 1 or v in graph[v]: cycles.append(sorted(comp))
for v in sorted(seen):
    if v not in index: visit(v)

bad = [c for c in cycles if not set(c) <= ALLOWED]
print(f"{len(seen)} functions reachable from {', '.join(roots)}; "
      f"{sum('goto _start' in bodies[n] for n in seen)} self tail loops")
for c in cycles:
    print(("  allowed: " if set(c) <= ALLOWED else "  RECURSIVE: ") + " <-> ".join(c))
sys.exit(1 if bad else 0)
