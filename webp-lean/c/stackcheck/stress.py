"""Stress inputs for run.sh: stress.py <frames|chunks|xchunks|subchunks> <n> <out.webp> <dir with one_lossless.webp, one_lossy.webp>."""
import struct, sys
def chunks(path):
    d = open(path, 'rb').read(); p, out = 12, []
    while p + 8 <= len(d):
        tag, n = d[p:p+4], struct.unpack('<I', d[p+4:p+8])[0]
        out.append((tag, d[p+8:p+8+n])); p += 8 + n + (n & 1)
    return out
def chunk(tag, p): return tag + struct.pack('<I', len(p)) + p + (b'\0' if len(p) % 2 else b'')
def riff(body): return b'RIFF' + struct.pack('<I', 4 + len(body)) + b'WEBP' + body
u24 = lambda v: struct.pack('<I', v)[:3]
kind, n, out = sys.argv[1], int(sys.argv[2]), sys.argv[3]
here = sys.argv[4]
lossless = b''.join(chunk(t, p) for t, p in chunks(f'{here}/one_lossless.webp'))
lossy = b''.join(chunk(t, p) for t, p in chunks(f'{here}/one_lossy.webp') if t != b'VP8X')
if kind == 'frames':   # n 1x1 frames alternating lossless / lossy+ALPH, varying blend/dispose
    fr = []
    for i in range(n):
        data = lossless if i % 2 == 0 else lossy
        fr.append(chunk(b'ANMF', u24(0) + u24(0) + u24(0) + u24(0) + u24(10) + bytes([i % 4]) + data))
    body = chunk(b'VP8X', bytes([0x12, 0, 0, 0]) + u24(0) + u24(0)) + chunk(b'ANIM', b'\0' * 6) + b''.join(fr)
elif kind == 'chunks':   # simple lossless file + n empty unknown chunks
    body = lossless + b'ZZZZ\0\0\0\0' * n
elif kind == 'xchunks':  # extended still: n unknown chunks before the image data
    body = chunk(b'VP8X', bytes([0x10, 0, 0, 0]) + u24(0) + u24(0)) + b'ZZZZ\0\0\0\0' * n + lossy
elif kind == 'subchunks':  # one frame carrying n unknown subchunks
    data = b'ZZZZ\0\0\0\0' * n + lossless
    body = (chunk(b'VP8X', bytes([0x12, 0, 0, 0]) + u24(0) + u24(0)) + chunk(b'ANIM', b'\0' * 6)
            + chunk(b'ANMF', u24(0) * 4 + u24(10) + b'\0' + data))
open(out, 'wb').write(riff(body))
