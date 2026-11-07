"""PAM sources for run.sh: gen_images.py pam1 <out> (1x1 RGBA) | pambig <out> <size> (size x size RGBA)."""
import struct, sys, random
def pam(path, w, h, f):
    with open(path, 'wb') as o:
        o.write(f"P7\nWIDTH {w}\nHEIGHT {h}\nDEPTH 4\nMAXVAL 255\nTUPLTYPE RGB_ALPHA\nENDHDR\n".encode())
        row = bytearray()
        for y in range(h):
            row = bytearray()
            for x in range(w): row += bytes(f(x, y))
            o.write(row)
cmd = sys.argv[1]
if cmd == 'pam1':
    pam(sys.argv[2], 1, 1, lambda x, y: (200, 100, 50, 128))
elif cmd == 'pambig':
    w = h = int(sys.argv[3]); rnd = random.Random(1)
    noise = bytes(rnd.getrandbits(8) for _ in range(4096))
    pam(sys.argv[2], w, h, lambda x, y: ((x * 7) & 255, (y * 3) & 255, noise[(x ^ y) & 4095], (x + y) & 255))
