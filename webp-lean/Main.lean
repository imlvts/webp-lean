import WebP
open WebP WebP.Spec

def writePAM (path : String) (w h : Nat) (rgba : ByteArray) : IO Unit := do
  let hdr := s!"P7\nWIDTH {w}\nHEIGHT {h}\nDEPTH 4\nMAXVAL 255\nTUPLTYPE RGB_ALPHA\nENDHDR\n"
  IO.FS.writeBinFile path (hdr.toUTF8 ++ rgba)

/-- One line of text for a single (bounded-size) value. Lists from the input are printed one
item per line by the callers: `repr` of a whole list builds a left-nested `Format` whose
pretty-printing recurses once per element. -/
def line (f : Std.Format) : String := f.pretty 100000

def usage : String :=
  "usage: webp-lean decode <in.webp> <out-prefix>   (writes <out-prefix>.pam or <out-prefix>.<n>.pam)\n" ++
  "       webp-lean info <in.webp>     (metadata, without decoding pixels)\n" ++
  "       webp-lean layout <in.webp>   (demuxed container layout)"

def main (args : List String) : IO UInt32 := do
  match args with
  | ["decode", inp, out] =>
    let d ← IO.FS.readBinFile inp
    match WebP.decode d with
    | .error e => IO.eprintln s!"error: {e}"; pure 1
    | .ok o =>
      match o.frames with
      | [(_, c)] => if !o.animated then writePAM (out ++ ".pam") o.width o.height c
                    else writePAM (out ++ ".0.pam") o.width o.height c
      | fs => for ((_, c), i) in fs.zipIdx do writePAM s!"{out}.{i}.pam" o.width o.height c
      pure 0
  | ["info", inp] =>
    let d ← IO.FS.readBinFile inp
    match WebP.info d with
    | .error e => IO.println s!"error: {e}"; pure 1
    | .ok i =>
      IO.println s!"width: {i.width}\nheight: {i.height}\nanimated: {i.animated}\nhasAlpha: {i.hasAlpha}"
      IO.println s!"lossy: {i.lossy}\nloopCount: {i.loopCount}\nbackground: {i.background}"
      IO.println s!"extended: {i.extended}\niccp: {line (repr i.iccp)}\nexif: {line (repr i.exif)}"
      IO.println s!"xmp: {line (repr i.xmp)}\nframes: {i.frames.length}"
      for f in i.frames, n in [0:i.frames.length] do IO.println s!"frame {n}: {line (repr f)}"
      pure 0
  | ["layout", inp] =>
    let d ← IO.FS.readBinFile inp
    match Container.demux d with
    | .error e => IO.println s!"demux error: {e}"; pure 1
    | .ok (.still x alph bits) =>
      IO.println s!"still\nvp8x: {line (repr x)}\nalph: {line (repr alph)}\nbits: {line (repr bits)}"
      pure 0
    | .ok (.animated x bg loops frames) =>
      IO.println s!"animated\nvp8x: {line (repr x)}\nbackground: {bg}\nloopCount: {loops}"
      IO.println s!"frames: {frames.length}"
      for f in frames, n in [0:frames.length] do IO.println s!"frame {n}: {line (repr f)}"
      pure 0
  | _ => IO.eprintln usage; pure 2
