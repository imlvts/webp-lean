# WebP: Lean formalization + verified decoder + differential fuzzer

Layout (all under /var/data/diff-fuzz/webp):

- `rfc/rfc9649.txt` — the spec (RFC 9649, WebP image format).
- `libwebp/`        — reference C implementation (git checkout).
- `image-webp/`     — pure-Rust implementation (git checkout, v0.2.4).
- `webp-lean/`      — Lean 4 project (toolchain v4.35.0, no Mathlib).
  - `WebP/Basic.lean`          shared types (`WebP.RGBAImage`).
  - `WebP/Spec/*.lean`         formal spec of RFC 9649 (container grammar, VP8L, ALPH, animation).
  - `WebP/Container/*.lean`    RIFF/WebP demuxer.
  - `WebP/VP8L/*.lean`         lossless decoder.
  - `WebP/Spec/VP8/*.lean`     RFC 6386 key-frame decoding (transcription of the reference decoder) + YUV->RGBA.
  - `WebP/VP8.lean`, `WebP/VP8/*.lean`  shipped lossy decoder (= spec with optimized primitives, proven).
  - `WebP/VP8Libwebp/*.lean`   old libwebp-mimic VP8 decoder (model of libwebp, used by `vp8-check ... libwebp`).
  - `WebP/Proofs/*.lean`       proofs that the decoder implements the spec.
  - `WebP/FFI.lean`            `@[export]` entry point for the fuzzer.
  - `Main.lean`                CLI `webp-lean <file>` (debug / corpus checks).
- `fuzz/`           — differential fuzzer (Rust, libfuzzer-sys) + corpus + tools.

## Lean <-> fuzzer contract

Lean exports (module `WebP.FFI`):

```lean
@[export webp_lean_decode_impl]
def decodeFFI (data : ByteArray) (maxPixels : UInt64) : ByteArray   -- data is OWNED (consumed)
```

The returned ByteArray is a serialized result (all integers little-endian):

```
u8  status        0 = ok, 1 = invalid bitstream/container, 2 = resource limit (skip)
-- if status != 0: remaining bytes are a UTF-8 error message
u32 canvas_width
u32 canvas_height
u8  flags         bit0 = animated, bit1 = has_alpha (VP8X alpha flag, or VP8L/ALPH present), bit2 = lossy (any VP8 data)
u16 loop_count
u32 background_color   (raw ANIM value, BGRA byte order as in file; 0 if none)
u32 num_frames
repeated num_frames times:
  u32 duration_ms   (0 for still images)
  canvas_width*canvas_height*4 bytes RGBA (fully composited canvas after this frame)
```

C symbol: `lean_object* webp_lean_decode_impl(lean_object* data, uint64_t maxPixels)`.
C init: `initialize_webp_WebP(uint8_t builtin)` (root module; Lean 4.35 naming `initialize_<pkg>_<Module_path>`),
preceded by `lean_initialize_runtime_module()` and followed by `lean_io_mark_end_initialization()`.
Static lib: `lake build WebP:static` -> `webp-lean/.lake/build/lib/libwebp_WebP.a`, plus toolchain `lib/lean/libleanrt.a libInit.a libStd.a`, plus `libc++`, `libgmp`, `libuv` from the toolchain's `lib/`.

## Metadata (`WebP.info`, module `WebP.Info`)

```lean
@[export webp_lean_info_impl]
def infoFFI (data : ByteArray) : ByteArray   -- data is OWNED (consumed)
```

Parses the container and the bitstream headers only (VP8L header; VP8 frame header + first
partition headers), never pixel data. Proven to agree with `WebP.decode` on every file the
decoder accepts (`WebP.Proofs.info_of_decode`). Result (little-endian):

```
u8  status        0 = ok, 1 = invalid (remaining bytes: UTF-8 error message)
u32 canvas_width
u32 canvas_height
u8  flags         bit0 animated, bit1 has_alpha, bit2 lossy, bit3 extended (VP8X),
                  bit4 ICCP present, bit5 EXIF present, bit6 XMP present
u16 loop_count
u32 background_color   (raw ANIM value; 0 if none)
u32 iccp_offset, u32 iccp_size   (payload offset/size in the input; 0 if absent)
u32 exif_offset, u32 exif_size
u32 xmp_offset,  u32 xmp_size
u32 num_frames         (a still image is one frame at (0,0), duration 0)
repeated num_frames times (21 bytes):
  u32 x, u32 y, u32 width, u32 height, u32 duration_ms
  u8  flags       bit0 alpha-blend, bit1 dispose to background, bit2 lossy,
                  bit3 has_alpha (lossy: ALPH chunk present; lossless: alpha_is_used hint)
```

C API wrapping it: `webp-lean/c/webp_lean.h` (`webp_lean_get_info`, `webp_lean_info_free`);
`webp-lean/c/build.sh` builds the example `webp_lean_info` (link: `libwebp_WebP.a` +
`-lleanshared`; init via `initialize_webp_WebP_FFI`).

## VP8 (lossy) Lean API (module `WebP.VP8`)

```lean
namespace WebP.VP8
structure Frame where
  width : Nat
  height : Nat
  y : ByteArray      -- luma plane, stride = width (cropped to visible size)
  u : ByteArray      -- chroma planes, stride = (width+1)/2, height (height+1)/2
  v : ByteArray
/-- Parse the VP8 frame header only (dims), RFC 6386 `vp8_parse_frame_header`. -/
def readHeader (data : ByteArray) : Except String (Nat × Nat)
/-- Full keyframe decode of a 'VP8 ' chunk payload; `= Spec.VP8.decode` (proven). -/
def decodeFrame (data : ByteArray) : Except String Frame
/-- YUV420 -> RGBA (alpha = 255) bit-exactly matching libwebp's default
    (fancy upsampling) WebPDecodeRGBA output (WebP/Spec/VP8/ToRGBA.lean). -/
def Frame.toRGBA (f : Frame) : ByteArray
```

## Oracles in the differential fuzzer

1. Lean decoder (this project) — strict spec reading.
2. libwebp simple API (`WebPDecodeRGBA`) for still images; `WebPAnimDecoder` (demux) for all files.
3. image-webp (`WebPDecoder`), default options (fancy upsampling).

Lossless pixels must agree exactly. Lossy pixels: libwebp vs Lean exactly; image-webp best-effort.
Animation alpha-blend rounding differs between libwebp and image-webp (image-webp uses
round-to-nearest /255); Lean matches libwebp.

libwebp tools (cwebp, dwebp, img2webp, webpmux, webpinfo; Release, no instrumentation): `build/libwebp-tools/`.
