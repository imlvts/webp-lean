// C API for the Lean WebP implementation: file metadata without decoding pixel data.
//
// Backed by `WebP.info` (webp-lean/WebP/Info.lean), exported as `webp_lean_info_impl`.
// Proven in WebP/Proofs/Info.lean: whenever the Lean decoder accepts a file, this returns the
// same canvas size, flags, loop count, background color and frame durations. A file whose
// pixel data is corrupt can still have valid metadata.
//
// Link: webp_lean.c + webp-lean/.lake/build/lib/libwebp_WebP.a + the Lean runtime (see
// webp-lean/c/build.sh, which uses `leanc`).
#ifndef WEBP_LEAN_H
#define WEBP_LEAN_H

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

typedef enum {
  WEBP_LEAN_OK = 0,
  WEBP_LEAN_INVALID = 1,    // not a well-formed WebP file (message in info->error)
  WEBP_LEAN_NOMEM = 3,      // allocation failure in the C wrapper
  WEBP_LEAN_INTERNAL = 4,   // unexpected result from the Lean side (bug)
} webp_lean_status;

// A top-level chunk: payload offset in the input buffer and payload size.
typedef struct {
  uint8_t present;
  uint32_t offset;
  uint32_t size;
} webp_lean_chunk;

// One frame. A still image is reported as a single frame at (0, 0) with duration 0.
typedef struct {
  uint32_t x, y;            // offset on the canvas
  uint32_t width, height;
  uint32_t duration_ms;
  uint8_t blend;            // 1 = alpha-blend onto the canvas, 0 = overwrite
  uint8_t dispose;          // 1 = dispose to background color after display
  uint8_t lossy;            // 1 = 'VP8 ' bitstream, 0 = 'VP8L'
  uint8_t has_alpha;        // lossy: 'ALPH' chunk present; lossless: alpha_is_used hint
} webp_lean_frame;

typedef struct {
  uint32_t width, height;   // canvas size (image size for still images)
  uint8_t animated;
  uint8_t has_alpha;        // VP8X alpha flag; VP8L alpha_is_used for simple lossless files
  uint8_t lossy;            // some image data is lossy
  uint8_t extended;         // has a 'VP8X' chunk
  uint16_t loop_count;      // 0 = infinite; 0 for still images
  uint32_t background;      // raw 'ANIM' color, bytes B,G,R,A as little-endian u32
  webp_lean_chunk iccp;     // first 'ICCP' chunk (extended files only)
  webp_lean_chunk exif;     // first 'EXIF' chunk (extended files only)
  webp_lean_chunk xmp;      // first 'XMP ' chunk (extended files only)
  uint32_t num_frames;
  webp_lean_frame* frames;  // num_frames entries; release with webp_lean_info_free
  char error[256];          // NUL-terminated message when the status is not WEBP_LEAN_OK
} webp_lean_info;

// Initializes the Lean runtime. Optional (the functions below call it); thread-safe.
void webp_lean_init(void);

// Reads the metadata of the WebP file `data[0..size)`. `data` is not retained.
// On WEBP_LEAN_OK, `info` is filled in and must be released with webp_lean_info_free.
// Otherwise `info->error` holds a message and `info->frames` is NULL.
webp_lean_status webp_lean_get_info(const uint8_t* data, size_t size, webp_lean_info* info);

// Frees `info->frames` (safe to call on any result of webp_lean_get_info).
void webp_lean_info_free(webp_lean_info* info);

#ifdef __cplusplus
}
#endif

#endif  // WEBP_LEAN_H
