// C wrapper around the Lean export `webp_lean_info_impl` (wire format: ../../DESIGN.md).
#include "webp_lean.h"

#include <lean/lean.h>
#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

extern lean_object* webp_lean_info_impl(lean_object* data);  // consumes data
extern lean_object* initialize_webp_WebP_FFI(uint8_t builtin);
extern void lean_initialize_runtime_module(void);
extern void lean_io_mark_end_initialization(void);

static pthread_once_t g_once = PTHREAD_ONCE_INIT;

static void init_once(void) {
  lean_initialize_runtime_module();
  // No reachable Lean code panics; if one ever does, it is a bug: abort instead of
  // continuing with a default value.
  lean_set_panic_messages(true);
  lean_set_exit_on_panic(true);
  lean_object* res = initialize_webp_WebP_FFI(1);
  if (!lean_io_result_is_ok(res)) {
    lean_io_result_show_error(res);
    abort();
  }
  lean_dec_ref(res);
  lean_io_mark_end_initialization();
}

void webp_lean_init(void) { pthread_once(&g_once, init_once); }

typedef struct {
  const uint8_t* p;
  size_t n;
  size_t pos;
  int ok;
} reader;

static uint32_t rd(reader* r, int bytes) {
  if (r->pos + bytes > r->n) {
    r->ok = 0;
    return 0;
  }
  uint32_t v = 0;
  for (int i = 0; i < bytes; i++) v |= (uint32_t)r->p[r->pos + i] << (8 * i);
  r->pos += bytes;
  return v;
}

static void set_error(webp_lean_info* info, const char* msg, size_t len) {
  if (len >= sizeof(info->error)) len = sizeof(info->error) - 1;
  memcpy(info->error, msg, len);
  info->error[len] = 0;
}

static void read_chunk(reader* r, webp_lean_chunk* c, int present) {
  c->offset = rd(r, 4);
  c->size = rd(r, 4);
  c->present = (uint8_t)present;
}

static webp_lean_status parse(const uint8_t* p, size_t n, webp_lean_info* info) {
  if (n == 0) {
    set_error(info, "empty result", 12);
    return WEBP_LEAN_INTERNAL;
  }
  if (p[0] != 0) {
    set_error(info, (const char*)p + 1, n - 1);
    return p[0] == 1 ? WEBP_LEAN_INVALID : WEBP_LEAN_INTERNAL;
  }
  reader r = {p, n, 1, 1};
  info->width = rd(&r, 4);
  info->height = rd(&r, 4);
  uint32_t flags = rd(&r, 1);
  info->animated = flags & 1;
  info->has_alpha = (flags >> 1) & 1;
  info->lossy = (flags >> 2) & 1;
  info->extended = (flags >> 3) & 1;
  info->loop_count = (uint16_t)rd(&r, 2);
  info->background = rd(&r, 4);
  read_chunk(&r, &info->iccp, (flags >> 4) & 1);
  read_chunk(&r, &info->exif, (flags >> 5) & 1);
  read_chunk(&r, &info->xmp, (flags >> 6) & 1);
  info->num_frames = rd(&r, 4);
  const size_t frame_bytes = 21;
  if (!r.ok || info->num_frames > (n - r.pos) / frame_bytes) {
    set_error(info, "truncated result", 16);
    return WEBP_LEAN_INTERNAL;
  }
  info->frames = (webp_lean_frame*)calloc(info->num_frames ? info->num_frames : 1,
                                          sizeof(webp_lean_frame));
  if (info->frames == NULL) {
    set_error(info, "out of memory", 13);
    return WEBP_LEAN_NOMEM;
  }
  for (uint32_t i = 0; i < info->num_frames; i++) {
    webp_lean_frame* f = &info->frames[i];
    f->x = rd(&r, 4);
    f->y = rd(&r, 4);
    f->width = rd(&r, 4);
    f->height = rd(&r, 4);
    f->duration_ms = rd(&r, 4);
    uint32_t ff = rd(&r, 1);
    f->blend = ff & 1;
    f->dispose = (ff >> 1) & 1;
    f->lossy = (ff >> 2) & 1;
    f->has_alpha = (ff >> 3) & 1;
  }
  return WEBP_LEAN_OK;
}

webp_lean_status webp_lean_get_info(const uint8_t* data, size_t size, webp_lean_info* info) {
  memset(info, 0, sizeof(*info));
  webp_lean_init();
  lean_object* ba = lean_alloc_sarray(1, size, size);
  if (size) memcpy(lean_sarray_cptr(ba), data, size);
  lean_object* res = webp_lean_info_impl(ba);  // consumes ba
  webp_lean_status st = parse(lean_sarray_cptr(res), lean_sarray_size(res), info);
  lean_dec(res);
  if (st != WEBP_LEAN_OK) webp_lean_info_free(info);
  return st;
}

void webp_lean_info_free(webp_lean_info* info) {
  free(info->frames);
  info->frames = NULL;
  info->num_frames = 0;
}
