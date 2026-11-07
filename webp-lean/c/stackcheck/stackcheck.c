// Runs the Lean decoder and metadata reader on a thread with a fixed stack size.
// usage: stackcheck <stack-KiB> <decode|info> file...
#include <lean/lean.h>
#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
extern lean_object* webp_lean_decode_impl(lean_object*, uint64_t);
extern lean_object* webp_lean_info_impl(lean_object*);
extern lean_object* initialize_webp_WebP_FFI(uint8_t);
extern void lean_initialize_runtime_module(void);
extern void lean_io_mark_end_initialization(void);
static const char* g_mode; static char** g_files; static int g_n;
static void* run(void* arg) {
  (void)arg;
  for (int i = 0; i < g_n; i++) {
    FILE* f = fopen(g_files[i], "rb"); if (!f) { perror(g_files[i]); continue; }
    fseek(f, 0, SEEK_END); long n = ftell(f); fseek(f, 0, SEEK_SET);
    lean_object* ba = lean_alloc_sarray(1, n, n);
    if (fread(lean_sarray_cptr(ba), 1, n, f) != (size_t)n) abort();
    fclose(f);
    lean_object* r = strcmp(g_mode, "decode") == 0 ? webp_lean_decode_impl(ba, 1ull << 40)
                                                   : webp_lean_info_impl(ba);
    uint8_t* p = lean_sarray_cptr(r); size_t m = lean_sarray_size(r);
    if (p[0] == 0) {
      uint32_t w, h; memcpy(&w, p + 1, 4); memcpy(&h, p + 5, 4);
      printf("%s: %s ok %ux%u (%zu result bytes)\n", g_files[i], g_mode, w, h, m);
    } else printf("%s: %s status %u: %.*s\n", g_files[i], g_mode, p[0], (int)(m - 1), p + 1);
    fflush(stdout);
    lean_dec(r);
  }
  return NULL;
}
int main(int argc, char** argv) {
  if (argc < 4) return 2;
  size_t kib = strtoul(argv[1], 0, 10); g_mode = argv[2]; g_files = argv + 3; g_n = argc - 3;
  lean_initialize_runtime_module();
  lean_set_exit_on_panic(true);
  lean_object* res = initialize_webp_WebP_FFI(1);
  if (!lean_io_result_is_ok(res)) abort();
  lean_dec_ref(res); lean_io_mark_end_initialization();
  pthread_attr_t a; pthread_attr_init(&a); pthread_attr_setstacksize(&a, kib * 1024);
  pthread_t t; pthread_create(&t, &a, run, NULL); pthread_join(t, NULL);
  return 0;
}
