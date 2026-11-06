// Example: print the metadata of WebP files via the Lean implementation.
//   webp_lean_info file.webp...            print metadata
//   webp_lean_info -t N file.webp...       also run N threads over the files (smoke test)
#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "webp_lean.h"

static uint8_t* read_file(const char* path, size_t* size) {
  FILE* f = fopen(path, "rb");
  if (!f) return NULL;
  fseek(f, 0, SEEK_END);
  long n = ftell(f);
  fseek(f, 0, SEEK_SET);
  uint8_t* buf = (uint8_t*)malloc(n > 0 ? (size_t)n : 1);
  if (buf && fread(buf, 1, (size_t)n, f) != (size_t)n) {
    free(buf);
    buf = NULL;
  }
  fclose(f);
  *size = (size_t)n;
  return buf;
}

static void print_chunk(const char* name, const webp_lean_chunk* c) {
  if (c->present) printf("  %s: offset %u, %u bytes\n", name, c->offset, c->size);
}

static int print_info(const char* path) {
  size_t size;
  uint8_t* data = read_file(path, &size);
  if (!data) {
    fprintf(stderr, "%s: cannot read\n", path);
    return 1;
  }
  webp_lean_info info;
  webp_lean_status st = webp_lean_get_info(data, size, &info);
  free(data);
  if (st != WEBP_LEAN_OK) {
    printf("%s: invalid (%d): %s\n", path, st, info.error);
    return 1;
  }
  printf("%s: %ux%u%s%s%s%s\n", path, info.width, info.height,
         info.animated ? " animated" : "", info.has_alpha ? " alpha" : "",
         info.lossy ? " lossy" : " lossless", info.extended ? " extended" : "");
  if (info.animated)
    printf("  loop_count %u, background 0x%08x\n", info.loop_count, info.background);
  print_chunk("ICCP", &info.iccp);
  print_chunk("EXIF", &info.exif);
  print_chunk("XMP ", &info.xmp);
  for (uint32_t i = 0; i < info.num_frames; i++) {
    const webp_lean_frame* f = &info.frames[i];
    printf("  frame %u: %ux%u at (%u,%u), %u ms, %s%s%s%s\n", i, f->width, f->height, f->x, f->y,
           f->duration_ms, f->lossy ? "lossy" : "lossless", f->has_alpha ? ", alpha" : "",
           info.animated ? (f->blend ? ", blend" : ", no-blend") : "",
           f->dispose ? ", dispose" : "");
  }
  webp_lean_info_free(&info);
  return 0;
}

typedef struct {
  char** paths;
  int n;
  int failures;
} job;

static void* worker(void* arg) {
  job* j = (job*)arg;
  for (int rep = 0; rep < 20; rep++)
    for (int i = 0; i < j->n; i++) {
      size_t size;
      uint8_t* data = read_file(j->paths[i], &size);
      if (!data) continue;
      webp_lean_info a, b;
      webp_lean_status sa = webp_lean_get_info(data, size, &a);
      webp_lean_status sb = webp_lean_get_info(data, size, &b);
      if (sa != sb || (sa == WEBP_LEAN_OK && (a.width != b.width || a.num_frames != b.num_frames)))
        j->failures++;
      webp_lean_info_free(&a);
      webp_lean_info_free(&b);
      free(data);
    }
  return NULL;
}

int main(int argc, char** argv) {
  int threads = 0, first = 1;
  if (argc > 2 && strcmp(argv[1], "-t") == 0) {
    threads = atoi(argv[2]);
    first = 3;
  }
  if (first >= argc) {
    fprintf(stderr, "usage: %s [-t threads] file.webp...\n", argv[0]);
    return 2;
  }
  int bad = 0;
  if (threads > 0) {
    pthread_t* t = (pthread_t*)calloc((size_t)threads, sizeof(pthread_t));
    job* jobs = (job*)calloc((size_t)threads, sizeof(job));
    for (int i = 0; i < threads; i++) {
      jobs[i] = (job){argv + first, argc - first, 0};
      pthread_create(&t[i], NULL, worker, &jobs[i]);
    }
    for (int i = 0; i < threads; i++) {
      pthread_join(t[i], NULL);
      bad += jobs[i].failures;
    }
    printf("threads: %d, inconsistent results: %d\n", threads, bad);
    free(t);
    free(jobs);
    return bad != 0;
  }
  for (int i = first; i < argc; i++) bad |= print_info(argv[i]);
  return bad;
}
