#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>

long int_to_fix(long i) { return i << 16; }

void putrgb(char *buf, long stride, long x, long y, long r, long g, long b) {
  long i = 3 * (x + (y * stride));
  buf[i] = r;
  buf[i+1] = g;
  buf[i+2] = b;
}

long escape_iteration_count(long cx, long cy) {
  long zx = 0, zy = 0, zx2 = 0, zy2 = 0;
  unsigned long i = 0;
  unsigned long const iteration_limit = 256;
  while (((zx2 + zy2) < int_to_fix(4)) && (i < iteration_limit)) {
    long tx, ty;
    zx2 = (zx * zx) >> 16;
    zy2 = (zy * zy) >> 16;
    tx = cx + (zx2 - zy2);
    ty = cy + ((zx * zy) >> 15);
    i++;
    zx = tx;
    zy = ty;
  }
  return (i == iteration_limit) ? -1 : i;
}

int main(int argc, char *argv[]) {
  long const width = 1024;
  long const height = 1024;
  long y, x;
  char buf[width * height * 3];
  
  printf("P6 %d %d 255\n", width, height);
  fflush(NULL);
  for (y = 0; y < height; y++) {
    for (x = 0; x < width; x++) {
      long i = escape_iteration_count(int_to_fix(-2) + (x * (int_to_fix(4) / width)),
				      int_to_fix(-2) + (y * (int_to_fix(4) / height)));
      long b = (i == -1) ? 0 : i;
      putrgb(buf, width, x, y, b, b, b);
    }
  }
  write(1, buf, width * height * 3);
  return 0;
}
