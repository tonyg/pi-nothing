#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>

void putrgb(long r, long g, long b) {
  unsigned char buf[3];
  buf[0] = r;
  buf[1] = g;
  buf[2] = b;
  write(1, buf, 3);
}

double escape_iteration_count(double cx, double cy) {
  double zx = 0, zy = 0, zx2 = 0, zy2 = 0;
  unsigned long i = 0;
  unsigned long const iteration_limit = 256;
  while (((zx2 + zy2) < 4.0) && (i < iteration_limit)) {
    double tx, ty;
    zx2 = (zx * zx);
    zy2 = (zy * zy);
    tx = cx + (zx2 - zy2);
    ty = cy + (2 * zx * zy);
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
  
  printf("P6 %d %d 255\n", width, height);
  fflush(NULL);
  for (y = 0; y < height; y++) {
    for (x = 0; x < width; x++) {
      long i = escape_iteration_count(-2.0 + (x * (4.0 / width)),
				      -2.0 + (y * (4.0 / height)));
      long b = (i == -1) ? 0 : i;
      putrgb(b, b, b);
    }
  }
  return 0;
}
