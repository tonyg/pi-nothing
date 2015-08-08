/* attach-trailer.c - Constructs a Raspberry Pi trailer to permit devicetree boots */
/* Copyright (C) 2015 Tony Garnock-Jones <tonyg@leastfixedpoint.com>

   This program is free software; you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation; either version 3 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.
*/

/*
 * Based on lessons gleaned from reading a perl script, mkknlimg,
 * https://github.com/raspberrypi/tools/blob/master/mkimage/mkknlimg
 * and translating it into the context of my own small baremetal OS project.
 *
 * The mkknlimg script has the following copyright and licence notice attached to it:
   # ----------------------------------------------------------------------
   # mkknlimg by Phil Elwell for Raspberry Pi
   # based on extract-ikconfig by Dick Streefland
   #
   # (c) 2009,2010 Dick Streefland <dick@streefland.net>
   # (c) 2014,2015 Raspberry Pi (Trading) Limited <info@raspberrypi.org>
   #
   # Licensed under the terms of the GNU General Public License.
   # ----------------------------------------------------------------------
 */

#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <stdint.h>

static size_t copy_kernel(void) {
  unsigned char buf[1024];
  size_t n;
  size_t count = 0;

  while ((n = fread(buf, 1, sizeof(buf), stdin)) > 0) {
    if (fwrite(buf, 1, n, stdout) != n) {
      perror("copy_kernel write");
      exit(1);
    }
    count += n;
  }

  if (!feof(stdin) || ferror(stdin)) {
    perror("copy_kernel read");
    exit(1);
  }

  fflush(stdout);

  return count;
}

static size_t pad_to_four(size_t n) {
  size_t count = 0;
  while (n & 3) {
    fputc(0, stdout);
    n++;
    count++;
  }
  return count;
}

static size_t write_le_uint32(uint32_t v) {
  size_t count;
  for (count = 0; count < 4; count++) {
    if (fputc(v & 0xff, stdout) == EOF) {
      perror("write_le_uint32 fputc");
      exit(1);
    }
    v >>= 8;
  }
  return count;
}

static size_t write_trailer_field(char const *label, char const *data, size_t length) {
  size_t count = fwrite(data, 1, length, stdout);
  if (count != length) {
    perror("write_trailer_field fwrite data");
    exit(1);
  }
  count += pad_to_four(length);
  count += write_le_uint32(length);
  if (fwrite(label, 1, 4, stdout) != 4) {
    perror("write_trailer_field fwrite label");
    exit(1);
  }
  count += 4;
  return count;
}

int main(int argc, char *argv[]) {
  size_t trailer_size = 0;
  char const *kernel_version = (argc >= 2 ? argv[1] : "unknown");

  pad_to_four(copy_kernel());

  trailer_size += write_trailer_field("\0\0\0\0", "", 0);
  trailer_size += write_trailer_field("283x", "\0\0\0\0", 4);
  trailer_size += write_trailer_field("DDTK", "\0\0\0\0", 4);
  trailer_size += write_trailer_field("DTOK", "\1\0\0\0", 4); /* we want devicetree */
  trailer_size += write_trailer_field("KVer", kernel_version, strlen(kernel_version));

  write_le_uint32(trailer_size + 8);
  write_le_uint32(4);
  if (fwrite("RPTL", 1, 4, stdout) != 4) {
    perror("write of RPTL label");
    exit(1);
  }

  return 0;
}
