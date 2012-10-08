/* Copyright (C) 2012 Tony Garnock-Jones <tonygarnockjones@gmail.com> */

/* This file is part of pi-nothing. */

/* pi-nothing is free software: you can redistribute it and/or modify */
/* it under the terms of the GNU General Public License as published */
/* by the Free Software Foundation, either version 3 of the License, */
/* or (at your option) any later version. */

/* pi-nothing is distributed in the hope that it will be useful, but */
/* WITHOUT ANY WARRANTY; without even the implied warranty of */
/* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU */
/* General Public License for more details. */

/* You should have received a copy of the GNU General Public License */
/* along with pi-nothing. If not, see <http://www.gnu.org/licenses/>. */

#include <stdlib.h>
#include <string.h>
#include <stdio.h>

#include <beaengine/BeaEngine.h>

void disassemble_block(void *start,
		       int block_length,
		       unsigned int base,
		       int is_64bit,
		       int show_binary)
{
  DISASM d;
  int finished = 0;
  intptr_t end;

  memset(&d, 0, sizeof(d)); /* important! */
  d.Options = Tabulation | ATSyntax;
  d.EIP = (intptr_t) start;
  end = d.EIP + block_length;
  d.Archi = is_64bit ? 64 : 32;

  while (d.EIP < end) {
    int len, valid;

    d.VirtualAddr = d.EIP;
    len = Disasm(&d);
    valid = (len != UNKNOWN_OPCODE) && (len != OUT_OF_BLOCK);

    printf("%08lX %-50s",
	   (unsigned long) (d.EIP - (intptr_t) start) + base,
	   valid ? d.CompleteInstr : "????????");

    if (!valid) {
      printf("\n");
      break;
    }

    {
      int i;
      for (i = 0; i < len; i++) {
	printf(" %02X", * (unsigned char *) (d.EIP + i));
      }
    }
    printf("\n");

    d.EIP += len;
  }

  fflush(NULL);
}
 
/* int main(int argc, char* argv[]) { */
/*   disassemble_block(main, 200, 1, 1); */
/*   return 0; */
/* } */
