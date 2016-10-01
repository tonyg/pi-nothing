#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <stdint.h>

static char const *legalchars = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ_$";

unsigned long
elf_hash(const unsigned char *name)
{
  unsigned long h = 0, g;
  while (*name)
    {
      h = (h << 4) + *name++;
      if (g = (h & 0xf0000000))
        h ^= g >> 24;
      h &= ~g;
    }
  return h;
}

#define DIE_UNLESS(x) if (!(x)) { perror(#x); abort(); }

int main(int argc, char *argv[]) {
  int const num_legalchars = strlen(legalchars);
  FILE *randomf = fopen("/dev/urandom", "r");
  char identifier[256];
  int remaining = 0;

  DIE_UNLESS(argc == 2);
  remaining = atoi(argv[1]);
  DIE_UNLESS(remaining > 0);

  DIE_UNLESS(randomf != NULL);

  for (; remaining > 0; remaining--) {
    uint8_t identifier_length = 0;

    while (identifier_length == 0) {
      DIE_UNLESS(fread(&identifier_length, 1, 1, randomf) == 1);
    }

    for (int pos = 0; pos < identifier_length; pos++) {
      uint8_t alea = num_legalchars;
      while (alea >= num_legalchars) {
        DIE_UNLESS(fread(&alea, 1, 1, randomf) == 1);
      }
      identifier[pos] = legalchars[alea];
    }
    identifier[identifier_length] = '\0';

    printf("(#\"%s\" %lu)\n", identifier, elf_hash(identifier));
  }

  fclose(randomf);
  return 0;
}
