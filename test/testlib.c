#include "testlib.h"

void compare_and_print(const char *txt, uint8_t *reference, uint8_t *output, int size) {
  char str[2*size + 1];
  for (int i = 0; i < size; ++i)
    sprintf(str+2*i, "%02x", output[i]);
  str[2*size] = '\0';
  printf("[aead] output %s is %s\n", txt, str);

  for (int i = 0; i < size; ++i) {
    if (output[i] != reference[i]) {
      fprintf(stderr, "[aead] reference %s and expected %s differ at byte %d\n", txt, txt, i);
      exit(EXIT_FAILURE);
    }
  }

  printf("[aead] %s is a success\n", txt);
}
