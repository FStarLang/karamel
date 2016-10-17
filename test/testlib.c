#include "testlib.h"

void compare_and_print(const char *txt, uint8_t *reference, uint8_t *output, int size) {
  char *str = malloc(2*size + 1);
  char *str2 = malloc(2*size + 1);
  for (int i = 0; i < size; ++i) {
    sprintf(str+2*i, "%02x", output[i]);
    sprintf(str2+2*i, "%02x", reference[i]);
  }
  str[2*size] = '\0';
  printf("[test] expected output %s is %s\n", txt, str2);
  printf("[test] computed output %s is %s\n", txt, str);

  for (int i = 0; i < size; ++i) {
    if (output[i] != reference[i]) {
      fprintf(stderr, "[test] reference %s and expected %s differ at byte %d\n", txt, txt, i);
      exit(EXIT_FAILURE);
    }
  }

  printf("[test] %s is a success\n", txt);

  free(str);
  free(str2);
}

void TestLib_touch(int32_t x) {
}

void TestLib_check(int32_t x, int32_t y) {
  if (x != y) {
    printf("Test check failure: %"PRId32" != %"PRId32"\n", x, y);
    exit(253);
  }
}
