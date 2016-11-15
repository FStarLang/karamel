#include <time.h>
#include <stdio.h>

void StructErase_test();

void test() {
  StructErase_test();
}

int main(void) {
  int const numtests = 100;
  clock_t c1 = clock();
  test();
  {
    clock_t c2 = clock();
    double min =  ((double) c2 - c1) / CLOCKS_PER_SEC;
    int i = 1;
    for (; i < numtests; ++i) {
      c1 = clock();
      test();
      c2 = clock();
      double val =((double) c2 - c1) / CLOCKS_PER_SEC;
      min = ((val < min) ? val : min);
    }
    printf("%d tests taking at least %f s each\n", numtests, min);
    return 0;
  }
}
