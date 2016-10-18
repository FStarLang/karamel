#include <stdio.h>
#include <stdlib.h>
#include <inttypes.h>
#include <time.h>

// Functions for hand-written tests, no prefix
void compare_and_print(const char *txt, uint8_t *reference, uint8_t *output, int size);

// Functions for F*-written tests, exposed via TestLib.fsti
void TestLib_touch(int32_t);
void TestLib_check(int32_t, int32_t);

void *unsafe_malloc(size_t size);

void print_clock_diff(clock_t t1, clock_t t2);
