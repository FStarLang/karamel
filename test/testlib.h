#include <stdio.h>
#include <stdlib.h>
#include <inttypes.h>

// Functions for hand-written tests, no prefix
void compare_and_print(const char *txt, uint8_t *reference, uint8_t *output, int size);
void compare_and_print2(uint8_t *reference, uint8_t *output, int size);

// Functions for F*-written tests, exposed via TestLib.fsti
void TestLib_touch(int32_t);
void TestLib_check(int32_t, int32_t);
