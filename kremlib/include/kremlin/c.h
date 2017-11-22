#ifndef __KREMLIN_C_H
#define __KREMLIN_C_H

#include <inttypes.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

/******************************************************************************/
/* Implementing C.fst                                                         */
/******************************************************************************/

/* A value for the (opaque) type C.intptr_t. For interop purposes. */
extern intptr_t nullptr;

/* For non-base types (i.e. not machine integers), KreMLin generates calls to
 * assumed equality functions. */
static inline bool __eq__C_char(char c1, char c2) {
  return c1 == c2;
}
static inline bool __neq__C_char(char c1, char c2) {
  return c1 != c2;
}

/* This one allows the user to write C.EXIT_SUCCESS. */
typedef int exit_code;

/* Now also exposed via FStar.Bytes.fst */
void print_bytes(const uint8_t *b, uint32_t len);

#endif
