#ifndef __KREMLIB_TYPES_H
#define __KREMLIB_TYPES_H

#if __STDC_VERSION__ >= 199901L /* C99 and up */
#include <inttypes.h>
#include <stdbool.h>
#else
#include <stdint.h>
typedef int bool;
#define true 1
#define false 0
#define PRId8 "hhd"
#define PRIu8 "hhu"
#define PRId16 "hd"
#define PRIu16 "hu"
#define PRIu32 "u"
#define PRId32 "d"
#define PRId64 "lu"
#define PRIu64 "lu"
#define PRIx64 "lx"
#endif

#endif /* __KREMLIB_TYPES_H */
