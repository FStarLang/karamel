#ifndef __KREMLIN_KREMLIB_H
#define __KREMLIN_KREMLIB_H

#include <inttypes.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

/* For very old versions of GCC */
#ifdef __GNUC__
#  define inline __inline__
#endif

/* If some globals need to be initialized before the main, then kremlin will
 * generate and try to link last a function with this type: */
void kremlinit_globals(void);


/******************************************************************************/
/* Opting out of dependencies on the C standard library                       */
/******************************************************************************/

/* For "bare" targets that do not have a C stdlib, the user might want to use
 * [-add-early-include '"mydefinitions.h"'] and override these. */
#ifndef KRML_HOST_PRINTF
#  define KRML_HOST_PRINTF printf
#endif

#ifndef KRML_HOST_EXIT
#  define KRML_HOST_EXIT exit
#endif

#ifndef KRML_HOST_MALLOC
#  define KRML_HOST_MALLOC malloc
#endif


/******************************************************************************/
/* The bare-bones macros that almost every KreMLin program will need          */
/******************************************************************************/

/* In statement position, exiting is easy. */
#define KRML_EXIT                                                              \
  do {                                                                         \
    KRML_HOST_PRINTF("Unimplemented function at %s:%d\n", __FILE__, __LINE__); \
    KRML_HOST_EXIT(254);                                                       \
  } while (0)

/* In expression position, use the comma-operator and a malloc to return an
 * expression of the right size. KreMLin passes t as the parameter to the macro.
 */
#define KRML_EABORT(t, msg)                                                    \
  (KRML_HOST_PRINTF("KreMLin abort at %s:%d\n%s\n", __FILE__, __LINE__, msg),  \
   KRML_HOST_EXIT(255), *((t *)KRML_HOST_MALLOC(sizeof(t))))

/* In FStar.Buffer.fst, the size of arrays is uint32_t, but it's a number of
 * *elements*. Do an ugly, run-time check (some of which KreMLin can eliminate).
 */
#define KRML_CHECK_SIZE(elt, size)                                             \
  if (((size_t)size) > SIZE_MAX / sizeof(elt)) {                               \
    KRML_HOST_PRINTF(                                                          \
        "Maximum allocatable size exceeded, aborting before overflow at "      \
        "%s:%d\n",                                                             \
        __FILE__, __LINE__);                                                   \
    KRML_HOST_EXIT(253);                                                       \
  }

#endif     /* __KREMLIN_KREMLIB_H */
