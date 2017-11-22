#ifndef __KREMLIN_HEAP_H
#define __KREMLIN_HEAP_H

/******************************************************************************/
/* Stubs to ease compilation of non-Low* code                                 */
/******************************************************************************/

/* Some types that KreMLin has no special knowledge of; many of them appear in
 * signatures of ghost functions, meaning that it suffices to give them (any)
 * definition. */
typedef void *FStar_Monotonic_HyperStack_mem, *Prims_prop,
        *FStar_Monotonic_HyperHeap_rid;

/* Stubs to make ST happy. Important note: you must generate a use of the macro
 * argument, otherwise, you may have FStar_ST_recall(f) as the only use of f;
 * KreMLin will think that this is a valid use, but then the C compiler, after
 * macro expansion, will error out. */
#define FStar_HyperHeap_root 0
#define FStar_HyperStack_is_eternal_color(x) 0
#define FStar_Monotonic_HyperHeap_root 0
#define FStar_HyperStack_ST_new_region(x) 0

#define FStar_HyperStack_ST_recall(x)                                          \
  do {                                                                         \
    (void)(x);                                                                 \
  } while (0)

#define FStar_HyperStack_ST_recall_region(x)                                   \
  do {                                                                         \
    (void)(x);                                                                 \
  } while (0)

#define FStar_Monotonic_RRef_m_recall(x1)                                      \
  do {                                                                         \
    (void)(x1);                                                                \
  } while (0)

#define FStar_Monotonic_RRef_m_write(x1, x2, x3, x4, x5)                       \
  do {                                                                         \
    (void)(x1);                                                                \
    (void)(x2);                                                                \
    (void)(x3);                                                                \
    (void)(x4);                                                                \
    (void)(x5);                                                                \
  } while (0)

#endif
