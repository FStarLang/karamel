#ifndef __KREMLIN_BUFFER_H
#define __KREMLIN_BUFFER_H

/******************************************************************************/
/* Implementing FStar.Buffer.fst                                              */
/******************************************************************************/

#define FStar_Buffer_eqb(b1, b2, n)                                            \
  (memcmp((b1), (b2), (n) * sizeof((b1)[0])) == 0)

#define FStar_Buffer_recall(x)

#endif
