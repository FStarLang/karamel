#include "kremlib.h"
#include "kremstr.h"

#include <time.h>

/******************************************************************************/
/* Implementation of FStar.Date                                               */
/******************************************************************************/

/* FStar_Date.h has all the extern val's. This is just the implementation. */

Prims_nat FStar_Date_secondsFromDawn() {
  return (Prims_nat) time(NULL);
}
