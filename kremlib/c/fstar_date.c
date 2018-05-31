#include "FStar_Date.h"

/******************************************************************************/
/* Implementation of FStar.Date                                               */
/******************************************************************************/

Prims_nat FStar_Date_secondsFromDawn() {
  return KRML_HOST_TIME();
}
