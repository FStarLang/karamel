#include "LowStar_Printf.h"

#define PRINT(N, T, M) \
  void LowStar_Printf_print_ ## N (T x) { \
    printf("%" M, x); \
  }

#define PRINTB(N, T, M) \
  void LowStar_Printf_print_lmbuffer_ ## N (uint32_t len, T *x) { \
    for (size_t i = 0; i < (size_t) len; ++i) \
      printf("%" M " ", x[i]); \
  }

#define PRINT2(N, T, M1, M2) \
  PRINT(N, T, M1) \
  PRINTB(N, T, M2)

PRINT2 (string, Prims_string, "s", "s")
PRINT2 (char, FStar_Char_char, PRIu32, PRIx32)
PRINT2 (u8, uint8_t, PRIu8, PRIx8)
PRINT2 (u16, uint16_t, PRIu16, PRIx16)
PRINT2 (u32, uint32_t, PRIu32, PRIx32)
PRINT2 (u64, uint64_t, PRIu64, PRIx64)
PRINT2 (i8, int8_t, PRIi8, PRIx8)
PRINT2 (i16, int16_t, PRIi16, PRIx16)
PRINT2 (i32, int32_t, PRIi32, PRIx32)
PRINT2 (i64, int64_t, PRIi64, PRIx64)

void LowStar_Printf_print_bool(bool b) {
  printf("%s", b ? "true" : "false");
}

void LowStar_Printf_print_lmbuffer_bool(uint32_t len, bool *x) {
  for (size_t i = 0; i < (size_t) len; ++i)
    printf("%s ", x[i] ? "true" : "false");
}

