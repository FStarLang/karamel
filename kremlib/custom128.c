/* From OPENSSL's code base */
#define CONSTANT_TIME_CARRY(a, b)                                              \
  ((a ^ ((a ^ b) | ((a - b) ^ b))) >> (sizeof(a) * 8 - 1))

DECL_RET_BY_VAL
(
 FStar_UInt128_t,
 FStar_UInt128_add,
 DECL_BY_VAL(FStar_UInt128_t,x),
 DECL_BY_VAL(FStar_UInt128_t,y)
 ) {
  DECL_LOCAL(FStar_UInt128_t,r);
  LOCAL_FIELD(r,low) = LOCAL_FIELD(x,low) + LOCAL_FIELD(y,low);
  LOCAL_FIELD(r,high) = LOCAL_FIELD(x,high) + LOCAL_FIELD(y,high) + CONSTANT_TIME_CARRY(LOCAL_FIELD(r,low), LOCAL_FIELD(y,low));
  RET_LOCAL(FStar_UInt128_t, r);
}

DECL_RET_BY_VAL
(
 FStar_UInt128_t,
 FStar_UInt128_add_mod,
 DECL_BY_VAL(FStar_UInt128_t,x),
 DECL_BY_VAL(FStar_UInt128_t,y)
 ) {
  RET_CALL_BY_VAL(FStar_UInt128_add, PASS_LOCAL(FStar_UInt128_t,x), PASS_LOCAL(FStar_UInt128_t,y));
}

DECL_RET_BY_VAL
(
 FStar_UInt128_t,
 FStar_UInt128_sub,
 DECL_BY_VAL(FStar_UInt128_t,x),
 DECL_BY_VAL(FStar_UInt128_t,y)
 ) {
  DECL_LOCAL(FStar_UInt128_t,r);
  LOCAL_FIELD(r,low) = LOCAL_FIELD(x,low) - LOCAL_FIELD(y,low);
  LOCAL_FIELD(r,high) = LOCAL_FIELD(x,high) - LOCAL_FIELD(y,high) - CONSTANT_TIME_CARRY(LOCAL_FIELD(x,low), LOCAL_FIELD(r,low));
  RET_LOCAL(FStar_UInt128_t, r);
}

DECL_RET_BY_VAL
(
 FStar_UInt128_t,
 FStar_UInt128_sub_mod,
 DECL_BY_VAL(FStar_UInt128_t,x),
 DECL_BY_VAL(FStar_UInt128_t,y)
 ) {
  RET_CALL_BY_VAL(FStar_UInt128_sub, PASS_LOCAL(FStar_UInt128_t,x), PASS_LOCAL(FStar_UInt128_t,y));
}

DECL_RET_BY_VAL
(
 FStar_UInt128_t,
 FStar_UInt128_logand,
 DECL_BY_VAL(FStar_UInt128_t,x),
 DECL_BY_VAL(FStar_UInt128_t,y)
 ) {
  DECL_LOCAL(FStar_UInt128_t,r);
  LOCAL_FIELD(r,high) = LOCAL_FIELD(x,high) & LOCAL_FIELD(y,high);
  LOCAL_FIELD(r,low) = LOCAL_FIELD(x,low) & LOCAL_FIELD(y,low);
  RET_LOCAL(FStar_UInt128_t, r);
}

DECL_RET_BY_VAL
(
 FStar_UInt128_t,
 FStar_UInt128_logor,
 DECL_BY_VAL(FStar_UInt128_t,x),
 DECL_BY_VAL(FStar_UInt128_t,y)
 ) {
  DECL_LOCAL(FStar_UInt128_t,r);
  LOCAL_FIELD(r,high) = LOCAL_FIELD(x,high) | LOCAL_FIELD(y,high);
  LOCAL_FIELD(r,low) = LOCAL_FIELD(x,low) | LOCAL_FIELD(y,low);
  RET_LOCAL(FStar_UInt128_t, r);
}

DECL_RET_BY_VAL
(
 FStar_UInt128_t,
 FStar_UInt128_logxor,
 DECL_BY_VAL(FStar_UInt128_t,x),
 DECL_BY_VAL(FStar_UInt128_t,y)
 ) {
  DECL_LOCAL(FStar_UInt128_t,r);
  LOCAL_FIELD(r,high) = LOCAL_FIELD(x,high) ^ LOCAL_FIELD(y,high);
  LOCAL_FIELD(r,low) = LOCAL_FIELD(x,low) ^ LOCAL_FIELD(y,low);
  RET_LOCAL(FStar_UInt128_t, r);
}

DECL_RET_BY_VAL
(
 FStar_UInt128_t,
 FStar_UInt128_lognot,
 DECL_BY_VAL(FStar_UInt128_t,x)
 ) {
  DECL_LOCAL(FStar_UInt128_t,r);
  LOCAL_FIELD(r,high) = ~(LOCAL_FIELD(x,high));
  LOCAL_FIELD(r,low) = ~(LOCAL_FIELD(x,low));
  RET_LOCAL(FStar_UInt128_t, r);
}

/* y >= 128 should never happen */
DECL_RET_BY_VAL
(
 FStar_UInt128_t,
 FStar_UInt128_shift_left,
 DECL_BY_VAL(FStar_UInt128_t,x),
 FStar_UInt32_t y
 ) {
  DECL_LOCAL(FStar_UInt128_t,r);
  uint64_t mask_64_m = (((int64_t)y - 64) >> 63);
  uint64_t mask_64_p = ((64 - (int64_t)y) >> 63);
  uint64_t mask_64 = ~(mask_64_m | mask_64_p);
  uint64_t mask_0 = ((int64_t)y - 1) >> 63;
  LOCAL_FIELD(r,low) = mask_64_m & (LOCAL_FIELD(x,low) << y);
  LOCAL_FIELD(r,high) = (mask_64_m & ((LOCAL_FIELD(x,high) << y) | ((~mask_0) & (LOCAL_FIELD(x,low) >> (64 - y))))) |
    ((mask_64_p) & (LOCAL_FIELD(x,low) << (y - 64))) | (mask_64 & LOCAL_FIELD(x,low));
  RET_LOCAL(FStar_UInt128_t, r);
}

DECL_RET_BY_VAL
(
 FStar_UInt128_t,
 FStar_UInt128_shift_right,
 DECL_BY_VAL(FStar_UInt128_t,x),
 FStar_UInt32_t y
 ) {
  DECL_LOCAL(FStar_UInt128_t,r);
  uint64_t mask_64_m = (((int64_t)y - 64) >> 63);
  uint64_t mask_64_p = ((64 - (int64_t)y) >> 63);
  uint64_t mask_64 = ~(mask_64_m | mask_64_p);
  uint64_t mask_0 = ((int64_t)y - 1) >> 63;
  LOCAL_FIELD(r,high) = mask_64_m & (LOCAL_FIELD(x,high) >> y);
  LOCAL_FIELD(r,low) = (mask_64_m & ((LOCAL_FIELD(x,low) >> y) | ((~mask_0) & (LOCAL_FIELD(x,high) << (64 - y))))) |
    ((mask_64_p) & (LOCAL_FIELD(x,high) >> (y - 64))) | (mask_64 & LOCAL_FIELD(x,high));
  RET_LOCAL(FStar_UInt128_t,r);
}

/* Conversions */
DECL_RET_BY_VAL
(
 FStar_UInt128_t,
 FStar_Int_Cast_uint64_to_uint128,
 uint64_t x
) {
  RET_INIT(FStar_UInt128_t, high, UINT64_C(0), low, x);
  //  return (FStar_UInt128_t){.high = UINT64_C(0), .low = x};
}

uint64_t FStar_Int_Cast_uint128_to_uint64(DECL_BY_VAL(FStar_UInt128_t,x)) { return LOCAL_FIELD(x,low); }

DECL_RET_BY_VAL
(
 FStar_UInt128_t,
 FStar_UInt128_eq_mask,
 DECL_BY_VAL(FStar_UInt128_t,x),
 DECL_BY_VAL(FStar_UInt128_t,y)
 ) {
  RET_INIT(FStar_UInt128_t, low, FStar_UInt64_eq_mask(LOCAL_FIELD(x,low), LOCAL_FIELD(y,low)),
	   high, FStar_UInt64_eq_mask(LOCAL_FIELD(x,high), LOCAL_FIELD(y,high)));
}

DECL_RET_BY_VAL
(
 FStar_UInt128_t,
 FStar_UInt128_gte_mask,
 DECL_BY_VAL(FStar_UInt128_t,x),
 DECL_BY_VAL(FStar_UInt128_t,y)
 ) {
  uint64_t mask = (FStar_UInt64_gte_mask(LOCAL_FIELD(x,high), LOCAL_FIELD(y,high)) &
                   ~(FStar_UInt64_eq_mask(LOCAL_FIELD(x,high), LOCAL_FIELD(y,high)))) |
    (FStar_UInt64_eq_mask(LOCAL_FIELD(x,high), LOCAL_FIELD(y,high)) &
     FStar_UInt64_gte_mask(LOCAL_FIELD(x,low), LOCAL_FIELD(y,low)));
  RET_INIT(FStar_UInt128_t, high, mask, low, mask);
}

DECL_RET_BY_VAL
(
 FStar_UInt128_t,
 FStar_UInt128_mul_wide,
 uint64_t x,
 uint64_t y
) {
  uint64_t u1, v1, t, w3, k, w1;
  u1 = (x & 0xffffffff);
  v1 = (y & 0xffffffff);
  t = (u1 * v1);
  w3 = (t & 0xffffffff);
  k = (t >> 32);
  x >>= 32;
  t = (x * v1) + k;
  k = (t & 0xffffffff);
  w1 = (t >> 32);
  y >>= 32;
  t = (u1 * y) + k;
  k = (t >> 32);
  RET_INIT(FStar_UInt128_t, high, (x * y) + w1 + k, low, (t << 32) + w3);
}

bool FStar_UInt128_op_Greater_Greater_Hat
(
 DECL_BY_VAL(FStar_UInt128_t,x),
 FStar_UInt32_t y
) {
  exit(254);
}
