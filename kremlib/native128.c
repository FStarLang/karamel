FStar_UInt128_t FStar_UInt128_add(FStar_UInt128_t x, FStar_UInt128_t y) {
  return x + y;
}

FStar_UInt128_t FStar_UInt128_add_mod(FStar_UInt128_t x, FStar_UInt128_t y) {
  return x + y;
}

FStar_UInt128_t FStar_UInt128_sub(FStar_UInt128_t x, FStar_UInt128_t y) {
  return x - y;
}

FStar_UInt128_t FStar_UInt128_sub_mod(FStar_UInt128_t x, FStar_UInt128_t y) {
  return x - y;
}

FStar_UInt128_t FStar_UInt128_logand(FStar_UInt128_t x, FStar_UInt128_t y) {
  return x & y;
}

FStar_UInt128_t FStar_UInt128_logor(FStar_UInt128_t x, FStar_UInt128_t y) {
  return x | y;
}

FStar_UInt128_t FStar_UInt128_logxor(FStar_UInt128_t x, FStar_UInt128_t y) {
  return x ^ y;
}

FStar_UInt128_t FStar_UInt128_lognot(FStar_UInt128_t x) { return ~x; }

/* y >= 128 should never happen */
FStar_UInt128_t FStar_UInt128_shift_left(FStar_UInt128_t x, FStar_UInt32_t y) {
  return x << y;
}

FStar_UInt128_t FStar_UInt128_shift_right(FStar_UInt128_t x, FStar_UInt32_t y) {
  return x >> y;
}

/* Conversions */
FStar_UInt128_t FStar_Int_Cast_uint64_to_uint128(uint64_t x) {
  return (FStar_UInt128_t)x;
}

uint64_t FStar_Int_Cast_uint128_to_uint64(FStar_UInt128_t x) {
  return (uint64_t)x;
}

FStar_UInt128_t FStar_UInt128_eq_mask(FStar_UInt128_t x, FStar_UInt128_t y) {
  uint64_t mask =
      FStar_UInt64_eq_mask((uint64_t)(x >> 64), (uint64_t)(y >> 64)) &
      FStar_UInt64_eq_mask(x, y);
  return ((FStar_UInt128_t)mask) << 64 | mask;
}

FStar_UInt128_t FStar_UInt128_gte_mask(FStar_UInt128_t x, FStar_UInt128_t y) {
  uint64_t mask =
      (FStar_UInt64_gte_mask(x >> 64, y >> 64) &
       ~(FStar_UInt64_eq_mask(x >> 64, y >> 64))) |
      (FStar_UInt64_eq_mask(x >> 64, y >> 64) & FStar_UInt64_gte_mask(x, y));
  return ((FStar_UInt128_t)mask) << 64 | mask;
}

FStar_UInt128_t FStar_UInt128_mul_wide(uint64_t x, uint64_t y) {
  return (FStar_UInt128_t)x * y;
}

bool FStar_UInt128_op_Greater_Greater_Hat(FStar_UInt128_t x, FStar_UInt32_t y) {
  return x >> y;
}

