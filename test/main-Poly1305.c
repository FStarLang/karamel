#include "krmllib.h"
#include "testlib.h"
#include "Crypto_Symmetric_Poly1305.h"

uint8_t key[] = {
  0x85, 0xd6, 0xbe, 0x78, 0x57, 0x55, 0x6d, 0x33, 0x7f, 0x44, 0x52, 0xfe, 0x42,
  0xd5, 0x06, 0xa8, 0x01, 0x03, 0x80, 0x8a, 0xfb, 0x0d, 0xb2, 0xfd, 0x4a, 0xbf,
  0xf6, 0xaf, 0x41, 0x49, 0xf5, 0x1b
};
uint8_t *msg = (uint8_t*)"Cryptographic Forum Research Group";
uint8_t expected_hash[] = {
  0xa8, 0x06, 0x1d, 0xc1, 0x30, 0x51, 0x36, 0xc6, 0xc2, 0x2b, 0x8b, 0xaf, 0x0c,
  0x01, 0x27, 0xa9
};

#define HASH_SIZE 16

int main() {
  uint8_t hash[HASH_SIZE];
  Crypto_Symmetric_Poly1305_poly1305_mac(hash, msg, 34, key);
  TestLib_compare_and_print("mac", hash, expected_hash, HASH_SIZE);
  return EXIT_SUCCESS;
}
