#include <inttypes.h>

void Chacha_chacha20_encrypt(
  uint8_t *ciphertext,
  uint8_t *key,
  uint32_t counter,
  uint8_t *nonce,
  uint8_t *plaintext,
  uint32_t len
);
