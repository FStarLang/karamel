#include <stdio.h>
#include <stdlib.h>

#include "Server.h"

int main() {
  uint32_t state = 0;
  char response[2048];
  uint32_t n;
  const char *request1 = "GET / HTTP/1.1\r\n";
  n = server(&state, (char *) request1, response);
  response[n] = 0;
  printf(">>> %s\n%s\n", request1, response);
  const char *request2 = "GET /stats HTTP/1.1\r\n";
  n = server(&state, (char *) request2, response);
  response[n] = 0;
  printf(">>> %s\n%s\n", request2, response);
  const char *request3 = "GET /notfound HTTP/1.1\r\n";
  n = server(&state, (char *) request3, response);
  response[n] = 0;
  printf(">>> %s\n%s\n", request3, response);
  return EXIT_SUCCESS;
}
