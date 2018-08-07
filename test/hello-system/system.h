#ifdef _WIN32
#define WINVER 0x0501
#include <winsock2.h>
#include <ws2tcpip.h>
#else
#include <netdb.h>
#endif

#define null(X) 0

extern const char *null_string;
extern int ai_protocol_any;

typedef const char *string;
typedef struct addrinfo addrinfo_t;
