#include <stdio.h>
#include <stdlib.h>
#include <inttypes.h>
#include <time.h>

// This file has a hand-written .h file so that test files written in C (e.g.
// main-Poly1305.c) can use the functions from this file too (e.g.
// [compare_and_print]).

// Functions for F*-written tests, exposed via TestLib.fsti
void TestLib_touch(int32_t);
void TestLib_check(int32_t, int32_t);

// These functions are also called by HACL
void TestLib_compare_and_print(const char *txt, uint8_t *reference, uint8_t *output, int size);

void *TestLib_unsafe_malloc(size_t size);
void TestLib_print_clock_diff(clock_t t1, clock_t t2);

#if defined(__i386__)

static __inline__ unsigned long long rdtsc(void)
{
  unsigned long long int x;
  __asm__ volatile (".byte 0x0f, 0x31" : "=A" (x));
  return x;
}
#elif defined(__x86_64__)


static __inline__ unsigned long long rdtsc(void)
{
  unsigned hi, lo;
  __asm__ __volatile__ ("rdtsc" : "=a"(lo), "=d"(hi));
  return ( (unsigned long long)lo)|( ((unsigned long long)hi)<<32 );
}

#elif defined(__powerpc__)


static __inline__ unsigned long long rdtsc(void)
{
  unsigned long long int result=0;
  unsigned long int upper, lower,tmp;
  __asm__ volatile(
                "0:                  \n"
                "\tmftbu   %0           \n"
                "\tmftb    %1           \n"
                "\tmftbu   %2           \n"
                "\tcmpw    %2,%0        \n"
                "\tbne     0b         \n"
                : "=r"(upper),"=r"(lower),"=r"(tmp)
		   );
  result = upper;
  result = result<<32;
  result = result|lower;

  return(result);
}

#endif
