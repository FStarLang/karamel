#ifndef __GCC_COMPAT_H
#define __GCC_COMPAT_H


#if defined(__STDC__)
# define PREDEF_STANDARD_C_1989
# if defined(__STDC_VERSION__)
#  if (__STDC_VERSION__ >= 199409L)
#   define PREDEF_STANDARD_C_1994
#  endif
#  if (__STDC_VERSION__ >= 199901L)
#   define PREDEF_STANDARD_C_1999
#  endif
# endif
#endif

#if !defined(PREDEF_STANDARD_C_1989)
#error "need at least a a c89 compiler"
#elif !defined(PREDEF_STANDART_C_1994) && !defined(PREDEF_STANDART_C_1999)
#define inline __inline__
#endif

#ifndef _MSC_VER
/* Use the gcc predefined macros if on a platform/architectures that set them.  Otherwise define them to be empty. */
  #ifndef __cdecl
    #define __cdecl
  #endif
  #ifndef __stdcall
    #define __stdcall
  #endif
  #ifndef __fastcall
    #define __fastcall
  #endif
#endif


#endif /* __GCC_COMPAT_H */
