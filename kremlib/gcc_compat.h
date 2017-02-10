#ifndef __GCC_COMPAT_H
#define __GCC_COMPAT_H

#ifdef __GNUC__
// gcc does not support the __cdecl, __stdcall or __fastcall notation
// except on Windows
#ifndef _WIN32
#define __cdecl __attribute__((cdecl))
#define __stdcall __attribute__((stdcall))
#define __fastcall __attribute__((fastcall))
#endif // ! _WIN32
#endif // __GNUC__

#endif // __GCC_COMPAT_H
