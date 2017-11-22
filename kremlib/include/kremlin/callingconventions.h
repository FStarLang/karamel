#ifndef __GCC_COMPAT_H
#define __GCC_COMPAT_H

/* KreMLin supports calling convention annotations (currently not exposed in the
 * F* frontend), which result in __stdcall and __cdecl being prepended to function
 * declarations. This mostly matters on Windows, and this header makes sure
 * these keywords are a no-op on other platforms. */

#ifndef _MSC_VER
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
