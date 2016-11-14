#ifndef __NOSTRUCT_H
#define __NOSTRUCT_H

#ifdef __NOSTRUCT__

#define DECL_BY_VAL(typ, NAME) \
  DECL_BY_VAL_##typ(NAME)  // must be defined for the given type

#define DECL_LOCAL(typ, NAME)						\
  DECL_LOCAL_##typ(NAME)  // must be defined for the given type. Ideally, should be the same as DECL_BY_VAL_ except that , are replaced with ;

#define DECL_RET_BY_VAL(typ, NAME, ...)	\
  void NAME (typ * retval, __VA_ARGS__ )


/*

#define CALL_RET_BY_VAL(x, f, ...)		\
  ((f)(&(x), __VA_ARGS__ ))

#define INIT_RET_BY_VAL(typ, x, f, ...) \
  typ x; \
  CALL_RET_BY_VAL(x, f, __VA_ARGS__ )

*/

#define PASS_LOCAL(typ, NAME) \
  PASS_LOCAL_##typ(NAME) // must be defined for the given type

#define RET_BY_VAL(typ, ...)				 \
  LOCAL_TO_STRUCT_##typ(retval, __VA_ARGS__ );		 \
  return   // must be defined for the given type

#define RET_LOCAL(typ, NAME) \
  RET_BY_VAL(typ, PASS_LOCAL(typ,NAME))

#define RET_CALL_BY_VAL(...) RET_CALL_BY_VAL2(__VA_ARGS__)
#define RET_CALL_BY_VAL2(f, ...) \
  ((f)(retval, __VA_ARGS__ )); \
  return

#define LOCAL_FIELD(NAME, field) \
  NAME##_##field

#define ASSIGN_INIT_LOCAL(...) ASSIGN_INIT_LOCAL2(__VA_ARGS__)
#define ASSIGN_INIT_LOCAL2(ty, NAME, ...) \
  ASSIGN_INIT_##ty(NAME, __VA_ARGS__)

#define INIT_LOCAL(...) INIT_LOCAL2(__VA_ARGS__)
#define INIT_LOCAL2(ty, NAME, ...)		\
  DECL_LOCAL(ty, NAME); \
  ASSIGN_INIT_LOCAL(ty, NAME, __VA_ARGS__)

#define RET_INIT(...) RET_INIT2(__VA_ARGS__)
#define RET_INIT2(ty, ...) \
  INIT_LOCAL(ty, _retval, __VA_ARGS__); \
  RET_LOCAL(ty, _retval)

#define PASS_BY_COPY(ty, x) \
  PASS_BY_COPY_##ty(x)   // must be defined for the given type

#else

#define DECL_BY_VAL(typ, NAME) \
  typ NAME

#define DECL_LOCAL(typ, NAME) \
  typ NAME

#define DECL_RET_BY_VAL(typ, NAME, ...) \
  typ NAME( __VA_ARGS__ )

#define CALL_RET_BY_VAL_2(x, f, ...) \
  x = (f)( __VA_ARGS__ )

#define CALL_RET_BY_VAL(x, f, ...) \
  (CALL_RET_BY_VAL_2((x), f, __VA_ARGS__ ))

#define INIT_RET_BY_VAL(typ, x, f, ...) \
  typ CALL_RET_BY_VAL_2(x, f, __VA_ARGS__ )

#define RET_LOCAL(typ, NAME) \
  return NAME

#define PASS_LOCAL(typ, NAME) \
  NAME

#define RET_CALL_BY_VAL(...) RET_CALL_BY_VAL2(__VA_ARGS__)
#define RET_CALL_BY_VAL2(f, ...) \
  return (f)( __VA_ARGS__ )

#define LOCAL_FIELD(NAME, field) \
  NAME.field

#define STRUCT_INIT(ty) \
    STRUCT_INIT_##ty // must be defined for the given type, and defined to inner of initializer block

#define ASSIGN_INIT_LOCAL(ty, r, ...) \
  r = { STRUCT_INIT(ty)(__VA_ARGS__) }

#define INIT_LOCAL(ty, NAME, ...) \
  ty ASSIGN_INIT_LOCAL(ty, NAME, __VA_ARGS__ )

#define RET_INIT(...) RET_INIT2(__VA_ARGS__)
#define RET_INIT2(ty, ...) \
  return (ty){ STRUCT_INIT(ty)(__VA_ARGS__) }

#define PASS_BY_COPY(ty, x) \
    (x)

#endif // __NOSTRUCT__

#endif // __NOSTRUCT_H
