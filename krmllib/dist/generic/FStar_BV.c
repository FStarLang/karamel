/*
  Copyright (c) INRIA and Microsoft Corporation. All rights reserved.
  Licensed under the Apache 2.0 License.
*/


#include "internal/FStar_BV.h"

Prims_list__bool *FStar_List_Tot_Base_append__bool(Prims_list__bool *x, Prims_list__bool *y)
{
  if (x->tag == Prims_Nil)
  {
    return y;
  }
  else if (x->tag == Prims_Cons)
  {
    Prims_list__bool *tl1 = x->tl;
    bool a1 = x->hd;
    Prims_list__bool *buf = KRML_HOST_MALLOC(sizeof (Prims_list__bool));
    buf[0U]
    =
      (
        (Prims_list__bool){
          .tag = Prims_Cons,
          .hd = a1,
          .tl = FStar_List_Tot_Base_append__bool(tl1, y)
        }
      );
    return buf;
  }
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

Prims_list__bool *FStar_Seq_Base_append__bool(Prims_list__bool *s1, Prims_list__bool *s2)
{
  return FStar_List_Tot_Base_append__bool(s1, s2);
}

static Prims_list__bool *cons__bool(bool x, Prims_list__bool *s)
{
  Prims_list__bool *buf = KRML_HOST_MALLOC(sizeof (Prims_list__bool));
  buf[0U] = ((Prims_list__bool){ .tag = Prims_Cons, .hd = x, .tl = s });
  return buf;
}

Prims_list__bool *FStar_Seq_Base_create__bool(krml_checked_int_t len, bool v)
{
  if (len == (krml_checked_int_t)0)
  {
    Prims_list__bool *buf = KRML_HOST_MALLOC(sizeof (Prims_list__bool));
    buf[0U] = ((Prims_list__bool){ .tag = Prims_Nil });
    return buf;
  }
  else
  {
    return
      cons__bool(v,
        FStar_Seq_Base_create__bool(Prims_op_Subtraction(len, (krml_checked_int_t)1), v));
  }
}

Prims_list__bool
*FStar_BV_bv_uext(krml_checked_int_t n, krml_checked_int_t i, Prims_list__bool *a)
{
  KRML_MAYBE_UNUSED_VAR(n);
  return FStar_Seq_Base_append__bool(FStar_Seq_Base_create__bool(i, false), a);
}

Prims_list__bool
*(*FStar_BV_int2bv)(krml_checked_int_t x0, krml_checked_int_t x1) = FStar_UInt_to_vec;

krml_checked_int_t
(*FStar_BV_bv2int)(krml_checked_int_t x0, Prims_list__bool *x1) = FStar_UInt_from_vec;

Prims_list__bool *FStar_Seq_Base_empty__bool(void)
{
  Prims_list__bool *buf = KRML_HOST_MALLOC(sizeof (Prims_list__bool));
  buf[0U] = ((Prims_list__bool){ .tag = Prims_Nil });
  return buf;
}

Prims_list__bool *FStar_Seq_Base_op_At_Bar__bool(Prims_list__bool *s1, Prims_list__bool *s2)
{
  return FStar_Seq_Base_append__bool(s1, s2);
}

Prims_list__bool *FStar_Seq_Properties_seq_of_list__bool(Prims_list__bool *l)
{
  if (l->tag == Prims_Nil)
  {
    return FStar_Seq_Base_empty__bool();
  }
  else if (l->tag == Prims_Cons)
  {
    Prims_list__bool *tl = l->tl;
    bool hd = l->hd;
    return
      FStar_Seq_Base_op_At_Bar__bool(FStar_Seq_Base_create__bool((krml_checked_int_t)1, hd),
        FStar_Seq_Properties_seq_of_list__bool(tl));
  }
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

Prims_list__bool *FStar_BV_list2bv(krml_checked_int_t n, Prims_list__bool *l)
{
  KRML_MAYBE_UNUSED_VAR(n);
  return FStar_Seq_Properties_seq_of_list__bool(l);
}

krml_checked_int_t FStar_List_Tot_Base_length__bool(Prims_list__bool *uu___)
{
  if (uu___->tag == Prims_Nil)
  {
    return (krml_checked_int_t)0;
  }
  else if (uu___->tag == Prims_Cons)
  {
    Prims_list__bool *tl1 = uu___->tl;
    return Prims_op_Addition((krml_checked_int_t)1, FStar_List_Tot_Base_length__bool(tl1));
  }
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

krml_checked_int_t FStar_Seq_Base_length__bool(Prims_list__bool *s)
{
  return FStar_List_Tot_Base_length__bool(s);
}

bool FStar_List_Tot_Base_hd__bool(Prims_list__bool *uu___)
{
  if (uu___->tag == Prims_Cons)
  {
    return uu___->hd;
  }
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

Prims_list__bool *FStar_List_Tot_Base_tail__bool(Prims_list__bool *uu___)
{
  if (uu___->tag == Prims_Cons)
  {
    return uu___->tl;
  }
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

Prims_list__bool
*(*FStar_List_Tot_Base_tl__bool)(Prims_list__bool *x0) = FStar_List_Tot_Base_tail__bool;

bool FStar_List_Tot_Base_index__bool(Prims_list__bool *l, krml_checked_int_t i)
{
  if (i == (krml_checked_int_t)0)
  {
    return FStar_List_Tot_Base_hd__bool(l);
  }
  else
  {
    return
      FStar_List_Tot_Base_index__bool(FStar_List_Tot_Base_tl__bool(l),
        Prims_op_Subtraction(i, (krml_checked_int_t)1));
  }
}

bool FStar_Seq_Base_index__bool(Prims_list__bool *s, krml_checked_int_t i)
{
  return FStar_List_Tot_Base_index__bool(s, i);
}

static Prims_list__bool *tl__bool(Prims_list__bool *s)
{
  return FStar_List_Tot_Base_tl__bool(s);
}

static bool hd__bool(Prims_list__bool *s)
{
  return FStar_List_Tot_Base_hd__bool(s);
}

Prims_list__bool
*FStar_Seq_Base_slice___bool(Prims_list__bool *s, krml_checked_int_t i, krml_checked_int_t j)
{
  if (Prims_op_GreaterThan(i, (krml_checked_int_t)0))
  {
    return
      FStar_Seq_Base_slice___bool(tl__bool(s),
        Prims_op_Subtraction(i, (krml_checked_int_t)1),
        Prims_op_Subtraction(j, (krml_checked_int_t)1));
  }
  else if (j == (krml_checked_int_t)0)
  {
    Prims_list__bool *buf = KRML_HOST_MALLOC(sizeof (Prims_list__bool));
    buf[0U] = ((Prims_list__bool){ .tag = Prims_Nil });
    return buf;
  }
  else
  {
    return
      cons__bool(hd__bool(s),
        FStar_Seq_Base_slice___bool(tl__bool(s), i, Prims_op_Subtraction(j, (krml_checked_int_t)1)));
  }
}

Prims_list__bool
*(*FStar_Seq_Base_slice__bool)(
  Prims_list__bool *x0,
  krml_checked_int_t x1,
  krml_checked_int_t x2
) = FStar_Seq_Base_slice___bool;

Prims_list__bool *FStar_Seq_Properties_seq_to_list__bool(Prims_list__bool *s)
{
  if (FStar_Seq_Base_length__bool(s) == (krml_checked_int_t)0)
  {
    Prims_list__bool *buf = KRML_HOST_MALLOC(sizeof (Prims_list__bool));
    buf[0U] = ((Prims_list__bool){ .tag = Prims_Nil });
    return buf;
  }
  else
  {
    Prims_list__bool *buf = KRML_HOST_MALLOC(sizeof (Prims_list__bool));
    buf[0U]
    =
      (
        (Prims_list__bool){
          .tag = Prims_Cons,
          .hd = FStar_Seq_Base_index__bool(s, (krml_checked_int_t)0),
          .tl = FStar_Seq_Properties_seq_to_list__bool(FStar_Seq_Base_slice__bool(s,
              (krml_checked_int_t)1,
              FStar_Seq_Base_length__bool(s)))
        }
      );
    return buf;
  }
}

Prims_list__bool *FStar_BV_bv2list(krml_checked_int_t n, Prims_list__bool *s)
{
  KRML_MAYBE_UNUSED_VAR(n);
  return FStar_Seq_Properties_seq_to_list__bool(s);
}

Prims_list__bool
*(*FStar_BV_bvand)(krml_checked_int_t x0, Prims_list__bool *x1, Prims_list__bool *x2) =
  FStar_BitVector_logand_vec;

Prims_list__bool
*(*FStar_BV_bvxor)(krml_checked_int_t x0, Prims_list__bool *x1, Prims_list__bool *x2) =
  FStar_BitVector_logxor_vec;

Prims_list__bool
*(*FStar_BV_bvor)(krml_checked_int_t x0, Prims_list__bool *x1, Prims_list__bool *x2) =
  FStar_BitVector_logor_vec;

Prims_list__bool
*(*FStar_BV_bvnot)(krml_checked_int_t x0, Prims_list__bool *x1) = FStar_BitVector_lognot_vec;

Prims_list__bool
*(*FStar_BV_bvshl)(krml_checked_int_t x0, Prims_list__bool *x1, krml_checked_int_t x2) =
  FStar_BitVector_shift_left_vec;

Prims_list__bool
*(*FStar_BV_bvshr)(krml_checked_int_t x0, Prims_list__bool *x1, krml_checked_int_t x2) =
  FStar_BitVector_shift_right_vec;

Prims_list__bool *FStar_BV_bv_zero(krml_checked_int_t n)
{
  return FStar_BV_int2bv(n, (krml_checked_int_t)0);
}

bool FStar_BV_bvult(krml_checked_int_t n, Prims_list__bool *a, Prims_list__bool *b)
{
  return Prims_op_LessThan(FStar_BV_bv2int(n, a), FStar_BV_bv2int(n, b));
}

Prims_list__bool
*FStar_BV_bvadd(krml_checked_int_t n, Prims_list__bool *a, Prims_list__bool *b)
{
  return FStar_BV_int2bv(n, FStar_UInt_add_mod(n, FStar_BV_bv2int(n, a), FStar_BV_bv2int(n, b)));
}

Prims_list__bool
*FStar_BV_bvsub(krml_checked_int_t n, Prims_list__bool *a, Prims_list__bool *b)
{
  return FStar_BV_int2bv(n, FStar_UInt_sub_mod(n, FStar_BV_bv2int(n, a), FStar_BV_bv2int(n, b)));
}

Prims_list__bool
*FStar_BV_bvdiv(krml_checked_int_t n, Prims_list__bool *a, krml_checked_int_t b)
{
  return FStar_BV_int2bv(n, FStar_UInt_udiv(n, FStar_BV_bv2int(n, a), b));
}

Prims_list__bool
*FStar_BV_bvdiv_unsafe(krml_checked_int_t n, Prims_list__bool *a, Prims_list__bool *b)
{
  if (FStar_BV_bv2int(n, b) != (krml_checked_int_t)0)
  {
    return FStar_BV_bvdiv(n, a, FStar_BV_bv2int(n, b));
  }
  else
  {
    return FStar_BV_int2bv(n, (krml_checked_int_t)0);
  }
}

Prims_list__bool
*FStar_BV_bvmod(krml_checked_int_t n, Prims_list__bool *a, krml_checked_int_t b)
{
  return FStar_BV_int2bv(n, FStar_UInt_mod(n, FStar_BV_bv2int(n, a), b));
}

Prims_list__bool
*FStar_BV_bvmul(krml_checked_int_t n, Prims_list__bool *a, krml_checked_int_t b)
{
  return FStar_BV_int2bv(n, FStar_UInt_mul_mod(n, FStar_BV_bv2int(n, a), b));
}

