/*
  Copyright (c) INRIA and Microsoft Corporation. All rights reserved.
  Licensed under the Apache 2.0 and MIT Licenses.
*/


#ifndef FStar_Pprint_H
#define FStar_Pprint_H

#include "FStar_Issue.h"
#include <inttypes.h>
#include "krmllib.h"
#include "krml/internal/compat.h"
#include "krml/internal/target.h"

extern FStar_Pprint_document FStar_Pprint_empty;

extern FStar_Pprint_document FStar_Pprint_doc_of_char(FStar_Char_char uu___);

extern FStar_Pprint_document FStar_Pprint_doc_of_string(Prims_string uu___);

extern FStar_Pprint_document FStar_Pprint_doc_of_bool(bool uu___);

extern FStar_Pprint_document
FStar_Pprint_substring(
  Prims_string uu___,
  krml_checked_int_t uu___1,
  krml_checked_int_t uu___2
);

extern FStar_Pprint_document
FStar_Pprint_fancystring(Prims_string uu___, krml_checked_int_t uu___1);

extern FStar_Pprint_document
FStar_Pprint_fancysubstring(
  Prims_string uu___,
  krml_checked_int_t uu___1,
  krml_checked_int_t uu___2,
  krml_checked_int_t uu___3
);

extern FStar_Pprint_document FStar_Pprint_utf8string(Prims_string uu___);

extern FStar_Pprint_document FStar_Pprint_hardline;

extern FStar_Pprint_document FStar_Pprint_blank(krml_checked_int_t uu___);

extern FStar_Pprint_document FStar_Pprint_break_(krml_checked_int_t uu___);

extern FStar_Pprint_document
FStar_Pprint_op_Hat_Hat(FStar_Pprint_document uu___, FStar_Pprint_document uu___1);

extern FStar_Pprint_document
FStar_Pprint_op_Hat_Slash_Hat(FStar_Pprint_document uu___, FStar_Pprint_document uu___1);

extern FStar_Pprint_document
FStar_Pprint_nest(krml_checked_int_t uu___, FStar_Pprint_document uu___1);

extern FStar_Pprint_document FStar_Pprint_group(FStar_Pprint_document uu___);

extern FStar_Pprint_document
FStar_Pprint_ifflat(FStar_Pprint_document uu___, FStar_Pprint_document uu___1);

extern FStar_Pprint_document FStar_Pprint_lparen;

extern FStar_Pprint_document FStar_Pprint_rparen;

extern FStar_Pprint_document FStar_Pprint_langle;

extern FStar_Pprint_document FStar_Pprint_rangle;

extern FStar_Pprint_document FStar_Pprint_lbrace;

extern FStar_Pprint_document FStar_Pprint_rbrace;

extern FStar_Pprint_document FStar_Pprint_lbracket;

extern FStar_Pprint_document FStar_Pprint_rbracket;

extern FStar_Pprint_document FStar_Pprint_squote;

extern FStar_Pprint_document FStar_Pprint_dquote;

extern FStar_Pprint_document FStar_Pprint_bquote;

extern FStar_Pprint_document FStar_Pprint_semi;

extern FStar_Pprint_document FStar_Pprint_colon;

extern FStar_Pprint_document FStar_Pprint_comma;

extern FStar_Pprint_document FStar_Pprint_space;

extern FStar_Pprint_document FStar_Pprint_dot;

extern FStar_Pprint_document FStar_Pprint_sharp;

extern FStar_Pprint_document FStar_Pprint_slash;

extern FStar_Pprint_document FStar_Pprint_backslash;

extern FStar_Pprint_document FStar_Pprint_equals;

extern FStar_Pprint_document FStar_Pprint_qmark;

extern FStar_Pprint_document FStar_Pprint_tilde;

extern FStar_Pprint_document FStar_Pprint_at;

extern FStar_Pprint_document FStar_Pprint_percent;

extern FStar_Pprint_document FStar_Pprint_dollar;

extern FStar_Pprint_document FStar_Pprint_caret;

extern FStar_Pprint_document FStar_Pprint_ampersand;

extern FStar_Pprint_document FStar_Pprint_star;

extern FStar_Pprint_document FStar_Pprint_plus;

extern FStar_Pprint_document FStar_Pprint_minus;

extern FStar_Pprint_document FStar_Pprint_underscore;

extern FStar_Pprint_document FStar_Pprint_bang;

extern FStar_Pprint_document FStar_Pprint_bar;

extern FStar_Pprint_document FStar_Pprint_rarrow;

extern FStar_Pprint_document FStar_Pprint_long_left_arrow;

extern FStar_Pprint_document FStar_Pprint_larrow;

extern FStar_Pprint_document
FStar_Pprint_precede(FStar_Pprint_document uu___, FStar_Pprint_document uu___1);

extern FStar_Pprint_document
FStar_Pprint_terminate(FStar_Pprint_document uu___, FStar_Pprint_document uu___1);

extern FStar_Pprint_document
FStar_Pprint_enclose(
  FStar_Pprint_document uu___,
  FStar_Pprint_document uu___1,
  FStar_Pprint_document uu___2
);

extern FStar_Pprint_document FStar_Pprint_squotes(FStar_Pprint_document uu___);

extern FStar_Pprint_document FStar_Pprint_dquotes(FStar_Pprint_document uu___);

extern FStar_Pprint_document FStar_Pprint_bquotes(FStar_Pprint_document uu___);

extern FStar_Pprint_document FStar_Pprint_braces(FStar_Pprint_document uu___);

extern FStar_Pprint_document FStar_Pprint_parens(FStar_Pprint_document uu___);

extern FStar_Pprint_document FStar_Pprint_angles(FStar_Pprint_document uu___);

extern FStar_Pprint_document FStar_Pprint_brackets(FStar_Pprint_document uu___);

extern FStar_Pprint_document FStar_Pprint_twice(FStar_Pprint_document uu___);

extern FStar_Pprint_document
FStar_Pprint_repeat(krml_checked_int_t uu___, FStar_Pprint_document uu___1);

extern FStar_Pprint_document FStar_Pprint_concat(Prims_list__FStar_Pprint_document *uu___);

extern FStar_Pprint_document
FStar_Pprint_separate(FStar_Pprint_document uu___, Prims_list__FStar_Pprint_document *uu___1);

extern FStar_Pprint_document
FStar_Pprint_separate2(
  FStar_Pprint_document uu___,
  FStar_Pprint_document uu___1,
  Prims_list__FStar_Pprint_document *uu___2
);

extern Prims_list__FStar_Pprint_document *FStar_Pprint_lines(Prims_string uu___);

extern FStar_Pprint_document FStar_Pprint_arbitrary_string(Prims_string uu___);

extern Prims_list__FStar_Pprint_document *FStar_Pprint_words(Prims_string uu___);

extern Prims_list__FStar_Pprint_document
*FStar_Pprint_split(bool (*uu___)(FStar_Char_char x0), Prims_string uu___1);

extern FStar_Pprint_document
FStar_Pprint_flow(FStar_Pprint_document uu___, Prims_list__FStar_Pprint_document *uu___1);

extern FStar_Pprint_document FStar_Pprint_url(Prims_string uu___);

extern FStar_Pprint_document FStar_Pprint_align(FStar_Pprint_document uu___);

extern FStar_Pprint_document
FStar_Pprint_hang(krml_checked_int_t uu___, FStar_Pprint_document uu___1);

extern FStar_Pprint_document
FStar_Pprint_prefix(
  krml_checked_int_t uu___,
  krml_checked_int_t uu___1,
  FStar_Pprint_document uu___2,
  FStar_Pprint_document uu___3
);

extern FStar_Pprint_document
FStar_Pprint_jump(
  krml_checked_int_t uu___,
  krml_checked_int_t uu___1,
  FStar_Pprint_document uu___2
);

extern FStar_Pprint_document
FStar_Pprint_infix(
  krml_checked_int_t uu___,
  krml_checked_int_t uu___1,
  FStar_Pprint_document uu___2,
  FStar_Pprint_document uu___3,
  FStar_Pprint_document uu___4
);

extern FStar_Pprint_document
FStar_Pprint_surround(
  krml_checked_int_t uu___,
  krml_checked_int_t uu___1,
  FStar_Pprint_document uu___2,
  FStar_Pprint_document uu___3,
  FStar_Pprint_document uu___4
);

extern FStar_Pprint_document
FStar_Pprint_soft_surround(
  krml_checked_int_t uu___,
  krml_checked_int_t uu___1,
  FStar_Pprint_document uu___2,
  FStar_Pprint_document uu___3,
  FStar_Pprint_document uu___4
);

extern FStar_Pprint_document
FStar_Pprint_surround_separate(
  krml_checked_int_t uu___,
  krml_checked_int_t uu___1,
  FStar_Pprint_document uu___2,
  FStar_Pprint_document uu___3,
  FStar_Pprint_document uu___4,
  FStar_Pprint_document uu___5,
  Prims_list__FStar_Pprint_document *uu___6
);

extern Prims_string
FStar_Pprint_pretty_string(
  FStar_Float_float uu___,
  krml_checked_int_t uu___1,
  FStar_Pprint_document uu___2
);

extern Prims_string FStar_Pprint_render(FStar_Pprint_document uu___);


#define FStar_Pprint_H_DEFINED
#endif /* FStar_Pprint_H */
