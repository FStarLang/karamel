/*
  Copyright (c) INRIA and Microsoft Corporation. All rights reserved.
  Licensed under the Apache 2.0 License.
*/

#include <inttypes.h>
#include "kremlib.h"
#include "kremlin/internal/compat.h"
#include "kremlin/internal/target.h"

#ifndef __FStar_IO_H
#define __FStar_IO_H




extern void FStar_IO_print_newline();

extern void FStar_IO_print_string(Prims_string uu____30);

extern void FStar_IO_print_uint8(uint8_t uu____42);

extern void FStar_IO_print_uint16(uint16_t uu____54);

extern void FStar_IO_print_uint32(uint32_t uu____66);

extern void FStar_IO_print_uint64(uint64_t uu____78);

extern void FStar_IO_print_uint8_dec(uint8_t uu____90);

extern void FStar_IO_print_uint16_dec(uint16_t uu____102);

extern void FStar_IO_print_uint32_dec(uint32_t uu____114);

extern void FStar_IO_print_uint64_dec(uint64_t uu____126);

extern void FStar_IO_print_uint8_hex_pad(uint8_t uu____138);

extern void FStar_IO_print_uint16_hex_pad(uint16_t uu____150);

extern void FStar_IO_print_uint32_hex_pad(uint32_t uu____162);

extern void FStar_IO_print_uint64_hex_pad(uint64_t uu____174);

extern void FStar_IO_print_uint8_dec_pad(uint8_t uu____186);

extern void FStar_IO_print_uint16_dec_pad(uint16_t uu____198);

extern void FStar_IO_print_uint32_dec_pad(uint32_t uu____210);

extern void FStar_IO_print_uint64_dec_pad(uint64_t uu____222);

extern Prims_string FStar_IO_input_line();

extern Prims_int FStar_IO_input_int();

extern FStar_Float_float FStar_IO_input_float();

extern FStar_IO_fd_read FStar_IO_open_read_file(Prims_string uu____286);

extern FStar_IO_fd_write FStar_IO_open_write_file(Prims_string uu____298);

extern void FStar_IO_close_read_file(FStar_IO_fd_read uu____309);

extern void FStar_IO_close_write_file(FStar_IO_fd_write uu____319);

extern Prims_string FStar_IO_read_line(FStar_IO_fd_read uu____330);

extern void FStar_IO_write_string(FStar_IO_fd_write uu____349, Prims_string uu____350);

extern bool FStar_IO_debug_print_string(Prims_string uu____363);

#define __FStar_IO_H_DEFINED
#endif
