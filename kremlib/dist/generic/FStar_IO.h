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




extern FStar_IO_fd_read FStar_IO_stdin;

extern FStar_IO_fd_write FStar_IO_stdout;

extern FStar_IO_fd_write FStar_IO_stderr;

extern void FStar_IO_print_newline();

extern void FStar_IO_print_string(Prims_string uu____32);

extern void FStar_IO_print_uint8(uint8_t uu____40);

extern void FStar_IO_print_uint16(uint16_t uu____48);

extern void FStar_IO_print_uint32(uint32_t uu____56);

extern void FStar_IO_print_uint64(uint64_t uu____64);

extern void FStar_IO_print_uint8_dec(uint8_t uu____72);

extern void FStar_IO_print_uint16_dec(uint16_t uu____80);

extern void FStar_IO_print_uint32_dec(uint32_t uu____88);

extern void FStar_IO_print_uint64_dec(uint64_t uu____96);

extern void FStar_IO_print_uint8_hex_pad(uint8_t uu____104);

extern void FStar_IO_print_uint16_hex_pad(uint16_t uu____112);

extern void FStar_IO_print_uint32_hex_pad(uint32_t uu____120);

extern void FStar_IO_print_uint64_hex_pad(uint64_t uu____128);

extern void FStar_IO_print_uint8_dec_pad(uint8_t uu____136);

extern void FStar_IO_print_uint16_dec_pad(uint16_t uu____144);

extern void FStar_IO_print_uint32_dec_pad(uint32_t uu____152);

extern void FStar_IO_print_uint64_dec_pad(uint64_t uu____160);

extern Prims_string FStar_IO_input_line();

extern Prims_int FStar_IO_input_int();

extern FStar_Float_float FStar_IO_input_float();

extern FStar_IO_fd_read FStar_IO_open_read_file(Prims_string uu____208);

extern FStar_IO_fd_write FStar_IO_open_write_file(Prims_string uu____216);

extern void FStar_IO_close_read_file(FStar_IO_fd_read uu____224);

extern void FStar_IO_close_write_file(FStar_IO_fd_write uu____232);

extern Prims_string FStar_IO_read_line(FStar_IO_fd_read uu____240);

extern void FStar_IO_write_string(FStar_IO_fd_write uu____255, Prims_string uu____256);

extern bool FStar_IO_debug_print_string(Prims_string uu____264);

#define __FStar_IO_H_DEFINED
#endif
