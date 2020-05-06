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

extern void FStar_IO_print_string(Prims_string uu____45);

extern void FStar_IO_print_uint8(uint8_t uu____57);

extern void FStar_IO_print_uint16(uint16_t uu____69);

extern void FStar_IO_print_uint32(uint32_t uu____81);

extern void FStar_IO_print_uint64(uint64_t uu____93);

extern void FStar_IO_print_uint8_dec(uint8_t uu____105);

extern void FStar_IO_print_uint16_dec(uint16_t uu____117);

extern void FStar_IO_print_uint32_dec(uint32_t uu____129);

extern void FStar_IO_print_uint64_dec(uint64_t uu____141);

extern void FStar_IO_print_uint8_hex_pad(uint8_t uu____153);

extern void FStar_IO_print_uint16_hex_pad(uint16_t uu____165);

extern void FStar_IO_print_uint32_hex_pad(uint32_t uu____177);

extern void FStar_IO_print_uint64_hex_pad(uint64_t uu____189);

extern void FStar_IO_print_uint8_dec_pad(uint8_t uu____201);

extern void FStar_IO_print_uint16_dec_pad(uint16_t uu____213);

extern void FStar_IO_print_uint32_dec_pad(uint32_t uu____225);

extern void FStar_IO_print_uint64_dec_pad(uint64_t uu____237);

extern Prims_string FStar_IO_input_line();

extern Prims_int FStar_IO_input_int();

extern FStar_Float_float FStar_IO_input_float();

extern FStar_IO_fd_read FStar_IO_open_read_file(Prims_string uu____301);

extern FStar_IO_fd_write FStar_IO_open_write_file(Prims_string uu____313);

extern void FStar_IO_close_read_file(FStar_IO_fd_read uu____324);

extern void FStar_IO_close_write_file(FStar_IO_fd_write uu____334);

extern Prims_string FStar_IO_read_line(FStar_IO_fd_read uu____345);

extern void FStar_IO_write_string(FStar_IO_fd_write uu____364, Prims_string uu____365);

extern bool FStar_IO_debug_print_string(Prims_string uu____378);

#define __FStar_IO_H_DEFINED
#endif
