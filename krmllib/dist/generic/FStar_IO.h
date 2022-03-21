/*
  Copyright (c) INRIA and Microsoft Corporation. All rights reserved.
  Licensed under the Apache 2.0 License.
*/


#ifndef __FStar_IO_H
#define __FStar_IO_H




#include <inttypes.h>
#include "kremlib.h"
#include "kremlin/internal/compat.h"
#include "kremlin/internal/target.h"
extern FStar_IO_fd_read FStar_IO_stdin;

extern FStar_IO_fd_write FStar_IO_stdout;

extern FStar_IO_fd_write FStar_IO_stderr;

extern void FStar_IO_print_newline();

extern void FStar_IO_print_string(Prims_string uu___);

extern void FStar_IO_print_uint8(uint8_t uu___);

extern void FStar_IO_print_uint16(uint16_t uu___);

extern void FStar_IO_print_uint32(uint32_t uu___);

extern void FStar_IO_print_uint64(uint64_t uu___);

extern void FStar_IO_print_uint8_dec(uint8_t uu___);

extern void FStar_IO_print_uint16_dec(uint16_t uu___);

extern void FStar_IO_print_uint32_dec(uint32_t uu___);

extern void FStar_IO_print_uint64_dec(uint64_t uu___);

extern void FStar_IO_print_uint8_hex_pad(uint8_t uu___);

extern void FStar_IO_print_uint16_hex_pad(uint16_t uu___);

extern void FStar_IO_print_uint32_hex_pad(uint32_t uu___);

extern void FStar_IO_print_uint64_hex_pad(uint64_t uu___);

extern void FStar_IO_print_uint8_dec_pad(uint8_t uu___);

extern void FStar_IO_print_uint16_dec_pad(uint16_t uu___);

extern void FStar_IO_print_uint32_dec_pad(uint32_t uu___);

extern void FStar_IO_print_uint64_dec_pad(uint64_t uu___);

extern Prims_string FStar_IO_input_line();

extern Prims_int FStar_IO_input_int();

extern FStar_Float_float FStar_IO_input_float();

extern FStar_IO_fd_read FStar_IO_open_read_file(Prims_string uu___);

extern FStar_IO_fd_write FStar_IO_open_write_file(Prims_string uu___);

extern void FStar_IO_close_read_file(FStar_IO_fd_read uu___);

extern void FStar_IO_close_write_file(FStar_IO_fd_write uu___);

extern Prims_string FStar_IO_read_line(FStar_IO_fd_read uu___);

extern void FStar_IO_write_string(FStar_IO_fd_write uu___, Prims_string uu___1);

extern bool FStar_IO_debug_print_string(Prims_string uu___);


#define __FStar_IO_H_DEFINED
#endif
