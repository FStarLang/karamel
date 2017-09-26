// This module performs low-level WASM manipulations, such as linking several
// modules together and inspecting the debug zone at the bottom of the memory.
// This module is aware of the compilation strategy of kreMLin. It can be
// included from either a browser or a shell context, as long as my_print is
// defined in scope.

"use strict";

var my_print;

/******************************************************************************/
/* Some printing helpers                                                      */
/******************************************************************************/

function p8(n) {
  return ("0"+Number(n).toString(16)).slice(-2);
}

function hex(m8, start, len) {
  let s = "";
  for (let i = 0; i < len; ++i)
    s += p8(m8[start + i]);
  return s;
}

function hexle(m8, i, m) {
  let buf = "";
  let n = m - 1;
  while (n >= 0) {
    buf += p8(m8[i+n]);
    n--;
  }
  return buf;
}

function hex32(m8, start) {
  return hexle(m8, start, 4);
}

function hex64(m8, start) {
  return hexle(m8, start, 8);
}

function p32(n) {
  return ("0000000"+Number(n).toString(16)).slice(-8);
}

function dump(mem, size) {
  let m8 = new Uint8Array(mem.buffer);
  let i = 0;
  let buf = "";
  while (i < size) {
    buf += p32(i) + "    ";
    for (let j = 0; j < 32; ++j) {
      buf += p8(m8[i+j]);
      if (j % 4 == 3)
        buf += " ";
    }
    buf += "    ";
    for (let j = 0; j < 32; ++j) {
      let c = m8[i+j];
      if (32 <= c && c < 128)
        buf += String.fromCharCode(c);
      else
        buf += ".";
    }
    buf += "\n";
    i += 32;
  }
  my_print(buf);
}

/******************************************************************************/
/* Implementations of the kremlin runtime support library                     */
/******************************************************************************/

function stringAtAddr(mem, addr) {
  let m8 = new Uint8Array(mem.buffer);
  let buf = "";
  while (m8[addr] != 0) {
    buf += String.fromCharCode(m8[addr++]);
  }
  return buf;
}

function readLeAtAddr(mem, addr, bytes) {
  let m8 = new Uint8Array(mem.buffer);
  let i = 0;
  while (bytes-- > 0)
    i = (i << 8) + m8[addr + bytes];
  return i;
}

function writeLeAtAddr(mem, addr, n, bytes) {
  let m8 = new Uint8Array(mem.buffer);
  while (bytes > 0) {
    m8[addr + bytes - 1] = n & 255;
    bytes--;
    n >>= 255;
  }
}

function dummyModule(funcs, globals) {
  let module = {};
  for (let f of funcs)
    module[f] = () => {
      my_print("Not implemented: " + s);
      throw new Error();
    };
  for (let g of globals)
    module[g] = 0;
  return module;
}


let mkWasmSupport = (mem) => ({
  WasmSupport_trap: () => {
    dump(mem, 2*1024);
    my_print("Run-time trap, e.g. zero-sized array.");
    throw new Error();
  }
});

let mkFStar = () => dummyModule(
  [ "FStar_UInt128_constant_time_carry_ok", "FStar_PropositionalExtensionality_axiom" ],
  [ "FStar_Monotonic_Heap_lemma_mref_injectivity" ]);

let mkC = (mem) => ({
  srand: () => { throw new Error("todo: srand") },
  rand: () => { throw new Error("todo: rand") },
  exit: () => { throw new Error("todo: exit") },
  print_bytes: () => { throw new Error("todo: print_bytes") },
  htole16: () => { throw new Error("todo: htole16") },
  le16toh: () => { throw new Error("todo: le16toh") },
  htole32: () => { throw new Error("todo: htole32") },
  le32toh: () => { throw new Error("todo: le32toh") },
  htole64: () => { throw new Error("todo: htole64") },
  le64toh: () => { throw new Error("todo: le64toh") },
  htobe16: () => { throw new Error("todo: htobe16") },
  be16toh: () => { throw new Error("todo: be16toh") },
  htobe32: () => { throw new Error("todo: htobe32") },
  be32toh: () => { throw new Error("todo: be32toh") },
  htobe64: () => { throw new Error("todo: htobe64") },
  be64toh: () => { throw new Error("todo: be64toh") },
  store16_le: () => { throw new Error("todo: store16_le") },
  load16_le: () => { throw new Error("todo: load16_le") },
  store16_be: () => { throw new Error("todo: store16_be") },
  load16_be: () => { throw new Error("todo: load16_be") },
  store32_le: (addr, n) => {
    writeLeAtAddr(mem, addr, n, 4);
  },
  load32_le: (addr) => {
    return readLeAtAddr(mem, addr, 4);
  },
  store32_be: () => { throw new Error("todo: store32_be") },
  load32_be: () => { throw new Error("todo: load32_be") },
  load64_le: () => { throw new Error("todo: load64_le") },
  store64_le: () => { throw new Error("todo: store64_le") },
  load64_be: () => { throw new Error("todo: load64_be") },
  store64_be: () => { throw new Error("todo: store64_be") },
  load128_le: () => { throw new Error("todo: load128_le") },
  store128_le: () => { throw new Error("todo: store128_le") },
  load128_be: () => { throw new Error("todo: load128_be") },
  store128_be: () => { throw new Error("todo: store128_be") },

  // A Prims_string generates a literal allocated in the data segment;
  // string_of_literal is just a typing trick.
  string_of_literal: (x) => x,
  print_string: (addr) => my_print(stringAtAddr(mem, addr)),
});

function checkEq(mem, name) {
  return (x1, x2) => {
    if (x1 != x2) {
      dump(mem, 2*1024);
      my_print(name + ": equality failure, "+x1+" != "+x2);
      throw new Error();
    }
    return 0;
  };
}

let mkTestLib = (mem) => ({
  TestLib_touch: () => 0,
  TestLib_check8: checkEq(mem, "TestLib_check8"),
  TestLib_check16: checkEq(mem, "TestLib_check16"),
  TestLib_check32: checkEq(mem, "TestLib_check32"),
  TestLib_check64: checkEq(mem, "TestLib_check64"),
  TestLib_checku8: checkEq(mem, "TestLib_checku8"),
  TestLib_checku16: checkEq(mem, "TestLib_checku16"),
  TestLib_checku32: checkEq(mem, "TestLib_checku32"),
  TestLib_checku64: checkEq(mem, "TestLib_checku64"),
  TestLib_unsafe_malloc: () => { throw new Error("todo: unsafe_malloc") },
  TestLib_perr: (err) => {
    my_print("Got error code "+err);
    return 0;
  },
  TestLib_uint8_p_null: 0,
  TestLib_uint32_p_null: 0,
  TestLib_uint64_p_null: 0,
  TestLib_compare_and_print: (addr, b1, b2, len) => {
    let m8 = new Uint8Array(mem.buffer);
    let str = stringAtAddr(m8, addr);
    let hex1 = hex(m8, b1, len);
    let hex2 = hex(m8, b2, len);
    my_print("[test] expected output "+str+" is "+hex1+"\n");
    my_print("[test] computed output "+str+" is "+hex2+"\n");
    for (let i = 0; i < len; ++i) {
      if (m8[b1+i] != m8[b2+i]) {
        my_print("[test] reference "+str+" and expected "+str+" differ at byte "+i+"\n");
        throw new Error("test failure");
      }
    }
    my_print("[test] "+str+" is a success\n");
  },
});

/******************************************************************************/
/* Memory layout                                                              */
/******************************************************************************/

// mem[0..3] = top-of-the-stack pointer (I32);
// mem[4..127] = scratch space for debugging.
// Conventions for debugging and "debugging format" (lolz) are in WasmDebug.ml
const header_size = 128;

// this sets up the base data pointer and the debug entry point for the WASM
// context; WASM-generated code expects to have these defined.
function init() {
  let mem = new WebAssembly.Memory({ initial: 16 });
  let m8 = new Uint8Array(mem.buffer);
  let nest = 0;

  let debug = () => {
    let i = 0;
    let buf = "";
    let string = () => {
      let ptr = m8[i] + (m8[i+1] << 8) + (m8[i+2] << 16) + (m8[i+3] << 24);
      i += 4;
      while (m8[ptr] != 0) {
        buf += String.fromCharCode(m8[ptr]);
        ptr++;
      }
    };
    let int32 = () => {
      buf += "0x";
      buf += hex32(m8, i);
      i += 4;
    };
    let int64 = () => {
      buf += "0x";
      buf += hex64(m8, i);
      i += 8;
    };
    // Dump the stack pointer
    int32();
    buf += " | ";
    buf += " ".repeat(nest);
    while (m8[i] != 0 && i < 128) {
      let c = m8[i];
      i++;
      switch (c) {
        case 1:
          string();
          break;
        case 2:
          int32();
          break;
        case 3:
          int64();
          break;
        case 4:
          nest++;
          break;
        case 5:
          nest--;
          break;
        default:
          my_print(hex(m8, 0, 128));
          throw "unrecognized debug format:\n  buf="+buf+"\n  c=0x"+p8(c)+"\n  i="+i;
      }
      buf += " ";
    }
    my_print(buf);
  };

  // Initialize the highwater mark.
  new Uint32Array(mem.buffer)[0] = header_size;

  // Base stuff that appears as requirement, because they're exposed in TestLib
  // and/or C.
  let imports = {
    Kremlin: {
      mem: mem,
      debug: debug,
      data_start: header_size
    },
    WasmSupport: mkWasmSupport(mem),
    FStar: mkFStar(mem),
    C: mkC(mem),
    TestLib: mkTestLib(mem)
  };
  return imports;
}

// One MUST call this function after loading a module.
function propagate(module_name, imports, instance) {
  my_print("Module", module_name, "successfully loaded");
  my_print("Adding exports into global import table:\n ", Object.keys(instance.exports));
  if (!(module_name in imports))
    imports[module_name] = {};
  for (let o of Object.keys(instance.exports)) {
    imports[module_name][o] = instance.exports[o];
  }
  my_print("This module has a data segment of size: ", instance.exports.data_size);
  imports.Kremlin.data_start += instance.exports.data_size;
  my_print("Next data segment will start at: ", imports.Kremlin.data_start);
  // Set the highwater mark right after the data segment
  new Uint32Array(imports.Kremlin.mem.buffer)[0] = imports.Kremlin.data_start;
  my_print();
}

// One MAY only call this function after all modules have been loaded and
// suitable calls to propagate have been performed.
function reserve(mem, size) {
  let m32 = new Uint32Array(mem.buffer);
  let p = m32[0];
  m32[0] += size;
  my_print("Reserved memory area 0x"+p32(p)+"..0x"+p32(m32[0]));
  return p;
}

function link(modules) {
  let fold = async (imports, modules) => {
    if (!modules.length)
      return imports;

    let [{ name, buf }, ...ms] = modules;
    let { module, instance } = await WebAssembly.instantiate(buf, imports);
    propagate(name, imports, instance);
    return fold(imports, ms);
  };

  return fold(init(), modules);
}
