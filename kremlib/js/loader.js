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

function hex32(m8, start) {
  return hex(m8, start, 4);
}

function hex64(m8, start) {
  return hex(m8, start, 8);
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


const implWasmSupport = {
  WasmSupport_trap: () => {
    my_print("Run-time trap, e.g. zero-sized array.");
    throw new Error();
  }
};

const implFStar = dummyModule(
  [ "FStar_UInt128_constant_time_carry_ok", "FStar_PropositionalExtensionality_axiom" ],
  [ "FStar_Monotonic_Heap_lemma_mref_injectivity" ]);

const implC = dummyModule([ "srand", "rand", "exit", "print_bytes", "htole16",
  "le16toh", "htole32", "le32toh", "htole64", "le64toh", "htobe16", "be16toh",
  "htobe32", "be32toh", "htobe64", "be64toh", "store16_le", "load16_le",
  "store16_be", "load16_be", "store32_le", "load32_le", "store32_be", "load32_be",
  "load64_le", "store64_le", "load64_be", "store64_be", "load128_le",
  "store128_le", "load128_be", "store128_be" ], []);

function checkEq(name) {
  return (x1, x2) => {
    if (x1 != x2) {
      my_print(name + ": equality failure, "+x1+" != "+x2);
      throw new Error();
    }
    return 0;
  };
}

const implTestLib = {
  TestLib_touch: () => 0,
  TestLib_check8: checkEq("TestLib_check8"),
  TestLib_check16: checkEq("TestLib_check16"),
  TestLib_check32: checkEq("TestLib_check32"),
  TestLib_check64: checkEq("TestLib_check64"),
  TestLib_checku8: checkEq("TestLib_checku8"),
  TestLib_checku16: checkEq("TestLib_checku16"),
  TestLib_checku32: checkEq("TestLib_checku32"),
  TestLib_checku64: checkEq("TestLib_checku64"),
  TestLib_unsafe_malloc: () => { throw new Error("todo: unsafe_malloc") },
  TestLib_perr: (err) => {
    my_print("Got error code "+err);
    return 0;
  },
  TestLib_uint8_p_null: 0,
  TestLib_uint32_p_null: 0,
  TestLib_uint64_p_null: 0,
};

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
    WasmSupport: implWasmSupport,
    FStar: implFStar,
    C: implC,
    TestLib: implTestLib
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
