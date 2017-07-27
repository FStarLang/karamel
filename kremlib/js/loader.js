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

  // unit -> unit
  let trap = (_) => {
    my_print("Run-time trap, e.g. zero-sized array.");
    throw new Error();
  };

  // Initialize the highwater mark.
  new Uint32Array(mem.buffer)[0] = header_size;
  let imports = {
    Kremlin: {
      mem: mem,
      __debug: debug,
      __trap: trap,
      data_start: header_size
    }
  };
  return imports;
}

// One MUST call this function after loading a module.
function propagate(module_name, imports, instance) {
  my_print("Module", module_name, "successfully loaded");
  my_print("Adding exports into global import table:\n ", Object.keys(instance.exports));
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
