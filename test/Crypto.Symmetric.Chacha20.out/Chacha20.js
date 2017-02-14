"use strict";

const header_size = 256;

// Some printing helpers
function p8(n) {
  return ("0"+Number(n).toString(16)).slice(-2);
}

function hexn(m8, i, m) {
  let buf = "";
  let n = m - 1;
  while (n >= 0) {
    buf += p8(m8[i+n]);
    n--;
  }
  return buf;
}

function hex32(m8, start) {
  return hexn(m8, start, 4);
}

function hex64(m8, start) {
  return hexn(m8, start, 8);
}

function hex(m8, start, len) {
  let s = "";
  for (let i = 0; i < len; ++i)
    s += p8(m8[start + i]);
  return s;
}

function p32(n) {
  return ("0000000"+Number(n).toString(16)).slice(-8);
}


// Memory layout
// -------------
//
// mem[0..3] = top-of-the-stack pointer (I32);
// mem[4..127] = scratch space for debugging.
// Conventions for debugging and "debugging format" (lolz) are in WasmDebug.ml
function init(print) {
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
          print(hex(m8, 0, 128));
          throw "unrecognized debug format:\n  buf="+buf+"\n  c=0x"+p8(c)+"\n  i="+i;
      }
      buf += " ";
    }
    print(buf);
  };

  let reserved_area_size = 128;

  // Initialize the highwater mark.
  new Uint32Array(mem.buffer)[0] = reserved_area_size;
  let imports = {
    Kremlin: {
      mem: mem,
      debug: debug,
      data_start: reserved_area_size
    }
  };
  return imports;
}

// One MUST call this function after loading a module.
function propagate(module_name, imports, instance) {
  print("Module", module_name, "successfully loaded");
  print("Adding exports into global import table:\n ", Object.keys(instance.exports));
  imports[module_name] = {};
  for (let o of Object.keys(instance.exports)) {
    imports[module_name][o] = instance.exports[o];
  }
  print("This module has a data segment of size: ", instance.exports.data_size);
  imports.Kremlin.data_start += instance.exports.data_size;
  print("Next data segment will start at: ", imports.Kremlin.data_start);
  new Uint32Array(imports.Kremlin.mem.buffer)[0] = imports.Kremlin.data_start;
  print();
}

// One MAY only call this function after all modules have been loaded and
// suitable calls to propagate have been performed.
function reserve(mem, size) {
  let m32 = new Uint32Array(mem.buffer);
  let p = m32[0];
  m32[0] += size;
  print("Reserved memory area 0x"+p32(p)+"..0x"+p32(m32[0]));
  return p;
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
  print(buf);
}

const iv = [ 0, 0, 0, 0, 0, 0, 0, 0x4a, 0, 0, 0, 0 ];
const plain =
  "Ladies and Gentlemen of the class of '99: If I could offer you only one tip " +
  "for the future, sunscreen would be it.";
const cipher = [
  0x6e, 0x2e, 0x35, 0x9a, 0x25, 0x68, 0xf9, 0x80, 0x41, 0xba, 0x07, 0x28, 0xdd,
  0x0d, 0x69, 0x81, 0xe9, 0x7e, 0x7a, 0xec, 0x1d, 0x43, 0x60, 0xc2, 0x0a, 0x27,
  0xaf, 0xcc, 0xfd, 0x9f, 0xae, 0x0b, 0xf9, 0x1b, 0x65, 0xc5, 0x52, 0x47, 0x33,
  0xab, 0x8f, 0x59, 0x3d, 0xab, 0xcd, 0x62, 0xb3, 0x57, 0x16, 0x39, 0xd6, 0x24,
  0xe6, 0x51, 0x52, 0xab, 0x8f, 0x53, 0x0c, 0x35, 0x9f, 0x08, 0x61, 0xd8, 0x07,
  0xca, 0x0d, 0xbf, 0x50, 0x0d, 0x6a, 0x61, 0x56, 0xa3, 0x8e, 0x08, 0x8a, 0x22,
  0xb6, 0x5e, 0x52, 0xbc, 0x51, 0x4d, 0x16, 0xcc, 0xf8, 0x06, 0x81, 0x8c, 0xe9,
  0x1a, 0xb7, 0x79, 0x37, 0x36, 0x5a, 0xf9, 0x0b, 0xbf, 0x74, 0xa3, 0x5b, 0xe6,
  0xb4, 0x0b, 0x8e, 0xed, 0xf2, 0x78, 0x5e, 0x42, 0x87, 0x4d ];

function main(buf1, buf2, print) {
  var imports = init(print);

  WebAssembly.instantiate(buf1, imports).then(({ module, instance }) => {
    propagate("Buffer_Utils", imports, instance);
    return WebAssembly.instantiate(buf2, imports);
  }).then(({ module, instance }) => {
    propagate("Crypto_Symmetric_Chacha20", imports, instance);

    let mem = imports.Kremlin.mem;
    let start = reserve(mem, 1024);
    dump(mem, 2*1024);

    // Allocating our parameters in the first 1k of the memory.
    let m8 = new Uint8Array(mem.buffer);
    let counter = 1;
    let len = plain.length;
    let p_key = start;
    for (let i = 0; i < 32; ++i)
      m8[p_key+i] = i;
    let p_iv = p_key + 32;
    for (let i = 0; i < iv.length; ++i)
      m8[p_iv + i] = iv[i];
    let p_plain = p_iv + iv.length;
    for (let i = 0; i < plain.length; ++i)
      m8[p_plain + i] = plain.charCodeAt(i);
    let p_cipher = p_plain + plain.length;

    let counter_mode = instance.exports.Crypto_Symmetric_Chacha20_counter_mode;
    counter_mode(p_key, p_iv, counter, len, p_plain, p_cipher);

    print("Chacha20 finished (len="+len+")");
    print("Plaintext was:");
    print(hex(m8, p_plain, len));
    print("Ciphertext is:");
    print(hex(m8, p_cipher, len));

    for (let i = 0; i < len; ++i) {
      if (m8[p_cipher+i] != cipher[i]) {
        throw (new Error("Cipher & reference differ at byte "+i));
      }
    }

    dump(mem, 2*1024);

    print("SUCCESS");
  }).catch((e) => {
    print(e);
  });
}
