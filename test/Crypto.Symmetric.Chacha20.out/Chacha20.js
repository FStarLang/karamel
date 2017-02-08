const header_size = 256;

// Memory layout
// -------------
//
// mem[0..3] = top-of-the-stack pointer (I32);
// mem[4..127] = scratch space for a zero-terminated string (to be written by
//   Wasm code, to be printed by the debug function)
function init(print) {
  let mem = new WebAssembly.Memory({ initial: 16 });
  let m8 = new Uint8Array(mem.buffer);

  let debug = () => {
    let s = "";
    let i = 4;
    while (m8[i] != 0 && i < 128) {
      s += String.fromCharCode(m8[i]);
      i++;
    }
    print(s);
  };

  // Initialize the highwater mark.
  new Uint32Array(mem.buffer)[0] = header_size;
  let imports = {
    Kremlin: {
      mem: mem,
      debug: debug
    }
  };
  return imports;
}

// Reserve some portion of the memory at the beginning for some private data
// structures, or arguments to be passed to the functions. The Wasm code will
// not touch these. Size is a number of bytes.
function reserve(mem, size) {
  new Uint32Array(mem.buffer)[0] = size+header_size;
  return 4;
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
    print("Buffer_Utils ok");
    print("Exports: "+Object.keys(instance.exports));
    imports.Buffer_Utils = {};
    for (let o of Object.keys(instance.exports)) {
      imports.Buffer_Utils[o] = instance.exports[o];
    }
    return WebAssembly.instantiate(buf2, imports);
  }).then(({ module, instance }) => {
    print("Crypto_Symmetric_Chacha20 ok");
    print("Exports: "+Object.keys(instance.exports));

    let mem = imports.Kremlin.mem;
    reserve(mem, 1024);

    // Allocating our parameters in the first 1k of the memory.
    let m8 = new Uint8Array(mem);
    let p_key = header_size;
    for (let i = 0; i < 32; ++i)
      m8[p_key+i] = i;
    let p_iv = p_key + 32;
    for (let i = 0; i < iv.length; ++i)
      m8[p_iv + i] = iv[i];
    let p_plain = p_iv + iv.length;
    for (let i = 0; i < plain.length; ++i)
      m8[p_plain + i] = plain[i];
    let p_cipher = p_plain + plain.length;
    let counter = 1;

    let counter_mode = instance.exports.Crypto_Symmetric_Chacha20_counter_mode;
    counter_mode(p_key, p_iv, counter, plain.length, p_plain, p_cipher);

    for (let i = 0; i < cipher.len; ++i) {
      if (m8[p_cipher+i] != cipher[i]) {
        throw (new Error("Cipher & reference differ at byte "+i));
      }
    }
    print("SUCCESS");
  }).catch((e) => {
    print(e);
  });
}
