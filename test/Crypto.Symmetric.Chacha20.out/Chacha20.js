// Just a wrapper around the generated Web Assembly
let buf1 = readbuffer("Buffer_Utils.wasm");
let buf2 = readbuffer("Crypto_Symmetric_Chacha20.wasm");
print("read two files");

let mem = new WebAssembly.Memory({ initial: 16 });
let imports = {
  Shared: {
    mem: mem
  }
};
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
}, (e) => {
  print(e);
});
