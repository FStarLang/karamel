load("Chacha20.js");
let buf1 = readbuffer("Buffer_Utils.wasm");
let buf2 = readbuffer("Crypto_Symmetric_Chacha20.wasm");
main(buf1, buf2, print);
