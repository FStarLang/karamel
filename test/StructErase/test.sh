#!/bin/bash
# additional argument: options to locate the CompCert runtime library.

ulimit -S unlimited

ccomp -o StructErase StructErase_instru.c StructErase_test.c -I ../../kremlib/ $* -fstruct-passing
echo -n compcert:
./StructErase
ccomp -o StructErase StructErase_instru.c StructErase_test.c -I ../../kremlib/ $* -D__NOSTRUCT__
echo -n compcert instru:
./StructErase
for i in `seq 0 3`
do
    gcc -O$i -o StructErase StructErase_instru.c StructErase_test.c -I ../../kremlib/
    echo -n gcc -O$i:
    ./StructErase
    gcc -O$i -o StructErase StructErase_instru.c StructErase_test.c -I ../../kremlib/ -D__NOSTRUCT__ -U__SIZEOF_INT128__
    echo -n gcc -O$i instru:
    ./StructErase
done
rm StructErase StructErase*.o
