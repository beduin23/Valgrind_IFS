# Valgrind_IFS
Provenance Tracking tool in Valgrind
```
git clone https://github.com/beduin23/Valgrind_IFS.git
cd Valgrind_IFS/valgrind-3.12.0/
./autogen.sh
./configure –prefix=`pwd`/inst 
sudo make
sudo make install
cd testcase
clang –m32 test1.c –o test1
../inst/bin/valgrind –tool=prov_trace ./test1
```
