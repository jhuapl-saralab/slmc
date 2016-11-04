License
=======
Copyright (c) 2016, Johns Hopkins University Applied Physics Laboratory
All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are
met:

1. Redistributions of source code must retain the above copyright
notice, this list of conditions and the following disclaimer.

2. Redistributions in binary form must reproduce the above copyright
notice, this list of conditions and the following disclaimer in the
documentation and/or other materials provided with the distribution.

3. Neither the name of the copyright holder nor the names of its
contributors may be used to endorse or promote products derived from
this software without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
"AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

About
=====

SLMC, the SLMech Compiler, is an experimental translation tool for
converting C code to the input language of the
[SLMech](https://www.github.com/jhuapl-saralab/slmech) program
verification tool.

SLMC is in very early stages of development. It supports only a narrow
subset of the C language. SLMC takes a single C or C++ input and
doesn't pass through any compiler flags to clang.

Our goal for SLMC is to provide a bidirectional transparent mapping
between C and SLMech's input language. Ideally the user of SLMech will
never have to directly interact with the SLMech program language.

Build Instructions
==================

Most of this is from the clang libtooling tutorial
http://clang.llvm.org/docs/LibASTMatchersTutorial.html

First you'll want to obtain the clang source with extra tools
component
```
	mkdir ~/clang-llvm && cd ~/clang-llvm
	git clone http://llvm.org/git/llvm.git
	cd llvm/tools
	git clone http://llvm.org/git/clang.git
	cd clang/tools
	git clone http://llvm.org/git/clang-tools-extra.git extra
```
You may also need CMake
```
	cd ~/clang-llvm
	git clone git://cmake.org/stage/cmake.git
	cd cmake
	git checkout next
	./bootstrap
	make
	sudo make install
```
Build clang
```
	cd ~/clang-llvm
	mkdir build && cd build
	cmake ../llvm -DLLVM_BUILD_TESTS=ON
	make
	make check # Test LLVM only.
	make clang-test  # Test Clang only.
	make install
```

If any of the tests do not pass it may be due to clang and llvm being
out of sync.  In that case run 'git svn rebase' in both llvm and
clang.

Next, set clang as its own compiler

```
	cd ~/clang-llvm/build
	ccmake ../llvm
```

should open a curse gui, press 't' for the advanced mode and change
CMAKE_CXX_COMPILER to /usr/local/bin/clang++ and CMAKE_C_COMPILER to
/usr/local/bin/clang, or whereever you installed the new clang build.
When you're done press 'c' to configure and 'g' to generate the CMake
files.  When this is finished, run make once more.

Now, you will want to grab SLMC and place it in the clang-llvm
tools/extra directory

```
	cd ~/
	git clone git@github.com:jhuapl-saralab/slmc.git ~/clang-llvm/llvm/tools/clang/tools/extra/slmc
	echo "add_subdirectory(slmc)" >> ~/clang-llvm/llvm/tools/clang/tools/extra/CMakeLists.txt
	cd ~/clang-llvm/build/
	cmake ../llvm
	make
```

This should create the `slmc` binary and place them in ~/clang-llvm/build/bin. 