#!/bin/bash
set -e
#export LLVM_INSTALL_PATH=/home/gihan/LLVM/install-10.0.1
#export LLVM_INSTALL_PATH=/modules/cs325/llvm-8/
#export LLVM_INSTALL_PATH=/modules/cs325/llvm-10.0.1
#export LLVM_INSTALL_PATH=/modules/cs325/llvm-12.0.1
#export LLVM_INSTALL_PATH=/tmp/LLVM/llvm-14.0.6
#export LLVM_INSTALL_PATH=/modules/cs325/llvm-15.0.0
#export LLVM_INSTALL_PATH=/modules/cs325/llvm-16.0.0
#export LLVM_INSTALL_PATH=/modules/cs325/llvm-17.0.1
export LLVM_INSTALL_PATH=/modules/cs325/llvm-18.1.8
export PATH=$LLVM_INSTALL_PATH/bin:$PATH
export LD_LIBRARY_PATH=$LLVM_INSTALL_PATH/lib:$LD_LIBRARY_PATH
CLANG=$LLVM_INSTALL_PATH/bin/clang++

module load GCC/13.3.0

DIR="$(pwd)"

### Build mccomp compiler
echo "Cleanup *****"
rm -rf ./mccomp

echo "Compile *****"

make clean
make -j mccomp

COMP=$DIR/mccomp
echo $COMP

function validate {
  $1 > perf_out
  echo
  echo $1
  grep "Result" perf_out;grep "PASSED" perf_out
  rc=$?; if [[ $rc != 0 ]]; then echo "TEST FAILED *****";exit $rc; fi;rm perf_out
#  rc=$?; if [[ $rc != 0 ]]; then echo "TEST FAILED *****"; $rc; fi;rm perf_out
}

echo "Test *****"

addition=1
factorial=1
fibonacci=1
pi=1
while=1
void=1
cosine=1
unary=1
palindrome=1
recurse=1
rfact=1

cd tests/addition/

if [ $addition == 1 ]
then	
	cd ../addition/
	pwd
	rm -rf output.ll add
	"$COMP" ./addition.c
	$CLANG driver.cpp output.ll  -o add
	validate "./add"
fi


if [ $factorial == 1 ];
then	
	cd ../factorial
	pwd
	rm -rf output.ll fact
	"$COMP" ./factorial.c
	$CLANG driver.cpp output.ll -o fact
	validate "./fact"
fi

if [ $fibonacci == 1 ];
then	
	cd ../fibonacci
	pwd
	rm -rf output.ll fib
	"$COMP" ./fibonacci.c
	$CLANG driver.cpp output.ll -o fib
	validate "./fib"
fi

if [ $pi == 1 ];
then	
	cd ../pi
	pwd
	rm -rf output.ll pi
	"$COMP" ./pi.c
	$CLANG driver.cpp output.ll -o pi
	validate "./pi"
fi

if [ $while == 1 ];
then	
	cd ../while
	pwd
	rm -rf output.ll while
	"$COMP" ./while.c
	$CLANG driver.cpp output.ll -o while
	validate "./while"
fi

if [ $void == 1 ];
then	
	cd ../void
	pwd
	rm -rf output.ll void
	"$COMP" ./void.c 
	$CLANG driver.cpp output.ll -o void
	validate "./void"
fi

if [ $cosine == 1 ];
then	
	cd ../cosine
	pwd
	rm -rf output.ll cosine
	"$COMP" ./cosine.c
	$CLANG driver.cpp output.ll -o cosine
	validate "./cosine"
fi

if [ $unary == 1 ];
then	
	cd ../unary
	pwd
	rm -rf output.ll unary
	"$COMP" ./unary.c
	$CLANG driver.cpp output.ll -o unary
	validate "./unary"
fi

if [ $recurse == 1 ];
then	
	cd ../recurse
	pwd
	rm -rf output.ll recurse
	"$COMP" ./recurse.c
	$CLANG driver.cpp output.ll -o recurse
	validate "./recurse"
fi

if [ $rfact == 1 ];
then	
	cd ../rfact
	pwd
	rm -rf output.ll rfact
	"$COMP" ./rfact.c
	$CLANG driver.cpp output.ll -o rfact
	validate "./rfact"
fi

if [ $palindrome == 1 ];
then	
	cd ../palindrome
	pwd
	rm -rf output.ll palindrome
	"$COMP" ./palindrome.c
	$CLANG driver.cpp output.ll -o palindrome
	validate "./palindrome"
fi

echo "***** ALL TESTS PASSED *****"
