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

# core tests (gihan)
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

# medium tests (edmund)
example_scope=1
long=1
truthiness=1
widening=1
fail=1

# hard tests (various (compiled by codethulu))
assign=0
associativity=0
global=0
infinite=0 # this infinitely loops, test manually
lazyeval=0 # only turn on for boolean short-circuiting
returns=0
scope=0
unary2=0 # if you turn this on, you deserve what you get FAILED
while2=0
two_return=0

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

echo "***** ALL BASE TESTS PASSED *****"

if [ $example_scope == 1 ];
then	
	cd ../example_scope
	pwd
	rm -rf output.ll example_scope
	"$COMP" ./example_scope.c
	$CLANG driver.cpp output.ll -o example_scope
	validate "./example_scope"
fi

if [ $long == 1 ];
then	
	cd ../long
	pwd
	rm -rf output.ll long
	"$COMP" ./long.c
	$CLANG driver.cpp output.ll -o long
	validate "./long"
fi

if [ $truthiness == 1 ];
then	
	cd ../truthiness
	pwd
	rm -rf output.ll truthiness
	"$COMP" ./truthiness.c
	$CLANG driver.cpp output.ll -o truthiness
	validate "./truthiness"
fi

if [ $widening == 1 ];
then	
	cd ../widening
	pwd
	rm -rf output.ll widening
	"$COMP" ./widening.c
	$CLANG driver.cpp output.ll -o widening
	validate "./widening"
fi

if [ $fail == 1 ];
then
	cd ../fail
	pwd
	echo "./call_undefined.c"

	if "$COMP" ./call_undefined.c; then
		echo "TEST FAILED *****"
		echo "Expected semantic error in 'call_undefined.c'! for example clang:"
		clang ./call_undefined.c
		exit 1;
	else
		echo "TEST PASSED *****"
		echo "Got semantic error! Compare with clang:"
		clang ./call_undefined.c || true
	fi

	echo "./double_func_mismatched.c"
	if "$COMP" ./double_func_mismatched.c; then
		echo "TEST FAILED *****"
		echo "Expected semantic error in 'double_func_mismatched.c'! for example clang:"
		clang ./double_func_mismatched.c
		exit 1;
	else
		echo "TEST PASSED *****"
		echo "Got semantic error! Compare with clang:"
		clang ./double_func_mismatched.c || true
	fi

	echo "./double_func.c"
	if "$COMP" ./double_func.c; then
		echo "TEST FAILED *****"
		echo "Expected semantic error in 'double_func.c'! for example clang:"
		clang ./double_func.c
		exit 1;
	else
		echo "TEST PASSED *****"
		echo "Got semantic error! Compare with clang:"
		clang ./double_func.c || true
	fi

	echo "./double_global.c"
	if "$COMP" ./double_global.c; then
		echo "TEST FAILED *****"
		echo "Expected semantic error in 'double_global.c'!"
		clang ./double_global.c
		exit 1;
	else
		echo "TEST PASSED *****"
		echo "Got semantic error!"
		clang ./double_global.c || true
	fi

	echo "./double_local.c"
	if "$COMP" ./double_local.c; then
		echo "TEST FAILED *****"
		echo "Expected semantic error in 'double_local'! for example clang:"
		clang ./double_local.c
		exit 1;
	else
		echo "TEST PASSED *****"
		echo "Got semantic error! Compare with clang:"
		clang ./double_local.c || true
	fi

	echo "./extern_fun_decl_mismatch.c"
	if "$COMP" ./extern_fun_decl_mismatch.c; then
		echo "TEST FAILED *****"
		echo "Expected semantic error in 'extern_fun_decl_mismatch.c'! for example clang:"
		clang ./extern_fun_decl_mismatch.c
		exit 1;
	else
		echo "TEST PASSED *****"
		echo "Got semantic error! Compare with clang:"
		clang ./extern_fun_decl_mismatch.c || true
	fi

	echo "./no_init_assign.c"
	if "$COMP" ./no_init_assign.c; then
		echo "TEST FAILED *****"
		echo "Expected semantic error in 'no_init_assign.c'! for example clang:"
		clang ./no_init_assign.c
		exit 1;
	else
		echo "TEST PASSED *****"
		echo "Got semantic error! Compare with clang:"
		clang ./no_init_assign.c || true
	fi

	echo "./scope_bleed.c"
	if "$COMP" ./scope_bleed.c; then
		echo "TEST FAILED *****"
		echo "Expected semantic error in 'scope_bleed.c'! for example clang:"
		clang ./scope_bleed.c
		exit 1;
	else
		echo "TEST PASSED *****"
		echo "Got semantic error! Compare with clang:"
		clang ./scope_bleed.c || true
	fi

	echo "./undefined_var.c"
	if "$COMP" ./undefined_var.c; then
		echo "TEST FAILED *****"
		echo "Expected semantic error in 'undefined_var.c'! for example clang:"
		clang ./undefined_var.c
		exit 1;
	else
		echo "TEST PASSED *****"
		echo "Got semantic error! Compare with clang:"
		clang ./undefined_var.c || true
	fi

	echo "./unexpected_ret.c"
	if "$COMP" ./unexpected_ret.c; then
		echo "TEST FAILED *****"
		echo "Expected semantic error in 'unexpected_ret.c'! for example clang:"
		clang ./unexpected_ret.c
		exit 1;
	else
		echo "TEST PASSED *****"
		echo "Got semantic error! Compare with clang:"
		clang ./unexpected_ret.c || true
	fi

	echo "./wrong_num_args.c"
	if "$COMP" ./wrong_num_args.c; then
		echo "TEST FAILED *****"
		echo "Expected semantic error in 'wrong_num_args.c'! for example clang:"
		clang ./wrong_num_args.c
		exit 1;
	else
		echo "TEST PASSED *****"
		echo "Got semantic error! Compare with clang:"
		clang ./wrong_num_args.c || true
	fi

	echo "./wrong_type_args.c"
	if "$COMP" ./wrong_type_args.c; then
		echo "TEST FAILED *****"
		echo "Expected semantic error in 'wrong_type_args.c'!"
		clang ./wrong_type_args.c
		exit 1;
	else
		echo "TEST PASSED *****"
		echo "Got semantic error!"
		clang ./wrong_type_args.c || true
	fi

	echo "./wrong_type_ret.c"
	if "$COMP" ./wrong_type_ret.c; then
		echo "TEST FAILED *****"
		echo "Expected semantic error in 'wrong_type_ret.c'!"
		clang ./wrong_type_ret.c
		exit 1;
	else
		echo "TEST PASSED *****"
		echo "Got semantic error!"
		clang ./wrong_type_ret.c || true
	fi

	echo "./no_return.c"
	if "$COMP" ./no_return.c; then
		echo "TEST FAILED *****"
		echo "Expected semantic error in 'no_return.c'!"
		clang ./no_return.c
		exit 1;
	else
		echo "TEST PASSED *****"
		echo "Got semantic error!"
		clang ./no_return.c || true
	fi
fi

echo "***** ALL MEDIUM TESTS PASSED *****"

if [ $assign == 1 ];
then	
	cd ../assign
	pwd
	rm -rf output.ll assign
	"$COMP" ./assign.c
	$CLANG driver.cpp output.ll -o assign
	validate "./assign"
fi

if [ $associativity == 1 ];
then	
	cd ../associativity
	pwd
	rm -rf output.ll associativity
	"$COMP" ./associativity.c
	$CLANG driver.cpp output.ll -o associativity
	validate "./associativity"
fi

if [ $global == 1 ];
then	
	cd ../global
	pwd
	rm -rf output.ll global
	"$COMP" ./global.c
	$CLANG driver.cpp output.ll -o global
	validate "./global"
fi

if [ $infinite == 1 ];
then	
	cd ../infinite
	pwd
	rm -rf output.ll infinite
	"$COMP" ./infinite.c
	$CLANG driver.cpp output.ll -o infinite
	validate "./infinite"
fi

if [ $lazyeval == 1 ];
then	
	cd ../lazyeval
	pwd
	rm -rf output.ll lazyeval
	"$COMP" ./lazyeval.c
	$CLANG driver.cpp output.ll -o lazyeval
	validate "./lazyeval"
fi

if [ $returns == 1 ];
then	
	cd ../returns
	pwd
	rm -rf output.ll returns
	"$COMP" ./returns.c
	$CLANG driver.cpp output.ll -o returns
	validate "./returns"
fi

if [ $scope == 1 ];
then	
	cd ../scope
	pwd
	rm -rf output.ll scope
	"$COMP" ./scope.c
	$CLANG driver.cpp output.ll -o scope
	validate "./scope"
fi

if [ $unary2 == 1 ];
then	
	cd ../unary2
	pwd
	rm -rf output.ll unary2
	"$COMP" ./unary2.c
	$CLANG driver.cpp output.ll -o unary2
	validate "./unary2"
fi

if [ $while2 == 1 ];
then	
	cd ../while2
	pwd
	rm -rf output.ll while
	"$COMP" ./while.c
	$CLANG driver.cpp output.ll -o while
	validate "./while"
fi

if [ $two_return == 1 ];
then	
	cd ../two_return
	pwd
	rm -rf output.ll two_return
	"$COMP" ./two_return.c
	$CLANG driver.cpp output.ll -o two_return
	validate "./two_return"
fi

echo "***** ALL HARD TESTS PASSED *****"

echo "***** ALL TESTS PASSED *****"

echo "https://tenor.com/en-GB/view/frodo-baggins-its-over-its-done-lotr-gif-12920799"
