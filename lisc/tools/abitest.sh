#!/bin/sh

OCAMLC=/usr/bin/ocamlc
QBE=lisc

failure() {
	echo "Failure at stage:" $1 >&2
	exit 1
}

cleanup() {
	rm -fr $TMP
}

compile() {
	cp tools/abi.ml $TMP
	pushd $TMP > /dev/null
	if ! $OCAMLC abi.ml -o gentest
	then
		popd > /dev/null
		cleanup
		failure "abifuzz compilation"
	fi
	popd > /dev/null
}

once() {
	if test -z "$1"
	then
		$TMP/gentest $TMP c ssa
	else
		$TMP/gentest -s $1 $TMP c ssa
	fi

	./$QBE -o $TMP/callee.s $TMP/callee.ssa ||
		failure "qbe"

	c99 -g -o $TMP/abitest $TMP/caller.c $TMP/callee.s ||
		failure "cc + linking"

	$TMP/abitest ||
		failure "runtime"
}

usage() {
	echo "usage: abitest.sh [-s SEED] [-n ITERATIONS]" >&2
	exit 1
}

N=1

while test -n "$1"
do
	test -n "$2" || usage
	case "$1" in
	"-s")
		S="$2"
		N=1
		;;
	"-n")
		N="$2"
		;;
	*)
		usage
		;;
	esac
	shift 2
done

TMP=`mktemp -d abifuzz.XXXXXX`

compile

if test -n "$S"
then
	once $S
else
	for n in `seq $N`
	do
		once
		echo "$n" | grep "00$"
	done
fi

echo "All done."

cleanup
