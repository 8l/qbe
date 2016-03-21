#!/bin/sh

OCAML=/usr/bin/ocaml
QBE=lisc
TMP=`mktemp -d abifuzz.XXXXXX`

failure() {
	echo "Failure at stage:" $1 >&2
	exit 1
}

if ! test -x $QBE
then
	echo "error: I must run in the directory containing $QBE." >&2
	exit 1
fi

	$OCAML tools/abi.ml $TMP c ssa
	./$QBE -o $TMP/callee.s $TMP/callee.ssa         || failure "qbe"
	c99 -o $TMP/abitest $TMP/caller.c $TMP/callee.s || failure "cc + linking"
	$TMP/abitest                                    || failure "runtime"

rm -fr $TMP
