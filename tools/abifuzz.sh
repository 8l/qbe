#!/bin/sh

OCAMLC=${OCAMLC:-/usr/bin/ocamlc}
DIR=`cd $(dirname "$0"); pwd`
QBE=$DIR/../obj/qbe

failure() {
	echo "Failure at stage:" $1 >&2
	exit 1
}

cleanup() {
	rm -fr $TMP
}

init() {
	cp $DIR/callgen.ml $TMP
	pushd $TMP > /dev/null

	cat > Makefile << EOM

.PHONY: test
test: caller.o callee.o
	c99 -o \$@ caller.o callee.o
%.o: %.c
	c99 -c -o \$@ \$<
%.o: %.ssa
	$QBE -o \$*.s \$<
	c99 -c -o \$@ \$*.s

EOM

	if ! $OCAMLC callgen.ml -o callgen
	then
		popd > /dev/null
		cleanup
		failure "abifuzz compilation"
	fi
	popd > /dev/null
}

once() {
	if test -z "$3"
	then
		$TMP/callgen $TMP $1 $2
	else
		$TMP/callgen -s $3 $TMP $1 $2
	fi
	make -C $TMP test > /dev/null || failure "building"
	$TMP/test || failure "runtime"
}

usage() {
	echo "usage: abitest.sh [-callssa] [-callc] [-s SEED] [-n ITERATIONS]" >&2
	exit 1
}

N=1
CALLER=c
CALLEE=ssa

while test -n "$1"
do
	case "$1" in
	"-callssa")
		CALLER=c
		CALLEE=ssa
		;;
	"-callc")
		CALLER=ssa
		CALLEE=c
		;;
	"-s")
		test -n "$2" || usage
		shift
		SEED="$1"
		;;
	"-n")
		test -n "$2" || usage
		shift
		N="$1"
		;;
	*)
		usage
		;;
	esac
	shift
done

TMP=`mktemp -d abifuzz.XXXXXX`

init

if test -n "$S"
then
	once $CALLER $CALLEE $SEED
else
	for n in `seq $N`
	do
		once $CALLER $CALLEE
		echo "$n" | grep "00$"
	done
fi

echo "All done."

cleanup
