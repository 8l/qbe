#!/bin/sh

DIR=`cd $(dirname "$0"); pwd`
QBE=$DIR/../obj/qbe

TMP=/tmp/qbe.zzzz

DRV=$TMP.c
ASM=$TMP.s
BIN=$TMP.bin
OUT=$TMP.out

cleanup() {
	rm -f $DRV $ASM $BIN $OUT
}

extract() {
	WHAT="$1"
	FILE="$2"

	awk "
		/^# >>> $WHAT/ {
			p = 1
			next
		}
		/^# <<</ {
			p = 0
		}
		p
	" $FILE \
	| sed -e 's/# //' \
	| sed -e 's/#$//'
}

once() {
	T="$1"

	if ! test -f $T
	then
		echo "invalid test file $T" >&2
		exit 1
	fi

	printf "%-45s" "$(basename $T)..."

	if ! $QBE -o $ASM $T
	then
		echo "[qbe fail]"
		return 1
	fi

	extract driver $T > $DRV
	extract output $T > $OUT

	if test -s $DRV
	then
		LNK="$DRV $ASM"
	else
		LNK="$ASM"
	fi

	if ! cc -no-pie -g -o $BIN $LNK
	then
		echo "[cc fail]"
		return 1
	fi

	if test -s $OUT
	then
		$BIN a b c | diff - $OUT
		RET=$?
		REASON="output"
	else
		$BIN a b c
		RET=$?
		REASON="returned $RET"
	fi

	if test $RET -ne 0
	then
		echo "[$REASON fail]"
		return 1
	fi

	echo "[ok]"
}


#trap cleanup TERM QUIT

if test -z "$1"
then
	echo "usage: tools/unit.sh {all, SSAFILE}" 2>&1
	exit 1
fi

case $1 in
	"all")
		F=0
		for T in $DIR/../test/[!_]*.ssa
		do
			once $T
			F=`expr $F + $?`
		done
		if test $F -ge 1
		then
			echo
			echo "$F test(s) failed!"
		else
			echo
			echo "All is fine!"
		fi
		exit $F
		;;
	*)
		once $1
		exit $?
		;;
esac
