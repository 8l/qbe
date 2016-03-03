#!/bin/sh

QBE=./lisc
CC=cc

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
			if (p)
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

	printf "$T... "

	if ! $QBE $T -o $ASM 2> /dev/null
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

	if ! $CC -o $BIN $LNK
	then
		echo "[cc fail]"
		return 1
	fi

	if test -s $OUT
	then
		$BIN | diff - $OUT > /dev/null
		RET=$?
		REASON="output"
	else
		$BIN
		RET=$?
		REASON="return"
	fi

	if test $RET -ne 0
	then
		echo "[$REASON, fail]"
		return 1
	fi

	echo "[ok]"
}


#trap cleanup TERM QUIT

case $1 in
	"all")
		F=0
		for T in test/*
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
		;;
	*)
		once $1
		exit $?
		;;
esac
