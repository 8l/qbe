#!/bin/sh

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

	echo "$T... "

	if ! ./lisc $T -o $ASM
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

	if ! cc -o $BIN $LNK
	then
		echo "[cc fail]"
		return 1
	fi

	if test -s $OUT
	then
		$BIN a b c | diff - $OUT > /dev/null
		RET=$?
		REASON="output"
	else
		$BIN a b c
		RET=$?
		REASON="ret code"
	fi

	if test $RET -ne 0
	then
		echo "[$REASON fail]"
		return 1
	fi

	printf "\033[1A\033[45C[ok]\n"
}


#trap cleanup TERM QUIT

if test -z "$1"
then
	echo "usage: test/go.sh {all, SSAFILE}" 2>&1
	exit 1
fi

case $1 in
	"all")
		F=0
		for T in test/[!_]*.ssa
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
