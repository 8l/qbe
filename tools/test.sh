#!/bin/sh

dir=`cd $(dirname "$0"); pwd`
bin=$dir/../obj/qbe
binref=$dir/../obj/qbe.ref

tmp=/tmp/qbe.zzzz

drv=$tmp.c
asm=$tmp.s
asmref=$tmp.ref.s
exe=$tmp.exe
out=$tmp.out

testcc() {
	echo "int main() { }" | $1 -x c -o /dev/null - >/dev/null 2>&1
	return $?
}

init() {
	case "$TARGET" in
	arm64)
		for p in aarch64-linux-musl aarch64-linux-gnu
		do
			cc="$p-gcc -no-pie"
			qemu="qemu-aarch64"
			if
				$cc -v >/dev/null 2>&1 &&
				$qemu -version >/dev/null 2>&1
			then
				if sysroot=$($cc -print-sysroot) && test -n "$sysroot"
				then
					qemu="$qemu -L $sysroot"
				fi
				break
			fi
			cc=
		done
		if test -z "$cc"
		then
			echo "Cannot find arm64 compiler or qemu."
			exit 1
		fi
		bin="$bin -t arm64"
		;;
	"")
		case `uname` in
		*Darwin*)
			cc="cc -Wl,-no_pie"
			;;
		*OpenBSD*)
			cc="cc -nopie"
			;;
		*FreeBSD*)
			cc="cc"
			;;
		*)
			cc="cc -no-pie"
			testcc "$cc" || cc="cc"
			;;
		esac
		;;
	*)
		echo "Unknown target '$TARGET'."
		exit 1
		;;
	esac
}

cleanup() {
	rm -f $drv $asm $exe $out
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
	t="$1"

	if ! test -f $t
	then
		echo "invalid test file $t" >&2
		exit 1
	fi

	if
		sed -e 1q $t |
		grep "skip.* $TARGET\( .*\)\?$" \
		>/dev/null
	then
		return 0
	fi

	printf "%-45s" "$(basename $t)..."

	if ! $bin -o $asm $t
	then
		echo "[qbe fail]"
		return 1
	fi

	if test -x $binref
	then
		$binref -o $asmref $t 2>/dev/null
	fi

	extract driver $t > $drv
	extract output $t > $out

	if test -s $drv
	then
		src="$drv $asm"
	else
		src="$asm"
	fi

	if ! $cc -g -o $exe $src
	then
		echo "[cc fail]"
		return 1
	fi

	if test -s $out
	then
		$qemu $exe a b c | diff - $out
		ret=$?
		reason="output"
	else
		$qemu $exe a b c
		ret=$?
		reason="returned $ret"
	fi

	if test $ret -ne 0
	then
		echo "[$reason fail]"
		return 1
	fi

	echo "[ok]"

	if test -f $asmref && ! cmp -s $asm $asmref
	then
		loc0=`wc -l $asm    | cut -d' ' -f1`
		loc1=`wc -l $asmref | cut -d' ' -f1`
		printf "    asm diff: %+d\n" $(($loc0 - $loc1))
		return 0
	fi
}

#trap cleanup TERM QUIT

init

if test -z "$1"
then
	echo "usage: tools/test.sh {all, SSAFILE}" 2>&1
	exit 1
fi

case "$1" in
"all")
	fail=0
	for t in $dir/../test/[!_]*.ssa
	do
		once $t
		fail=`expr $fail + $?`
	done
	if test $fail -ge 1
	then
		echo
		echo "$fail test(s) failed!"
	else
		echo
		echo "All is fine!"
	fi
	exit $fail
	;;
*)
	once $1
	exit $?
	;;
esac
