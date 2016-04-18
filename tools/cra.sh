#!/bin/sh

DIR=`cd $(dirname "$0"); pwd`
QBE=$DIR/../obj/qbe
BUGF=/tmp/bug.id
FIND=$1
FIND=${FIND:-afl-find}

if ! test -f $BUGF
then
	echo 1 > $BUGF
fi

while true
do
	ID=`cat $BUGF`

	if test `ls $FIND/crashes/id* | wc -l` -lt $ID
	then
		rm -f bug.ssa
		echo "All done!"
		exit 0
	fi

	BUG=`ls $FIND/crashes/id* | sed -ne "${ID}{p;q}"`

	echo "*** Crash $ID"
	cp $BUG bug.ssa

	$QBE bug.ssa > /dev/null
	RET=$?
	if test \( $RET -ne 0 \) -a \( $RET -ne 1 \)
	then
		exit 1
	fi

	expr $ID + 1 > $BUGF
done
