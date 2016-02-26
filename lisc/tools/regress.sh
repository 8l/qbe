#!/bin/sh

for t in test/*
do
	printf "Test $t ... "

	./lisc   $t 2>&1 > /tmp/out.0
	./lisc.1 $t 2>&1 > /tmp/out.1

	if diff /tmp/out.0 /tmp/out.1 > /dev/null
	then
		echo "OK"
	else
		echo "KO"
		break
	fi
done
