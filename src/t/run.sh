APP="./app"
TDIR="t"
TESTS="lex parse lannot"

if [ -f "$TDIR/$1.while" ]; then
	echo "generating test outputs for $TDIR/$1.while"
	for TEST in $TESTS; do
		echo "-- $TEST"
		$APP -t$TEST < $TDIR/$1.while | tee $TDIR/$TEST/$1.while
		echo ""
	done
	exit 0
fi

for TFILE in $TDIR/*.while; do
	printf "testing $TFILE "
	for TEST in $TESTS; do
		$APP -t$TEST < $TFILE | diff - $TDIR/$TEST/`basename $TFILE` > /tmp/testdiff
		[ $? -ne 0 ] && { echo " [$TEST failure] (see diff in /tmp/testdiff)"; exit 1; }
		printf "[$TEST ok] "
	done
	echo ""
done
