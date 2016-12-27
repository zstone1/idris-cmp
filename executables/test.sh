#!bash/bin


cd ../CompilerFiles
idris -p effects -p lightyear -p contrib --ibcsubdir Bin --total Root.idr -o ../Testing/comp
cd ../Testing

temp="/home/zach/tmp/comptest"
mkdir -p "$temp"
mkdir -p "asm"
mkdir -p "results"
mkdir -p test-prgms
failures=()
for tfile in  test-prgms/*.tst; do
	### get the test's real name
	t=${tfile##*/}
	t=${t%.*}
	echo "$t"
	### compile and execute the test
	./comp "$tfile" "asm/$t.asm"
	nasm -felf64 "asm/$t.asm" -o "$temp/$t.o" 
	ld "$temp/$t.o" -o "$temp/$t.out"
	"$temp/$t.out" > "results/$t.txt"
	### compare to expected result
	d=$(diff "expected/$t.expt" "results/$t.txt")
	if [ "$d" != "" ]
	then
		echo "failure"
		failures+=("$t")
	fi
done
echo "Failures: $failures"

