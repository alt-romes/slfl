tests=( "unit" )
for t in "${tests[@]}"
do
    diff -b tests/$t.correct <(ghci Check.hs < tests/$t.test | grep *Check | sed 's/*Check> //') ||
        if echo "Test failed:"; then
            echo tests/$t
            exit
        fi
done
echo "All tests passed"
