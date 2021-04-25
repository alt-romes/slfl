## Testing

The folder `tests` has two files for each test. `file.test` and `file.correct`

The `.test` file is the input passed into `ghci`, and the `.correct` file is the expected output

To test one of these files run:
```
$ diff -b tests/file.correct <(ghci Check.hs < tests/file.test | grep *Check> | sed 's/*Check> //')
```

If something is printed out to the console then the actual output and the expected output differ, and changes should be made until all tests pass.

To test all files at the same time run:
```
$ ./run-tests.sh
```
