# Dafny Libraries With Automatically Generated Tests

This fork of Dafny Standard Library showcases the newest automatic test generation for Dafny. To skim through the generated tests without reproducing, look in the `tests` directory (note that some files don't have tests - this is normal since there are several absract modules and ghost methods. In addition, test generation does not support certain features, e.g. infinite maps).

To reproduce and run the tests, run `make` (if you are on Ubuntu rather than Mac please change the verison of z3 speciifed in the Makefile accordingly)

The `make` file performs the following operations:

1) Builds the fork of Dafny that has the newest version of test generation on it and downloads z3 into it
2) Generates the tests for each of the files in the `src` directory and puts them in the `tests` directory
3) Compiles Dafny code to C# and creates two files - `src/AllSource.cs` and `tests/AllTests.cs`, which contain all code under test and all code including the tests, respectively
4) Creates a file `testCoverage/OnlyTests.cs`, which contains the tests but not the code under tests. This is necessary to run coverlet properly
5) Runs coverlet to produce a coverage report. By default, the report covers all namespaces, including those that are part of the standard Dafny to C# compilation pipeline
6) Extracts from the coverlet report the coverage information for each relevant Dafny module and prints it to command line
