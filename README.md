# Dafny Libraries With Automatically Generated Tests

This fork of Dafny Standard Library showcases the newest automatic test generation for Dafny. To skim through the generated tests without reproducing, look in the `tests` directory (note that some files don't have tests - this is normal since there are several absract modules and ghost methods. In addition, test generation does not support certain features, e.g. infinite maps).

Please clone this with `git clone --recursive`.

To reproduce and run the tests, run `make generate`. If you are on Ubuntu rather than Mac please change the verison of z3 speciifed in the Makefile accordingly. Please note that test generation can take up to several minutes for each of the `Uint`-prefixed files in `src/Collections/Sequences`. While it will be fixed soon, the alorithm may currently also spawn z3 processes that are not terminated so it will kill all z3 processes on your machine inbetween processing files.

Finally, due to Dafny's incompleteness, 5 of the 260 generated tests are invalid. These are commented out in the tests directory and if you are to generate the tests again, you would need to comment then again before measuring the coverage.

Run `make` or `make coverage` to get the coverage report.