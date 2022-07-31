include "../../..//src/NonlinearArithmetic/Internals/DivInternals.dfy"
module srcNonlinearArithmeticInternalsDivInternalsdfyUnitTests {
import DivInternals
import GeneralInternals
import ModInternals
import MulInternals
import MulInternalsNonlinear
import Mul
import ModInternalsNonlinear
import DivInternalsNonlinear
// Merging boogie files...
// Converting function calls to method calls...
// Adding Impl$$ methods to support inlining...
// Removing assertions...
// Annotating blocks...
// Generating modifications...
// Test DivInternals.DivPos(block#249261) covers block 249256
// Test DivInternals.DivPos(block#249261) covers block 249257
// Test DivInternals.DivPos(block#249261) covers block 249261
// Extracting the test for DivInternals.DivPos(block#249261) from the counterexample...
method {:test} test0() {
var r0 := DivInternals.DivPos(-2439, 2438);
}
// Test DivInternals.DivPos(block#249260) covers block 249256
// Test DivInternals.DivPos(block#249260) covers block 249258
// Test DivInternals.DivPos(block#249260) covers block 249260
// Extracting the test for DivInternals.DivPos(block#249260) from the counterexample...
method {:test} test1() {
var r0 := DivInternals.DivPos(2438, 1);
}
// Test DivInternals.DivPos(block#249259) covers block 249256
// Test DivInternals.DivPos(block#249259) covers block 249258
// Test DivInternals.DivPos(block#249259) covers block 249259
// Extracting the test for DivInternals.DivPos(block#249259) from the counterexample...
method {:test} test2() {
var r0 := DivInternals.DivPos(0, 1);
}
// No test can be generated for DivInternals.DivRecursive(block#250455) because the verifier suceeded.
// No test can be generated for DivInternals.DivRecursive(block#250454) because the verifier suceeded.
// No test can be generated for DivInternals.DivRecursive(block#250453) because the verifier suceeded.
// Test DivInternals.DivRecursive(block#250452) covers block 250452
// Extracting the test for DivInternals.DivRecursive(block#250452) from the counterexample...
method {:test} test3() {
var r0 := DivInternals.DivRecursive(0, 12);
}

}
