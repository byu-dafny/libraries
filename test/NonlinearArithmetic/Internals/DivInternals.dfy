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
// Test DivInternals.DivPos(block#235505) covers block 235500
// Test DivInternals.DivPos(block#235505) covers block 235501
// Test DivInternals.DivPos(block#235505) covers block 235505
// Extracting the test for DivInternals.DivPos(block#235505) from the counterexample...
method {:test} test0() {
expect 1797 > 0, "Test does not meet preconditions and should be removed";
var r0 := DivInternals.DivPos(-1798, 1797);
}
// Test DivInternals.DivPos(block#235504) covers block 235500
// Test DivInternals.DivPos(block#235504) covers block 235502
// Test DivInternals.DivPos(block#235504) covers block 235504
// Extracting the test for DivInternals.DivPos(block#235504) from the counterexample...
method {:test} test1() {
expect 2460 > 0, "Test does not meet preconditions and should be removed";
var r0 := DivInternals.DivPos(4417, 2460);
}
// Test DivInternals.DivPos(block#235503) covers block 235500
// Test DivInternals.DivPos(block#235503) covers block 235502
// Test DivInternals.DivPos(block#235503) covers block 235503
// Extracting the test for DivInternals.DivPos(block#235503) from the counterexample...
method {:test} test2() {
expect 1 > 0, "Test does not meet preconditions and should be removed";
var r0 := DivInternals.DivPos(0, 1);
}
// No test can be generated for DivInternals.DivRecursive(block#236418) because the verifier timed out.
// No test can be generated for DivInternals.DivRecursive(block#236417) because the verifier timed out.
// No test can be generated for DivInternals.DivRecursive(block#236416) because the verifier timed out.
// Test DivInternals.DivRecursive(block#236415) covers block 236415
// Extracting the test for DivInternals.DivRecursive(block#236415) from the counterexample...
method {:test} test3() {
expect 11 != 0, "Test does not meet preconditions and should be removed";
var r0 := DivInternals.DivRecursive(0, 11);
}

}
