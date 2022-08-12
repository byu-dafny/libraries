include "../../..//src/NonlinearArithmetic/Internals/MulInternals.dfy"
module srcNonlinearArithmeticInternalsMulInternalsdfyUnitTests {
import MulInternals
import GeneralInternals
import MulInternalsNonlinear
// Merging boogie files...
// Converting function calls to method calls...
// Adding Impl$$ methods to support inlining...
// Removing assertions...
// Annotating blocks...
// Generating modifications...
// Test MulInternals.MulPos(block#187413) covers block 187410
// Test MulInternals.MulPos(block#187413) covers block 187412
// Test MulInternals.MulPos(block#187413) covers block 187413
// Extracting the test for MulInternals.MulPos(block#187413) from the counterexample...
method {:test} test0() {
expect 1799 >= 0, "Test does not meet preconditions and should be removed";
var r0 := MulInternals.MulPos(1799, -7719);
}
// Test MulInternals.MulPos(block#187411) covers block 187410
// Test MulInternals.MulPos(block#187411) covers block 187411
// Extracting the test for MulInternals.MulPos(block#187411) from the counterexample...
method {:test} test1() {
expect 0 >= 0, "Test does not meet preconditions and should be removed";
var r0 := MulInternals.MulPos(0, 0);
}
// Test MulInternals.MulRecursive(block#188345) covers block 188342
// Test MulInternals.MulRecursive(block#188345) covers block 188343
// Test MulInternals.MulRecursive(block#188345) covers block 188345
// Extracting the test for MulInternals.MulRecursive(block#188345) from the counterexample...
method {:test} test2() {
var r0 := MulInternals.MulRecursive(1238, -7719);
}
// No test can be generated for MulInternals.MulRecursive(block#188344) because the verifier timed out.

}
