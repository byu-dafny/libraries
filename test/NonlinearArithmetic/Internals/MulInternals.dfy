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
// Test MulInternals.MulPos(block#196653) covers block 196650
// Test MulInternals.MulPos(block#196653) covers block 196652
// Test MulInternals.MulPos(block#196653) covers block 196653
// Extracting the test for MulInternals.MulPos(block#196653) from the counterexample...
method {:test} test0() {
var r0 := MulInternals.MulPos(8856, 1236);
}
// Test MulInternals.MulPos(block#196651) covers block 196650
// Test MulInternals.MulPos(block#196651) covers block 196651
// Extracting the test for MulInternals.MulPos(block#196651) from the counterexample...
method {:test} test1() {
var r0 := MulInternals.MulPos(0, 0);
}
// Test MulInternals.MulRecursive(block#197595) covers block 197592
// Test MulInternals.MulRecursive(block#197595) covers block 197593
// Test MulInternals.MulRecursive(block#197595) covers block 197595
// Extracting the test for MulInternals.MulRecursive(block#197595) from the counterexample...
method {:test} test2() {
var r0 := MulInternals.MulRecursive(38, 14);
}
// Test MulInternals.MulRecursive(block#197594) covers block 197592
// Test MulInternals.MulRecursive(block#197594) covers block 197594
// Extracting the test for MulInternals.MulRecursive(block#197594) from the counterexample...
method {:test} test3() {
var r0 := MulInternals.MulRecursive(-39, 14);
}

}
