include "../../..//src/NonlinearArithmetic/Internals/ModInternals.dfy"
module srcNonlinearArithmeticInternalsModInternalsdfyUnitTests {
import ModInternals
import GeneralInternals
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
// Test ModInternals.ModRecursive(block#242541) covers block 242536
// Test ModInternals.ModRecursive(block#242541) covers block 242537
// Test ModInternals.ModRecursive(block#242541) covers block 242541
// Extracting the test for ModInternals.ModRecursive(block#242541) from the counterexample...
method {:test} test0() {
var r0 := ModInternals.ModRecursive(-2439, 2438);
}
// Test ModInternals.ModRecursive(block#242540) covers block 242536
// Test ModInternals.ModRecursive(block#242540) covers block 242538
// Test ModInternals.ModRecursive(block#242540) covers block 242540
// Extracting the test for ModInternals.ModRecursive(block#242540) from the counterexample...
method {:test} test1() {
var r0 := ModInternals.ModRecursive(2438, 1);
}
// Test ModInternals.ModRecursive(block#242539) covers block 242536
// Test ModInternals.ModRecursive(block#242539) covers block 242538
// Test ModInternals.ModRecursive(block#242539) covers block 242539
// Extracting the test for ModInternals.ModRecursive(block#242539) from the counterexample...
method {:test} test2() {
var r0 := ModInternals.ModRecursive(0, 1);
}

}
