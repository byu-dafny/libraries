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
// Test ModInternals.ModRecursive(block#231170) covers block 231165
// Test ModInternals.ModRecursive(block#231170) covers block 231166
// Test ModInternals.ModRecursive(block#231170) covers block 231170
// Extracting the test for ModInternals.ModRecursive(block#231170) from the counterexample...
method {:test} test0() {
expect 8856 > 0, "Test does not meet preconditions and should be removed";
var r0 := ModInternals.ModRecursive(-8857, 8856);
}
// Test ModInternals.ModRecursive(block#231169) covers block 231165
// Test ModInternals.ModRecursive(block#231169) covers block 231167
// Test ModInternals.ModRecursive(block#231169) covers block 231169
// Extracting the test for ModInternals.ModRecursive(block#231169) from the counterexample...
method {:test} test1() {
expect 2460 > 0, "Test does not meet preconditions and should be removed";
var r0 := ModInternals.ModRecursive(4417, 2460);
}
// Test ModInternals.ModRecursive(block#231168) covers block 231165
// Test ModInternals.ModRecursive(block#231168) covers block 231167
// Test ModInternals.ModRecursive(block#231168) covers block 231168
// Extracting the test for ModInternals.ModRecursive(block#231168) from the counterexample...
method {:test} test2() {
expect 1 > 0, "Test does not meet preconditions and should be removed";
var r0 := ModInternals.ModRecursive(0, 1);
}

}
