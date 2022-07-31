include "../..//src/NonlinearArithmetic/Power.dfy"
module srcNonlinearArithmeticPowerdfyUnitTests {
import Power
import DivMod
import DivInternalsNonlinear
import DivInternals
import GeneralInternals
import ModInternals
import MulInternals
import MulInternalsNonlinear
import Mul
import ModInternalsNonlinear
// Merging boogie files...
// Converting function calls to method calls...
// Adding Impl$$ methods to support inlining...
// Removing assertions...
// Annotating blocks...
// Generating modifications...
// No test can be generated for Power.Pow(block#398220) because the verifier suceeded.
// No test can be generated for Power.Pow(block#398219) because the verifier suceeded.
// No test can be generated for Power.Pow(block#398218) because the verifier suceeded.
// Test Power.Pow(block#398217) covers block 398217
// Extracting the test for Power.Pow(block#398217) from the counterexample...
method {:test} test0() {
var r0 := Power.Pow(0, (0 as nat));
}

}
