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
// No test can be generated for Power.Pow(block#378666) because the verifier timed out.
// No test can be generated for Power.Pow(block#378665) because the verifier timed out.
// No test can be generated for Power.Pow(block#378664) because the verifier timed out.
// Test Power.Pow(block#378663) covers block 378663
// Extracting the test for Power.Pow(block#378663) from the counterexample...
method {:test} test0() {
var r0 := Power.Pow(0, (0 as nat));
}

}
