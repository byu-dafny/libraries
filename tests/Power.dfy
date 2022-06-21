include "../src//NonlinearArithmetic/Power.dfy"
module PowerUnitTests {
import Power
import DivMod
import GeneralInternals
import Mul
import MulInternals
import DivInternalsNonlinear
import DivInternals
import MulInternalsNonlinear
import ModInternals
import ModInternalsNonlinear
method {:test} test0() {
var r0 := Power.Pow(0, 0);
}

}
