include "../src//NonlinearArithmetic/Power.dfy"
module PowerUnitTests {
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
method {:test} test0() {
var r0 := Power.Pow(0, (0 as nat));
}

}
