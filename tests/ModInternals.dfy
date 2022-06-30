include "../src//NonlinearArithmetic/Internals/ModInternals.dfy"
module ModInternalsUnitTests {
import ModInternals
import GeneralInternals
import MulInternals
import MulInternalsNonlinear
import Mul
import ModInternalsNonlinear
import DivInternalsNonlinear
method {:test} test0() {
var r0 := ModInternals.ModRecursive(-2439, 2438);
}
method {:test} test1() {
var r0 := ModInternals.ModRecursive(2438, 1);
}
method {:test} test2() {
var r0 := ModInternals.ModRecursive(0, 1);
}

}
