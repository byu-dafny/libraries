include "../src//NonlinearArithmetic/Internals/DivInternals.dfy"
module DivInternalsUnitTests {
import DivInternals
import GeneralInternals
import ModInternals
import MulInternals
import MulInternalsNonlinear
import Mul
import ModInternalsNonlinear
import DivInternalsNonlinear
method {:test} test0() {
var r0 := DivInternals.DivRecursive(0, 12);
}
method {:test} test1() {
var r0 := DivInternals.DivPos(-2439, 2438);
}
method {:test} test2() {
var r0 := DivInternals.DivPos(2438, 1);
}
method {:test} test3() {
var r0 := DivInternals.DivPos(0, 1);
}

}
