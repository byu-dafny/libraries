include "../src//NonlinearArithmetic/Internals/MulInternals.dfy"
module MulInternalsUnitTests {
import MulInternals
import GeneralInternals
import MulInternalsNonlinear
method {:test} test0() {
var r0 := MulInternals.MulRecursive(38, 14);
}
method {:test} test1() {
var r0 := MulInternals.MulRecursive(-39, 14);
}
method {:test} test2() {
var r0 := MulInternals.MulPos(8856, 1236);
}
method {:test} test3() {
var r0 := MulInternals.MulPos(0, 0);
}

}
