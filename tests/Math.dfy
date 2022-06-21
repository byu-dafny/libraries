include "../src//Math.dfy"
module MathUnitTests {
import Math
method {:test} test0() {
var r0 := Math.Max(0, 1);
}
method {:test} test1() {
var r0 := Math.Max(0, 0);
}
method {:test} test2() {
var r0 := Math.Min(7719, 7720);
}
method {:test} test3() {
var r0 := Math.Min(0, 0);
}

}
