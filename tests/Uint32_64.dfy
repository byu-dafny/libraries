include "../src//Collections/Sequences/Uint32_64.dfy"
module Uint32_64UnitTests {
import Uint32_64
import Uint32_64.Uint32Seq
import Uint32_64.Uint64Seq
import DivMod
import Mul
import Power
import Seq
import DivInternalsNonlinear
import DivInternals
import GeneralInternals
import MulInternalsNonlinear
import MulInternals
import Wrappers
import Math
import ModInternals
import ModInternalsNonlinear
method {:test} test0() {
var r0 := Uint32_64.ToLarge([]);
}
/*method {:test} test1() {
var r0 := Uint32_64.ToLarge([0, 0, 0, 0, 0, 0, 0]);
}*/
method {:test} test2() {
var r0 := Uint32_64.ToSmall([]);
}
method {:test} test3() {
var r0 := Uint32_64.Uint64Seq.SeqSub([0, 0, 0, 0, 0, 0, 0, 2475], [0, 0, 0, 0, 0, 0, 0, 1888]);
}
method {:test} test4() {
var r0 := Uint32_64.Uint64Seq.SeqSub([0, 0, 535], [0, 0, 536]);
}
method {:test} test5() {
var r0 := Uint32_64.Uint64Seq.SeqSub([], []);
}
method {:test} test6() {
var r0 := Uint32_64.Uint64Seq.SeqAdd([0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]);
}
method {:test} test7() {
var r0 := Uint32_64.Uint64Seq.SeqAdd([0, 0, 0, 0, 8098], [0, 0, 0, 0, 16953]);
}
method {:test} test8() {
var r0 := Uint32_64.Uint64Seq.SeqAdd([], []);
}
method {:test} test9() {
var r0 := Uint32_64.Uint64Seq.SeqZero(1);
}
method {:test} test10() {
var r0 := Uint32_64.Uint64Seq.FromNatWithLen(1236, 1);
}
method {:test} test11() {
var r0 := Uint32_64.Uint64Seq.SeqExtendMultiple([0, 0], 3);
}
method {:test} test12() {
var r0 := Uint32_64.Uint64Seq.SeqExtend([0], 1);
}
method {:test} test13() {
var r0 := Uint32_64.Uint64Seq.SeqExtend([0, 0, 0, 0, 0, 0], 7);
}
method {:test} test14() {
var r0 := Uint32_64.Uint64Seq.FromNat(2279);
}
method {:test} test15() {
var r0 := Uint32_64.Uint64Seq.FromNat(0);
}
method {:test} test16() {
var r0 := Uint32_64.Uint64Seq.ToNatLeft([]);
}
method {:test} test17() {
var r0 := Uint32_64.Uint64Seq.ToNatRight([]);
}
method {:test} test18() {
var r0 := Uint32_64.Uint32Seq.SeqSub([0, 4044], [0, 1653]);
}
method {:test} test19() {
var r0 := Uint32_64.Uint32Seq.SeqSub([0, 0, 535], [0, 0, 536]);
}
method {:test} test20() {
var r0 := Uint32_64.Uint32Seq.SeqSub([], []);
}
method {:test} test21() {
var r0 := Uint32_64.Uint32Seq.SeqAdd([0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]);
}
method {:test} test22() {
var r0 := Uint32_64.Uint32Seq.SeqAdd([0, 0, 0, 0, 8098], [0, 0, 0, 0, 16953]);
}
method {:test} test23() {
var r0 := Uint32_64.Uint32Seq.SeqAdd([], []);
}
method {:test} test24() {
var r0 := Uint32_64.Uint32Seq.SeqZero(1);
}
method {:test} test25() {
var r0 := Uint32_64.Uint32Seq.FromNatWithLen(1236, 1);
}
method {:test} test26() {
var r0 := Uint32_64.Uint32Seq.SeqExtendMultiple([0, 0], 3);
}
method {:test} test27() {
var r0 := Uint32_64.Uint32Seq.SeqExtend([0], 1);
}
method {:test} test28() {
var r0 := Uint32_64.Uint32Seq.SeqExtend([0, 0, 0, 0, 0, 0], 7);
}
method {:test} test29() {
var r0 := Uint32_64.Uint32Seq.FromNat(2279);
}
method {:test} test30() {
var r0 := Uint32_64.Uint32Seq.FromNat(0);
}
method {:test} test31() {
var r0 := Uint32_64.Uint32Seq.ToNatLeft([]);
}
method {:test} test32() {
var r0 := Uint32_64.Uint32Seq.ToNatRight([]);
}

}
