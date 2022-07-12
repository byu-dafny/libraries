include "../src//Collections/Sequences/Uint8_32.dfy"
module Uint8_32UnitTests {
import Uint8_32
import Uint8_32.Uint8Seq
import Uint8_32.Uint32Seq
import DivMod
import DivInternalsNonlinear
import DivInternals
import GeneralInternals
import ModInternals
import MulInternals
import MulInternalsNonlinear
import Mul
import ModInternalsNonlinear
import Power
import Seq
import Wrappers
import Math
method {:test} test0() {
var d0 : seq<Uint8_32.Uint8Seq.uint> := [];
var r0 := Uint8_32.ToLarge(d0);
expect |r0| == |d0| / Uint8_32.E();
}
/*method {:test} test1() {
var d0 : seq<Uint8_32.Uint8Seq.uint> := [0, 0, 0, 0, 0, 0, 0];
var r0 := Uint8_32.ToLarge(d0);
expect |r0| == |d0| / Uint8_32.E();
}*/
method {:test} test2() {
var d0 : seq<Uint8_32.Uint32Seq.uint> := [];
var r0 := Uint8_32.ToSmall(d0);
expect |r0| == |d0| * Uint8_32.E();
}
method {:test} test3() {
var d0 : seq<Uint8_32.Uint32Seq.uint> := [0, 0, 0, 0, 0, 0, 0, 2475];
var d1 : seq<Uint8_32.Uint32Seq.uint> := [0, 0, 0, 0, 0, 0, 0, 1888];
var r0 := Uint8_32.Uint32Seq.SeqSub(d0, d1);
}
method {:test} test4() {
var d0 : seq<Uint8_32.Uint32Seq.uint> := [0, 0, 535];
var d1 : seq<Uint8_32.Uint32Seq.uint> := [0, 0, 536];
var r0 := Uint8_32.Uint32Seq.SeqSub(d0, d1);
}
method {:test} test5() {
var d0 : seq<Uint8_32.Uint32Seq.uint> := [];
var d1 : seq<Uint8_32.Uint32Seq.uint> := [];
var r0 := Uint8_32.Uint32Seq.SeqSub(d0, d1);
}
method {:test} test6() {
var d0 : seq<Uint8_32.Uint32Seq.uint> := [0, 0, 0, 0, 0, 0, 0, 0];
var d1 : seq<Uint8_32.Uint32Seq.uint> := [0, 0, 0, 0, 0, 0, 0, 0];
var r0 := Uint8_32.Uint32Seq.SeqAdd(d0, d1);
}
method {:test} test7() {
var d0 : seq<Uint8_32.Uint32Seq.uint> := [0, 0, 0, 0, 8098];
var d1 : seq<Uint8_32.Uint32Seq.uint> := [0, 0, 0, 0, 16953];
var r0 := Uint8_32.Uint32Seq.SeqAdd(d0, d1);
}
method {:test} test8() {
var d0 : seq<Uint8_32.Uint32Seq.uint> := [];
var d1 : seq<Uint8_32.Uint32Seq.uint> := [];
var r0 := Uint8_32.Uint32Seq.SeqAdd(d0, d1);
}
method {:test} test9() {
var r0 := Uint8_32.Uint32Seq.SeqZero((1 as nat));
expect |r0| == (1 as nat);
expect Uint8_32.Uint32Seq.ToNatRight(r0) == 0;
}
method {:test} test10() {
var r0 := Uint8_32.Uint32Seq.FromNatWithLen((1236 as nat), (1 as nat));
expect |r0| == (1 as nat);
expect Uint8_32.Uint32Seq.ToNatRight(r0) == (1236 as nat);
}
method {:test} test11() {
var d0 : seq<Uint8_32.Uint32Seq.uint> := [0, 0];
var r0 := Uint8_32.Uint32Seq.SeqExtendMultiple(d0, (3 as nat));
expect |r0| % (3 as nat) == 0;
expect Uint8_32.Uint32Seq.ToNatRight(r0) == Uint8_32.Uint32Seq.ToNatRight(d0);
}
method {:test} test12() {
var d0 : seq<Uint8_32.Uint32Seq.uint> := [0];
var r0 := Uint8_32.Uint32Seq.SeqExtend(d0, (1 as nat));
expect |r0| == (1 as nat);
expect Uint8_32.Uint32Seq.ToNatRight(r0) == Uint8_32.Uint32Seq.ToNatRight(d0);
}
method {:test} test13() {
var d0 : seq<Uint8_32.Uint32Seq.uint> := [0, 0, 0, 0, 0, 0];
var r0 := Uint8_32.Uint32Seq.SeqExtend(d0, (7 as nat));
expect |r0| == (7 as nat);
expect Uint8_32.Uint32Seq.ToNatRight(r0) == Uint8_32.Uint32Seq.ToNatRight(d0);
}
method {:test} test14() {
var r0 := Uint8_32.Uint32Seq.FromNat((2279 as nat));
}
method {:test} test15() {
var r0 := Uint8_32.Uint32Seq.FromNat((0 as nat));
}
method {:test} test16() {
var d0 : seq<Uint8_32.Uint32Seq.uint> := [];
var r0 := Uint8_32.Uint32Seq.ToNatLeft(d0);
}
method {:test} test17() {
var d0 : seq<Uint8_32.Uint32Seq.uint> := [];
var r0 := Uint8_32.Uint32Seq.ToNatRight(d0);
}
method {:test} test18() {
var d0 : seq<Uint8_32.Uint8Seq.uint> := [0, 4044];
var d1 : seq<Uint8_32.Uint8Seq.uint> := [0, 1653];
var r0 := Uint8_32.Uint8Seq.SeqSub(d0, d1);
}
method {:test} test19() {
var d0 : seq<Uint8_32.Uint8Seq.uint> := [0, 0, 535];
var d1 : seq<Uint8_32.Uint8Seq.uint> := [0, 0, 536];
var r0 := Uint8_32.Uint8Seq.SeqSub(d0, d1);
}
method {:test} test20() {
var d0 : seq<Uint8_32.Uint8Seq.uint> := [];
var d1 : seq<Uint8_32.Uint8Seq.uint> := [];
var r0 := Uint8_32.Uint8Seq.SeqSub(d0, d1);
}
method {:test} test21() {
var d0 : seq<Uint8_32.Uint8Seq.uint> := [0, 0, 0, 0, 0, 0, 0, 0];
var d1 : seq<Uint8_32.Uint8Seq.uint> := [0, 0, 0, 0, 0, 0, 0, 0];
var r0 := Uint8_32.Uint8Seq.SeqAdd(d0, d1);
}
method {:test} test22() {
var d0 : seq<Uint8_32.Uint8Seq.uint> := [0, 0, 0, 0, 8098];
var d1 : seq<Uint8_32.Uint8Seq.uint> := [0, 0, 0, 0, 16953];
var r0 := Uint8_32.Uint8Seq.SeqAdd(d0, d1);
}
method {:test} test23() {
var d0 : seq<Uint8_32.Uint8Seq.uint> := [];
var d1 : seq<Uint8_32.Uint8Seq.uint> := [];
var r0 := Uint8_32.Uint8Seq.SeqAdd(d0, d1);
}
method {:test} test24() {
var r0 := Uint8_32.Uint8Seq.SeqZero((1 as nat));
expect |r0| == (1 as nat);
expect Uint8_32.Uint8Seq.ToNatRight(r0) == 0;
}
/*method {:test} test25() {
var r0 := Uint8_32.Uint8Seq.FromNatWithLen((1236 as nat), (1 as nat));
expect |r0| == (1 as nat);
expect Uint8_32.Uint8Seq.ToNatRight(r0) == (1236 as nat);
}*/
method {:test} test26() {
var d0 : seq<Uint8_32.Uint8Seq.uint> := [0, 0];
var r0 := Uint8_32.Uint8Seq.SeqExtendMultiple(d0, (3 as nat));
expect |r0| % (3 as nat) == 0;
expect Uint8_32.Uint8Seq.ToNatRight(r0) == Uint8_32.Uint8Seq.ToNatRight(d0);
}
method {:test} test27() {
var d0 : seq<Uint8_32.Uint8Seq.uint> := [0];
var r0 := Uint8_32.Uint8Seq.SeqExtend(d0, (1 as nat));
expect |r0| == (1 as nat);
expect Uint8_32.Uint8Seq.ToNatRight(r0) == Uint8_32.Uint8Seq.ToNatRight(d0);
}
method {:test} test28() {
var d0 : seq<Uint8_32.Uint8Seq.uint> := [0, 0, 0, 0, 0, 0];
var r0 := Uint8_32.Uint8Seq.SeqExtend(d0, (7 as nat));
expect |r0| == (7 as nat);
expect Uint8_32.Uint8Seq.ToNatRight(r0) == Uint8_32.Uint8Seq.ToNatRight(d0);
}
method {:test} test29() {
var r0 := Uint8_32.Uint8Seq.FromNat((2279 as nat));
}
method {:test} test30() {
var r0 := Uint8_32.Uint8Seq.FromNat((0 as nat));
}
method {:test} test31() {
var d0 : seq<Uint8_32.Uint8Seq.uint> := [];
var r0 := Uint8_32.Uint8Seq.ToNatLeft(d0);
}
method {:test} test32() {
var d0 : seq<Uint8_32.Uint8Seq.uint> := [];
var r0 := Uint8_32.Uint8Seq.ToNatRight(d0);
}

}
