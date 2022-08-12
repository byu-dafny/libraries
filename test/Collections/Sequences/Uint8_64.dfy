// Warning: Values of type Uint8_64.Uint8Seq.uint will be assigned a default value of type int, which may or may not match the associated condition
// Warning: Values of type Uint8_64.Uint64Seq.uint will be assigned a default value of type int, which may or may not match the associated condition
include "../../..//src/Collections/Sequences/Uint8_64.dfy"
module srcCollectionsSequencesUint8_64dfyUnitTests {
import Uint8_64
import Uint8_64.Uint8Seq
import Uint8_64.Uint64Seq
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
// Warning: Values of type Uint8_64.Uint8Seq.uint will be assigned a default value of type int, which may or may not match the associated condition
// Warning: Values of type Uint8_64.Uint64Seq.uint will be assigned a default value of type int, which may or may not match the associated condition
// Warning: Values of type Uint8_64.Uint8Seq.uint will be assigned a default value of type int, which may or may not match the associated condition
// Warning: Values of type Uint8_64.Uint64Seq.uint will be assigned a default value of type int, which may or may not match the associated condition
// Merging boogie files...
// Converting function calls to method calls...
// Adding Impl$$ methods to support inlining...
// Removing assertions...
// Annotating blocks...
// Generating modifications...
// No test can be generated for Uint8_64.Uint8Seq.ToNatRight(block#1146788) because the verifier timed out.
// No test can be generated for Uint8_64.Uint8Seq.ToNatRight(block#1146787) because the verifier timed out.
// No test can be generated for Uint8_64.Uint8Seq.ToNatRight(block#1146786) because the verifier timed out.
// Test Uint8_64.Uint8Seq.ToNatRight(block#1146785) covers block 1146785
// Extracting the test for Uint8_64.Uint8Seq.ToNatRight(block#1146785) from the counterexample...
method {:test} test0() {
var d0 : seq<Uint8_64.Uint8Seq.uint> := [];
var r0 := Uint8_64.Uint8Seq.ToNatRight(d0);
}
// No test can be generated for Uint8_64.Uint8Seq.ToNatLeft(block#1148188) because the verifier timed out.
// No test can be generated for Uint8_64.Uint8Seq.ToNatLeft(block#1148187) because the verifier timed out.
// No test can be generated for Uint8_64.Uint8Seq.ToNatLeft(block#1148186) because the verifier timed out.
// Test Uint8_64.Uint8Seq.ToNatLeft(block#1148185) covers block 1148185
// Extracting the test for Uint8_64.Uint8Seq.ToNatLeft(block#1148185) from the counterexample...
method {:test} test1() {
var d0 : seq<Uint8_64.Uint8Seq.uint> := [];
var r0 := Uint8_64.Uint8Seq.ToNatLeft(d0);
}
// Test Uint8_64.Uint8Seq.FromNat(block#1166103) covers block 1166100
// Test Uint8_64.Uint8Seq.FromNat(block#1166103) covers block 1166102
// Test Uint8_64.Uint8Seq.FromNat(block#1166103) covers block 1166103
// Extracting the test for Uint8_64.Uint8Seq.FromNat(block#1166103) from the counterexample...
method {:test} test2() {
var r0 := Uint8_64.Uint8Seq.FromNat((65 as nat));
}
// Test Uint8_64.Uint8Seq.FromNat(block#1166101) covers block 1166100
// Test Uint8_64.Uint8Seq.FromNat(block#1166101) covers block 1166101
// Extracting the test for Uint8_64.Uint8Seq.FromNat(block#1166101) from the counterexample...
method {:test} test3() {
var r0 := Uint8_64.Uint8Seq.FromNat((0 as nat));
}
// No test can be generated for Uint8_64.Uint8Seq.SeqExtend(block#1169395) because the verifier timed out.
// No test can be generated for Uint8_64.Uint8Seq.SeqExtend(block#1169394) because the verifier timed out.
// No test can be generated for Uint8_64.Uint8Seq.SeqExtend(block#1169393) because the verifier timed out.
// Test Uint8_64.Uint8Seq.SeqExtend(block#1169392) covers block 1169392
// Extracting the test for Uint8_64.Uint8Seq.SeqExtend(block#1169392) from the counterexample...
method {:test} test4() {
var d0 : seq<Uint8_64.Uint8Seq.uint> := [(0 as Uint8_64.Uint8Seq.uint)];
expect |d0| <= (1 as nat), "Test does not meet preconditions and should be removed";
var r0 := Uint8_64.Uint8Seq.SeqExtend(d0, (1 as nat));
expect |r0| == (1 as nat);
expect Uint8_64.Uint8Seq.ToNatRight(r0) == Uint8_64.Uint8Seq.ToNatRight(d0);
}
// No test can be generated for Uint8_64.Uint8Seq.SeqExtendMultiple(block#1170574) because the verifier timed out.
// No test can be generated for Uint8_64.Uint8Seq.FromNatWithLen(block#1171652) because the verifier timed out.
// No test can be generated for Uint8_64.Uint8Seq.SeqZero(block#1173229) because the verifier timed out.
// Test Uint8_64.Uint8Seq.SeqAdd(block#1178346) covers block 1178340
// Test Uint8_64.Uint8Seq.SeqAdd(block#1178346) covers block 1178342
// Test Uint8_64.Uint8Seq.SeqAdd(block#1178346) covers block 1178343
// Test Uint8_64.Uint8Seq.SeqAdd(block#1178346) covers block 1178345
// Test Uint8_64.Uint8Seq.SeqAdd(block#1178346) covers block 1178346
// Extracting the test for Uint8_64.Uint8Seq.SeqAdd(block#1178346) from the counterexample...
method {:test} test5() {
var d0 : seq<Uint8_64.Uint8Seq.uint> := [(0 as Uint8_64.Uint8Seq.uint), (0 as Uint8_64.Uint8Seq.uint)];
var d1 : seq<Uint8_64.Uint8Seq.uint> := [(0 as Uint8_64.Uint8Seq.uint), (0 as Uint8_64.Uint8Seq.uint)];
expect |d0| == |d1|, "Test does not meet preconditions and should be removed";
var r0 := Uint8_64.Uint8Seq.SeqAdd(d0, d1);
}
// Test Uint8_64.Uint8Seq.SeqAdd(block#1178344) covers block 1178340
// Test Uint8_64.Uint8Seq.SeqAdd(block#1178344) covers block 1178342
// Test Uint8_64.Uint8Seq.SeqAdd(block#1178344) covers block 1178344
// Extracting the test for Uint8_64.Uint8Seq.SeqAdd(block#1178344) from the counterexample...
method {:test} test6() {
var d0 : seq<Uint8_64.Uint8Seq.uint> := [(12 as Uint8_64.Uint8Seq.uint), (2283 as Uint8_64.Uint8Seq.uint)];
var d1 : seq<Uint8_64.Uint8Seq.uint> := [(281 as Uint8_64.Uint8Seq.uint), (11138 as Uint8_64.Uint8Seq.uint)];
expect |d0| == |d1|, "Test does not meet preconditions and should be removed";
var r0 := Uint8_64.Uint8Seq.SeqAdd(d0, d1);
}
// Test Uint8_64.Uint8Seq.SeqAdd(block#1178341) covers block 1178340
// Test Uint8_64.Uint8Seq.SeqAdd(block#1178341) covers block 1178341
// Extracting the test for Uint8_64.Uint8Seq.SeqAdd(block#1178341) from the counterexample...
method {:test} test7() {
var d0 : seq<Uint8_64.Uint8Seq.uint> := [];
var d1 : seq<Uint8_64.Uint8Seq.uint> := [];
expect |d0| == |d1|, "Test does not meet preconditions and should be removed";
var r0 := Uint8_64.Uint8Seq.SeqAdd(d0, d1);
}
// Test Uint8_64.Uint8Seq.SeqSub(block#1185608) covers block 1185602
// Test Uint8_64.Uint8Seq.SeqSub(block#1185608) covers block 1185604
// Test Uint8_64.Uint8Seq.SeqSub(block#1185608) covers block 1185605
// Test Uint8_64.Uint8Seq.SeqSub(block#1185608) covers block 1185607
// Test Uint8_64.Uint8Seq.SeqSub(block#1185608) covers block 1185608
// Extracting the test for Uint8_64.Uint8Seq.SeqSub(block#1185608) from the counterexample...
method {:test} test8() {
var d0 : seq<Uint8_64.Uint8Seq.uint> := [(1325 as Uint8_64.Uint8Seq.uint), (2331 as Uint8_64.Uint8Seq.uint)];
var d1 : seq<Uint8_64.Uint8Seq.uint> := [(234 as Uint8_64.Uint8Seq.uint), (1796 as Uint8_64.Uint8Seq.uint)];
expect |d0| == |d1|, "Test does not meet preconditions and should be removed";
var r0 := Uint8_64.Uint8Seq.SeqSub(d0, d1);
}
// Test Uint8_64.Uint8Seq.SeqSub(block#1185606) covers block 1185602
// Test Uint8_64.Uint8Seq.SeqSub(block#1185606) covers block 1185604
// Test Uint8_64.Uint8Seq.SeqSub(block#1185606) covers block 1185606
// Extracting the test for Uint8_64.Uint8Seq.SeqSub(block#1185606) from the counterexample...
method {:test} test9() {
var d0 : seq<Uint8_64.Uint8Seq.uint> := [(920 as Uint8_64.Uint8Seq.uint), (2061 as Uint8_64.Uint8Seq.uint)];
var d1 : seq<Uint8_64.Uint8Seq.uint> := [(645 as Uint8_64.Uint8Seq.uint), (2062 as Uint8_64.Uint8Seq.uint)];
expect |d0| == |d1|, "Test does not meet preconditions and should be removed";
var r0 := Uint8_64.Uint8Seq.SeqSub(d0, d1);
}
// Test Uint8_64.Uint8Seq.SeqSub(block#1185603) covers block 1185602
// Test Uint8_64.Uint8Seq.SeqSub(block#1185603) covers block 1185603
// Extracting the test for Uint8_64.Uint8Seq.SeqSub(block#1185603) from the counterexample...
method {:test} test10() {
var d0 : seq<Uint8_64.Uint8Seq.uint> := [];
var d1 : seq<Uint8_64.Uint8Seq.uint> := [];
expect |d0| == |d1|, "Test does not meet preconditions and should be removed";
var r0 := Uint8_64.Uint8Seq.SeqSub(d0, d1);
}
// No test can be generated for Uint8_64.Uint64Seq.ToNatRight(block#1221294) because the verifier timed out.
// No test can be generated for Uint8_64.Uint64Seq.ToNatRight(block#1221293) because the verifier timed out.
// No test can be generated for Uint8_64.Uint64Seq.ToNatRight(block#1221292) because the verifier timed out.
// Test Uint8_64.Uint64Seq.ToNatRight(block#1221291) covers block 1221291
// Extracting the test for Uint8_64.Uint64Seq.ToNatRight(block#1221291) from the counterexample...
method {:test} test11() {
var d0 : seq<Uint8_64.Uint64Seq.uint> := [];
var r0 := Uint8_64.Uint64Seq.ToNatRight(d0);
}
// No test can be generated for Uint8_64.Uint64Seq.ToNatLeft(block#1222694) because the verifier timed out.
// No test can be generated for Uint8_64.Uint64Seq.ToNatLeft(block#1222693) because the verifier timed out.
// No test can be generated for Uint8_64.Uint64Seq.ToNatLeft(block#1222692) because the verifier timed out.
// Test Uint8_64.Uint64Seq.ToNatLeft(block#1222691) covers block 1222691
// Extracting the test for Uint8_64.Uint64Seq.ToNatLeft(block#1222691) from the counterexample...
method {:test} test12() {
var d0 : seq<Uint8_64.Uint64Seq.uint> := [];
var r0 := Uint8_64.Uint64Seq.ToNatLeft(d0);
}
// Test Uint8_64.Uint64Seq.FromNat(block#1240609) covers block 1240606
// Test Uint8_64.Uint64Seq.FromNat(block#1240609) covers block 1240608
// Test Uint8_64.Uint64Seq.FromNat(block#1240609) covers block 1240609
// Extracting the test for Uint8_64.Uint64Seq.FromNat(block#1240609) from the counterexample...
method {:test} test13() {
var r0 := Uint8_64.Uint64Seq.FromNat((65 as nat));
}
// Test Uint8_64.Uint64Seq.FromNat(block#1240607) covers block 1240606
// Test Uint8_64.Uint64Seq.FromNat(block#1240607) covers block 1240607
// Extracting the test for Uint8_64.Uint64Seq.FromNat(block#1240607) from the counterexample...
method {:test} test14() {
var r0 := Uint8_64.Uint64Seq.FromNat((0 as nat));
}
// No test can be generated for Uint8_64.Uint64Seq.SeqExtend(block#1243901) because the verifier timed out.
// No test can be generated for Uint8_64.Uint64Seq.SeqExtend(block#1243900) because the verifier timed out.
// No test can be generated for Uint8_64.Uint64Seq.SeqExtend(block#1243899) because the verifier timed out.
// Test Uint8_64.Uint64Seq.SeqExtend(block#1243898) covers block 1243898
// Extracting the test for Uint8_64.Uint64Seq.SeqExtend(block#1243898) from the counterexample...
method {:test} test15() {
var d0 : seq<Uint8_64.Uint64Seq.uint> := [(0 as Uint8_64.Uint64Seq.uint)];
expect |d0| <= (1 as nat), "Test does not meet preconditions and should be removed";
var r0 := Uint8_64.Uint64Seq.SeqExtend(d0, (1 as nat));
expect |r0| == (1 as nat);
expect Uint8_64.Uint64Seq.ToNatRight(r0) == Uint8_64.Uint64Seq.ToNatRight(d0);
}
// No test can be generated for Uint8_64.Uint64Seq.SeqExtendMultiple(block#1245080) because the verifier timed out.
// No test can be generated for Uint8_64.Uint64Seq.FromNatWithLen(block#1246158) because the verifier timed out.
// No test can be generated for Uint8_64.Uint64Seq.SeqZero(block#1247735) because the verifier timed out.
// Test Uint8_64.Uint64Seq.SeqAdd(block#1252852) covers block 1252846
// Test Uint8_64.Uint64Seq.SeqAdd(block#1252852) covers block 1252848
// Test Uint8_64.Uint64Seq.SeqAdd(block#1252852) covers block 1252849
// Test Uint8_64.Uint64Seq.SeqAdd(block#1252852) covers block 1252851
// Test Uint8_64.Uint64Seq.SeqAdd(block#1252852) covers block 1252852
// Extracting the test for Uint8_64.Uint64Seq.SeqAdd(block#1252852) from the counterexample...
method {:test} test16() {
var d0 : seq<Uint8_64.Uint64Seq.uint> := [(0 as Uint8_64.Uint64Seq.uint), (0 as Uint8_64.Uint64Seq.uint)];
var d1 : seq<Uint8_64.Uint64Seq.uint> := [(0 as Uint8_64.Uint64Seq.uint), (0 as Uint8_64.Uint64Seq.uint)];
expect |d0| == |d1|, "Test does not meet preconditions and should be removed";
var r0 := Uint8_64.Uint64Seq.SeqAdd(d0, d1);
}
// Test Uint8_64.Uint64Seq.SeqAdd(block#1252850) covers block 1252846
// Test Uint8_64.Uint64Seq.SeqAdd(block#1252850) covers block 1252848
// Test Uint8_64.Uint64Seq.SeqAdd(block#1252850) covers block 1252850
// Extracting the test for Uint8_64.Uint64Seq.SeqAdd(block#1252850) from the counterexample...
method {:test} test17() {
var d0 : seq<Uint8_64.Uint64Seq.uint> := [(342 as Uint8_64.Uint64Seq.uint), (4720 as Uint8_64.Uint64Seq.uint)];
var d1 : seq<Uint8_64.Uint64Seq.uint> := [(281 as Uint8_64.Uint64Seq.uint), (2283 as Uint8_64.Uint64Seq.uint)];
expect |d0| == |d1|, "Test does not meet preconditions and should be removed";
var r0 := Uint8_64.Uint64Seq.SeqAdd(d0, d1);
}
// Test Uint8_64.Uint64Seq.SeqAdd(block#1252847) covers block 1252846
// Test Uint8_64.Uint64Seq.SeqAdd(block#1252847) covers block 1252847
// Extracting the test for Uint8_64.Uint64Seq.SeqAdd(block#1252847) from the counterexample...
method {:test} test18() {
var d0 : seq<Uint8_64.Uint64Seq.uint> := [];
var d1 : seq<Uint8_64.Uint64Seq.uint> := [];
expect |d0| == |d1|, "Test does not meet preconditions and should be removed";
var r0 := Uint8_64.Uint64Seq.SeqAdd(d0, d1);
}
// Test Uint8_64.Uint64Seq.SeqSub(block#1260114) covers block 1260108
// Test Uint8_64.Uint64Seq.SeqSub(block#1260114) covers block 1260110
// Test Uint8_64.Uint64Seq.SeqSub(block#1260114) covers block 1260111
// Test Uint8_64.Uint64Seq.SeqSub(block#1260114) covers block 1260113
// Test Uint8_64.Uint64Seq.SeqSub(block#1260114) covers block 1260114
// Extracting the test for Uint8_64.Uint64Seq.SeqSub(block#1260114) from the counterexample...
method {:test} test19() {
var d0 : seq<Uint8_64.Uint64Seq.uint> := [(1325 as Uint8_64.Uint64Seq.uint), (2331 as Uint8_64.Uint64Seq.uint)];
var d1 : seq<Uint8_64.Uint64Seq.uint> := [(234 as Uint8_64.Uint64Seq.uint), (1796 as Uint8_64.Uint64Seq.uint)];
expect |d0| == |d1|, "Test does not meet preconditions and should be removed";
var r0 := Uint8_64.Uint64Seq.SeqSub(d0, d1);
}
// Test Uint8_64.Uint64Seq.SeqSub(block#1260112) covers block 1260108
// Test Uint8_64.Uint64Seq.SeqSub(block#1260112) covers block 1260110
// Test Uint8_64.Uint64Seq.SeqSub(block#1260112) covers block 1260112
// Extracting the test for Uint8_64.Uint64Seq.SeqSub(block#1260112) from the counterexample...
method {:test} test20() {
var d0 : seq<Uint8_64.Uint64Seq.uint> := [(920 as Uint8_64.Uint64Seq.uint), (2061 as Uint8_64.Uint64Seq.uint)];
var d1 : seq<Uint8_64.Uint64Seq.uint> := [(645 as Uint8_64.Uint64Seq.uint), (2062 as Uint8_64.Uint64Seq.uint)];
expect |d0| == |d1|, "Test does not meet preconditions and should be removed";
var r0 := Uint8_64.Uint64Seq.SeqSub(d0, d1);
}
// Test Uint8_64.Uint64Seq.SeqSub(block#1260109) covers block 1260108
// Test Uint8_64.Uint64Seq.SeqSub(block#1260109) covers block 1260109
// Extracting the test for Uint8_64.Uint64Seq.SeqSub(block#1260109) from the counterexample...
method {:test} test21() {
var d0 : seq<Uint8_64.Uint64Seq.uint> := [];
var d1 : seq<Uint8_64.Uint64Seq.uint> := [];
expect |d0| == |d1|, "Test does not meet preconditions and should be removed";
var r0 := Uint8_64.Uint64Seq.SeqSub(d0, d1);
}
// No test can be generated for Uint8_64.E(block#1277186) because the verifier timed out.
// No test can be generated for Uint8_64.ToSmall(block#1278787) because the verifier timed out.
// No test can be generated for Uint8_64.ToSmall(block#1278786) because the verifier timed out.
// No test can be generated for Uint8_64.ToSmall(block#1278785) because the verifier timed out.
// Test Uint8_64.ToSmall(block#1278784) covers block 1278784
// Extracting the test for Uint8_64.ToSmall(block#1278784) from the counterexample...
method {:test} test22() {
var d0 : seq<Uint8_64.Uint64Seq.uint> := [];
var r0 := Uint8_64.ToSmall(d0);
expect |r0| == |d0| * Uint8_64.E();
}
// No test can be generated for Uint8_64.ToLarge(block#1280527) because the verifier timed out.
// No test can be generated for Uint8_64.ToLarge(block#1280526) because the verifier timed out.
// No test can be generated for Uint8_64.ToLarge(block#1280525) because the verifier timed out.
// Test Uint8_64.ToLarge(block#1280524) covers block 1280524
// Extracting the test for Uint8_64.ToLarge(block#1280524) from the counterexample...
/*method {:test} test23() {
var d0 : seq<Uint8_64.Uint8Seq.uint> := [(0 as Uint8_64.Uint8Seq.uint), (0 as Uint8_64.Uint8Seq.uint), (0 as Uint8_64.Uint8Seq.uint), (0 as Uint8_64.Uint8Seq.uint), (0 as Uint8_64.Uint8Seq.uint), (0 as Uint8_64.Uint8Seq.uint), (0 as Uint8_64.Uint8Seq.uint), (0 as Uint8_64.Uint8Seq.uint), (0 as Uint8_64.Uint8Seq.uint), (0 as Uint8_64.Uint8Seq.uint), (0 as Uint8_64.Uint8Seq.uint), (0 as Uint8_64.Uint8Seq.uint), (0 as Uint8_64.Uint8Seq.uint), (0 as Uint8_64.Uint8Seq.uint), (0 as Uint8_64.Uint8Seq.uint), (0 as Uint8_64.Uint8Seq.uint), (0 as Uint8_64.Uint8Seq.uint), (0 as Uint8_64.Uint8Seq.uint), (0 as Uint8_64.Uint8Seq.uint), (0 as Uint8_64.Uint8Seq.uint), (0 as Uint8_64.Uint8Seq.uint), (0 as Uint8_64.Uint8Seq.uint), (0 as Uint8_64.Uint8Seq.uint), (0 as Uint8_64.Uint8Seq.uint), (0 as Uint8_64.Uint8Seq.uint), (0 as Uint8_64.Uint8Seq.uint), (0 as Uint8_64.Uint8Seq.uint), (0 as Uint8_64.Uint8Seq.uint), (0 as Uint8_64.Uint8Seq.uint), (0 as Uint8_64.Uint8Seq.uint), (0 as Uint8_64.Uint8Seq.uint), (0 as Uint8_64.Uint8Seq.uint), (0 as Uint8_64.Uint8Seq.uint), (0 as Uint8_64.Uint8Seq.uint), (0 as Uint8_64.Uint8Seq.uint), (0 as Uint8_64.Uint8Seq.uint), (0 as Uint8_64.Uint8Seq.uint), (0 as Uint8_64.Uint8Seq.uint), (0 as Uint8_64.Uint8Seq.uint), (0 as Uint8_64.Uint8Seq.uint), (0 as Uint8_64.Uint8Seq.uint), (0 as Uint8_64.Uint8Seq.uint), (0 as Uint8_64.Uint8Seq.uint), (0 as Uint8_64.Uint8Seq.uint), (0 as Uint8_64.Uint8Seq.uint), (0 as Uint8_64.Uint8Seq.uint), (0 as Uint8_64.Uint8Seq.uint), (0 as Uint8_64.Uint8Seq.uint), (0 as Uint8_64.Uint8Seq.uint), (0 as Uint8_64.Uint8Seq.uint), (0 as Uint8_64.Uint8Seq.uint), (0 as Uint8_64.Uint8Seq.uint), (0 as Uint8_64.Uint8Seq.uint), (0 as Uint8_64.Uint8Seq.uint), (0 as Uint8_64.Uint8Seq.uint), (0 as Uint8_64.Uint8Seq.uint), (0 as Uint8_64.Uint8Seq.uint), (0 as Uint8_64.Uint8Seq.uint), (0 as Uint8_64.Uint8Seq.uint), (0 as Uint8_64.Uint8Seq.uint), (0 as Uint8_64.Uint8Seq.uint), (0 as Uint8_64.Uint8Seq.uint), (0 as Uint8_64.Uint8Seq.uint), (0 as Uint8_64.Uint8Seq.uint), (0 as Uint8_64.Uint8Seq.uint), (0 as Uint8_64.Uint8Seq.uint), (0 as Uint8_64.Uint8Seq.uint), (0 as Uint8_64.Uint8Seq.uint), (0 as Uint8_64.Uint8Seq.uint), (0 as Uint8_64.Uint8Seq.uint), (0 as Uint8_64.Uint8Seq.uint), (0 as Uint8_64.Uint8Seq.uint), (0 as Uint8_64.Uint8Seq.uint), (0 as Uint8_64.Uint8Seq.uint), (0 as Uint8_64.Uint8Seq.uint), (0 as Uint8_64.Uint8Seq.uint), (0 as Uint8_64.Uint8Seq.uint), (0 as Uint8_64.Uint8Seq.uint), (0 as Uint8_64.Uint8Seq.uint), (0 as Uint8_64.Uint8Seq.uint), (0 as Uint8_64.Uint8Seq.uint), (0 as Uint8_64.Uint8Seq.uint), (0 as Uint8_64.Uint8Seq.uint), (0 as Uint8_64.Uint8Seq.uint), (0 as Uint8_64.Uint8Seq.uint), (0 as Uint8_64.Uint8Seq.uint)];
expect |d0| % Uint8_64.E() == 0, "Test does not meet preconditions and should be removed";
var r0 := Uint8_64.ToLarge(d0);
expect |r0| == |d0| / Uint8_64.E();
}*/

}
