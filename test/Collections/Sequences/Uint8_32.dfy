// Warning: Values of type Uint8_32.Uint8Seq.uint will be assigned a default value of type int, which may or may not match the associated condition
// Warning: Values of type Uint8_32.Uint32Seq.uint will be assigned a default value of type int, which may or may not match the associated condition
include "../../..//src/Collections/Sequences/Uint8_32.dfy"
module srcCollectionsSequencesUint8_32dfyUnitTests {
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
// Warning: Values of type Uint8_32.Uint8Seq.uint will be assigned a default value of type int, which may or may not match the associated condition
// Warning: Values of type Uint8_32.Uint32Seq.uint will be assigned a default value of type int, which may or may not match the associated condition
// Warning: Values of type Uint8_32.Uint8Seq.uint will be assigned a default value of type int, which may or may not match the associated condition
// Warning: Values of type Uint8_32.Uint32Seq.uint will be assigned a default value of type int, which may or may not match the associated condition
// Merging boogie files...
// Converting function calls to method calls...
// Adding Impl$$ methods to support inlining...
// Removing assertions...
// Annotating blocks...
// Generating modifications...
// No test can be generated for Uint8_32.Uint8Seq.ToNatRight(block#1813605) because the verifier suceeded.
// No test can be generated for Uint8_32.Uint8Seq.ToNatRight(block#1813604) because the verifier suceeded.
// No test can be generated for Uint8_32.Uint8Seq.ToNatRight(block#1813603) because the verifier suceeded.
// Test Uint8_32.Uint8Seq.ToNatRight(block#1813602) covers block 1813602
// Extracting the test for Uint8_32.Uint8Seq.ToNatRight(block#1813602) from the counterexample...
method {:test} test0() {
var d0 : seq<Uint8_32.Uint8Seq.uint> := [];
var r0 := Uint8_32.Uint8Seq.ToNatRight(d0);
}
// No test can be generated for Uint8_32.Uint8Seq.ToNatLeft(block#1815793) because the verifier suceeded.
// No test can be generated for Uint8_32.Uint8Seq.ToNatLeft(block#1815792) because the verifier suceeded.
// No test can be generated for Uint8_32.Uint8Seq.ToNatLeft(block#1815791) because the verifier suceeded.
// Test Uint8_32.Uint8Seq.ToNatLeft(block#1815790) covers block 1815790
// Extracting the test for Uint8_32.Uint8Seq.ToNatLeft(block#1815790) from the counterexample...
method {:test} test1() {
var d0 : seq<Uint8_32.Uint8Seq.uint> := [];
var r0 := Uint8_32.Uint8Seq.ToNatLeft(d0);
}
// Test Uint8_32.Uint8Seq.FromNat(block#1840656) covers block 1840653
// Test Uint8_32.Uint8Seq.FromNat(block#1840656) covers block 1840655
// Test Uint8_32.Uint8Seq.FromNat(block#1840656) covers block 1840656
// Extracting the test for Uint8_32.Uint8Seq.FromNat(block#1840656) from the counterexample...
method {:test} test2() {
var r0 := Uint8_32.Uint8Seq.FromNat((2279 as nat));
}
// Test Uint8_32.Uint8Seq.FromNat(block#1840654) covers block 1840653
// Test Uint8_32.Uint8Seq.FromNat(block#1840654) covers block 1840654
// Extracting the test for Uint8_32.Uint8Seq.FromNat(block#1840654) from the counterexample...
method {:test} test3() {
var r0 := Uint8_32.Uint8Seq.FromNat((0 as nat));
}
// Test Uint8_32.Uint8Seq.SeqExtend(block#1845472) covers block 1845469
// Test Uint8_32.Uint8Seq.SeqExtend(block#1845472) covers block 1845470
// Test Uint8_32.Uint8Seq.SeqExtend(block#1845472) covers block 1845472
// Extracting the test for Uint8_32.Uint8Seq.SeqExtend(block#1845472) from the counterexample...
method {:test} test4() {
var d0 : seq<Uint8_32.Uint8Seq.uint> := [(0 as Uint8_32.Uint8Seq.uint)];
var r0 := Uint8_32.Uint8Seq.SeqExtend(d0, (1 as nat));
expect |r0| == (1 as nat);
expect Uint8_32.Uint8Seq.ToNatRight(r0) == Uint8_32.Uint8Seq.ToNatRight(d0);
}
// Test Uint8_32.Uint8Seq.SeqExtend(block#1845471) covers block 1845469
// Test Uint8_32.Uint8Seq.SeqExtend(block#1845471) covers block 1845471
// Extracting the test for Uint8_32.Uint8Seq.SeqExtend(block#1845471) from the counterexample...
method {:test} test5() {
var d0 : seq<Uint8_32.Uint8Seq.uint> := [(0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint)];
var r0 := Uint8_32.Uint8Seq.SeqExtend(d0, (98 as nat));
expect |r0| == (98 as nat);
expect Uint8_32.Uint8Seq.ToNatRight(r0) == Uint8_32.Uint8Seq.ToNatRight(d0);
}
// Test Uint8_32.Uint8Seq.SeqExtendMultiple(block#1847563) covers block 1847563
// Extracting the test for Uint8_32.Uint8Seq.SeqExtendMultiple(block#1847563) from the counterexample...
method {:test} test6() {
var d0 : seq<Uint8_32.Uint8Seq.uint> := [(0 as Uint8_32.Uint8Seq.uint)];
var r0 := Uint8_32.Uint8Seq.SeqExtendMultiple(d0, (66 as nat));
expect |r0| % (66 as nat) == 0;
expect Uint8_32.Uint8Seq.ToNatRight(r0) == Uint8_32.Uint8Seq.ToNatRight(d0);
}
// Test Uint8_32.Uint8Seq.FromNatWithLen(block#1849515) covers block 1849515
// Extracting the test for Uint8_32.Uint8Seq.FromNatWithLen(block#1849515) from the counterexample...
/*method {:test} test7() {
var r0 := Uint8_32.Uint8Seq.FromNatWithLen((1236 as nat), (1 as nat));
expect |r0| == (1 as nat);
expect Uint8_32.Uint8Seq.ToNatRight(r0) == (1236 as nat);
}*/
// Test Uint8_32.Uint8Seq.SeqZero(block#1852400) covers block 1852400
// Extracting the test for Uint8_32.Uint8Seq.SeqZero(block#1852400) from the counterexample...
method {:test} test8() {
var r0 := Uint8_32.Uint8Seq.SeqZero((1 as nat));
expect |r0| == (1 as nat);
expect Uint8_32.Uint8Seq.ToNatRight(r0) == 0;
}
// Test Uint8_32.Uint8Seq.SeqAdd(block#1858606) covers block 1858600
// Test Uint8_32.Uint8Seq.SeqAdd(block#1858606) covers block 1858602
// Test Uint8_32.Uint8Seq.SeqAdd(block#1858606) covers block 1858603
// Test Uint8_32.Uint8Seq.SeqAdd(block#1858606) covers block 1858605
// Test Uint8_32.Uint8Seq.SeqAdd(block#1858606) covers block 1858606
// Extracting the test for Uint8_32.Uint8Seq.SeqAdd(block#1858606) from the counterexample...
method {:test} test9() {
var d0 : seq<Uint8_32.Uint8Seq.uint> := [(0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint)];
var d1 : seq<Uint8_32.Uint8Seq.uint> := [(0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint)];
var r0 := Uint8_32.Uint8Seq.SeqAdd(d0, d1);
}
// Test Uint8_32.Uint8Seq.SeqAdd(block#1858604) covers block 1858600
// Test Uint8_32.Uint8Seq.SeqAdd(block#1858604) covers block 1858602
// Test Uint8_32.Uint8Seq.SeqAdd(block#1858604) covers block 1858604
// Extracting the test for Uint8_32.Uint8Seq.SeqAdd(block#1858604) from the counterexample...
method {:test} test10() {
var d0 : seq<Uint8_32.Uint8Seq.uint> := [(0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (8098 as Uint8_32.Uint8Seq.uint)];
var d1 : seq<Uint8_32.Uint8Seq.uint> := [(0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (16953 as Uint8_32.Uint8Seq.uint)];
var r0 := Uint8_32.Uint8Seq.SeqAdd(d0, d1);
}
// Test Uint8_32.Uint8Seq.SeqAdd(block#1858601) covers block 1858600
// Test Uint8_32.Uint8Seq.SeqAdd(block#1858601) covers block 1858601
// Extracting the test for Uint8_32.Uint8Seq.SeqAdd(block#1858601) from the counterexample...
method {:test} test11() {
var d0 : seq<Uint8_32.Uint8Seq.uint> := [];
var d1 : seq<Uint8_32.Uint8Seq.uint> := [];
var r0 := Uint8_32.Uint8Seq.SeqAdd(d0, d1);
}
// Test Uint8_32.Uint8Seq.SeqSub(block#1866992) covers block 1866986
// Test Uint8_32.Uint8Seq.SeqSub(block#1866992) covers block 1866988
// Test Uint8_32.Uint8Seq.SeqSub(block#1866992) covers block 1866989
// Test Uint8_32.Uint8Seq.SeqSub(block#1866992) covers block 1866991
// Test Uint8_32.Uint8Seq.SeqSub(block#1866992) covers block 1866992
// Extracting the test for Uint8_32.Uint8Seq.SeqSub(block#1866992) from the counterexample...
method {:test} test12() {
var d0 : seq<Uint8_32.Uint8Seq.uint> := [(0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (4044 as Uint8_32.Uint8Seq.uint)];
var d1 : seq<Uint8_32.Uint8Seq.uint> := [(0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (1653 as Uint8_32.Uint8Seq.uint)];
var r0 := Uint8_32.Uint8Seq.SeqSub(d0, d1);
}
// Test Uint8_32.Uint8Seq.SeqSub(block#1866990) covers block 1866986
// Test Uint8_32.Uint8Seq.SeqSub(block#1866990) covers block 1866988
// Test Uint8_32.Uint8Seq.SeqSub(block#1866990) covers block 1866990
// Extracting the test for Uint8_32.Uint8Seq.SeqSub(block#1866990) from the counterexample...
method {:test} test13() {
var d0 : seq<Uint8_32.Uint8Seq.uint> := [(0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (535 as Uint8_32.Uint8Seq.uint)];
var d1 : seq<Uint8_32.Uint8Seq.uint> := [(0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (536 as Uint8_32.Uint8Seq.uint)];
var r0 := Uint8_32.Uint8Seq.SeqSub(d0, d1);
}
// Test Uint8_32.Uint8Seq.SeqSub(block#1866987) covers block 1866986
// Test Uint8_32.Uint8Seq.SeqSub(block#1866987) covers block 1866987
// Extracting the test for Uint8_32.Uint8Seq.SeqSub(block#1866987) from the counterexample...
method {:test} test14() {
var d0 : seq<Uint8_32.Uint8Seq.uint> := [];
var d1 : seq<Uint8_32.Uint8Seq.uint> := [];
var r0 := Uint8_32.Uint8Seq.SeqSub(d0, d1);
}
// No test can be generated for Uint8_32.Uint32Seq.ToNatRight(block#1928089) because the verifier suceeded.
// No test can be generated for Uint8_32.Uint32Seq.ToNatRight(block#1928088) because the verifier suceeded.
// No test can be generated for Uint8_32.Uint32Seq.ToNatRight(block#1928087) because the verifier suceeded.
// Test Uint8_32.Uint32Seq.ToNatRight(block#1928086) covers block 1928086
// Extracting the test for Uint8_32.Uint32Seq.ToNatRight(block#1928086) from the counterexample...
method {:test} test15() {
var d0 : seq<Uint8_32.Uint32Seq.uint> := [];
var r0 := Uint8_32.Uint32Seq.ToNatRight(d0);
}
// No test can be generated for Uint8_32.Uint32Seq.ToNatLeft(block#1930493) because the verifier suceeded.
// No test can be generated for Uint8_32.Uint32Seq.ToNatLeft(block#1930492) because the verifier suceeded.
// No test can be generated for Uint8_32.Uint32Seq.ToNatLeft(block#1930491) because the verifier suceeded.
// Test Uint8_32.Uint32Seq.ToNatLeft(block#1930490) covers block 1930490
// Extracting the test for Uint8_32.Uint32Seq.ToNatLeft(block#1930490) from the counterexample...
method {:test} test16() {
var d0 : seq<Uint8_32.Uint32Seq.uint> := [];
var r0 := Uint8_32.Uint32Seq.ToNatLeft(d0);
}
// Test Uint8_32.Uint32Seq.FromNat(block#1957300) covers block 1957297
// Test Uint8_32.Uint32Seq.FromNat(block#1957300) covers block 1957299
// Test Uint8_32.Uint32Seq.FromNat(block#1957300) covers block 1957300
// Extracting the test for Uint8_32.Uint32Seq.FromNat(block#1957300) from the counterexample...
method {:test} test17() {
var r0 := Uint8_32.Uint32Seq.FromNat((2279 as nat));
}
// Test Uint8_32.Uint32Seq.FromNat(block#1957298) covers block 1957297
// Test Uint8_32.Uint32Seq.FromNat(block#1957298) covers block 1957298
// Extracting the test for Uint8_32.Uint32Seq.FromNat(block#1957298) from the counterexample...
method {:test} test18() {
var r0 := Uint8_32.Uint32Seq.FromNat((0 as nat));
}
// Test Uint8_32.Uint32Seq.SeqExtend(block#1962548) covers block 1962545
// Test Uint8_32.Uint32Seq.SeqExtend(block#1962548) covers block 1962546
// Test Uint8_32.Uint32Seq.SeqExtend(block#1962548) covers block 1962548
// Extracting the test for Uint8_32.Uint32Seq.SeqExtend(block#1962548) from the counterexample...
method {:test} test19() {
var d0 : seq<Uint8_32.Uint32Seq.uint> := [(0 as Uint8_32.Uint32Seq.uint)];
var r0 := Uint8_32.Uint32Seq.SeqExtend(d0, (1 as nat));
expect |r0| == (1 as nat);
expect Uint8_32.Uint32Seq.ToNatRight(r0) == Uint8_32.Uint32Seq.ToNatRight(d0);
}
// Test Uint8_32.Uint32Seq.SeqExtend(block#1962547) covers block 1962545
// Test Uint8_32.Uint32Seq.SeqExtend(block#1962547) covers block 1962547
// Extracting the test for Uint8_32.Uint32Seq.SeqExtend(block#1962547) from the counterexample...
method {:test} test20() {
var d0 : seq<Uint8_32.Uint32Seq.uint> := [(0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint)];
var r0 := Uint8_32.Uint32Seq.SeqExtend(d0, (98 as nat));
expect |r0| == (98 as nat);
expect Uint8_32.Uint32Seq.ToNatRight(r0) == Uint8_32.Uint32Seq.ToNatRight(d0);
}
// Test Uint8_32.Uint32Seq.SeqExtendMultiple(block#1964855) covers block 1964855
// Extracting the test for Uint8_32.Uint32Seq.SeqExtendMultiple(block#1964855) from the counterexample...
method {:test} test21() {
var d0 : seq<Uint8_32.Uint32Seq.uint> := [(0 as Uint8_32.Uint32Seq.uint)];
var r0 := Uint8_32.Uint32Seq.SeqExtendMultiple(d0, (66 as nat));
expect |r0| % (66 as nat) == 0;
expect Uint8_32.Uint32Seq.ToNatRight(r0) == Uint8_32.Uint32Seq.ToNatRight(d0);
}
// Test Uint8_32.Uint32Seq.FromNatWithLen(block#1967023) covers block 1967023
// Extracting the test for Uint8_32.Uint32Seq.FromNatWithLen(block#1967023) from the counterexample...
method {:test} test22() {
var r0 := Uint8_32.Uint32Seq.FromNatWithLen((1236 as nat), (1 as nat));
expect |r0| == (1 as nat);
expect Uint8_32.Uint32Seq.ToNatRight(r0) == (1236 as nat);
}
// Test Uint8_32.Uint32Seq.SeqZero(block#1970232) covers block 1970232
// Extracting the test for Uint8_32.Uint32Seq.SeqZero(block#1970232) from the counterexample...
method {:test} test23() {
var r0 := Uint8_32.Uint32Seq.SeqZero((1 as nat));
expect |r0| == (1 as nat);
expect Uint8_32.Uint32Seq.ToNatRight(r0) == 0;
}
// Test Uint8_32.Uint32Seq.SeqAdd(block#1976762) covers block 1976756
// Test Uint8_32.Uint32Seq.SeqAdd(block#1976762) covers block 1976758
// Test Uint8_32.Uint32Seq.SeqAdd(block#1976762) covers block 1976759
// Test Uint8_32.Uint32Seq.SeqAdd(block#1976762) covers block 1976761
// Test Uint8_32.Uint32Seq.SeqAdd(block#1976762) covers block 1976762
// Extracting the test for Uint8_32.Uint32Seq.SeqAdd(block#1976762) from the counterexample...
method {:test} test24() {
var d0 : seq<Uint8_32.Uint32Seq.uint> := [(0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint)];
var d1 : seq<Uint8_32.Uint32Seq.uint> := [(0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint)];
var r0 := Uint8_32.Uint32Seq.SeqAdd(d0, d1);
}
// Test Uint8_32.Uint32Seq.SeqAdd(block#1976760) covers block 1976756
// Test Uint8_32.Uint32Seq.SeqAdd(block#1976760) covers block 1976758
// Test Uint8_32.Uint32Seq.SeqAdd(block#1976760) covers block 1976760
// Extracting the test for Uint8_32.Uint32Seq.SeqAdd(block#1976760) from the counterexample...
method {:test} test25() {
var d0 : seq<Uint8_32.Uint32Seq.uint> := [(0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (8098 as Uint8_32.Uint32Seq.uint)];
var d1 : seq<Uint8_32.Uint32Seq.uint> := [(0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (16953 as Uint8_32.Uint32Seq.uint)];
var r0 := Uint8_32.Uint32Seq.SeqAdd(d0, d1);
}
// Test Uint8_32.Uint32Seq.SeqAdd(block#1976757) covers block 1976756
// Test Uint8_32.Uint32Seq.SeqAdd(block#1976757) covers block 1976757
// Extracting the test for Uint8_32.Uint32Seq.SeqAdd(block#1976757) from the counterexample...
method {:test} test26() {
var d0 : seq<Uint8_32.Uint32Seq.uint> := [];
var d1 : seq<Uint8_32.Uint32Seq.uint> := [];
var r0 := Uint8_32.Uint32Seq.SeqAdd(d0, d1);
}
// Test Uint8_32.Uint32Seq.SeqSub(block#1985472) covers block 1985466
// Test Uint8_32.Uint32Seq.SeqSub(block#1985472) covers block 1985468
// Test Uint8_32.Uint32Seq.SeqSub(block#1985472) covers block 1985469
// Test Uint8_32.Uint32Seq.SeqSub(block#1985472) covers block 1985471
// Test Uint8_32.Uint32Seq.SeqSub(block#1985472) covers block 1985472
// Extracting the test for Uint8_32.Uint32Seq.SeqSub(block#1985472) from the counterexample...
method {:test} test27() {
var d0 : seq<Uint8_32.Uint32Seq.uint> := [(0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (2475 as Uint8_32.Uint32Seq.uint)];
var d1 : seq<Uint8_32.Uint32Seq.uint> := [(0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (1888 as Uint8_32.Uint32Seq.uint)];
var r0 := Uint8_32.Uint32Seq.SeqSub(d0, d1);
}
// Test Uint8_32.Uint32Seq.SeqSub(block#1985470) covers block 1985466
// Test Uint8_32.Uint32Seq.SeqSub(block#1985470) covers block 1985468
// Test Uint8_32.Uint32Seq.SeqSub(block#1985470) covers block 1985470
// Extracting the test for Uint8_32.Uint32Seq.SeqSub(block#1985470) from the counterexample...
method {:test} test28() {
var d0 : seq<Uint8_32.Uint32Seq.uint> := [(0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (535 as Uint8_32.Uint32Seq.uint)];
var d1 : seq<Uint8_32.Uint32Seq.uint> := [(0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (0 as Uint8_32.Uint32Seq.uint), (536 as Uint8_32.Uint32Seq.uint)];
var r0 := Uint8_32.Uint32Seq.SeqSub(d0, d1);
}
// Test Uint8_32.Uint32Seq.SeqSub(block#1985467) covers block 1985466
// Test Uint8_32.Uint32Seq.SeqSub(block#1985467) covers block 1985467
// Extracting the test for Uint8_32.Uint32Seq.SeqSub(block#1985467) from the counterexample...
method {:test} test29() {
var d0 : seq<Uint8_32.Uint32Seq.uint> := [];
var d1 : seq<Uint8_32.Uint32Seq.uint> := [];
var r0 := Uint8_32.Uint32Seq.SeqSub(d0, d1);
}
// No test can be generated for Uint8_32.E(block#2044992) because the verifier suceeded.
// No test can be generated for Uint8_32.ToSmall(block#2047750) because the verifier suceeded.
// No test can be generated for Uint8_32.ToSmall(block#2047749) because the verifier suceeded.
// No test can be generated for Uint8_32.ToSmall(block#2047748) because the verifier suceeded.
// Test Uint8_32.ToSmall(block#2047747) covers block 2047747
// Extracting the test for Uint8_32.ToSmall(block#2047747) from the counterexample...
method {:test} test30() {
var d0 : seq<Uint8_32.Uint32Seq.uint> := [];
var r0 := Uint8_32.ToSmall(d0);
expect |r0| == |d0| * Uint8_32.E();
}
// Test Uint8_32.ToLarge(block#2050546) covers block 2050543
// Test Uint8_32.ToLarge(block#2050546) covers block 2050544
// Test Uint8_32.ToLarge(block#2050546) covers block 2050546
// Extracting the test for Uint8_32.ToLarge(block#2050546) from the counterexample...
method {:test} test31() {
var d0 : seq<Uint8_32.Uint8Seq.uint> := [];
var r0 := Uint8_32.ToLarge(d0);
expect |r0| == |d0| / Uint8_32.E();
}
// Test Uint8_32.ToLarge(block#2050545) covers block 2050543
// Test Uint8_32.ToLarge(block#2050545) covers block 2050545
// Extracting the test for Uint8_32.ToLarge(block#2050545) from the counterexample...
/*method {:test} test32() {
var d0 : seq<Uint8_32.Uint8Seq.uint> := [(0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint), (0 as Uint8_32.Uint8Seq.uint)];
var r0 := Uint8_32.ToLarge(d0);
expect |r0| == |d0| / Uint8_32.E();
}*/

}
