include "../../..//src/Collections/Sequences/Seq.dfy"
module srcCollectionsSequencesSeqdfyUnitTests {
import Seq
import Wrappers
import Math
// Merging boogie files...
// Converting function calls to method calls...
// Adding Impl$$ methods to support inlining...
// Removing assertions...
// Annotating blocks...
// Generating modifications...
// Test Seq.First(block#690809) covers block 690809
// Extracting the test for Seq.First(block#690809) from the counterexample...
method {:test} test0() {
var d0 : seq<int> := [0];
expect |d0| > 0, "Test does not meet preconditions and should be removed";
var r0 := Seq.First<int>(d0);
}
// Test Seq.DropFirst(block#691392) covers block 691392
// Extracting the test for Seq.DropFirst(block#691392) from the counterexample...
method {:test} test1() {
var d0 : seq<int> := [0];
expect |d0| > 0, "Test does not meet preconditions and should be removed";
var r0 := Seq.DropFirst<int>(d0);
}
// Test Seq.Last(block#691977) covers block 691977
// Extracting the test for Seq.Last(block#691977) from the counterexample...
method {:test} test2() {
var d0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect |d0| > 0, "Test does not meet preconditions and should be removed";
var r0 := Seq.Last<int>(d0);
}
// Test Seq.DropLast(block#692576) covers block 692576
// Extracting the test for Seq.DropLast(block#692576) from the counterexample...
method {:test} test3() {
var d0 : seq<int> := [0, 0];
expect |d0| > 0, "Test does not meet preconditions and should be removed";
var r0 := Seq.DropLast<int>(d0);
}
// Test Seq.ToArray(block#697704) covers block 697693
// Test Seq.ToArray(block#697704) covers block 697704
// Extracting the test for Seq.ToArray(block#697704) from the counterexample...
method {:test} test4() {
var d0 : seq<int> := [0];
var r0 := Seq.ToArray<int>(d0);
expect r0.Length == |d0|;
}
// No test can be generated for Seq.ToArray(block#697702) because the verifier suceeded.
// No test can be generated for Seq.ToArray(block#697701) because the verifier suceeded.
// Test Seq.ToArray(block#697700) covers block 697693
// Test Seq.ToArray(block#697700) covers block 697694
// Test Seq.ToArray(block#697700) covers block 697695
// Test Seq.ToArray(block#697700) covers block 697696
// Test Seq.ToArray(block#697700) covers block 697700
// Extracting the test for Seq.ToArray(block#697700) from the counterexample...
// Test for Seq.ToArray(block#697700) matches a test previously generated for Seq.ToArray(block#697704).
// Test Seq.ToArray(block#697699) covers block 697693
// Test Seq.ToArray(block#697699) covers block 697694
// Test Seq.ToArray(block#697699) covers block 697695
// Test Seq.ToArray(block#697699) covers block 697696
// Test Seq.ToArray(block#697699) covers block 697699
// Extracting the test for Seq.ToArray(block#697699) from the counterexample...
method {:test} test6() {
var d0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var r0 := Seq.ToArray<int>(d0);
expect r0.Length == |d0|;
}
// Test Seq.ToArray(block#697697) covers block 697693
// Test Seq.ToArray(block#697697) covers block 697694
// Test Seq.ToArray(block#697697) covers block 697695
// Test Seq.ToArray(block#697697) covers block 697697
// Extracting the test for Seq.ToArray(block#697697) from the counterexample...
// Test for Seq.ToArray(block#697697) matches a test previously generated for Seq.ToArray(block#697704).
// Test Seq.ToSet(block#698185) covers block 698180
// Test Seq.ToSet(block#698185) covers block 698181
// Test Seq.ToSet(block#698185) covers block 698182
// Test Seq.ToSet(block#698185) covers block 698185
// Extracting the test for Seq.ToSet(block#698185) from the counterexample...
method {:test} test8() {
var d0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var r0 := Seq.ToSet<int>(d0);
}
// Test Seq.ToSet(block#698184) covers block 698180
// Test Seq.ToSet(block#698184) covers block 698184
// Extracting the test for Seq.ToSet(block#698184) from the counterexample...
method {:test} test9() {
var d0 : seq<int> := [];
var r0 := Seq.ToSet<int>(d0);
}
// Test Seq.ToSet(block#698183) covers block 698180
// Test Seq.ToSet(block#698183) covers block 698181
// Test Seq.ToSet(block#698183) covers block 698183
// Extracting the test for Seq.ToSet(block#698183) from the counterexample...
// Test for Seq.ToSet(block#698183) matches a test previously generated for Seq.ToSet(block#698184).
// Test Seq.IndexOf(block#704785) covers block 704782
// Test Seq.IndexOf(block#704785) covers block 704783
// Test Seq.IndexOf(block#704785) covers block 704785
// Extracting the test for Seq.IndexOf(block#704785) from the counterexample...
method {:test} test11() {
var d0 : seq<int> := [1];
expect 1 in d0, "Test does not meet preconditions and should be removed";
var r0 := Seq.IndexOf<int>(d0, 1);
expect r0 < |d0| && d0[r0] == 1;
}
// Test Seq.IndexOf(block#704784) covers block 704782
// Test Seq.IndexOf(block#704784) covers block 704784
// Extracting the test for Seq.IndexOf(block#704784) from the counterexample...
method {:test} test12() {
var d0 : seq<int> := [0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1];
expect 1 in d0, "Test does not meet preconditions and should be removed";
var r0 := Seq.IndexOf<int>(d0, 1);
expect r0 < |d0| && d0[r0] == 1;
}
// Test Seq.IndexOfOption(block#707142) covers block 707135
// Test Seq.IndexOfOption(block#707142) covers block 707136
// Test Seq.IndexOfOption(block#707142) covers block 707142
// Extracting the test for Seq.IndexOfOption(block#707142) from the counterexample...
method {:test} test13() {
var d0 : seq<int> := [];
var r0 := Seq.IndexOfOption<int>(d0, 0);
}
// Test Seq.IndexOfOption(block#707141) covers block 707135
// Test Seq.IndexOfOption(block#707141) covers block 707137
// Test Seq.IndexOfOption(block#707141) covers block 707139
// Test Seq.IndexOfOption(block#707141) covers block 707141
// Extracting the test for Seq.IndexOfOption(block#707141) from the counterexample...
method {:test} test14() {
var d0 : seq<int> := [0];
var r0 := Seq.IndexOfOption<int>(d0, 1);
}
// Test Seq.IndexOfOption(block#707140) covers block 707135
// Test Seq.IndexOfOption(block#707140) covers block 707137
// Test Seq.IndexOfOption(block#707140) covers block 707139
// Test Seq.IndexOfOption(block#707140) covers block 707140
// Extracting the test for Seq.IndexOfOption(block#707140) from the counterexample...
method {:test} test15() {
var d0 : seq<int> := [1, 2];
var r0 := Seq.IndexOfOption<int>(d0, 2);
}
// Test Seq.IndexOfOption(block#707138) covers block 707135
// Test Seq.IndexOfOption(block#707138) covers block 707137
// Test Seq.IndexOfOption(block#707138) covers block 707138
// Extracting the test for Seq.IndexOfOption(block#707138) from the counterexample...
method {:test} test16() {
var d0 : seq<int> := [0];
var r0 := Seq.IndexOfOption<int>(d0, 0);
}
// Test Seq.LastIndexOf(block#708800) covers block 708797
// Test Seq.LastIndexOf(block#708800) covers block 708798
// Test Seq.LastIndexOf(block#708800) covers block 708800
// Extracting the test for Seq.LastIndexOf(block#708800) from the counterexample...
method {:test} test17() {
var d0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect 0 in d0, "Test does not meet preconditions and should be removed";
var r0 := Seq.LastIndexOf<int>(d0, 0);
expect r0 < |d0| && d0[r0] == 0;
}
// Test Seq.LastIndexOf(block#708799) covers block 708797
// Test Seq.LastIndexOf(block#708799) covers block 708799
// Extracting the test for Seq.LastIndexOf(block#708799) from the counterexample...
method {:test} test18() {
var d0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1];
expect 0 in d0, "Test does not meet preconditions and should be removed";
var r0 := Seq.LastIndexOf<int>(d0, 0);
expect r0 < |d0| && d0[r0] == 0;
}
// Test Seq.LastIndexOfOption(block#710794) covers block 710789
// Test Seq.LastIndexOfOption(block#710794) covers block 710790
// Test Seq.LastIndexOfOption(block#710794) covers block 710794
// Extracting the test for Seq.LastIndexOfOption(block#710794) from the counterexample...
method {:test} test19() {
var d0 : seq<int> := [];
var r0 := Seq.LastIndexOfOption<int>(d0, 0);
}
// Test Seq.LastIndexOfOption(block#710793) covers block 710789
// Test Seq.LastIndexOfOption(block#710793) covers block 710791
// Test Seq.LastIndexOfOption(block#710793) covers block 710793
// Extracting the test for Seq.LastIndexOfOption(block#710793) from the counterexample...
method {:test} test20() {
var d0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2];
var r0 := Seq.LastIndexOfOption<int>(d0, 3);
}
// Test Seq.LastIndexOfOption(block#710792) covers block 710789
// Test Seq.LastIndexOfOption(block#710792) covers block 710791
// Test Seq.LastIndexOfOption(block#710792) covers block 710792
// Extracting the test for Seq.LastIndexOfOption(block#710792) from the counterexample...
method {:test} test21() {
var d0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var r0 := Seq.LastIndexOfOption<int>(d0, 0);
}
// Test Seq.Remove(block#711944) covers block 711944
// Extracting the test for Seq.Remove(block#711944) from the counterexample...
method {:test} test22() {
var d0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect (39 as nat) < |d0|, "Test does not meet preconditions and should be removed";
var r0 := Seq.Remove<int>(d0, (39 as nat));
expect |r0| == |d0| - 1;
}
// Test Seq.RemoveValue(block#713768) covers block 713765
// Test Seq.RemoveValue(block#713768) covers block 713766
// Test Seq.RemoveValue(block#713768) covers block 713768
// Extracting the test for Seq.RemoveValue(block#713768) from the counterexample...
method {:test} test23() {
var d0 : seq<int> := [];
var r0 := Seq.RemoveValue<int>(d0, 0);
expect 0 !in d0 ==> d0 == r0;
expect 0 in d0 ==> |multiset(r0)| == |multiset(d0)| - 1;
expect 0 in d0 ==> multiset(r0)[0] == multiset(d0)[0] - 1;
}
// Test Seq.RemoveValue(block#713767) covers block 713765
// Test Seq.RemoveValue(block#713767) covers block 713767
// Extracting the test for Seq.RemoveValue(block#713767) from the counterexample...
method {:test} test24() {
var d0 : seq<int> := [0, 2, 0];
var r0 := Seq.RemoveValue<int>(d0, 2);
expect 2 !in d0 ==> d0 == r0;
expect 2 in d0 ==> |multiset(r0)| == |multiset(d0)| - 1;
expect 2 in d0 ==> multiset(r0)[2] == multiset(d0)[2] - 1;
}
// Test Seq.Insert(block#716024) covers block 716024
// Extracting the test for Seq.Insert(block#716024) from the counterexample...
method {:test} test25() {
var d0 : seq<int> := [0, 0];
expect (1 as nat) <= |d0|, "Test does not meet preconditions and should be removed";
var r0 := Seq.Insert<int>(d0, 0, (1 as nat));
expect |Seq.Insert(d0, 0, (1 as nat))| == |d0| + 1;
expect Seq.Insert(d0, 0, (1 as nat))[(1 as nat)] == 0;
expect multiset(Seq.Insert(d0, 0, (1 as nat))) == multiset(d0) + multiset{0};
}
// Test Seq.Reverse(block#717534) covers block 717531
// Test Seq.Reverse(block#717534) covers block 717532
// Test Seq.Reverse(block#717534) covers block 717534
// Extracting the test for Seq.Reverse(block#717534) from the counterexample...
method {:test} test26() {
var d0 : seq<int> := [];
var r0 := Seq.Reverse<int>(d0);
expect |r0| == |d0|;
}
// Test Seq.Reverse(block#717533) covers block 717531
// Test Seq.Reverse(block#717533) covers block 717533
// Extracting the test for Seq.Reverse(block#717533) from the counterexample...
method {:test} test27() {
var d0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0];
var r0 := Seq.Reverse<int>(d0);
expect |r0| == |d0|;
}
// Test Seq.Repeat(block#718896) covers block 718893
// Test Seq.Repeat(block#718896) covers block 718895
// Test Seq.Repeat(block#718896) covers block 718896
// Extracting the test for Seq.Repeat(block#718896) from the counterexample...
method {:test} test28() {
var r0 := Seq.Repeat<int>(0, (76 as nat));
expect |r0| == (76 as nat);
}
// Test Seq.Repeat(block#718894) covers block 718893
// Test Seq.Repeat(block#718894) covers block 718894
// Extracting the test for Seq.Repeat(block#718894) from the counterexample...
method {:test} test29() {
var r0 := Seq.Repeat<int>(0, (0 as nat));
expect |r0| == (0 as nat);
}
// Test Seq.Unzip(block#722286) covers block 722283
// Test Seq.Unzip(block#722286) covers block 722284
// Test Seq.Unzip(block#722286) covers block 722286
// Extracting the test for Seq.Unzip(block#722286) from the counterexample...
// Failed - temporary disable tuple support
// Test Seq.Unzip(block#722285) covers block 722283
// Test Seq.Unzip(block#722285) covers block 722285
// Extracting the test for Seq.Unzip(block#722285) from the counterexample...
// Failed - temporary disable tuple support
// Test Seq.Zip(block#725385) covers block 725382
// Test Seq.Zip(block#725385) covers block 725382
// Test Seq.Zip(block#725385) covers block 725384
// Test Seq.Zip(block#725385) covers block 725385
// Extracting the test for Seq.Zip(block#725385) from the counterexample...
method {:test} test32() {
var d0 : seq<int> := [0, 0];
var d1 : seq<int> := [0, 0];
expect |d0| == |d1|, "Test does not meet preconditions and should be removed";
var r0 := Seq.Zip<int,int>(d0, d1);
expect |Seq.Zip(d0, d1)| == |d0|;
expect Seq.Unzip(Seq.Zip(d0, d1)).0 == d0;
expect Seq.Unzip(Seq.Zip(d0, d1)).1 == d1;
}
// Test Seq.Zip(block#725383) covers block 725382
// Test Seq.Zip(block#725383) covers block 725383
// Test Seq.Zip(block#725383) covers block 725382
// Extracting the test for Seq.Zip(block#725383) from the counterexample...
method {:test} test33() {
var d0 : seq<int> := [];
var d1 : seq<int> := [];
expect |d0| == |d1|, "Test does not meet preconditions and should be removed";
var r0 := Seq.Zip<int,int>(d0, d1);
expect |Seq.Zip(d0, d1)| == |d0|;
expect Seq.Unzip(Seq.Zip(d0, d1)).0 == d0;
expect Seq.Unzip(Seq.Zip(d0, d1)).1 == d1;
}
// Test Seq.Max(block#727823) covers block 727820
// Test Seq.Max(block#727823) covers block 727822
// Test Seq.Max(block#727823) covers block 727823
// Extracting the test for Seq.Max(block#727823) from the counterexample...
method {:test} test34() {
var d0 : seq<int> := [8855, 8878, 8879];
expect 0 < |d0|, "Test does not meet preconditions and should be removed";
var r0 := Seq.Max(d0);
expect Seq.Max(d0) in d0;
}
// Test Seq.Max(block#727821) covers block 727820
// Test Seq.Max(block#727821) covers block 727821
// Extracting the test for Seq.Max(block#727821) from the counterexample...
method {:test} test35() {
var d0 : seq<int> := [0];
expect 0 < |d0|, "Test does not meet preconditions and should be removed";
var r0 := Seq.Max(d0);
expect Seq.Max(d0) in d0;
}
// Test Seq.Min(block#730718) covers block 730715
// Test Seq.Min(block#730718) covers block 730717
// Test Seq.Min(block#730718) covers block 730718
// Extracting the test for Seq.Min(block#730718) from the counterexample...
method {:test} test36() {
var d0 : seq<int> := [8855, 1141, 1142];
expect 0 < |d0|, "Test does not meet preconditions and should be removed";
var r0 := Seq.Min(d0);
expect Seq.Min(d0) in d0;
}
// Test Seq.Min(block#730716) covers block 730715
// Test Seq.Min(block#730716) covers block 730716
// Extracting the test for Seq.Min(block#730716) from the counterexample...
method {:test} test37() {
var d0 : seq<int> := [0];
expect 0 < |d0|, "Test does not meet preconditions and should be removed";
var r0 := Seq.Min(d0);
expect Seq.Min(d0) in d0;
}
// Test Seq.Flatten(block#736348) covers block 736345
// Test Seq.Flatten(block#736348) covers block 736346
// Test Seq.Flatten(block#736348) covers block 736348
// Extracting the test for Seq.Flatten(block#736348) from the counterexample...
method {:test} test38() {
var d0 : seq<seq<int>> := [];
var r0 := Seq.Flatten<int>(d0);
}
// Test Seq.Flatten(block#736347) covers block 736345
// Test Seq.Flatten(block#736347) covers block 736347
// Extracting the test for Seq.Flatten(block#736347) from the counterexample...
method {:test} test39() {
var d0 : seq<int> := [];
var d1 : seq<int> := [0];
var d2 : seq<seq<int>> := [d0, d1];
var r0 := Seq.Flatten<int>(d2);
}
// Test Seq.FlattenReverse(block#738966) covers block 738963
// Test Seq.FlattenReverse(block#738966) covers block 738964
// Test Seq.FlattenReverse(block#738966) covers block 738966
// Extracting the test for Seq.FlattenReverse(block#738966) from the counterexample...
method {:test} test40() {
var d0 : seq<seq<int>> := [];
var r0 := Seq.FlattenReverse<int>(d0);
}
// Test Seq.FlattenReverse(block#738965) covers block 738963
// Test Seq.FlattenReverse(block#738965) covers block 738965
// Extracting the test for Seq.FlattenReverse(block#738965) from the counterexample...
method {:test} test41() {
var d0 : seq<int> := [];
var d1 : seq<int> := [];
var d2 : seq<seq<int>> := [d0, d1];
var r0 := Seq.FlattenReverse<int>(d2);
}
// Test Seq.Map(block#747126) covers block 747123
// Test Seq.Map(block#747126) covers block 747124
// Test Seq.Map(block#747126) covers block 747126
// Extracting the test for Seq.Map(block#747126) from the counterexample...
method {:test} test42() {
var d0 : seq<int> := [];
var r0 := Seq.Map<int,int>((a0:int)=>0, d0);
expect |r0| == |d0|;
}
// Test Seq.Map(block#747125) covers block 747123
// Test Seq.Map(block#747125) covers block 747125
// Extracting the test for Seq.Map(block#747125) from the counterexample...
method {:test} test43() {
var d0 : seq<int> := [0, 1];
var r0 := Seq.Map<int,int>((a0:int)=>0, d0);
expect |r0| == |d0|;
}
// Test Seq.MapWithResult(block#752664) covers block 752657
// Test Seq.MapWithResult(block#752664) covers block 752658
// Test Seq.MapWithResult(block#752664) covers block 752664
// Extracting the test for Seq.MapWithResult(block#752664) from the counterexample...
method {:test} test44() {
var d0 : Wrappers.Result<int, int> := Wrappers.Result<int, int>.Success(value:=0);
var d1 : seq<int> := [];
var r0 := Seq.MapWithResult<int,int,int>((a0:int)=>d0, d1);
}
// Test Seq.MapWithResult(block#752663) covers block 752657
// Test Seq.MapWithResult(block#752663) covers block 752659
// Test Seq.MapWithResult(block#752663) covers block 752661
// Test Seq.MapWithResult(block#752663) covers block 752663
// Extracting the test for Seq.MapWithResult(block#752663) from the counterexample...
method {:test} test45() {
var d0 : Wrappers.Result<int, int> := Wrappers.Result<int, int>.Success(value:=0);
var d1 : seq<int> := [0, 1];
var r0 := Seq.MapWithResult<int,int,int>((a0:int)=>d0, d1);
}
// Test Seq.MapWithResult(block#752662) covers block 752657
// Test Seq.MapWithResult(block#752662) covers block 752659
// Test Seq.MapWithResult(block#752662) covers block 752661
// Test Seq.MapWithResult(block#752662) covers block 752662
// Extracting the test for Seq.MapWithResult(block#752662) from the counterexample...
method {:test} test46() {
var d0 : Wrappers.Result<int, int> := Wrappers.Result<int, int>.Success(value:=0);
var d1 : seq<int> := [0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var r0 := Seq.MapWithResult<int,int,int>((a0:int)=>d0, d1);
}
// Test Seq.MapWithResult(block#752660) covers block 752657
// Test Seq.MapWithResult(block#752660) covers block 752659
// Test Seq.MapWithResult(block#752660) covers block 752660
// Extracting the test for Seq.MapWithResult(block#752660) from the counterexample...
method {:test} test47() {
var d0 : Wrappers.Result<int, int> := Wrappers.Result<int, int>.Success(value:=0);
var d1 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var r0 := Seq.MapWithResult<int,int,int>((a0:int)=>d0, d1);
}
// Test Seq.Filter(block#759332) covers block 759326
// Test Seq.Filter(block#759332) covers block 759327
// Test Seq.Filter(block#759332) covers block 759332
// Extracting the test for Seq.Filter(block#759332) from the counterexample...
method {:test} test48() {
var d0 : seq<int> := [];
var r0 := Seq.Filter<int>((a0:int)=>false, d0);
expect |r0| <= |d0|;
}
// Test Seq.Filter(block#759331) covers block 759326
// Test Seq.Filter(block#759331) covers block 759328
// Test Seq.Filter(block#759331) covers block 759329
// Test Seq.Filter(block#759331) covers block 759331
// Extracting the test for Seq.Filter(block#759331) from the counterexample...
method {:test} test49() {
var d0 : seq<int> := [0];
var r0 := Seq.Filter<int>((a0:int)=>false, d0);
expect |r0| <= |d0|;
}
// Test Seq.Filter(block#759330) covers block 759326
// Test Seq.Filter(block#759330) covers block 759328
// Test Seq.Filter(block#759330) covers block 759330
// Extracting the test for Seq.Filter(block#759330) from the counterexample...
// Test for Seq.Filter(block#759330) matches a test previously generated for Seq.Filter(block#759331).
// Test Seq.FoldLeft(block#764532) covers block 764529
// Test Seq.FoldLeft(block#764532) covers block 764530
// Test Seq.FoldLeft(block#764532) covers block 764532
// Extracting the test for Seq.FoldLeft(block#764532) from the counterexample...
method {:test} test51() {
var d0 : seq<int> := [];
var r0 := Seq.FoldLeft<int,int>((a0:int,a1:int)=>0, 0, d0);
}
// Test Seq.FoldLeft(block#764531) covers block 764529
// Test Seq.FoldLeft(block#764531) covers block 764531
// Extracting the test for Seq.FoldLeft(block#764531) from the counterexample...
method {:test} test52() {
var d0 : seq<int> := [1];
var r0 := Seq.FoldLeft<int,int>((a0:int,a1:int)=>0, 0, d0);
}
// Test Seq.FoldRight(block#770609) covers block 770606
// Test Seq.FoldRight(block#770609) covers block 770607
// Test Seq.FoldRight(block#770609) covers block 770609
// Extracting the test for Seq.FoldRight(block#770609) from the counterexample...
method {:test} test53() {
var d0 : seq<int> := [];
var r0 := Seq.FoldRight<int,int>((a0:int,a1:int)=>0, d0, 0);
}
// Test Seq.FoldRight(block#770608) covers block 770606
// Test Seq.FoldRight(block#770608) covers block 770608
// Extracting the test for Seq.FoldRight(block#770608) from the counterexample...
method {:test} test54() {
var d0 : seq<int> := [0];
var r0 := Seq.FoldRight<int,int>((a0:int,a1:int)=>0, d0, 0);
}

}
