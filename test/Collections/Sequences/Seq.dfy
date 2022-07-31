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
// Test Seq.First(block#822750) covers block 822750
// Extracting the test for Seq.First(block#822750) from the counterexample...
method {:test} test0() {
var d0 : seq<int> := [0];
var r0 := Seq.First<int>(d0);
}
// Test Seq.DropFirst(block#823813) covers block 823813
// Extracting the test for Seq.DropFirst(block#823813) from the counterexample...
method {:test} test1() {
var d0 : seq<int> := [0];
var r0 := Seq.DropFirst<int>(d0);
}
// Test Seq.Last(block#824878) covers block 824878
// Extracting the test for Seq.Last(block#824878) from the counterexample...
method {:test} test2() {
var d0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var r0 := Seq.Last<int>(d0);
}
// Test Seq.DropLast(block#825957) covers block 825957
// Extracting the test for Seq.DropLast(block#825957) from the counterexample...
method {:test} test3() {
var d0 : seq<int> := [0, 0];
var r0 := Seq.DropLast<int>(d0);
}
// Test Seq.ToArray(block#834685) covers block 834674
// Test Seq.ToArray(block#834685) covers block 834685
// Extracting the test for Seq.ToArray(block#834685) from the counterexample...
method {:test} test4() {
var d0 : seq<int> := [0];
var r0 := Seq.ToArray<int>(d0);
expect r0.Length == |d0|;
}
// No test can be generated for Seq.ToArray(block#834683) because the verifier suceeded.
// No test can be generated for Seq.ToArray(block#834682) because the verifier suceeded.
// Test Seq.ToArray(block#834681) covers block 834674
// Test Seq.ToArray(block#834681) covers block 834675
// Test Seq.ToArray(block#834681) covers block 834676
// Test Seq.ToArray(block#834681) covers block 834677
// Test Seq.ToArray(block#834681) covers block 834681
// Extracting the test for Seq.ToArray(block#834681) from the counterexample...
// Test for Seq.ToArray(block#834681) matches a test previously generated for Seq.ToArray(block#834685).
// Test Seq.ToArray(block#834680) covers block 834674
// Test Seq.ToArray(block#834680) covers block 834675
// Test Seq.ToArray(block#834680) covers block 834676
// Test Seq.ToArray(block#834680) covers block 834677
// Test Seq.ToArray(block#834680) covers block 834680
// Extracting the test for Seq.ToArray(block#834680) from the counterexample...
method {:test} test6() {
var d0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var r0 := Seq.ToArray<int>(d0);
expect r0.Length == |d0|;
}
// Test Seq.ToArray(block#834678) covers block 834674
// Test Seq.ToArray(block#834678) covers block 834675
// Test Seq.ToArray(block#834678) covers block 834676
// Test Seq.ToArray(block#834678) covers block 834678
// Extracting the test for Seq.ToArray(block#834678) from the counterexample...
// Test for Seq.ToArray(block#834678) matches a test previously generated for Seq.ToArray(block#834685).
// Test Seq.ToSet(block#835509) covers block 835504
// Test Seq.ToSet(block#835509) covers block 835505
// Test Seq.ToSet(block#835509) covers block 835506
// Test Seq.ToSet(block#835509) covers block 835509
// Extracting the test for Seq.ToSet(block#835509) from the counterexample...
method {:test} test8() {
var d0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var r0 := Seq.ToSet<int>(d0);
}
// Test Seq.ToSet(block#835508) covers block 835504
// Test Seq.ToSet(block#835508) covers block 835508
// Extracting the test for Seq.ToSet(block#835508) from the counterexample...
method {:test} test9() {
var d0 : seq<int> := [];
var r0 := Seq.ToSet<int>(d0);
}
// Test Seq.ToSet(block#835507) covers block 835504
// Test Seq.ToSet(block#835507) covers block 835505
// Test Seq.ToSet(block#835507) covers block 835507
// Extracting the test for Seq.ToSet(block#835507) from the counterexample...
// Test for Seq.ToSet(block#835507) matches a test previously generated for Seq.ToSet(block#835508).
// Test Seq.IndexOf(block#843706) covers block 843703
// Test Seq.IndexOf(block#843706) covers block 843704
// Test Seq.IndexOf(block#843706) covers block 843706
// Extracting the test for Seq.IndexOf(block#843706) from the counterexample...
method {:test} test11() {
var d0 : seq<int> := [1];
var r0 := Seq.IndexOf<int>(d0, 1);
expect r0 < |d0| && d0[r0] == 1;
}
// Test Seq.IndexOf(block#843705) covers block 843703
// Test Seq.IndexOf(block#843705) covers block 843705
// Extracting the test for Seq.IndexOf(block#843705) from the counterexample...
method {:test} test12() {
var d0 : seq<int> := [0, 1];
var r0 := Seq.IndexOf<int>(d0, 1);
expect r0 < |d0| && d0[r0] == 1;
}
// Test Seq.IndexOfOption(block#846511) covers block 846504
// Test Seq.IndexOfOption(block#846511) covers block 846505
// Test Seq.IndexOfOption(block#846511) covers block 846511
// Extracting the test for Seq.IndexOfOption(block#846511) from the counterexample...
method {:test} test13() {
var d0 : seq<int> := [];
var r0 := Seq.IndexOfOption<int>(d0, 0);
}
// Test Seq.IndexOfOption(block#846510) covers block 846504
// Test Seq.IndexOfOption(block#846510) covers block 846506
// Test Seq.IndexOfOption(block#846510) covers block 846508
// Test Seq.IndexOfOption(block#846510) covers block 846510
// Extracting the test for Seq.IndexOfOption(block#846510) from the counterexample...
method {:test} test14() {
var d0 : seq<int> := [0];
var r0 := Seq.IndexOfOption<int>(d0, 1);
}
// Test Seq.IndexOfOption(block#846509) covers block 846504
// Test Seq.IndexOfOption(block#846509) covers block 846506
// Test Seq.IndexOfOption(block#846509) covers block 846508
// Test Seq.IndexOfOption(block#846509) covers block 846509
// Extracting the test for Seq.IndexOfOption(block#846509) from the counterexample...
method {:test} test15() {
var d0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1];
var r0 := Seq.IndexOfOption<int>(d0, 1);
}
// Test Seq.IndexOfOption(block#846507) covers block 846504
// Test Seq.IndexOfOption(block#846507) covers block 846506
// Test Seq.IndexOfOption(block#846507) covers block 846507
// Extracting the test for Seq.IndexOfOption(block#846507) from the counterexample...
method {:test} test16() {
var d0 : seq<int> := [0];
var r0 := Seq.IndexOfOption<int>(d0, 0);
}
// Test Seq.LastIndexOf(block#848633) covers block 848630
// Test Seq.LastIndexOf(block#848633) covers block 848631
// Test Seq.LastIndexOf(block#848633) covers block 848633
// Extracting the test for Seq.LastIndexOf(block#848633) from the counterexample...
method {:test} test17() {
var d0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var r0 := Seq.LastIndexOf<int>(d0, 0);
expect r0 < |d0| && d0[r0] == 0;
}
// Test Seq.LastIndexOf(block#848632) covers block 848630
// Test Seq.LastIndexOf(block#848632) covers block 848632
// Extracting the test for Seq.LastIndexOf(block#848632) from the counterexample...
method {:test} test18() {
var d0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1];
var r0 := Seq.LastIndexOf<int>(d0, 0);
expect r0 < |d0| && d0[r0] == 0;
}
// Test Seq.LastIndexOfOption(block#851085) covers block 851080
// Test Seq.LastIndexOfOption(block#851085) covers block 851081
// Test Seq.LastIndexOfOption(block#851085) covers block 851085
// Extracting the test for Seq.LastIndexOfOption(block#851085) from the counterexample...
method {:test} test19() {
var d0 : seq<int> := [];
var r0 := Seq.LastIndexOfOption<int>(d0, 0);
}
// Test Seq.LastIndexOfOption(block#851084) covers block 851080
// Test Seq.LastIndexOfOption(block#851084) covers block 851082
// Test Seq.LastIndexOfOption(block#851084) covers block 851084
// Extracting the test for Seq.LastIndexOfOption(block#851084) from the counterexample...
method {:test} test20() {
var d0 : seq<int> := [0, 0];
var r0 := Seq.LastIndexOfOption<int>(d0, 1);
}
// Test Seq.LastIndexOfOption(block#851083) covers block 851080
// Test Seq.LastIndexOfOption(block#851083) covers block 851082
// Test Seq.LastIndexOfOption(block#851083) covers block 851083
// Extracting the test for Seq.LastIndexOfOption(block#851083) from the counterexample...
method {:test} test21() {
var d0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var r0 := Seq.LastIndexOfOption<int>(d0, 0);
}
// Test Seq.Remove(block#852840) covers block 852840
// Extracting the test for Seq.Remove(block#852840) from the counterexample...
method {:test} test22() {
var d0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var r0 := Seq.Remove<int>(d0, (39 as nat));
expect |r0| == |d0| - 1;
}
// Test Seq.RemoveValue(block#855364) covers block 855361
// Test Seq.RemoveValue(block#855364) covers block 855362
// Test Seq.RemoveValue(block#855364) covers block 855364
// Extracting the test for Seq.RemoveValue(block#855364) from the counterexample...
method {:test} test23() {
var d0 : seq<int> := [];
var r0 := Seq.RemoveValue<int>(d0, 0);
expect 0 !in d0 ==> d0 == r0;
expect 0 in d0 ==> |multiset(r0)| == |multiset(d0)| - 1;
expect 0 in d0 ==> multiset(r0)[0] == multiset(d0)[0] - 1;
}
// Test Seq.RemoveValue(block#855363) covers block 855361
// Test Seq.RemoveValue(block#855363) covers block 855363
// Extracting the test for Seq.RemoveValue(block#855363) from the counterexample...
method {:test} test24() {
var d0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var r0 := Seq.RemoveValue<int>(d0, 0);
expect 0 !in d0 ==> d0 == r0;
expect 0 in d0 ==> |multiset(r0)| == |multiset(d0)| - 1;
expect 0 in d0 ==> multiset(r0)[0] == multiset(d0)[0] - 1;
}
// Test Seq.Insert(block#858265) covers block 858265
// Extracting the test for Seq.Insert(block#858265) from the counterexample...
method {:test} test25() {
var d0 : seq<int> := [0, 0];
var r0 := Seq.Insert<int>(d0, 0, (1 as nat));
expect |Seq.Insert(d0, 0, (1 as nat))| == |d0| + 1;
expect Seq.Insert(d0, 0, (1 as nat))[(1 as nat)] == 0;
expect multiset(Seq.Insert(d0, 0, (1 as nat))) == multiset(d0) + multiset{0};
}
// Test Seq.Reverse(block#860241) covers block 860238
// Test Seq.Reverse(block#860241) covers block 860239
// Test Seq.Reverse(block#860241) covers block 860241
// Extracting the test for Seq.Reverse(block#860241) from the counterexample...
method {:test} test26() {
var d0 : seq<int> := [];
var r0 := Seq.Reverse<int>(d0);
expect |r0| == |d0|;
}
// Test Seq.Reverse(block#860240) covers block 860238
// Test Seq.Reverse(block#860240) covers block 860240
// Extracting the test for Seq.Reverse(block#860240) from the counterexample...
method {:test} test27() {
var d0 : seq<int> := [0, 0];
var r0 := Seq.Reverse<int>(d0);
expect |r0| == |d0|;
}
// Test Seq.Repeat(block#862069) covers block 862066
// Test Seq.Repeat(block#862069) covers block 862068
// Test Seq.Repeat(block#862069) covers block 862069
// Extracting the test for Seq.Repeat(block#862069) from the counterexample...
method {:test} test28() {
var r0 := Seq.Repeat<int>(0, (2 as nat));
expect |r0| == (2 as nat);
}
// Test Seq.Repeat(block#862067) covers block 862066
// Test Seq.Repeat(block#862067) covers block 862067
// Extracting the test for Seq.Repeat(block#862067) from the counterexample...
method {:test} test29() {
var r0 := Seq.Repeat<int>(0, (0 as nat));
expect |r0| == (0 as nat);
}
// Test Seq.Unzip(block#865833) covers block 865830
// Test Seq.Unzip(block#865833) covers block 865831
// Test Seq.Unzip(block#865833) covers block 865833
// Extracting the test for Seq.Unzip(block#865833) from the counterexample...
// Failed - temporary disable datatype support
// Test Seq.Unzip(block#865832) covers block 865830
// Test Seq.Unzip(block#865832) covers block 865832
// Extracting the test for Seq.Unzip(block#865832) from the counterexample...
// Failed - temporary disable datatype support
// Test Seq.Zip(block#869314) covers block 869311
// Test Seq.Zip(block#869314) covers block 869313
// Test Seq.Zip(block#869314) covers block 869314
// Extracting the test for Seq.Zip(block#869314) from the counterexample...
method {:test} test32() {
var d0 : seq<int> := [0, 0];
var d1 : seq<int> := [0, 1];
var r0 := Seq.Zip<int,int>(d0, d1);
expect |Seq.Zip(d0, d1)| == |d0|;
expect Seq.Unzip(Seq.Zip(d0, d1)).0 == d0;
expect Seq.Unzip(Seq.Zip(d0, d1)).1 == d1;
}
// Test Seq.Zip(block#869312) covers block 869311
// Test Seq.Zip(block#869312) covers block 869312
// Extracting the test for Seq.Zip(block#869312) from the counterexample...
method {:test} test33() {
var d0 : seq<int> := [];
var d1 : seq<int> := [];
var r0 := Seq.Zip<int,int>(d0, d1);
expect |Seq.Zip(d0, d1)| == |d0|;
expect Seq.Unzip(Seq.Zip(d0, d1)).0 == d0;
expect Seq.Unzip(Seq.Zip(d0, d1)).1 == d1;
}
// Test Seq.Max(block#872604) covers block 872601
// Test Seq.Max(block#872604) covers block 872603
// Test Seq.Max(block#872604) covers block 872604
// Extracting the test for Seq.Max(block#872604) from the counterexample...
method {:test} test34() {
var d0 : seq<int> := [8855, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5853, 0, 0, 0, 0, 0, 0, 5853, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var r0 := Seq.Max(d0);
expect Seq.Max(d0) in d0;
}
// Test Seq.Max(block#872602) covers block 872601
// Test Seq.Max(block#872602) covers block 872602
// Extracting the test for Seq.Max(block#872602) from the counterexample...
method {:test} test35() {
var d0 : seq<int> := [0];
var r0 := Seq.Max(d0);
expect Seq.Max(d0) in d0;
}
// Test Seq.Min(block#876344) covers block 876341
// Test Seq.Min(block#876344) covers block 876343
// Test Seq.Min(block#876344) covers block 876344
// Extracting the test for Seq.Min(block#876344) from the counterexample...
method {:test} test36() {
var d0 : seq<int> := [8855, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5853, 0, 0, 0, 0, 0, 0, 5853, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var r0 := Seq.Min(d0);
expect Seq.Min(d0) in d0;
}
// Test Seq.Min(block#876342) covers block 876341
// Test Seq.Min(block#876342) covers block 876342
// Extracting the test for Seq.Min(block#876342) from the counterexample...
method {:test} test37() {
var d0 : seq<int> := [0];
var r0 := Seq.Min(d0);
expect Seq.Min(d0) in d0;
}
// Test Seq.Flatten(block#883749) covers block 883746
// Test Seq.Flatten(block#883749) covers block 883747
// Test Seq.Flatten(block#883749) covers block 883749
// Extracting the test for Seq.Flatten(block#883749) from the counterexample...
method {:test} test38() {
var d0 : seq<seq<int>> := [];
var r0 := Seq.Flatten<int>(d0);
}
// Test Seq.Flatten(block#883748) covers block 883746
// Test Seq.Flatten(block#883748) covers block 883748
// Extracting the test for Seq.Flatten(block#883748) from the counterexample...
method {:test} test39() {
var d0 : seq<int> := [];
var d1 : seq<int> := [0];
var d2 : seq<seq<int>> := [d0, d1];
var r0 := Seq.Flatten<int>(d2);
}
// Test Seq.FlattenReverse(block#887087) covers block 887084
// Test Seq.FlattenReverse(block#887087) covers block 887085
// Test Seq.FlattenReverse(block#887087) covers block 887087
// Extracting the test for Seq.FlattenReverse(block#887087) from the counterexample...
method {:test} test40() {
var d0 : seq<seq<int>> := [];
var r0 := Seq.FlattenReverse<int>(d0);
}
// Test Seq.FlattenReverse(block#887086) covers block 887084
// Test Seq.FlattenReverse(block#887086) covers block 887086
// Extracting the test for Seq.FlattenReverse(block#887086) from the counterexample...
method {:test} test41() {
var d0 : seq<int> := [];
var d1 : seq<int> := [];
var d2 : seq<seq<int>> := [d0, d1];
var r0 := Seq.FlattenReverse<int>(d2);
}
// Test Seq.Map(block#897153) covers block 897150
// Test Seq.Map(block#897153) covers block 897151
// Test Seq.Map(block#897153) covers block 897153
// Extracting the test for Seq.Map(block#897153) from the counterexample...
method {:test} test42() {
var d0 : seq<int> := [];
var r0 := Seq.Map<int,int>((a0:int)=>0, d0);
expect |r0| == |d0|;
}
// Test Seq.Map(block#897152) covers block 897150
// Test Seq.Map(block#897152) covers block 897152
// Extracting the test for Seq.Map(block#897152) from the counterexample...
method {:test} test43() {
var d0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var r0 := Seq.Map<int,int>((a0:int)=>0, d0);
expect |r0| == |d0|;
}
// Test Seq.MapWithResult(block#903143) covers block 903136
// Test Seq.MapWithResult(block#903143) covers block 903137
// Test Seq.MapWithResult(block#903143) covers block 903143
// Extracting the test for Seq.MapWithResult(block#903143) from the counterexample...
method {:test} test44() {
var d0 : Wrappers.Result<int, int> := Wrappers.Result<int, int>.Success(value:=0);
var d1 : seq<int> := [];
var r0 := Seq.MapWithResult<int,int,int>((a0:int)=>d0, d1);
}
// Test Seq.MapWithResult(block#903142) covers block 903136
// Test Seq.MapWithResult(block#903142) covers block 903138
// Test Seq.MapWithResult(block#903142) covers block 903140
// Test Seq.MapWithResult(block#903142) covers block 903142
// Extracting the test for Seq.MapWithResult(block#903142) from the counterexample...
method {:test} test45() {
var d0 : Wrappers.Result<int, int> := Wrappers.Result<int, int>.Success(value:=0);
var d1 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var r0 := Seq.MapWithResult<int,int,int>((a0:int)=>d0, d1);
}
// Test Seq.MapWithResult(block#903141) covers block 903136
// Test Seq.MapWithResult(block#903141) covers block 903138
// Test Seq.MapWithResult(block#903141) covers block 903140
// Test Seq.MapWithResult(block#903141) covers block 903141
// Extracting the test for Seq.MapWithResult(block#903141) from the counterexample...
method {:test} test46() {
var d0 : Wrappers.Result<int, int> := Wrappers.Result<int, int>.Success(value:=0);
var d1 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var r0 := Seq.MapWithResult<int,int,int>((a0:int)=>d0, d1);
}
// Test Seq.MapWithResult(block#903139) covers block 903136
// Test Seq.MapWithResult(block#903139) covers block 903138
// Test Seq.MapWithResult(block#903139) covers block 903139
// Extracting the test for Seq.MapWithResult(block#903139) from the counterexample...
method {:test} test47() {
var d0 : Wrappers.Result<int, int> := Wrappers.Result<int, int>.Success(value:=0);
var d1 : seq<int> := [0];
var r0 := Seq.MapWithResult<int,int,int>((a0:int)=>d0, d1);
}
// Test Seq.Filter(block#910664) covers block 910658
// Test Seq.Filter(block#910664) covers block 910659
// Test Seq.Filter(block#910664) covers block 910664
// Extracting the test for Seq.Filter(block#910664) from the counterexample...
method {:test} test48() {
var d0 : seq<int> := [];
var r0 := Seq.Filter<int>((a0:int)=>false, d0);
expect |r0| <= |d0|;
}
// Test Seq.Filter(block#910663) covers block 910658
// Test Seq.Filter(block#910663) covers block 910660
// Test Seq.Filter(block#910663) covers block 910661
// Test Seq.Filter(block#910663) covers block 910663
// Extracting the test for Seq.Filter(block#910663) from the counterexample...
method {:test} test49() {
var d0 : seq<int> := [0, 0];
var r0 := Seq.Filter<int>((a0:int)=>false, d0);
expect |r0| <= |d0|;
}
// Test Seq.Filter(block#910662) covers block 910658
// Test Seq.Filter(block#910662) covers block 910660
// Test Seq.Filter(block#910662) covers block 910662
// Extracting the test for Seq.Filter(block#910662) from the counterexample...
method {:test} test50() {
var d0 : seq<int> := [0];
var r0 := Seq.Filter<int>((a0:int)=>false, d0);
expect |r0| <= |d0|;
}
// Test Seq.FoldLeft(block#916719) covers block 916716
// Test Seq.FoldLeft(block#916719) covers block 916717
// Test Seq.FoldLeft(block#916719) covers block 916719
// Extracting the test for Seq.FoldLeft(block#916719) from the counterexample...
method {:test} test51() {
var d0 : seq<int> := [];
var r0 := Seq.FoldLeft<int,int>((a0:int,a1:int)=>0, 0, d0);
}
// Test Seq.FoldLeft(block#916718) covers block 916716
// Test Seq.FoldLeft(block#916718) covers block 916718
// Extracting the test for Seq.FoldLeft(block#916718) from the counterexample...
method {:test} test52() {
var d0 : seq<int> := [1];
var r0 := Seq.FoldLeft<int,int>((a0:int,a1:int)=>0, 0, d0);
}
// Test Seq.FoldRight(block#923634) covers block 923631
// Test Seq.FoldRight(block#923634) covers block 923632
// Test Seq.FoldRight(block#923634) covers block 923634
// Extracting the test for Seq.FoldRight(block#923634) from the counterexample...
method {:test} test53() {
var d0 : seq<int> := [];
var r0 := Seq.FoldRight<int,int>((a0:int,a1:int)=>0, d0, 0);
}
// Test Seq.FoldRight(block#923633) covers block 923631
// Test Seq.FoldRight(block#923633) covers block 923633
// Extracting the test for Seq.FoldRight(block#923633) from the counterexample...
method {:test} test54() {
var d0 : seq<int> := [0];
var r0 := Seq.FoldRight<int,int>((a0:int,a1:int)=>0, d0, 0);
}

}
