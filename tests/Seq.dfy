include "../src//Collections/Sequences/Seq.dfy"
module SeqUnitTests {
import Seq
import Wrappers
import Math
method {:test} test0() {
var d0 : seq<int> := [];
var r0 := Seq.FoldRight<int,int>((a0:int,a1:int)=>0, d0, 0);
}
method {:test} test1() {
var d0 : seq<int> := [0];
var r0 := Seq.FoldRight<int,int>((a0:int,a1:int)=>0, d0, 0);
}
method {:test} test2() {
var d0 : seq<int> := [];
var r0 := Seq.FoldLeft<int,int>((a0:int,a1:int)=>0, 0, d0);
}
method {:test} test3() {
var d0 : seq<int> := [1];
var r0 := Seq.FoldLeft<int,int>((a0:int,a1:int)=>0, 0, d0);
}
method {:test} test4() {
var d0 : seq<int> := [];
var r0 := Seq.Filter<int>((a0:int)=>false, d0);
expect |r0| <= |d0|;
}
method {:test} test5() {
var d0 : seq<int> := [0, 0];
var r0 := Seq.Filter<int>((a0:int)=>false, d0);
expect |r0| <= |d0|;
}
method {:test} test6() {
var d0 : seq<int> := [0];
var r0 := Seq.Filter<int>((a0:int)=>false, d0);
expect |r0| <= |d0|;
}
method {:test} test7() {
var d0 : Wrappers.Result<int, int> := Wrappers.Result<int, int>.Success(value:=0);
var d1 : seq<int> := [];
var r0 := Seq.MapWithResult<int,int,int>((a0:int)=>d0, d1);
}
method {:test} test8() {
var d0 : Wrappers.Result<int, int> := Wrappers.Result<int, int>.Success(value:=0);
var d1 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0];
var r0 := Seq.MapWithResult<int,int,int>((a0:int)=>d0, d1);
}
method {:test} test9() {
var d0 : seq<int> := [];
var r0 := Seq.Map<int,int>((a0:int)=>0, d0);
expect |r0| == |d0|;
}
method {:test} test10() {
var d0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0];
var r0 := Seq.Map<int,int>((a0:int)=>0, d0);
expect |r0| == |d0|;
}
method {:test} test11() {
var d0 : seq<seq<int>> := [];
var r0 := Seq.FlattenReverse<int>(d0);
}
method {:test} test12() {
var d0 : seq<int> := [];
var d1 : seq<int> := [];
var d2 : seq<seq<int>> := [d0, d1];
var r0 := Seq.FlattenReverse<int>(d2);
}
method {:test} test13() {
var d0 : seq<seq<int>> := [];
var r0 := Seq.Flatten<int>(d0);
}
method {:test} test14() {
var d0 : seq<int> := [];
var d1 : seq<int> := [0];
var d2 : seq<seq<int>> := [d0, d1];
var r0 := Seq.Flatten<int>(d2);
}
method {:test} test15() {
var d0 : seq<int> := [8855, 0, 0, 0, 0, 0, 5853, 0];
var r0 := Seq.Min(d0);
expect Seq.Min(d0) in d0;
}
method {:test} test16() {
var d0 : seq<int> := [0];
var r0 := Seq.Min(d0);
expect Seq.Min(d0) in d0;
}
method {:test} test17() {
var d0 : seq<int> := [8855, 0, 0, 0, 0, 0, 5853, 0];
var r0 := Seq.Max(d0);
expect Seq.Max(d0) in d0;
}
method {:test} test18() {
var d0 : seq<int> := [0];
var r0 := Seq.Max(d0);
expect Seq.Max(d0) in d0;
}
method {:test} test19() {
var d0 : seq<int> := [0, 0];
var d1 : seq<int> := [0, 1];
var r0 := Seq.Zip<int,int>(d0, d1);
expect |Seq.Zip(d0, d1)| == |d0|;
expect Seq.Unzip(Seq.Zip(d0, d1)).0 == d0;
expect Seq.Unzip(Seq.Zip(d0, d1)).1 == d1;
}
method {:test} test20() {
var d0 : seq<int> := [];
var d1 : seq<int> := [];
var r0 := Seq.Zip<int,int>(d0, d1);
expect |Seq.Zip(d0, d1)| == |d0|;
expect Seq.Unzip(Seq.Zip(d0, d1)).0 == d0;
expect Seq.Unzip(Seq.Zip(d0, d1)).1 == d1;
}


method {:test} test23() {
var r0 := Seq.Repeat<int>(0, (2 as nat));
expect |r0| == (2 as nat);
}
method {:test} test24() {
var r0 := Seq.Repeat<int>(0, (0 as nat));
expect |r0| == (0 as nat);
}
method {:test} test25() {
var d0 : seq<int> := [];
var r0 := Seq.Reverse<int>(d0);
expect |r0| == |d0|;
}
method {:test} test26() {
var d0 : seq<int> := [0, 0];
var r0 := Seq.Reverse<int>(d0);
expect |r0| == |d0|;
}
method {:test} test27() {
var d0 : seq<int> := [0, 0];
var r0 := Seq.Insert<int>(d0, 0, (1 as nat));
expect |Seq.Insert(d0, 0, (1 as nat))| == |d0| + 1;
expect Seq.Insert(d0, 0, (1 as nat))[(1 as nat)] == 0;
expect multiset(Seq.Insert(d0, 0, (1 as nat))) == multiset(d0) + multiset{0};
}
method {:test} test28() {
var d0 : seq<int> := [];
var r0 := Seq.RemoveValue<int>(d0, 0);
expect 0 !in d0 ==> d0 == r0;
expect 0 in d0 ==> |multiset(r0)| == |multiset(d0)| - 1;
expect 0 in d0 ==> multiset(r0)[0] == multiset(d0)[0] - 1;
}
method {:test} test29() {
var d0 : seq<int> := [0, 0, 0, 0, 0, 0, 0];
var r0 := Seq.RemoveValue<int>(d0, 0);
expect 0 !in d0 ==> d0 == r0;
expect 0 in d0 ==> |multiset(r0)| == |multiset(d0)| - 1;
expect 0 in d0 ==> multiset(r0)[0] == multiset(d0)[0] - 1;
}
method {:test} test30() {
var d0 : seq<int> := [0, 0, 0, 0, 0];
var r0 := Seq.Remove<int>(d0, (4 as nat));
expect |r0| == |d0| - 1;
}
method {:test} test31() {
var d0 : seq<int> := [];
var r0 := Seq.LastIndexOfOption<int>(d0, 0);
}
method {:test} test32() {
var d0 : seq<int> := [0, 0];
var r0 := Seq.LastIndexOfOption<int>(d0, 1);
}
method {:test} test33() {
var d0 : seq<int> := [0, 0, 0, 0, 0, 0, 0];
var r0 := Seq.LastIndexOfOption<int>(d0, 0);
}
method {:test} test34() {
var d0 : seq<int> := [0, 0, 0, 0, 0, 0, 0];
var r0 := Seq.LastIndexOf<int>(d0, 0);
expect r0 < |d0| && d0[r0] == 0;
}
method {:test} test35() {
var d0 : seq<int> := [0, 0, 1];
var r0 := Seq.LastIndexOf<int>(d0, 0);
expect r0 < |d0| && d0[r0] == 0;
}
method {:test} test36() {
var d0 : seq<int> := [];
var r0 := Seq.IndexOfOption<int>(d0, 0);
}
method {:test} test37() {
var d0 : seq<int> := [0];
var r0 := Seq.IndexOfOption<int>(d0, 1);
}
method {:test} test38() {
var d0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 1];
var r0 := Seq.IndexOfOption<int>(d0, 1);
}
method {:test} test39() {
var d0 : seq<int> := [0];
var r0 := Seq.IndexOfOption<int>(d0, 0);
}
method {:test} test40() {
var d0 : seq<int> := [1];
var r0 := Seq.IndexOf<int>(d0, 1);
expect r0 < |d0| && d0[r0] == 1;
}
method {:test} test41() {
var d0 : seq<int> := [0, 1];
var r0 := Seq.IndexOf<int>(d0, 1);
expect r0 < |d0| && d0[r0] == 1;
}
method {:test} test42() {
var d0 : seq<int> := [0, 0, 0, 0, 0, 0, 0];
var r0 := Seq.ToSet<int>(d0);
}
method {:test} test43() {
var d0 : seq<int> := [];
var r0 := Seq.ToSet<int>(d0);
}
method {:test} test45() {
var d0 : seq<int> := [0];
var r0 := Seq.ToArray<int>(d0);
expect r0.Length == |d0|;
}
method {:test} test47() {
var d0 : seq<int> := [0, 0, 0, 0, 0, 0, 0];
var r0 := Seq.ToArray<int>(d0);
expect r0.Length == |d0|;
}
method {:test} test49() {
var d0 : seq<int> := [0, 0];
var r0 := Seq.DropLast<int>(d0);
}
method {:test} test50() {
var d0 : seq<int> := [0, 0, 0, 0, 0, 0, 0];
var r0 := Seq.Last<int>(d0);
}
method {:test} test51() {
var d0 : seq<int> := [0];
var r0 := Seq.DropFirst<int>(d0);
}
method {:test} test52() {
var d0 : seq<int> := [0];
var r0 := Seq.First<int>(d0);
}

}
