include "../src//Collections/Sequences/Seq.dfy"
module SeqUnitTests {
import Seq
import Wrappers
import Math
method {:test} test0() {
var r0 := Seq.FoldRight<int,int>((a0:int,a1:int)=>0, [], 0);
}
method {:test} test1() {
var r0 := Seq.FoldRight<int,int>((a0:int,a1:int)=>0, [0], 0);
}
method {:test} test2() {
var r0 := Seq.FoldLeft<int,int>((a0:int,a1:int)=>0, 0, []);
}
method {:test} test3() {
var r0 := Seq.FoldLeft<int,int>((a0:int,a1:int)=>0, 0, [1]);
}
method {:test} test4() {
var r0 := Seq.Filter<int>((a0:int)=>false, []);
}
method {:test} test5() {
var r0 := Seq.Filter<int>((a0:int)=>false, [0, 0]);
}
method {:test} test6() {
var r0 := Seq.Filter<int>((a0:int)=>false, [0]);
}
method {:test} test7() {
var d0 : Wrappers.Result<int, int> := Wrappers.Result<int, int>.Success(value:=0);
var r0 := Seq.MapWithResult<int,int,int>((a0:int)=>d0, []);
}
method {:test} test8() {
var d0 : Wrappers.Result<int, int> := Wrappers.Result<int, int>.Success(value:=0);
var r0 := Seq.MapWithResult<int,int,int>((a0:int)=>d0, [0, 0, 0, 0, 0, 0, 0, 0]);
}
method {:test} test9() {
var r0 := Seq.Map<int,int>((a0:int)=>0, []);
}
method {:test} test10() {
var r0 := Seq.Map<int,int>((a0:int)=>0, [0, 0, 0, 0, 0, 0, 0, 0]);
}
method {:test} test11() {
var r0 := Seq.FlattenReverse<int>([]);
}
method {:test} test12() {
var r0 := Seq.FlattenReverse<int>([[], []]);
}
method {:test} test13() {
var r0 := Seq.Flatten<int>([]);
}
method {:test} test14() {
var r0 := Seq.Flatten<int>([[], [0]]);
}
method {:test} test15() {
var r0 := Seq.Min([8855, 0, 0, 0, 0, 0, 5853, 0]);
}
method {:test} test16() {
var r0 := Seq.Min([0]);
}
method {:test} test17() {
var r0 := Seq.Max([8855, 0, 0, 0, 0, 0, 5853, 0]);
}
method {:test} test18() {
var r0 := Seq.Max([0]);
}
method {:test} test19() {
var r0 := Seq.Zip<int,int>([0, 0], [0, 1]);
}
method {:test} test20() {
var r0 := Seq.Zip<int,int>([], []);
}
method {:test} test21() {
var r0 := Seq.Unzip<int,int>([]);
}
method {:test} test22() {
var d0 := (0,0);
var d1 := (0,1);
var r0 := Seq.Unzip<int,int>([d0, d1]);
}
method {:test} test23() {
var r0 := Seq.Repeat<int>(0, (2 as nat));
}
method {:test} test24() {
var r0 := Seq.Repeat<int>(0, (0 as nat));
}
method {:test} test25() {
var r0 := Seq.Reverse<int>([]);
}
method {:test} test26() {
var r0 := Seq.Reverse<int>([0, 0]);
}
method {:test} test27() {
var r0 := Seq.Insert<int>([0, 0], 0, (1 as nat));
}
method {:test} test28() {
var r0 := Seq.RemoveValue<int>([], 0);
}
method {:test} test29() {
var r0 := Seq.RemoveValue<int>([0, 0, 0, 0, 0, 0, 0], 0);
}
method {:test} test30() {
var r0 := Seq.Remove<int>([0, 0, 0, 0, 0], (4 as nat));
}
method {:test} test31() {
var r0 := Seq.LastIndexOfOption<int>([], 0);
}
method {:test} test32() {
var r0 := Seq.LastIndexOfOption<int>([0, 0], 1);
}
method {:test} test33() {
var r0 := Seq.LastIndexOfOption<int>([0, 0, 0, 0, 0, 0, 0], 0);
}
method {:test} test34() {
var r0 := Seq.LastIndexOf<int>([0, 0, 0, 0, 0, 0, 0], 0);
}
method {:test} test35() {
var r0 := Seq.LastIndexOf<int>([0, 0, 1], 0);
}
method {:test} test36() {
var r0 := Seq.IndexOfOption<int>([], 0);
}
method {:test} test37() {
var r0 := Seq.IndexOfOption<int>([0], 1);
}
method {:test} test38() {
var r0 := Seq.IndexOfOption<int>([0, 0, 0, 0, 0, 0, 0, 1], 1);
}
method {:test} test39() {
var r0 := Seq.IndexOfOption<int>([0], 0);
}
method {:test} test40() {
var r0 := Seq.IndexOf<int>([1], 1);
}
method {:test} test41() {
var r0 := Seq.IndexOf<int>([0, 1], 1);
}
method {:test} test42() {
var r0 := Seq.ToSet<int>([0, 0, 0, 0, 0, 0, 0]);
}
method {:test} test43() {
var r0 := Seq.ToSet<int>([]);
}
method {:test} test45() {
var r0 := Seq.ToArray<int>([0]);
}
method {:test} test47() {
var r0 := Seq.ToArray<int>([0, 0, 0, 0, 0, 0, 0]);
}
method {:test} test49() {
var r0 := Seq.DropLast<int>([0, 0]);
}
method {:test} test50() {
var r0 := Seq.Last<int>([0, 0, 0, 0, 0, 0, 0]);
}
method {:test} test51() {
var r0 := Seq.DropFirst<int>([0]);
}
method {:test} test52() {
var r0 := Seq.First<int>([0]);
}

}
