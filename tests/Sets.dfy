include "../src//Collections/Sets/Sets.dfy"
module SetsUnitTests {
import Sets
import Functions
method {:test} test0() {
var r0 := Sets.SetRangeZeroBound(1);
expect |r0| == 1;
}
method {:test} test1() {
var r0 := Sets.SetRange(2437, 2438);
expect |r0| == 2438 - 2437;
}
method {:test} test2() {
var r0 := Sets.SetRange(15, 15);
expect |r0| == 15 - 15;
}
method {:test} test3() {
var d0 : set<int> := {0, 1, 2};
var r0 := Sets.Filter<int>(d0, (a0:int)=>false);
expect |r0| <= |d0|;
}
method {:test} test4() {
var d0 : set<int> := {};
var r0 := Sets.Filter<int>(d0, (a0:int)=>false);
expect |r0| <= |d0|;
}
method {:test} test5() {
var d0 : set<int> := {0};
var r0 := Sets.Filter<int>(d0, (a0:int)=>false);
expect |r0| <= |d0|;
}
/*method {:test} test7() {
var d0 : set<int> := {0, 1, 2};
var r0 := Sets.Map<int,int>(d0, (a0:int)=>0);
expect |d0| == |r0|;
}*/
method {:test} test8() {
var d0 : set<int> := {};
var r0 := Sets.Map<int,int>(d0, (a0:int)=>0);
expect |d0| == |r0|;
}

}
