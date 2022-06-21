include "../src//Collections/Sets/Sets.dfy"
module SetsUnitTests {
import Sets
import Functions
method {:test} test0() {
var r0 := Sets.SetRangeZeroBound(1);
}
method {:test} test1() {
var r0 := Sets.SetRange(2437, 2438);
}
method {:test} test2() {
var r0 := Sets.SetRange(15, 15);
}
method {:test} test3() {
var r0 := Sets.Filter<int>({0, 1, 2}, (a0:int)=>false);
}
method {:test} test4() {
var r0 := Sets.Filter<int>({}, (a0:int)=>false);
}
method {:test} test5() {
var r0 := Sets.Filter<int>({0}, (a0:int)=>false);
}
method {:test} test7() {
var r0 := Sets.Map<int,int>({0, 1, 2}, (a0:int)=>0);
}
method {:test} test8() {
var r0 := Sets.Map<int,int>({}, (a0:int)=>0);
}

}
