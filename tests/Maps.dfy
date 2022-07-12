include "../src//Collections/Maps/Maps.dfy"
module MapsUnitTests {
import Maps
import Wrappers
method {:test} test0() {
var d0 : map<int, int> := map[];
var d1 : map<int, int> := map[];
var r0 := Maps.Union<int,int>(d0, d1);
expect r0.Keys == d0.Keys + d1.Keys;
}
method {:test} test1() {
var d0 : map<int, int> := map[0 := 1, 2 := 3, 4 := 5, 6 := 7];
var d1 : set<int> := {0};
var r0 := Maps.Restrict<int,int>(d0, d1);
expect r0 == Maps.RemoveKeys(d0, d0.Keys - d1);
}
method {:test} test2() {
var d0 : map<int, int> := map[];
var d1 : set<int> := {};
var r0 := Maps.Restrict<int,int>(d0, d1);
expect r0 == Maps.RemoveKeys(d0, d0.Keys - d1);
}
method {:test} test3() {
var d0 : map<int, int> := map[];
var d1 : set<int> := {0};
var r0 := Maps.Restrict<int,int>(d0, d1);
expect r0 == Maps.RemoveKeys(d0, d0.Keys - d1);
}
method {:test} test5() {
var d0 : map<int, int> := map[0 := 1, 2 := 3, 4 := 5, 6 := 7];
var r0 := Maps.Remove<int,int>(d0, 8);
expect r0 == Maps.RemoveKeys(d0, {8});
expect |r0.Keys| <= |d0.Keys|;
expect 8 in d0 ==> |r0| == |d0| - 1;
expect 8 !in d0 ==> |r0| == |d0|;
}
method {:test} test6() {
var d0 : map<int, int> := map[];
var r0 := Maps.Remove<int,int>(d0, 0);
expect r0 == Maps.RemoveKeys(d0, {0});
expect |r0.Keys| <= |d0.Keys|;
expect 0 in d0 ==> |r0| == |d0| - 1;
expect 0 !in d0 ==> |r0| == |d0|;
}
method {:test} test7() {
var d0 : map<int, int> := map[0 := 1, 2 := 3, 4 := 5, 6 := 7];
var r0 := Maps.Remove<int,int>(d0, 6);
expect r0 == Maps.RemoveKeys(d0, {6});
expect |r0.Keys| <= |d0.Keys|;
expect 6 in d0 ==> |r0| == |d0| - 1;
expect 6 !in d0 ==> |r0| == |d0|;
}
method {:test} test9() {
var d0 : map<int, int> := map[];
var d1 : set<int> := {};
var r0 := Maps.RemoveKeys<int,int>(d0, d1);
expect r0.Keys == d0.Keys - d1;
}
method {:test} test10() {
var d0 : map<int, int> := map[0 := 1, 2 := 3, 4 := 5, 6 := 7];
var r0 := Maps.ToImap<int,int>(d0);
}
method {:test} test11() {
var d0 : map<int, int> := map[];
var r0 := Maps.ToImap<int,int>(d0);
}
method {:test} test13() {
var d0 : map<int, int> := map[0 := 1, 2 := 3, 4 := 5, 6 := 7];
var r0 := Maps.Get<int,int>(d0, 0);
}
method {:test} test14() {
var d0 : map<int, int> := map[];
var r0 := Maps.Get<int,int>(d0, 0);
}

}
