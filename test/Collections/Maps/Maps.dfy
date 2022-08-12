include "../../..//src/Collections/Maps/Maps.dfy"
module srcCollectionsMapsMapsdfyUnitTests {
import Maps
import Wrappers
// Merging boogie files...
// Converting function calls to method calls...
// Adding Impl$$ methods to support inlining...
// Removing assertions...
// Annotating blocks...
// Generating modifications...
// Test Maps.Get(block#281143) covers block 281140
// Test Maps.Get(block#281143) covers block 281141
// Test Maps.Get(block#281143) covers block 281143
// Extracting the test for Maps.Get(block#281143) from the counterexample...
method {:test} test0() {
var d0 : map<int, int> := map[0 := 1, 2 := 3, 4 := 5, 6 := 7];
var r0 := Maps.Get<int,int>(d0, 0);
}
// Test Maps.Get(block#281142) covers block 281140
// Test Maps.Get(block#281142) covers block 281142
// Extracting the test for Maps.Get(block#281142) from the counterexample...
method {:test} test1() {
var d0 : map<int, int> := map[];
var r0 := Maps.Get<int,int>(d0, 0);
}
// Test Maps.ToImap(block#282340) covers block 282335
// Test Maps.ToImap(block#282340) covers block 282336
// Test Maps.ToImap(block#282340) covers block 282337
// Test Maps.ToImap(block#282340) covers block 282340
// Extracting the test for Maps.ToImap(block#282340) from the counterexample...
method {:test} test2() {
var d0 : map<int, int> := map[0 := 1, 2 := 3, 4 := 5, 6 := 7];
var r0 := Maps.ToImap<int,int>(d0);
}
// Test Maps.ToImap(block#282339) covers block 282335
// Test Maps.ToImap(block#282339) covers block 282339
// Extracting the test for Maps.ToImap(block#282339) from the counterexample...
method {:test} test3() {
var d0 : map<int, int> := map[];
var r0 := Maps.ToImap<int,int>(d0);
}
// Test Maps.ToImap(block#282338) covers block 282335
// Test Maps.ToImap(block#282338) covers block 282336
// Test Maps.ToImap(block#282338) covers block 282338
// Extracting the test for Maps.ToImap(block#282338) from the counterexample...
// Test for Maps.ToImap(block#282338) matches a test previously generated for Maps.ToImap(block#282339).
// Test Maps.RemoveKeys(block#283564) covers block 283564
// Extracting the test for Maps.RemoveKeys(block#283564) from the counterexample...
method {:test} test5() {
var d0 : map<int, int> := map[];
var d1 : set<int> := {};
var r0 := Maps.RemoveKeys<int,int>(d0, d1);
expect r0.Keys == d0.Keys - d1;
}
// Test Maps.Remove(block#285146) covers block 285138
// Test Maps.Remove(block#285146) covers block 285139
// Test Maps.Remove(block#285146) covers block 285140
// Test Maps.Remove(block#285146) covers block 285143
// Test Maps.Remove(block#285146) covers block 285146
// Extracting the test for Maps.Remove(block#285146) from the counterexample...
method {:test} test6() {
var d0 : map<int, int> := map[0 := 1, 2 := 3, 4 := 5, 6 := 7];
var r0 := Maps.Remove<int,int>(d0, 8);
expect r0 == Maps.RemoveKeys(d0, {8});
expect |r0.Keys| <= |d0.Keys|;
expect 8 in d0 ==> |r0| == |d0| - 1;
expect 8 !in d0 ==> |r0| == |d0|;
}
// Test Maps.Remove(block#285145) covers block 285138
// Test Maps.Remove(block#285145) covers block 285145
// Extracting the test for Maps.Remove(block#285145) from the counterexample...
method {:test} test7() {
var d0 : map<int, int> := map[];
var r0 := Maps.Remove<int,int>(d0, 0);
expect r0 == Maps.RemoveKeys(d0, {0});
expect |r0.Keys| <= |d0.Keys|;
expect 0 in d0 ==> |r0| == |d0| - 1;
expect 0 !in d0 ==> |r0| == |d0|;
}
// Test Maps.Remove(block#285144) covers block 285138
// Test Maps.Remove(block#285144) covers block 285139
// Test Maps.Remove(block#285144) covers block 285140
// Test Maps.Remove(block#285144) covers block 285144
// Extracting the test for Maps.Remove(block#285144) from the counterexample...
method {:test} test8() {
var d0 : map<int, int> := map[0 := 1, 2 := 3, 4 := 5, 6 := 7];
var r0 := Maps.Remove<int,int>(d0, 6);
expect r0 == Maps.RemoveKeys(d0, {6});
expect |r0.Keys| <= |d0.Keys|;
expect 6 in d0 ==> |r0| == |d0| - 1;
expect 6 !in d0 ==> |r0| == |d0|;
}
// Test Maps.Remove(block#285141) covers block 285138
// Test Maps.Remove(block#285141) covers block 285139
// Test Maps.Remove(block#285141) covers block 285141
// Extracting the test for Maps.Remove(block#285141) from the counterexample...
// Test for Maps.Remove(block#285141) matches a test previously generated for Maps.Remove(block#285145).
// Test Maps.Restrict(block#286265) covers block 286257
// Test Maps.Restrict(block#286265) covers block 286258
// Test Maps.Restrict(block#286265) covers block 286259
// Test Maps.Restrict(block#286265) covers block 286262
// Test Maps.Restrict(block#286265) covers block 286265
// Extracting the test for Maps.Restrict(block#286265) from the counterexample...
method {:test} test10() {
var d0 : map<int, int> := map[0 := 1, 2 := 3, 4 := 5, 6 := 7];
var d1 : set<int> := {0};
var r0 := Maps.Restrict<int,int>(d0, d1);
expect r0 == Maps.RemoveKeys(d0, d0.Keys - d1);
}
// Test Maps.Restrict(block#286264) covers block 286257
// Test Maps.Restrict(block#286264) covers block 286264
// Extracting the test for Maps.Restrict(block#286264) from the counterexample...
method {:test} test11() {
var d0 : map<int, int> := map[];
var d1 : set<int> := {};
var r0 := Maps.Restrict<int,int>(d0, d1);
expect r0 == Maps.RemoveKeys(d0, d0.Keys - d1);
}
// Test Maps.Restrict(block#286263) covers block 286257
// Test Maps.Restrict(block#286263) covers block 286258
// Test Maps.Restrict(block#286263) covers block 286259
// Test Maps.Restrict(block#286263) covers block 286263
// Extracting the test for Maps.Restrict(block#286263) from the counterexample...
method {:test} test12() {
var d0 : map<int, int> := map[];
var d1 : set<int> := {0};
var r0 := Maps.Restrict<int,int>(d0, d1);
expect r0 == Maps.RemoveKeys(d0, d0.Keys - d1);
}
// Test Maps.Restrict(block#286260) covers block 286257
// Test Maps.Restrict(block#286260) covers block 286258
// Test Maps.Restrict(block#286260) covers block 286260
// Extracting the test for Maps.Restrict(block#286260) from the counterexample...
// Test for Maps.Restrict(block#286260) matches a test previously generated for Maps.Restrict(block#286264).
// Test Maps.Union(block#288894) covers block 288894
// Extracting the test for Maps.Union(block#288894) from the counterexample...
method {:test} test14() {
var d0 : map<int, int> := map[];
var d1 : map<int, int> := map[];
var r0 := Maps.Union<int,int>(d0, d1);
expect r0.Keys == d0.Keys + d1.Keys;
}

}
