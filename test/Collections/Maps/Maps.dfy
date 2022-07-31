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
// Test Maps.Get(block#312790) covers block 312787
// Test Maps.Get(block#312790) covers block 312788
// Test Maps.Get(block#312790) covers block 312790
// Extracting the test for Maps.Get(block#312790) from the counterexample...
method {:test} test0() {
var d0 : map<int, int> := map[0 := 1, 2 := 3, 4 := 5, 6 := 7];
var r0 := Maps.Get<int,int>(d0, 0);
}
// Test Maps.Get(block#312789) covers block 312787
// Test Maps.Get(block#312789) covers block 312789
// Extracting the test for Maps.Get(block#312789) from the counterexample...
method {:test} test1() {
var d0 : map<int, int> := map[];
var r0 := Maps.Get<int,int>(d0, 0);
}
// Test Maps.ToImap(block#314354) covers block 314349
// Test Maps.ToImap(block#314354) covers block 314350
// Test Maps.ToImap(block#314354) covers block 314351
// Test Maps.ToImap(block#314354) covers block 314354
// Extracting the test for Maps.ToImap(block#314354) from the counterexample...
method {:test} test2() {
var d0 : map<int, int> := map[0 := 1, 2 := 3, 4 := 5, 6 := 7];
var r0 := Maps.ToImap<int,int>(d0);
}
// Test Maps.ToImap(block#314353) covers block 314349
// Test Maps.ToImap(block#314353) covers block 314353
// Extracting the test for Maps.ToImap(block#314353) from the counterexample...
method {:test} test3() {
var d0 : map<int, int> := map[];
var r0 := Maps.ToImap<int,int>(d0);
}
// Test Maps.ToImap(block#314352) covers block 314349
// Test Maps.ToImap(block#314352) covers block 314350
// Test Maps.ToImap(block#314352) covers block 314352
// Extracting the test for Maps.ToImap(block#314352) from the counterexample...
// Test for Maps.ToImap(block#314352) matches a test previously generated for Maps.ToImap(block#314353).
// Test Maps.RemoveKeys(block#315961) covers block 315961
// Extracting the test for Maps.RemoveKeys(block#315961) from the counterexample...
method {:test} test5() {
var d0 : map<int, int> := map[];
var d1 : set<int> := {};
var r0 := Maps.RemoveKeys<int,int>(d0, d1);
expect r0.Keys == d0.Keys - d1;
}
// Test Maps.Remove(block#317933) covers block 317925
// Test Maps.Remove(block#317933) covers block 317926
// Test Maps.Remove(block#317933) covers block 317927
// Test Maps.Remove(block#317933) covers block 317930
// Test Maps.Remove(block#317933) covers block 317933
// Extracting the test for Maps.Remove(block#317933) from the counterexample...
method {:test} test6() {
var d0 : map<int, int> := map[0 := 1, 2 := 3, 4 := 5, 6 := 7];
var r0 := Maps.Remove<int,int>(d0, 8);
expect r0 == Maps.RemoveKeys(d0, {8});
expect |r0.Keys| <= |d0.Keys|;
expect 8 in d0 ==> |r0| == |d0| - 1;
expect 8 !in d0 ==> |r0| == |d0|;
}
// Test Maps.Remove(block#317932) covers block 317925
// Test Maps.Remove(block#317932) covers block 317932
// Extracting the test for Maps.Remove(block#317932) from the counterexample...
method {:test} test7() {
var d0 : map<int, int> := map[];
var r0 := Maps.Remove<int,int>(d0, 0);
expect r0 == Maps.RemoveKeys(d0, {0});
expect |r0.Keys| <= |d0.Keys|;
expect 0 in d0 ==> |r0| == |d0| - 1;
expect 0 !in d0 ==> |r0| == |d0|;
}
// Test Maps.Remove(block#317931) covers block 317925
// Test Maps.Remove(block#317931) covers block 317926
// Test Maps.Remove(block#317931) covers block 317927
// Test Maps.Remove(block#317931) covers block 317931
// Extracting the test for Maps.Remove(block#317931) from the counterexample...
method {:test} test8() {
var d0 : map<int, int> := map[0 := 1, 2 := 3, 4 := 5, 6 := 7];
var r0 := Maps.Remove<int,int>(d0, 6);
expect r0 == Maps.RemoveKeys(d0, {6});
expect |r0.Keys| <= |d0.Keys|;
expect 6 in d0 ==> |r0| == |d0| - 1;
expect 6 !in d0 ==> |r0| == |d0|;
}
// Test Maps.Remove(block#317928) covers block 317925
// Test Maps.Remove(block#317928) covers block 317926
// Test Maps.Remove(block#317928) covers block 317928
// Extracting the test for Maps.Remove(block#317928) from the counterexample...
// Test for Maps.Remove(block#317928) matches a test previously generated for Maps.Remove(block#317932).
// Test Maps.Restrict(block#319432) covers block 319424
// Test Maps.Restrict(block#319432) covers block 319425
// Test Maps.Restrict(block#319432) covers block 319426
// Test Maps.Restrict(block#319432) covers block 319429
// Test Maps.Restrict(block#319432) covers block 319432
// Extracting the test for Maps.Restrict(block#319432) from the counterexample...
method {:test} test10() {
var d0 : map<int, int> := map[0 := 1, 2 := 3, 4 := 5, 6 := 7];
var d1 : set<int> := {0};
var r0 := Maps.Restrict<int,int>(d0, d1);
expect r0 == Maps.RemoveKeys(d0, d0.Keys - d1);
}
// Test Maps.Restrict(block#319431) covers block 319424
// Test Maps.Restrict(block#319431) covers block 319431
// Extracting the test for Maps.Restrict(block#319431) from the counterexample...
method {:test} test11() {
var d0 : map<int, int> := map[];
var d1 : set<int> := {};
var r0 := Maps.Restrict<int,int>(d0, d1);
expect r0 == Maps.RemoveKeys(d0, d0.Keys - d1);
}
// Test Maps.Restrict(block#319430) covers block 319424
// Test Maps.Restrict(block#319430) covers block 319425
// Test Maps.Restrict(block#319430) covers block 319426
// Test Maps.Restrict(block#319430) covers block 319430
// Extracting the test for Maps.Restrict(block#319430) from the counterexample...
method {:test} test12() {
var d0 : map<int, int> := map[];
var d1 : set<int> := {0};
var r0 := Maps.Restrict<int,int>(d0, d1);
expect r0 == Maps.RemoveKeys(d0, d0.Keys - d1);
}
// Test Maps.Restrict(block#319427) covers block 319424
// Test Maps.Restrict(block#319427) covers block 319425
// Test Maps.Restrict(block#319427) covers block 319427
// Extracting the test for Maps.Restrict(block#319427) from the counterexample...
// Test for Maps.Restrict(block#319427) matches a test previously generated for Maps.Restrict(block#319431).
// Test Maps.Union(block#322564) covers block 322564
// Extracting the test for Maps.Union(block#322564) from the counterexample...
method {:test} test14() {
var d0 : map<int, int> := map[];
var d1 : map<int, int> := map[];
var r0 := Maps.Union<int,int>(d0, d1);
expect r0.Keys == d0.Keys + d1.Keys;
}

}
