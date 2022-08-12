include "../../..//src/Collections/Sets/Sets.dfy"
module srcCollectionsSetsSetsdfyUnitTests {
import Sets
import Functions
// Merging boogie files...
// Converting function calls to method calls...
// Adding Impl$$ methods to support inlining...
// Removing assertions...
// Annotating blocks...
// Generating modifications...
// Test Sets.Map(block#223439) covers block 223434
// Test Sets.Map(block#223439) covers block 223435
// Test Sets.Map(block#223439) covers block 223436
// Test Sets.Map(block#223439) covers block 223439
// Extracting the test for Sets.Map(block#223439) from the counterexample...
/*method {:test} test0() {
var d0 : set<int> := {0, 1, 2};
var r0 := Sets.Map<int,int>(d0, (a0:int)=>0);
expect |d0| == |r0|;
}*/
// Test Sets.Map(block#223438) covers block 223434
// Test Sets.Map(block#223438) covers block 223438
// Extracting the test for Sets.Map(block#223438) from the counterexample...
method {:test} test1() {
var d0 : set<int> := {};
var r0 := Sets.Map<int,int>(d0, (a0:int)=>0);
expect |d0| == |r0|;
}
// Test Sets.Map(block#223437) covers block 223434
// Test Sets.Map(block#223437) covers block 223435
// Test Sets.Map(block#223437) covers block 223437
// Extracting the test for Sets.Map(block#223437) from the counterexample...
// Test for Sets.Map(block#223437) matches a test previously generated for Sets.Map(block#223438).
// Test Sets.Filter(block#226391) covers block 226383
// Test Sets.Filter(block#226391) covers block 226384
// Test Sets.Filter(block#226391) covers block 226385
// Test Sets.Filter(block#226391) covers block 226388
// Test Sets.Filter(block#226391) covers block 226391
// Extracting the test for Sets.Filter(block#226391) from the counterexample...
method {:test} test3() {
var d0 : set<int> := {0, 1, 2};
var r0 := Sets.Filter<int>(d0, (a0:int)=>false);
expect |r0| <= |d0|;
}
// Test Sets.Filter(block#226390) covers block 226383
// Test Sets.Filter(block#226390) covers block 226390
// Extracting the test for Sets.Filter(block#226390) from the counterexample...
method {:test} test4() {
var d0 : set<int> := {};
var r0 := Sets.Filter<int>(d0, (a0:int)=>false);
expect |r0| <= |d0|;
}
// Test Sets.Filter(block#226389) covers block 226383
// Test Sets.Filter(block#226389) covers block 226384
// Test Sets.Filter(block#226389) covers block 226385
// Test Sets.Filter(block#226389) covers block 226389
// Extracting the test for Sets.Filter(block#226389) from the counterexample...
method {:test} test5() {
var d0 : set<int> := {0};
var r0 := Sets.Filter<int>(d0, (a0:int)=>false);
expect |r0| <= |d0|;
}
// Test Sets.Filter(block#226386) covers block 226383
// Test Sets.Filter(block#226386) covers block 226384
// Test Sets.Filter(block#226386) covers block 226386
// Extracting the test for Sets.Filter(block#226386) from the counterexample...
// Test for Sets.Filter(block#226386) matches a test previously generated for Sets.Filter(block#226390).
// Test Sets.SetRange(block#228143) covers block 228140
// Test Sets.SetRange(block#228143) covers block 228142
// Test Sets.SetRange(block#228143) covers block 228143
// Extracting the test for Sets.SetRange(block#228143) from the counterexample...
method {:test} test7() {
expect 2275 <= 2279, "Test does not meet preconditions and should be removed";
var r0 := Sets.SetRange(2275, 2279);
expect |r0| == 2279 - 2275;
}
// Test Sets.SetRange(block#228141) covers block 228140
// Test Sets.SetRange(block#228141) covers block 228141
// Extracting the test for Sets.SetRange(block#228141) from the counterexample...
method {:test} test8() {
expect 7719 <= 7719, "Test does not meet preconditions and should be removed";
var r0 := Sets.SetRange(7719, 7719);
expect |r0| == 7719 - 7719;
}
// Test Sets.SetRangeZeroBound(block#228927) covers block 228927
// Extracting the test for Sets.SetRangeZeroBound(block#228927) from the counterexample...
method {:test} test9() {
expect 3 >= 0, "Test does not meet preconditions and should be removed";
var r0 := Sets.SetRangeZeroBound(3);
expect |r0| == 3;
}

}
