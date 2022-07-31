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
// Test Sets.Map(block#242437) covers block 242432
// Test Sets.Map(block#242437) covers block 242433
// Test Sets.Map(block#242437) covers block 242434
// Test Sets.Map(block#242437) covers block 242437
// Extracting the test for Sets.Map(block#242437) from the counterexample...
/*method {:test} test0() {
var d0 : set<int> := {0, 1, 2};
var r0 := Sets.Map<int,int>(d0, (a0:int)=>0);
expect |d0| == |r0|;
}*/
// Test Sets.Map(block#242436) covers block 242432
// Test Sets.Map(block#242436) covers block 242436
// Extracting the test for Sets.Map(block#242436) from the counterexample...
method {:test} test1() {
var d0 : set<int> := {};
var r0 := Sets.Map<int,int>(d0, (a0:int)=>0);
expect |d0| == |r0|;
}
// Test Sets.Map(block#242435) covers block 242432
// Test Sets.Map(block#242435) covers block 242433
// Test Sets.Map(block#242435) covers block 242435
// Extracting the test for Sets.Map(block#242435) from the counterexample...
// Test for Sets.Map(block#242435) matches a test previously generated for Sets.Map(block#242436).
// Test Sets.Filter(block#245712) covers block 245704
// Test Sets.Filter(block#245712) covers block 245705
// Test Sets.Filter(block#245712) covers block 245706
// Test Sets.Filter(block#245712) covers block 245709
// Test Sets.Filter(block#245712) covers block 245712
// Extracting the test for Sets.Filter(block#245712) from the counterexample...
method {:test} test3() {
var d0 : set<int> := {0, 1, 2};
var r0 := Sets.Filter<int>(d0, (a0:int)=>false);
expect |r0| <= |d0|;
}
// Test Sets.Filter(block#245711) covers block 245704
// Test Sets.Filter(block#245711) covers block 245711
// Extracting the test for Sets.Filter(block#245711) from the counterexample...
method {:test} test4() {
var d0 : set<int> := {};
var r0 := Sets.Filter<int>(d0, (a0:int)=>false);
expect |r0| <= |d0|;
}
// Test Sets.Filter(block#245710) covers block 245704
// Test Sets.Filter(block#245710) covers block 245705
// Test Sets.Filter(block#245710) covers block 245706
// Test Sets.Filter(block#245710) covers block 245710
// Extracting the test for Sets.Filter(block#245710) from the counterexample...
method {:test} test5() {
var d0 : set<int> := {0};
var r0 := Sets.Filter<int>(d0, (a0:int)=>false);
expect |r0| <= |d0|;
}
// Test Sets.Filter(block#245707) covers block 245704
// Test Sets.Filter(block#245707) covers block 245705
// Test Sets.Filter(block#245707) covers block 245707
// Extracting the test for Sets.Filter(block#245707) from the counterexample...
// Test for Sets.Filter(block#245707) matches a test previously generated for Sets.Filter(block#245711).
// Test Sets.SetRange(block#247594) covers block 247591
// Test Sets.SetRange(block#247594) covers block 247593
// Test Sets.SetRange(block#247594) covers block 247594
// Extracting the test for Sets.SetRange(block#247594) from the counterexample...
method {:test} test7() {
var r0 := Sets.SetRange(2437, 2438);
expect |r0| == 2438 - 2437;
}
// Test Sets.SetRange(block#247592) covers block 247591
// Test Sets.SetRange(block#247592) covers block 247592
// Extracting the test for Sets.SetRange(block#247592) from the counterexample...
method {:test} test8() {
var r0 := Sets.SetRange(15, 15);
expect |r0| == 15 - 15;
}
// Test Sets.SetRangeZeroBound(block#248563) covers block 248563
// Extracting the test for Sets.SetRangeZeroBound(block#248563) from the counterexample...
method {:test} test9() {
var r0 := Sets.SetRangeZeroBound(1);
expect |r0| == 1;
}

}
