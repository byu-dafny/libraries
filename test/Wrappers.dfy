include "..//src/Wrappers.dfy"
module srcWrappersdfyUnitTests {
import Wrappers
// Merging boogie files...
// Converting function calls to method calls...
// Adding Impl$$ methods to support inlining...
// Removing assertions...
// Annotating blocks...
// Generating modifications...
// Test Wrappers.Option.ToResult(block#203114) covers block 203109
// Test Wrappers.Option.ToResult(block#203114) covers block 203110
// Test Wrappers.Option.ToResult(block#203114) covers block 203114
// Extracting the test for Wrappers.Option.ToResult(block#203114) from the counterexample...
method {:test} test0() {
var d0 : Wrappers.Option<int> := Wrappers.Option<int>.Some(value:=0);
var r0 := d0.ToResult();
}
// No test can be generated for Wrappers.Option.ToResult(block#203113) because the verifier suceeded.
// Test Wrappers.Option.ToResult(block#203112) covers block 203109
// Test Wrappers.Option.ToResult(block#203112) covers block 203111
// Test Wrappers.Option.ToResult(block#203112) covers block 203112
// Extracting the test for Wrappers.Option.ToResult(block#203112) from the counterexample...
// Test for Wrappers.Option.ToResult(block#203112) matches a test previously generated for Wrappers.Option.ToResult(block#203114).
// Test Wrappers.Option.UnwrapOr(block#203774) covers block 203769
// Test Wrappers.Option.UnwrapOr(block#203774) covers block 203770
// Test Wrappers.Option.UnwrapOr(block#203774) covers block 203774
// Extracting the test for Wrappers.Option.UnwrapOr(block#203774) from the counterexample...
method {:test} test2() {
var d0 : Wrappers.Option<int> := Wrappers.Option<int>.Some(value:=0);
var r0 := d0.UnwrapOr(1);
}
// No test can be generated for Wrappers.Option.UnwrapOr(block#203773) because the verifier suceeded.
// Test Wrappers.Option.UnwrapOr(block#203772) covers block 203769
// Test Wrappers.Option.UnwrapOr(block#203772) covers block 203771
// Test Wrappers.Option.UnwrapOr(block#203772) covers block 203772
// Extracting the test for Wrappers.Option.UnwrapOr(block#203772) from the counterexample...
// Test for Wrappers.Option.UnwrapOr(block#203772) matches a test previously generated for Wrappers.Option.UnwrapOr(block#203774).
// Test Wrappers.Option.IsFailure(block#204147) covers block 204147
// Extracting the test for Wrappers.Option.IsFailure(block#204147) from the counterexample...
method {:test} test4() {
var d0 : Wrappers.Option<int> := Wrappers.Option<int>.Some(value:=0);
var r0 := d0.IsFailure();
}
// Test Wrappers.Option.PropagateFailure(block#204623) covers block 204623
// Extracting the test for Wrappers.Option.PropagateFailure(block#204623) from the counterexample...
method {:test} test5() {
var d0 : Wrappers.Option<int> := Wrappers.Option<int>.None;
expect d0.None?, "Test does not meet preconditions and should be removed";
var r0 := d0.PropagateFailure<int>();
}
// Test Wrappers.Option.Extract(block#205147) covers block 205147
// Extracting the test for Wrappers.Option.Extract(block#205147) from the counterexample...
method {:test} test6() {
var d0 : Wrappers.Option<int> := Wrappers.Option<int>.Some(value:=0);
expect d0.Some?, "Test does not meet preconditions and should be removed";
var r0 := d0.Extract();
}
// Test Wrappers.Result.ToOption(block#206543) covers block 206538
// Test Wrappers.Result.ToOption(block#206543) covers block 206539
// Test Wrappers.Result.ToOption(block#206543) covers block 206543
// Extracting the test for Wrappers.Result.ToOption(block#206543) from the counterexample...
method {:test} test7() {
var d0 : Wrappers.Result<int, int> := Wrappers.Result<int, int>.Success(value:=0);
var r0 := d0.ToOption();
}
// No test can be generated for Wrappers.Result.ToOption(block#206542) because the verifier suceeded.
// Test Wrappers.Result.ToOption(block#206541) covers block 206538
// Test Wrappers.Result.ToOption(block#206541) covers block 206540
// Test Wrappers.Result.ToOption(block#206541) covers block 206541
// Extracting the test for Wrappers.Result.ToOption(block#206541) from the counterexample...
method {:test} test8() {
var d0 : Wrappers.Result<int, int> := Wrappers.Result<int, int>.Failure(error:=0);
var r0 := d0.ToOption();
}
// Test Wrappers.Result.UnwrapOr(block#207341) covers block 207336
// Test Wrappers.Result.UnwrapOr(block#207341) covers block 207337
// Test Wrappers.Result.UnwrapOr(block#207341) covers block 207341
// Extracting the test for Wrappers.Result.UnwrapOr(block#207341) from the counterexample...
method {:test} test9() {
var d0 : Wrappers.Result<int, int> := Wrappers.Result<int, int>.Success(value:=0);
var r0 := d0.UnwrapOr(1);
}
// No test can be generated for Wrappers.Result.UnwrapOr(block#207340) because the verifier suceeded.
// Test Wrappers.Result.UnwrapOr(block#207339) covers block 207336
// Test Wrappers.Result.UnwrapOr(block#207339) covers block 207338
// Test Wrappers.Result.UnwrapOr(block#207339) covers block 207339
// Extracting the test for Wrappers.Result.UnwrapOr(block#207339) from the counterexample...
method {:test} test10() {
var d0 : Wrappers.Result<int, int> := Wrappers.Result<int, int>.Failure(error:=0);
var r0 := d0.UnwrapOr(1);
}
// Test Wrappers.Result.IsFailure(block#207766) covers block 207766
// Extracting the test for Wrappers.Result.IsFailure(block#207766) from the counterexample...
method {:test} test11() {
var d0 : Wrappers.Result<int, int> := Wrappers.Result<int, int>.Success(value:=0);
var r0 := d0.IsFailure();
}
// Test Wrappers.Result.PropagateFailure(block#208439) covers block 208439
// Extracting the test for Wrappers.Result.PropagateFailure(block#208439) from the counterexample...
method {:test} test12() {
var d0 : Wrappers.Result<int, int> := Wrappers.Result<int, int>.Failure(error:=0);
expect d0.Failure?, "Test does not meet preconditions and should be removed";
var r0 := d0.PropagateFailure<int>();
}
// Test Wrappers.Result.MapFailure(block#209456) covers block 209451
// Test Wrappers.Result.MapFailure(block#209456) covers block 209452
// Test Wrappers.Result.MapFailure(block#209456) covers block 209456
// Extracting the test for Wrappers.Result.MapFailure(block#209456) from the counterexample...
method {:test} test13() {
var d0 : Wrappers.Result<int, int> := Wrappers.Result<int, int>.Success(value:=0);
var r0 := d0.MapFailure<int>((a0:int)=>0);
}
// No test can be generated for Wrappers.Result.MapFailure(block#209455) because the verifier suceeded.
// Test Wrappers.Result.MapFailure(block#209454) covers block 209451
// Test Wrappers.Result.MapFailure(block#209454) covers block 209453
// Test Wrappers.Result.MapFailure(block#209454) covers block 209454
// Extracting the test for Wrappers.Result.MapFailure(block#209454) from the counterexample...
method {:test} test14() {
var d0 : Wrappers.Result<int, int> := Wrappers.Result<int, int>.Failure(error:=0);
var r0 := d0.MapFailure<int>((a0:int)=>0);
}
// Test Wrappers.Result.Extract(block#210039) covers block 210039
// Extracting the test for Wrappers.Result.Extract(block#210039) from the counterexample...
method {:test} test15() {
var d0 : Wrappers.Result<int, int> := Wrappers.Result<int, int>.Success(value:=0);
expect d0.Success?, "Test does not meet preconditions and should be removed";
var r0 := d0.Extract();
}
// Test Wrappers.Outcome.IsFailure(block#211057) covers block 211057
// Extracting the test for Wrappers.Outcome.IsFailure(block#211057) from the counterexample...
method {:test} test16() {
var d0 : Wrappers.Outcome<int> := Wrappers.Outcome<int>.Pass;
var r0 := d0.IsFailure();
}
// Test Wrappers.Outcome.PropagateFailure(block#211670) covers block 211670
// Extracting the test for Wrappers.Outcome.PropagateFailure(block#211670) from the counterexample...
method {:test} test17() {
var d0 : Wrappers.Outcome<int> := Wrappers.Outcome<int>.Fail(error:=0);
expect d0.Fail?, "Test does not meet preconditions and should be removed";
var r0 := d0.PropagateFailure<int>();
}
// Test Wrappers.Need(block#212316) covers block 212313
// Test Wrappers.Need(block#212316) covers block 212314
// Test Wrappers.Need(block#212316) covers block 212316
// Extracting the test for Wrappers.Need(block#212316) from the counterexample...
method {:test} test18() {
var r0 := Wrappers.Need<int>(true, 0);
}
// Test Wrappers.Need(block#212315) covers block 212313
// Test Wrappers.Need(block#212315) covers block 212315
// Extracting the test for Wrappers.Need(block#212315) from the counterexample...
method {:test} test19() {
var r0 := Wrappers.Need<int>(false, 0);
}

}
