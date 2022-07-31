include "..//src/Wrappers.dfy"
module srcWrappersdfyUnitTests {
import Wrappers
// Merging boogie files...
// Converting function calls to method calls...
// Adding Impl$$ methods to support inlining...
// Removing assertions...
// Annotating blocks...
// Generating modifications...
// Test Wrappers.Option.ToResult(block#212140) covers block 212135
// Test Wrappers.Option.ToResult(block#212140) covers block 212136
// Test Wrappers.Option.ToResult(block#212140) covers block 212140
// Extracting the test for Wrappers.Option.ToResult(block#212140) from the counterexample...
method {:test} test0() {
var d0 : Wrappers.Option<int> := Wrappers.Option<int>.Some(value:=0);
var r0 := d0.ToResult();
}
// No test can be generated for Wrappers.Option.ToResult(block#212139) because the verifier suceeded.
// Test Wrappers.Option.ToResult(block#212138) covers block 212135
// Test Wrappers.Option.ToResult(block#212138) covers block 212137
// Test Wrappers.Option.ToResult(block#212138) covers block 212138
// Extracting the test for Wrappers.Option.ToResult(block#212138) from the counterexample...
// Test for Wrappers.Option.ToResult(block#212138) matches a test previously generated for Wrappers.Option.ToResult(block#212140).
// Test Wrappers.Option.UnwrapOr(block#212800) covers block 212795
// Test Wrappers.Option.UnwrapOr(block#212800) covers block 212796
// Test Wrappers.Option.UnwrapOr(block#212800) covers block 212800
// Extracting the test for Wrappers.Option.UnwrapOr(block#212800) from the counterexample...
method {:test} test2() {
var d0 : Wrappers.Option<int> := Wrappers.Option<int>.Some(value:=0);
var r0 := d0.UnwrapOr(1);
}
// No test can be generated for Wrappers.Option.UnwrapOr(block#212799) because the verifier suceeded.
// Test Wrappers.Option.UnwrapOr(block#212798) covers block 212795
// Test Wrappers.Option.UnwrapOr(block#212798) covers block 212797
// Test Wrappers.Option.UnwrapOr(block#212798) covers block 212798
// Extracting the test for Wrappers.Option.UnwrapOr(block#212798) from the counterexample...
// Test for Wrappers.Option.UnwrapOr(block#212798) matches a test previously generated for Wrappers.Option.UnwrapOr(block#212800).
// Test Wrappers.Option.IsFailure(block#213173) covers block 213173
// Extracting the test for Wrappers.Option.IsFailure(block#213173) from the counterexample...
method {:test} test4() {
var d0 : Wrappers.Option<int> := Wrappers.Option<int>.Some(value:=0);
var r0 := d0.IsFailure();
}
// Test Wrappers.Option.PropagateFailure(block#213649) covers block 213649
// Extracting the test for Wrappers.Option.PropagateFailure(block#213649) from the counterexample...
method {:test} test5() {
var d0 : Wrappers.Option<int> := Wrappers.Option<int>.None;
var r0 := d0.PropagateFailure<int>();
}
// Test Wrappers.Option.Extract(block#214173) covers block 214173
// Extracting the test for Wrappers.Option.Extract(block#214173) from the counterexample...
method {:test} test6() {
var d0 : Wrappers.Option<int> := Wrappers.Option<int>.Some(value:=0);
var r0 := d0.Extract();
}
// Test Wrappers.Result.ToOption(block#215569) covers block 215564
// Test Wrappers.Result.ToOption(block#215569) covers block 215565
// Test Wrappers.Result.ToOption(block#215569) covers block 215569
// Extracting the test for Wrappers.Result.ToOption(block#215569) from the counterexample...
method {:test} test7() {
var d0 : Wrappers.Result<int, int> := Wrappers.Result<int, int>.Success(value:=0);
var r0 := d0.ToOption();
}
// No test can be generated for Wrappers.Result.ToOption(block#215568) because the verifier suceeded.
// Test Wrappers.Result.ToOption(block#215567) covers block 215564
// Test Wrappers.Result.ToOption(block#215567) covers block 215566
// Test Wrappers.Result.ToOption(block#215567) covers block 215567
// Extracting the test for Wrappers.Result.ToOption(block#215567) from the counterexample...
method {:test} test8() {
var d0 : Wrappers.Result<int, int> := Wrappers.Result<int, int>.Failure(error:=0);
var r0 := d0.ToOption();
}
// Test Wrappers.Result.UnwrapOr(block#216367) covers block 216362
// Test Wrappers.Result.UnwrapOr(block#216367) covers block 216363
// Test Wrappers.Result.UnwrapOr(block#216367) covers block 216367
// Extracting the test for Wrappers.Result.UnwrapOr(block#216367) from the counterexample...
method {:test} test9() {
var d0 : Wrappers.Result<int, int> := Wrappers.Result<int, int>.Success(value:=0);
var r0 := d0.UnwrapOr(1);
}
// No test can be generated for Wrappers.Result.UnwrapOr(block#216366) because the verifier suceeded.
// Test Wrappers.Result.UnwrapOr(block#216365) covers block 216362
// Test Wrappers.Result.UnwrapOr(block#216365) covers block 216364
// Test Wrappers.Result.UnwrapOr(block#216365) covers block 216365
// Extracting the test for Wrappers.Result.UnwrapOr(block#216365) from the counterexample...
method {:test} test10() {
var d0 : Wrappers.Result<int, int> := Wrappers.Result<int, int>.Failure(error:=0);
var r0 := d0.UnwrapOr(1);
}
// Test Wrappers.Result.IsFailure(block#216792) covers block 216792
// Extracting the test for Wrappers.Result.IsFailure(block#216792) from the counterexample...
method {:test} test11() {
var d0 : Wrappers.Result<int, int> := Wrappers.Result<int, int>.Success(value:=0);
var r0 := d0.IsFailure();
}
// Test Wrappers.Result.PropagateFailure(block#217465) covers block 217465
// Extracting the test for Wrappers.Result.PropagateFailure(block#217465) from the counterexample...
method {:test} test12() {
var d0 : Wrappers.Result<int, int> := Wrappers.Result<int, int>.Failure(error:=0);
var r0 := d0.PropagateFailure<int>();
}
// Test Wrappers.Result.MapFailure(block#218482) covers block 218477
// Test Wrappers.Result.MapFailure(block#218482) covers block 218478
// Test Wrappers.Result.MapFailure(block#218482) covers block 218482
// Extracting the test for Wrappers.Result.MapFailure(block#218482) from the counterexample...
method {:test} test13() {
var d0 : Wrappers.Result<int, int> := Wrappers.Result<int, int>.Success(value:=0);
var r0 := d0.MapFailure<int>((a0:int)=>0);
}
// No test can be generated for Wrappers.Result.MapFailure(block#218481) because the verifier suceeded.
// Test Wrappers.Result.MapFailure(block#218480) covers block 218477
// Test Wrappers.Result.MapFailure(block#218480) covers block 218479
// Test Wrappers.Result.MapFailure(block#218480) covers block 218480
// Extracting the test for Wrappers.Result.MapFailure(block#218480) from the counterexample...
method {:test} test14() {
var d0 : Wrappers.Result<int, int> := Wrappers.Result<int, int>.Failure(error:=0);
var r0 := d0.MapFailure<int>((a0:int)=>0);
}
// Test Wrappers.Result.Extract(block#219065) covers block 219065
// Extracting the test for Wrappers.Result.Extract(block#219065) from the counterexample...
method {:test} test15() {
var d0 : Wrappers.Result<int, int> := Wrappers.Result<int, int>.Success(value:=0);
var r0 := d0.Extract();
}
// Test Wrappers.Outcome.IsFailure(block#220083) covers block 220083
// Extracting the test for Wrappers.Outcome.IsFailure(block#220083) from the counterexample...
method {:test} test16() {
var d0 : Wrappers.Outcome<int> := Wrappers.Outcome<int>.Pass;
var r0 := d0.IsFailure();
}
// Test Wrappers.Outcome.PropagateFailure(block#220696) covers block 220696
// Extracting the test for Wrappers.Outcome.PropagateFailure(block#220696) from the counterexample...
method {:test} test17() {
var d0 : Wrappers.Outcome<int> := Wrappers.Outcome<int>.Fail(error:=0);
var r0 := d0.PropagateFailure<int>();
}
// Test Wrappers.Need(block#221342) covers block 221339
// Test Wrappers.Need(block#221342) covers block 221340
// Test Wrappers.Need(block#221342) covers block 221342
// Extracting the test for Wrappers.Need(block#221342) from the counterexample...
method {:test} test18() {
var r0 := Wrappers.Need<int>(true, 0);
}
// Test Wrappers.Need(block#221341) covers block 221339
// Test Wrappers.Need(block#221341) covers block 221341
// Extracting the test for Wrappers.Need(block#221341) from the counterexample...
method {:test} test19() {
var r0 := Wrappers.Need<int>(false, 0);
}

}
