include "../src//Wrappers.dfy"
module WrappersUnitTests {
import Wrappers
method {:test} test0() {
var d0 : Wrappers.Outcome<int> := Wrappers.Outcome<int>.Pass;
var r0 := d0.IsFailure();
}
method {:test} test1() {
var d0 : Wrappers.Result<int, int> := Wrappers.Result<int, int>.Success(value:=0);
var r0 := d0.Extract();
}
method {:test} test2() {
var d0 : Wrappers.Result<int, int> := Wrappers.Result<int, int>.Success(value:=0);
var r0 := d0.MapFailure<int>((a0:int)=>0);
}
method {:test} test4() {
var d0 : Wrappers.Result<int, int> := Wrappers.Result<int, int>.Success(value:=0);
var r0 := d0.IsFailure();
}
method {:test} test5() {
var d0 : Wrappers.Result<int, int> := Wrappers.Result<int, int>.Success(value:=0);
var r0 := d0.UnwrapOr(1);
}
method {:test} test6() {
var d0 : Wrappers.Result<int, int> := Wrappers.Result<int, int>.Success(value:=0);
var r0 := d0.UnwrapOr(0);
}
method {:test} test7() {
var d0 : Wrappers.Result<int, int> := Wrappers.Result<int, int>.Success(value:=0);
var r0 := d0.ToOption();
}
method {:test} test9() {
var d0 : Wrappers.Option<int> := Wrappers.Option<int>.Some(value:=0);
var r0 := d0.Extract();
}
method {:test} test10() {
var d0 : Wrappers.Option<int> := Wrappers.Option<int>.None;
var r0 := d0.PropagateFailure<int>();
}
method {:test} test11() {
var d0 : Wrappers.Option<int> := Wrappers.Option<int>.Some(value:=0);
var r0 := d0.IsFailure();
}
method {:test} test12() {
var d0 : Wrappers.Option<int> := Wrappers.Option<int>.Some(value:=0);
var r0 := d0.UnwrapOr(1);
}
method {:test} test14() {
var d0 : Wrappers.Option<int> := Wrappers.Option<int>.Some(value:=0);
var r0 := d0.ToResult();
}

}
