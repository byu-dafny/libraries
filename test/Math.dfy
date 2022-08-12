include "..//src/Math.dfy"
module srcMathdfyUnitTests {
import Math
// Merging boogie files...
// Converting function calls to method calls...
// Adding Impl$$ methods to support inlining...
// Removing assertions...
// Annotating blocks...
// Generating modifications...
// Test Math.Min(block#146979) covers block 146976
// Test Math.Min(block#146979) covers block 146977
// Test Math.Min(block#146979) covers block 146979
// Extracting the test for Math.Min(block#146979) from the counterexample...
method {:test} test0() {
var r0 := Math.Min(7719, 7720);
}
// Test Math.Min(block#146978) covers block 146976
// Test Math.Min(block#146978) covers block 146978
// Extracting the test for Math.Min(block#146978) from the counterexample...
method {:test} test1() {
var r0 := Math.Min(0, 0);
}
// Test Math.Max(block#147323) covers block 147320
// Test Math.Max(block#147323) covers block 147321
// Test Math.Max(block#147323) covers block 147323
// Extracting the test for Math.Max(block#147323) from the counterexample...
method {:test} test2() {
var r0 := Math.Max(0, 1);
}
// Test Math.Max(block#147322) covers block 147320
// Test Math.Max(block#147322) covers block 147322
// Extracting the test for Math.Max(block#147322) from the counterexample...
method {:test} test3() {
var r0 := Math.Max(0, 0);
}

}
