include "..//src/Math.dfy"
module srcMathdfyUnitTests {
import Math
// Merging boogie files...
// Converting function calls to method calls...
// Adding Impl$$ methods to support inlining...
// Removing assertions...
// Annotating blocks...
// Generating modifications...
// Test Math.Min(block#153942) covers block 153939
// Test Math.Min(block#153942) covers block 153940
// Test Math.Min(block#153942) covers block 153942
// Extracting the test for Math.Min(block#153942) from the counterexample...
method {:test} test0() {
var r0 := Math.Min(7719, 7720);
}
// Test Math.Min(block#153941) covers block 153939
// Test Math.Min(block#153941) covers block 153941
// Extracting the test for Math.Min(block#153941) from the counterexample...
method {:test} test1() {
var r0 := Math.Min(0, 0);
}
// Test Math.Max(block#154286) covers block 154283
// Test Math.Max(block#154286) covers block 154284
// Test Math.Max(block#154286) covers block 154286
// Extracting the test for Math.Max(block#154286) from the counterexample...
method {:test} test2() {
var r0 := Math.Max(0, 1);
}
// Test Math.Max(block#154285) covers block 154283
// Test Math.Max(block#154285) covers block 154285
// Extracting the test for Math.Max(block#154285) from the counterexample...
method {:test} test3() {
var r0 := Math.Max(0, 0);
}

}
