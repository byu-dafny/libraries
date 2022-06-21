include "../src//Collections/Maps/Maps.dfy"
module MapsUnitTests {
import Maps
import Wrappers
method {:test} test0() {
var r0 := Maps.Union<int,int>(map[], map[]);
}
method {:test} test1() {
var r0 := Maps.Restrict<int,int>(map[0 := 1, 2 := 3, 4 := 5, 6 := 7], {0});
}
method {:test} test2() {
var r0 := Maps.Restrict<int,int>(map[], {});
}
method {:test} test3() {
var r0 := Maps.Restrict<int,int>(map[], {0});
}
method {:test} test5() {
var r0 := Maps.Remove<int,int>(map[0 := 1, 2 := 3, 4 := 5, 6 := 7], 8);
}
method {:test} test6() {
var r0 := Maps.Remove<int,int>(map[], 0);
}
method {:test} test7() {
var r0 := Maps.Remove<int,int>(map[0 := 1, 2 := 3, 4 := 5, 6 := 7], 6);
}
method {:test} test9() {
var r0 := Maps.RemoveKeys<int,int>(map[], {});
}
method {:test} test10() {
var r0 := Maps.ToImap<int,int>(map[0 := 1, 2 := 3, 4 := 5, 6 := 7]);
}
method {:test} test11() {
var r0 := Maps.ToImap<int,int>(map[]);
}
method {:test} test13() {
var r0 := Maps.Get<int,int>(map[0 := 1, 2 := 3, 4 := 5, 6 := 7], 0);
}
method {:test} test14() {
var r0 := Maps.Get<int,int>(map[], 0);
}

}
