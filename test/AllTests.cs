// Dafny program AllTests.dfy compiled into C#
// To recompile, you will need the libraries
//     System.Runtime.Numerics.dll System.Collections.Immutable.dll
// but the 'dotnet' tool in net6.0 should pick those up automatically.
// Optionally, you may want to include compiler switches like
//     /debug /nowarn:162,164,168,183,219,436,1717,1718

using System;
using System.Numerics;
using System.Collections;
[assembly: DafnyAssembly.DafnySourceAttribute(@"// Dafny 3.7.1.40621
// Command Line Options: /compileVerbose:1 /compile:0 /spillTargetCode:3 /noVerify test/AllTests.dfy
// AllTests.dfy


module AllTests {

  import srcBoundedIntsdfyUnitTests

  import srcNonlinearArithmeticInternalsDivInternalsdfyUnitTests

  import srcNonlinearArithmeticInternalsDivInternalsNonlineardfyUnitTests

  import srcNonlinearArithmeticDivModdfyUnitTests

  import srcFunctionsdfyUnitTests

  import srcNonlinearArithmeticInternalsGeneralInternalsdfyUnitTests

  import srcCollectionsMapsImapsdfyUnitTests

  import srcCollectionsSetsIsetsdfyUnitTests

  import srcCollectionsSequencesLittleEndianNatdfyUnitTests

  import srcCollectionsSequencesLittleEndianNatConversionsdfyUnitTests

  import srcCollectionsMapsMapsdfyUnitTests

  import srcMathdfyUnitTests

  import srcNonlinearArithmeticInternalsModInternalsdfyUnitTests

  import srcNonlinearArithmeticInternalsModInternalsNonlineardfyUnitTests

  import srcNonlinearArithmeticMuldfyUnitTests

  import srcNonlinearArithmeticInternalsMulInternalsdfyUnitTests

  import srcNonlinearArithmeticInternalsMulInternalsNonlineardfyUnitTests

  import srcNonlinearArithmeticPowerdfyUnitTests

  import srcNonlinearArithmeticPower2dfyUnitTests

  import srcCollectionsSequencesSeqdfyUnitTests

  import srcCollectionsSetsSetsdfyUnitTests

  import srcCollectionsSequencesUint8_16dfyUnitTests

  import srcCollectionsSequencesUint8_32dfyUnitTests

  import srcCollectionsSequencesUint8_64dfyUnitTests

  import srcCollectionsSequencesUint16_32dfyUnitTests

  import srcCollectionsSequencesUint32_64dfyUnitTests

  import srcWrappersdfyUnitTests
}

module srcWrappersdfyUnitTests {

  import Wrappers
  method {:test} test0()
  {
    var d0: Wrappers.Option<int> := Wrappers.Option<int>.Some(value := 0);
    var r0 := d0.ToResult();
  }

  method {:test} test2()
  {
    var d0: Wrappers.Option<int> := Wrappers.Option<int>.Some(value := 0);
    var r0 := d0.UnwrapOr(1);
  }

  method {:test} test4()
  {
    var d0: Wrappers.Option<int> := Wrappers.Option<int>.Some(value := 0);
    var r0 := d0.IsFailure();
  }

  method {:test} test5()
  {
    var d0: Wrappers.Option<int> := Wrappers.Option<int>.None;
    expect d0.None?, ""Test does not meet preconditions and should be removed""
    var r0 := d0.PropagateFailure<int>();
  }

  method {:test} test6()
  {
    var d0: Wrappers.Option<int> := Wrappers.Option<int>.Some(value := 0);
    expect d0.Some?, ""Test does not meet preconditions and should be removed""
    var r0 := d0.Extract();
  }

  method {:test} test7()
  {
    var d0: Wrappers.Result<int, int> := Wrappers.Result<int, int>.Success(value := 0);
    var r0 := d0.ToOption();
  }

  method {:test} test8()
  {
    var d0: Wrappers.Result<int, int> := Wrappers.Result<int, int>.Failure(error := 0);
    var r0 := d0.ToOption();
  }

  method {:test} test9()
  {
    var d0: Wrappers.Result<int, int> := Wrappers.Result<int, int>.Success(value := 0);
    var r0 := d0.UnwrapOr(1);
  }

  method {:test} test10()
  {
    var d0: Wrappers.Result<int, int> := Wrappers.Result<int, int>.Failure(error := 0);
    var r0 := d0.UnwrapOr(1);
  }

  method {:test} test11()
  {
    var d0: Wrappers.Result<int, int> := Wrappers.Result<int, int>.Success(value := 0);
    var r0 := d0.IsFailure();
  }

  method {:test} test12()
  {
    var d0: Wrappers.Result<int, int> := Wrappers.Result<int, int>.Failure(error := 0);
    expect d0.Failure?, ""Test does not meet preconditions and should be removed""
    var r0 := d0.PropagateFailure<int>();
  }

  method {:test} test13()
  {
    var d0: Wrappers.Result<int, int> := Wrappers.Result<int, int>.Success(value := 0);
    var r0 := d0.MapFailure<int>((a0: int) => 0);
  }

  method {:test} test14()
  {
    var d0: Wrappers.Result<int, int> := Wrappers.Result<int, int>.Failure(error := 0);
    var r0 := d0.MapFailure<int>((a0: int) => 0);
  }

  method {:test} test15()
  {
    var d0: Wrappers.Result<int, int> := Wrappers.Result<int, int>.Success(value := 0);
    expect d0.Success?, ""Test does not meet preconditions and should be removed""
    var r0 := d0.Extract();
  }

  method {:test} test16()
  {
    var d0: Wrappers.Outcome<int> := Wrappers.Outcome<int>.Pass;
    var r0 := d0.IsFailure();
  }

  method {:test} test17()
  {
    var d0: Wrappers.Outcome<int> := Wrappers.Outcome<int>.Fail(error := 0);
    expect d0.Fail?, ""Test does not meet preconditions and should be removed""
    var r0 := d0.PropagateFailure<int>();
  }

  method {:test} test18()
  {
    var r0 := Wrappers.Need<int>(true, 0);
  }

  method {:test} test19()
  {
    var r0 := Wrappers.Need<int>(false, 0);
  }
}

module Wrappers {
  datatype Option<+T> = None | Some(value: T) {
    function method ToResult(): Result<T, string>
      decreases this
    {
      match this
      case Some(v) =>
        Success(v)
      case None() =>
        Failure(""Option is None"")
    }

    function method UnwrapOr(default: T): T
      decreases this
    {
      match this
      case Some(v) =>
        v
      case None() =>
        default
    }

    predicate method IsFailure()
      decreases this
    {
      None?
    }

    function method PropagateFailure<U>(): Option<U>
      requires None?
      decreases this
    {
      None
    }

    function method Extract(): T
      requires Some?
      decreases this
    {
      value
    }
  }

  datatype Result<+T, +R> = Success(value: T) | Failure(error: R) {
    function method ToOption(): Option<T>
      decreases this
    {
      match this
      case Success(s) =>
        Some(s)
      case Failure(e) =>
        None()
    }

    function method UnwrapOr(default: T): T
      decreases this
    {
      match this
      case Success(s) =>
        s
      case Failure(e) =>
        default
    }

    predicate method IsFailure()
      decreases this
    {
      Failure?
    }

    function method PropagateFailure<U>(): Result<U, R>
      requires Failure?
      decreases this
    {
      Failure(this.error)
    }

    function method MapFailure<NewR>(reWrap: R -> NewR): Result<T, NewR>
      decreases this
    {
      match this
      case Success(s) =>
        Success(s)
      case Failure(e) =>
        Failure(reWrap(e))
    }

    function method Extract(): T
      requires Success?
      decreases this
    {
      value
    }
  }

  datatype Outcome<E> = Pass | Fail(error: E) {
    predicate method IsFailure()
      decreases this
    {
      Fail?
    }

    function method PropagateFailure<U>(): Result<U, E>
      requires Fail?
      decreases this
    {
      Failure(this.error)
    }
  }

  function method Need<E>(condition: bool, error: E): (result: Outcome<E>)
    decreases condition
  {
    if condition then
      Pass
    else
      Fail(error)
  }
}

module srcMathdfyUnitTests {

  import Math
  method {:test} test0()
  {
    var r0 := Math.Min(7719, 7720);
  }

  method {:test} test1()
  {
    var r0 := Math.Min(0, 0);
  }

  method {:test} test2()
  {
    var r0 := Math.Max(0, 1);
  }

  method {:test} test3()
  {
    var r0 := Math.Max(0, 0);
  }
}

module Math {
  function method Min(a: int, b: int): int
    decreases a, b
  {
    if a < b then
      a
    else
      b
  }

  function method Max(a: int, b: int): int
    decreases a, b
  {
    if a < b then
      b
    else
      a
  }
}

module srcBoundedIntsdfyUnitTests {

  import BoundedInts
}

module BoundedInts {
  newtype uint8 = x: int
    | 0 <= x < TWO_TO_THE_8

  newtype uint16 = x: int
    | 0 <= x < TWO_TO_THE_16

  newtype uint32 = x: int
    | 0 <= x < TWO_TO_THE_32

  newtype uint64 = x: int
    | 0 <= x < TWO_TO_THE_64

  newtype int8 = x: int
    | -128 <= x < 128

  newtype int16 = x: int
    | -32768 <= x < 32768

  newtype int32 = x: int
    | -2147483648 <= x < 2147483648

  newtype int64 = x: int
    | -9223372036854775808 <= x < 9223372036854775808

  newtype nat8 = x: int
    | 0 <= x < 128

  newtype nat16 = x: int
    | 0 <= x < 32768

  newtype nat32 = x: int
    | 0 <= x < 2147483648

  newtype nat64 = x: int
    | 0 <= x < 9223372036854775808

  const TWO_TO_THE_0: int := 1
  const TWO_TO_THE_1: int := 2
  const TWO_TO_THE_2: int := 4
  const TWO_TO_THE_4: int := 16
  const TWO_TO_THE_5: int := 32
  const TWO_TO_THE_8: int := 256
  const TWO_TO_THE_16: int := 65536
  const TWO_TO_THE_24: int := 16777216
  const TWO_TO_THE_32: int := 4294967296
  const TWO_TO_THE_40: int := 1099511627776
  const TWO_TO_THE_48: int := 281474976710656
  const TWO_TO_THE_56: int := 72057594037927936
  const TWO_TO_THE_64: int := 18446744073709551616
  const TWO_TO_THE_128: int := 340282366920938463463374607431768211456
  const TWO_TO_THE_256: int := 115792089237316195423570985008687907853269984665640564039457584007913129639936
  const TWO_TO_THE_512: int := 13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096
}

module srcFunctionsdfyUnitTests {

  import Functions
}

module Functions {
  predicate Injective<X(!new), Y>(f: X --> Y)
    requires forall x: X :: f.requires(x)
    reads f.reads
    decreases set _x0: X, _o0: object? | _o0 in f.reads(_x0) :: _o0
  {
    forall x1: X, x2: X :: 
      f(x1) == f(x2) ==>
        x1 == x2
  }
}

module srcNonlinearArithmeticMuldfyUnitTests {

  import Mul

  import MulInternalsNonlinear

  import MulInternals

  import GeneralInternals
}

module Mul {

  import MulINL = MulInternalsNonlinear

  import opened MulInternals
  lemma LemmaMulIsMulRecursive(x: int, y: int)
    ensures x * y == MulRecursive(x, y)
    decreases x, y
  {
  }

  lemma LemmaMulIsMulRecursiveAuto()
    ensures forall x: int, y: int :: x * y == MulRecursive(x, y)
  {
  }

  lemma /*{:_induction x, y}*/ LemmaMulIsMulPos(x: int, y: int)
    requires x >= 0
    ensures x * y == MulPos(x, y)
    decreases x, y
  {
  }

  lemma LemmaMulBasics(x: int)
    ensures 0 * x == 0
    ensures x * 0 == 0
    ensures 1 * x == x
    ensures x * 1 == x
    decreases x
  {
  }

  lemma LemmaMulBasicsAuto()
    ensures forall x: int {:trigger 0 * x} :: 0 * x == 0
    ensures forall x: int {:trigger x * 0} :: x * 0 == 0
    ensures forall x: int {:trigger 1 * x} :: 1 * x == x
    ensures forall x: int {:trigger x * 1} :: x * 1 == x
  {
  }

  lemma LemmaMulNonzero(x: int, y: int)
    ensures x * y != 0 <==> x != 0 && y != 0
    decreases x, y
  {
  }

  lemma LemmaMulNonzeroAuto()
    ensures forall x: int, y: int {:trigger x * y} :: x * y != 0 <==> x != 0 && y != 0
  {
  }

  lemma LemmaMulByZeroIsZeroAuto()
    ensures forall x: int {:trigger 0 * x} {:trigger x * 0} :: x * 0 == 0 * x == 0
  {
  }

  lemma LemmaMulIsAssociative(x: int, y: int, z: int)
    ensures x * y * z == x * y * z
    decreases x, y, z
  {
  }

  lemma LemmaMulIsAssociativeAuto()
    ensures forall x: int, y: int, z: int {:trigger x * y * z} {:trigger x * y * z} :: x * y * z == x * y * z
  {
  }

  lemma LemmaMulIsCommutative(x: int, y: int)
    ensures x * y == y * x
    decreases x, y
  {
  }

  lemma LemmaMulIsCommutativeAuto()
    ensures forall x: int, y: int {:trigger x * y} :: x * y == y * x
  {
  }

  lemma LemmaMulOrdering(x: int, y: int)
    requires x != 0
    requires y != 0
    requires 0 <= x * y
    ensures x * y >= x && x * y >= y
    decreases x, y
  {
  }

  lemma LemmaMulOrderingAuto()
    ensures forall x: int, y: int {:trigger x * y} :: 0 != x && 0 != y && x * y >= 0 ==> x * y >= x && x * y >= y
  {
  }

  lemma LemmaMulEquality(x: int, y: int, z: int)
    requires x == y
    ensures x * z == y * z
    decreases x, y, z
  {
  }

  lemma LemmaMulEqualityAuto()
    ensures forall x: int, y: int, z: int {:trigger x * z, y * z} :: x == y ==> x * z == y * z
  {
  }

  lemma LemmaMulInequality(x: int, y: int, z: int)
    requires x <= y
    requires z >= 0
    ensures x * z <= y * z
    decreases x, y, z
  {
  }

  lemma LemmaMulInequalityAuto()
    ensures forall x: int, y: int, z: int {:trigger x * z, y * z} :: x <= y && z >= 0 ==> x * z <= y * z
  {
  }

  lemma LemmaMulStrictInequality(x: int, y: int, z: int)
    requires x < y
    requires z > 0
    ensures x * z < y * z
    decreases x, y, z
  {
  }

  lemma LemmaMulStrictInequalityAuto()
    ensures forall x: int, y: int, z: int {:trigger x * z, y * z} :: x < y && z > 0 ==> x * z < y * z
  {
  }

  lemma LemmaMulUpperBound(x: int, XBound: int, y: int, YBound: int)
    requires x <= XBound
    requires y <= YBound
    requires 0 <= x
    requires 0 <= y
    ensures x * y <= XBound * YBound
    decreases x, XBound, y, YBound
  {
  }

  lemma LemmaMulUpperBoundAuto()
    ensures forall YBound: int, y: int, XBound: int, x: int {:trigger x * y, XBound * YBound} :: x <= XBound && y <= YBound && 0 <= x && 0 <= y ==> x * y <= XBound * YBound
  {
  }

  lemma LemmaMulStrictUpperBound(x: int, XBound: int, y: int, YBound: int)
    requires x < XBound
    requires y < YBound
    requires 0 < x
    requires 0 < y
    ensures x * y <= (XBound - 1) * (YBound - 1)
    decreases x, XBound, y, YBound
  {
  }

  lemma LemmaMulStrictUpperBoundAuto()
    ensures forall YBound: int, y: int, XBound: int, x: int {:trigger x * y, (XBound - 1) * (YBound - 1)} :: x < XBound && y < YBound && 0 < x && 0 < y ==> x * y <= (XBound - 1) * (YBound - 1)
  {
  }

  lemma LemmaMulLeftInequality(x: int, y: int, z: int)
    requires 0 < x
    ensures y <= z ==> x * y <= x * z
    ensures y < z ==> x * y < x * z
    decreases x, y, z
  {
  }

  lemma LemmaMulLeftInequalityAuto()
    ensures forall x: int, y: int, z: int {:trigger x * y, x * z} :: x > 0 ==> (y <= z ==> x * y <= x * z) && (y < z ==> x * y < x * z)
  {
  }

  lemma LemmaMulEqualityConverse(m: int, x: int, y: int)
    requires m != 0
    requires m * x == m * y
    ensures x == y
    decreases m, x, y
  {
  }

  lemma LemmaMulEqualityConverseAuto()
    ensures forall m: int, x: int, y: int {:trigger m * x, m * y} :: m != 0 && m * x == m * y ==> x == y
  {
  }

  lemma LemmaMulInequalityConverse(x: int, y: int, z: int)
    requires x * z <= y * z
    requires z > 0
    ensures x <= y
    decreases x, y, z
  {
  }

  lemma LemmaMulInequalityConverseAuto()
    ensures forall x: int, y: int, z: int {:trigger x * z, y * z} :: x * z <= y * z && z > 0 ==> x <= y
  {
  }

  lemma LemmaMulStrictInequalityConverse(x: int, y: int, z: int)
    requires x * z < y * z
    requires z >= 0
    ensures x < y
    decreases x, y, z
  {
  }

  lemma LemmaMulStrictInequalityConverseAuto()
    ensures forall x: int, y: int, z: int {:trigger x * z, y * z} :: x * z < y * z && z >= 0 ==> x < y
  {
  }

  lemma LemmaMulIsDistributiveAdd(x: int, y: int, z: int)
    ensures x * (y + z) == x * y + x * z
    decreases x, y, z
  {
  }

  lemma LemmaMulIsDistributiveAddAuto()
    ensures forall x: int, y: int, z: int {:trigger x * (y + z)} :: x * (y + z) == x * y + x * z
  {
  }

  lemma LemmaMulIsDistributiveAddOtherWay(x: int, y: int, z: int)
    ensures (y + z) * x == y * x + z * x
    decreases x, y, z
  {
  }

  lemma LemmaMulIsDistributiveAddOtherWayAuto()
    ensures forall x: int, y: int, z: int {:trigger (y + z) * x} :: (y + z) * x == y * x + z * x
  {
  }

  lemma LemmaMulIsDistributiveSub(x: int, y: int, z: int)
    ensures x * (y - z) == x * y - x * z
    decreases x, y, z
  {
  }

  lemma LemmaMulIsDistributiveSubAuto()
    ensures forall x: int, y: int, z: int {:trigger x * (y - z)} :: x * (y - z) == x * y - x * z
  {
  }

  lemma LemmaMulIsDistributive(x: int, y: int, z: int)
    ensures x * (y + z) == x * y + x * z
    ensures x * (y - z) == x * y - x * z
    ensures (y + z) * x == y * x + z * x
    ensures (y - z) * x == y * x - z * x
    ensures x * (y + z) == (y + z) * x
    ensures x * (y - z) == (y - z) * x
    ensures x * y == y * x
    ensures x * z == z * x
    decreases x, y, z
  {
  }

  lemma LemmaMulIsDistributiveAuto()
    ensures forall x: int, y: int, z: int {:trigger x * (y + z)} :: x * (y + z) == x * y + x * z
    ensures forall x: int, y: int, z: int {:trigger x * (y - z)} :: x * (y - z) == x * y - x * z
    ensures forall x: int, y: int, z: int {:trigger (y + z) * x} :: (y + z) * x == y * x + z * x
    ensures forall x: int, y: int, z: int {:trigger (y - z) * x} :: (y - z) * x == y * x - z * x
  {
  }

  lemma LemmaMulStrictlyPositive(x: int, y: int)
    ensures 0 < x && 0 < y ==> 0 < x * y
    decreases x, y
  {
  }

  lemma LemmaMulStrictlyPositiveAuto()
    ensures forall x: int, y: int {:trigger x * y} :: 0 < x && 0 < y ==> 0 < x * y
  {
  }

  lemma LemmaMulStrictlyIncreases(x: int, y: int)
    requires 1 < x
    requires 0 < y
    ensures y < x * y
    decreases x, y
  {
  }

  lemma LemmaMulStrictlyIncreasesAuto()
    ensures forall x: int, y: int {:trigger x * y} :: 1 < x && 0 < y ==> y < x * y
  {
  }

  lemma LemmaMulIncreases(x: int, y: int)
    requires 0 < x
    requires 0 < y
    ensures y <= x * y
    decreases x, y
  {
  }

  lemma LemmaMulIncreasesAuto()
    ensures forall x: int, y: int {:trigger x * y} :: 0 < x && 0 < y ==> y <= x * y
  {
  }

  lemma LemmaMulNonnegative(x: int, y: int)
    requires 0 <= x
    requires 0 <= y
    ensures 0 <= x * y
    decreases x, y
  {
  }

  lemma LemmaMulNonnegativeAuto()
    ensures forall x: int, y: int {:trigger x * y} :: 0 <= x && 0 <= y ==> 0 <= x * y
  {
  }

  lemma LemmaMulUnaryNegation(x: int, y: int)
    ensures -x * y == -(x * y) == x * -y
    decreases x, y
  {
  }

  lemma LemmaMulUnaryNegationAuto()
    ensures forall x: int, y: int {:trigger -x * y} {:trigger x * -y} :: -x * y == -(x * y) == x * -y
  {
  }

  lemma LemmaMulCancelsNegatives(x: int, y: int)
    ensures x * y == -x * -y
    decreases x, y
  {
  }

  lemma LemmaMulCancelsNegativesAuto()
    ensures forall x: int, y: int {:trigger x * y} :: x * y == -x * -y
  {
  }

  lemma LemmaMulProperties()
    ensures forall x: int, y: int {:trigger x * y} :: x * y == y * x
    ensures forall x: int {:trigger x * 1} {:trigger 1 * x} :: x * 1 == 1 * x == x
    ensures forall x: int, y: int, z: int {:trigger x * z, y * z} :: x < y && z > 0 ==> x * z < y * z
    ensures forall x: int, y: int, z: int {:trigger x * z, y * z} :: x <= y && z >= 0 ==> x * z <= y * z
    ensures forall x: int, y: int, z: int {:trigger x * (y + z)} :: x * (y + z) == x * y + x * z
    ensures forall x: int, y: int, z: int {:trigger x * (y - z)} :: x * (y - z) == x * y - x * z
    ensures forall x: int, y: int, z: int {:trigger (y + z) * x} :: (y + z) * x == y * x + z * x
    ensures forall x: int, y: int, z: int {:trigger (y - z) * x} :: (y - z) * x == y * x - z * x
    ensures forall x: int, y: int, z: int {:trigger x * y * z} {:trigger x * y * z} :: x * y * z == x * y * z
    ensures forall x: int, y: int {:trigger x * y} :: x * y != 0 <==> x != 0 && y != 0
    ensures forall x: int, y: int {:trigger x * y} :: 0 <= x && 0 <= y ==> 0 <= x * y
    ensures forall x: int, y: int {:trigger x * y} :: 0 < x && 0 < y && 0 <= x * y ==> x <= x * y && y <= x * y
    ensures forall x: int, y: int {:trigger x * y} :: 1 < x && 0 < y ==> y < x * y
    ensures forall x: int, y: int {:trigger x * y} :: 0 < x && 0 < y ==> y <= x * y
    ensures forall x: int, y: int {:trigger x * y} :: 0 < x && 0 < y ==> 0 < x * y
  {
  }
}

module MulInternalsNonlinear {
  lemma LemmaMulStrictlyPositive(x: int, y: int)
    ensures 0 < x && 0 < y ==> 0 < x * y
    decreases x, y
  {
  }

  lemma LemmaMulNonzero(x: int, y: int)
    ensures x * y != 0 <==> x != 0 && y != 0
    decreases x, y
  {
  }

  lemma LemmaMulIsAssociative(x: int, y: int, z: int)
    ensures x * y * z == x * y * z
    decreases x, y, z
  {
  }

  lemma LemmaMulIsDistributiveAdd(x: int, y: int, z: int)
    ensures x * (y + z) == x * y + x * z
    decreases x, y, z
  {
  }

  lemma LemmaMulOrdering(x: int, y: int)
    requires x != 0
    requires y != 0
    requires 0 <= x * y
    ensures x * y >= x && x * y >= y
    decreases x, y
  {
  }

  lemma LemmaMulStrictInequality(x: int, y: int, z: int)
    requires x < y
    requires z > 0
    ensures x * z < y * z
    decreases x, y, z
  {
  }
}

module MulInternals {

  import opened GeneralInternals

  import opened MulInternalsNonlinear
  function method {:opaque} {:fuel 0, 0} MulPos(x: int, y: int): int
    requires x >= 0
    decreases x, y
  {
    if x == 0 then
      0
    else
      y + MulPos(x - 1, y)
  }

  function method MulRecursive(x: int, y: int): int
    decreases x, y
  {
    if x >= 0 then
      MulPos(x, y)
    else
      -1 * MulPos(-1 * x, y)
  }

  lemma LemmaMulInduction(f: int -> bool)
    requires f(0)
    requires forall i: int {:trigger f(i), f(i + 1)} :: i >= 0 && f(i) ==> f(i + 1)
    requires forall i: int {:trigger f(i), f(i - 1)} :: i <= 0 && f(i) ==> f(i - 1)
    ensures forall i: int {:trigger f(i)} :: f(i)
  {
  }

  lemma LemmaMulCommutes()
    ensures forall x: int, y: int {:trigger x * y} :: x * y == y * x
  {
  }

  lemma LemmaMulSuccessor()
    ensures forall x: int, y: int {:trigger (x + 1) * y} :: (x + 1) * y == x * y + y
    ensures forall x: int, y: int {:trigger (x - 1) * y} :: (x - 1) * y == x * y - y
  {
  }

  lemma LemmaMulDistributes()
    ensures forall x: int, y: int, z: int {:trigger (x + y) * z} :: (x + y) * z == x * z + y * z
    ensures forall x: int, y: int, z: int {:trigger (x - y) * z} :: (x - y) * z == x * z - y * z
  {
  }

  predicate MulAuto()
  {
    (forall x: int, y: int {:trigger x * y} :: 
      x * y == y * x) &&
    (forall x: int, y: int, z: int {:trigger (x + y) * z} :: 
      (x + y) * z == x * z + y * z) &&
    forall x: int, y: int, z: int {:trigger (x - y) * z} :: 
      (x - y) * z == x * z - y * z
  }

  lemma LemmaMulAuto()
    ensures MulAuto()
  {
  }

  lemma LemmaMulInductionAuto(x: int, f: int -> bool)
    requires MulAuto() ==> f(0) && (forall i: int {:trigger IsLe(0, i)} :: IsLe(0, i) && f(i) ==> f(i + 1)) && forall i: int {:trigger IsLe(i, 0)} :: IsLe(i, 0) && f(i) ==> f(i - 1)
    ensures MulAuto()
    ensures f(x)
    decreases x
  {
  }

  lemma LemmaMulInductionAutoForall(f: int -> bool)
    requires MulAuto() ==> f(0) && (forall i: int {:trigger IsLe(0, i)} :: IsLe(0, i) && f(i) ==> f(i + 1)) && forall i: int {:trigger IsLe(i, 0)} :: IsLe(i, 0) && f(i) ==> f(i - 1)
    ensures MulAuto()
    ensures forall i: int {:trigger f(i)} :: f(i)
  {
  }
}

module GeneralInternals {
  predicate IsLe(x: int, y: int)
    decreases x, y
  {
    x <= y
  }

  lemma LemmaInductionHelper(n: int, f: int -> bool, x: int)
    requires n > 0
    requires forall i: int :: 0 <= i < n ==> f(i)
    requires forall i: int {:trigger f(i), f(i + n)} :: i >= 0 && f(i) ==> f(i + n)
    requires forall i: int {:trigger f(i), f(i - n)} :: i < n && f(i) ==> f(i - n)
    ensures f(x)
    decreases if x >= n then x else -x
  {
  }
}

module srcNonlinearArithmeticInternalsModInternalsdfyUnitTests {

  import ModInternals

  import GeneralInternals

  import MulInternals

  import MulInternalsNonlinear

  import Mul

  import ModInternalsNonlinear

  import DivInternalsNonlinear
  method {:test} test0()
  {
    expect 8856 > 0, ""Test does not meet preconditions and should be removed""
    var r0 := ModInternals.ModRecursive(-8857, 8856);
  }

  method {:test} test1()
  {
    expect 2460 > 0, ""Test does not meet preconditions and should be removed""
    var r0 := ModInternals.ModRecursive(4417, 2460);
  }

  method {:test} test2()
  {
    expect 1 > 0, ""Test does not meet preconditions and should be removed""
    var r0 := ModInternals.ModRecursive(0, 1);
  }
}

module ModInternals {

  import opened GeneralInternals

  import opened Mul

  import opened MulInternalsNonlinear

  import opened MulInternals

  import opened ModInternalsNonlinear

  import opened DivInternalsNonlinear
  function method {:opaque} {:fuel 0, 0} ModRecursive(x: int, d: int): int
    requires d > 0
    decreases if x < 0 then d - x else x
  {
    if x < 0 then
      ModRecursive(d + x, d)
    else if x < d then
      x
    else
      ModRecursive(x - d, d)
  }

  lemma LemmaModInductionForall(n: int, f: int -> bool)
    requires n > 0
    requires forall i: int :: 0 <= i < n ==> f(i)
    requires forall i: int {:trigger f(i), f(i + n)} :: i >= 0 && f(i) ==> f(i + n)
    requires forall i: int {:trigger f(i), f(i - n)} :: i < n && f(i) ==> f(i - n)
    ensures forall i: int :: f(i)
    decreases n
  {
  }

  lemma LemmaModInductionForall2(n: int, f: (int, int) -> bool)
    requires n > 0
    requires forall i: int, j: int :: 0 <= i < n && 0 <= j < n ==> f(i, j)
    requires forall i: int, j: int {:trigger f(i, j), f(i + n, j)} :: i >= 0 && f(i, j) ==> f(i + n, j)
    requires forall i: int, j: int {:trigger f(i, j), f(i, j + n)} :: j >= 0 && f(i, j) ==> f(i, j + n)
    requires forall i: int, j: int {:trigger f(i, j), f(i - n, j)} :: i < n && f(i, j) ==> f(i - n, j)
    requires forall i: int, j: int {:trigger f(i, j), f(i, j - n)} :: j < n && f(i, j) ==> f(i, j - n)
    ensures forall i: int, j: int :: f(i, j)
    decreases n
  {
  }

  lemma LemmaModBasics(n: int)
    requires n > 0
    ensures forall x: int {:trigger (x + n) % n} :: (x + n) % n == x % n
    ensures forall x: int {:trigger (x - n) % n} :: (x - n) % n == x % n
    ensures forall x: int {:trigger (x + n) / n} :: (x + n) / n == x / n + 1
    ensures forall x: int {:trigger (x - n) / n} :: (x - n) / n == x / n - 1
    ensures forall x: int {:trigger x % n} :: 0 <= x < n <==> x % n == x
    decreases n
  {
  }

  lemma LemmaQuotientAndRemainder(x: int, q: int, r: int, n: int)
    requires n > 0
    requires 0 <= r < n
    requires x == q * n + r
    ensures q == x / n
    ensures r == x % n
    decreases if q > 0 then q else -q
  {
  }

  predicate ModAuto(n: int)
    requires n > 0
    decreases n
  {
    n % n == -n % n == 0 &&
    (forall x: int {:trigger x % n % n} :: 
      x % n % n == x % n) &&
    (forall x: int {:trigger x % n} :: 
      0 <= x < n <==> x % n == x) &&
    (forall x: int, y: int {:trigger (x + y) % n} :: 
      ghost var z: int := x % n + y % n; (0 <= z < n && (x + y) % n == z) || (n <= z < n + n && (x + y) % n == z - n)) &&
    forall x: int, y: int {:trigger (x - y) % n} :: 
      ghost var z: int := x % n - y % n; (0 <= z < n && (x - y) % n == z) || (-n <= z < 0 && (x - y) % n == z + n)
  }

  lemma LemmaModAuto(n: int)
    requires n > 0
    ensures ModAuto(n)
    decreases n
  {
  }

  lemma LemmaModInductionAuto(n: int, x: int, f: int -> bool)
    requires n > 0
    requires ModAuto(n) ==> (forall i: int {:trigger IsLe(0, i)} :: IsLe(0, i) && i < n ==> f(i)) && (forall i: int {:trigger IsLe(0, i)} :: IsLe(0, i) && f(i) ==> f(i + n)) && forall i: int {:trigger IsLe(i + 1, n)} :: IsLe(i + 1, n) && f(i) ==> f(i - n)
    ensures ModAuto(n)
    ensures f(x)
    decreases n, x
  {
  }

  lemma LemmaModInductionAutoForall(n: int, f: int -> bool)
    requires n > 0
    requires ModAuto(n) ==> (forall i: int {:trigger IsLe(0, i)} :: IsLe(0, i) && i < n ==> f(i)) && (forall i: int {:trigger IsLe(0, i)} :: IsLe(0, i) && f(i) ==> f(i + n)) && forall i: int {:trigger IsLe(i + 1, n)} :: IsLe(i + 1, n) && f(i) ==> f(i - n)
    ensures ModAuto(n)
    ensures forall i: int {:trigger f(i)} :: f(i)
    decreases n
  {
  }
}

module ModInternalsNonlinear {
  lemma LemmaModOfZeroIsZero(m: int)
    requires 0 < m
    ensures 0 % m == 0
    decreases m
  {
  }

  lemma LemmaFundamentalDivMod(x: int, d: int)
    requires d != 0
    ensures x == d * x / d + x % d
    decreases x, d
  {
  }

  lemma Lemma0ModAnything()
    ensures forall m: int {:trigger 0 % m} :: m > 0 ==> 0 % m == 0
  {
  }

  lemma LemmaSmallMod(x: nat, m: nat)
    requires x < m
    requires 0 < m
    ensures x % m == x
    decreases x, m
  {
  }

  lemma LemmaModRange(x: int, m: int)
    requires m > 0
    ensures 0 <= x % m < m
    decreases x, m
  {
  }
}

module DivInternalsNonlinear {
  lemma LemmaDivOf0(d: int)
    requires d != 0
    ensures 0 / d == 0
    decreases d
  {
  }

  lemma LemmaDivBySelf(d: int)
    requires d != 0
    ensures d / d == 1
    decreases d
  {
  }

  lemma LemmaSmallDiv()
    ensures forall d: int, x: int {:trigger x / d} :: 0 <= x < d && d > 0 ==> x / d == 0
  {
  }

  lemma LemmaRealDivGt(x: real, y: real)
    requires x > y
    requires x >= 0.0
    requires y > 0.0
    ensures x / y > 1 as real
    decreases x, y
  {
  }
}

module srcNonlinearArithmeticInternalsMulInternalsdfyUnitTests {

  import MulInternals

  import GeneralInternals

  import MulInternalsNonlinear
  method {:test} test0()
  {
    expect 1799 >= 0, ""Test does not meet preconditions and should be removed""
    var r0 := MulInternals.MulPos(1799, -7719);
  }

  method {:test} test1()
  {
    expect 0 >= 0, ""Test does not meet preconditions and should be removed""
    var r0 := MulInternals.MulPos(0, 0);
  }

  method {:test} test2()
  {
    var r0 := MulInternals.MulRecursive(1238, -7719);
  }
}

module srcNonlinearArithmeticInternalsMulInternalsNonlineardfyUnitTests {

  import MulInternalsNonlinear
}

module srcNonlinearArithmeticInternalsDivInternalsdfyUnitTests {

  import DivInternals

  import GeneralInternals

  import ModInternals

  import MulInternals

  import MulInternalsNonlinear

  import Mul

  import ModInternalsNonlinear

  import DivInternalsNonlinear
  method {:test} test0()
  {
    expect 1797 > 0, ""Test does not meet preconditions and should be removed""
    var r0 := DivInternals.DivPos(-1798, 1797);
  }

  method {:test} test1()
  {
    expect 2460 > 0, ""Test does not meet preconditions and should be removed""
    var r0 := DivInternals.DivPos(4417, 2460);
  }

  method {:test} test2()
  {
    expect 1 > 0, ""Test does not meet preconditions and should be removed""
    var r0 := DivInternals.DivPos(0, 1);
  }

  method {:test} test3()
  {
    expect 11 != 0, ""Test does not meet preconditions and should be removed""
    var r0 := DivInternals.DivRecursive(0, 11);
  }
}

module DivInternals {

  import opened GeneralInternals

  import opened ModInternals

  import opened ModInternalsNonlinear

  import opened DivInternalsNonlinear

  import opened MulInternals
  function method {:opaque} {:fuel 0, 0} DivPos(x: int, d: int): int
    requires d > 0
    decreases if x < 0 then d - x else x
  {
    if x < 0 then
      -1 + DivPos(x + d, d)
    else if x < d then
      0
    else
      1 + DivPos(x - d, d)
  }

  function method {:opaque} {:fuel 0, 0} DivRecursive(x: int, d: int): int
    requires d != 0
    decreases x, d
  {
    reveal DivPos();
    if d > 0 then
      DivPos(x, d)
    else
      -1 * DivPos(x, -1 * d)
  }

  lemma LemmaDivBasics(n: int)
    requires n > 0
    ensures n / n == -(-n / n) == 1
    ensures forall x: int {:trigger x / n} :: 0 <= x < n <==> x / n == 0
    ensures forall x: int {:trigger (x + n) / n} :: (x + n) / n == x / n + 1
    ensures forall x: int {:trigger (x - n) / n} :: (x - n) / n == x / n - 1
    decreases n
  {
  }

  predicate DivAuto(n: int)
    requires n > 0
    decreases n
  {
    ModAuto(n) &&
    n / n == -(-n / n) == 1 &&
    (forall x: int {:trigger x / n} :: 
      0 <= x < n <==> x / n == 0) &&
    (forall x: int, y: int {:trigger (x + y) / n} :: 
      ghost var z: int := x % n + y % n; (0 <= z < n && (x + y) / n == x / n + y / n) || (n <= z < n + n && (x + y) / n == x / n + y / n + 1)) &&
    forall x: int, y: int {:trigger (x - y) / n} :: 
      ghost var z: int := x % n - y % n; (0 <= z < n && (x - y) / n == x / n - y / n) || (-n <= z < 0 && (x - y) / n == x / n - y / n - 1)
  }

  lemma LemmaDivAuto(n: int)
    requires n > 0
    ensures DivAuto(n)
    decreases n
  {
  }

  lemma LemmaDivInductionAuto(n: int, x: int, f: int -> bool)
    requires n > 0
    requires DivAuto(n) ==> (forall i: int {:trigger IsLe(0, i)} :: IsLe(0, i) && i < n ==> f(i)) && (forall i: int {:trigger IsLe(0, i)} :: IsLe(0, i) && f(i) ==> f(i + n)) && forall i: int {:trigger IsLe(i + 1, n)} :: IsLe(i + 1, n) && f(i) ==> f(i - n)
    ensures DivAuto(n)
    ensures f(x)
    decreases n, x
  {
  }

  lemma LemmaDivInductionAutoForall(n: int, f: int -> bool)
    requires n > 0
    requires DivAuto(n) ==> (forall i: int {:trigger IsLe(0, i)} :: IsLe(0, i) && i < n ==> f(i)) && (forall i: int {:trigger IsLe(0, i)} :: IsLe(0, i) && f(i) ==> f(i + n)) && forall i: int {:trigger IsLe(i + 1, n)} :: IsLe(i + 1, n) && f(i) ==> f(i - n)
    ensures DivAuto(n)
    ensures forall i: int {:trigger f(i)} :: f(i)
    decreases n
  {
  }
}

module srcNonlinearArithmeticInternalsGeneralInternalsdfyUnitTests {

  import GeneralInternals
}

module srcNonlinearArithmeticInternalsModInternalsNonlineardfyUnitTests {

  import ModInternalsNonlinear
}

module srcNonlinearArithmeticInternalsDivInternalsNonlineardfyUnitTests {

  import DivInternalsNonlinear
}

module srcNonlinearArithmeticPowerdfyUnitTests {

  import Power

  import DivMod

  import DivInternalsNonlinear

  import DivInternals

  import GeneralInternals

  import ModInternals

  import MulInternals

  import MulInternalsNonlinear

  import Mul

  import ModInternalsNonlinear
  method {:test} test0()
  {
    var r0 := Power.Pow(0, 0 as nat);
  }
}

module Power {

  import opened DivMod

  import opened GeneralInternals

  import opened Mul

  import opened MulInternals
  function method {:opaque} {:fuel 0, 0} Pow(b: int, e: nat): int
    decreases e
  {
    if e == 0 then
      1
    else
      b * Pow(b, e - 1)
  }

  lemma /*{:_induction b}*/ LemmaPow0(b: int)
    ensures Pow(b, 0) == 1
    decreases b
  {
  }

  lemma LemmaPow0Auto()
    ensures forall b: nat {:trigger Pow(b, 0)} :: Pow(b, 0) == 1
  {
  }

  lemma /*{:_induction b}*/ LemmaPow1(b: int)
    ensures Pow(b, 1) == b
    decreases b
  {
  }

  lemma LemmaPow1Auto()
    ensures forall b: nat {:trigger Pow(b, 1)} :: Pow(b, 1) == b
  {
  }

  lemma /*{:_induction e}*/ Lemma0Pow(e: nat)
    requires e > 0
    ensures Pow(0, e) == 0
    decreases e
  {
  }

  lemma Lemma0PowAuto()
    ensures forall e: nat {:trigger Pow(0, e)} :: e > 0 ==> Pow(0, e) == 0
  {
  }

  lemma /*{:_induction e}*/ Lemma1Pow(e: nat)
    ensures Pow(1, e) == 1
    decreases e
  {
  }

  lemma Lemma1PowAuto()
    ensures forall e: nat {:trigger Pow(1, e)} :: Pow(1, e) == 1
  {
  }

  lemma /*{:_induction x}*/ LemmaSquareIsPow2(x: nat)
    ensures Pow(x, 2) == x * x
    decreases x
  {
  }

  lemma LemmaSquareIsPow2Auto()
    ensures forall x: nat {:trigger Pow(x, 2)} :: Pow(x, 2) == x * x
  {
  }

  lemma /*{:_induction b, e}*/ LemmaPowPositive(b: int, e: nat)
    requires b > 0
    ensures 0 < Pow(b, e)
    decreases b, e
  {
  }

  lemma LemmaPowPositiveAuto()
    ensures forall b: int, e: nat {:trigger Pow(b, e)} :: b > 0 ==> 0 < Pow(b, e)
  {
  }

  lemma /*{:_induction b, e1, e2}*/ LemmaPowAdds(b: int, e1: nat, e2: nat)
    ensures Pow(b, e1 + e2) == Pow(b, e1) * Pow(b, e2)
    decreases e1
  {
  }

  lemma LemmaPowAddsAuto()
    ensures forall b: int, e1: nat, e2: nat {:trigger Pow(b, e1 + e2)} :: Pow(b, e1 + e2) == Pow(b, e1) * Pow(b, e2)
  {
  }

  lemma /*{:_induction b, e1, e2}*/ LemmaPowSubtracts(b: nat, e1: nat, e2: nat)
    requires b > 0
    requires e1 <= e2
    ensures Pow(b, e1) > 0
    ensures Pow(b, e2 - e1) == Pow(b, e2) / Pow(b, e1) > 0
    decreases b, e1, e2
  {
  }

  lemma LemmaPowSubtractsAuto()
    ensures forall b: nat, e1: nat :: b > 0 ==> Pow(b, e1) > 0
    ensures forall e2: nat, e1: nat, b: nat {:trigger Pow(b, e2 - e1)} :: b > 0 && e1 <= e2 ==> Pow(b, e2 - e1) == Pow(b, e2) / Pow(b, e1) > 0
  {
  }

  lemma /*{:_induction a, b, c}*/ LemmaPowMultiplies(a: int, b: nat, c: nat)
    ensures 0 <= b * c
    ensures Pow(Pow(a, b), c) == Pow(a, b * c)
    decreases c
  {
  }

  lemma LemmaPowMultipliesAuto()
    ensures forall b: nat, c: nat {:trigger b * c} :: 0 <= b * c
    ensures forall a: int, b: nat, c: nat {:trigger Pow(a, b * c)} :: Pow(Pow(a, b), c) == Pow(a, b * c)
  {
  }

  lemma /*{:_induction a, b, e}*/ LemmaPowDistributes(a: int, b: int, e: nat)
    ensures Pow(a * b, e) == Pow(a, e) * Pow(b, e)
    decreases e
  {
  }

  lemma LemmaPowDistributesAuto()
    ensures forall a: int, b: int, e: nat {:trigger Pow(a * b, e)} :: Pow(a * b, e) == Pow(a, e) * Pow(b, e)
  {
  }

  lemma LemmaPowAuto()
    ensures forall x: int {:trigger Pow(x, 0)} :: Pow(x, 0) == 1
    ensures forall x: int {:trigger Pow(x, 1)} :: Pow(x, 1) == x
    ensures forall x: int, y: int {:trigger Pow(x, y)} :: y == 0 ==> Pow(x, y) == 1
    ensures forall x: int, y: int {:trigger Pow(x, y)} :: y == 1 ==> Pow(x, y) == x
    ensures forall x: int, y: int {:trigger x * y} :: 0 < x && 0 < y ==> x <= x * y
    ensures forall x: int, y: int {:trigger x * y} :: 0 < x && 1 < y ==> x < x * y
    ensures forall x: int, y: nat, z: nat {:trigger Pow(x, y + z)} :: Pow(x, y + z) == Pow(x, y) * Pow(x, z)
    ensures forall x: int, y: nat, z: nat {:trigger Pow(x, y - z)} :: y >= z ==> Pow(x, y - z) * Pow(x, z) == Pow(x, y)
    ensures forall x: int, y: int, z: nat {:trigger Pow(x * y, z)} :: Pow(x * y, z) == Pow(x, z) * Pow(y, z)
  {
  }

  lemma /*{:_induction b, e1, e2}*/ LemmaPowStrictlyIncreases(b: nat, e1: nat, e2: nat)
    requires 1 < b
    requires e1 < e2
    ensures Pow(b, e1) < Pow(b, e2)
    decreases b, e1, e2
  {
  }

  lemma LemmaPowStrictlyIncreasesAuto()
    ensures forall e2: nat, e1: nat, b: nat {:trigger Pow(b, e1), Pow(b, e2)} :: 1 < b && e1 < e2 ==> Pow(b, e1) < Pow(b, e2)
  {
  }

  lemma /*{:_induction b, e1, e2}*/ LemmaPowIncreases(b: nat, e1: nat, e2: nat)
    requires b > 0
    requires e1 <= e2
    ensures Pow(b, e1) <= Pow(b, e2)
    decreases b, e1, e2
  {
  }

  lemma LemmaPowIncreasesAuto()
    ensures forall e2: nat, e1: nat, b: nat {:trigger Pow(b, e1), Pow(b, e2)} :: 1 < b && e1 <= e2 ==> Pow(b, e1) <= Pow(b, e2)
  {
  }

  lemma /*{:_induction b, e1, e2}*/ LemmaPowStrictlyIncreasesConverse(b: nat, e1: nat, e2: nat)
    requires b > 0
    requires Pow(b, e1) < Pow(b, e2)
    ensures e1 < e2
    decreases b, e1, e2
  {
  }

  lemma LemmaPowStrictlyIncreasesConverseAuto()
    ensures forall b: nat, e1: nat, e2: nat {:trigger Pow(b, e1), Pow(b, e2)} :: b > 0 && Pow(b, e1) < Pow(b, e2) ==> e1 < e2
  {
  }

  lemma /*{:_induction b, e1, e2}*/ LemmaPowIncreasesConverse(b: nat, e1: nat, e2: nat)
    requires 1 < b
    requires Pow(b, e1) <= Pow(b, e2)
    ensures e1 <= e2
    decreases b, e1, e2
  {
  }

  lemma LemmaPowIncreasesConverseAuto()
    ensures forall b: nat, e1: nat, e2: nat {:trigger Pow(b, e1), Pow(b, e2)} :: 1 < b && Pow(b, e1) <= Pow(b, e2) ==> e1 <= e2
  {
  }

  lemma /*{:_induction b, x, y, z}*/ LemmaPullOutPows(b: nat, x: nat, y: nat, z: nat)
    requires b > 0
    ensures 0 <= x * y
    ensures 0 <= y * z
    ensures Pow(Pow(b, x * y), z) == Pow(Pow(b, x), y * z)
    decreases b, x, y, z
  {
  }

  lemma LemmaPullOutPowsAuto()
    ensures forall y: nat, z: nat {:trigger z * y} :: 0 <= z * y && 0 <= y * z
    ensures forall b: nat, x: nat, y: nat, z: nat {:trigger Pow(Pow(b, x * y), z)} :: b > 0 ==> Pow(Pow(b, x * y), z) == Pow(Pow(b, x), y * z)
  {
  }

  lemma /*{:_induction b, e1, e2}*/ LemmaPowDivisionInequality(x: nat, b: nat, e1: nat, e2: nat)
    requires b > 0
    requires e2 <= e1
    requires x < Pow(b, e1)
    ensures Pow(b, e2) > 0
    ensures x / Pow(b, e2) < Pow(b, e1 - e2)
    decreases x, b, e1, e2
  {
  }

  lemma LemmaPowDivisionInequalityAuto()
    ensures forall b: nat, e2: nat :: b > 0 ==> Pow(b, e2) > 0
    ensures forall x: nat, b: nat, e1: nat, e2: nat {:trigger x / Pow(b, e2), Pow(b, e1 - e2)} :: b > 0 && e2 <= e1 && x < Pow(b, e1) ==> x / Pow(b, e2) < Pow(b, e1 - e2)
  {
  }

  lemma /*{:_induction b, e}*/ LemmaPowMod(b: nat, e: nat)
    requires b > 0 && e > 0
    ensures Pow(b, e) % b == 0
    decreases b, e
  {
  }

  lemma LemmaPowModAuto()
    ensures forall b: nat, e: nat {:trigger Pow(b, e)} :: b > 0 && e > 0 ==> Pow(b, e) % b == 0
  {
  }

  lemma /*{:_induction b, e, m}*/ LemmaPowModNoop(b: int, e: nat, m: int)
    requires m > 0
    ensures Pow(b % m, e) % m == Pow(b, e) % m
    decreases e
  {
  }

  lemma LemmaPowModNoopAuto()
    ensures forall b: nat, e: nat, m: nat {:trigger Pow(b % m, e)} :: m > 0 ==> Pow(b % m, e) % m == Pow(b, e) % m
  {
  }
}

module DivMod {

  import opened DivInternals

  import DivINL = DivInternalsNonlinear

  import opened ModInternals

  import ModINL = ModInternalsNonlinear

  import opened MulInternals

  import opened Mul

  import opened GeneralInternals
  lemma LemmaDivIsDivRecursive(x: int, d: int)
    requires 0 < d
    ensures DivRecursive(x, d) == x / d
    decreases x, d
  {
  }

  lemma LemmaDivIsDivRecursiveAuto()
    ensures forall x: int, d: int {:trigger x / d} :: d > 0 ==> DivRecursive(x, d) == x / d
  {
  }

  lemma LemmaDivBySelf(d: int)
    requires d != 0
    ensures d / d == 1
    decreases d
  {
  }

  lemma LemmaDivOf0(d: int)
    requires d != 0
    ensures 0 / d == 0
    decreases d
  {
  }

  lemma LemmaDivBasics(x: int)
    ensures x != 0 ==> 0 / x == 0
    ensures x / 1 == x
    ensures x != 0 ==> x / x == 1
    decreases x
  {
  }

  lemma LemmaDivBasicsAuto()
    ensures forall x: int {:trigger 0 / x} :: x != 0 ==> 0 / x == 0
    ensures forall x: int {:trigger x / 1} :: x / 1 == x
    ensures forall x: int, y: int {:trigger x / y} :: x >= 0 && y > 0 ==> x / y >= 0
    ensures forall x: int, y: int {:trigger x / y} :: x >= 0 && y > 0 ==> x / y <= x
  {
  }

  lemma LemmaSmallDivConverseAuto()
    ensures forall x: int, d: int {:trigger x / d} :: 0 <= x && 0 < d && x / d == 0 ==> x < d
  {
  }

  lemma LemmaDivIsOrderedByDenominator(x: int, y: int, z: int)
    requires 0 <= x
    requires 1 <= y <= z
    ensures x / y >= x / z
    decreases x
  {
  }

  lemma LemmaDivIsOrderedByDenominatorAuto()
    ensures forall z: int, y: int, x: int {:trigger x / y, x / z} :: 0 <= x && 1 <= y <= z ==> x / y >= x / z
  {
  }

  lemma LemmaDivIsStrictlyOrderedByDenominator(x: int, d: int)
    requires 0 < x
    requires 1 < d
    ensures x / d < x
    decreases x
  {
  }

  lemma LemmaDivIsStrictlyOrderedByDenominatorAuto()
    ensures forall x: int, d: int {:trigger x / d} :: 0 < x && 1 < d ==> x / d < x
  {
  }

  lemma LemmaDividingSums(a: int, b: int, d: int, R: int)
    requires 0 < d
    requires R == a % d + b % d - (a + b) % d
    ensures d * (a + b) / d - R == d * a / d + d * b / d
    decreases a, b, d, R
  {
  }

  lemma LemmaDividingSumsAuto()
    ensures forall a: int, b: int, d: int, R: int {:trigger d * (a + b) / d - R, d * a / d + d * b / d} :: 0 < d && R == a % d + b % d - (a + b) % d ==> d * (a + b) / d - R == d * a / d + d * b / d
  {
  }

  lemma LemmaDivPosIsPos(x: int, d: int)
    requires 0 <= x
    requires 0 < d
    ensures 0 <= x / d
    decreases x, d
  {
  }

  lemma LemmaDivPosIsPosAuto()
    ensures forall x: int, d: int {:trigger x / d} :: 0 <= x && 0 < d ==> 0 <= x / d
  {
  }

  lemma LemmaDivPlusOne(x: int, d: int)
    requires 0 < d
    ensures 1 + x / d == (d + x) / d
    decreases x, d
  {
  }

  lemma LemmaDivPlusOneAuto()
    ensures forall x: int, d: int {:trigger 1 + x / d, (d + x) / d} :: 0 < d ==> 1 + x / d == (d + x) / d
  {
  }

  lemma LemmaDivMinusOne(x: int, d: int)
    requires 0 < d
    ensures -1 + x / d == (-d + x) / d
    decreases x, d
  {
  }

  lemma LemmaDivMinusOneAuto()
    ensures forall x: int, d: int {:trigger -1 + x / d, (-d + x) / d} :: 0 < d ==> -1 + x / d == (-d + x) / d
  {
  }

  lemma LemmaBasicDiv(d: int)
    requires 0 < d
    ensures forall x: int {:trigger x / d} :: 0 <= x < d ==> x / d == 0
    decreases d
  {
  }

  lemma LemmaBasicDivAuto()
    ensures forall d: int, x: int {:trigger x / d} :: 0 <= x < d ==> x / d == 0
  {
  }

  lemma LemmaDivIsOrdered(x: int, y: int, z: int)
    requires x <= y
    requires 0 < z
    ensures x / z <= y / z
    decreases x, y, z
  {
  }

  lemma LemmaDivIsOrderedAuto()
    ensures forall x: int, y: int, z: int {:trigger x / z, y / z} :: x <= y && 0 < z ==> x / z <= y / z
  {
  }

  lemma LemmaDivDecreases(x: int, d: int)
    requires 0 < x
    requires 1 < d
    ensures x / d < x
    decreases x, d
  {
  }

  lemma LemmaDivDecreasesAuto()
    ensures forall x: int, d: int {:trigger x / d} :: 0 < x && 1 < d ==> x / d < x
  {
  }

  lemma LemmaDivNonincreasing(x: int, d: int)
    requires 0 <= x
    requires 0 < d
    ensures x / d <= x
    decreases x, d
  {
  }

  lemma LemmaDivNonincreasingAuto()
    ensures forall x: int, d: int {:trigger x / d} :: 0 <= x && 0 < d ==> x / d <= x
  {
  }

  lemma LemmaSmallMod(x: nat, m: nat)
    requires x < m
    requires 0 < m
    ensures x % m == x
    decreases x, m
  {
  }

  lemma LemmaBreakdown(x: int, y: int, z: int)
    requires 0 <= x
    requires 0 < y
    requires 0 < z
    ensures 0 < y * z
    ensures x % (y * z) == y * x / y % z + x % y
    decreases x, y, z
  {
  }

  lemma LemmaBreakdownAuto()
    ensures forall x: int, y: int, z: int {:trigger y * z, x % (y * z), y * x / y % z + x % y} :: 0 <= x && 0 < y && 0 < z ==> 0 < y * z && x % (y * z) == y * x / y % z + x % y
  {
  }

  lemma LemmaRemainderUpper(x: int, d: int)
    requires 0 <= x
    requires 0 < d
    ensures x - d < x / d * d
    decreases x, d
  {
  }

  lemma LemmaRemainderUpperAuto()
    ensures forall x: int, d: int {:trigger x - d, d * d} :: 0 <= x && 0 < d ==> x - d < x / d * d
  {
  }

  lemma LemmaRemainderLower(x: int, d: int)
    requires 0 <= x
    requires 0 < d
    ensures x >= x / d * d
    decreases x, d
  {
  }

  lemma LemmaRemainderLowerAuto()
    ensures forall x: int, d: int {:trigger x / d * d} :: 0 <= x && 0 < d ==> x >= x / d * d
  {
  }

  lemma LemmaRemainder(x: int, d: int)
    requires 0 <= x
    requires 0 < d
    ensures 0 <= x - x / d * d < d
    decreases x, d
  {
  }

  lemma LemmaRemainderAuto()
    ensures forall x: int, d: int {:trigger x - x / d * d} :: 0 <= x && 0 < d ==> 0 <= x - x / d * d < d
  {
  }

  lemma LemmaFundamentalDivMod(x: int, d: int)
    requires d != 0
    ensures x == d * x / d + x % d
    decreases x, d
  {
  }

  lemma LemmaFundamentalDivModAuto()
    ensures forall x: int, d: int {:trigger d * x / d + x % d} :: d != 0 ==> x == d * x / d + x % d
  {
  }

  lemma LemmaDivDenominator(x: int, c: nat, d: nat)
    requires 0 <= x
    requires 0 < c
    requires 0 < d
    ensures c * d != 0
    ensures x / c / d == x / (c * d)
    decreases x, c, d
  {
  }

  lemma LemmaDivDenominatorAuto()
    ensures forall c: nat, d: nat {:trigger c * d} :: 0 < c && 0 < d ==> c * d != 0
    ensures forall x: int, c: nat, d: nat {:trigger x / c / d} :: 0 <= x && 0 < c && 0 < d ==> x / c / d == x / (c * d)
  {
  }

  lemma LemmaMulHoistInequality(x: int, y: int, z: int)
    requires 0 <= x
    requires 0 < z
    ensures x * y / z <= x * y / z
    decreases x, y, z
  {
  }

  lemma LemmaMulHoistInequalityAuto()
    ensures forall x: int, y: int, z: int {:trigger x * y / z, x * y / z} :: 0 <= x && 0 < z ==> x * y / z <= x * y / z
  {
  }

  lemma LemmaIndistinguishableQuotients(a: int, b: int, d: int)
    requires 0 < d
    requires 0 <= a - a % d <= b < a + d - a % d
    ensures a / d == b / d
    decreases a, b, d
  {
  }

  lemma LemmaIndistinguishableQuotientsAuto()
    ensures forall a: int, b: int, d: int {:trigger a / d, b / d} :: 0 < d && 0 <= a - a % d <= b < a + d - a % d ==> a / d == b / d
  {
  }

  lemma LemmaTruncateMiddle(x: int, b: int, c: int)
    requires 0 <= x
    requires 0 < b
    requires 0 < c
    ensures 0 < b * c
    ensures b * x % (b * c) == b * x % c
    decreases x, b, c
  {
  }

  lemma LemmaTruncateMiddleAuto()
    ensures forall x: int, b: int, c: int {:trigger b * x % c} :: 0 <= x && 0 < b && 0 < c && 0 < b * c ==> b * x % (b * c) == b * x % c
  {
  }

  lemma LemmaDivMultiplesVanishQuotient(x: int, a: int, d: int)
    requires 0 < x
    requires 0 <= a
    requires 0 < d
    ensures 0 < x * d
    ensures a / d == x * a / (x * d)
    decreases x, a, d
  {
  }

  lemma LemmaDivMultiplesVanishQuotientAuto()
    ensures forall x: int, a: int, d: int {:trigger a / d, x * d, x * a} :: 0 < x && 0 <= a && 0 < d ==> 0 < x * d && a / d == x * a / (x * d)
  {
  }

  lemma LemmaRoundDown(a: int, r: int, d: int)
    requires 0 < d
    requires a % d == 0
    requires 0 <= r < d
    ensures a == d * (a + r) / d
    decreases a, r, d
  {
  }

  lemma LemmaRoundDownAuto()
    ensures forall d: int, r: int, a: int {:trigger d * (a + r) / d} :: 0 < d && a % d == 0 && 0 <= r < d ==> a == d * (a + r) / d
  {
  }

  lemma LemmaDivMultiplesVanishFancy(x: int, b: int, d: int)
    requires 0 < d
    requires 0 <= b < d
    ensures (d * x + b) / d == x
    decreases x, b, d
  {
  }

  lemma LemmaDivMultiplesVanishFancyAuto()
    ensures forall d: int, b: int, x: int {:trigger (d * x + b) / d} :: 0 < d && 0 <= b < d ==> (d * x + b) / d == x
  {
  }

  lemma LemmaDivMultiplesVanish(x: int, d: int)
    requires 0 < d
    ensures d * x / d == x
    decreases x, d
  {
  }

  lemma LemmaDivMultiplesVanishAuto()
    ensures forall x: int, d: int {:trigger d * x / d} :: 0 < d ==> d * x / d == x
  {
  }

  lemma LemmaDivByMultiple(b: int, d: int)
    requires 0 <= b
    requires 0 < d
    ensures b * d / d == b
    decreases b, d
  {
  }

  lemma LemmaDivByMultipleAuto()
    ensures forall b: int, d: int {:trigger b * d / d} :: 0 <= b && 0 < d ==> b * d / d == b
  {
  }

  lemma LemmaDivByMultipleIsStronglyOrdered(x: int, y: int, m: int, z: int)
    requires x < y
    requires y == m * z
    requires 0 < z
    ensures x / z < y / z
    decreases x, y, m, z
  {
  }

  lemma LemmaDivByMultipleIsStronglyOrderedAuto()
    ensures forall z: int, m: int, y: int, x: int {:trigger x / z, m * z, y / z} :: x < y && y == m * z && 0 < z ==> x / z < y / z
  {
  }

  lemma LemmaMultiplyDivideLe(a: int, b: int, c: int)
    requires 0 < b
    requires a <= b * c
    ensures a / b <= c
    decreases a, b, c
  {
  }

  lemma LemmaMultiplyDivideLeAuto()
    ensures forall a: int, b: int, c: int {:trigger a / b, b * c} :: 0 < b && a <= b * c ==> a / b <= c
  {
  }

  lemma LemmaMultiplyDivideLt(a: int, b: int, c: int)
    requires 0 < b
    requires a < b * c
    ensures a / b < c
    decreases a, b, c
  {
  }

  lemma LemmaMultiplyDivideLtAuto()
    ensures forall a: int, b: int, c: int {:trigger a / b, b * c} :: 0 < b && a < b * c ==> a / b < c
  {
  }

  lemma LemmaHoistOverDenominator(x: int, j: int, d: nat)
    requires 0 < d
    ensures x / d + j == (x + j * d) / d
    decreases x, j, d
  {
  }

  lemma LemmaHoistOverDenominatorAuto()
    ensures forall x: int, j: int, d: nat {:trigger x / d + j} :: 0 < d ==> x / d + j == (x + j * d) / d
  {
  }

  lemma LemmaPartBound1(a: int, b: int, c: int)
    requires 0 <= a
    requires 0 < b
    requires 0 < c
    ensures 0 < b * c
    ensures b * a / b % (b * c) <= b * (c - 1)
    decreases a, b, c
  {
  }

  lemma LemmaPartBound1Auto()
    ensures forall a: int, b: int, c: int {:trigger b * a / b % (b * c)} :: 0 <= a && 0 < b && 0 < c ==> 0 < b * c && b * a / b % (b * c) <= b * (c - 1)
  {
  }

  lemma /*{:_induction x, m}*/ LemmaModIsModRecursive(x: int, m: int)
    requires m > 0
    ensures ModRecursive(x, m) == x % m
    decreases if x < 0 then -x + m else x
  {
  }

  lemma LemmaModIsModRecursiveAuto()
    ensures forall x: int, d: int {:trigger x % d} :: d > 0 ==> ModRecursive(x, d) == x % d
  {
  }

  lemma LemmaModBasicsAuto()
    ensures forall m: int {:trigger m % m} :: m > 0 ==> m % m == 0
    ensures forall x: int, m: int {:trigger x % m % m} :: m > 0 ==> x % m % m == x % m
  {
  }

  lemma LemmaModPropertiesAuto()
    ensures forall m: int {:trigger m % m} :: m > 0 ==> m % m == 0
    ensures forall x: int, m: int {:trigger x % m % m} :: m > 0 ==> x % m % m == x % m
    ensures forall x: int, m: int {:trigger x % m} :: m > 0 ==> 0 <= x % m < m
  {
  }

  lemma LemmaModDecreases(x: nat, m: nat)
    requires 0 < m
    ensures x % m <= x
    decreases x, m
  {
  }

  lemma LemmaModDecreasesAuto()
    ensures forall x: nat, m: nat {:trigger x % m} :: 0 < m ==> x % m <= x
  {
  }

  lemma LemmaModIsZero(x: nat, m: nat)
    requires x > 0 && m > 0
    requires x % m == 0
    ensures x >= m
    decreases x, m
  {
  }

  lemma LemmaModIsZeroAuto()
    ensures forall m: nat, x: nat {:trigger x % m} :: x > 0 && m > 0 && x % m == 0 ==> x >= m
  {
  }

  lemma LemmaModMultiplesBasic(x: int, m: int)
    requires m > 0
    ensures x * m % m == 0
    decreases x, m
  {
  }

  lemma LemmaModMultiplesBasicAuto()
    ensures forall x: int, m: int {:trigger x * m % m} :: m > 0 ==> x * m % m == 0
  {
  }

  lemma LemmaModAddMultiplesVanish(b: int, m: int)
    requires 0 < m
    ensures (m + b) % m == b % m
    decreases b, m
  {
  }

  lemma LemmaModAddMultiplesVanishAuto()
    ensures forall b: int, m: int {:trigger b % m} :: 0 < m ==> (m + b) % m == b % m
  {
  }

  lemma LemmaModSubMultiplesVanish(b: int, m: int)
    requires 0 < m
    ensures (-m + b) % m == b % m
    decreases b, m
  {
  }

  lemma LemmaModSubMultiplesVanishAuto()
    ensures forall b: int, m: int {:trigger b % m} :: 0 < m ==> (-m + b) % m == b % m
  {
  }

  lemma LemmaModMultiplesVanish(a: int, b: int, m: int)
    requires 0 < m
    ensures (m * a + b) % m == b % m
    decreases if a > 0 then a else -a
  {
  }

  lemma LemmaModMultiplesVanishAuto()
    ensures forall a: int, b: int, m: int {:trigger (m * a + b) % m} :: 0 < m ==> (m * a + b) % m == b % m
  {
  }

  lemma LemmaModSubtraction(x: nat, s: nat, d: nat)
    requires 0 < d
    requires 0 <= s <= x % d
    ensures x % d - s % d == (x - s) % d
    decreases x, s, d
  {
  }

  lemma LemmaModSubtractionAuto()
    ensures forall x: nat, s: nat, d: nat {:trigger (x - s) % d} :: 0 < d && 0 <= s <= x % d ==> x % d - s % d == (x - s) % d
  {
  }

  lemma LemmaAddModNoop(x: int, y: int, m: int)
    requires 0 < m
    ensures (x % m + y % m) % m == (x + y) % m
    decreases x, y, m
  {
  }

  lemma LemmaAddModNoopAuto()
    ensures forall x: int, y: int, m: int {:trigger (x + y) % m} :: 0 < m ==> (x % m + y % m) % m == (x + y) % m
  {
  }

  lemma LemmaAddModNoopRight(x: int, y: int, m: int)
    requires 0 < m
    ensures (x + y % m) % m == (x + y) % m
    decreases x, y, m
  {
  }

  lemma LemmaAddModNoopRightAuto()
    ensures forall x: int, y: int, m: int {:trigger (x + y) % m} :: 0 < m ==> (x + y % m) % m == (x + y) % m
  {
  }

  lemma LemmaSubModNoop(x: int, y: int, m: int)
    requires 0 < m
    ensures (x % m - y % m) % m == (x - y) % m
    decreases x, y, m
  {
  }

  lemma LemmaSubModNoopAuto()
    ensures forall x: int, y: int, m: int {:trigger (x - y) % m} :: 0 < m ==> (x % m - y % m) % m == (x - y) % m
  {
  }

  lemma LemmaSubModNoopRight(x: int, y: int, m: int)
    requires 0 < m
    ensures (x - y % m) % m == (x - y) % m
    decreases x, y, m
  {
  }

  lemma LemmaSubModNoopRightAuto()
    ensures forall x: int, y: int, m: int {:trigger (x - y) % m} :: 0 < m ==> (x - y % m) % m == (x - y) % m
  {
  }

  lemma LemmaModAdds(a: int, b: int, d: int)
    requires 0 < d
    ensures a % d + b % d == (a + b) % d + d * (a % d + b % d) / d
    ensures a % d + b % d < d ==> a % d + b % d == (a + b) % d
    decreases a, b, d
  {
  }

  lemma LemmaModAddsAuto()
    ensures forall a: int, b: int, d: int {:trigger (a + b) % d} :: 0 < d ==> a % d + b % d == (a + b) % d + d * (a % d + b % d) / d && a % d + b % d < d ==> a % d + b % d == (a + b) % d
  {
  }

  lemma {:timeLimitMultiplier 2} /*{:_timeLimit 20}*/ LemmaModNegNeg(x: int, d: int)
    requires 0 < d
    ensures x % d == x * (1 - d) % d
    decreases x, d
  {
  }

  lemma {:timeLimitMultiplier 5} /*{:_timeLimit 50}*/ LemmaFundamentalDivModConverse(x: int, d: int, q: int, r: int)
    requires d != 0
    requires 0 <= r < d
    requires x == q * d + r
    ensures q == x / d
    ensures r == x % d
    decreases x, d, q, r
  {
  }

  lemma {:timeLimitMultiplier 5} /*{:_timeLimit 50}*/ LemmaFundamentalDivModConverseAuto()
    ensures forall x: int, d: int, q: int, r: int {:trigger q * d + r, x % d} :: d != 0 && 0 <= r < d && x == q * d + r ==> q == x / d && r == x % d
  {
  }

  lemma LemmaModPosBound(x: int, m: int)
    requires 0 <= x
    requires 0 < m
    ensures 0 <= x % m < m
    decreases x
  {
  }

  lemma LemmaModPosBoundAuto()
    ensures forall x: int, m: int {:trigger x % m} :: 0 <= x && 0 < m ==> 0 <= x % m < m
  {
  }

  lemma LemmaMulModNoopLeft(x: int, y: int, m: int)
    requires 0 < m
    ensures x % m * y % m == x * y % m
    decreases x, y, m
  {
  }

  lemma LemmaMulModNoopLeftAuto()
    ensures forall x: int, y: int, m: int {:trigger x * y % m} :: 0 < m ==> x % m * y % m == x * y % m
  {
  }

  lemma LemmaMulModNoopRight(x: int, y: int, m: int)
    requires 0 < m
    ensures x * y % m % m == x * y % m
    decreases x, y, m
  {
  }

  lemma LemmaMulModNoopRightAuto()
    ensures forall x: int, y: int, m: int {:trigger x * y % m} :: 0 < m ==> x * y % m % m == x * y % m
  {
  }

  lemma LemmaMulModNoopGeneral(x: int, y: int, m: int)
    requires 0 < m
    ensures x % m * y % m == x * y % m
    ensures x * y % m % m == x * y % m
    ensures x % m * y % m % m == x * y % m
    decreases x, y, m
  {
  }

  lemma LemmaMulModNoopGeneralAuto()
    ensures forall x: int, y: int, m: int {:trigger x * y % m} :: 0 < m ==> x % m * y % m == x * y % m % m == x % m * y % m % m == x * y % m
  {
  }

  lemma LemmaMulModNoop(x: int, y: int, m: int)
    requires 0 < m
    ensures x % m * y % m % m == x * y % m
    decreases x, y, m
  {
  }

  lemma LemmaMulModNoopAuto()
    ensures forall x: int, y: int, m: int {:trigger x * y % m} :: 0 < m ==> x % m * y % m % m == x * y % m
  {
  }

  lemma LemmaModEquivalence(x: int, y: int, m: int)
    requires 0 < m
    ensures x % m == y % m <==> (x - y) % m == 0
    decreases x, y, m
  {
  }

  lemma LemmaModEquivalenceAuto()
    ensures forall x: int, y: int, m: int {:trigger x % m, y % m} :: 0 < m && x % m == y % m <==> 0 < m && (x - y) % m == 0
  {
  }

  predicate IsModEquivalent(x: int, y: int, m: int)
    requires m > 0
    ensures x % m == y % m <==> (x - y) % m == 0
    decreases x, y, m
  {
    LemmaModEquivalence(x, y, m);
    (x - y) % m == 0
  }

  lemma LemmaModMulEquivalent(x: int, y: int, z: int, m: int)
    requires m > 0
    requires IsModEquivalent(x, y, m)
    ensures IsModEquivalent(x * z, y * z, m)
    decreases x, y, z, m
  {
  }

  lemma LemmaModMulEquivalentAuto()
    ensures forall x: int, y: int, z: int, m: int {:trigger IsModEquivalent(x * z, y * z, m)} :: m > 0 && IsModEquivalent(x, y, m) ==> IsModEquivalent(x * z, y * z, m)
  {
  }

  lemma LemmaModOrdering(x: int, k: int, d: int)
    requires 1 < d
    requires 0 < k
    ensures 0 < d * k
    ensures x % d <= x % (d * k)
    decreases x, k, d
  {
  }

  lemma LemmaModOrderingAuto()
    ensures forall x: int, k: int, d: int {:trigger x % (d * k)} :: 1 < d && 0 < k ==> 0 < d * k && x % d <= x % (d * k)
  {
  }

  lemma LemmaModMod(x: int, a: int, b: int)
    requires 0 < a
    requires 0 < b
    ensures 0 < a * b
    ensures x % (a * b) % a == x % a
    decreases x, a, b
  {
  }

  lemma LemmaModModAuto()
    ensures forall x: int, a: int, b: int {:trigger a * b, x % a} :: 0 < a && 0 < b ==> 0 < a * b && x % (a * b) % a == x % a
  {
  }

  lemma LemmaPartBound2(x: int, y: int, z: int)
    requires 0 <= x
    requires 0 < y
    requires 0 < z
    ensures y * z > 0
    ensures x % y % (y * z) < y
    decreases x, y, z
  {
  }

  lemma LemmaPartBound2Auto()
    ensures forall x: int, y: int, z: int {:trigger y * z, x % y} :: 0 <= x && 0 < y && 0 < z ==> y * z > 0 && x % y % (y * z) < y
  {
  }

  lemma LemmaModBreakdown(x: int, y: int, z: int)
    requires 0 <= x
    requires 0 < y
    requires 0 < z
    ensures y * z > 0
    ensures x % (y * z) == y * x / y % z + x % y
    decreases x, y, z
  {
  }

  lemma LemmaModBreakdownAuto()
    ensures forall x: int, y: int, z: int {:trigger x % (y * z)} :: 0 <= x && 0 < y && 0 < z ==> y * z > 0 && x % (y * z) == y * x / y % z + x % y
  {
  }
}

module srcNonlinearArithmeticDivModdfyUnitTests {

  import DivMod

  import DivInternalsNonlinear

  import DivInternals

  import GeneralInternals

  import ModInternals

  import MulInternals

  import MulInternalsNonlinear

  import Mul

  import ModInternalsNonlinear
}

module srcNonlinearArithmeticPower2dfyUnitTests {

  import Power2

  import GeneralInternals

  import MulInternals

  import MulInternalsNonlinear

  import Power

  import DivMod

  import DivInternalsNonlinear

  import DivInternals

  import ModInternals

  import Mul

  import ModInternalsNonlinear
}

module Power2 {

  import opened GeneralInternals

  import opened MulInternals

  import opened Power
  function method {:opaque} {:fuel 0, 0} Pow2(e: nat): nat
    ensures Pow2(e) > 0
    decreases e
  {
    reveal Pow();
    LemmaPowPositive(2, e);
    Pow(2, e)
  }

  lemma /*{:_induction e}*/ LemmaPow2(e: nat)
    ensures Pow2(e) == Pow(2, e)
    decreases e
  {
  }

  lemma LemmaPow2Auto()
    ensures forall e: nat {:trigger Pow2(e)} :: Pow2(e) == Pow(2, e)
  {
  }

  lemma LemmaPow2MaskDiv2(e: nat)
    requires 0 < e
    ensures (Pow2(e) - 1) / 2 == Pow2(e - 1) - 1
    decreases e
  {
  }

  lemma LemmaPow2MaskDiv2Auto()
    ensures forall e: nat {:trigger Pow2(e)} :: 0 < e ==> (Pow2(e) - 1) / 2 == Pow2(e - 1) - 1
  {
  }

  lemma Lemma2To64()
    ensures Pow2(0) == 1
    ensures Pow2(1) == 2
    ensures Pow2(2) == 4
    ensures Pow2(3) == 8
    ensures Pow2(4) == 16
    ensures Pow2(5) == 32
    ensures Pow2(6) == 64
    ensures Pow2(7) == 128
    ensures Pow2(8) == 256
    ensures Pow2(9) == 512
    ensures Pow2(10) == 1024
    ensures Pow2(11) == 2048
    ensures Pow2(12) == 4096
    ensures Pow2(13) == 8192
    ensures Pow2(14) == 16384
    ensures Pow2(15) == 32768
    ensures Pow2(16) == 65536
    ensures Pow2(17) == 131072
    ensures Pow2(18) == 262144
    ensures Pow2(19) == 524288
    ensures Pow2(20) == 1048576
    ensures Pow2(21) == 2097152
    ensures Pow2(22) == 4194304
    ensures Pow2(23) == 8388608
    ensures Pow2(24) == 16777216
    ensures Pow2(25) == 33554432
    ensures Pow2(26) == 67108864
    ensures Pow2(27) == 134217728
    ensures Pow2(28) == 268435456
    ensures Pow2(29) == 536870912
    ensures Pow2(30) == 1073741824
    ensures Pow2(31) == 2147483648
    ensures Pow2(32) == 4294967296
    ensures Pow2(64) == 18446744073709551616
  {
  }
}

module srcCollectionsMapsMapsdfyUnitTests {

  import Maps

  import Wrappers
  method {:test} test0()
  {
    var d0: map<int, int> := map[0 := 1, 2 := 3, 4 := 5, 6 := 7];
    var r0 := Maps.Get<int, int>(d0, 0);
  }

  method {:test} test1()
  {
    var d0: map<int, int> := map[];
    var r0 := Maps.Get<int, int>(d0, 0);
  }

  method {:test} test2()
  {
    var d0: map<int, int> := map[0 := 1, 2 := 3, 4 := 5, 6 := 7];
    var r0 := Maps.ToImap<int, int>(d0);
  }

  method {:test} test3()
  {
    var d0: map<int, int> := map[];
    var r0 := Maps.ToImap<int, int>(d0);
  }

  method {:test} test5()
  {
    var d0: map<int, int> := map[];
    var d1: set<int> := {};
    var r0 := Maps.RemoveKeys<int, int>(d0, d1);
    expect r0.Keys == d0.Keys - d1, ""expectation violation""
  }

  method {:test} test6()
  {
    var d0: map<int, int> := map[0 := 1, 2 := 3, 4 := 5, 6 := 7];
    var r0 := Maps.Remove<int, int>(d0, 8);
    expect r0 == Maps.RemoveKeys(d0, {8}), ""expectation violation""
    expect |r0.Keys| <= |d0.Keys|, ""expectation violation""
    expect 8 in d0 ==> |r0| == |d0| - 1, ""expectation violation""
    expect 8 !in d0 ==> |r0| == |d0|, ""expectation violation""
  }

  method {:test} test7()
  {
    var d0: map<int, int> := map[];
    var r0 := Maps.Remove<int, int>(d0, 0);
    expect r0 == Maps.RemoveKeys(d0, {0}), ""expectation violation""
    expect |r0.Keys| <= |d0.Keys|, ""expectation violation""
    expect 0 in d0 ==> |r0| == |d0| - 1, ""expectation violation""
    expect 0 !in d0 ==> |r0| == |d0|, ""expectation violation""
  }

  method {:test} test8()
  {
    var d0: map<int, int> := map[0 := 1, 2 := 3, 4 := 5, 6 := 7];
    var r0 := Maps.Remove<int, int>(d0, 6);
    expect r0 == Maps.RemoveKeys(d0, {6}), ""expectation violation""
    expect |r0.Keys| <= |d0.Keys|, ""expectation violation""
    expect 6 in d0 ==> |r0| == |d0| - 1, ""expectation violation""
    expect 6 !in d0 ==> |r0| == |d0|, ""expectation violation""
  }

  method {:test} test10()
  {
    var d0: map<int, int> := map[0 := 1, 2 := 3, 4 := 5, 6 := 7];
    var d1: set<int> := {0};
    var r0 := Maps.Restrict<int, int>(d0, d1);
    expect r0 == Maps.RemoveKeys(d0, d0.Keys - d1), ""expectation violation""
  }

  method {:test} test11()
  {
    var d0: map<int, int> := map[];
    var d1: set<int> := {};
    var r0 := Maps.Restrict<int, int>(d0, d1);
    expect r0 == Maps.RemoveKeys(d0, d0.Keys - d1), ""expectation violation""
  }

  method {:test} test12()
  {
    var d0: map<int, int> := map[];
    var d1: set<int> := {0};
    var r0 := Maps.Restrict<int, int>(d0, d1);
    expect r0 == Maps.RemoveKeys(d0, d0.Keys - d1), ""expectation violation""
  }

  method {:test} test14()
  {
    var d0: map<int, int> := map[];
    var d1: map<int, int> := map[];
    var r0 := Maps.Union<int, int>(d0, d1);
    expect r0.Keys == d0.Keys + d1.Keys, ""expectation violation""
  }
}

module Maps {

  import opened Wrappers
  function method Get<X, Y>(m: map<X, Y>, x: X): Option<Y>
    decreases m
  {
    if x in m then
      Some(m[x])
    else
      None
  }

  function method {:opaque} {:fuel 0, 0} ToImap<X, Y>(m: map<X, Y>): (m': imap<X, Y>)
    ensures forall x: X {:trigger m'[x]} :: x in m ==> x in m' && m'[x] == m[x]
    ensures forall x: X {:trigger x in m'} :: x in m' ==> x in m
    decreases m
  {
    imap x: X {:trigger m[x]} {:trigger x in m} | x in m :: m[x]
  }

  function method {:opaque} {:fuel 0, 0} RemoveKeys<X, Y>(m: map<X, Y>, xs: set<X>): (m': map<X, Y>)
    ensures forall x: X {:trigger m'[x]} :: x in m && x !in xs ==> x in m' && m'[x] == m[x]
    ensures forall x: X {:trigger x in m'} :: x in m' ==> x in m && x !in xs
    ensures m'.Keys == m.Keys - xs
    decreases m, xs
  {
    m - xs
  }

  function method {:opaque} {:fuel 0, 0} Remove<X, Y>(m: map<X, Y>, x: X): (m': map<X, Y>)
    ensures m' == RemoveKeys(m, {x})
    ensures |m'.Keys| <= |m.Keys|
    ensures x in m ==> |m'| == |m| - 1
    ensures x !in m ==> |m'| == |m|
    decreases m
  {
    var m': map<X, Y> := map x': X {:trigger m[x']} {:trigger x' in m} | x' in m && x' != x :: m[x'];
    assert m'.Keys == m.Keys - {x};
    m'
  }

  function method {:opaque} {:fuel 0, 0} Restrict<X, Y>(m: map<X, Y>, xs: set<X>): (m': map<X, Y>)
    ensures m' == RemoveKeys(m, m.Keys - xs)
    decreases m, xs
  {
    map x: X {:trigger m[x]} {:trigger x in m} {:trigger x in xs} | x in xs && x in m :: m[x]
  }

  predicate EqualOnKey<X, Y>(m: map<X, Y>, m': map<X, Y>, x: X)
    decreases m, m'
  {
    (x !in m && x !in m') || (x in m && x in m' && m[x] == m'[x])
  }

  predicate IsSubset<X, Y>(m: map<X, Y>, m': map<X, Y>)
    decreases m, m'
  {
    m.Keys <= m'.Keys &&
    forall x: X {:trigger EqualOnKey(m, m', x)} {:trigger x in m} :: 
      x in m ==>
        EqualOnKey(m, m', x)
  }

  function method {:opaque} {:fuel 0, 0} Union<X, Y>(m: map<X, Y>, m': map<X, Y>): (r: map<X, Y>)
    ensures r.Keys == m.Keys + m'.Keys
    ensures forall x: X {:trigger r[x]} :: x in m' ==> r[x] == m'[x]
    ensures forall x: X {:trigger r[x]} :: x in m && x !in m' ==> r[x] == m[x]
    decreases m, m'
  {
    m + m'
  }

  lemma LemmaDisjointUnionSize<X, Y>(m: map<X, Y>, m': map<X, Y>)
    requires m.Keys !! m'.Keys
    ensures |Union(m, m')| == |m| + |m'|
    decreases m, m'
  {
  }

  predicate {:opaque} {:fuel 0, 0} Injective<X, Y>(m: map<X, Y>)
    decreases m
  {
    forall x: X, x': X {:trigger m[x], m[x']} :: 
      x != x' &&
      x in m &&
      x' in m ==>
        m[x] != m[x']
  }

  function {:opaque} {:fuel 0, 0} Invert<X, Y>(m: map<X, Y>): map<Y, X>
    decreases m
  {
    map y: Y {:trigger y in m.Values} | y in m.Values :: ghost var x: X :| x in m.Keys && m[x] == y; x
  }

  lemma LemmaInvertIsInjective<X, Y>(m: map<X, Y>)
    ensures Injective(Invert(m))
    decreases m
  {
  }

  predicate {:opaque} {:fuel 0, 0} Total<X(!new), Y>(m: map<X, Y>)
    decreases m
  {
    forall i: X {:trigger m[i]} {:trigger i in m} :: 
      i in m
  }

  predicate {:opaque} {:fuel 0, 0} Monotonic(m: map<int, int>)
    decreases m
  {
    forall x: int, x': int {:trigger m[x], m[x']} :: 
      x in m &&
      x' in m &&
      x <= x' ==>
        m[x] <= m[x']
  }

  predicate {:opaque} {:fuel 0, 0} MonotonicFrom(m: map<int, int>, start: int)
    decreases m, start
  {
    forall x: int, x': int {:trigger m[x], m[x']} :: 
      x in m &&
      x' in m &&
      start <= x <= x' ==>
        m[x] <= m[x']
  }
}

module srcCollectionsMapsImapsdfyUnitTests {

  import Imaps

  import Wrappers
  method {:test} test0()
  {
    var d0: imap<int, int> := imap[];
    var r0 := Imaps.Get<int, int>(d0, 0);
  }
}

module Imaps {

  import opened Wrappers
  function method Get<X, Y>(m: imap<X, Y>, x: X): Option<Y>
  {
    if x in m then
      Some(m[x])
    else
      None
  }

  function {:opaque} {:fuel 0, 0} RemoveKeys<X, Y>(m: imap<X, Y>, xs: iset<X>): (m': imap<X, Y>)
    ensures forall x: X {:trigger m'[x]} :: x in m && x !in xs ==> x in m' && m'[x] == m[x]
    ensures forall x: X {:trigger x in m'} :: x in m' ==> x in m && x !in xs
    ensures m'.Keys == m.Keys - xs
  {
    imap x: X {:trigger m[x]} {:trigger x in xs} {:trigger x in m} | x in m && x !in xs :: m[x]
  }

  function {:opaque} {:fuel 0, 0} RemoveKey<X, Y>(m: imap<X, Y>, x: X): (m': imap<X, Y>)
    ensures m' == RemoveKeys(m, iset{x})
    ensures forall x': X {:trigger m'[x']} :: x' in m' ==> m'[x'] == m[x']
  {
    imap i: X {:trigger m[i]} {:trigger i in m} | i in m && i != x :: m[i]
  }

  function {:opaque} {:fuel 0, 0} Restrict<X, Y>(m: imap<X, Y>, xs: iset<X>): (m': imap<X, Y>)
    ensures m' == RemoveKeys(m, m.Keys - xs)
  {
    imap x: X {:trigger m[x]} {:trigger x in m} {:trigger x in xs} | x in xs && x in m :: m[x]
  }

  predicate EqualOnKey<X, Y>(m: imap<X, Y>, m': imap<X, Y>, x: X)
  {
    (x !in m && x !in m') || (x in m && x in m' && m[x] == m'[x])
  }

  predicate IsSubset<X, Y>(m: imap<X, Y>, m': imap<X, Y>)
  {
    m.Keys <= m'.Keys &&
    forall x: X {:trigger EqualOnKey(m, m', x)} {:trigger x in m} :: 
      x in m ==>
        EqualOnKey(m, m', x)
  }

  function {:opaque} {:fuel 0, 0} Union<X, Y>(m: imap<X, Y>, m': imap<X, Y>): (r: imap<X, Y>)
    ensures r.Keys == m.Keys + m'.Keys
    ensures forall x: X {:trigger r[x]} :: x in m' ==> r[x] == m'[x]
    ensures forall x: X {:trigger r[x]} :: x in m && x !in m' ==> r[x] == m[x]
  {
    m + m'
  }

  predicate {:opaque} {:fuel 0, 0} Injective<X, Y>(m: imap<X, Y>)
  {
    forall x: X, x': X {:trigger m[x], m[x']} :: 
      x != x' &&
      x in m &&
      x' in m ==>
        m[x] != m[x']
  }

  function {:opaque} {:fuel 0, 0} Invert<X, Y>(m: imap<X, Y>): imap<Y, X>
  {
    imap y: Y {:trigger y in m.Values} | y in m.Values :: ghost var x: X :| x in m.Keys && m[x] == y; x
  }

  lemma LemmaInvertIsInjective<X, Y>(m: imap<X, Y>)
    ensures Injective(Invert(m))
  {
  }

  predicate {:opaque} {:fuel 0, 0} Total<X(!new), Y>(m: imap<X, Y>)
  {
    forall i: X {:trigger m[i]} {:trigger i in m} :: 
      i in m
  }

  predicate {:opaque} {:fuel 0, 0} Monotonic(m: imap<int, int>)
  {
    forall x: int, x': int {:trigger m[x], m[x']} :: 
      x in m &&
      x' in m &&
      x <= x' ==>
        m[x] <= m[x']
  }

  predicate {:opaque} {:fuel 0, 0} MonotonicFrom(m: imap<int, int>, start: int)
    decreases start
  {
    forall x: int, x': int {:trigger m[x], m[x']} :: 
      x in m &&
      x' in m &&
      start <= x <= x' ==>
        m[x] <= m[x']
  }
}

module srcCollectionsSequencesLittleEndianNatConversionsdfyUnitTests {

  import DivMod

  import DivInternalsNonlinear

  import DivInternals

  import GeneralInternals

  import ModInternals

  import MulInternals

  import MulInternalsNonlinear

  import Mul

  import ModInternalsNonlinear

  import Power

  import Seq

  import Wrappers

  import Math
}

abstract module SmallSeq refines LittleEndianNat {
  function method BITS(): nat
    ensures BITS() > 1

  function method BASE(): nat
    ensures BASE() > 1
  {
    LemmaPowPositive(2, BITS() - 1);
    LemmaPowStrictlyIncreases(2, BITS() - 1, BITS());
    Pow(2, BITS())
  }

  function method {:opaque} {:fuel 0, 0} ToNatRight(xs: seq<uint>): nat
    decreases xs
  {
    if |xs| == 0 then
      0
    else
      LemmaMulNonnegativeAuto(); ToNatRight(DropFirst(xs)) * BASE() + First(xs)
  }

  function method {:opaque} {:fuel 0, 0} ToNatLeft(xs: seq<uint>): nat
    decreases xs
  {
    if |xs| == 0 then
      0
    else
      LemmaPowPositiveAuto(); LemmaMulNonnegativeAuto(); ToNatLeft(DropLast(xs)) + Last(xs) * Pow(BASE(), |xs| - 1)
  }

  lemma {:vcs_split_on_every_assert} /*{:_induction xs}*/ LemmaToNatLeftEqToNatRight(xs: seq<uint>)
    ensures ToNatRight(xs) == ToNatLeft(xs)
    decreases xs
  {
    reveal ToNatRight();
    reveal ToNatLeft();
    if xs == [] {
    } else {
      if DropLast(xs) == [] {
        calc {
          ToNatLeft(xs);
          Last(xs) * Pow(BASE(), |xs| - 1);
          {
            reveal Pow();
          }
          Last(xs);
          First(xs);
          {
            assert ToNatRight(DropFirst(xs)) == 0;
          }
          ToNatRight(xs);
        }
      } else {
        calc {
          ToNatLeft(xs);
          ToNatLeft(DropLast(xs)) + Last(xs) * Pow(BASE(), |xs| - 1);
          {
            LemmaToNatLeftEqToNatRight(DropLast(xs));
          }
          ToNatRight(DropLast(xs)) + Last(xs) * Pow(BASE(), |xs| - 1);
          ToNatRight(DropFirst(DropLast(xs))) * BASE() + First(xs) + Last(xs) * Pow(BASE(), |xs| - 1);
          {
            LemmaToNatLeftEqToNatRight(DropFirst(DropLast(xs)));
          }
          ToNatLeft(DropFirst(DropLast(xs))) * BASE() + First(xs) + Last(xs) * Pow(BASE(), |xs| - 1);
          {
            assert DropFirst(DropLast(xs)) == DropLast(DropFirst(xs));
            reveal Pow();
            LemmaMulProperties();
          }
          ToNatLeft(DropLast(DropFirst(xs))) * BASE() + First(xs) + Last(xs) * Pow(BASE(), |xs| - 2) * BASE();
          {
            LemmaMulIsDistributiveAddOtherWayAuto();
          }
          ToNatLeft(DropFirst(xs)) * BASE() + First(xs);
          {
            LemmaToNatLeftEqToNatRight(DropFirst(xs));
          }
          ToNatRight(xs);
        }
      }
    }
  }

  lemma LemmaToNatLeftEqToNatRightAuto()
    ensures forall xs: seq<uint> :: ToNatRight(xs) == ToNatLeft(xs)
  {
    reveal ToNatRight();
    reveal ToNatLeft();
    forall xs: seq<uint> | true
      ensures ToNatRight(xs) == ToNatLeft(xs)
    {
      LemmaToNatLeftEqToNatRight(xs);
    }
  }

  lemma /*{:_induction xs}*/ LemmaSeqLen1(xs: seq<uint>)
    requires |xs| == 1
    ensures ToNatRight(xs) == First(xs)
    decreases xs
  {
    reveal ToNatRight();
  }

  lemma /*{:_induction xs}*/ LemmaSeqLen2(xs: seq<uint>)
    requires |xs| == 2
    ensures ToNatRight(xs) == First(xs) + xs[1] * BASE()
    decreases xs
  {
    reveal ToNatRight();
    LemmaSeqLen1(DropLast(xs));
  }

  lemma /*{:_induction xs}*/ LemmaSeqAppendZero(xs: seq<uint>)
    ensures ToNatRight(xs + [0]) == ToNatRight(xs)
    decreases xs
  {
    reveal ToNatLeft();
    LemmaToNatLeftEqToNatRightAuto();
    calc {
      ToNatRight(xs + [0]);
      ToNatLeft(xs + [0]);
      ToNatLeft(xs) + 0 * Pow(BASE(), |xs|);
      {
        LemmaMulBasicsAuto();
      }
      ToNatLeft(xs);
      ToNatRight(xs);
    }
  }

  lemma /*{:_induction xs}*/ LemmaSeqNatBound(xs: seq<uint>)
    ensures ToNatRight(xs) < Pow(BASE(), |xs|)
    decreases xs
  {
    reveal Pow();
    if |xs| == 0 {
      reveal ToNatRight();
    } else {
      ghost var len' := |xs| - 1;
      ghost var pow := Pow(BASE(), len');
      calc {
        ToNatRight(xs);
        {
          LemmaToNatLeftEqToNatRight(xs);
        }
        ToNatLeft(xs);
        {
          reveal ToNatLeft();
        }
        ToNatLeft(DropLast(xs)) + Last(xs) * pow;
      <
        {
          LemmaToNatLeftEqToNatRight(DropLast(xs));
          LemmaSeqNatBound(DropLast(xs));
        }
        pow + Last(xs) * pow;
      <=
        {
          LemmaPowPositiveAuto();
          LemmaMulInequalityAuto();
        }
        pow + (BASE() - 1) * pow;
        {
          LemmaMulIsDistributiveAuto();
        }
        Pow(BASE(), len' + 1);
      }
    }
  }

  lemma /*{:_induction xs, i}*/ LemmaSeqPrefix(xs: seq<uint>, i: nat)
    requires 0 <= i <= |xs|
    ensures ToNatRight(xs[..i]) + ToNatRight(xs[i..]) * Pow(BASE(), i) == ToNatRight(xs)
    decreases xs, i
  {
    reveal ToNatRight();
    reveal Pow();
    if i == 1 {
      assert ToNatRight(xs[..1]) == First(xs);
    } else if i > 1 {
      calc {
        ToNatRight(xs[..i]) + ToNatRight(xs[i..]) * Pow(BASE(), i);
        ToNatRight(DropFirst(xs[..i])) * BASE() + First(xs) + ToNatRight(xs[i..]) * Pow(BASE(), i);
        {
          assert DropFirst(xs[..i]) == DropFirst(xs)[..i - 1];
          LemmaMulProperties();
        }
        ToNatRight(DropFirst(xs)[..i - 1]) * BASE() + First(xs) + ToNatRight(xs[i..]) * Pow(BASE(), i - 1) * BASE();
        {
          LemmaMulIsDistributiveAddOtherWayAuto();
        }
        (ToNatRight(DropFirst(xs)[..i - 1]) + ToNatRight(DropFirst(xs)[i - 1..]) * Pow(BASE(), i - 1)) * BASE() + First(xs);
        {
          LemmaSeqPrefix(DropFirst(xs), i - 1);
        }
        ToNatRight(xs);
      }
    }
  }

  lemma /*{:_induction xs, ys}*/ LemmaSeqMswInequality(xs: seq<uint>, ys: seq<uint>)
    requires |xs| == |ys| > 0
    requires Last(xs) < Last(ys)
    ensures ToNatRight(xs) < ToNatRight(ys)
    decreases xs, ys
  {
    reveal ToNatLeft();
    LemmaToNatLeftEqToNatRightAuto();
    ghost var len' := |xs| - 1;
    calc {
      ToNatRight(xs);
      ToNatLeft(xs);
    <
      {
        LemmaSeqNatBound(DropLast(xs));
      }
      Pow(BASE(), len') + Last(xs) * Pow(BASE(), len');
    ==
      {
        LemmaMulIsDistributiveAuto();
      }
      (1 + Last(xs)) * Pow(BASE(), len');
    <=
      {
        LemmaPowPositiveAuto();
        LemmaMulInequalityAuto();
      }
      ToNatLeft(ys);
      ToNatRight(ys);
    }
  }

  lemma /*{:_induction xs, ys}*/ LemmaSeqPrefixNeq(xs: seq<uint>, ys: seq<uint>, i: nat)
    requires 0 <= i <= |xs| == |ys|
    requires ToNatRight(xs[..i]) != ToNatRight(ys[..i])
    ensures ToNatRight(xs) != ToNatRight(ys)
    decreases |xs| - i
  {
    if i == |xs| {
      assert xs[..i] == xs;
      assert ys[..i] == ys;
    } else {
      if xs[i] == ys[i] {
        reveal ToNatLeft();
        assert DropLast(xs[..i + 1]) == xs[..i];
        assert DropLast(ys[..i + 1]) == ys[..i];
        LemmaToNatLeftEqToNatRightAuto();
        assert ToNatRight(xs[..i + 1]) == ToNatLeft(xs[..i + 1]);
      } else if xs[i] < ys[i] {
        LemmaSeqMswInequality(xs[..i + 1], ys[..i + 1]);
      } else {
        LemmaSeqMswInequality(ys[..i + 1], xs[..i + 1]);
      }
      LemmaSeqPrefixNeq(xs, ys, i + 1);
    }
  }

  lemma /*{:_induction xs, ys}*/ LemmaSeqNeq(xs: seq<uint>, ys: seq<uint>)
    requires |xs| == |ys|
    requires xs != ys
    ensures ToNatRight(xs) != ToNatRight(ys)
    decreases xs, ys
  {
    ghost var i: nat, n: nat := 0, |xs|;
    while i < n
      invariant 0 <= i < n
      invariant xs[..i] == ys[..i]
      decreases n - i
    {
      if xs[i] != ys[i] {
        break;
      }
      i := i + 1;
    }
    assert ToNatLeft(xs[..i]) == ToNatLeft(ys[..i]);
    reveal ToNatLeft();
    assert xs[..i + 1][..i] == xs[..i];
    assert ys[..i + 1][..i] == ys[..i];
    LemmaPowPositiveAuto();
    LemmaMulStrictInequalityAuto();
    assert ToNatLeft(xs[..i + 1]) != ToNatLeft(ys[..i + 1]);
    LemmaToNatLeftEqToNatRightAuto();
    LemmaSeqPrefixNeq(xs, ys, i + 1);
  }

  lemma /*{:_induction xs, ys}*/ LemmaSeqEq(xs: seq<uint>, ys: seq<uint>)
    requires |xs| == |ys|
    requires ToNatRight(xs) == ToNatRight(ys)
    ensures xs == ys
    decreases xs, ys
  {
    calc ==> {
      xs != ys;
      {
        LemmaSeqNeq(xs, ys);
      }
      ToNatRight(xs) != ToNatRight(ys);
      false;
    }
  }

  lemma /*{:_induction xs}*/ LemmaSeqLswModEquivalence(xs: seq<uint>)
    requires |xs| >= 1
    ensures IsModEquivalent(ToNatRight(xs), First(xs), BASE())
    decreases xs
  {
    if |xs| == 1 {
      LemmaSeqLen1(xs);
      LemmaModEquivalenceAuto();
    } else {
      assert IsModEquivalent(ToNatRight(xs), First(xs), BASE()) by {
        reveal ToNatRight();
        calc ==> {
          true;
          {
            LemmaModEquivalenceAuto();
          }
          IsModEquivalent(ToNatRight(xs), ToNatRight(DropFirst(xs)) * BASE() + First(xs), BASE());
          {
            LemmaModMultiplesBasicAuto();
          }
          IsModEquivalent(ToNatRight(xs), First(xs), BASE());
        }
      }
    }
  }

  function method {:opaque} {:fuel 0, 0} FromNat(n: nat): (xs: seq<uint>)
    decreases n
  {
    if n == 0 then
      []
    else
      LemmaDivBasicsAuto(); LemmaDivDecreasesAuto(); [n % BASE()] + FromNat(n / BASE())
  }

  lemma /*{:_induction n, len}*/ LemmaFromNatLen(n: nat, len: nat)
    requires Pow(BASE(), len) > n
    ensures |FromNat(n)| <= len
    decreases n, len
  {
    reveal FromNat();
    if n == 0 {
    } else {
      calc {
        |FromNat(n)|;
      ==
        {
          LemmaDivBasicsAuto();
        }
        1 + |FromNat(n / BASE())|;
      <=
        {
          LemmaMultiplyDivideLtAuto();
          LemmaDivDecreasesAuto();
          reveal Pow();
          LemmaFromNatLen(n / BASE(), len - 1);
        }
        len;
      }
    }
  }

  lemma /*{:_induction n}*/ LemmaNatSeqNat(n: nat)
    ensures ToNatRight(FromNat(n)) == n
    decreases n
  {
    reveal ToNatRight();
    reveal FromNat();
    if n == 0 {
    } else {
      calc {
        ToNatRight(FromNat(n));
        {
          LemmaDivBasicsAuto();
        }
        ToNatRight([n % BASE()] + FromNat(n / BASE()));
        n % BASE() + ToNatRight(FromNat(n / BASE())) * BASE();
        {
          LemmaDivDecreasesAuto();
          LemmaNatSeqNat(n / BASE());
        }
        n % BASE() + n / BASE() * BASE();
        {
          LemmaFundamentalDivMod(n, BASE());
        }
        n;
      }
    }
  }

  function method {:opaque} {:fuel 0, 0} SeqExtend(xs: seq<uint>, n: nat): (ys: seq<uint>)
    requires |xs| <= n
    ensures |ys| == n
    ensures ToNatRight(ys) == ToNatRight(xs)
    decreases n - |xs|
  {
    if |xs| >= n then
      xs
    else
      LemmaSeqAppendZero(xs); SeqExtend(xs + [0], n)
  }

  function method {:opaque} {:fuel 0, 0} SeqExtendMultiple(xs: seq<uint>, n: nat): (ys: seq<uint>)
    requires n > 0
    ensures |ys| % n == 0
    ensures ToNatRight(ys) == ToNatRight(xs)
    decreases xs, n
  {
    var newLen: int := |xs| + n - |xs| % n;
    LemmaSubModNoopRight(|xs| + n, |xs|, n);
    LemmaModBasicsAuto();
    assert newLen % n == 0;
    LemmaSeqNatBound(xs);
    LemmaPowIncreasesAuto();
    SeqExtend(xs, newLen)
  }

  function method {:opaque} {:fuel 0, 0} FromNatWithLen(n: nat, len: nat): (xs: seq<uint>)
    requires Pow(BASE(), len) > n
    ensures |xs| == len
    ensures ToNatRight(xs) == n
    decreases n, len
  {
    LemmaFromNatLen(n, len);
    LemmaNatSeqNat(n);
    SeqExtend(FromNat(n), len)
  }

  lemma /*{:_induction xs}*/ LemmaSeqZero(xs: seq<uint>)
    requires ToNatRight(xs) == 0
    ensures forall i: int :: 0 <= i < |xs| ==> xs[i] == 0
    decreases xs
  {
    reveal ToNatRight();
    if |xs| == 0 {
    } else {
      LemmaMulNonnegativeAuto();
      assert First(xs) == 0;
      LemmaMulNonzeroAuto();
      LemmaSeqZero(DropFirst(xs));
    }
  }

  function method {:opaque} {:fuel 0, 0} SeqZero(len: nat): (xs: seq<uint>)
    ensures |xs| == len
    ensures forall i: int :: 0 <= i < |xs| ==> xs[i] == 0
    ensures ToNatRight(xs) == 0
    decreases len
  {
    LemmaPowPositive(BASE(), len);
    var xs: seq<uint> := FromNatWithLen(0, len);
    LemmaSeqZero(xs);
    xs
  }

  lemma /*{:_induction xs}*/ LemmaSeqNatSeq(xs: seq<uint>)
    ensures Pow(BASE(), |xs|) > ToNatRight(xs)
    ensures FromNatWithLen(ToNatRight(xs), |xs|) == xs
    decreases xs
  {
    reveal FromNat();
    reveal ToNatRight();
    LemmaSeqNatBound(xs);
    if |xs| > 0 {
      calc {
        FromNatWithLen(ToNatRight(xs), |xs|) != xs;
        {
          LemmaSeqNeq(FromNatWithLen(ToNatRight(xs), |xs|), xs);
        }
        ToNatRight(FromNatWithLen(ToNatRight(xs), |xs|)) != ToNatRight(xs);
        ToNatRight(xs) != ToNatRight(xs);
        false;
      }
    }
  }

  function method {:opaque} {:fuel 0, 0} SeqAdd(xs: seq<uint>, ys: seq<uint>): (seq<uint>, nat)
    requires |xs| == |ys|
    ensures var (zs: seq<uint>, cout: nat) := SeqAdd(xs, ys); |zs| == |xs| && 0 <= cout <= 1
    decreases xs
  {
    if |xs| == 0 then
      ([], 0)
    else
      var (zs': seq<uint>, cin: nat) := SeqAdd(DropLast(xs), DropLast(ys)); var sum: int := Last(xs) + Last(ys) + cin; var (sum_out: int, cout: int) := if sum < BASE() then (sum, 0) else (sum - BASE(), 1); (zs' + [sum_out], cout)
  }

  lemma /*{:_induction xs, ys, zs}*/ LemmaSeqAdd(xs: seq<uint>, ys: seq<uint>, zs: seq<uint>, cout: nat)
    requires |xs| == |ys|
    requires SeqAdd(xs, ys) == (zs, cout)
    ensures ToNatRight(xs) + ToNatRight(ys) == ToNatRight(zs) + cout * Pow(BASE(), |xs|)
    decreases xs, ys, zs, cout
  {
    reveal SeqAdd();
    if |xs| == 0 {
      reveal ToNatRight();
    } else {
      ghost var pow := Pow(BASE(), |xs| - 1);
      var (zs', cin) := SeqAdd(DropLast(xs), DropLast(ys));
      ghost var sum: int := Last(xs) + Last(ys) + cin;
      ghost var z := if sum < BASE() then sum else sum - BASE();
      assert sum == z + cout * BASE();
      reveal ToNatLeft();
      LemmaToNatLeftEqToNatRightAuto();
      calc {
        ToNatRight(zs);
        ToNatLeft(zs);
        ToNatLeft(zs') + z * pow;
        {
          LemmaSeqAdd(DropLast(xs), DropLast(ys), zs', cin);
        }
        ToNatLeft(DropLast(xs)) + ToNatLeft(DropLast(ys)) - cin * pow + z * pow;
        {
          LemmaMulEqualityAuto();
          assert sum * pow == (z + cout * BASE()) * pow;
          LemmaMulIsDistributiveAuto();
        }
        ToNatLeft(xs) + ToNatLeft(ys) - cout * BASE() * pow;
        {
          LemmaMulIsAssociative(cout, BASE(), pow);
          reveal Pow();
        }
        ToNatLeft(xs) + ToNatLeft(ys) - cout * Pow(BASE(), |xs|);
        ToNatRight(xs) + ToNatRight(ys) - cout * Pow(BASE(), |xs|);
      }
    }
  }

  function method {:opaque} {:fuel 0, 0} SeqSub(xs: seq<uint>, ys: seq<uint>): (seq<uint>, nat)
    requires |xs| == |ys|
    ensures var (zs: seq<uint>, cout: nat) := SeqSub(xs, ys); |zs| == |xs| && 0 <= cout <= 1
    decreases xs
  {
    if |xs| == 0 then
      ([], 0)
    else
      var (zs: seq<uint>, cin: nat) := SeqSub(DropLast(xs), DropLast(ys)); var (diff_out: int, cout: int) := if Last(xs) >= Last(ys) + cin then (Last(xs) - Last(ys) - cin, 0) else (BASE() + Last(xs) - Last(ys) - cin, 1); (zs + [diff_out], cout)
  }

  lemma /*{:_induction xs, ys, zs}*/ LemmaSeqSub(xs: seq<uint>, ys: seq<uint>, zs: seq<uint>, cout: nat)
    requires |xs| == |ys|
    requires SeqSub(xs, ys) == (zs, cout)
    ensures ToNatRight(xs) - ToNatRight(ys) + cout * Pow(BASE(), |xs|) == ToNatRight(zs)
    decreases xs, ys, zs, cout
  {
    reveal SeqSub();
    if |xs| == 0 {
      reveal ToNatRight();
    } else {
      ghost var pow := Pow(BASE(), |xs| - 1);
      var (zs', cin) := SeqSub(DropLast(xs), DropLast(ys));
      ghost var z := if Last(xs) >= Last(ys) + cin then Last(xs) - Last(ys) - cin else BASE() + Last(xs) - Last(ys) - cin;
      assert cout * BASE() + Last(xs) - cin - Last(ys) == z;
      reveal ToNatLeft();
      LemmaToNatLeftEqToNatRightAuto();
      calc {
        ToNatRight(zs);
        ToNatLeft(zs);
        ToNatLeft(zs') + z * pow;
        {
          LemmaSeqSub(DropLast(xs), DropLast(ys), zs', cin);
        }
        ToNatLeft(DropLast(xs)) - ToNatLeft(DropLast(ys)) + cin * pow + z * pow;
        {
          LemmaMulEqualityAuto();
          assert pow * (cout * BASE() + Last(xs) - cin - Last(ys)) == pow * z;
          LemmaMulIsDistributiveAuto();
        }
        ToNatLeft(xs) - ToNatLeft(ys) + cout * BASE() * pow;
        {
          LemmaMulIsAssociative(cout, BASE(), pow);
          reveal Pow();
        }
        ToNatLeft(xs) - ToNatLeft(ys) + cout * Pow(BASE(), |xs|);
        ToNatRight(xs) - ToNatRight(ys) + cout * Pow(BASE(), |xs|);
      }
    }
  }

  import opened DivMod

  import opened Mul

  import opened Power

  import opened Seq

  type uint = i: int
    | 0 <= i < BASE()
}

abstract module LargeSeq refines LittleEndianNat {

  import Small : SmallSeq
  function method BITS(): nat
    ensures BITS() > Small.BITS() && BITS() % Small.BITS() == 0

  function method BASE(): nat
    ensures BASE() > 1
  {
    LemmaPowPositive(2, BITS() - 1);
    LemmaPowStrictlyIncreases(2, BITS() - 1, BITS());
    Pow(2, BITS())
  }

  function method {:opaque} {:fuel 0, 0} ToNatRight(xs: seq<uint>): nat
    decreases xs
  {
    if |xs| == 0 then
      0
    else
      LemmaMulNonnegativeAuto(); ToNatRight(DropFirst(xs)) * BASE() + First(xs)
  }

  function method {:opaque} {:fuel 0, 0} ToNatLeft(xs: seq<uint>): nat
    decreases xs
  {
    if |xs| == 0 then
      0
    else
      LemmaPowPositiveAuto(); LemmaMulNonnegativeAuto(); ToNatLeft(DropLast(xs)) + Last(xs) * Pow(BASE(), |xs| - 1)
  }

  lemma {:vcs_split_on_every_assert} /*{:_induction xs}*/ LemmaToNatLeftEqToNatRight(xs: seq<uint>)
    ensures ToNatRight(xs) == ToNatLeft(xs)
    decreases xs
  {
    reveal ToNatRight();
    reveal ToNatLeft();
    if xs == [] {
    } else {
      if DropLast(xs) == [] {
        calc {
          ToNatLeft(xs);
          Last(xs) * Pow(BASE(), |xs| - 1);
          {
            reveal Pow();
          }
          Last(xs);
          First(xs);
          {
            assert ToNatRight(DropFirst(xs)) == 0;
          }
          ToNatRight(xs);
        }
      } else {
        calc {
          ToNatLeft(xs);
          ToNatLeft(DropLast(xs)) + Last(xs) * Pow(BASE(), |xs| - 1);
          {
            LemmaToNatLeftEqToNatRight(DropLast(xs));
          }
          ToNatRight(DropLast(xs)) + Last(xs) * Pow(BASE(), |xs| - 1);
          ToNatRight(DropFirst(DropLast(xs))) * BASE() + First(xs) + Last(xs) * Pow(BASE(), |xs| - 1);
          {
            LemmaToNatLeftEqToNatRight(DropFirst(DropLast(xs)));
          }
          ToNatLeft(DropFirst(DropLast(xs))) * BASE() + First(xs) + Last(xs) * Pow(BASE(), |xs| - 1);
          {
            assert DropFirst(DropLast(xs)) == DropLast(DropFirst(xs));
            reveal Pow();
            LemmaMulProperties();
          }
          ToNatLeft(DropLast(DropFirst(xs))) * BASE() + First(xs) + Last(xs) * Pow(BASE(), |xs| - 2) * BASE();
          {
            LemmaMulIsDistributiveAddOtherWayAuto();
          }
          ToNatLeft(DropFirst(xs)) * BASE() + First(xs);
          {
            LemmaToNatLeftEqToNatRight(DropFirst(xs));
          }
          ToNatRight(xs);
        }
      }
    }
  }

  lemma LemmaToNatLeftEqToNatRightAuto()
    ensures forall xs: seq<uint> :: ToNatRight(xs) == ToNatLeft(xs)
  {
    reveal ToNatRight();
    reveal ToNatLeft();
    forall xs: seq<uint> | true
      ensures ToNatRight(xs) == ToNatLeft(xs)
    {
      LemmaToNatLeftEqToNatRight(xs);
    }
  }

  lemma /*{:_induction xs}*/ LemmaSeqLen1(xs: seq<uint>)
    requires |xs| == 1
    ensures ToNatRight(xs) == First(xs)
    decreases xs
  {
    reveal ToNatRight();
  }

  lemma /*{:_induction xs}*/ LemmaSeqLen2(xs: seq<uint>)
    requires |xs| == 2
    ensures ToNatRight(xs) == First(xs) + xs[1] * BASE()
    decreases xs
  {
    reveal ToNatRight();
    LemmaSeqLen1(DropLast(xs));
  }

  lemma /*{:_induction xs}*/ LemmaSeqAppendZero(xs: seq<uint>)
    ensures ToNatRight(xs + [0]) == ToNatRight(xs)
    decreases xs
  {
    reveal ToNatLeft();
    LemmaToNatLeftEqToNatRightAuto();
    calc {
      ToNatRight(xs + [0]);
      ToNatLeft(xs + [0]);
      ToNatLeft(xs) + 0 * Pow(BASE(), |xs|);
      {
        LemmaMulBasicsAuto();
      }
      ToNatLeft(xs);
      ToNatRight(xs);
    }
  }

  lemma /*{:_induction xs}*/ LemmaSeqNatBound(xs: seq<uint>)
    ensures ToNatRight(xs) < Pow(BASE(), |xs|)
    decreases xs
  {
    reveal Pow();
    if |xs| == 0 {
      reveal ToNatRight();
    } else {
      ghost var len' := |xs| - 1;
      ghost var pow := Pow(BASE(), len');
      calc {
        ToNatRight(xs);
        {
          LemmaToNatLeftEqToNatRight(xs);
        }
        ToNatLeft(xs);
        {
          reveal ToNatLeft();
        }
        ToNatLeft(DropLast(xs)) + Last(xs) * pow;
      <
        {
          LemmaToNatLeftEqToNatRight(DropLast(xs));
          LemmaSeqNatBound(DropLast(xs));
        }
        pow + Last(xs) * pow;
      <=
        {
          LemmaPowPositiveAuto();
          LemmaMulInequalityAuto();
        }
        pow + (BASE() - 1) * pow;
        {
          LemmaMulIsDistributiveAuto();
        }
        Pow(BASE(), len' + 1);
      }
    }
  }

  lemma /*{:_induction xs, i}*/ LemmaSeqPrefix(xs: seq<uint>, i: nat)
    requires 0 <= i <= |xs|
    ensures ToNatRight(xs[..i]) + ToNatRight(xs[i..]) * Pow(BASE(), i) == ToNatRight(xs)
    decreases xs, i
  {
    reveal ToNatRight();
    reveal Pow();
    if i == 1 {
      assert ToNatRight(xs[..1]) == First(xs);
    } else if i > 1 {
      calc {
        ToNatRight(xs[..i]) + ToNatRight(xs[i..]) * Pow(BASE(), i);
        ToNatRight(DropFirst(xs[..i])) * BASE() + First(xs) + ToNatRight(xs[i..]) * Pow(BASE(), i);
        {
          assert DropFirst(xs[..i]) == DropFirst(xs)[..i - 1];
          LemmaMulProperties();
        }
        ToNatRight(DropFirst(xs)[..i - 1]) * BASE() + First(xs) + ToNatRight(xs[i..]) * Pow(BASE(), i - 1) * BASE();
        {
          LemmaMulIsDistributiveAddOtherWayAuto();
        }
        (ToNatRight(DropFirst(xs)[..i - 1]) + ToNatRight(DropFirst(xs)[i - 1..]) * Pow(BASE(), i - 1)) * BASE() + First(xs);
        {
          LemmaSeqPrefix(DropFirst(xs), i - 1);
        }
        ToNatRight(xs);
      }
    }
  }

  lemma /*{:_induction xs, ys}*/ LemmaSeqMswInequality(xs: seq<uint>, ys: seq<uint>)
    requires |xs| == |ys| > 0
    requires Last(xs) < Last(ys)
    ensures ToNatRight(xs) < ToNatRight(ys)
    decreases xs, ys
  {
    reveal ToNatLeft();
    LemmaToNatLeftEqToNatRightAuto();
    ghost var len' := |xs| - 1;
    calc {
      ToNatRight(xs);
      ToNatLeft(xs);
    <
      {
        LemmaSeqNatBound(DropLast(xs));
      }
      Pow(BASE(), len') + Last(xs) * Pow(BASE(), len');
    ==
      {
        LemmaMulIsDistributiveAuto();
      }
      (1 + Last(xs)) * Pow(BASE(), len');
    <=
      {
        LemmaPowPositiveAuto();
        LemmaMulInequalityAuto();
      }
      ToNatLeft(ys);
      ToNatRight(ys);
    }
  }

  lemma /*{:_induction xs, ys}*/ LemmaSeqPrefixNeq(xs: seq<uint>, ys: seq<uint>, i: nat)
    requires 0 <= i <= |xs| == |ys|
    requires ToNatRight(xs[..i]) != ToNatRight(ys[..i])
    ensures ToNatRight(xs) != ToNatRight(ys)
    decreases |xs| - i
  {
    if i == |xs| {
      assert xs[..i] == xs;
      assert ys[..i] == ys;
    } else {
      if xs[i] == ys[i] {
        reveal ToNatLeft();
        assert DropLast(xs[..i + 1]) == xs[..i];
        assert DropLast(ys[..i + 1]) == ys[..i];
        LemmaToNatLeftEqToNatRightAuto();
        assert ToNatRight(xs[..i + 1]) == ToNatLeft(xs[..i + 1]);
      } else if xs[i] < ys[i] {
        LemmaSeqMswInequality(xs[..i + 1], ys[..i + 1]);
      } else {
        LemmaSeqMswInequality(ys[..i + 1], xs[..i + 1]);
      }
      LemmaSeqPrefixNeq(xs, ys, i + 1);
    }
  }

  lemma /*{:_induction xs, ys}*/ LemmaSeqNeq(xs: seq<uint>, ys: seq<uint>)
    requires |xs| == |ys|
    requires xs != ys
    ensures ToNatRight(xs) != ToNatRight(ys)
    decreases xs, ys
  {
    ghost var i: nat, n: nat := 0, |xs|;
    while i < n
      invariant 0 <= i < n
      invariant xs[..i] == ys[..i]
      decreases n - i
    {
      if xs[i] != ys[i] {
        break;
      }
      i := i + 1;
    }
    assert ToNatLeft(xs[..i]) == ToNatLeft(ys[..i]);
    reveal ToNatLeft();
    assert xs[..i + 1][..i] == xs[..i];
    assert ys[..i + 1][..i] == ys[..i];
    LemmaPowPositiveAuto();
    LemmaMulStrictInequalityAuto();
    assert ToNatLeft(xs[..i + 1]) != ToNatLeft(ys[..i + 1]);
    LemmaToNatLeftEqToNatRightAuto();
    LemmaSeqPrefixNeq(xs, ys, i + 1);
  }

  lemma /*{:_induction xs, ys}*/ LemmaSeqEq(xs: seq<uint>, ys: seq<uint>)
    requires |xs| == |ys|
    requires ToNatRight(xs) == ToNatRight(ys)
    ensures xs == ys
    decreases xs, ys
  {
    calc ==> {
      xs != ys;
      {
        LemmaSeqNeq(xs, ys);
      }
      ToNatRight(xs) != ToNatRight(ys);
      false;
    }
  }

  lemma /*{:_induction xs}*/ LemmaSeqLswModEquivalence(xs: seq<uint>)
    requires |xs| >= 1
    ensures IsModEquivalent(ToNatRight(xs), First(xs), BASE())
    decreases xs
  {
    if |xs| == 1 {
      LemmaSeqLen1(xs);
      LemmaModEquivalenceAuto();
    } else {
      assert IsModEquivalent(ToNatRight(xs), First(xs), BASE()) by {
        reveal ToNatRight();
        calc ==> {
          true;
          {
            LemmaModEquivalenceAuto();
          }
          IsModEquivalent(ToNatRight(xs), ToNatRight(DropFirst(xs)) * BASE() + First(xs), BASE());
          {
            LemmaModMultiplesBasicAuto();
          }
          IsModEquivalent(ToNatRight(xs), First(xs), BASE());
        }
      }
    }
  }

  function method {:opaque} {:fuel 0, 0} FromNat(n: nat): (xs: seq<uint>)
    decreases n
  {
    if n == 0 then
      []
    else
      LemmaDivBasicsAuto(); LemmaDivDecreasesAuto(); [n % BASE()] + FromNat(n / BASE())
  }

  lemma /*{:_induction n, len}*/ LemmaFromNatLen(n: nat, len: nat)
    requires Pow(BASE(), len) > n
    ensures |FromNat(n)| <= len
    decreases n, len
  {
    reveal FromNat();
    if n == 0 {
    } else {
      calc {
        |FromNat(n)|;
      ==
        {
          LemmaDivBasicsAuto();
        }
        1 + |FromNat(n / BASE())|;
      <=
        {
          LemmaMultiplyDivideLtAuto();
          LemmaDivDecreasesAuto();
          reveal Pow();
          LemmaFromNatLen(n / BASE(), len - 1);
        }
        len;
      }
    }
  }

  lemma /*{:_induction n}*/ LemmaNatSeqNat(n: nat)
    ensures ToNatRight(FromNat(n)) == n
    decreases n
  {
    reveal ToNatRight();
    reveal FromNat();
    if n == 0 {
    } else {
      calc {
        ToNatRight(FromNat(n));
        {
          LemmaDivBasicsAuto();
        }
        ToNatRight([n % BASE()] + FromNat(n / BASE()));
        n % BASE() + ToNatRight(FromNat(n / BASE())) * BASE();
        {
          LemmaDivDecreasesAuto();
          LemmaNatSeqNat(n / BASE());
        }
        n % BASE() + n / BASE() * BASE();
        {
          LemmaFundamentalDivMod(n, BASE());
        }
        n;
      }
    }
  }

  function method {:opaque} {:fuel 0, 0} SeqExtend(xs: seq<uint>, n: nat): (ys: seq<uint>)
    requires |xs| <= n
    ensures |ys| == n
    ensures ToNatRight(ys) == ToNatRight(xs)
    decreases n - |xs|
  {
    if |xs| >= n then
      xs
    else
      LemmaSeqAppendZero(xs); SeqExtend(xs + [0], n)
  }

  function method {:opaque} {:fuel 0, 0} SeqExtendMultiple(xs: seq<uint>, n: nat): (ys: seq<uint>)
    requires n > 0
    ensures |ys| % n == 0
    ensures ToNatRight(ys) == ToNatRight(xs)
    decreases xs, n
  {
    var newLen: int := |xs| + n - |xs| % n;
    LemmaSubModNoopRight(|xs| + n, |xs|, n);
    LemmaModBasicsAuto();
    assert newLen % n == 0;
    LemmaSeqNatBound(xs);
    LemmaPowIncreasesAuto();
    SeqExtend(xs, newLen)
  }

  function method {:opaque} {:fuel 0, 0} FromNatWithLen(n: nat, len: nat): (xs: seq<uint>)
    requires Pow(BASE(), len) > n
    ensures |xs| == len
    ensures ToNatRight(xs) == n
    decreases n, len
  {
    LemmaFromNatLen(n, len);
    LemmaNatSeqNat(n);
    SeqExtend(FromNat(n), len)
  }

  lemma /*{:_induction xs}*/ LemmaSeqZero(xs: seq<uint>)
    requires ToNatRight(xs) == 0
    ensures forall i: int :: 0 <= i < |xs| ==> xs[i] == 0
    decreases xs
  {
    reveal ToNatRight();
    if |xs| == 0 {
    } else {
      LemmaMulNonnegativeAuto();
      assert First(xs) == 0;
      LemmaMulNonzeroAuto();
      LemmaSeqZero(DropFirst(xs));
    }
  }

  function method {:opaque} {:fuel 0, 0} SeqZero(len: nat): (xs: seq<uint>)
    ensures |xs| == len
    ensures forall i: int :: 0 <= i < |xs| ==> xs[i] == 0
    ensures ToNatRight(xs) == 0
    decreases len
  {
    LemmaPowPositive(BASE(), len);
    var xs: seq<uint> := FromNatWithLen(0, len);
    LemmaSeqZero(xs);
    xs
  }

  lemma /*{:_induction xs}*/ LemmaSeqNatSeq(xs: seq<uint>)
    ensures Pow(BASE(), |xs|) > ToNatRight(xs)
    ensures FromNatWithLen(ToNatRight(xs), |xs|) == xs
    decreases xs
  {
    reveal FromNat();
    reveal ToNatRight();
    LemmaSeqNatBound(xs);
    if |xs| > 0 {
      calc {
        FromNatWithLen(ToNatRight(xs), |xs|) != xs;
        {
          LemmaSeqNeq(FromNatWithLen(ToNatRight(xs), |xs|), xs);
        }
        ToNatRight(FromNatWithLen(ToNatRight(xs), |xs|)) != ToNatRight(xs);
        ToNatRight(xs) != ToNatRight(xs);
        false;
      }
    }
  }

  function method {:opaque} {:fuel 0, 0} SeqAdd(xs: seq<uint>, ys: seq<uint>): (seq<uint>, nat)
    requires |xs| == |ys|
    ensures var (zs: seq<uint>, cout: nat) := SeqAdd(xs, ys); |zs| == |xs| && 0 <= cout <= 1
    decreases xs
  {
    if |xs| == 0 then
      ([], 0)
    else
      var (zs': seq<uint>, cin: nat) := SeqAdd(DropLast(xs), DropLast(ys)); var sum: int := Last(xs) + Last(ys) + cin; var (sum_out: int, cout: int) := if sum < BASE() then (sum, 0) else (sum - BASE(), 1); (zs' + [sum_out], cout)
  }

  lemma /*{:_induction xs, ys, zs}*/ LemmaSeqAdd(xs: seq<uint>, ys: seq<uint>, zs: seq<uint>, cout: nat)
    requires |xs| == |ys|
    requires SeqAdd(xs, ys) == (zs, cout)
    ensures ToNatRight(xs) + ToNatRight(ys) == ToNatRight(zs) + cout * Pow(BASE(), |xs|)
    decreases xs, ys, zs, cout
  {
    reveal SeqAdd();
    if |xs| == 0 {
      reveal ToNatRight();
    } else {
      ghost var pow := Pow(BASE(), |xs| - 1);
      var (zs', cin) := SeqAdd(DropLast(xs), DropLast(ys));
      ghost var sum: int := Last(xs) + Last(ys) + cin;
      ghost var z := if sum < BASE() then sum else sum - BASE();
      assert sum == z + cout * BASE();
      reveal ToNatLeft();
      LemmaToNatLeftEqToNatRightAuto();
      calc {
        ToNatRight(zs);
        ToNatLeft(zs);
        ToNatLeft(zs') + z * pow;
        {
          LemmaSeqAdd(DropLast(xs), DropLast(ys), zs', cin);
        }
        ToNatLeft(DropLast(xs)) + ToNatLeft(DropLast(ys)) - cin * pow + z * pow;
        {
          LemmaMulEqualityAuto();
          assert sum * pow == (z + cout * BASE()) * pow;
          LemmaMulIsDistributiveAuto();
        }
        ToNatLeft(xs) + ToNatLeft(ys) - cout * BASE() * pow;
        {
          LemmaMulIsAssociative(cout, BASE(), pow);
          reveal Pow();
        }
        ToNatLeft(xs) + ToNatLeft(ys) - cout * Pow(BASE(), |xs|);
        ToNatRight(xs) + ToNatRight(ys) - cout * Pow(BASE(), |xs|);
      }
    }
  }

  function method {:opaque} {:fuel 0, 0} SeqSub(xs: seq<uint>, ys: seq<uint>): (seq<uint>, nat)
    requires |xs| == |ys|
    ensures var (zs: seq<uint>, cout: nat) := SeqSub(xs, ys); |zs| == |xs| && 0 <= cout <= 1
    decreases xs
  {
    if |xs| == 0 then
      ([], 0)
    else
      var (zs: seq<uint>, cin: nat) := SeqSub(DropLast(xs), DropLast(ys)); var (diff_out: int, cout: int) := if Last(xs) >= Last(ys) + cin then (Last(xs) - Last(ys) - cin, 0) else (BASE() + Last(xs) - Last(ys) - cin, 1); (zs + [diff_out], cout)
  }

  lemma /*{:_induction xs, ys, zs}*/ LemmaSeqSub(xs: seq<uint>, ys: seq<uint>, zs: seq<uint>, cout: nat)
    requires |xs| == |ys|
    requires SeqSub(xs, ys) == (zs, cout)
    ensures ToNatRight(xs) - ToNatRight(ys) + cout * Pow(BASE(), |xs|) == ToNatRight(zs)
    decreases xs, ys, zs, cout
  {
    reveal SeqSub();
    if |xs| == 0 {
      reveal ToNatRight();
    } else {
      ghost var pow := Pow(BASE(), |xs| - 1);
      var (zs', cin) := SeqSub(DropLast(xs), DropLast(ys));
      ghost var z := if Last(xs) >= Last(ys) + cin then Last(xs) - Last(ys) - cin else BASE() + Last(xs) - Last(ys) - cin;
      assert cout * BASE() + Last(xs) - cin - Last(ys) == z;
      reveal ToNatLeft();
      LemmaToNatLeftEqToNatRightAuto();
      calc {
        ToNatRight(zs);
        ToNatLeft(zs);
        ToNatLeft(zs') + z * pow;
        {
          LemmaSeqSub(DropLast(xs), DropLast(ys), zs', cin);
        }
        ToNatLeft(DropLast(xs)) - ToNatLeft(DropLast(ys)) + cin * pow + z * pow;
        {
          LemmaMulEqualityAuto();
          assert pow * (cout * BASE() + Last(xs) - cin - Last(ys)) == pow * z;
          LemmaMulIsDistributiveAuto();
        }
        ToNatLeft(xs) - ToNatLeft(ys) + cout * BASE() * pow;
        {
          LemmaMulIsAssociative(cout, BASE(), pow);
          reveal Pow();
        }
        ToNatLeft(xs) - ToNatLeft(ys) + cout * Pow(BASE(), |xs|);
        ToNatRight(xs) - ToNatRight(ys) + cout * Pow(BASE(), |xs|);
      }
    }
  }

  import opened DivMod

  import opened Mul

  import opened Power

  import opened Seq

  type uint = i: int
    | 0 <= i < BASE()
}

abstract module LittleEndianNatConversions {

  import opened DivMod

  import opened Mul

  import opened Power

  import opened Seq

  import opened Large : LargeSeq
  function method E(): (E: nat)
    ensures Pow(Small.BASE(), E) == Large.BASE()
    ensures E > 0
  {
    LemmaDivBasicsAuto();
    LemmaPowMultipliesAuto();
    LemmaFundamentalDivMod(Large.BITS(), Small.BITS());
    Large.BITS() / Small.BITS()
  }

  function method {:opaque} {:fuel 0, 0} ToSmall(xs: seq<Large.uint>): (ys: seq<Small.uint>)
    ensures |ys| == |xs| * E()
    decreases xs
  {
    if |xs| == 0 then
      []
    else
      LemmaMulIsDistributiveAddOtherWay(E(), 1, |xs| - 1); Small.FromNatWithLen(First(xs), E()) + ToSmall(DropFirst(xs))
  }

  function method {:opaque} {:fuel 0, 0} ToLarge(xs: seq<Small.uint>): (ys: seq<Large.uint>)
    requires |xs| % E() == 0
    ensures |ys| == |xs| / E()
    decreases xs
  {
    if |xs| == 0 then
      LemmaDivBasicsAuto();
      []
    else
      LemmaModIsZero(|xs|, E()); assert |xs| >= E(); Small.LemmaSeqNatBound(xs[..E()]); LemmaModSubMultiplesVanishAuto(); LemmaDivMinusOne(|xs|, E()); [Small.ToNatRight(xs[..E()]) as Large.uint] + ToLarge(xs[E()..])
  }

  lemma /*{:_induction xs}*/ LemmaToSmall(xs: seq<Large.uint>)
    ensures Small.ToNatRight(ToSmall(xs)) == Large.ToNatRight(xs)
    decreases xs
  {
  }

  lemma /*{:_induction xs}*/ LemmaToLarge(xs: seq<Small.uint>)
    requires |xs| % E() == 0
    ensures Large.ToNatRight(ToLarge(xs)) == Small.ToNatRight(xs)
    decreases xs
  {
  }

  lemma /*{:_induction xs, ys}*/ LemmaToSmallIsInjective(xs: seq<Large.uint>, ys: seq<Large.uint>)
    requires ToSmall(xs) == ToSmall(ys)
    requires |xs| == |ys|
    ensures xs == ys
    decreases xs, ys
  {
  }

  lemma /*{:_induction xs, ys}*/ LemmaToLargeIsInjective(xs: seq<Small.uint>, ys: seq<Small.uint>)
    requires |xs| % E() == |ys| % E() == 0
    requires ToLarge(xs) == ToLarge(ys)
    requires |xs| == |ys|
    ensures xs == ys
    decreases xs, ys
  {
  }

  lemma /*{:_induction xs}*/ LemmaSmallLargeSmall(xs: seq<Small.uint>)
    requires |xs| % E() == 0
    ensures ToSmall(ToLarge(xs)) == xs
    decreases xs
  {
  }

  lemma /*{:_induction xs}*/ LemmaLargeSmallLarge(xs: seq<Large.uint>)
    ensures |ToSmall(xs)| % E() == 0
    ensures ToLarge(ToSmall(xs)) == xs
    decreases xs
  {
  }
}

module Seq {

  import opened Wrappers

  import Math
  function method First<T>(s: seq<T>): T
    requires |s| > 0
    decreases s
  {
    s[0]
  }

  function method DropFirst<T>(s: seq<T>): seq<T>
    requires |s| > 0
    decreases s
  {
    s[1..]
  }

  function method Last<T>(s: seq<T>): T
    requires |s| > 0
    decreases s
  {
    s[|s| - 1]
  }

  function method DropLast<T>(s: seq<T>): seq<T>
    requires |s| > 0
    decreases s
  {
    s[..|s| - 1]
  }

  lemma LemmaLast<T>(s: seq<T>)
    requires |s| > 0
    ensures DropLast(s) + [Last(s)] == s
    decreases s
  {
  }

  lemma LemmaAppendLast<T>(a: seq<T>, b: seq<T>)
    requires 0 < |a + b| && 0 < |b|
    ensures Last(a + b) == Last(b)
    decreases a, b
  {
  }

  lemma LemmaConcatIsAssociative<T>(a: seq<T>, b: seq<T>, c: seq<T>)
    ensures a + (b + c) == a + b + c
    decreases a, b, c
  {
  }

  predicate IsPrefix<T>(a: seq<T>, b: seq<T>)
    ensures IsPrefix(a, b) ==> |a| <= |b| && a == b[..|a|]
    decreases a, b
  {
    a <= b
  }

  predicate IsSuffix<T>(a: seq<T>, b: seq<T>)
    decreases a, b
  {
    |a| <= |b| &&
    a == b[|b| - |a|..]
  }

  lemma LemmaSplitAt<T>(s: seq<T>, pos: nat)
    requires pos < |s|
    ensures s[..pos] + s[pos..] == s
    decreases s, pos
  {
  }

  lemma LemmaElementFromSlice<T>(s: seq<T>, s': seq<T>, a: int, b: int, pos: nat)
    requires 0 <= a <= b <= |s|
    requires s' == s[a .. b]
    requires a <= pos < b
    ensures pos - a < |s'|
    ensures s'[pos - a] == s[pos]
    decreases s, s', a, b, pos
  {
  }

  lemma LemmaSliceOfSlice<T>(s: seq<T>, s1: int, e1: int, s2: int, e2: int)
    requires 0 <= s1 <= e1 <= |s|
    requires 0 <= s2 <= e2 <= e1 - s1
    ensures s[s1 .. e1][s2 .. e2] == s[s1 + s2 .. s1 + e2]
    decreases s, s1, e1, s2, e2
  {
  }

  method ToArray<T>(s: seq<T>) returns (a: array<T>)
    ensures fresh(a)
    ensures a.Length == |s|
    ensures forall i: int :: 0 <= i < |s| ==> a[i] == s[i]
    decreases s
  {
    a := new T[|s|] ((i: int) requires 0 <= i < |s| => s[i]);
  }

  function method {:opaque} {:fuel 0, 0} ToSet<T>(s: seq<T>): set<T>
    decreases s
  {
    set x: T {:trigger x in s} | x in s
  }

  lemma LemmaCardinalityOfSet<T>(s: seq<T>)
    ensures |ToSet(s)| <= |s|
    decreases s
  {
  }

  lemma LemmaCardinalityOfEmptySetIs0<T>(s: seq<T>)
    ensures |ToSet(s)| == 0 <==> |s| == 0
    decreases s
  {
  }

  predicate {:opaque} {:fuel 0, 0} HasNoDuplicates<T>(s: seq<T>)
    decreases s
  {
    forall i: int, j: int {:trigger s[i], s[j]} :: 
      0 <= i < |s| &&
      0 <= j < |s| &&
      i != j ==>
        s[i] != s[j]
  }

  lemma {:timeLimitMultiplier 3} /*{:_timeLimit 30}*/ LemmaNoDuplicatesInConcat<T>(a: seq<T>, b: seq<T>)
    requires HasNoDuplicates(a)
    requires HasNoDuplicates(b)
    requires multiset(a) !! multiset(b)
    ensures HasNoDuplicates(a + b)
    decreases a, b
  {
  }

  lemma LemmaCardinalityOfSetNoDuplicates<T>(s: seq<T>)
    requires HasNoDuplicates(s)
    ensures |ToSet(s)| == |s|
    decreases s
  {
  }

  lemma LemmaNoDuplicatesCardinalityOfSet<T>(s: seq<T>)
    requires |ToSet(s)| == |s|
    ensures HasNoDuplicates(s)
    decreases s
  {
  }

  lemma LemmaMultisetHasNoDuplicates<T>(s: seq<T>)
    requires HasNoDuplicates(s)
    ensures forall x: T {:trigger multiset(s)[x]} | x in multiset(s) :: multiset(s)[x] == 1
    decreases s
  {
  }

  function method {:opaque} {:fuel 0, 0} IndexOf<T(==)>(s: seq<T>, v: T): (i: nat)
    requires v in s
    ensures i < |s| && s[i] == v
    ensures forall j: int {:trigger s[j]} :: 0 <= j < i ==> s[j] != v
    decreases s
  {
    if s[0] == v then
      0
    else
      1 + IndexOf(s[1..], v)
  }

  function method {:opaque} {:fuel 0, 0} IndexOfOption<T(==)>(s: seq<T>, v: T): (o: Option<nat>)
    ensures if o.Some? then o.value < |s| && s[o.value] == v && forall j: int {:trigger s[j]} :: 0 <= j < o.value ==> s[j] != v else v !in s
    decreases s
  {
    if |s| == 0 then
      None()
    else if s[0] == v then
      Some(0)
    else
      var o': Option<nat> := IndexOfOption(s[1..], v); if o'.Some? then Some(o'.value + 1) else None()
  }

  function method {:opaque} {:fuel 0, 0} LastIndexOf<T(==)>(s: seq<T>, v: T): (i: nat)
    requires v in s
    ensures i < |s| && s[i] == v
    ensures forall j: int {:trigger s[j]} :: i < j < |s| ==> s[j] != v
    decreases s
  {
    if s[|s| - 1] == v then
      |s| - 1
    else
      LastIndexOf(s[..|s| - 1], v)
  }

  function method {:opaque} {:fuel 0, 0} LastIndexOfOption<T(==)>(s: seq<T>, v: T): (o: Option<nat>)
    ensures if o.Some? then o.value < |s| && s[o.value] == v && forall j: int {:trigger s[j]} :: o.value < j < |s| ==> s[j] != v else v !in s
    decreases s
  {
    if |s| == 0 then
      None()
    else if s[|s| - 1] == v then
      Some(|s| - 1)
    else
      LastIndexOfOption(s[..|s| - 1], v)
  }

  function method {:opaque} {:fuel 0, 0} Remove<T>(s: seq<T>, pos: nat): (s': seq<T>)
    requires pos < |s|
    ensures |s'| == |s| - 1
    ensures forall i: int {:trigger s'[i], s[i]} | 0 <= i < pos :: s'[i] == s[i]
    ensures forall i: int {:trigger s'[i]} | pos <= i < |s| - 1 :: s'[i] == s[i + 1]
    decreases s, pos
  {
    s[..pos] + s[pos + 1..]
  }

  function method {:opaque} {:fuel 0, 0} RemoveValue<T(==)>(s: seq<T>, v: T): (s': seq<T>)
    ensures v !in s ==> s == s'
    ensures v in s ==> |multiset(s')| == |multiset(s)| - 1
    ensures v in s ==> multiset(s')[v] == multiset(s)[v] - 1
    ensures HasNoDuplicates(s) ==> HasNoDuplicates(s') && ToSet(s') == ToSet(s) - {v}
    decreases s
  {
    reveal HasNoDuplicates();
    reveal ToSet();
    if v !in s then
      s
    else
      var i: nat := IndexOf(s, v); assert s == s[..i] + [v] + s[i + 1..]; s[..i] + s[i + 1..]
  }

  function method {:opaque} {:fuel 0, 0} Insert<T>(s: seq<T>, a: T, pos: nat): seq<T>
    requires pos <= |s|
    ensures |Insert(s, a, pos)| == |s| + 1
    ensures forall i: int {:trigger Insert(s, a, pos)[i], s[i]} :: 0 <= i < pos ==> Insert(s, a, pos)[i] == s[i]
    ensures forall i: int {:trigger s[i]} :: pos <= i < |s| ==> Insert(s, a, pos)[i + 1] == s[i]
    ensures Insert(s, a, pos)[pos] == a
    ensures multiset(Insert(s, a, pos)) == multiset(s) + multiset{a}
    decreases s, pos
  {
    assert s == s[..pos] + s[pos..];
    s[..pos] + [a] + s[pos..]
  }

  function method {:opaque} {:fuel 0, 0} Reverse<T>(s: seq<T>): (s': seq<T>)
    ensures |s'| == |s|
    ensures forall i: int {:trigger s'[i]} {:trigger s[|s| - i - 1]} :: 0 <= i < |s| ==> s'[i] == s[|s| - i - 1]
    decreases s
  {
    if s == [] then
      []
    else
      [s[|s| - 1]] + Reverse(s[0 .. |s| - 1])
  }

  function method {:opaque} {:fuel 0, 0} Repeat<T>(v: T, length: nat): (s: seq<T>)
    ensures |s| == length
    ensures forall i: nat {:trigger s[i]} | i < |s| :: s[i] == v
    decreases length
  {
    if length == 0 then
      []
    else
      [v] + Repeat(v, length - 1)
  }

  function method {:opaque} {:fuel 0, 0} Unzip<A, B>(s: seq<(A, B)>): (seq<A>, seq<B>)
    ensures |Unzip(s).0| == |Unzip(s).1| == |s|
    ensures forall i: int {:trigger Unzip(s).0[i]} {:trigger Unzip(s).1[i]} :: 0 <= i < |s| ==> (Unzip(s).0[i], Unzip(s).1[i]) == s[i]
    decreases s
  {
    if |s| == 0 then
      ([], [])
    else
      var (a: seq<A>, b: seq<B>) := Unzip(DropLast(s)); (a + [Last(s).0], b + [Last(s).1])
  }

  function method {:opaque} {:fuel 0, 0} Zip<A, B>(a: seq<A>, b: seq<B>): seq<(A, B)>
    requires |a| == |b|
    ensures |Zip(a, b)| == |a|
    ensures forall i: int {:trigger Zip(a, b)[i]} :: 0 <= i < |Zip(a, b)| ==> Zip(a, b)[i] == (a[i], b[i])
    ensures Unzip(Zip(a, b)).0 == a
    ensures Unzip(Zip(a, b)).1 == b
    decreases a, b
  {
    if |a| == 0 then
      []
    else
      Zip(DropLast(a), DropLast(b)) + [(Last(a), Last(b))]
  }

  lemma /*{:_induction s}*/ LemmaZipOfUnzip<A, B>(s: seq<(A, B)>)
    ensures Zip(Unzip(s).0, Unzip(s).1) == s
    decreases s
  {
  }

  function method {:opaque} {:fuel 0, 0} Max(s: seq<int>): int
    requires 0 < |s|
    ensures forall k: int {:trigger k in s} :: k in s ==> Max(s) >= k
    ensures Max(s) in s
    decreases s
  {
    assert s == [s[0]] + s[1..];
    if |s| == 1 then
      s[0]
    else
      Math.Max(s[0], Max(s[1..]))
  }

  lemma /*{:_induction a, b}*/ LemmaMaxOfConcat(a: seq<int>, b: seq<int>)
    requires 0 < |a| && 0 < |b|
    ensures Max(a + b) >= Max(a)
    ensures Max(a + b) >= Max(b)
    ensures forall i: int {:trigger i in [Max(a + b)]} :: i in a + b ==> Max(a + b) >= i
    decreases a, b
  {
  }

  function method {:opaque} {:fuel 0, 0} Min(s: seq<int>): int
    requires 0 < |s|
    ensures forall k: int {:trigger k in s} :: k in s ==> Min(s) <= k
    ensures Min(s) in s
    decreases s
  {
    assert s == [s[0]] + s[1..];
    if |s| == 1 then
      s[0]
    else
      Math.Min(s[0], Min(s[1..]))
  }

  lemma /*{:_induction a, b}*/ LemmaMinOfConcat(a: seq<int>, b: seq<int>)
    requires 0 < |a| && 0 < |b|
    ensures Min(a + b) <= Min(a)
    ensures Min(a + b) <= Min(b)
    ensures forall i: int {:trigger i in a + b} :: i in a + b ==> Min(a + b) <= i
    decreases a, b
  {
  }

  lemma /*{:_induction s}*/ LemmaSubseqMax(s: seq<int>, from: nat, to: nat)
    requires from < to <= |s|
    ensures Max(s[from .. to]) <= Max(s)
    decreases s, from, to
  {
  }

  lemma /*{:_induction s}*/ LemmaSubseqMin(s: seq<int>, from: nat, to: nat)
    requires from < to <= |s|
    ensures Min(s[from .. to]) >= Min(s)
    decreases s, from, to
  {
  }

  function method Flatten<T>(s: seq<seq<T>>): seq<T>
    decreases |s|
  {
    if |s| == 0 then
      []
    else
      s[0] + Flatten(s[1..])
  }

  lemma /*{:_induction a, b}*/ LemmaFlattenConcat<T>(a: seq<seq<T>>, b: seq<seq<T>>)
    ensures Flatten(a + b) == Flatten(a) + Flatten(b)
    decreases a, b
  {
  }

  function method FlattenReverse<T>(s: seq<seq<T>>): seq<T>
    decreases |s|
  {
    if |s| == 0 then
      []
    else
      FlattenReverse(DropLast(s)) + Last(s)
  }

  lemma /*{:_induction a, b}*/ LemmaFlattenReverseConcat<T>(a: seq<seq<T>>, b: seq<seq<T>>)
    ensures FlattenReverse(a + b) == FlattenReverse(a) + FlattenReverse(b)
    decreases a, b
  {
  }

  lemma /*{:_induction s}*/ LemmaFlattenAndFlattenReverseAreEquivalent<T>(s: seq<seq<T>>)
    ensures Flatten(s) == FlattenReverse(s)
    decreases s
  {
  }

  lemma /*{:_induction s}*/ LemmaFlattenLengthGeSingleElementLength<T>(s: seq<seq<T>>, i: int)
    requires 0 <= i < |s|
    ensures |FlattenReverse(s)| >= |s[i]|
    decreases s, i
  {
  }

  lemma /*{:_induction s}*/ LemmaFlattenLengthLeMul<T>(s: seq<seq<T>>, j: int)
    requires forall i: int {:trigger s[i]} | 0 <= i < |s| :: |s[i]| <= j
    ensures |FlattenReverse(s)| <= |s| * j
    decreases s, j
  {
  }

  function method {:opaque} {:fuel 0, 0} Map<T, R>(f: T ~> R, s: seq<T>): (result: seq<R>)
    requires forall i: int {:trigger s[i]} :: 0 <= i < |s| ==> f.requires(s[i])
    reads set i: int, o: object? {:trigger o in f.reads(s[i])} | 0 <= i < |s| && o in f.reads(s[i]) :: o
    ensures |result| == |s|
    ensures forall i: int {:trigger result[i]} :: 0 <= i < |s| ==> result[i] == f(s[i])
    decreases set i: int, o: object? {:trigger o in f.reads(s[i])} | 0 <= i < |s| && o in f.reads(s[i]) :: o, s
  {
    if |s| == 0 then
      []
    else
      [f(s[0])] + Map(f, s[1..])
  }

  function method {:opaque} {:fuel 0, 0} MapWithResult<T, R, E>(f: T ~> Result<R, E>, s: seq<T>): (result: Result<seq<R>, E>)
    requires forall i: int :: 0 <= i < |s| ==> f.requires(s[i])
    reads set i: int, o: object? {:trigger o in f.reads(s[i])} | 0 <= i < |s| && o in f.reads(s[i]) :: o
    ensures result.Success? ==> |result.value| == |s| && forall i: int :: 0 <= i < |s| ==> f(s[i]).Success? && result.value[i] == f(s[i]).value
    decreases set i: int, o: object? {:trigger o in f.reads(s[i])} | 0 <= i < |s| && o in f.reads(s[i]) :: o, s
  {
    if |s| == 0 then
      Success([])
    else
      var head: R :- f(s[0]); var tail: seq<R> :- MapWithResult(f, s[1..]); Success([head] + tail)
  }

  lemma {:opaque} /*{:_induction f, a, b}*/ LemmaMapDistributesOverConcat<T, R>(f: T ~> R, a: seq<T>, b: seq<T>)
    requires forall i: int {:trigger a[i]} :: 0 <= i < |a| ==> f.requires(a[i])
    requires forall j: int {:trigger b[j]} :: 0 <= j < |b| ==> f.requires(b[j])
    ensures Map(f, a + b) == Map(f, a) + Map(f, b)
    decreases a, b
  {
  }

  function method {:opaque} {:fuel 0, 0} Filter<T>(f: T ~> bool, s: seq<T>): (result: seq<T>)
    requires forall i: int :: 0 <= i < |s| ==> f.requires(s[i])
    reads f.reads
    ensures |result| <= |s|
    ensures forall i: nat {:trigger result[i]} :: i < |result| && f.requires(result[i]) ==> f(result[i])
    decreases set _x0: T, _o0: object? | _o0 in f.reads(_x0) :: _o0, s
  {
    if |s| == 0 then
      []
    else
      (if f(s[0]) then [s[0]] else []) + Filter(f, s[1..])
  }

  lemma {:opaque} /*{:_induction f, a, b}*/ LemmaFilterDistributesOverConcat<T>(f: T ~> bool, a: seq<T>, b: seq<T>)
    requires forall i: int {:trigger a[i]} :: 0 <= i < |a| ==> f.requires(a[i])
    requires forall j: int {:trigger b[j]} :: 0 <= j < |b| ==> f.requires(b[j])
    ensures Filter(f, a + b) == Filter(f, a) + Filter(f, b)
    decreases a, b
  {
  }

  function method {:opaque} {:fuel 0, 0} FoldLeft<A, T>(f: (A, T) -> A, init: A, s: seq<T>): A
    decreases s
  {
    if |s| == 0 then
      init
    else
      FoldLeft(f, f(init, s[0]), s[1..])
  }

  lemma {:opaque} /*{:_induction f, a, b}*/ LemmaFoldLeftDistributesOverConcat<A, T>(f: (A, T) -> A, init: A, a: seq<T>, b: seq<T>)
    requires 0 <= |a + b|
    ensures FoldLeft(f, init, a + b) == FoldLeft(f, FoldLeft(f, init, a), b)
    decreases a, b
  {
  }

  predicate InvFoldLeft<A(!new), B(!new)>(inv: (B, seq<A>) -> bool, stp: (B, A, B) -> bool)
  {
    forall x: A, xs: seq<A>, b: B, b': B :: 
      inv(b, [x] + xs) &&
      stp(b, x, b') ==>
        inv(b', xs)
  }

  lemma /*{:_induction f, xs}*/ LemmaInvFoldLeft<A, B>(inv: (B, seq<A>) -> bool, stp: (B, A, B) -> bool, f: (B, A) -> B, b: B, xs: seq<A>)
    requires InvFoldLeft(inv, stp)
    requires forall b: B, a: A :: stp(b, a, f(b, a))
    requires inv(b, xs)
    ensures inv(FoldLeft(f, b, xs), [])
    decreases xs
  {
  }

  function method {:opaque} {:fuel 0, 0} FoldRight<A, T>(f: (T, A) -> A, s: seq<T>, init: A): A
    decreases s
  {
    if |s| == 0 then
      init
    else
      f(s[0], FoldRight(f, s[1..], init))
  }

  lemma {:opaque} /*{:_induction f, a, b}*/ LemmaFoldRightDistributesOverConcat<A, T>(f: (T, A) -> A, init: A, a: seq<T>, b: seq<T>)
    requires 0 <= |a + b|
    ensures FoldRight(f, a + b, init) == FoldRight(f, a, FoldRight(f, b, init))
    decreases a, b
  {
  }

  predicate InvFoldRight<A(!new), B(!new)>(inv: (seq<A>, B) -> bool, stp: (A, B, B) -> bool)
  {
    forall x: A, xs: seq<A>, b: B, b': B :: 
      inv(xs, b) &&
      stp(x, b, b') ==>
        inv([x] + xs, b')
  }

  lemma /*{:_induction f, xs}*/ LemmaInvFoldRight<A, B>(inv: (seq<A>, B) -> bool, stp: (A, B, B) -> bool, f: (A, B) -> B, b: B, xs: seq<A>)
    requires InvFoldRight(inv, stp)
    requires forall a: A, b: B :: stp(a, b, f(a, b))
    requires inv([], b)
    ensures inv(xs, FoldRight(f, xs, b))
    decreases xs
  {
  }
}

abstract module LittleEndianNat {

  import opened DivMod

  import opened Mul

  import opened Power

  import opened Seq
  type uint = i: int
    | 0 <= i < BASE()

  function method BASE(): nat
    ensures BASE() > 1

  function method {:opaque} {:fuel 0, 0} ToNatRight(xs: seq<uint>): nat
    decreases xs
  {
    if |xs| == 0 then
      0
    else
      LemmaMulNonnegativeAuto(); ToNatRight(DropFirst(xs)) * BASE() + First(xs)
  }

  function method {:opaque} {:fuel 0, 0} ToNatLeft(xs: seq<uint>): nat
    decreases xs
  {
    if |xs| == 0 then
      0
    else
      LemmaPowPositiveAuto(); LemmaMulNonnegativeAuto(); ToNatLeft(DropLast(xs)) + Last(xs) * Pow(BASE(), |xs| - 1)
  }

  lemma {:vcs_split_on_every_assert} /*{:_induction xs}*/ LemmaToNatLeftEqToNatRight(xs: seq<uint>)
    ensures ToNatRight(xs) == ToNatLeft(xs)
    decreases xs
  {
  }

  lemma LemmaToNatLeftEqToNatRightAuto()
    ensures forall xs: seq<uint> :: ToNatRight(xs) == ToNatLeft(xs)
  {
  }

  lemma /*{:_induction xs}*/ LemmaSeqLen1(xs: seq<uint>)
    requires |xs| == 1
    ensures ToNatRight(xs) == First(xs)
    decreases xs
  {
  }

  lemma /*{:_induction xs}*/ LemmaSeqLen2(xs: seq<uint>)
    requires |xs| == 2
    ensures ToNatRight(xs) == First(xs) + xs[1] * BASE()
    decreases xs
  {
  }

  lemma /*{:_induction xs}*/ LemmaSeqAppendZero(xs: seq<uint>)
    ensures ToNatRight(xs + [0]) == ToNatRight(xs)
    decreases xs
  {
  }

  lemma /*{:_induction xs}*/ LemmaSeqNatBound(xs: seq<uint>)
    ensures ToNatRight(xs) < Pow(BASE(), |xs|)
    decreases xs
  {
  }

  lemma /*{:_induction xs, i}*/ LemmaSeqPrefix(xs: seq<uint>, i: nat)
    requires 0 <= i <= |xs|
    ensures ToNatRight(xs[..i]) + ToNatRight(xs[i..]) * Pow(BASE(), i) == ToNatRight(xs)
    decreases xs, i
  {
  }

  lemma /*{:_induction xs, ys}*/ LemmaSeqMswInequality(xs: seq<uint>, ys: seq<uint>)
    requires |xs| == |ys| > 0
    requires Last(xs) < Last(ys)
    ensures ToNatRight(xs) < ToNatRight(ys)
    decreases xs, ys
  {
  }

  lemma /*{:_induction xs, ys}*/ LemmaSeqPrefixNeq(xs: seq<uint>, ys: seq<uint>, i: nat)
    requires 0 <= i <= |xs| == |ys|
    requires ToNatRight(xs[..i]) != ToNatRight(ys[..i])
    ensures ToNatRight(xs) != ToNatRight(ys)
    decreases |xs| - i
  {
  }

  lemma /*{:_induction xs, ys}*/ LemmaSeqNeq(xs: seq<uint>, ys: seq<uint>)
    requires |xs| == |ys|
    requires xs != ys
    ensures ToNatRight(xs) != ToNatRight(ys)
    decreases xs, ys
  {
  }

  lemma /*{:_induction xs, ys}*/ LemmaSeqEq(xs: seq<uint>, ys: seq<uint>)
    requires |xs| == |ys|
    requires ToNatRight(xs) == ToNatRight(ys)
    ensures xs == ys
    decreases xs, ys
  {
  }

  lemma /*{:_induction xs}*/ LemmaSeqLswModEquivalence(xs: seq<uint>)
    requires |xs| >= 1
    ensures IsModEquivalent(ToNatRight(xs), First(xs), BASE())
    decreases xs
  {
  }

  function method {:opaque} {:fuel 0, 0} FromNat(n: nat): (xs: seq<uint>)
    decreases n
  {
    if n == 0 then
      []
    else
      LemmaDivBasicsAuto(); LemmaDivDecreasesAuto(); [n % BASE()] + FromNat(n / BASE())
  }

  lemma /*{:_induction n, len}*/ LemmaFromNatLen(n: nat, len: nat)
    requires Pow(BASE(), len) > n
    ensures |FromNat(n)| <= len
    decreases n, len
  {
  }

  lemma /*{:_induction n}*/ LemmaNatSeqNat(n: nat)
    ensures ToNatRight(FromNat(n)) == n
    decreases n
  {
  }

  function method {:opaque} {:fuel 0, 0} SeqExtend(xs: seq<uint>, n: nat): (ys: seq<uint>)
    requires |xs| <= n
    ensures |ys| == n
    ensures ToNatRight(ys) == ToNatRight(xs)
    decreases n - |xs|
  {
    if |xs| >= n then
      xs
    else
      LemmaSeqAppendZero(xs); SeqExtend(xs + [0], n)
  }

  function method {:opaque} {:fuel 0, 0} SeqExtendMultiple(xs: seq<uint>, n: nat): (ys: seq<uint>)
    requires n > 0
    ensures |ys| % n == 0
    ensures ToNatRight(ys) == ToNatRight(xs)
    decreases xs, n
  {
    var newLen: int := |xs| + n - |xs| % n;
    LemmaSubModNoopRight(|xs| + n, |xs|, n);
    LemmaModBasicsAuto();
    assert newLen % n == 0;
    LemmaSeqNatBound(xs);
    LemmaPowIncreasesAuto();
    SeqExtend(xs, newLen)
  }

  function method {:opaque} {:fuel 0, 0} FromNatWithLen(n: nat, len: nat): (xs: seq<uint>)
    requires Pow(BASE(), len) > n
    ensures |xs| == len
    ensures ToNatRight(xs) == n
    decreases n, len
  {
    LemmaFromNatLen(n, len);
    LemmaNatSeqNat(n);
    SeqExtend(FromNat(n), len)
  }

  lemma /*{:_induction xs}*/ LemmaSeqZero(xs: seq<uint>)
    requires ToNatRight(xs) == 0
    ensures forall i: int :: 0 <= i < |xs| ==> xs[i] == 0
    decreases xs
  {
  }

  function method {:opaque} {:fuel 0, 0} SeqZero(len: nat): (xs: seq<uint>)
    ensures |xs| == len
    ensures forall i: int :: 0 <= i < |xs| ==> xs[i] == 0
    ensures ToNatRight(xs) == 0
    decreases len
  {
    LemmaPowPositive(BASE(), len);
    var xs: seq<uint> := FromNatWithLen(0, len);
    LemmaSeqZero(xs);
    xs
  }

  lemma /*{:_induction xs}*/ LemmaSeqNatSeq(xs: seq<uint>)
    ensures Pow(BASE(), |xs|) > ToNatRight(xs)
    ensures FromNatWithLen(ToNatRight(xs), |xs|) == xs
    decreases xs
  {
  }

  function method {:opaque} {:fuel 0, 0} SeqAdd(xs: seq<uint>, ys: seq<uint>): (seq<uint>, nat)
    requires |xs| == |ys|
    ensures var (zs: seq<uint>, cout: nat) := SeqAdd(xs, ys); |zs| == |xs| && 0 <= cout <= 1
    decreases xs
  {
    if |xs| == 0 then
      ([], 0)
    else
      var (zs': seq<uint>, cin: nat) := SeqAdd(DropLast(xs), DropLast(ys)); var sum: int := Last(xs) + Last(ys) + cin; var (sum_out: int, cout: int) := if sum < BASE() then (sum, 0) else (sum - BASE(), 1); (zs' + [sum_out], cout)
  }

  lemma /*{:_induction xs, ys, zs}*/ LemmaSeqAdd(xs: seq<uint>, ys: seq<uint>, zs: seq<uint>, cout: nat)
    requires |xs| == |ys|
    requires SeqAdd(xs, ys) == (zs, cout)
    ensures ToNatRight(xs) + ToNatRight(ys) == ToNatRight(zs) + cout * Pow(BASE(), |xs|)
    decreases xs, ys, zs, cout
  {
  }

  function method {:opaque} {:fuel 0, 0} SeqSub(xs: seq<uint>, ys: seq<uint>): (seq<uint>, nat)
    requires |xs| == |ys|
    ensures var (zs: seq<uint>, cout: nat) := SeqSub(xs, ys); |zs| == |xs| && 0 <= cout <= 1
    decreases xs
  {
    if |xs| == 0 then
      ([], 0)
    else
      var (zs: seq<uint>, cin: nat) := SeqSub(DropLast(xs), DropLast(ys)); var (diff_out: int, cout: int) := if Last(xs) >= Last(ys) + cin then (Last(xs) - Last(ys) - cin, 0) else (BASE() + Last(xs) - Last(ys) - cin, 1); (zs + [diff_out], cout)
  }

  lemma /*{:_induction xs, ys, zs}*/ LemmaSeqSub(xs: seq<uint>, ys: seq<uint>, zs: seq<uint>, cout: nat)
    requires |xs| == |ys|
    requires SeqSub(xs, ys) == (zs, cout)
    ensures ToNatRight(xs) - ToNatRight(ys) + cout * Pow(BASE(), |xs|) == ToNatRight(zs)
    decreases xs, ys, zs, cout
  {
  }
}

module srcCollectionsSequencesUint8_32dfyUnitTests {

  import Uint8_32

  import Uint8Seq = Uint8_32.Uint8Seq

  import Uint32Seq = Uint8_32.Uint32Seq

  import DivMod

  import DivInternalsNonlinear

  import DivInternals

  import GeneralInternals

  import ModInternals

  import MulInternals

  import MulInternalsNonlinear

  import Mul

  import ModInternalsNonlinear

  import Power

  import Seq

  import Wrappers

  import Math
  method {:test} test0()
  {
    var d0: seq<Uint8_32.Uint8Seq.uint> := [];
    var r0 := Uint8_32.Uint8Seq.ToNatRight(d0);
  }

  method {:test} test1()
  {
    var d0: seq<Uint8_32.Uint8Seq.uint> := [];
    var r0 := Uint8_32.Uint8Seq.ToNatLeft(d0);
  }

  method {:test} test2()
  {
    var r0 := Uint8_32.Uint8Seq.FromNat(65 as nat);
  }

  method {:test} test3()
  {
    var r0 := Uint8_32.Uint8Seq.FromNat(0 as nat);
  }

  method {:test} test4()
  {
    var d0: seq<Uint8_32.Uint8Seq.uint> := [0 as Uint8_32.Uint8Seq.uint];
    expect |d0| <= 1 as nat, ""Test does not meet preconditions and should be removed""
    var r0 := Uint8_32.Uint8Seq.SeqExtend(d0, 1 as nat);
    expect |r0| == 1 as nat, ""expectation violation""
    expect Uint8_32.Uint8Seq.ToNatRight(r0) == Uint8_32.Uint8Seq.ToNatRight(d0), ""expectation violation""
  }

  method {:test} test5()
  {
    var d0: seq<Uint8_32.Uint8Seq.uint> := [0 as Uint8_32.Uint8Seq.uint, 0 as Uint8_32.Uint8Seq.uint];
    var d1: seq<Uint8_32.Uint8Seq.uint> := [0 as Uint8_32.Uint8Seq.uint, 0 as Uint8_32.Uint8Seq.uint];
    expect |d0| == |d1|, ""Test does not meet preconditions and should be removed""
    var r0 := Uint8_32.Uint8Seq.SeqAdd(d0, d1);
  }

  method {:test} test6()
  {
    var d0: seq<Uint8_32.Uint8Seq.uint> := [12 as Uint8_32.Uint8Seq.uint, 2283 as Uint8_32.Uint8Seq.uint];
    var d1: seq<Uint8_32.Uint8Seq.uint> := [281 as Uint8_32.Uint8Seq.uint, 11138 as Uint8_32.Uint8Seq.uint];
    expect |d0| == |d1|, ""Test does not meet preconditions and should be removed""
    var r0 := Uint8_32.Uint8Seq.SeqAdd(d0, d1);
  }

  method {:test} test7()
  {
    var d0: seq<Uint8_32.Uint8Seq.uint> := [];
    var d1: seq<Uint8_32.Uint8Seq.uint> := [];
    expect |d0| == |d1|, ""Test does not meet preconditions and should be removed""
    var r0 := Uint8_32.Uint8Seq.SeqAdd(d0, d1);
  }

  method {:test} test8()
  {
    var d0: seq<Uint8_32.Uint8Seq.uint> := [1325 as Uint8_32.Uint8Seq.uint, 2331 as Uint8_32.Uint8Seq.uint];
    var d1: seq<Uint8_32.Uint8Seq.uint> := [234 as Uint8_32.Uint8Seq.uint, 1796 as Uint8_32.Uint8Seq.uint];
    expect |d0| == |d1|, ""Test does not meet preconditions and should be removed""
    var r0 := Uint8_32.Uint8Seq.SeqSub(d0, d1);
  }

  method {:test} test9()
  {
    var d0: seq<Uint8_32.Uint8Seq.uint> := [920 as Uint8_32.Uint8Seq.uint, 2061 as Uint8_32.Uint8Seq.uint];
    var d1: seq<Uint8_32.Uint8Seq.uint> := [645 as Uint8_32.Uint8Seq.uint, 2062 as Uint8_32.Uint8Seq.uint];
    expect |d0| == |d1|, ""Test does not meet preconditions and should be removed""
    var r0 := Uint8_32.Uint8Seq.SeqSub(d0, d1);
  }

  method {:test} test10()
  {
    var d0: seq<Uint8_32.Uint8Seq.uint> := [];
    var d1: seq<Uint8_32.Uint8Seq.uint> := [];
    expect |d0| == |d1|, ""Test does not meet preconditions and should be removed""
    var r0 := Uint8_32.Uint8Seq.SeqSub(d0, d1);
  }

  method {:test} test11()
  {
    var d0: seq<Uint8_32.Uint32Seq.uint> := [];
    var r0 := Uint8_32.Uint32Seq.ToNatRight(d0);
  }

  method {:test} test12()
  {
    var d0: seq<Uint8_32.Uint32Seq.uint> := [];
    var r0 := Uint8_32.Uint32Seq.ToNatLeft(d0);
  }

  method {:test} test13()
  {
    var r0 := Uint8_32.Uint32Seq.FromNat(65 as nat);
  }

  method {:test} test14()
  {
    var r0 := Uint8_32.Uint32Seq.FromNat(0 as nat);
  }

  method {:test} test15()
  {
    var d0: seq<Uint8_32.Uint32Seq.uint> := [0 as Uint8_32.Uint32Seq.uint];
    expect |d0| <= 1 as nat, ""Test does not meet preconditions and should be removed""
    var r0 := Uint8_32.Uint32Seq.SeqExtend(d0, 1 as nat);
    expect |r0| == 1 as nat, ""expectation violation""
    expect Uint8_32.Uint32Seq.ToNatRight(r0) == Uint8_32.Uint32Seq.ToNatRight(d0), ""expectation violation""
  }

  method {:test} test16()
  {
    var d0: seq<Uint8_32.Uint32Seq.uint> := [0 as Uint8_32.Uint32Seq.uint, 0 as Uint8_32.Uint32Seq.uint];
    var d1: seq<Uint8_32.Uint32Seq.uint> := [0 as Uint8_32.Uint32Seq.uint, 0 as Uint8_32.Uint32Seq.uint];
    expect |d0| == |d1|, ""Test does not meet preconditions and should be removed""
    var r0 := Uint8_32.Uint32Seq.SeqAdd(d0, d1);
  }

  method {:test} test17()
  {
    var d0: seq<Uint8_32.Uint32Seq.uint> := [342 as Uint8_32.Uint32Seq.uint, 4720 as Uint8_32.Uint32Seq.uint];
    var d1: seq<Uint8_32.Uint32Seq.uint> := [281 as Uint8_32.Uint32Seq.uint, 2283 as Uint8_32.Uint32Seq.uint];
    expect |d0| == |d1|, ""Test does not meet preconditions and should be removed""
    var r0 := Uint8_32.Uint32Seq.SeqAdd(d0, d1);
  }

  method {:test} test18()
  {
    var d0: seq<Uint8_32.Uint32Seq.uint> := [];
    var d1: seq<Uint8_32.Uint32Seq.uint> := [];
    expect |d0| == |d1|, ""Test does not meet preconditions and should be removed""
    var r0 := Uint8_32.Uint32Seq.SeqAdd(d0, d1);
  }

  method {:test} test19()
  {
    var d0: seq<Uint8_32.Uint32Seq.uint> := [1325 as Uint8_32.Uint32Seq.uint, 2331 as Uint8_32.Uint32Seq.uint];
    var d1: seq<Uint8_32.Uint32Seq.uint> := [234 as Uint8_32.Uint32Seq.uint, 1796 as Uint8_32.Uint32Seq.uint];
    expect |d0| == |d1|, ""Test does not meet preconditions and should be removed""
    var r0 := Uint8_32.Uint32Seq.SeqSub(d0, d1);
  }

  method {:test} test20()
  {
    var d0: seq<Uint8_32.Uint32Seq.uint> := [920 as Uint8_32.Uint32Seq.uint, 2061 as Uint8_32.Uint32Seq.uint];
    var d1: seq<Uint8_32.Uint32Seq.uint> := [645 as Uint8_32.Uint32Seq.uint, 2062 as Uint8_32.Uint32Seq.uint];
    expect |d0| == |d1|, ""Test does not meet preconditions and should be removed""
    var r0 := Uint8_32.Uint32Seq.SeqSub(d0, d1);
  }

  method {:test} test21()
  {
    var d0: seq<Uint8_32.Uint32Seq.uint> := [];
    var d1: seq<Uint8_32.Uint32Seq.uint> := [];
    expect |d0| == |d1|, ""Test does not meet preconditions and should be removed""
    var r0 := Uint8_32.Uint32Seq.SeqSub(d0, d1);
  }

  method {:test} test22()
  {
    var d0: seq<Uint8_32.Uint32Seq.uint> := [];
    var r0 := Uint8_32.ToSmall(d0);
    expect |r0| == |d0| * Uint8_32.E(), ""expectation violation""
  }
}

module Uint8_32 refines LittleEndianNatConversions {

  module {:extern ""Uint8__32_mUint8Seq_Compile""} Uint8Seq refines SmallSeq {
    function method BITS(): nat
      ensures BITS() > 1
    {
      8
    }

    function method BASE(): nat
      ensures BASE() > 1
    {
      LemmaPowPositive(2, BITS() - 1);
      LemmaPowStrictlyIncreases(2, BITS() - 1, BITS());
      Pow(2, BITS())
    }

    function method {:opaque} {:fuel 0, 0} ToNatRight(xs: seq<uint>): nat
      decreases xs
    {
      if |xs| == 0 then
        0
      else
        LemmaMulNonnegativeAuto(); ToNatRight(DropFirst(xs)) * BASE() + First(xs)
    }

    function method {:opaque} {:fuel 0, 0} ToNatLeft(xs: seq<uint>): nat
      decreases xs
    {
      if |xs| == 0 then
        0
      else
        LemmaPowPositiveAuto(); LemmaMulNonnegativeAuto(); ToNatLeft(DropLast(xs)) + Last(xs) * Pow(BASE(), |xs| - 1)
    }

    lemma {:vcs_split_on_every_assert} /*{:_induction xs}*/ LemmaToNatLeftEqToNatRight(xs: seq<uint>)
      ensures ToNatRight(xs) == ToNatLeft(xs)
      decreases xs
    {
      reveal ToNatRight();
      reveal ToNatLeft();
      if xs == [] {
      } else {
        if DropLast(xs) == [] {
          calc {
            ToNatLeft(xs);
            Last(xs) * Pow(BASE(), |xs| - 1);
            {
              reveal Pow();
            }
            Last(xs);
            First(xs);
            {
              assert ToNatRight(DropFirst(xs)) == 0;
            }
            ToNatRight(xs);
          }
        } else {
          calc {
            ToNatLeft(xs);
            ToNatLeft(DropLast(xs)) + Last(xs) * Pow(BASE(), |xs| - 1);
            {
              LemmaToNatLeftEqToNatRight(DropLast(xs));
            }
            ToNatRight(DropLast(xs)) + Last(xs) * Pow(BASE(), |xs| - 1);
            ToNatRight(DropFirst(DropLast(xs))) * BASE() + First(xs) + Last(xs) * Pow(BASE(), |xs| - 1);
            {
              LemmaToNatLeftEqToNatRight(DropFirst(DropLast(xs)));
            }
            ToNatLeft(DropFirst(DropLast(xs))) * BASE() + First(xs) + Last(xs) * Pow(BASE(), |xs| - 1);
            {
              assert DropFirst(DropLast(xs)) == DropLast(DropFirst(xs));
              reveal Pow();
              LemmaMulProperties();
            }
            ToNatLeft(DropLast(DropFirst(xs))) * BASE() + First(xs) + Last(xs) * Pow(BASE(), |xs| - 2) * BASE();
            {
              LemmaMulIsDistributiveAddOtherWayAuto();
            }
            ToNatLeft(DropFirst(xs)) * BASE() + First(xs);
            {
              LemmaToNatLeftEqToNatRight(DropFirst(xs));
            }
            ToNatRight(xs);
          }
        }
      }
    }

    lemma LemmaToNatLeftEqToNatRightAuto()
      ensures forall xs: seq<uint> :: ToNatRight(xs) == ToNatLeft(xs)
    {
      reveal ToNatRight();
      reveal ToNatLeft();
      forall xs: seq<uint> | true
        ensures ToNatRight(xs) == ToNatLeft(xs)
      {
        LemmaToNatLeftEqToNatRight(xs);
      }
    }

    lemma /*{:_induction xs}*/ LemmaSeqLen1(xs: seq<uint>)
      requires |xs| == 1
      ensures ToNatRight(xs) == First(xs)
      decreases xs
    {
      reveal ToNatRight();
    }

    lemma /*{:_induction xs}*/ LemmaSeqLen2(xs: seq<uint>)
      requires |xs| == 2
      ensures ToNatRight(xs) == First(xs) + xs[1] * BASE()
      decreases xs
    {
      reveal ToNatRight();
      LemmaSeqLen1(DropLast(xs));
    }

    lemma /*{:_induction xs}*/ LemmaSeqAppendZero(xs: seq<uint>)
      ensures ToNatRight(xs + [0]) == ToNatRight(xs)
      decreases xs
    {
      reveal ToNatLeft();
      LemmaToNatLeftEqToNatRightAuto();
      calc {
        ToNatRight(xs + [0]);
        ToNatLeft(xs + [0]);
        ToNatLeft(xs) + 0 * Pow(BASE(), |xs|);
        {
          LemmaMulBasicsAuto();
        }
        ToNatLeft(xs);
        ToNatRight(xs);
      }
    }

    lemma /*{:_induction xs}*/ LemmaSeqNatBound(xs: seq<uint>)
      ensures ToNatRight(xs) < Pow(BASE(), |xs|)
      decreases xs
    {
      reveal Pow();
      if |xs| == 0 {
        reveal ToNatRight();
      } else {
        ghost var len' := |xs| - 1;
        ghost var pow := Pow(BASE(), len');
        calc {
          ToNatRight(xs);
          {
            LemmaToNatLeftEqToNatRight(xs);
          }
          ToNatLeft(xs);
          {
            reveal ToNatLeft();
          }
          ToNatLeft(DropLast(xs)) + Last(xs) * pow;
        <
          {
            LemmaToNatLeftEqToNatRight(DropLast(xs));
            LemmaSeqNatBound(DropLast(xs));
          }
          pow + Last(xs) * pow;
        <=
          {
            LemmaPowPositiveAuto();
            LemmaMulInequalityAuto();
          }
          pow + (BASE() - 1) * pow;
          {
            LemmaMulIsDistributiveAuto();
          }
          Pow(BASE(), len' + 1);
        }
      }
    }

    lemma /*{:_induction xs, i}*/ LemmaSeqPrefix(xs: seq<uint>, i: nat)
      requires 0 <= i <= |xs|
      ensures ToNatRight(xs[..i]) + ToNatRight(xs[i..]) * Pow(BASE(), i) == ToNatRight(xs)
      decreases xs, i
    {
      reveal ToNatRight();
      reveal Pow();
      if i == 1 {
        assert ToNatRight(xs[..1]) == First(xs);
      } else if i > 1 {
        calc {
          ToNatRight(xs[..i]) + ToNatRight(xs[i..]) * Pow(BASE(), i);
          ToNatRight(DropFirst(xs[..i])) * BASE() + First(xs) + ToNatRight(xs[i..]) * Pow(BASE(), i);
          {
            assert DropFirst(xs[..i]) == DropFirst(xs)[..i - 1];
            LemmaMulProperties();
          }
          ToNatRight(DropFirst(xs)[..i - 1]) * BASE() + First(xs) + ToNatRight(xs[i..]) * Pow(BASE(), i - 1) * BASE();
          {
            LemmaMulIsDistributiveAddOtherWayAuto();
          }
          (ToNatRight(DropFirst(xs)[..i - 1]) + ToNatRight(DropFirst(xs)[i - 1..]) * Pow(BASE(), i - 1)) * BASE() + First(xs);
          {
            LemmaSeqPrefix(DropFirst(xs), i - 1);
          }
          ToNatRight(xs);
        }
      }
    }

    lemma /*{:_induction xs, ys}*/ LemmaSeqMswInequality(xs: seq<uint>, ys: seq<uint>)
      requires |xs| == |ys| > 0
      requires Last(xs) < Last(ys)
      ensures ToNatRight(xs) < ToNatRight(ys)
      decreases xs, ys
    {
      reveal ToNatLeft();
      LemmaToNatLeftEqToNatRightAuto();
      ghost var len' := |xs| - 1;
      calc {
        ToNatRight(xs);
        ToNatLeft(xs);
      <
        {
          LemmaSeqNatBound(DropLast(xs));
        }
        Pow(BASE(), len') + Last(xs) * Pow(BASE(), len');
      ==
        {
          LemmaMulIsDistributiveAuto();
        }
        (1 + Last(xs)) * Pow(BASE(), len');
      <=
        {
          LemmaPowPositiveAuto();
          LemmaMulInequalityAuto();
        }
        ToNatLeft(ys);
        ToNatRight(ys);
      }
    }

    lemma /*{:_induction xs, ys}*/ LemmaSeqPrefixNeq(xs: seq<uint>, ys: seq<uint>, i: nat)
      requires 0 <= i <= |xs| == |ys|
      requires ToNatRight(xs[..i]) != ToNatRight(ys[..i])
      ensures ToNatRight(xs) != ToNatRight(ys)
      decreases |xs| - i
    {
      if i == |xs| {
        assert xs[..i] == xs;
        assert ys[..i] == ys;
      } else {
        if xs[i] == ys[i] {
          reveal ToNatLeft();
          assert DropLast(xs[..i + 1]) == xs[..i];
          assert DropLast(ys[..i + 1]) == ys[..i];
          LemmaToNatLeftEqToNatRightAuto();
          assert ToNatRight(xs[..i + 1]) == ToNatLeft(xs[..i + 1]);
        } else if xs[i] < ys[i] {
          LemmaSeqMswInequality(xs[..i + 1], ys[..i + 1]);
        } else {
          LemmaSeqMswInequality(ys[..i + 1], xs[..i + 1]);
        }
        LemmaSeqPrefixNeq(xs, ys, i + 1);
      }
    }

    lemma /*{:_induction xs, ys}*/ LemmaSeqNeq(xs: seq<uint>, ys: seq<uint>)
      requires |xs| == |ys|
      requires xs != ys
      ensures ToNatRight(xs) != ToNatRight(ys)
      decreases xs, ys
    {
      ghost var i: nat, n: nat := 0, |xs|;
      while i < n
        invariant 0 <= i < n
        invariant xs[..i] == ys[..i]
        decreases n - i
      {
        if xs[i] != ys[i] {
          break;
        }
        i := i + 1;
      }
      assert ToNatLeft(xs[..i]) == ToNatLeft(ys[..i]);
      reveal ToNatLeft();
      assert xs[..i + 1][..i] == xs[..i];
      assert ys[..i + 1][..i] == ys[..i];
      LemmaPowPositiveAuto();
      LemmaMulStrictInequalityAuto();
      assert ToNatLeft(xs[..i + 1]) != ToNatLeft(ys[..i + 1]);
      LemmaToNatLeftEqToNatRightAuto();
      LemmaSeqPrefixNeq(xs, ys, i + 1);
    }

    lemma /*{:_induction xs, ys}*/ LemmaSeqEq(xs: seq<uint>, ys: seq<uint>)
      requires |xs| == |ys|
      requires ToNatRight(xs) == ToNatRight(ys)
      ensures xs == ys
      decreases xs, ys
    {
      calc ==> {
        xs != ys;
        {
          LemmaSeqNeq(xs, ys);
        }
        ToNatRight(xs) != ToNatRight(ys);
        false;
      }
    }

    lemma /*{:_induction xs}*/ LemmaSeqLswModEquivalence(xs: seq<uint>)
      requires |xs| >= 1
      ensures IsModEquivalent(ToNatRight(xs), First(xs), BASE())
      decreases xs
    {
      if |xs| == 1 {
        LemmaSeqLen1(xs);
        LemmaModEquivalenceAuto();
      } else {
        assert IsModEquivalent(ToNatRight(xs), First(xs), BASE()) by {
          reveal ToNatRight();
          calc ==> {
            true;
            {
              LemmaModEquivalenceAuto();
            }
            IsModEquivalent(ToNatRight(xs), ToNatRight(DropFirst(xs)) * BASE() + First(xs), BASE());
            {
              LemmaModMultiplesBasicAuto();
            }
            IsModEquivalent(ToNatRight(xs), First(xs), BASE());
          }
        }
      }
    }

    function method {:opaque} {:fuel 0, 0} FromNat(n: nat): (xs: seq<uint>)
      decreases n
    {
      if n == 0 then
        []
      else
        LemmaDivBasicsAuto(); LemmaDivDecreasesAuto(); [n % BASE()] + FromNat(n / BASE())
    }

    lemma /*{:_induction n, len}*/ LemmaFromNatLen(n: nat, len: nat)
      requires Pow(BASE(), len) > n
      ensures |FromNat(n)| <= len
      decreases n, len
    {
      reveal FromNat();
      if n == 0 {
      } else {
        calc {
          |FromNat(n)|;
        ==
          {
            LemmaDivBasicsAuto();
          }
          1 + |FromNat(n / BASE())|;
        <=
          {
            LemmaMultiplyDivideLtAuto();
            LemmaDivDecreasesAuto();
            reveal Pow();
            LemmaFromNatLen(n / BASE(), len - 1);
          }
          len;
        }
      }
    }

    lemma /*{:_induction n}*/ LemmaNatSeqNat(n: nat)
      ensures ToNatRight(FromNat(n)) == n
      decreases n
    {
      reveal ToNatRight();
      reveal FromNat();
      if n == 0 {
      } else {
        calc {
          ToNatRight(FromNat(n));
          {
            LemmaDivBasicsAuto();
          }
          ToNatRight([n % BASE()] + FromNat(n / BASE()));
          n % BASE() + ToNatRight(FromNat(n / BASE())) * BASE();
          {
            LemmaDivDecreasesAuto();
            LemmaNatSeqNat(n / BASE());
          }
          n % BASE() + n / BASE() * BASE();
          {
            LemmaFundamentalDivMod(n, BASE());
          }
          n;
        }
      }
    }

    function method {:opaque} {:fuel 0, 0} SeqExtend(xs: seq<uint>, n: nat): (ys: seq<uint>)
      requires |xs| <= n
      ensures |ys| == n
      ensures ToNatRight(ys) == ToNatRight(xs)
      decreases n - |xs|
    {
      if |xs| >= n then
        xs
      else
        LemmaSeqAppendZero(xs); SeqExtend(xs + [0], n)
    }

    function method {:opaque} {:fuel 0, 0} SeqExtendMultiple(xs: seq<uint>, n: nat): (ys: seq<uint>)
      requires n > 0
      ensures |ys| % n == 0
      ensures ToNatRight(ys) == ToNatRight(xs)
      decreases xs, n
    {
      var newLen: int := |xs| + n - |xs| % n;
      LemmaSubModNoopRight(|xs| + n, |xs|, n);
      LemmaModBasicsAuto();
      assert newLen % n == 0;
      LemmaSeqNatBound(xs);
      LemmaPowIncreasesAuto();
      SeqExtend(xs, newLen)
    }

    function method {:opaque} {:fuel 0, 0} FromNatWithLen(n: nat, len: nat): (xs: seq<uint>)
      requires Pow(BASE(), len) > n
      ensures |xs| == len
      ensures ToNatRight(xs) == n
      decreases n, len
    {
      LemmaFromNatLen(n, len);
      LemmaNatSeqNat(n);
      SeqExtend(FromNat(n), len)
    }

    lemma /*{:_induction xs}*/ LemmaSeqZero(xs: seq<uint>)
      requires ToNatRight(xs) == 0
      ensures forall i: int :: 0 <= i < |xs| ==> xs[i] == 0
      decreases xs
    {
      reveal ToNatRight();
      if |xs| == 0 {
      } else {
        LemmaMulNonnegativeAuto();
        assert First(xs) == 0;
        LemmaMulNonzeroAuto();
        LemmaSeqZero(DropFirst(xs));
      }
    }

    function method {:opaque} {:fuel 0, 0} SeqZero(len: nat): (xs: seq<uint>)
      ensures |xs| == len
      ensures forall i: int :: 0 <= i < |xs| ==> xs[i] == 0
      ensures ToNatRight(xs) == 0
      decreases len
    {
      LemmaPowPositive(BASE(), len);
      var xs: seq<uint> := FromNatWithLen(0, len);
      LemmaSeqZero(xs);
      xs
    }

    lemma /*{:_induction xs}*/ LemmaSeqNatSeq(xs: seq<uint>)
      ensures Pow(BASE(), |xs|) > ToNatRight(xs)
      ensures FromNatWithLen(ToNatRight(xs), |xs|) == xs
      decreases xs
    {
      reveal FromNat();
      reveal ToNatRight();
      LemmaSeqNatBound(xs);
      if |xs| > 0 {
        calc {
          FromNatWithLen(ToNatRight(xs), |xs|) != xs;
          {
            LemmaSeqNeq(FromNatWithLen(ToNatRight(xs), |xs|), xs);
          }
          ToNatRight(FromNatWithLen(ToNatRight(xs), |xs|)) != ToNatRight(xs);
          ToNatRight(xs) != ToNatRight(xs);
          false;
        }
      }
    }

    function method {:opaque} {:fuel 0, 0} SeqAdd(xs: seq<uint>, ys: seq<uint>): (seq<uint>, nat)
      requires |xs| == |ys|
      ensures var (zs: seq<uint>, cout: nat) := SeqAdd(xs, ys); |zs| == |xs| && 0 <= cout <= 1
      decreases xs
    {
      if |xs| == 0 then
        ([], 0)
      else
        var (zs': seq<uint>, cin: nat) := SeqAdd(DropLast(xs), DropLast(ys)); var sum: int := Last(xs) + Last(ys) + cin; var (sum_out: int, cout: int) := if sum < BASE() then (sum, 0) else (sum - BASE(), 1); (zs' + [sum_out], cout)
    }

    lemma /*{:_induction xs, ys, zs}*/ LemmaSeqAdd(xs: seq<uint>, ys: seq<uint>, zs: seq<uint>, cout: nat)
      requires |xs| == |ys|
      requires SeqAdd(xs, ys) == (zs, cout)
      ensures ToNatRight(xs) + ToNatRight(ys) == ToNatRight(zs) + cout * Pow(BASE(), |xs|)
      decreases xs, ys, zs, cout
    {
      reveal SeqAdd();
      if |xs| == 0 {
        reveal ToNatRight();
      } else {
        ghost var pow := Pow(BASE(), |xs| - 1);
        var (zs', cin) := SeqAdd(DropLast(xs), DropLast(ys));
        ghost var sum: int := Last(xs) + Last(ys) + cin;
        ghost var z := if sum < BASE() then sum else sum - BASE();
        assert sum == z + cout * BASE();
        reveal ToNatLeft();
        LemmaToNatLeftEqToNatRightAuto();
        calc {
          ToNatRight(zs);
          ToNatLeft(zs);
          ToNatLeft(zs') + z * pow;
          {
            LemmaSeqAdd(DropLast(xs), DropLast(ys), zs', cin);
          }
          ToNatLeft(DropLast(xs)) + ToNatLeft(DropLast(ys)) - cin * pow + z * pow;
          {
            LemmaMulEqualityAuto();
            assert sum * pow == (z + cout * BASE()) * pow;
            LemmaMulIsDistributiveAuto();
          }
          ToNatLeft(xs) + ToNatLeft(ys) - cout * BASE() * pow;
          {
            LemmaMulIsAssociative(cout, BASE(), pow);
            reveal Pow();
          }
          ToNatLeft(xs) + ToNatLeft(ys) - cout * Pow(BASE(), |xs|);
          ToNatRight(xs) + ToNatRight(ys) - cout * Pow(BASE(), |xs|);
        }
      }
    }

    function method {:opaque} {:fuel 0, 0} SeqSub(xs: seq<uint>, ys: seq<uint>): (seq<uint>, nat)
      requires |xs| == |ys|
      ensures var (zs: seq<uint>, cout: nat) := SeqSub(xs, ys); |zs| == |xs| && 0 <= cout <= 1
      decreases xs
    {
      if |xs| == 0 then
        ([], 0)
      else
        var (zs: seq<uint>, cin: nat) := SeqSub(DropLast(xs), DropLast(ys)); var (diff_out: int, cout: int) := if Last(xs) >= Last(ys) + cin then (Last(xs) - Last(ys) - cin, 0) else (BASE() + Last(xs) - Last(ys) - cin, 1); (zs + [diff_out], cout)
    }

    lemma /*{:_induction xs, ys, zs}*/ LemmaSeqSub(xs: seq<uint>, ys: seq<uint>, zs: seq<uint>, cout: nat)
      requires |xs| == |ys|
      requires SeqSub(xs, ys) == (zs, cout)
      ensures ToNatRight(xs) - ToNatRight(ys) + cout * Pow(BASE(), |xs|) == ToNatRight(zs)
      decreases xs, ys, zs, cout
    {
      reveal SeqSub();
      if |xs| == 0 {
        reveal ToNatRight();
      } else {
        ghost var pow := Pow(BASE(), |xs| - 1);
        var (zs', cin) := SeqSub(DropLast(xs), DropLast(ys));
        ghost var z := if Last(xs) >= Last(ys) + cin then Last(xs) - Last(ys) - cin else BASE() + Last(xs) - Last(ys) - cin;
        assert cout * BASE() + Last(xs) - cin - Last(ys) == z;
        reveal ToNatLeft();
        LemmaToNatLeftEqToNatRightAuto();
        calc {
          ToNatRight(zs);
          ToNatLeft(zs);
          ToNatLeft(zs') + z * pow;
          {
            LemmaSeqSub(DropLast(xs), DropLast(ys), zs', cin);
          }
          ToNatLeft(DropLast(xs)) - ToNatLeft(DropLast(ys)) + cin * pow + z * pow;
          {
            LemmaMulEqualityAuto();
            assert pow * (cout * BASE() + Last(xs) - cin - Last(ys)) == pow * z;
            LemmaMulIsDistributiveAuto();
          }
          ToNatLeft(xs) - ToNatLeft(ys) + cout * BASE() * pow;
          {
            LemmaMulIsAssociative(cout, BASE(), pow);
            reveal Pow();
          }
          ToNatLeft(xs) - ToNatLeft(ys) + cout * Pow(BASE(), |xs|);
          ToNatRight(xs) - ToNatRight(ys) + cout * Pow(BASE(), |xs|);
        }
      }
    }

    import opened DivMod

    import opened Mul

    import opened Power

    import opened Seq

    type uint = i: int
      | 0 <= i < BASE()
  }

  module {:extern ""Uint8__32_mUint32Seq_Compile""} Uint32Seq refines LargeSeq {

    import Small = Uint8Seq
    function method BITS(): nat
      ensures BITS() > Small.BITS() && BITS() % Small.BITS() == 0
    {
      32
    }

    function method BASE(): nat
      ensures BASE() > 1
    {
      LemmaPowPositive(2, BITS() - 1);
      LemmaPowStrictlyIncreases(2, BITS() - 1, BITS());
      Pow(2, BITS())
    }

    function method {:opaque} {:fuel 0, 0} ToNatRight(xs: seq<uint>): nat
      decreases xs
    {
      if |xs| == 0 then
        0
      else
        LemmaMulNonnegativeAuto(); ToNatRight(DropFirst(xs)) * BASE() + First(xs)
    }

    function method {:opaque} {:fuel 0, 0} ToNatLeft(xs: seq<uint>): nat
      decreases xs
    {
      if |xs| == 0 then
        0
      else
        LemmaPowPositiveAuto(); LemmaMulNonnegativeAuto(); ToNatLeft(DropLast(xs)) + Last(xs) * Pow(BASE(), |xs| - 1)
    }

    lemma {:vcs_split_on_every_assert} /*{:_induction xs}*/ LemmaToNatLeftEqToNatRight(xs: seq<uint>)
      ensures ToNatRight(xs) == ToNatLeft(xs)
      decreases xs
    {
      reveal ToNatRight();
      reveal ToNatLeft();
      if xs == [] {
      } else {
        if DropLast(xs) == [] {
          calc {
            ToNatLeft(xs);
            Last(xs) * Pow(BASE(), |xs| - 1);
            {
              reveal Pow();
            }
            Last(xs);
            First(xs);
            {
              assert ToNatRight(DropFirst(xs)) == 0;
            }
            ToNatRight(xs);
          }
        } else {
          calc {
            ToNatLeft(xs);
            ToNatLeft(DropLast(xs)) + Last(xs) * Pow(BASE(), |xs| - 1);
            {
              LemmaToNatLeftEqToNatRight(DropLast(xs));
            }
            ToNatRight(DropLast(xs)) + Last(xs) * Pow(BASE(), |xs| - 1);
            ToNatRight(DropFirst(DropLast(xs))) * BASE() + First(xs) + Last(xs) * Pow(BASE(), |xs| - 1);
            {
              LemmaToNatLeftEqToNatRight(DropFirst(DropLast(xs)));
            }
            ToNatLeft(DropFirst(DropLast(xs))) * BASE() + First(xs) + Last(xs) * Pow(BASE(), |xs| - 1);
            {
              assert DropFirst(DropLast(xs)) == DropLast(DropFirst(xs));
              reveal Pow();
              LemmaMulProperties();
            }
            ToNatLeft(DropLast(DropFirst(xs))) * BASE() + First(xs) + Last(xs) * Pow(BASE(), |xs| - 2) * BASE();
            {
              LemmaMulIsDistributiveAddOtherWayAuto();
            }
            ToNatLeft(DropFirst(xs)) * BASE() + First(xs);
            {
              LemmaToNatLeftEqToNatRight(DropFirst(xs));
            }
            ToNatRight(xs);
          }
        }
      }
    }

    lemma LemmaToNatLeftEqToNatRightAuto()
      ensures forall xs: seq<uint> :: ToNatRight(xs) == ToNatLeft(xs)
    {
      reveal ToNatRight();
      reveal ToNatLeft();
      forall xs: seq<uint> | true
        ensures ToNatRight(xs) == ToNatLeft(xs)
      {
        LemmaToNatLeftEqToNatRight(xs);
      }
    }

    lemma /*{:_induction xs}*/ LemmaSeqLen1(xs: seq<uint>)
      requires |xs| == 1
      ensures ToNatRight(xs) == First(xs)
      decreases xs
    {
      reveal ToNatRight();
    }

    lemma /*{:_induction xs}*/ LemmaSeqLen2(xs: seq<uint>)
      requires |xs| == 2
      ensures ToNatRight(xs) == First(xs) + xs[1] * BASE()
      decreases xs
    {
      reveal ToNatRight();
      LemmaSeqLen1(DropLast(xs));
    }

    lemma /*{:_induction xs}*/ LemmaSeqAppendZero(xs: seq<uint>)
      ensures ToNatRight(xs + [0]) == ToNatRight(xs)
      decreases xs
    {
      reveal ToNatLeft();
      LemmaToNatLeftEqToNatRightAuto();
      calc {
        ToNatRight(xs + [0]);
        ToNatLeft(xs + [0]);
        ToNatLeft(xs) + 0 * Pow(BASE(), |xs|);
        {
          LemmaMulBasicsAuto();
        }
        ToNatLeft(xs);
        ToNatRight(xs);
      }
    }

    lemma /*{:_induction xs}*/ LemmaSeqNatBound(xs: seq<uint>)
      ensures ToNatRight(xs) < Pow(BASE(), |xs|)
      decreases xs
    {
      reveal Pow();
      if |xs| == 0 {
        reveal ToNatRight();
      } else {
        ghost var len' := |xs| - 1;
        ghost var pow := Pow(BASE(), len');
        calc {
          ToNatRight(xs);
          {
            LemmaToNatLeftEqToNatRight(xs);
          }
          ToNatLeft(xs);
          {
            reveal ToNatLeft();
          }
          ToNatLeft(DropLast(xs)) + Last(xs) * pow;
        <
          {
            LemmaToNatLeftEqToNatRight(DropLast(xs));
            LemmaSeqNatBound(DropLast(xs));
          }
          pow + Last(xs) * pow;
        <=
          {
            LemmaPowPositiveAuto();
            LemmaMulInequalityAuto();
          }
          pow + (BASE() - 1) * pow;
          {
            LemmaMulIsDistributiveAuto();
          }
          Pow(BASE(), len' + 1);
        }
      }
    }

    lemma /*{:_induction xs, i}*/ LemmaSeqPrefix(xs: seq<uint>, i: nat)
      requires 0 <= i <= |xs|
      ensures ToNatRight(xs[..i]) + ToNatRight(xs[i..]) * Pow(BASE(), i) == ToNatRight(xs)
      decreases xs, i
    {
      reveal ToNatRight();
      reveal Pow();
      if i == 1 {
        assert ToNatRight(xs[..1]) == First(xs);
      } else if i > 1 {
        calc {
          ToNatRight(xs[..i]) + ToNatRight(xs[i..]) * Pow(BASE(), i);
          ToNatRight(DropFirst(xs[..i])) * BASE() + First(xs) + ToNatRight(xs[i..]) * Pow(BASE(), i);
          {
            assert DropFirst(xs[..i]) == DropFirst(xs)[..i - 1];
            LemmaMulProperties();
          }
          ToNatRight(DropFirst(xs)[..i - 1]) * BASE() + First(xs) + ToNatRight(xs[i..]) * Pow(BASE(), i - 1) * BASE();
          {
            LemmaMulIsDistributiveAddOtherWayAuto();
          }
          (ToNatRight(DropFirst(xs)[..i - 1]) + ToNatRight(DropFirst(xs)[i - 1..]) * Pow(BASE(), i - 1)) * BASE() + First(xs);
          {
            LemmaSeqPrefix(DropFirst(xs), i - 1);
          }
          ToNatRight(xs);
        }
      }
    }

    lemma /*{:_induction xs, ys}*/ LemmaSeqMswInequality(xs: seq<uint>, ys: seq<uint>)
      requires |xs| == |ys| > 0
      requires Last(xs) < Last(ys)
      ensures ToNatRight(xs) < ToNatRight(ys)
      decreases xs, ys
    {
      reveal ToNatLeft();
      LemmaToNatLeftEqToNatRightAuto();
      ghost var len' := |xs| - 1;
      calc {
        ToNatRight(xs);
        ToNatLeft(xs);
      <
        {
          LemmaSeqNatBound(DropLast(xs));
        }
        Pow(BASE(), len') + Last(xs) * Pow(BASE(), len');
      ==
        {
          LemmaMulIsDistributiveAuto();
        }
        (1 + Last(xs)) * Pow(BASE(), len');
      <=
        {
          LemmaPowPositiveAuto();
          LemmaMulInequalityAuto();
        }
        ToNatLeft(ys);
        ToNatRight(ys);
      }
    }

    lemma /*{:_induction xs, ys}*/ LemmaSeqPrefixNeq(xs: seq<uint>, ys: seq<uint>, i: nat)
      requires 0 <= i <= |xs| == |ys|
      requires ToNatRight(xs[..i]) != ToNatRight(ys[..i])
      ensures ToNatRight(xs) != ToNatRight(ys)
      decreases |xs| - i
    {
      if i == |xs| {
        assert xs[..i] == xs;
        assert ys[..i] == ys;
      } else {
        if xs[i] == ys[i] {
          reveal ToNatLeft();
          assert DropLast(xs[..i + 1]) == xs[..i];
          assert DropLast(ys[..i + 1]) == ys[..i];
          LemmaToNatLeftEqToNatRightAuto();
          assert ToNatRight(xs[..i + 1]) == ToNatLeft(xs[..i + 1]);
        } else if xs[i] < ys[i] {
          LemmaSeqMswInequality(xs[..i + 1], ys[..i + 1]);
        } else {
          LemmaSeqMswInequality(ys[..i + 1], xs[..i + 1]);
        }
        LemmaSeqPrefixNeq(xs, ys, i + 1);
      }
    }

    lemma /*{:_induction xs, ys}*/ LemmaSeqNeq(xs: seq<uint>, ys: seq<uint>)
      requires |xs| == |ys|
      requires xs != ys
      ensures ToNatRight(xs) != ToNatRight(ys)
      decreases xs, ys
    {
      ghost var i: nat, n: nat := 0, |xs|;
      while i < n
        invariant 0 <= i < n
        invariant xs[..i] == ys[..i]
        decreases n - i
      {
        if xs[i] != ys[i] {
          break;
        }
        i := i + 1;
      }
      assert ToNatLeft(xs[..i]) == ToNatLeft(ys[..i]);
      reveal ToNatLeft();
      assert xs[..i + 1][..i] == xs[..i];
      assert ys[..i + 1][..i] == ys[..i];
      LemmaPowPositiveAuto();
      LemmaMulStrictInequalityAuto();
      assert ToNatLeft(xs[..i + 1]) != ToNatLeft(ys[..i + 1]);
      LemmaToNatLeftEqToNatRightAuto();
      LemmaSeqPrefixNeq(xs, ys, i + 1);
    }

    lemma /*{:_induction xs, ys}*/ LemmaSeqEq(xs: seq<uint>, ys: seq<uint>)
      requires |xs| == |ys|
      requires ToNatRight(xs) == ToNatRight(ys)
      ensures xs == ys
      decreases xs, ys
    {
      calc ==> {
        xs != ys;
        {
          LemmaSeqNeq(xs, ys);
        }
        ToNatRight(xs) != ToNatRight(ys);
        false;
      }
    }

    lemma /*{:_induction xs}*/ LemmaSeqLswModEquivalence(xs: seq<uint>)
      requires |xs| >= 1
      ensures IsModEquivalent(ToNatRight(xs), First(xs), BASE())
      decreases xs
    {
      if |xs| == 1 {
        LemmaSeqLen1(xs);
        LemmaModEquivalenceAuto();
      } else {
        assert IsModEquivalent(ToNatRight(xs), First(xs), BASE()) by {
          reveal ToNatRight();
          calc ==> {
            true;
            {
              LemmaModEquivalenceAuto();
            }
            IsModEquivalent(ToNatRight(xs), ToNatRight(DropFirst(xs)) * BASE() + First(xs), BASE());
            {
              LemmaModMultiplesBasicAuto();
            }
            IsModEquivalent(ToNatRight(xs), First(xs), BASE());
          }
        }
      }
    }

    function method {:opaque} {:fuel 0, 0} FromNat(n: nat): (xs: seq<uint>)
      decreases n
    {
      if n == 0 then
        []
      else
        LemmaDivBasicsAuto(); LemmaDivDecreasesAuto(); [n % BASE()] + FromNat(n / BASE())
    }

    lemma /*{:_induction n, len}*/ LemmaFromNatLen(n: nat, len: nat)
      requires Pow(BASE(), len) > n
      ensures |FromNat(n)| <= len
      decreases n, len
    {
      reveal FromNat();
      if n == 0 {
      } else {
        calc {
          |FromNat(n)|;
        ==
          {
            LemmaDivBasicsAuto();
          }
          1 + |FromNat(n / BASE())|;
        <=
          {
            LemmaMultiplyDivideLtAuto();
            LemmaDivDecreasesAuto();
            reveal Pow();
            LemmaFromNatLen(n / BASE(), len - 1);
          }
          len;
        }
      }
    }

    lemma /*{:_induction n}*/ LemmaNatSeqNat(n: nat)
      ensures ToNatRight(FromNat(n)) == n
      decreases n
    {
      reveal ToNatRight();
      reveal FromNat();
      if n == 0 {
      } else {
        calc {
          ToNatRight(FromNat(n));
          {
            LemmaDivBasicsAuto();
          }
          ToNatRight([n % BASE()] + FromNat(n / BASE()));
          n % BASE() + ToNatRight(FromNat(n / BASE())) * BASE();
          {
            LemmaDivDecreasesAuto();
            LemmaNatSeqNat(n / BASE());
          }
          n % BASE() + n / BASE() * BASE();
          {
            LemmaFundamentalDivMod(n, BASE());
          }
          n;
        }
      }
    }

    function method {:opaque} {:fuel 0, 0} SeqExtend(xs: seq<uint>, n: nat): (ys: seq<uint>)
      requires |xs| <= n
      ensures |ys| == n
      ensures ToNatRight(ys) == ToNatRight(xs)
      decreases n - |xs|
    {
      if |xs| >= n then
        xs
      else
        LemmaSeqAppendZero(xs); SeqExtend(xs + [0], n)
    }

    function method {:opaque} {:fuel 0, 0} SeqExtendMultiple(xs: seq<uint>, n: nat): (ys: seq<uint>)
      requires n > 0
      ensures |ys| % n == 0
      ensures ToNatRight(ys) == ToNatRight(xs)
      decreases xs, n
    {
      var newLen: int := |xs| + n - |xs| % n;
      LemmaSubModNoopRight(|xs| + n, |xs|, n);
      LemmaModBasicsAuto();
      assert newLen % n == 0;
      LemmaSeqNatBound(xs);
      LemmaPowIncreasesAuto();
      SeqExtend(xs, newLen)
    }

    function method {:opaque} {:fuel 0, 0} FromNatWithLen(n: nat, len: nat): (xs: seq<uint>)
      requires Pow(BASE(), len) > n
      ensures |xs| == len
      ensures ToNatRight(xs) == n
      decreases n, len
    {
      LemmaFromNatLen(n, len);
      LemmaNatSeqNat(n);
      SeqExtend(FromNat(n), len)
    }

    lemma /*{:_induction xs}*/ LemmaSeqZero(xs: seq<uint>)
      requires ToNatRight(xs) == 0
      ensures forall i: int :: 0 <= i < |xs| ==> xs[i] == 0
      decreases xs
    {
      reveal ToNatRight();
      if |xs| == 0 {
      } else {
        LemmaMulNonnegativeAuto();
        assert First(xs) == 0;
        LemmaMulNonzeroAuto();
        LemmaSeqZero(DropFirst(xs));
      }
    }

    function method {:opaque} {:fuel 0, 0} SeqZero(len: nat): (xs: seq<uint>)
      ensures |xs| == len
      ensures forall i: int :: 0 <= i < |xs| ==> xs[i] == 0
      ensures ToNatRight(xs) == 0
      decreases len
    {
      LemmaPowPositive(BASE(), len);
      var xs: seq<uint> := FromNatWithLen(0, len);
      LemmaSeqZero(xs);
      xs
    }

    lemma /*{:_induction xs}*/ LemmaSeqNatSeq(xs: seq<uint>)
      ensures Pow(BASE(), |xs|) > ToNatRight(xs)
      ensures FromNatWithLen(ToNatRight(xs), |xs|) == xs
      decreases xs
    {
      reveal FromNat();
      reveal ToNatRight();
      LemmaSeqNatBound(xs);
      if |xs| > 0 {
        calc {
          FromNatWithLen(ToNatRight(xs), |xs|) != xs;
          {
            LemmaSeqNeq(FromNatWithLen(ToNatRight(xs), |xs|), xs);
          }
          ToNatRight(FromNatWithLen(ToNatRight(xs), |xs|)) != ToNatRight(xs);
          ToNatRight(xs) != ToNatRight(xs);
          false;
        }
      }
    }

    function method {:opaque} {:fuel 0, 0} SeqAdd(xs: seq<uint>, ys: seq<uint>): (seq<uint>, nat)
      requires |xs| == |ys|
      ensures var (zs: seq<uint>, cout: nat) := SeqAdd(xs, ys); |zs| == |xs| && 0 <= cout <= 1
      decreases xs
    {
      if |xs| == 0 then
        ([], 0)
      else
        var (zs': seq<uint>, cin: nat) := SeqAdd(DropLast(xs), DropLast(ys)); var sum: int := Last(xs) + Last(ys) + cin; var (sum_out: int, cout: int) := if sum < BASE() then (sum, 0) else (sum - BASE(), 1); (zs' + [sum_out], cout)
    }

    lemma /*{:_induction xs, ys, zs}*/ LemmaSeqAdd(xs: seq<uint>, ys: seq<uint>, zs: seq<uint>, cout: nat)
      requires |xs| == |ys|
      requires SeqAdd(xs, ys) == (zs, cout)
      ensures ToNatRight(xs) + ToNatRight(ys) == ToNatRight(zs) + cout * Pow(BASE(), |xs|)
      decreases xs, ys, zs, cout
    {
      reveal SeqAdd();
      if |xs| == 0 {
        reveal ToNatRight();
      } else {
        ghost var pow := Pow(BASE(), |xs| - 1);
        var (zs', cin) := SeqAdd(DropLast(xs), DropLast(ys));
        ghost var sum: int := Last(xs) + Last(ys) + cin;
        ghost var z := if sum < BASE() then sum else sum - BASE();
        assert sum == z + cout * BASE();
        reveal ToNatLeft();
        LemmaToNatLeftEqToNatRightAuto();
        calc {
          ToNatRight(zs);
          ToNatLeft(zs);
          ToNatLeft(zs') + z * pow;
          {
            LemmaSeqAdd(DropLast(xs), DropLast(ys), zs', cin);
          }
          ToNatLeft(DropLast(xs)) + ToNatLeft(DropLast(ys)) - cin * pow + z * pow;
          {
            LemmaMulEqualityAuto();
            assert sum * pow == (z + cout * BASE()) * pow;
            LemmaMulIsDistributiveAuto();
          }
          ToNatLeft(xs) + ToNatLeft(ys) - cout * BASE() * pow;
          {
            LemmaMulIsAssociative(cout, BASE(), pow);
            reveal Pow();
          }
          ToNatLeft(xs) + ToNatLeft(ys) - cout * Pow(BASE(), |xs|);
          ToNatRight(xs) + ToNatRight(ys) - cout * Pow(BASE(), |xs|);
        }
      }
    }

    function method {:opaque} {:fuel 0, 0} SeqSub(xs: seq<uint>, ys: seq<uint>): (seq<uint>, nat)
      requires |xs| == |ys|
      ensures var (zs: seq<uint>, cout: nat) := SeqSub(xs, ys); |zs| == |xs| && 0 <= cout <= 1
      decreases xs
    {
      if |xs| == 0 then
        ([], 0)
      else
        var (zs: seq<uint>, cin: nat) := SeqSub(DropLast(xs), DropLast(ys)); var (diff_out: int, cout: int) := if Last(xs) >= Last(ys) + cin then (Last(xs) - Last(ys) - cin, 0) else (BASE() + Last(xs) - Last(ys) - cin, 1); (zs + [diff_out], cout)
    }

    lemma /*{:_induction xs, ys, zs}*/ LemmaSeqSub(xs: seq<uint>, ys: seq<uint>, zs: seq<uint>, cout: nat)
      requires |xs| == |ys|
      requires SeqSub(xs, ys) == (zs, cout)
      ensures ToNatRight(xs) - ToNatRight(ys) + cout * Pow(BASE(), |xs|) == ToNatRight(zs)
      decreases xs, ys, zs, cout
    {
      reveal SeqSub();
      if |xs| == 0 {
        reveal ToNatRight();
      } else {
        ghost var pow := Pow(BASE(), |xs| - 1);
        var (zs', cin) := SeqSub(DropLast(xs), DropLast(ys));
        ghost var z := if Last(xs) >= Last(ys) + cin then Last(xs) - Last(ys) - cin else BASE() + Last(xs) - Last(ys) - cin;
        assert cout * BASE() + Last(xs) - cin - Last(ys) == z;
        reveal ToNatLeft();
        LemmaToNatLeftEqToNatRightAuto();
        calc {
          ToNatRight(zs);
          ToNatLeft(zs);
          ToNatLeft(zs') + z * pow;
          {
            LemmaSeqSub(DropLast(xs), DropLast(ys), zs', cin);
          }
          ToNatLeft(DropLast(xs)) - ToNatLeft(DropLast(ys)) + cin * pow + z * pow;
          {
            LemmaMulEqualityAuto();
            assert pow * (cout * BASE() + Last(xs) - cin - Last(ys)) == pow * z;
            LemmaMulIsDistributiveAuto();
          }
          ToNatLeft(xs) - ToNatLeft(ys) + cout * BASE() * pow;
          {
            LemmaMulIsAssociative(cout, BASE(), pow);
            reveal Pow();
          }
          ToNatLeft(xs) - ToNatLeft(ys) + cout * Pow(BASE(), |xs|);
          ToNatRight(xs) - ToNatRight(ys) + cout * Pow(BASE(), |xs|);
        }
      }
    }

    import opened DivMod

    import opened Mul

    import opened Power

    import opened Seq

    type uint = i: int
      | 0 <= i < BASE()
  }

  import opened Large = Uint32Seq

  import Small = Large.Small
  function method E(): (E: nat)
    ensures Pow(Small.BASE(), E) == Large.BASE()
    ensures E > 0
  {
    LemmaDivBasicsAuto();
    LemmaPowMultipliesAuto();
    LemmaFundamentalDivMod(Large.BITS(), Small.BITS());
    Large.BITS() / Small.BITS()
  }

  function method {:opaque} {:fuel 0, 0} ToSmall(xs: seq<Large.uint>): (ys: seq<Small.uint>)
    ensures |ys| == |xs| * E()
    decreases xs
  {
    if |xs| == 0 then
      []
    else
      LemmaMulIsDistributiveAddOtherWay(E(), 1, |xs| - 1); Small.FromNatWithLen(First(xs), E()) + ToSmall(DropFirst(xs))
  }

  function method {:opaque} {:fuel 0, 0} ToLarge(xs: seq<Small.uint>): (ys: seq<Large.uint>)
    requires |xs| % E() == 0
    ensures |ys| == |xs| / E()
    decreases xs
  {
    if |xs| == 0 then
      LemmaDivBasicsAuto();
      []
    else
      LemmaModIsZero(|xs|, E()); assert |xs| >= E(); Small.LemmaSeqNatBound(xs[..E()]); LemmaModSubMultiplesVanishAuto(); LemmaDivMinusOne(|xs|, E()); [Small.ToNatRight(xs[..E()]) as Large.uint] + ToLarge(xs[E()..])
  }

  lemma /*{:_induction xs}*/ LemmaToSmall(xs: seq<Large.uint>)
    ensures Small.ToNatRight(ToSmall(xs)) == Large.ToNatRight(xs)
    decreases xs
  {
    reveal Small.ToNatRight();
    reveal Large.ToNatRight();
    reveal ToSmall();
    if |xs| == 0 {
    } else {
      calc {
        Small.ToNatRight(ToSmall(xs));
        Small.ToNatRight(Small.FromNatWithLen(First(xs), E()) + ToSmall(DropFirst(xs)));
        {
          Small.LemmaSeqPrefix(Small.FromNatWithLen(First(xs), E()) + ToSmall(DropFirst(xs)), E());
          LemmaToSmall(DropFirst(xs));
        }
        First(xs) + Large.ToNatRight(DropFirst(xs)) * Pow(Small.BASE(), E());
        {
          assert Pow(Small.BASE(), E()) == Large.BASE();
        }
        Large.ToNatRight(xs);
      }
    }
  }

  lemma /*{:_induction xs}*/ LemmaToLarge(xs: seq<Small.uint>)
    requires |xs| % E() == 0
    ensures Large.ToNatRight(ToLarge(xs)) == Small.ToNatRight(xs)
    decreases xs
  {
    reveal Large.ToNatRight();
    reveal Small.ToNatRight();
    reveal ToLarge();
    if |xs| == 0 {
    } else {
      calc {
        Large.ToNatRight(ToLarge(xs));
        {
          LemmaModIsZero(|xs|, E());
          LemmaModSubMultiplesVanishAuto();
          Small.LemmaSeqNatBound(xs[..E()]);
        }
        Large.ToNatRight([Small.ToNatRight(xs[..E()]) as Large.uint] + ToLarge(xs[E()..]));
        {
          LemmaToLarge(xs[E()..]);
        }
        Small.ToNatRight(xs[..E()]) + Small.ToNatRight(xs[E()..]) * Pow(Small.BASE(), E());
        {
          Small.LemmaSeqPrefix(xs, E());
        }
        Small.ToNatRight(xs);
      }
    }
  }

  lemma /*{:_induction xs, ys}*/ LemmaToSmallIsInjective(xs: seq<Large.uint>, ys: seq<Large.uint>)
    requires ToSmall(xs) == ToSmall(ys)
    requires |xs| == |ys|
    ensures xs == ys
    decreases xs, ys
  {
    LemmaToSmall(xs);
    LemmaToSmall(ys);
    assert Large.ToNatRight(xs) == Large.ToNatRight(ys);
    Large.LemmaSeqEq(xs, ys);
  }

  lemma /*{:_induction xs, ys}*/ LemmaToLargeIsInjective(xs: seq<Small.uint>, ys: seq<Small.uint>)
    requires |xs| % E() == |ys| % E() == 0
    requires ToLarge(xs) == ToLarge(ys)
    requires |xs| == |ys|
    ensures xs == ys
    decreases xs, ys
  {
    LemmaToLarge(xs);
    LemmaToLarge(ys);
    assert Small.ToNatRight(xs) == Small.ToNatRight(ys);
    Small.LemmaSeqEq(xs, ys);
  }

  lemma /*{:_induction xs}*/ LemmaSmallLargeSmall(xs: seq<Small.uint>)
    requires |xs| % E() == 0
    ensures ToSmall(ToLarge(xs)) == xs
    decreases xs
  {
    reveal ToSmall();
    reveal ToLarge();
    if |xs| == 0 {
    } else {
      calc {
        ToSmall(ToLarge(xs));
        {
          LemmaModIsZero(|xs|, E());
          Small.LemmaSeqNatBound(xs[..E()]);
          LemmaModSubMultiplesVanishAuto();
        }
        ToSmall([Small.ToNatRight(xs[..E()]) as Large.uint] + ToLarge(xs[E()..]));
        Small.FromNatWithLen(Small.ToNatRight(xs[..E()]), E()) + ToSmall(ToLarge(xs[E()..]));
        {
          Small.LemmaSeqNatSeq(xs[..E()]);
          LemmaSmallLargeSmall(xs[E()..]);
        }
        xs;
      }
    }
  }

  lemma /*{:_induction xs}*/ LemmaLargeSmallLarge(xs: seq<Large.uint>)
    ensures |ToSmall(xs)| % E() == 0
    ensures ToLarge(ToSmall(xs)) == xs
    decreases xs
  {
    reveal ToSmall();
    reveal ToLarge();
    LemmaModMultiplesBasicAuto();
    if |xs| == 0 {
    } else {
      calc {
        ToLarge(ToSmall(xs));
        ToLarge(Small.FromNatWithLen(First(xs), E()) + ToSmall(DropFirst(xs)));
        [Small.ToNatRight(Small.FromNatWithLen(First(xs), E())) as Large.uint] + ToLarge(ToSmall(DropFirst(xs)));
        [First(xs)] + ToLarge(ToSmall(DropFirst(xs)));
        {
          LemmaLargeSmallLarge(DropFirst(xs));
        }
        [First(xs)] + DropFirst(xs);
        xs;
      }
    }
  }

  import opened DivMod

  import opened Mul

  import opened Power

  import opened Seq
}

module srcCollectionsSequencesLittleEndianNatdfyUnitTests {

  import DivMod

  import DivInternalsNonlinear

  import DivInternals

  import GeneralInternals

  import ModInternals

  import MulInternals

  import MulInternalsNonlinear

  import Mul

  import ModInternalsNonlinear

  import Power

  import Seq

  import Wrappers

  import Math
}

module srcCollectionsSequencesSeqdfyUnitTests {

  import Seq

  import Wrappers

  import Math
  method {:test} test0()
  {
    var d0: seq<int> := [0];
    expect |d0| > 0, ""Test does not meet preconditions and should be removed""
    var r0 := Seq.First<int>(d0);
  }

  method {:test} test1()
  {
    var d0: seq<int> := [0];
    expect |d0| > 0, ""Test does not meet preconditions and should be removed""
    var r0 := Seq.DropFirst<int>(d0);
  }

  method {:test} test2()
  {
    var d0: seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
    expect |d0| > 0, ""Test does not meet preconditions and should be removed""
    var r0 := Seq.Last<int>(d0);
  }

  method {:test} test3()
  {
    var d0: seq<int> := [0, 0];
    expect |d0| > 0, ""Test does not meet preconditions and should be removed""
    var r0 := Seq.DropLast<int>(d0);
  }

  method {:test} test4()
  {
    var d0: seq<int> := [0];
    var r0 := Seq.ToArray<int>(d0);
    expect r0.Length == |d0|, ""expectation violation""
  }

  method {:test} test6()
  {
    var d0: seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
    var r0 := Seq.ToArray<int>(d0);
    expect r0.Length == |d0|, ""expectation violation""
  }

  method {:test} test8()
  {
    var d0: seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
    var r0 := Seq.ToSet<int>(d0);
  }

  method {:test} test9()
  {
    var d0: seq<int> := [];
    var r0 := Seq.ToSet<int>(d0);
  }

  method {:test} test11()
  {
    var d0: seq<int> := [1];
    expect 1 in d0, ""Test does not meet preconditions and should be removed""
    var r0 := Seq.IndexOf<int>(d0, 1);
    expect r0 < |d0| && d0[r0] == 1, ""expectation violation""
  }

  method {:test} test12()
  {
    var d0: seq<int> := [0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1];
    expect 1 in d0, ""Test does not meet preconditions and should be removed""
    var r0 := Seq.IndexOf<int>(d0, 1);
    expect r0 < |d0| && d0[r0] == 1, ""expectation violation""
  }

  method {:test} test13()
  {
    var d0: seq<int> := [];
    var r0 := Seq.IndexOfOption<int>(d0, 0);
  }

  method {:test} test14()
  {
    var d0: seq<int> := [0];
    var r0 := Seq.IndexOfOption<int>(d0, 1);
  }

  method {:test} test15()
  {
    var d0: seq<int> := [1, 2];
    var r0 := Seq.IndexOfOption<int>(d0, 2);
  }

  method {:test} test16()
  {
    var d0: seq<int> := [0];
    var r0 := Seq.IndexOfOption<int>(d0, 0);
  }

  method {:test} test17()
  {
    var d0: seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
    expect 0 in d0, ""Test does not meet preconditions and should be removed""
    var r0 := Seq.LastIndexOf<int>(d0, 0);
    expect r0 < |d0| && d0[r0] == 0, ""expectation violation""
  }

  method {:test} test18()
  {
    var d0: seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1];
    expect 0 in d0, ""Test does not meet preconditions and should be removed""
    var r0 := Seq.LastIndexOf<int>(d0, 0);
    expect r0 < |d0| && d0[r0] == 0, ""expectation violation""
  }

  method {:test} test19()
  {
    var d0: seq<int> := [];
    var r0 := Seq.LastIndexOfOption<int>(d0, 0);
  }

  method {:test} test20()
  {
    var d0: seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2];
    var r0 := Seq.LastIndexOfOption<int>(d0, 3);
  }

  method {:test} test21()
  {
    var d0: seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
    var r0 := Seq.LastIndexOfOption<int>(d0, 0);
  }

  method {:test} test22()
  {
    var d0: seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
    expect 39 as nat < |d0|, ""Test does not meet preconditions and should be removed""
    var r0 := Seq.Remove<int>(d0, 39 as nat);
    expect |r0| == |d0| - 1, ""expectation violation""
  }

  method {:test} test23()
  {
    var d0: seq<int> := [];
    var r0 := Seq.RemoveValue<int>(d0, 0);
    expect 0 !in d0 ==> d0 == r0, ""expectation violation""
    expect 0 in d0 ==> |multiset(r0)| == |multiset(d0)| - 1, ""expectation violation""
    expect 0 in d0 ==> multiset(r0)[0] == multiset(d0)[0] - 1, ""expectation violation""
  }

  method {:test} test24()
  {
    var d0: seq<int> := [0, 2, 0];
    var r0 := Seq.RemoveValue<int>(d0, 2);
    expect 2 !in d0 ==> d0 == r0, ""expectation violation""
    expect 2 in d0 ==> |multiset(r0)| == |multiset(d0)| - 1, ""expectation violation""
    expect 2 in d0 ==> multiset(r0)[2] == multiset(d0)[2] - 1, ""expectation violation""
  }

  method {:test} test25()
  {
    var d0: seq<int> := [0, 0];
    expect 1 as nat <= |d0|, ""Test does not meet preconditions and should be removed""
    var r0 := Seq.Insert<int>(d0, 0, 1 as nat);
    expect |Seq.Insert(d0, 0, 1 as nat)| == |d0| + 1, ""expectation violation""
    expect Seq.Insert(d0, 0, 1 as nat)[1 as nat] == 0, ""expectation violation""
    expect multiset(Seq.Insert(d0, 0, 1 as nat)) == multiset(d0) + multiset{0}, ""expectation violation""
  }

  method {:test} test26()
  {
    var d0: seq<int> := [];
    var r0 := Seq.Reverse<int>(d0);
    expect |r0| == |d0|, ""expectation violation""
  }

  method {:test} test27()
  {
    var d0: seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0];
    var r0 := Seq.Reverse<int>(d0);
    expect |r0| == |d0|, ""expectation violation""
  }

  method {:test} test28()
  {
    var r0 := Seq.Repeat<int>(0, 76 as nat);
    expect |r0| == 76 as nat, ""expectation violation""
  }

  method {:test} test29()
  {
    var r0 := Seq.Repeat<int>(0, 0 as nat);
    expect |r0| == 0 as nat, ""expectation violation""
  }

  method {:test} test32()
  {
    var d0: seq<int> := [0, 0];
    var d1: seq<int> := [0, 0];
    expect |d0| == |d1|, ""Test does not meet preconditions and should be removed""
    var r0 := Seq.Zip<int, int>(d0, d1);
    expect |Seq.Zip(d0, d1)| == |d0|, ""expectation violation""
    expect Seq.Unzip(Seq.Zip(d0, d1)).0 == d0, ""expectation violation""
    expect Seq.Unzip(Seq.Zip(d0, d1)).1 == d1, ""expectation violation""
  }

  method {:test} test33()
  {
    var d0: seq<int> := [];
    var d1: seq<int> := [];
    expect |d0| == |d1|, ""Test does not meet preconditions and should be removed""
    var r0 := Seq.Zip<int, int>(d0, d1);
    expect |Seq.Zip(d0, d1)| == |d0|, ""expectation violation""
    expect Seq.Unzip(Seq.Zip(d0, d1)).0 == d0, ""expectation violation""
    expect Seq.Unzip(Seq.Zip(d0, d1)).1 == d1, ""expectation violation""
  }

  method {:test} test34()
  {
    var d0: seq<int> := [8855, 8878, 8879];
    expect 0 < |d0|, ""Test does not meet preconditions and should be removed""
    var r0 := Seq.Max(d0);
    expect Seq.Max(d0) in d0, ""expectation violation""
  }

  method {:test} test35()
  {
    var d0: seq<int> := [0];
    expect 0 < |d0|, ""Test does not meet preconditions and should be removed""
    var r0 := Seq.Max(d0);
    expect Seq.Max(d0) in d0, ""expectation violation""
  }

  method {:test} test36()
  {
    var d0: seq<int> := [8855, 1141, 1142];
    expect 0 < |d0|, ""Test does not meet preconditions and should be removed""
    var r0 := Seq.Min(d0);
    expect Seq.Min(d0) in d0, ""expectation violation""
  }

  method {:test} test37()
  {
    var d0: seq<int> := [0];
    expect 0 < |d0|, ""Test does not meet preconditions and should be removed""
    var r0 := Seq.Min(d0);
    expect Seq.Min(d0) in d0, ""expectation violation""
  }

  method {:test} test38()
  {
    var d0: seq<seq<int>> := [];
    var r0 := Seq.Flatten<int>(d0);
  }

  method {:test} test39()
  {
    var d0: seq<int> := [];
    var d1: seq<int> := [0];
    var d2: seq<seq<int>> := [d0, d1];
    var r0 := Seq.Flatten<int>(d2);
  }

  method {:test} test40()
  {
    var d0: seq<seq<int>> := [];
    var r0 := Seq.FlattenReverse<int>(d0);
  }

  method {:test} test41()
  {
    var d0: seq<int> := [];
    var d1: seq<int> := [];
    var d2: seq<seq<int>> := [d0, d1];
    var r0 := Seq.FlattenReverse<int>(d2);
  }

  method {:test} test42()
  {
    var d0: seq<int> := [];
    var r0 := Seq.Map<int, int>((a0: int) => 0, d0);
    expect |r0| == |d0|, ""expectation violation""
  }

  method {:test} test43()
  {
    var d0: seq<int> := [0, 1];
    var r0 := Seq.Map<int, int>((a0: int) => 0, d0);
    expect |r0| == |d0|, ""expectation violation""
  }

  method {:test} test44()
  {
    var d0: Wrappers.Result<int, int> := Wrappers.Result<int, int>.Success(value := 0);
    var d1: seq<int> := [];
    var r0 := Seq.MapWithResult<int, int, int>((a0: int) => d0, d1);
  }

  method {:test} test45()
  {
    var d0: Wrappers.Result<int, int> := Wrappers.Result<int, int>.Success(value := 0);
    var d1: seq<int> := [0, 1];
    var r0 := Seq.MapWithResult<int, int, int>((a0: int) => d0, d1);
  }

  method {:test} test46()
  {
    var d0: Wrappers.Result<int, int> := Wrappers.Result<int, int>.Success(value := 0);
    var d1: seq<int> := [0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
    var r0 := Seq.MapWithResult<int, int, int>((a0: int) => d0, d1);
  }

  method {:test} test47()
  {
    var d0: Wrappers.Result<int, int> := Wrappers.Result<int, int>.Success(value := 0);
    var d1: seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
    var r0 := Seq.MapWithResult<int, int, int>((a0: int) => d0, d1);
  }

  method {:test} test48()
  {
    var d0: seq<int> := [];
    var r0 := Seq.Filter<int>((a0: int) => false, d0);
    expect |r0| <= |d0|, ""expectation violation""
  }

  method {:test} test49()
  {
    var d0: seq<int> := [0];
    var r0 := Seq.Filter<int>((a0: int) => false, d0);
    expect |r0| <= |d0|, ""expectation violation""
  }

  method {:test} test51()
  {
    var d0: seq<int> := [];
    var r0 := Seq.FoldLeft<int, int>((a0: int, a1: int) => 0, 0, d0);
  }

  method {:test} test52()
  {
    var d0: seq<int> := [1];
    var r0 := Seq.FoldLeft<int, int>((a0: int, a1: int) => 0, 0, d0);
  }

  method {:test} test53()
  {
    var d0: seq<int> := [];
    var r0 := Seq.FoldRight<int, int>((a0: int, a1: int) => 0, d0, 0);
  }

  method {:test} test54()
  {
    var d0: seq<int> := [0];
    var r0 := Seq.FoldRight<int, int>((a0: int, a1: int) => 0, d0, 0);
  }
}

module srcCollectionsSequencesUint16_32dfyUnitTests {

  import Uint16_32

  import Uint16Seq = Uint16_32.Uint16Seq

  import Uint32Seq = Uint16_32.Uint32Seq

  import DivMod

  import DivInternalsNonlinear

  import DivInternals

  import GeneralInternals

  import ModInternals

  import MulInternals

  import MulInternalsNonlinear

  import Mul

  import ModInternalsNonlinear

  import Power

  import Seq

  import Wrappers

  import Math
  method {:test} test0()
  {
    var d0: seq<Uint16_32.Uint16Seq.uint> := [];
    var r0 := Uint16_32.Uint16Seq.ToNatRight(d0);
  }

  method {:test} test1()
  {
    var d0: seq<Uint16_32.Uint16Seq.uint> := [];
    var r0 := Uint16_32.Uint16Seq.ToNatLeft(d0);
  }

  method {:test} test2()
  {
    var r0 := Uint16_32.Uint16Seq.FromNat(65 as nat);
  }

  method {:test} test3()
  {
    var r0 := Uint16_32.Uint16Seq.FromNat(0 as nat);
  }

  method {:test} test4()
  {
    var d0: seq<Uint16_32.Uint16Seq.uint> := [0 as Uint16_32.Uint16Seq.uint];
    expect |d0| <= 1 as nat, ""Test does not meet preconditions and should be removed""
    var r0 := Uint16_32.Uint16Seq.SeqExtend(d0, 1 as nat);
    expect |r0| == 1 as nat, ""expectation violation""
    expect Uint16_32.Uint16Seq.ToNatRight(r0) == Uint16_32.Uint16Seq.ToNatRight(d0), ""expectation violation""
  }

  method {:test} test5()
  {
    var d0: seq<Uint16_32.Uint16Seq.uint> := [0 as Uint16_32.Uint16Seq.uint, 0 as Uint16_32.Uint16Seq.uint];
    var d1: seq<Uint16_32.Uint16Seq.uint> := [0 as Uint16_32.Uint16Seq.uint, 0 as Uint16_32.Uint16Seq.uint];
    expect |d0| == |d1|, ""Test does not meet preconditions and should be removed""
    var r0 := Uint16_32.Uint16Seq.SeqAdd(d0, d1);
  }

  method {:test} test6()
  {
    var d0: seq<Uint16_32.Uint16Seq.uint> := [12 as Uint16_32.Uint16Seq.uint, 2283 as Uint16_32.Uint16Seq.uint];
    var d1: seq<Uint16_32.Uint16Seq.uint> := [281 as Uint16_32.Uint16Seq.uint, 11138 as Uint16_32.Uint16Seq.uint];
    expect |d0| == |d1|, ""Test does not meet preconditions and should be removed""
    var r0 := Uint16_32.Uint16Seq.SeqAdd(d0, d1);
  }

  method {:test} test7()
  {
    var d0: seq<Uint16_32.Uint16Seq.uint> := [];
    var d1: seq<Uint16_32.Uint16Seq.uint> := [];
    expect |d0| == |d1|, ""Test does not meet preconditions and should be removed""
    var r0 := Uint16_32.Uint16Seq.SeqAdd(d0, d1);
  }

  method {:test} test8()
  {
    var d0: seq<Uint16_32.Uint16Seq.uint> := [1325 as Uint16_32.Uint16Seq.uint, 2331 as Uint16_32.Uint16Seq.uint];
    var d1: seq<Uint16_32.Uint16Seq.uint> := [234 as Uint16_32.Uint16Seq.uint, 1796 as Uint16_32.Uint16Seq.uint];
    expect |d0| == |d1|, ""Test does not meet preconditions and should be removed""
    var r0 := Uint16_32.Uint16Seq.SeqSub(d0, d1);
  }

  method {:test} test9()
  {
    var d0: seq<Uint16_32.Uint16Seq.uint> := [920 as Uint16_32.Uint16Seq.uint, 2061 as Uint16_32.Uint16Seq.uint];
    var d1: seq<Uint16_32.Uint16Seq.uint> := [645 as Uint16_32.Uint16Seq.uint, 2062 as Uint16_32.Uint16Seq.uint];
    expect |d0| == |d1|, ""Test does not meet preconditions and should be removed""
    var r0 := Uint16_32.Uint16Seq.SeqSub(d0, d1);
  }

  method {:test} test10()
  {
    var d0: seq<Uint16_32.Uint16Seq.uint> := [];
    var d1: seq<Uint16_32.Uint16Seq.uint> := [];
    expect |d0| == |d1|, ""Test does not meet preconditions and should be removed""
    var r0 := Uint16_32.Uint16Seq.SeqSub(d0, d1);
  }

  method {:test} test11()
  {
    var d0: seq<Uint16_32.Uint32Seq.uint> := [];
    var r0 := Uint16_32.Uint32Seq.ToNatRight(d0);
  }

  method {:test} test12()
  {
    var d0: seq<Uint16_32.Uint32Seq.uint> := [];
    var r0 := Uint16_32.Uint32Seq.ToNatLeft(d0);
  }

  method {:test} test13()
  {
    var r0 := Uint16_32.Uint32Seq.FromNat(65 as nat);
  }

  method {:test} test14()
  {
    var r0 := Uint16_32.Uint32Seq.FromNat(0 as nat);
  }

  method {:test} test15()
  {
    var d0: seq<Uint16_32.Uint32Seq.uint> := [0 as Uint16_32.Uint32Seq.uint];
    expect |d0| <= 1 as nat, ""Test does not meet preconditions and should be removed""
    var r0 := Uint16_32.Uint32Seq.SeqExtend(d0, 1 as nat);
    expect |r0| == 1 as nat, ""expectation violation""
    expect Uint16_32.Uint32Seq.ToNatRight(r0) == Uint16_32.Uint32Seq.ToNatRight(d0), ""expectation violation""
  }

  method {:test} test16()
  {
    var d0: seq<Uint16_32.Uint32Seq.uint> := [0 as Uint16_32.Uint32Seq.uint, 0 as Uint16_32.Uint32Seq.uint];
    var d1: seq<Uint16_32.Uint32Seq.uint> := [0 as Uint16_32.Uint32Seq.uint, 0 as Uint16_32.Uint32Seq.uint];
    expect |d0| == |d1|, ""Test does not meet preconditions and should be removed""
    var r0 := Uint16_32.Uint32Seq.SeqAdd(d0, d1);
  }

  method {:test} test17()
  {
    var d0: seq<Uint16_32.Uint32Seq.uint> := [342 as Uint16_32.Uint32Seq.uint, 4720 as Uint16_32.Uint32Seq.uint];
    var d1: seq<Uint16_32.Uint32Seq.uint> := [281 as Uint16_32.Uint32Seq.uint, 2283 as Uint16_32.Uint32Seq.uint];
    expect |d0| == |d1|, ""Test does not meet preconditions and should be removed""
    var r0 := Uint16_32.Uint32Seq.SeqAdd(d0, d1);
  }

  method {:test} test18()
  {
    var d0: seq<Uint16_32.Uint32Seq.uint> := [];
    var d1: seq<Uint16_32.Uint32Seq.uint> := [];
    expect |d0| == |d1|, ""Test does not meet preconditions and should be removed""
    var r0 := Uint16_32.Uint32Seq.SeqAdd(d0, d1);
  }

  method {:test} test19()
  {
    var d0: seq<Uint16_32.Uint32Seq.uint> := [1325 as Uint16_32.Uint32Seq.uint, 2331 as Uint16_32.Uint32Seq.uint];
    var d1: seq<Uint16_32.Uint32Seq.uint> := [234 as Uint16_32.Uint32Seq.uint, 1796 as Uint16_32.Uint32Seq.uint];
    expect |d0| == |d1|, ""Test does not meet preconditions and should be removed""
    var r0 := Uint16_32.Uint32Seq.SeqSub(d0, d1);
  }

  method {:test} test20()
  {
    var d0: seq<Uint16_32.Uint32Seq.uint> := [920 as Uint16_32.Uint32Seq.uint, 2061 as Uint16_32.Uint32Seq.uint];
    var d1: seq<Uint16_32.Uint32Seq.uint> := [645 as Uint16_32.Uint32Seq.uint, 2062 as Uint16_32.Uint32Seq.uint];
    expect |d0| == |d1|, ""Test does not meet preconditions and should be removed""
    var r0 := Uint16_32.Uint32Seq.SeqSub(d0, d1);
  }

  method {:test} test21()
  {
    var d0: seq<Uint16_32.Uint32Seq.uint> := [];
    var d1: seq<Uint16_32.Uint32Seq.uint> := [];
    expect |d0| == |d1|, ""Test does not meet preconditions and should be removed""
    var r0 := Uint16_32.Uint32Seq.SeqSub(d0, d1);
  }

  method {:test} test22()
  {
    var d0: seq<Uint16_32.Uint32Seq.uint> := [];
    var r0 := Uint16_32.ToSmall(d0);
    expect |r0| == |d0| * Uint16_32.E(), ""expectation violation""
  }

  method {:test} test23()
  {
    var d0: seq<Uint16_32.Uint16Seq.uint> := [0 as Uint16_32.Uint16Seq.uint, 0 as Uint16_32.Uint16Seq.uint, 0 as Uint16_32.Uint16Seq.uint, 0 as Uint16_32.Uint16Seq.uint, 0 as Uint16_32.Uint16Seq.uint, 0 as Uint16_32.Uint16Seq.uint, 0 as Uint16_32.Uint16Seq.uint, 0 as Uint16_32.Uint16Seq.uint, 0 as Uint16_32.Uint16Seq.uint, 0 as Uint16_32.Uint16Seq.uint, 0 as Uint16_32.Uint16Seq.uint, 0 as Uint16_32.Uint16Seq.uint, 0 as Uint16_32.Uint16Seq.uint, 0 as Uint16_32.Uint16Seq.uint, 0 as Uint16_32.Uint16Seq.uint, 0 as Uint16_32.Uint16Seq.uint, 0 as Uint16_32.Uint16Seq.uint, 0 as Uint16_32.Uint16Seq.uint, 0 as Uint16_32.Uint16Seq.uint, 0 as Uint16_32.Uint16Seq.uint, 0 as Uint16_32.Uint16Seq.uint, 0 as Uint16_32.Uint16Seq.uint, 0 as Uint16_32.Uint16Seq.uint, 0 as Uint16_32.Uint16Seq.uint, 0 as Uint16_32.Uint16Seq.uint, 0 as Uint16_32.Uint16Seq.uint, 0 as Uint16_32.Uint16Seq.uint, 0 as Uint16_32.Uint16Seq.uint, 0 as Uint16_32.Uint16Seq.uint, 0 as Uint16_32.Uint16Seq.uint, 0 as Uint16_32.Uint16Seq.uint, 0 as Uint16_32.Uint16Seq.uint, 0 as Uint16_32.Uint16Seq.uint, 0 as Uint16_32.Uint16Seq.uint, 0 as Uint16_32.Uint16Seq.uint, 0 as Uint16_32.Uint16Seq.uint, 0 as Uint16_32.Uint16Seq.uint, 0 as Uint16_32.Uint16Seq.uint, 0 as Uint16_32.Uint16Seq.uint, 0 as Uint16_32.Uint16Seq.uint, 0 as Uint16_32.Uint16Seq.uint, 0 as Uint16_32.Uint16Seq.uint, 0 as Uint16_32.Uint16Seq.uint, 0 as Uint16_32.Uint16Seq.uint, 0 as Uint16_32.Uint16Seq.uint, 0 as Uint16_32.Uint16Seq.uint, 0 as Uint16_32.Uint16Seq.uint, 0 as Uint16_32.Uint16Seq.uint, 0 as Uint16_32.Uint16Seq.uint, 0 as Uint16_32.Uint16Seq.uint, 0 as Uint16_32.Uint16Seq.uint, 0 as Uint16_32.Uint16Seq.uint, 0 as Uint16_32.Uint16Seq.uint, 0 as Uint16_32.Uint16Seq.uint, 0 as Uint16_32.Uint16Seq.uint, 0 as Uint16_32.Uint16Seq.uint, 0 as Uint16_32.Uint16Seq.uint, 0 as Uint16_32.Uint16Seq.uint, 0 as Uint16_32.Uint16Seq.uint, 0 as Uint16_32.Uint16Seq.uint, 0 as Uint16_32.Uint16Seq.uint, 0 as Uint16_32.Uint16Seq.uint, 0 as Uint16_32.Uint16Seq.uint, 0 as Uint16_32.Uint16Seq.uint, 0 as Uint16_32.Uint16Seq.uint, 0 as Uint16_32.Uint16Seq.uint, 0 as Uint16_32.Uint16Seq.uint, 0 as Uint16_32.Uint16Seq.uint, 0 as Uint16_32.Uint16Seq.uint, 0 as Uint16_32.Uint16Seq.uint, 0 as Uint16_32.Uint16Seq.uint, 0 as Uint16_32.Uint16Seq.uint, 0 as Uint16_32.Uint16Seq.uint, 0 as Uint16_32.Uint16Seq.uint, 0 as Uint16_32.Uint16Seq.uint, 0 as Uint16_32.Uint16Seq.uint, 0 as Uint16_32.Uint16Seq.uint, 0 as Uint16_32.Uint16Seq.uint, 0 as Uint16_32.Uint16Seq.uint, 0 as Uint16_32.Uint16Seq.uint, 0 as Uint16_32.Uint16Seq.uint, 0 as Uint16_32.Uint16Seq.uint, 0 as Uint16_32.Uint16Seq.uint, 0 as Uint16_32.Uint16Seq.uint, 0 as Uint16_32.Uint16Seq.uint, 0 as Uint16_32.Uint16Seq.uint];
    expect |d0| % Uint16_32.E() == 0, ""Test does not meet preconditions and should be removed""
    var r0 := Uint16_32.ToLarge(d0);
    expect |r0| == |d0| / Uint16_32.E(), ""expectation violation""
  }
}

module Uint16_32 refines LittleEndianNatConversions {

  module {:extern ""Uint16__32_mUint16Seq_Compile""} Uint16Seq refines SmallSeq {
    function method BITS(): nat
      ensures BITS() > 1
    {
      16
    }

    function method BASE(): nat
      ensures BASE() > 1
    {
      LemmaPowPositive(2, BITS() - 1);
      LemmaPowStrictlyIncreases(2, BITS() - 1, BITS());
      Pow(2, BITS())
    }

    function method {:opaque} {:fuel 0, 0} ToNatRight(xs: seq<uint>): nat
      decreases xs
    {
      if |xs| == 0 then
        0
      else
        LemmaMulNonnegativeAuto(); ToNatRight(DropFirst(xs)) * BASE() + First(xs)
    }

    function method {:opaque} {:fuel 0, 0} ToNatLeft(xs: seq<uint>): nat
      decreases xs
    {
      if |xs| == 0 then
        0
      else
        LemmaPowPositiveAuto(); LemmaMulNonnegativeAuto(); ToNatLeft(DropLast(xs)) + Last(xs) * Pow(BASE(), |xs| - 1)
    }

    lemma {:vcs_split_on_every_assert} /*{:_induction xs}*/ LemmaToNatLeftEqToNatRight(xs: seq<uint>)
      ensures ToNatRight(xs) == ToNatLeft(xs)
      decreases xs
    {
      reveal ToNatRight();
      reveal ToNatLeft();
      if xs == [] {
      } else {
        if DropLast(xs) == [] {
          calc {
            ToNatLeft(xs);
            Last(xs) * Pow(BASE(), |xs| - 1);
            {
              reveal Pow();
            }
            Last(xs);
            First(xs);
            {
              assert ToNatRight(DropFirst(xs)) == 0;
            }
            ToNatRight(xs);
          }
        } else {
          calc {
            ToNatLeft(xs);
            ToNatLeft(DropLast(xs)) + Last(xs) * Pow(BASE(), |xs| - 1);
            {
              LemmaToNatLeftEqToNatRight(DropLast(xs));
            }
            ToNatRight(DropLast(xs)) + Last(xs) * Pow(BASE(), |xs| - 1);
            ToNatRight(DropFirst(DropLast(xs))) * BASE() + First(xs) + Last(xs) * Pow(BASE(), |xs| - 1);
            {
              LemmaToNatLeftEqToNatRight(DropFirst(DropLast(xs)));
            }
            ToNatLeft(DropFirst(DropLast(xs))) * BASE() + First(xs) + Last(xs) * Pow(BASE(), |xs| - 1);
            {
              assert DropFirst(DropLast(xs)) == DropLast(DropFirst(xs));
              reveal Pow();
              LemmaMulProperties();
            }
            ToNatLeft(DropLast(DropFirst(xs))) * BASE() + First(xs) + Last(xs) * Pow(BASE(), |xs| - 2) * BASE();
            {
              LemmaMulIsDistributiveAddOtherWayAuto();
            }
            ToNatLeft(DropFirst(xs)) * BASE() + First(xs);
            {
              LemmaToNatLeftEqToNatRight(DropFirst(xs));
            }
            ToNatRight(xs);
          }
        }
      }
    }

    lemma LemmaToNatLeftEqToNatRightAuto()
      ensures forall xs: seq<uint> :: ToNatRight(xs) == ToNatLeft(xs)
    {
      reveal ToNatRight();
      reveal ToNatLeft();
      forall xs: seq<uint> | true
        ensures ToNatRight(xs) == ToNatLeft(xs)
      {
        LemmaToNatLeftEqToNatRight(xs);
      }
    }

    lemma /*{:_induction xs}*/ LemmaSeqLen1(xs: seq<uint>)
      requires |xs| == 1
      ensures ToNatRight(xs) == First(xs)
      decreases xs
    {
      reveal ToNatRight();
    }

    lemma /*{:_induction xs}*/ LemmaSeqLen2(xs: seq<uint>)
      requires |xs| == 2
      ensures ToNatRight(xs) == First(xs) + xs[1] * BASE()
      decreases xs
    {
      reveal ToNatRight();
      LemmaSeqLen1(DropLast(xs));
    }

    lemma /*{:_induction xs}*/ LemmaSeqAppendZero(xs: seq<uint>)
      ensures ToNatRight(xs + [0]) == ToNatRight(xs)
      decreases xs
    {
      reveal ToNatLeft();
      LemmaToNatLeftEqToNatRightAuto();
      calc {
        ToNatRight(xs + [0]);
        ToNatLeft(xs + [0]);
        ToNatLeft(xs) + 0 * Pow(BASE(), |xs|);
        {
          LemmaMulBasicsAuto();
        }
        ToNatLeft(xs);
        ToNatRight(xs);
      }
    }

    lemma /*{:_induction xs}*/ LemmaSeqNatBound(xs: seq<uint>)
      ensures ToNatRight(xs) < Pow(BASE(), |xs|)
      decreases xs
    {
      reveal Pow();
      if |xs| == 0 {
        reveal ToNatRight();
      } else {
        ghost var len' := |xs| - 1;
        ghost var pow := Pow(BASE(), len');
        calc {
          ToNatRight(xs);
          {
            LemmaToNatLeftEqToNatRight(xs);
          }
          ToNatLeft(xs);
          {
            reveal ToNatLeft();
          }
          ToNatLeft(DropLast(xs)) + Last(xs) * pow;
        <
          {
            LemmaToNatLeftEqToNatRight(DropLast(xs));
            LemmaSeqNatBound(DropLast(xs));
          }
          pow + Last(xs) * pow;
        <=
          {
            LemmaPowPositiveAuto();
            LemmaMulInequalityAuto();
          }
          pow + (BASE() - 1) * pow;
          {
            LemmaMulIsDistributiveAuto();
          }
          Pow(BASE(), len' + 1);
        }
      }
    }

    lemma /*{:_induction xs, i}*/ LemmaSeqPrefix(xs: seq<uint>, i: nat)
      requires 0 <= i <= |xs|
      ensures ToNatRight(xs[..i]) + ToNatRight(xs[i..]) * Pow(BASE(), i) == ToNatRight(xs)
      decreases xs, i
    {
      reveal ToNatRight();
      reveal Pow();
      if i == 1 {
        assert ToNatRight(xs[..1]) == First(xs);
      } else if i > 1 {
        calc {
          ToNatRight(xs[..i]) + ToNatRight(xs[i..]) * Pow(BASE(), i);
          ToNatRight(DropFirst(xs[..i])) * BASE() + First(xs) + ToNatRight(xs[i..]) * Pow(BASE(), i);
          {
            assert DropFirst(xs[..i]) == DropFirst(xs)[..i - 1];
            LemmaMulProperties();
          }
          ToNatRight(DropFirst(xs)[..i - 1]) * BASE() + First(xs) + ToNatRight(xs[i..]) * Pow(BASE(), i - 1) * BASE();
          {
            LemmaMulIsDistributiveAddOtherWayAuto();
          }
          (ToNatRight(DropFirst(xs)[..i - 1]) + ToNatRight(DropFirst(xs)[i - 1..]) * Pow(BASE(), i - 1)) * BASE() + First(xs);
          {
            LemmaSeqPrefix(DropFirst(xs), i - 1);
          }
          ToNatRight(xs);
        }
      }
    }

    lemma /*{:_induction xs, ys}*/ LemmaSeqMswInequality(xs: seq<uint>, ys: seq<uint>)
      requires |xs| == |ys| > 0
      requires Last(xs) < Last(ys)
      ensures ToNatRight(xs) < ToNatRight(ys)
      decreases xs, ys
    {
      reveal ToNatLeft();
      LemmaToNatLeftEqToNatRightAuto();
      ghost var len' := |xs| - 1;
      calc {
        ToNatRight(xs);
        ToNatLeft(xs);
      <
        {
          LemmaSeqNatBound(DropLast(xs));
        }
        Pow(BASE(), len') + Last(xs) * Pow(BASE(), len');
      ==
        {
          LemmaMulIsDistributiveAuto();
        }
        (1 + Last(xs)) * Pow(BASE(), len');
      <=
        {
          LemmaPowPositiveAuto();
          LemmaMulInequalityAuto();
        }
        ToNatLeft(ys);
        ToNatRight(ys);
      }
    }

    lemma /*{:_induction xs, ys}*/ LemmaSeqPrefixNeq(xs: seq<uint>, ys: seq<uint>, i: nat)
      requires 0 <= i <= |xs| == |ys|
      requires ToNatRight(xs[..i]) != ToNatRight(ys[..i])
      ensures ToNatRight(xs) != ToNatRight(ys)
      decreases |xs| - i
    {
      if i == |xs| {
        assert xs[..i] == xs;
        assert ys[..i] == ys;
      } else {
        if xs[i] == ys[i] {
          reveal ToNatLeft();
          assert DropLast(xs[..i + 1]) == xs[..i];
          assert DropLast(ys[..i + 1]) == ys[..i];
          LemmaToNatLeftEqToNatRightAuto();
          assert ToNatRight(xs[..i + 1]) == ToNatLeft(xs[..i + 1]);
        } else if xs[i] < ys[i] {
          LemmaSeqMswInequality(xs[..i + 1], ys[..i + 1]);
        } else {
          LemmaSeqMswInequality(ys[..i + 1], xs[..i + 1]);
        }
        LemmaSeqPrefixNeq(xs, ys, i + 1);
      }
    }

    lemma /*{:_induction xs, ys}*/ LemmaSeqNeq(xs: seq<uint>, ys: seq<uint>)
      requires |xs| == |ys|
      requires xs != ys
      ensures ToNatRight(xs) != ToNatRight(ys)
      decreases xs, ys
    {
      ghost var i: nat, n: nat := 0, |xs|;
      while i < n
        invariant 0 <= i < n
        invariant xs[..i] == ys[..i]
        decreases n - i
      {
        if xs[i] != ys[i] {
          break;
        }
        i := i + 1;
      }
      assert ToNatLeft(xs[..i]) == ToNatLeft(ys[..i]);
      reveal ToNatLeft();
      assert xs[..i + 1][..i] == xs[..i];
      assert ys[..i + 1][..i] == ys[..i];
      LemmaPowPositiveAuto();
      LemmaMulStrictInequalityAuto();
      assert ToNatLeft(xs[..i + 1]) != ToNatLeft(ys[..i + 1]);
      LemmaToNatLeftEqToNatRightAuto();
      LemmaSeqPrefixNeq(xs, ys, i + 1);
    }

    lemma /*{:_induction xs, ys}*/ LemmaSeqEq(xs: seq<uint>, ys: seq<uint>)
      requires |xs| == |ys|
      requires ToNatRight(xs) == ToNatRight(ys)
      ensures xs == ys
      decreases xs, ys
    {
      calc ==> {
        xs != ys;
        {
          LemmaSeqNeq(xs, ys);
        }
        ToNatRight(xs) != ToNatRight(ys);
        false;
      }
    }

    lemma /*{:_induction xs}*/ LemmaSeqLswModEquivalence(xs: seq<uint>)
      requires |xs| >= 1
      ensures IsModEquivalent(ToNatRight(xs), First(xs), BASE())
      decreases xs
    {
      if |xs| == 1 {
        LemmaSeqLen1(xs);
        LemmaModEquivalenceAuto();
      } else {
        assert IsModEquivalent(ToNatRight(xs), First(xs), BASE()) by {
          reveal ToNatRight();
          calc ==> {
            true;
            {
              LemmaModEquivalenceAuto();
            }
            IsModEquivalent(ToNatRight(xs), ToNatRight(DropFirst(xs)) * BASE() + First(xs), BASE());
            {
              LemmaModMultiplesBasicAuto();
            }
            IsModEquivalent(ToNatRight(xs), First(xs), BASE());
          }
        }
      }
    }

    function method {:opaque} {:fuel 0, 0} FromNat(n: nat): (xs: seq<uint>)
      decreases n
    {
      if n == 0 then
        []
      else
        LemmaDivBasicsAuto(); LemmaDivDecreasesAuto(); [n % BASE()] + FromNat(n / BASE())
    }

    lemma /*{:_induction n, len}*/ LemmaFromNatLen(n: nat, len: nat)
      requires Pow(BASE(), len) > n
      ensures |FromNat(n)| <= len
      decreases n, len
    {
      reveal FromNat();
      if n == 0 {
      } else {
        calc {
          |FromNat(n)|;
        ==
          {
            LemmaDivBasicsAuto();
          }
          1 + |FromNat(n / BASE())|;
        <=
          {
            LemmaMultiplyDivideLtAuto();
            LemmaDivDecreasesAuto();
            reveal Pow();
            LemmaFromNatLen(n / BASE(), len - 1);
          }
          len;
        }
      }
    }

    lemma /*{:_induction n}*/ LemmaNatSeqNat(n: nat)
      ensures ToNatRight(FromNat(n)) == n
      decreases n
    {
      reveal ToNatRight();
      reveal FromNat();
      if n == 0 {
      } else {
        calc {
          ToNatRight(FromNat(n));
          {
            LemmaDivBasicsAuto();
          }
          ToNatRight([n % BASE()] + FromNat(n / BASE()));
          n % BASE() + ToNatRight(FromNat(n / BASE())) * BASE();
          {
            LemmaDivDecreasesAuto();
            LemmaNatSeqNat(n / BASE());
          }
          n % BASE() + n / BASE() * BASE();
          {
            LemmaFundamentalDivMod(n, BASE());
          }
          n;
        }
      }
    }

    function method {:opaque} {:fuel 0, 0} SeqExtend(xs: seq<uint>, n: nat): (ys: seq<uint>)
      requires |xs| <= n
      ensures |ys| == n
      ensures ToNatRight(ys) == ToNatRight(xs)
      decreases n - |xs|
    {
      if |xs| >= n then
        xs
      else
        LemmaSeqAppendZero(xs); SeqExtend(xs + [0], n)
    }

    function method {:opaque} {:fuel 0, 0} SeqExtendMultiple(xs: seq<uint>, n: nat): (ys: seq<uint>)
      requires n > 0
      ensures |ys| % n == 0
      ensures ToNatRight(ys) == ToNatRight(xs)
      decreases xs, n
    {
      var newLen: int := |xs| + n - |xs| % n;
      LemmaSubModNoopRight(|xs| + n, |xs|, n);
      LemmaModBasicsAuto();
      assert newLen % n == 0;
      LemmaSeqNatBound(xs);
      LemmaPowIncreasesAuto();
      SeqExtend(xs, newLen)
    }

    function method {:opaque} {:fuel 0, 0} FromNatWithLen(n: nat, len: nat): (xs: seq<uint>)
      requires Pow(BASE(), len) > n
      ensures |xs| == len
      ensures ToNatRight(xs) == n
      decreases n, len
    {
      LemmaFromNatLen(n, len);
      LemmaNatSeqNat(n);
      SeqExtend(FromNat(n), len)
    }

    lemma /*{:_induction xs}*/ LemmaSeqZero(xs: seq<uint>)
      requires ToNatRight(xs) == 0
      ensures forall i: int :: 0 <= i < |xs| ==> xs[i] == 0
      decreases xs
    {
      reveal ToNatRight();
      if |xs| == 0 {
      } else {
        LemmaMulNonnegativeAuto();
        assert First(xs) == 0;
        LemmaMulNonzeroAuto();
        LemmaSeqZero(DropFirst(xs));
      }
    }

    function method {:opaque} {:fuel 0, 0} SeqZero(len: nat): (xs: seq<uint>)
      ensures |xs| == len
      ensures forall i: int :: 0 <= i < |xs| ==> xs[i] == 0
      ensures ToNatRight(xs) == 0
      decreases len
    {
      LemmaPowPositive(BASE(), len);
      var xs: seq<uint> := FromNatWithLen(0, len);
      LemmaSeqZero(xs);
      xs
    }

    lemma /*{:_induction xs}*/ LemmaSeqNatSeq(xs: seq<uint>)
      ensures Pow(BASE(), |xs|) > ToNatRight(xs)
      ensures FromNatWithLen(ToNatRight(xs), |xs|) == xs
      decreases xs
    {
      reveal FromNat();
      reveal ToNatRight();
      LemmaSeqNatBound(xs);
      if |xs| > 0 {
        calc {
          FromNatWithLen(ToNatRight(xs), |xs|) != xs;
          {
            LemmaSeqNeq(FromNatWithLen(ToNatRight(xs), |xs|), xs);
          }
          ToNatRight(FromNatWithLen(ToNatRight(xs), |xs|)) != ToNatRight(xs);
          ToNatRight(xs) != ToNatRight(xs);
          false;
        }
      }
    }

    function method {:opaque} {:fuel 0, 0} SeqAdd(xs: seq<uint>, ys: seq<uint>): (seq<uint>, nat)
      requires |xs| == |ys|
      ensures var (zs: seq<uint>, cout: nat) := SeqAdd(xs, ys); |zs| == |xs| && 0 <= cout <= 1
      decreases xs
    {
      if |xs| == 0 then
        ([], 0)
      else
        var (zs': seq<uint>, cin: nat) := SeqAdd(DropLast(xs), DropLast(ys)); var sum: int := Last(xs) + Last(ys) + cin; var (sum_out: int, cout: int) := if sum < BASE() then (sum, 0) else (sum - BASE(), 1); (zs' + [sum_out], cout)
    }

    lemma /*{:_induction xs, ys, zs}*/ LemmaSeqAdd(xs: seq<uint>, ys: seq<uint>, zs: seq<uint>, cout: nat)
      requires |xs| == |ys|
      requires SeqAdd(xs, ys) == (zs, cout)
      ensures ToNatRight(xs) + ToNatRight(ys) == ToNatRight(zs) + cout * Pow(BASE(), |xs|)
      decreases xs, ys, zs, cout
    {
      reveal SeqAdd();
      if |xs| == 0 {
        reveal ToNatRight();
      } else {
        ghost var pow := Pow(BASE(), |xs| - 1);
        var (zs', cin) := SeqAdd(DropLast(xs), DropLast(ys));
        ghost var sum: int := Last(xs) + Last(ys) + cin;
        ghost var z := if sum < BASE() then sum else sum - BASE();
        assert sum == z + cout * BASE();
        reveal ToNatLeft();
        LemmaToNatLeftEqToNatRightAuto();
        calc {
          ToNatRight(zs);
          ToNatLeft(zs);
          ToNatLeft(zs') + z * pow;
          {
            LemmaSeqAdd(DropLast(xs), DropLast(ys), zs', cin);
          }
          ToNatLeft(DropLast(xs)) + ToNatLeft(DropLast(ys)) - cin * pow + z * pow;
          {
            LemmaMulEqualityAuto();
            assert sum * pow == (z + cout * BASE()) * pow;
            LemmaMulIsDistributiveAuto();
          }
          ToNatLeft(xs) + ToNatLeft(ys) - cout * BASE() * pow;
          {
            LemmaMulIsAssociative(cout, BASE(), pow);
            reveal Pow();
          }
          ToNatLeft(xs) + ToNatLeft(ys) - cout * Pow(BASE(), |xs|);
          ToNatRight(xs) + ToNatRight(ys) - cout * Pow(BASE(), |xs|);
        }
      }
    }

    function method {:opaque} {:fuel 0, 0} SeqSub(xs: seq<uint>, ys: seq<uint>): (seq<uint>, nat)
      requires |xs| == |ys|
      ensures var (zs: seq<uint>, cout: nat) := SeqSub(xs, ys); |zs| == |xs| && 0 <= cout <= 1
      decreases xs
    {
      if |xs| == 0 then
        ([], 0)
      else
        var (zs: seq<uint>, cin: nat) := SeqSub(DropLast(xs), DropLast(ys)); var (diff_out: int, cout: int) := if Last(xs) >= Last(ys) + cin then (Last(xs) - Last(ys) - cin, 0) else (BASE() + Last(xs) - Last(ys) - cin, 1); (zs + [diff_out], cout)
    }

    lemma /*{:_induction xs, ys, zs}*/ LemmaSeqSub(xs: seq<uint>, ys: seq<uint>, zs: seq<uint>, cout: nat)
      requires |xs| == |ys|
      requires SeqSub(xs, ys) == (zs, cout)
      ensures ToNatRight(xs) - ToNatRight(ys) + cout * Pow(BASE(), |xs|) == ToNatRight(zs)
      decreases xs, ys, zs, cout
    {
      reveal SeqSub();
      if |xs| == 0 {
        reveal ToNatRight();
      } else {
        ghost var pow := Pow(BASE(), |xs| - 1);
        var (zs', cin) := SeqSub(DropLast(xs), DropLast(ys));
        ghost var z := if Last(xs) >= Last(ys) + cin then Last(xs) - Last(ys) - cin else BASE() + Last(xs) - Last(ys) - cin;
        assert cout * BASE() + Last(xs) - cin - Last(ys) == z;
        reveal ToNatLeft();
        LemmaToNatLeftEqToNatRightAuto();
        calc {
          ToNatRight(zs);
          ToNatLeft(zs);
          ToNatLeft(zs') + z * pow;
          {
            LemmaSeqSub(DropLast(xs), DropLast(ys), zs', cin);
          }
          ToNatLeft(DropLast(xs)) - ToNatLeft(DropLast(ys)) + cin * pow + z * pow;
          {
            LemmaMulEqualityAuto();
            assert pow * (cout * BASE() + Last(xs) - cin - Last(ys)) == pow * z;
            LemmaMulIsDistributiveAuto();
          }
          ToNatLeft(xs) - ToNatLeft(ys) + cout * BASE() * pow;
          {
            LemmaMulIsAssociative(cout, BASE(), pow);
            reveal Pow();
          }
          ToNatLeft(xs) - ToNatLeft(ys) + cout * Pow(BASE(), |xs|);
          ToNatRight(xs) - ToNatRight(ys) + cout * Pow(BASE(), |xs|);
        }
      }
    }

    import opened DivMod

    import opened Mul

    import opened Power

    import opened Seq

    type uint = i: int
      | 0 <= i < BASE()
  }

  module {:extern ""Uint16__32_mUint32Seq_Compile""} Uint32Seq refines LargeSeq {

    import Small = Uint16Seq
    function method BITS(): nat
      ensures BITS() > Small.BITS() && BITS() % Small.BITS() == 0
    {
      32
    }

    function method BASE(): nat
      ensures BASE() > 1
    {
      LemmaPowPositive(2, BITS() - 1);
      LemmaPowStrictlyIncreases(2, BITS() - 1, BITS());
      Pow(2, BITS())
    }

    function method {:opaque} {:fuel 0, 0} ToNatRight(xs: seq<uint>): nat
      decreases xs
    {
      if |xs| == 0 then
        0
      else
        LemmaMulNonnegativeAuto(); ToNatRight(DropFirst(xs)) * BASE() + First(xs)
    }

    function method {:opaque} {:fuel 0, 0} ToNatLeft(xs: seq<uint>): nat
      decreases xs
    {
      if |xs| == 0 then
        0
      else
        LemmaPowPositiveAuto(); LemmaMulNonnegativeAuto(); ToNatLeft(DropLast(xs)) + Last(xs) * Pow(BASE(), |xs| - 1)
    }

    lemma {:vcs_split_on_every_assert} /*{:_induction xs}*/ LemmaToNatLeftEqToNatRight(xs: seq<uint>)
      ensures ToNatRight(xs) == ToNatLeft(xs)
      decreases xs
    {
      reveal ToNatRight();
      reveal ToNatLeft();
      if xs == [] {
      } else {
        if DropLast(xs) == [] {
          calc {
            ToNatLeft(xs);
            Last(xs) * Pow(BASE(), |xs| - 1);
            {
              reveal Pow();
            }
            Last(xs);
            First(xs);
            {
              assert ToNatRight(DropFirst(xs)) == 0;
            }
            ToNatRight(xs);
          }
        } else {
          calc {
            ToNatLeft(xs);
            ToNatLeft(DropLast(xs)) + Last(xs) * Pow(BASE(), |xs| - 1);
            {
              LemmaToNatLeftEqToNatRight(DropLast(xs));
            }
            ToNatRight(DropLast(xs)) + Last(xs) * Pow(BASE(), |xs| - 1);
            ToNatRight(DropFirst(DropLast(xs))) * BASE() + First(xs) + Last(xs) * Pow(BASE(), |xs| - 1);
            {
              LemmaToNatLeftEqToNatRight(DropFirst(DropLast(xs)));
            }
            ToNatLeft(DropFirst(DropLast(xs))) * BASE() + First(xs) + Last(xs) * Pow(BASE(), |xs| - 1);
            {
              assert DropFirst(DropLast(xs)) == DropLast(DropFirst(xs));
              reveal Pow();
              LemmaMulProperties();
            }
            ToNatLeft(DropLast(DropFirst(xs))) * BASE() + First(xs) + Last(xs) * Pow(BASE(), |xs| - 2) * BASE();
            {
              LemmaMulIsDistributiveAddOtherWayAuto();
            }
            ToNatLeft(DropFirst(xs)) * BASE() + First(xs);
            {
              LemmaToNatLeftEqToNatRight(DropFirst(xs));
            }
            ToNatRight(xs);
          }
        }
      }
    }

    lemma LemmaToNatLeftEqToNatRightAuto()
      ensures forall xs: seq<uint> :: ToNatRight(xs) == ToNatLeft(xs)
    {
      reveal ToNatRight();
      reveal ToNatLeft();
      forall xs: seq<uint> | true
        ensures ToNatRight(xs) == ToNatLeft(xs)
      {
        LemmaToNatLeftEqToNatRight(xs);
      }
    }

    lemma /*{:_induction xs}*/ LemmaSeqLen1(xs: seq<uint>)
      requires |xs| == 1
      ensures ToNatRight(xs) == First(xs)
      decreases xs
    {
      reveal ToNatRight();
    }

    lemma /*{:_induction xs}*/ LemmaSeqLen2(xs: seq<uint>)
      requires |xs| == 2
      ensures ToNatRight(xs) == First(xs) + xs[1] * BASE()
      decreases xs
    {
      reveal ToNatRight();
      LemmaSeqLen1(DropLast(xs));
    }

    lemma /*{:_induction xs}*/ LemmaSeqAppendZero(xs: seq<uint>)
      ensures ToNatRight(xs + [0]) == ToNatRight(xs)
      decreases xs
    {
      reveal ToNatLeft();
      LemmaToNatLeftEqToNatRightAuto();
      calc {
        ToNatRight(xs + [0]);
        ToNatLeft(xs + [0]);
        ToNatLeft(xs) + 0 * Pow(BASE(), |xs|);
        {
          LemmaMulBasicsAuto();
        }
        ToNatLeft(xs);
        ToNatRight(xs);
      }
    }

    lemma /*{:_induction xs}*/ LemmaSeqNatBound(xs: seq<uint>)
      ensures ToNatRight(xs) < Pow(BASE(), |xs|)
      decreases xs
    {
      reveal Pow();
      if |xs| == 0 {
        reveal ToNatRight();
      } else {
        ghost var len' := |xs| - 1;
        ghost var pow := Pow(BASE(), len');
        calc {
          ToNatRight(xs);
          {
            LemmaToNatLeftEqToNatRight(xs);
          }
          ToNatLeft(xs);
          {
            reveal ToNatLeft();
          }
          ToNatLeft(DropLast(xs)) + Last(xs) * pow;
        <
          {
            LemmaToNatLeftEqToNatRight(DropLast(xs));
            LemmaSeqNatBound(DropLast(xs));
          }
          pow + Last(xs) * pow;
        <=
          {
            LemmaPowPositiveAuto();
            LemmaMulInequalityAuto();
          }
          pow + (BASE() - 1) * pow;
          {
            LemmaMulIsDistributiveAuto();
          }
          Pow(BASE(), len' + 1);
        }
      }
    }

    lemma /*{:_induction xs, i}*/ LemmaSeqPrefix(xs: seq<uint>, i: nat)
      requires 0 <= i <= |xs|
      ensures ToNatRight(xs[..i]) + ToNatRight(xs[i..]) * Pow(BASE(), i) == ToNatRight(xs)
      decreases xs, i
    {
      reveal ToNatRight();
      reveal Pow();
      if i == 1 {
        assert ToNatRight(xs[..1]) == First(xs);
      } else if i > 1 {
        calc {
          ToNatRight(xs[..i]) + ToNatRight(xs[i..]) * Pow(BASE(), i);
          ToNatRight(DropFirst(xs[..i])) * BASE() + First(xs) + ToNatRight(xs[i..]) * Pow(BASE(), i);
          {
            assert DropFirst(xs[..i]) == DropFirst(xs)[..i - 1];
            LemmaMulProperties();
          }
          ToNatRight(DropFirst(xs)[..i - 1]) * BASE() + First(xs) + ToNatRight(xs[i..]) * Pow(BASE(), i - 1) * BASE();
          {
            LemmaMulIsDistributiveAddOtherWayAuto();
          }
          (ToNatRight(DropFirst(xs)[..i - 1]) + ToNatRight(DropFirst(xs)[i - 1..]) * Pow(BASE(), i - 1)) * BASE() + First(xs);
          {
            LemmaSeqPrefix(DropFirst(xs), i - 1);
          }
          ToNatRight(xs);
        }
      }
    }

    lemma /*{:_induction xs, ys}*/ LemmaSeqMswInequality(xs: seq<uint>, ys: seq<uint>)
      requires |xs| == |ys| > 0
      requires Last(xs) < Last(ys)
      ensures ToNatRight(xs) < ToNatRight(ys)
      decreases xs, ys
    {
      reveal ToNatLeft();
      LemmaToNatLeftEqToNatRightAuto();
      ghost var len' := |xs| - 1;
      calc {
        ToNatRight(xs);
        ToNatLeft(xs);
      <
        {
          LemmaSeqNatBound(DropLast(xs));
        }
        Pow(BASE(), len') + Last(xs) * Pow(BASE(), len');
      ==
        {
          LemmaMulIsDistributiveAuto();
        }
        (1 + Last(xs)) * Pow(BASE(), len');
      <=
        {
          LemmaPowPositiveAuto();
          LemmaMulInequalityAuto();
        }
        ToNatLeft(ys);
        ToNatRight(ys);
      }
    }

    lemma /*{:_induction xs, ys}*/ LemmaSeqPrefixNeq(xs: seq<uint>, ys: seq<uint>, i: nat)
      requires 0 <= i <= |xs| == |ys|
      requires ToNatRight(xs[..i]) != ToNatRight(ys[..i])
      ensures ToNatRight(xs) != ToNatRight(ys)
      decreases |xs| - i
    {
      if i == |xs| {
        assert xs[..i] == xs;
        assert ys[..i] == ys;
      } else {
        if xs[i] == ys[i] {
          reveal ToNatLeft();
          assert DropLast(xs[..i + 1]) == xs[..i];
          assert DropLast(ys[..i + 1]) == ys[..i];
          LemmaToNatLeftEqToNatRightAuto();
          assert ToNatRight(xs[..i + 1]) == ToNatLeft(xs[..i + 1]);
        } else if xs[i] < ys[i] {
          LemmaSeqMswInequality(xs[..i + 1], ys[..i + 1]);
        } else {
          LemmaSeqMswInequality(ys[..i + 1], xs[..i + 1]);
        }
        LemmaSeqPrefixNeq(xs, ys, i + 1);
      }
    }

    lemma /*{:_induction xs, ys}*/ LemmaSeqNeq(xs: seq<uint>, ys: seq<uint>)
      requires |xs| == |ys|
      requires xs != ys
      ensures ToNatRight(xs) != ToNatRight(ys)
      decreases xs, ys
    {
      ghost var i: nat, n: nat := 0, |xs|;
      while i < n
        invariant 0 <= i < n
        invariant xs[..i] == ys[..i]
        decreases n - i
      {
        if xs[i] != ys[i] {
          break;
        }
        i := i + 1;
      }
      assert ToNatLeft(xs[..i]) == ToNatLeft(ys[..i]);
      reveal ToNatLeft();
      assert xs[..i + 1][..i] == xs[..i];
      assert ys[..i + 1][..i] == ys[..i];
      LemmaPowPositiveAuto();
      LemmaMulStrictInequalityAuto();
      assert ToNatLeft(xs[..i + 1]) != ToNatLeft(ys[..i + 1]);
      LemmaToNatLeftEqToNatRightAuto();
      LemmaSeqPrefixNeq(xs, ys, i + 1);
    }

    lemma /*{:_induction xs, ys}*/ LemmaSeqEq(xs: seq<uint>, ys: seq<uint>)
      requires |xs| == |ys|
      requires ToNatRight(xs) == ToNatRight(ys)
      ensures xs == ys
      decreases xs, ys
    {
      calc ==> {
        xs != ys;
        {
          LemmaSeqNeq(xs, ys);
        }
        ToNatRight(xs) != ToNatRight(ys);
        false;
      }
    }

    lemma /*{:_induction xs}*/ LemmaSeqLswModEquivalence(xs: seq<uint>)
      requires |xs| >= 1
      ensures IsModEquivalent(ToNatRight(xs), First(xs), BASE())
      decreases xs
    {
      if |xs| == 1 {
        LemmaSeqLen1(xs);
        LemmaModEquivalenceAuto();
      } else {
        assert IsModEquivalent(ToNatRight(xs), First(xs), BASE()) by {
          reveal ToNatRight();
          calc ==> {
            true;
            {
              LemmaModEquivalenceAuto();
            }
            IsModEquivalent(ToNatRight(xs), ToNatRight(DropFirst(xs)) * BASE() + First(xs), BASE());
            {
              LemmaModMultiplesBasicAuto();
            }
            IsModEquivalent(ToNatRight(xs), First(xs), BASE());
          }
        }
      }
    }

    function method {:opaque} {:fuel 0, 0} FromNat(n: nat): (xs: seq<uint>)
      decreases n
    {
      if n == 0 then
        []
      else
        LemmaDivBasicsAuto(); LemmaDivDecreasesAuto(); [n % BASE()] + FromNat(n / BASE())
    }

    lemma /*{:_induction n, len}*/ LemmaFromNatLen(n: nat, len: nat)
      requires Pow(BASE(), len) > n
      ensures |FromNat(n)| <= len
      decreases n, len
    {
      reveal FromNat();
      if n == 0 {
      } else {
        calc {
          |FromNat(n)|;
        ==
          {
            LemmaDivBasicsAuto();
          }
          1 + |FromNat(n / BASE())|;
        <=
          {
            LemmaMultiplyDivideLtAuto();
            LemmaDivDecreasesAuto();
            reveal Pow();
            LemmaFromNatLen(n / BASE(), len - 1);
          }
          len;
        }
      }
    }

    lemma /*{:_induction n}*/ LemmaNatSeqNat(n: nat)
      ensures ToNatRight(FromNat(n)) == n
      decreases n
    {
      reveal ToNatRight();
      reveal FromNat();
      if n == 0 {
      } else {
        calc {
          ToNatRight(FromNat(n));
          {
            LemmaDivBasicsAuto();
          }
          ToNatRight([n % BASE()] + FromNat(n / BASE()));
          n % BASE() + ToNatRight(FromNat(n / BASE())) * BASE();
          {
            LemmaDivDecreasesAuto();
            LemmaNatSeqNat(n / BASE());
          }
          n % BASE() + n / BASE() * BASE();
          {
            LemmaFundamentalDivMod(n, BASE());
          }
          n;
        }
      }
    }

    function method {:opaque} {:fuel 0, 0} SeqExtend(xs: seq<uint>, n: nat): (ys: seq<uint>)
      requires |xs| <= n
      ensures |ys| == n
      ensures ToNatRight(ys) == ToNatRight(xs)
      decreases n - |xs|
    {
      if |xs| >= n then
        xs
      else
        LemmaSeqAppendZero(xs); SeqExtend(xs + [0], n)
    }

    function method {:opaque} {:fuel 0, 0} SeqExtendMultiple(xs: seq<uint>, n: nat): (ys: seq<uint>)
      requires n > 0
      ensures |ys| % n == 0
      ensures ToNatRight(ys) == ToNatRight(xs)
      decreases xs, n
    {
      var newLen: int := |xs| + n - |xs| % n;
      LemmaSubModNoopRight(|xs| + n, |xs|, n);
      LemmaModBasicsAuto();
      assert newLen % n == 0;
      LemmaSeqNatBound(xs);
      LemmaPowIncreasesAuto();
      SeqExtend(xs, newLen)
    }

    function method {:opaque} {:fuel 0, 0} FromNatWithLen(n: nat, len: nat): (xs: seq<uint>)
      requires Pow(BASE(), len) > n
      ensures |xs| == len
      ensures ToNatRight(xs) == n
      decreases n, len
    {
      LemmaFromNatLen(n, len);
      LemmaNatSeqNat(n);
      SeqExtend(FromNat(n), len)
    }

    lemma /*{:_induction xs}*/ LemmaSeqZero(xs: seq<uint>)
      requires ToNatRight(xs) == 0
      ensures forall i: int :: 0 <= i < |xs| ==> xs[i] == 0
      decreases xs
    {
      reveal ToNatRight();
      if |xs| == 0 {
      } else {
        LemmaMulNonnegativeAuto();
        assert First(xs) == 0;
        LemmaMulNonzeroAuto();
        LemmaSeqZero(DropFirst(xs));
      }
    }

    function method {:opaque} {:fuel 0, 0} SeqZero(len: nat): (xs: seq<uint>)
      ensures |xs| == len
      ensures forall i: int :: 0 <= i < |xs| ==> xs[i] == 0
      ensures ToNatRight(xs) == 0
      decreases len
    {
      LemmaPowPositive(BASE(), len);
      var xs: seq<uint> := FromNatWithLen(0, len);
      LemmaSeqZero(xs);
      xs
    }

    lemma /*{:_induction xs}*/ LemmaSeqNatSeq(xs: seq<uint>)
      ensures Pow(BASE(), |xs|) > ToNatRight(xs)
      ensures FromNatWithLen(ToNatRight(xs), |xs|) == xs
      decreases xs
    {
      reveal FromNat();
      reveal ToNatRight();
      LemmaSeqNatBound(xs);
      if |xs| > 0 {
        calc {
          FromNatWithLen(ToNatRight(xs), |xs|) != xs;
          {
            LemmaSeqNeq(FromNatWithLen(ToNatRight(xs), |xs|), xs);
          }
          ToNatRight(FromNatWithLen(ToNatRight(xs), |xs|)) != ToNatRight(xs);
          ToNatRight(xs) != ToNatRight(xs);
          false;
        }
      }
    }

    function method {:opaque} {:fuel 0, 0} SeqAdd(xs: seq<uint>, ys: seq<uint>): (seq<uint>, nat)
      requires |xs| == |ys|
      ensures var (zs: seq<uint>, cout: nat) := SeqAdd(xs, ys); |zs| == |xs| && 0 <= cout <= 1
      decreases xs
    {
      if |xs| == 0 then
        ([], 0)
      else
        var (zs': seq<uint>, cin: nat) := SeqAdd(DropLast(xs), DropLast(ys)); var sum: int := Last(xs) + Last(ys) + cin; var (sum_out: int, cout: int) := if sum < BASE() then (sum, 0) else (sum - BASE(), 1); (zs' + [sum_out], cout)
    }

    lemma /*{:_induction xs, ys, zs}*/ LemmaSeqAdd(xs: seq<uint>, ys: seq<uint>, zs: seq<uint>, cout: nat)
      requires |xs| == |ys|
      requires SeqAdd(xs, ys) == (zs, cout)
      ensures ToNatRight(xs) + ToNatRight(ys) == ToNatRight(zs) + cout * Pow(BASE(), |xs|)
      decreases xs, ys, zs, cout
    {
      reveal SeqAdd();
      if |xs| == 0 {
        reveal ToNatRight();
      } else {
        ghost var pow := Pow(BASE(), |xs| - 1);
        var (zs', cin) := SeqAdd(DropLast(xs), DropLast(ys));
        ghost var sum: int := Last(xs) + Last(ys) + cin;
        ghost var z := if sum < BASE() then sum else sum - BASE();
        assert sum == z + cout * BASE();
        reveal ToNatLeft();
        LemmaToNatLeftEqToNatRightAuto();
        calc {
          ToNatRight(zs);
          ToNatLeft(zs);
          ToNatLeft(zs') + z * pow;
          {
            LemmaSeqAdd(DropLast(xs), DropLast(ys), zs', cin);
          }
          ToNatLeft(DropLast(xs)) + ToNatLeft(DropLast(ys)) - cin * pow + z * pow;
          {
            LemmaMulEqualityAuto();
            assert sum * pow == (z + cout * BASE()) * pow;
            LemmaMulIsDistributiveAuto();
          }
          ToNatLeft(xs) + ToNatLeft(ys) - cout * BASE() * pow;
          {
            LemmaMulIsAssociative(cout, BASE(), pow);
            reveal Pow();
          }
          ToNatLeft(xs) + ToNatLeft(ys) - cout * Pow(BASE(), |xs|);
          ToNatRight(xs) + ToNatRight(ys) - cout * Pow(BASE(), |xs|);
        }
      }
    }

    function method {:opaque} {:fuel 0, 0} SeqSub(xs: seq<uint>, ys: seq<uint>): (seq<uint>, nat)
      requires |xs| == |ys|
      ensures var (zs: seq<uint>, cout: nat) := SeqSub(xs, ys); |zs| == |xs| && 0 <= cout <= 1
      decreases xs
    {
      if |xs| == 0 then
        ([], 0)
      else
        var (zs: seq<uint>, cin: nat) := SeqSub(DropLast(xs), DropLast(ys)); var (diff_out: int, cout: int) := if Last(xs) >= Last(ys) + cin then (Last(xs) - Last(ys) - cin, 0) else (BASE() + Last(xs) - Last(ys) - cin, 1); (zs + [diff_out], cout)
    }

    lemma /*{:_induction xs, ys, zs}*/ LemmaSeqSub(xs: seq<uint>, ys: seq<uint>, zs: seq<uint>, cout: nat)
      requires |xs| == |ys|
      requires SeqSub(xs, ys) == (zs, cout)
      ensures ToNatRight(xs) - ToNatRight(ys) + cout * Pow(BASE(), |xs|) == ToNatRight(zs)
      decreases xs, ys, zs, cout
    {
      reveal SeqSub();
      if |xs| == 0 {
        reveal ToNatRight();
      } else {
        ghost var pow := Pow(BASE(), |xs| - 1);
        var (zs', cin) := SeqSub(DropLast(xs), DropLast(ys));
        ghost var z := if Last(xs) >= Last(ys) + cin then Last(xs) - Last(ys) - cin else BASE() + Last(xs) - Last(ys) - cin;
        assert cout * BASE() + Last(xs) - cin - Last(ys) == z;
        reveal ToNatLeft();
        LemmaToNatLeftEqToNatRightAuto();
        calc {
          ToNatRight(zs);
          ToNatLeft(zs);
          ToNatLeft(zs') + z * pow;
          {
            LemmaSeqSub(DropLast(xs), DropLast(ys), zs', cin);
          }
          ToNatLeft(DropLast(xs)) - ToNatLeft(DropLast(ys)) + cin * pow + z * pow;
          {
            LemmaMulEqualityAuto();
            assert pow * (cout * BASE() + Last(xs) - cin - Last(ys)) == pow * z;
            LemmaMulIsDistributiveAuto();
          }
          ToNatLeft(xs) - ToNatLeft(ys) + cout * BASE() * pow;
          {
            LemmaMulIsAssociative(cout, BASE(), pow);
            reveal Pow();
          }
          ToNatLeft(xs) - ToNatLeft(ys) + cout * Pow(BASE(), |xs|);
          ToNatRight(xs) - ToNatRight(ys) + cout * Pow(BASE(), |xs|);
        }
      }
    }

    import opened DivMod

    import opened Mul

    import opened Power

    import opened Seq

    type uint = i: int
      | 0 <= i < BASE()
  }

  import opened Large = Uint32Seq

  import Small = Large.Small
  function method E(): (E: nat)
    ensures Pow(Small.BASE(), E) == Large.BASE()
    ensures E > 0
  {
    LemmaDivBasicsAuto();
    LemmaPowMultipliesAuto();
    LemmaFundamentalDivMod(Large.BITS(), Small.BITS());
    Large.BITS() / Small.BITS()
  }

  function method {:opaque} {:fuel 0, 0} ToSmall(xs: seq<Large.uint>): (ys: seq<Small.uint>)
    ensures |ys| == |xs| * E()
    decreases xs
  {
    if |xs| == 0 then
      []
    else
      LemmaMulIsDistributiveAddOtherWay(E(), 1, |xs| - 1); Small.FromNatWithLen(First(xs), E()) + ToSmall(DropFirst(xs))
  }

  function method {:opaque} {:fuel 0, 0} ToLarge(xs: seq<Small.uint>): (ys: seq<Large.uint>)
    requires |xs| % E() == 0
    ensures |ys| == |xs| / E()
    decreases xs
  {
    if |xs| == 0 then
      LemmaDivBasicsAuto();
      []
    else
      LemmaModIsZero(|xs|, E()); assert |xs| >= E(); Small.LemmaSeqNatBound(xs[..E()]); LemmaModSubMultiplesVanishAuto(); LemmaDivMinusOne(|xs|, E()); [Small.ToNatRight(xs[..E()]) as Large.uint] + ToLarge(xs[E()..])
  }

  lemma /*{:_induction xs}*/ LemmaToSmall(xs: seq<Large.uint>)
    ensures Small.ToNatRight(ToSmall(xs)) == Large.ToNatRight(xs)
    decreases xs
  {
    reveal Small.ToNatRight();
    reveal Large.ToNatRight();
    reveal ToSmall();
    if |xs| == 0 {
    } else {
      calc {
        Small.ToNatRight(ToSmall(xs));
        Small.ToNatRight(Small.FromNatWithLen(First(xs), E()) + ToSmall(DropFirst(xs)));
        {
          Small.LemmaSeqPrefix(Small.FromNatWithLen(First(xs), E()) + ToSmall(DropFirst(xs)), E());
          LemmaToSmall(DropFirst(xs));
        }
        First(xs) + Large.ToNatRight(DropFirst(xs)) * Pow(Small.BASE(), E());
        {
          assert Pow(Small.BASE(), E()) == Large.BASE();
        }
        Large.ToNatRight(xs);
      }
    }
  }

  lemma /*{:_induction xs}*/ LemmaToLarge(xs: seq<Small.uint>)
    requires |xs| % E() == 0
    ensures Large.ToNatRight(ToLarge(xs)) == Small.ToNatRight(xs)
    decreases xs
  {
    reveal Large.ToNatRight();
    reveal Small.ToNatRight();
    reveal ToLarge();
    if |xs| == 0 {
    } else {
      calc {
        Large.ToNatRight(ToLarge(xs));
        {
          LemmaModIsZero(|xs|, E());
          LemmaModSubMultiplesVanishAuto();
          Small.LemmaSeqNatBound(xs[..E()]);
        }
        Large.ToNatRight([Small.ToNatRight(xs[..E()]) as Large.uint] + ToLarge(xs[E()..]));
        {
          LemmaToLarge(xs[E()..]);
        }
        Small.ToNatRight(xs[..E()]) + Small.ToNatRight(xs[E()..]) * Pow(Small.BASE(), E());
        {
          Small.LemmaSeqPrefix(xs, E());
        }
        Small.ToNatRight(xs);
      }
    }
  }

  lemma /*{:_induction xs, ys}*/ LemmaToSmallIsInjective(xs: seq<Large.uint>, ys: seq<Large.uint>)
    requires ToSmall(xs) == ToSmall(ys)
    requires |xs| == |ys|
    ensures xs == ys
    decreases xs, ys
  {
    LemmaToSmall(xs);
    LemmaToSmall(ys);
    assert Large.ToNatRight(xs) == Large.ToNatRight(ys);
    Large.LemmaSeqEq(xs, ys);
  }

  lemma /*{:_induction xs, ys}*/ LemmaToLargeIsInjective(xs: seq<Small.uint>, ys: seq<Small.uint>)
    requires |xs| % E() == |ys| % E() == 0
    requires ToLarge(xs) == ToLarge(ys)
    requires |xs| == |ys|
    ensures xs == ys
    decreases xs, ys
  {
    LemmaToLarge(xs);
    LemmaToLarge(ys);
    assert Small.ToNatRight(xs) == Small.ToNatRight(ys);
    Small.LemmaSeqEq(xs, ys);
  }

  lemma /*{:_induction xs}*/ LemmaSmallLargeSmall(xs: seq<Small.uint>)
    requires |xs| % E() == 0
    ensures ToSmall(ToLarge(xs)) == xs
    decreases xs
  {
    reveal ToSmall();
    reveal ToLarge();
    if |xs| == 0 {
    } else {
      calc {
        ToSmall(ToLarge(xs));
        {
          LemmaModIsZero(|xs|, E());
          Small.LemmaSeqNatBound(xs[..E()]);
          LemmaModSubMultiplesVanishAuto();
        }
        ToSmall([Small.ToNatRight(xs[..E()]) as Large.uint] + ToLarge(xs[E()..]));
        Small.FromNatWithLen(Small.ToNatRight(xs[..E()]), E()) + ToSmall(ToLarge(xs[E()..]));
        {
          Small.LemmaSeqNatSeq(xs[..E()]);
          LemmaSmallLargeSmall(xs[E()..]);
        }
        xs;
      }
    }
  }

  lemma /*{:_induction xs}*/ LemmaLargeSmallLarge(xs: seq<Large.uint>)
    ensures |ToSmall(xs)| % E() == 0
    ensures ToLarge(ToSmall(xs)) == xs
    decreases xs
  {
    reveal ToSmall();
    reveal ToLarge();
    LemmaModMultiplesBasicAuto();
    if |xs| == 0 {
    } else {
      calc {
        ToLarge(ToSmall(xs));
        ToLarge(Small.FromNatWithLen(First(xs), E()) + ToSmall(DropFirst(xs)));
        [Small.ToNatRight(Small.FromNatWithLen(First(xs), E())) as Large.uint] + ToLarge(ToSmall(DropFirst(xs)));
        [First(xs)] + ToLarge(ToSmall(DropFirst(xs)));
        {
          LemmaLargeSmallLarge(DropFirst(xs));
        }
        [First(xs)] + DropFirst(xs);
        xs;
      }
    }
  }

  import opened DivMod

  import opened Mul

  import opened Power

  import opened Seq
}

module srcCollectionsSequencesUint8_64dfyUnitTests {

  import Uint8_64

  import Uint8Seq = Uint8_64.Uint8Seq

  import Uint64Seq = Uint8_64.Uint64Seq

  import DivMod

  import DivInternalsNonlinear

  import DivInternals

  import GeneralInternals

  import ModInternals

  import MulInternals

  import MulInternalsNonlinear

  import Mul

  import ModInternalsNonlinear

  import Power

  import Seq

  import Wrappers

  import Math
  method {:test} test0()
  {
    var d0: seq<Uint8_64.Uint8Seq.uint> := [];
    var r0 := Uint8_64.Uint8Seq.ToNatRight(d0);
  }

  method {:test} test1()
  {
    var d0: seq<Uint8_64.Uint8Seq.uint> := [];
    var r0 := Uint8_64.Uint8Seq.ToNatLeft(d0);
  }

  method {:test} test2()
  {
    var r0 := Uint8_64.Uint8Seq.FromNat(65 as nat);
  }

  method {:test} test3()
  {
    var r0 := Uint8_64.Uint8Seq.FromNat(0 as nat);
  }

  method {:test} test4()
  {
    var d0: seq<Uint8_64.Uint8Seq.uint> := [0 as Uint8_64.Uint8Seq.uint];
    expect |d0| <= 1 as nat, ""Test does not meet preconditions and should be removed""
    var r0 := Uint8_64.Uint8Seq.SeqExtend(d0, 1 as nat);
    expect |r0| == 1 as nat, ""expectation violation""
    expect Uint8_64.Uint8Seq.ToNatRight(r0) == Uint8_64.Uint8Seq.ToNatRight(d0), ""expectation violation""
  }

  method {:test} test5()
  {
    var d0: seq<Uint8_64.Uint8Seq.uint> := [0 as Uint8_64.Uint8Seq.uint, 0 as Uint8_64.Uint8Seq.uint];
    var d1: seq<Uint8_64.Uint8Seq.uint> := [0 as Uint8_64.Uint8Seq.uint, 0 as Uint8_64.Uint8Seq.uint];
    expect |d0| == |d1|, ""Test does not meet preconditions and should be removed""
    var r0 := Uint8_64.Uint8Seq.SeqAdd(d0, d1);
  }

  method {:test} test6()
  {
    var d0: seq<Uint8_64.Uint8Seq.uint> := [12 as Uint8_64.Uint8Seq.uint, 2283 as Uint8_64.Uint8Seq.uint];
    var d1: seq<Uint8_64.Uint8Seq.uint> := [281 as Uint8_64.Uint8Seq.uint, 11138 as Uint8_64.Uint8Seq.uint];
    expect |d0| == |d1|, ""Test does not meet preconditions and should be removed""
    var r0 := Uint8_64.Uint8Seq.SeqAdd(d0, d1);
  }

  method {:test} test7()
  {
    var d0: seq<Uint8_64.Uint8Seq.uint> := [];
    var d1: seq<Uint8_64.Uint8Seq.uint> := [];
    expect |d0| == |d1|, ""Test does not meet preconditions and should be removed""
    var r0 := Uint8_64.Uint8Seq.SeqAdd(d0, d1);
  }

  method {:test} test8()
  {
    var d0: seq<Uint8_64.Uint8Seq.uint> := [1325 as Uint8_64.Uint8Seq.uint, 2331 as Uint8_64.Uint8Seq.uint];
    var d1: seq<Uint8_64.Uint8Seq.uint> := [234 as Uint8_64.Uint8Seq.uint, 1796 as Uint8_64.Uint8Seq.uint];
    expect |d0| == |d1|, ""Test does not meet preconditions and should be removed""
    var r0 := Uint8_64.Uint8Seq.SeqSub(d0, d1);
  }

  method {:test} test9()
  {
    var d0: seq<Uint8_64.Uint8Seq.uint> := [920 as Uint8_64.Uint8Seq.uint, 2061 as Uint8_64.Uint8Seq.uint];
    var d1: seq<Uint8_64.Uint8Seq.uint> := [645 as Uint8_64.Uint8Seq.uint, 2062 as Uint8_64.Uint8Seq.uint];
    expect |d0| == |d1|, ""Test does not meet preconditions and should be removed""
    var r0 := Uint8_64.Uint8Seq.SeqSub(d0, d1);
  }

  method {:test} test10()
  {
    var d0: seq<Uint8_64.Uint8Seq.uint> := [];
    var d1: seq<Uint8_64.Uint8Seq.uint> := [];
    expect |d0| == |d1|, ""Test does not meet preconditions and should be removed""
    var r0 := Uint8_64.Uint8Seq.SeqSub(d0, d1);
  }

  method {:test} test11()
  {
    var d0: seq<Uint8_64.Uint64Seq.uint> := [];
    var r0 := Uint8_64.Uint64Seq.ToNatRight(d0);
  }

  method {:test} test12()
  {
    var d0: seq<Uint8_64.Uint64Seq.uint> := [];
    var r0 := Uint8_64.Uint64Seq.ToNatLeft(d0);
  }

  method {:test} test13()
  {
    var r0 := Uint8_64.Uint64Seq.FromNat(65 as nat);
  }

  method {:test} test14()
  {
    var r0 := Uint8_64.Uint64Seq.FromNat(0 as nat);
  }

  method {:test} test15()
  {
    var d0: seq<Uint8_64.Uint64Seq.uint> := [0 as Uint8_64.Uint64Seq.uint];
    expect |d0| <= 1 as nat, ""Test does not meet preconditions and should be removed""
    var r0 := Uint8_64.Uint64Seq.SeqExtend(d0, 1 as nat);
    expect |r0| == 1 as nat, ""expectation violation""
    expect Uint8_64.Uint64Seq.ToNatRight(r0) == Uint8_64.Uint64Seq.ToNatRight(d0), ""expectation violation""
  }

  method {:test} test16()
  {
    var d0: seq<Uint8_64.Uint64Seq.uint> := [0 as Uint8_64.Uint64Seq.uint, 0 as Uint8_64.Uint64Seq.uint];
    var d1: seq<Uint8_64.Uint64Seq.uint> := [0 as Uint8_64.Uint64Seq.uint, 0 as Uint8_64.Uint64Seq.uint];
    expect |d0| == |d1|, ""Test does not meet preconditions and should be removed""
    var r0 := Uint8_64.Uint64Seq.SeqAdd(d0, d1);
  }

  method {:test} test17()
  {
    var d0: seq<Uint8_64.Uint64Seq.uint> := [342 as Uint8_64.Uint64Seq.uint, 4720 as Uint8_64.Uint64Seq.uint];
    var d1: seq<Uint8_64.Uint64Seq.uint> := [281 as Uint8_64.Uint64Seq.uint, 2283 as Uint8_64.Uint64Seq.uint];
    expect |d0| == |d1|, ""Test does not meet preconditions and should be removed""
    var r0 := Uint8_64.Uint64Seq.SeqAdd(d0, d1);
  }

  method {:test} test18()
  {
    var d0: seq<Uint8_64.Uint64Seq.uint> := [];
    var d1: seq<Uint8_64.Uint64Seq.uint> := [];
    expect |d0| == |d1|, ""Test does not meet preconditions and should be removed""
    var r0 := Uint8_64.Uint64Seq.SeqAdd(d0, d1);
  }

  method {:test} test19()
  {
    var d0: seq<Uint8_64.Uint64Seq.uint> := [1325 as Uint8_64.Uint64Seq.uint, 2331 as Uint8_64.Uint64Seq.uint];
    var d1: seq<Uint8_64.Uint64Seq.uint> := [234 as Uint8_64.Uint64Seq.uint, 1796 as Uint8_64.Uint64Seq.uint];
    expect |d0| == |d1|, ""Test does not meet preconditions and should be removed""
    var r0 := Uint8_64.Uint64Seq.SeqSub(d0, d1);
  }

  method {:test} test20()
  {
    var d0: seq<Uint8_64.Uint64Seq.uint> := [920 as Uint8_64.Uint64Seq.uint, 2061 as Uint8_64.Uint64Seq.uint];
    var d1: seq<Uint8_64.Uint64Seq.uint> := [645 as Uint8_64.Uint64Seq.uint, 2062 as Uint8_64.Uint64Seq.uint];
    expect |d0| == |d1|, ""Test does not meet preconditions and should be removed""
    var r0 := Uint8_64.Uint64Seq.SeqSub(d0, d1);
  }

  method {:test} test21()
  {
    var d0: seq<Uint8_64.Uint64Seq.uint> := [];
    var d1: seq<Uint8_64.Uint64Seq.uint> := [];
    expect |d0| == |d1|, ""Test does not meet preconditions and should be removed""
    var r0 := Uint8_64.Uint64Seq.SeqSub(d0, d1);
  }

  method {:test} test22()
  {
    var d0: seq<Uint8_64.Uint64Seq.uint> := [];
    var r0 := Uint8_64.ToSmall(d0);
    expect |r0| == |d0| * Uint8_64.E(), ""expectation violation""
  }
}

module Uint8_64 refines LittleEndianNatConversions {

  module {:extern ""Uint8__64_mUint8Seq_Compile""} Uint8Seq refines SmallSeq {
    function method BITS(): nat
      ensures BITS() > 1
    {
      8
    }

    function method BASE(): nat
      ensures BASE() > 1
    {
      LemmaPowPositive(2, BITS() - 1);
      LemmaPowStrictlyIncreases(2, BITS() - 1, BITS());
      Pow(2, BITS())
    }

    function method {:opaque} {:fuel 0, 0} ToNatRight(xs: seq<uint>): nat
      decreases xs
    {
      if |xs| == 0 then
        0
      else
        LemmaMulNonnegativeAuto(); ToNatRight(DropFirst(xs)) * BASE() + First(xs)
    }

    function method {:opaque} {:fuel 0, 0} ToNatLeft(xs: seq<uint>): nat
      decreases xs
    {
      if |xs| == 0 then
        0
      else
        LemmaPowPositiveAuto(); LemmaMulNonnegativeAuto(); ToNatLeft(DropLast(xs)) + Last(xs) * Pow(BASE(), |xs| - 1)
    }

    lemma {:vcs_split_on_every_assert} /*{:_induction xs}*/ LemmaToNatLeftEqToNatRight(xs: seq<uint>)
      ensures ToNatRight(xs) == ToNatLeft(xs)
      decreases xs
    {
      reveal ToNatRight();
      reveal ToNatLeft();
      if xs == [] {
      } else {
        if DropLast(xs) == [] {
          calc {
            ToNatLeft(xs);
            Last(xs) * Pow(BASE(), |xs| - 1);
            {
              reveal Pow();
            }
            Last(xs);
            First(xs);
            {
              assert ToNatRight(DropFirst(xs)) == 0;
            }
            ToNatRight(xs);
          }
        } else {
          calc {
            ToNatLeft(xs);
            ToNatLeft(DropLast(xs)) + Last(xs) * Pow(BASE(), |xs| - 1);
            {
              LemmaToNatLeftEqToNatRight(DropLast(xs));
            }
            ToNatRight(DropLast(xs)) + Last(xs) * Pow(BASE(), |xs| - 1);
            ToNatRight(DropFirst(DropLast(xs))) * BASE() + First(xs) + Last(xs) * Pow(BASE(), |xs| - 1);
            {
              LemmaToNatLeftEqToNatRight(DropFirst(DropLast(xs)));
            }
            ToNatLeft(DropFirst(DropLast(xs))) * BASE() + First(xs) + Last(xs) * Pow(BASE(), |xs| - 1);
            {
              assert DropFirst(DropLast(xs)) == DropLast(DropFirst(xs));
              reveal Pow();
              LemmaMulProperties();
            }
            ToNatLeft(DropLast(DropFirst(xs))) * BASE() + First(xs) + Last(xs) * Pow(BASE(), |xs| - 2) * BASE();
            {
              LemmaMulIsDistributiveAddOtherWayAuto();
            }
            ToNatLeft(DropFirst(xs)) * BASE() + First(xs);
            {
              LemmaToNatLeftEqToNatRight(DropFirst(xs));
            }
            ToNatRight(xs);
          }
        }
      }
    }

    lemma LemmaToNatLeftEqToNatRightAuto()
      ensures forall xs: seq<uint> :: ToNatRight(xs) == ToNatLeft(xs)
    {
      reveal ToNatRight();
      reveal ToNatLeft();
      forall xs: seq<uint> | true
        ensures ToNatRight(xs) == ToNatLeft(xs)
      {
        LemmaToNatLeftEqToNatRight(xs);
      }
    }

    lemma /*{:_induction xs}*/ LemmaSeqLen1(xs: seq<uint>)
      requires |xs| == 1
      ensures ToNatRight(xs) == First(xs)
      decreases xs
    {
      reveal ToNatRight();
    }

    lemma /*{:_induction xs}*/ LemmaSeqLen2(xs: seq<uint>)
      requires |xs| == 2
      ensures ToNatRight(xs) == First(xs) + xs[1] * BASE()
      decreases xs
    {
      reveal ToNatRight();
      LemmaSeqLen1(DropLast(xs));
    }

    lemma /*{:_induction xs}*/ LemmaSeqAppendZero(xs: seq<uint>)
      ensures ToNatRight(xs + [0]) == ToNatRight(xs)
      decreases xs
    {
      reveal ToNatLeft();
      LemmaToNatLeftEqToNatRightAuto();
      calc {
        ToNatRight(xs + [0]);
        ToNatLeft(xs + [0]);
        ToNatLeft(xs) + 0 * Pow(BASE(), |xs|);
        {
          LemmaMulBasicsAuto();
        }
        ToNatLeft(xs);
        ToNatRight(xs);
      }
    }

    lemma /*{:_induction xs}*/ LemmaSeqNatBound(xs: seq<uint>)
      ensures ToNatRight(xs) < Pow(BASE(), |xs|)
      decreases xs
    {
      reveal Pow();
      if |xs| == 0 {
        reveal ToNatRight();
      } else {
        ghost var len' := |xs| - 1;
        ghost var pow := Pow(BASE(), len');
        calc {
          ToNatRight(xs);
          {
            LemmaToNatLeftEqToNatRight(xs);
          }
          ToNatLeft(xs);
          {
            reveal ToNatLeft();
          }
          ToNatLeft(DropLast(xs)) + Last(xs) * pow;
        <
          {
            LemmaToNatLeftEqToNatRight(DropLast(xs));
            LemmaSeqNatBound(DropLast(xs));
          }
          pow + Last(xs) * pow;
        <=
          {
            LemmaPowPositiveAuto();
            LemmaMulInequalityAuto();
          }
          pow + (BASE() - 1) * pow;
          {
            LemmaMulIsDistributiveAuto();
          }
          Pow(BASE(), len' + 1);
        }
      }
    }

    lemma /*{:_induction xs, i}*/ LemmaSeqPrefix(xs: seq<uint>, i: nat)
      requires 0 <= i <= |xs|
      ensures ToNatRight(xs[..i]) + ToNatRight(xs[i..]) * Pow(BASE(), i) == ToNatRight(xs)
      decreases xs, i
    {
      reveal ToNatRight();
      reveal Pow();
      if i == 1 {
        assert ToNatRight(xs[..1]) == First(xs);
      } else if i > 1 {
        calc {
          ToNatRight(xs[..i]) + ToNatRight(xs[i..]) * Pow(BASE(), i);
          ToNatRight(DropFirst(xs[..i])) * BASE() + First(xs) + ToNatRight(xs[i..]) * Pow(BASE(), i);
          {
            assert DropFirst(xs[..i]) == DropFirst(xs)[..i - 1];
            LemmaMulProperties();
          }
          ToNatRight(DropFirst(xs)[..i - 1]) * BASE() + First(xs) + ToNatRight(xs[i..]) * Pow(BASE(), i - 1) * BASE();
          {
            LemmaMulIsDistributiveAddOtherWayAuto();
          }
          (ToNatRight(DropFirst(xs)[..i - 1]) + ToNatRight(DropFirst(xs)[i - 1..]) * Pow(BASE(), i - 1)) * BASE() + First(xs);
          {
            LemmaSeqPrefix(DropFirst(xs), i - 1);
          }
          ToNatRight(xs);
        }
      }
    }

    lemma /*{:_induction xs, ys}*/ LemmaSeqMswInequality(xs: seq<uint>, ys: seq<uint>)
      requires |xs| == |ys| > 0
      requires Last(xs) < Last(ys)
      ensures ToNatRight(xs) < ToNatRight(ys)
      decreases xs, ys
    {
      reveal ToNatLeft();
      LemmaToNatLeftEqToNatRightAuto();
      ghost var len' := |xs| - 1;
      calc {
        ToNatRight(xs);
        ToNatLeft(xs);
      <
        {
          LemmaSeqNatBound(DropLast(xs));
        }
        Pow(BASE(), len') + Last(xs) * Pow(BASE(), len');
      ==
        {
          LemmaMulIsDistributiveAuto();
        }
        (1 + Last(xs)) * Pow(BASE(), len');
      <=
        {
          LemmaPowPositiveAuto();
          LemmaMulInequalityAuto();
        }
        ToNatLeft(ys);
        ToNatRight(ys);
      }
    }

    lemma /*{:_induction xs, ys}*/ LemmaSeqPrefixNeq(xs: seq<uint>, ys: seq<uint>, i: nat)
      requires 0 <= i <= |xs| == |ys|
      requires ToNatRight(xs[..i]) != ToNatRight(ys[..i])
      ensures ToNatRight(xs) != ToNatRight(ys)
      decreases |xs| - i
    {
      if i == |xs| {
        assert xs[..i] == xs;
        assert ys[..i] == ys;
      } else {
        if xs[i] == ys[i] {
          reveal ToNatLeft();
          assert DropLast(xs[..i + 1]) == xs[..i];
          assert DropLast(ys[..i + 1]) == ys[..i];
          LemmaToNatLeftEqToNatRightAuto();
          assert ToNatRight(xs[..i + 1]) == ToNatLeft(xs[..i + 1]);
        } else if xs[i] < ys[i] {
          LemmaSeqMswInequality(xs[..i + 1], ys[..i + 1]);
        } else {
          LemmaSeqMswInequality(ys[..i + 1], xs[..i + 1]);
        }
        LemmaSeqPrefixNeq(xs, ys, i + 1);
      }
    }

    lemma /*{:_induction xs, ys}*/ LemmaSeqNeq(xs: seq<uint>, ys: seq<uint>)
      requires |xs| == |ys|
      requires xs != ys
      ensures ToNatRight(xs) != ToNatRight(ys)
      decreases xs, ys
    {
      ghost var i: nat, n: nat := 0, |xs|;
      while i < n
        invariant 0 <= i < n
        invariant xs[..i] == ys[..i]
        decreases n - i
      {
        if xs[i] != ys[i] {
          break;
        }
        i := i + 1;
      }
      assert ToNatLeft(xs[..i]) == ToNatLeft(ys[..i]);
      reveal ToNatLeft();
      assert xs[..i + 1][..i] == xs[..i];
      assert ys[..i + 1][..i] == ys[..i];
      LemmaPowPositiveAuto();
      LemmaMulStrictInequalityAuto();
      assert ToNatLeft(xs[..i + 1]) != ToNatLeft(ys[..i + 1]);
      LemmaToNatLeftEqToNatRightAuto();
      LemmaSeqPrefixNeq(xs, ys, i + 1);
    }

    lemma /*{:_induction xs, ys}*/ LemmaSeqEq(xs: seq<uint>, ys: seq<uint>)
      requires |xs| == |ys|
      requires ToNatRight(xs) == ToNatRight(ys)
      ensures xs == ys
      decreases xs, ys
    {
      calc ==> {
        xs != ys;
        {
          LemmaSeqNeq(xs, ys);
        }
        ToNatRight(xs) != ToNatRight(ys);
        false;
      }
    }

    lemma /*{:_induction xs}*/ LemmaSeqLswModEquivalence(xs: seq<uint>)
      requires |xs| >= 1
      ensures IsModEquivalent(ToNatRight(xs), First(xs), BASE())
      decreases xs
    {
      if |xs| == 1 {
        LemmaSeqLen1(xs);
        LemmaModEquivalenceAuto();
      } else {
        assert IsModEquivalent(ToNatRight(xs), First(xs), BASE()) by {
          reveal ToNatRight();
          calc ==> {
            true;
            {
              LemmaModEquivalenceAuto();
            }
            IsModEquivalent(ToNatRight(xs), ToNatRight(DropFirst(xs)) * BASE() + First(xs), BASE());
            {
              LemmaModMultiplesBasicAuto();
            }
            IsModEquivalent(ToNatRight(xs), First(xs), BASE());
          }
        }
      }
    }

    function method {:opaque} {:fuel 0, 0} FromNat(n: nat): (xs: seq<uint>)
      decreases n
    {
      if n == 0 then
        []
      else
        LemmaDivBasicsAuto(); LemmaDivDecreasesAuto(); [n % BASE()] + FromNat(n / BASE())
    }

    lemma /*{:_induction n, len}*/ LemmaFromNatLen(n: nat, len: nat)
      requires Pow(BASE(), len) > n
      ensures |FromNat(n)| <= len
      decreases n, len
    {
      reveal FromNat();
      if n == 0 {
      } else {
        calc {
          |FromNat(n)|;
        ==
          {
            LemmaDivBasicsAuto();
          }
          1 + |FromNat(n / BASE())|;
        <=
          {
            LemmaMultiplyDivideLtAuto();
            LemmaDivDecreasesAuto();
            reveal Pow();
            LemmaFromNatLen(n / BASE(), len - 1);
          }
          len;
        }
      }
    }

    lemma /*{:_induction n}*/ LemmaNatSeqNat(n: nat)
      ensures ToNatRight(FromNat(n)) == n
      decreases n
    {
      reveal ToNatRight();
      reveal FromNat();
      if n == 0 {
      } else {
        calc {
          ToNatRight(FromNat(n));
          {
            LemmaDivBasicsAuto();
          }
          ToNatRight([n % BASE()] + FromNat(n / BASE()));
          n % BASE() + ToNatRight(FromNat(n / BASE())) * BASE();
          {
            LemmaDivDecreasesAuto();
            LemmaNatSeqNat(n / BASE());
          }
          n % BASE() + n / BASE() * BASE();
          {
            LemmaFundamentalDivMod(n, BASE());
          }
          n;
        }
      }
    }

    function method {:opaque} {:fuel 0, 0} SeqExtend(xs: seq<uint>, n: nat): (ys: seq<uint>)
      requires |xs| <= n
      ensures |ys| == n
      ensures ToNatRight(ys) == ToNatRight(xs)
      decreases n - |xs|
    {
      if |xs| >= n then
        xs
      else
        LemmaSeqAppendZero(xs); SeqExtend(xs + [0], n)
    }

    function method {:opaque} {:fuel 0, 0} SeqExtendMultiple(xs: seq<uint>, n: nat): (ys: seq<uint>)
      requires n > 0
      ensures |ys| % n == 0
      ensures ToNatRight(ys) == ToNatRight(xs)
      decreases xs, n
    {
      var newLen: int := |xs| + n - |xs| % n;
      LemmaSubModNoopRight(|xs| + n, |xs|, n);
      LemmaModBasicsAuto();
      assert newLen % n == 0;
      LemmaSeqNatBound(xs);
      LemmaPowIncreasesAuto();
      SeqExtend(xs, newLen)
    }

    function method {:opaque} {:fuel 0, 0} FromNatWithLen(n: nat, len: nat): (xs: seq<uint>)
      requires Pow(BASE(), len) > n
      ensures |xs| == len
      ensures ToNatRight(xs) == n
      decreases n, len
    {
      LemmaFromNatLen(n, len);
      LemmaNatSeqNat(n);
      SeqExtend(FromNat(n), len)
    }

    lemma /*{:_induction xs}*/ LemmaSeqZero(xs: seq<uint>)
      requires ToNatRight(xs) == 0
      ensures forall i: int :: 0 <= i < |xs| ==> xs[i] == 0
      decreases xs
    {
      reveal ToNatRight();
      if |xs| == 0 {
      } else {
        LemmaMulNonnegativeAuto();
        assert First(xs) == 0;
        LemmaMulNonzeroAuto();
        LemmaSeqZero(DropFirst(xs));
      }
    }

    function method {:opaque} {:fuel 0, 0} SeqZero(len: nat): (xs: seq<uint>)
      ensures |xs| == len
      ensures forall i: int :: 0 <= i < |xs| ==> xs[i] == 0
      ensures ToNatRight(xs) == 0
      decreases len
    {
      LemmaPowPositive(BASE(), len);
      var xs: seq<uint> := FromNatWithLen(0, len);
      LemmaSeqZero(xs);
      xs
    }

    lemma /*{:_induction xs}*/ LemmaSeqNatSeq(xs: seq<uint>)
      ensures Pow(BASE(), |xs|) > ToNatRight(xs)
      ensures FromNatWithLen(ToNatRight(xs), |xs|) == xs
      decreases xs
    {
      reveal FromNat();
      reveal ToNatRight();
      LemmaSeqNatBound(xs);
      if |xs| > 0 {
        calc {
          FromNatWithLen(ToNatRight(xs), |xs|) != xs;
          {
            LemmaSeqNeq(FromNatWithLen(ToNatRight(xs), |xs|), xs);
          }
          ToNatRight(FromNatWithLen(ToNatRight(xs), |xs|)) != ToNatRight(xs);
          ToNatRight(xs) != ToNatRight(xs);
          false;
        }
      }
    }

    function method {:opaque} {:fuel 0, 0} SeqAdd(xs: seq<uint>, ys: seq<uint>): (seq<uint>, nat)
      requires |xs| == |ys|
      ensures var (zs: seq<uint>, cout: nat) := SeqAdd(xs, ys); |zs| == |xs| && 0 <= cout <= 1
      decreases xs
    {
      if |xs| == 0 then
        ([], 0)
      else
        var (zs': seq<uint>, cin: nat) := SeqAdd(DropLast(xs), DropLast(ys)); var sum: int := Last(xs) + Last(ys) + cin; var (sum_out: int, cout: int) := if sum < BASE() then (sum, 0) else (sum - BASE(), 1); (zs' + [sum_out], cout)
    }

    lemma /*{:_induction xs, ys, zs}*/ LemmaSeqAdd(xs: seq<uint>, ys: seq<uint>, zs: seq<uint>, cout: nat)
      requires |xs| == |ys|
      requires SeqAdd(xs, ys) == (zs, cout)
      ensures ToNatRight(xs) + ToNatRight(ys) == ToNatRight(zs) + cout * Pow(BASE(), |xs|)
      decreases xs, ys, zs, cout
    {
      reveal SeqAdd();
      if |xs| == 0 {
        reveal ToNatRight();
      } else {
        ghost var pow := Pow(BASE(), |xs| - 1);
        var (zs', cin) := SeqAdd(DropLast(xs), DropLast(ys));
        ghost var sum: int := Last(xs) + Last(ys) + cin;
        ghost var z := if sum < BASE() then sum else sum - BASE();
        assert sum == z + cout * BASE();
        reveal ToNatLeft();
        LemmaToNatLeftEqToNatRightAuto();
        calc {
          ToNatRight(zs);
          ToNatLeft(zs);
          ToNatLeft(zs') + z * pow;
          {
            LemmaSeqAdd(DropLast(xs), DropLast(ys), zs', cin);
          }
          ToNatLeft(DropLast(xs)) + ToNatLeft(DropLast(ys)) - cin * pow + z * pow;
          {
            LemmaMulEqualityAuto();
            assert sum * pow == (z + cout * BASE()) * pow;
            LemmaMulIsDistributiveAuto();
          }
          ToNatLeft(xs) + ToNatLeft(ys) - cout * BASE() * pow;
          {
            LemmaMulIsAssociative(cout, BASE(), pow);
            reveal Pow();
          }
          ToNatLeft(xs) + ToNatLeft(ys) - cout * Pow(BASE(), |xs|);
          ToNatRight(xs) + ToNatRight(ys) - cout * Pow(BASE(), |xs|);
        }
      }
    }

    function method {:opaque} {:fuel 0, 0} SeqSub(xs: seq<uint>, ys: seq<uint>): (seq<uint>, nat)
      requires |xs| == |ys|
      ensures var (zs: seq<uint>, cout: nat) := SeqSub(xs, ys); |zs| == |xs| && 0 <= cout <= 1
      decreases xs
    {
      if |xs| == 0 then
        ([], 0)
      else
        var (zs: seq<uint>, cin: nat) := SeqSub(DropLast(xs), DropLast(ys)); var (diff_out: int, cout: int) := if Last(xs) >= Last(ys) + cin then (Last(xs) - Last(ys) - cin, 0) else (BASE() + Last(xs) - Last(ys) - cin, 1); (zs + [diff_out], cout)
    }

    lemma /*{:_induction xs, ys, zs}*/ LemmaSeqSub(xs: seq<uint>, ys: seq<uint>, zs: seq<uint>, cout: nat)
      requires |xs| == |ys|
      requires SeqSub(xs, ys) == (zs, cout)
      ensures ToNatRight(xs) - ToNatRight(ys) + cout * Pow(BASE(), |xs|) == ToNatRight(zs)
      decreases xs, ys, zs, cout
    {
      reveal SeqSub();
      if |xs| == 0 {
        reveal ToNatRight();
      } else {
        ghost var pow := Pow(BASE(), |xs| - 1);
        var (zs', cin) := SeqSub(DropLast(xs), DropLast(ys));
        ghost var z := if Last(xs) >= Last(ys) + cin then Last(xs) - Last(ys) - cin else BASE() + Last(xs) - Last(ys) - cin;
        assert cout * BASE() + Last(xs) - cin - Last(ys) == z;
        reveal ToNatLeft();
        LemmaToNatLeftEqToNatRightAuto();
        calc {
          ToNatRight(zs);
          ToNatLeft(zs);
          ToNatLeft(zs') + z * pow;
          {
            LemmaSeqSub(DropLast(xs), DropLast(ys), zs', cin);
          }
          ToNatLeft(DropLast(xs)) - ToNatLeft(DropLast(ys)) + cin * pow + z * pow;
          {
            LemmaMulEqualityAuto();
            assert pow * (cout * BASE() + Last(xs) - cin - Last(ys)) == pow * z;
            LemmaMulIsDistributiveAuto();
          }
          ToNatLeft(xs) - ToNatLeft(ys) + cout * BASE() * pow;
          {
            LemmaMulIsAssociative(cout, BASE(), pow);
            reveal Pow();
          }
          ToNatLeft(xs) - ToNatLeft(ys) + cout * Pow(BASE(), |xs|);
          ToNatRight(xs) - ToNatRight(ys) + cout * Pow(BASE(), |xs|);
        }
      }
    }

    import opened DivMod

    import opened Mul

    import opened Power

    import opened Seq

    type uint = i: int
      | 0 <= i < BASE()
  }

  module {:extern ""Uint8__64_mUint64Seq_Compile""} Uint64Seq refines LargeSeq {

    import Small = Uint8Seq
    function method BITS(): nat
      ensures BITS() > Small.BITS() && BITS() % Small.BITS() == 0
    {
      64
    }

    function method BASE(): nat
      ensures BASE() > 1
    {
      LemmaPowPositive(2, BITS() - 1);
      LemmaPowStrictlyIncreases(2, BITS() - 1, BITS());
      Pow(2, BITS())
    }

    function method {:opaque} {:fuel 0, 0} ToNatRight(xs: seq<uint>): nat
      decreases xs
    {
      if |xs| == 0 then
        0
      else
        LemmaMulNonnegativeAuto(); ToNatRight(DropFirst(xs)) * BASE() + First(xs)
    }

    function method {:opaque} {:fuel 0, 0} ToNatLeft(xs: seq<uint>): nat
      decreases xs
    {
      if |xs| == 0 then
        0
      else
        LemmaPowPositiveAuto(); LemmaMulNonnegativeAuto(); ToNatLeft(DropLast(xs)) + Last(xs) * Pow(BASE(), |xs| - 1)
    }

    lemma {:vcs_split_on_every_assert} /*{:_induction xs}*/ LemmaToNatLeftEqToNatRight(xs: seq<uint>)
      ensures ToNatRight(xs) == ToNatLeft(xs)
      decreases xs
    {
      reveal ToNatRight();
      reveal ToNatLeft();
      if xs == [] {
      } else {
        if DropLast(xs) == [] {
          calc {
            ToNatLeft(xs);
            Last(xs) * Pow(BASE(), |xs| - 1);
            {
              reveal Pow();
            }
            Last(xs);
            First(xs);
            {
              assert ToNatRight(DropFirst(xs)) == 0;
            }
            ToNatRight(xs);
          }
        } else {
          calc {
            ToNatLeft(xs);
            ToNatLeft(DropLast(xs)) + Last(xs) * Pow(BASE(), |xs| - 1);
            {
              LemmaToNatLeftEqToNatRight(DropLast(xs));
            }
            ToNatRight(DropLast(xs)) + Last(xs) * Pow(BASE(), |xs| - 1);
            ToNatRight(DropFirst(DropLast(xs))) * BASE() + First(xs) + Last(xs) * Pow(BASE(), |xs| - 1);
            {
              LemmaToNatLeftEqToNatRight(DropFirst(DropLast(xs)));
            }
            ToNatLeft(DropFirst(DropLast(xs))) * BASE() + First(xs) + Last(xs) * Pow(BASE(), |xs| - 1);
            {
              assert DropFirst(DropLast(xs)) == DropLast(DropFirst(xs));
              reveal Pow();
              LemmaMulProperties();
            }
            ToNatLeft(DropLast(DropFirst(xs))) * BASE() + First(xs) + Last(xs) * Pow(BASE(), |xs| - 2) * BASE();
            {
              LemmaMulIsDistributiveAddOtherWayAuto();
            }
            ToNatLeft(DropFirst(xs)) * BASE() + First(xs);
            {
              LemmaToNatLeftEqToNatRight(DropFirst(xs));
            }
            ToNatRight(xs);
          }
        }
      }
    }

    lemma LemmaToNatLeftEqToNatRightAuto()
      ensures forall xs: seq<uint> :: ToNatRight(xs) == ToNatLeft(xs)
    {
      reveal ToNatRight();
      reveal ToNatLeft();
      forall xs: seq<uint> | true
        ensures ToNatRight(xs) == ToNatLeft(xs)
      {
        LemmaToNatLeftEqToNatRight(xs);
      }
    }

    lemma /*{:_induction xs}*/ LemmaSeqLen1(xs: seq<uint>)
      requires |xs| == 1
      ensures ToNatRight(xs) == First(xs)
      decreases xs
    {
      reveal ToNatRight();
    }

    lemma /*{:_induction xs}*/ LemmaSeqLen2(xs: seq<uint>)
      requires |xs| == 2
      ensures ToNatRight(xs) == First(xs) + xs[1] * BASE()
      decreases xs
    {
      reveal ToNatRight();
      LemmaSeqLen1(DropLast(xs));
    }

    lemma /*{:_induction xs}*/ LemmaSeqAppendZero(xs: seq<uint>)
      ensures ToNatRight(xs + [0]) == ToNatRight(xs)
      decreases xs
    {
      reveal ToNatLeft();
      LemmaToNatLeftEqToNatRightAuto();
      calc {
        ToNatRight(xs + [0]);
        ToNatLeft(xs + [0]);
        ToNatLeft(xs) + 0 * Pow(BASE(), |xs|);
        {
          LemmaMulBasicsAuto();
        }
        ToNatLeft(xs);
        ToNatRight(xs);
      }
    }

    lemma /*{:_induction xs}*/ LemmaSeqNatBound(xs: seq<uint>)
      ensures ToNatRight(xs) < Pow(BASE(), |xs|)
      decreases xs
    {
      reveal Pow();
      if |xs| == 0 {
        reveal ToNatRight();
      } else {
        ghost var len' := |xs| - 1;
        ghost var pow := Pow(BASE(), len');
        calc {
          ToNatRight(xs);
          {
            LemmaToNatLeftEqToNatRight(xs);
          }
          ToNatLeft(xs);
          {
            reveal ToNatLeft();
          }
          ToNatLeft(DropLast(xs)) + Last(xs) * pow;
        <
          {
            LemmaToNatLeftEqToNatRight(DropLast(xs));
            LemmaSeqNatBound(DropLast(xs));
          }
          pow + Last(xs) * pow;
        <=
          {
            LemmaPowPositiveAuto();
            LemmaMulInequalityAuto();
          }
          pow + (BASE() - 1) * pow;
          {
            LemmaMulIsDistributiveAuto();
          }
          Pow(BASE(), len' + 1);
        }
      }
    }

    lemma /*{:_induction xs, i}*/ LemmaSeqPrefix(xs: seq<uint>, i: nat)
      requires 0 <= i <= |xs|
      ensures ToNatRight(xs[..i]) + ToNatRight(xs[i..]) * Pow(BASE(), i) == ToNatRight(xs)
      decreases xs, i
    {
      reveal ToNatRight();
      reveal Pow();
      if i == 1 {
        assert ToNatRight(xs[..1]) == First(xs);
      } else if i > 1 {
        calc {
          ToNatRight(xs[..i]) + ToNatRight(xs[i..]) * Pow(BASE(), i);
          ToNatRight(DropFirst(xs[..i])) * BASE() + First(xs) + ToNatRight(xs[i..]) * Pow(BASE(), i);
          {
            assert DropFirst(xs[..i]) == DropFirst(xs)[..i - 1];
            LemmaMulProperties();
          }
          ToNatRight(DropFirst(xs)[..i - 1]) * BASE() + First(xs) + ToNatRight(xs[i..]) * Pow(BASE(), i - 1) * BASE();
          {
            LemmaMulIsDistributiveAddOtherWayAuto();
          }
          (ToNatRight(DropFirst(xs)[..i - 1]) + ToNatRight(DropFirst(xs)[i - 1..]) * Pow(BASE(), i - 1)) * BASE() + First(xs);
          {
            LemmaSeqPrefix(DropFirst(xs), i - 1);
          }
          ToNatRight(xs);
        }
      }
    }

    lemma /*{:_induction xs, ys}*/ LemmaSeqMswInequality(xs: seq<uint>, ys: seq<uint>)
      requires |xs| == |ys| > 0
      requires Last(xs) < Last(ys)
      ensures ToNatRight(xs) < ToNatRight(ys)
      decreases xs, ys
    {
      reveal ToNatLeft();
      LemmaToNatLeftEqToNatRightAuto();
      ghost var len' := |xs| - 1;
      calc {
        ToNatRight(xs);
        ToNatLeft(xs);
      <
        {
          LemmaSeqNatBound(DropLast(xs));
        }
        Pow(BASE(), len') + Last(xs) * Pow(BASE(), len');
      ==
        {
          LemmaMulIsDistributiveAuto();
        }
        (1 + Last(xs)) * Pow(BASE(), len');
      <=
        {
          LemmaPowPositiveAuto();
          LemmaMulInequalityAuto();
        }
        ToNatLeft(ys);
        ToNatRight(ys);
      }
    }

    lemma /*{:_induction xs, ys}*/ LemmaSeqPrefixNeq(xs: seq<uint>, ys: seq<uint>, i: nat)
      requires 0 <= i <= |xs| == |ys|
      requires ToNatRight(xs[..i]) != ToNatRight(ys[..i])
      ensures ToNatRight(xs) != ToNatRight(ys)
      decreases |xs| - i
    {
      if i == |xs| {
        assert xs[..i] == xs;
        assert ys[..i] == ys;
      } else {
        if xs[i] == ys[i] {
          reveal ToNatLeft();
          assert DropLast(xs[..i + 1]) == xs[..i];
          assert DropLast(ys[..i + 1]) == ys[..i];
          LemmaToNatLeftEqToNatRightAuto();
          assert ToNatRight(xs[..i + 1]) == ToNatLeft(xs[..i + 1]);
        } else if xs[i] < ys[i] {
          LemmaSeqMswInequality(xs[..i + 1], ys[..i + 1]);
        } else {
          LemmaSeqMswInequality(ys[..i + 1], xs[..i + 1]);
        }
        LemmaSeqPrefixNeq(xs, ys, i + 1);
      }
    }

    lemma /*{:_induction xs, ys}*/ LemmaSeqNeq(xs: seq<uint>, ys: seq<uint>)
      requires |xs| == |ys|
      requires xs != ys
      ensures ToNatRight(xs) != ToNatRight(ys)
      decreases xs, ys
    {
      ghost var i: nat, n: nat := 0, |xs|;
      while i < n
        invariant 0 <= i < n
        invariant xs[..i] == ys[..i]
        decreases n - i
      {
        if xs[i] != ys[i] {
          break;
        }
        i := i + 1;
      }
      assert ToNatLeft(xs[..i]) == ToNatLeft(ys[..i]);
      reveal ToNatLeft();
      assert xs[..i + 1][..i] == xs[..i];
      assert ys[..i + 1][..i] == ys[..i];
      LemmaPowPositiveAuto();
      LemmaMulStrictInequalityAuto();
      assert ToNatLeft(xs[..i + 1]) != ToNatLeft(ys[..i + 1]);
      LemmaToNatLeftEqToNatRightAuto();
      LemmaSeqPrefixNeq(xs, ys, i + 1);
    }

    lemma /*{:_induction xs, ys}*/ LemmaSeqEq(xs: seq<uint>, ys: seq<uint>)
      requires |xs| == |ys|
      requires ToNatRight(xs) == ToNatRight(ys)
      ensures xs == ys
      decreases xs, ys
    {
      calc ==> {
        xs != ys;
        {
          LemmaSeqNeq(xs, ys);
        }
        ToNatRight(xs) != ToNatRight(ys);
        false;
      }
    }

    lemma /*{:_induction xs}*/ LemmaSeqLswModEquivalence(xs: seq<uint>)
      requires |xs| >= 1
      ensures IsModEquivalent(ToNatRight(xs), First(xs), BASE())
      decreases xs
    {
      if |xs| == 1 {
        LemmaSeqLen1(xs);
        LemmaModEquivalenceAuto();
      } else {
        assert IsModEquivalent(ToNatRight(xs), First(xs), BASE()) by {
          reveal ToNatRight();
          calc ==> {
            true;
            {
              LemmaModEquivalenceAuto();
            }
            IsModEquivalent(ToNatRight(xs), ToNatRight(DropFirst(xs)) * BASE() + First(xs), BASE());
            {
              LemmaModMultiplesBasicAuto();
            }
            IsModEquivalent(ToNatRight(xs), First(xs), BASE());
          }
        }
      }
    }

    function method {:opaque} {:fuel 0, 0} FromNat(n: nat): (xs: seq<uint>)
      decreases n
    {
      if n == 0 then
        []
      else
        LemmaDivBasicsAuto(); LemmaDivDecreasesAuto(); [n % BASE()] + FromNat(n / BASE())
    }

    lemma /*{:_induction n, len}*/ LemmaFromNatLen(n: nat, len: nat)
      requires Pow(BASE(), len) > n
      ensures |FromNat(n)| <= len
      decreases n, len
    {
      reveal FromNat();
      if n == 0 {
      } else {
        calc {
          |FromNat(n)|;
        ==
          {
            LemmaDivBasicsAuto();
          }
          1 + |FromNat(n / BASE())|;
        <=
          {
            LemmaMultiplyDivideLtAuto();
            LemmaDivDecreasesAuto();
            reveal Pow();
            LemmaFromNatLen(n / BASE(), len - 1);
          }
          len;
        }
      }
    }

    lemma /*{:_induction n}*/ LemmaNatSeqNat(n: nat)
      ensures ToNatRight(FromNat(n)) == n
      decreases n
    {
      reveal ToNatRight();
      reveal FromNat();
      if n == 0 {
      } else {
        calc {
          ToNatRight(FromNat(n));
          {
            LemmaDivBasicsAuto();
          }
          ToNatRight([n % BASE()] + FromNat(n / BASE()));
          n % BASE() + ToNatRight(FromNat(n / BASE())) * BASE();
          {
            LemmaDivDecreasesAuto();
            LemmaNatSeqNat(n / BASE());
          }
          n % BASE() + n / BASE() * BASE();
          {
            LemmaFundamentalDivMod(n, BASE());
          }
          n;
        }
      }
    }

    function method {:opaque} {:fuel 0, 0} SeqExtend(xs: seq<uint>, n: nat): (ys: seq<uint>)
      requires |xs| <= n
      ensures |ys| == n
      ensures ToNatRight(ys) == ToNatRight(xs)
      decreases n - |xs|
    {
      if |xs| >= n then
        xs
      else
        LemmaSeqAppendZero(xs); SeqExtend(xs + [0], n)
    }

    function method {:opaque} {:fuel 0, 0} SeqExtendMultiple(xs: seq<uint>, n: nat): (ys: seq<uint>)
      requires n > 0
      ensures |ys| % n == 0
      ensures ToNatRight(ys) == ToNatRight(xs)
      decreases xs, n
    {
      var newLen: int := |xs| + n - |xs| % n;
      LemmaSubModNoopRight(|xs| + n, |xs|, n);
      LemmaModBasicsAuto();
      assert newLen % n == 0;
      LemmaSeqNatBound(xs);
      LemmaPowIncreasesAuto();
      SeqExtend(xs, newLen)
    }

    function method {:opaque} {:fuel 0, 0} FromNatWithLen(n: nat, len: nat): (xs: seq<uint>)
      requires Pow(BASE(), len) > n
      ensures |xs| == len
      ensures ToNatRight(xs) == n
      decreases n, len
    {
      LemmaFromNatLen(n, len);
      LemmaNatSeqNat(n);
      SeqExtend(FromNat(n), len)
    }

    lemma /*{:_induction xs}*/ LemmaSeqZero(xs: seq<uint>)
      requires ToNatRight(xs) == 0
      ensures forall i: int :: 0 <= i < |xs| ==> xs[i] == 0
      decreases xs
    {
      reveal ToNatRight();
      if |xs| == 0 {
      } else {
        LemmaMulNonnegativeAuto();
        assert First(xs) == 0;
        LemmaMulNonzeroAuto();
        LemmaSeqZero(DropFirst(xs));
      }
    }

    function method {:opaque} {:fuel 0, 0} SeqZero(len: nat): (xs: seq<uint>)
      ensures |xs| == len
      ensures forall i: int :: 0 <= i < |xs| ==> xs[i] == 0
      ensures ToNatRight(xs) == 0
      decreases len
    {
      LemmaPowPositive(BASE(), len);
      var xs: seq<uint> := FromNatWithLen(0, len);
      LemmaSeqZero(xs);
      xs
    }

    lemma /*{:_induction xs}*/ LemmaSeqNatSeq(xs: seq<uint>)
      ensures Pow(BASE(), |xs|) > ToNatRight(xs)
      ensures FromNatWithLen(ToNatRight(xs), |xs|) == xs
      decreases xs
    {
      reveal FromNat();
      reveal ToNatRight();
      LemmaSeqNatBound(xs);
      if |xs| > 0 {
        calc {
          FromNatWithLen(ToNatRight(xs), |xs|) != xs;
          {
            LemmaSeqNeq(FromNatWithLen(ToNatRight(xs), |xs|), xs);
          }
          ToNatRight(FromNatWithLen(ToNatRight(xs), |xs|)) != ToNatRight(xs);
          ToNatRight(xs) != ToNatRight(xs);
          false;
        }
      }
    }

    function method {:opaque} {:fuel 0, 0} SeqAdd(xs: seq<uint>, ys: seq<uint>): (seq<uint>, nat)
      requires |xs| == |ys|
      ensures var (zs: seq<uint>, cout: nat) := SeqAdd(xs, ys); |zs| == |xs| && 0 <= cout <= 1
      decreases xs
    {
      if |xs| == 0 then
        ([], 0)
      else
        var (zs': seq<uint>, cin: nat) := SeqAdd(DropLast(xs), DropLast(ys)); var sum: int := Last(xs) + Last(ys) + cin; var (sum_out: int, cout: int) := if sum < BASE() then (sum, 0) else (sum - BASE(), 1); (zs' + [sum_out], cout)
    }

    lemma /*{:_induction xs, ys, zs}*/ LemmaSeqAdd(xs: seq<uint>, ys: seq<uint>, zs: seq<uint>, cout: nat)
      requires |xs| == |ys|
      requires SeqAdd(xs, ys) == (zs, cout)
      ensures ToNatRight(xs) + ToNatRight(ys) == ToNatRight(zs) + cout * Pow(BASE(), |xs|)
      decreases xs, ys, zs, cout
    {
      reveal SeqAdd();
      if |xs| == 0 {
        reveal ToNatRight();
      } else {
        ghost var pow := Pow(BASE(), |xs| - 1);
        var (zs', cin) := SeqAdd(DropLast(xs), DropLast(ys));
        ghost var sum: int := Last(xs) + Last(ys) + cin;
        ghost var z := if sum < BASE() then sum else sum - BASE();
        assert sum == z + cout * BASE();
        reveal ToNatLeft();
        LemmaToNatLeftEqToNatRightAuto();
        calc {
          ToNatRight(zs);
          ToNatLeft(zs);
          ToNatLeft(zs') + z * pow;
          {
            LemmaSeqAdd(DropLast(xs), DropLast(ys), zs', cin);
          }
          ToNatLeft(DropLast(xs)) + ToNatLeft(DropLast(ys)) - cin * pow + z * pow;
          {
            LemmaMulEqualityAuto();
            assert sum * pow == (z + cout * BASE()) * pow;
            LemmaMulIsDistributiveAuto();
          }
          ToNatLeft(xs) + ToNatLeft(ys) - cout * BASE() * pow;
          {
            LemmaMulIsAssociative(cout, BASE(), pow);
            reveal Pow();
          }
          ToNatLeft(xs) + ToNatLeft(ys) - cout * Pow(BASE(), |xs|);
          ToNatRight(xs) + ToNatRight(ys) - cout * Pow(BASE(), |xs|);
        }
      }
    }

    function method {:opaque} {:fuel 0, 0} SeqSub(xs: seq<uint>, ys: seq<uint>): (seq<uint>, nat)
      requires |xs| == |ys|
      ensures var (zs: seq<uint>, cout: nat) := SeqSub(xs, ys); |zs| == |xs| && 0 <= cout <= 1
      decreases xs
    {
      if |xs| == 0 then
        ([], 0)
      else
        var (zs: seq<uint>, cin: nat) := SeqSub(DropLast(xs), DropLast(ys)); var (diff_out: int, cout: int) := if Last(xs) >= Last(ys) + cin then (Last(xs) - Last(ys) - cin, 0) else (BASE() + Last(xs) - Last(ys) - cin, 1); (zs + [diff_out], cout)
    }

    lemma /*{:_induction xs, ys, zs}*/ LemmaSeqSub(xs: seq<uint>, ys: seq<uint>, zs: seq<uint>, cout: nat)
      requires |xs| == |ys|
      requires SeqSub(xs, ys) == (zs, cout)
      ensures ToNatRight(xs) - ToNatRight(ys) + cout * Pow(BASE(), |xs|) == ToNatRight(zs)
      decreases xs, ys, zs, cout
    {
      reveal SeqSub();
      if |xs| == 0 {
        reveal ToNatRight();
      } else {
        ghost var pow := Pow(BASE(), |xs| - 1);
        var (zs', cin) := SeqSub(DropLast(xs), DropLast(ys));
        ghost var z := if Last(xs) >= Last(ys) + cin then Last(xs) - Last(ys) - cin else BASE() + Last(xs) - Last(ys) - cin;
        assert cout * BASE() + Last(xs) - cin - Last(ys) == z;
        reveal ToNatLeft();
        LemmaToNatLeftEqToNatRightAuto();
        calc {
          ToNatRight(zs);
          ToNatLeft(zs);
          ToNatLeft(zs') + z * pow;
          {
            LemmaSeqSub(DropLast(xs), DropLast(ys), zs', cin);
          }
          ToNatLeft(DropLast(xs)) - ToNatLeft(DropLast(ys)) + cin * pow + z * pow;
          {
            LemmaMulEqualityAuto();
            assert pow * (cout * BASE() + Last(xs) - cin - Last(ys)) == pow * z;
            LemmaMulIsDistributiveAuto();
          }
          ToNatLeft(xs) - ToNatLeft(ys) + cout * BASE() * pow;
          {
            LemmaMulIsAssociative(cout, BASE(), pow);
            reveal Pow();
          }
          ToNatLeft(xs) - ToNatLeft(ys) + cout * Pow(BASE(), |xs|);
          ToNatRight(xs) - ToNatRight(ys) + cout * Pow(BASE(), |xs|);
        }
      }
    }

    import opened DivMod

    import opened Mul

    import opened Power

    import opened Seq

    type uint = i: int
      | 0 <= i < BASE()
  }

  import opened Large = Uint64Seq

  import Small = Large.Small
  function method E(): (E: nat)
    ensures Pow(Small.BASE(), E) == Large.BASE()
    ensures E > 0
  {
    LemmaDivBasicsAuto();
    LemmaPowMultipliesAuto();
    LemmaFundamentalDivMod(Large.BITS(), Small.BITS());
    Large.BITS() / Small.BITS()
  }

  function method {:opaque} {:fuel 0, 0} ToSmall(xs: seq<Large.uint>): (ys: seq<Small.uint>)
    ensures |ys| == |xs| * E()
    decreases xs
  {
    if |xs| == 0 then
      []
    else
      LemmaMulIsDistributiveAddOtherWay(E(), 1, |xs| - 1); Small.FromNatWithLen(First(xs), E()) + ToSmall(DropFirst(xs))
  }

  function method {:opaque} {:fuel 0, 0} ToLarge(xs: seq<Small.uint>): (ys: seq<Large.uint>)
    requires |xs| % E() == 0
    ensures |ys| == |xs| / E()
    decreases xs
  {
    if |xs| == 0 then
      LemmaDivBasicsAuto();
      []
    else
      LemmaModIsZero(|xs|, E()); assert |xs| >= E(); Small.LemmaSeqNatBound(xs[..E()]); LemmaModSubMultiplesVanishAuto(); LemmaDivMinusOne(|xs|, E()); [Small.ToNatRight(xs[..E()]) as Large.uint] + ToLarge(xs[E()..])
  }

  lemma /*{:_induction xs}*/ LemmaToSmall(xs: seq<Large.uint>)
    ensures Small.ToNatRight(ToSmall(xs)) == Large.ToNatRight(xs)
    decreases xs
  {
    reveal Small.ToNatRight();
    reveal Large.ToNatRight();
    reveal ToSmall();
    if |xs| == 0 {
    } else {
      calc {
        Small.ToNatRight(ToSmall(xs));
        Small.ToNatRight(Small.FromNatWithLen(First(xs), E()) + ToSmall(DropFirst(xs)));
        {
          Small.LemmaSeqPrefix(Small.FromNatWithLen(First(xs), E()) + ToSmall(DropFirst(xs)), E());
          LemmaToSmall(DropFirst(xs));
        }
        First(xs) + Large.ToNatRight(DropFirst(xs)) * Pow(Small.BASE(), E());
        {
          assert Pow(Small.BASE(), E()) == Large.BASE();
        }
        Large.ToNatRight(xs);
      }
    }
  }

  lemma /*{:_induction xs}*/ LemmaToLarge(xs: seq<Small.uint>)
    requires |xs| % E() == 0
    ensures Large.ToNatRight(ToLarge(xs)) == Small.ToNatRight(xs)
    decreases xs
  {
    reveal Large.ToNatRight();
    reveal Small.ToNatRight();
    reveal ToLarge();
    if |xs| == 0 {
    } else {
      calc {
        Large.ToNatRight(ToLarge(xs));
        {
          LemmaModIsZero(|xs|, E());
          LemmaModSubMultiplesVanishAuto();
          Small.LemmaSeqNatBound(xs[..E()]);
        }
        Large.ToNatRight([Small.ToNatRight(xs[..E()]) as Large.uint] + ToLarge(xs[E()..]));
        {
          LemmaToLarge(xs[E()..]);
        }
        Small.ToNatRight(xs[..E()]) + Small.ToNatRight(xs[E()..]) * Pow(Small.BASE(), E());
        {
          Small.LemmaSeqPrefix(xs, E());
        }
        Small.ToNatRight(xs);
      }
    }
  }

  lemma /*{:_induction xs, ys}*/ LemmaToSmallIsInjective(xs: seq<Large.uint>, ys: seq<Large.uint>)
    requires ToSmall(xs) == ToSmall(ys)
    requires |xs| == |ys|
    ensures xs == ys
    decreases xs, ys
  {
    LemmaToSmall(xs);
    LemmaToSmall(ys);
    assert Large.ToNatRight(xs) == Large.ToNatRight(ys);
    Large.LemmaSeqEq(xs, ys);
  }

  lemma /*{:_induction xs, ys}*/ LemmaToLargeIsInjective(xs: seq<Small.uint>, ys: seq<Small.uint>)
    requires |xs| % E() == |ys| % E() == 0
    requires ToLarge(xs) == ToLarge(ys)
    requires |xs| == |ys|
    ensures xs == ys
    decreases xs, ys
  {
    LemmaToLarge(xs);
    LemmaToLarge(ys);
    assert Small.ToNatRight(xs) == Small.ToNatRight(ys);
    Small.LemmaSeqEq(xs, ys);
  }

  lemma /*{:_induction xs}*/ LemmaSmallLargeSmall(xs: seq<Small.uint>)
    requires |xs| % E() == 0
    ensures ToSmall(ToLarge(xs)) == xs
    decreases xs
  {
    reveal ToSmall();
    reveal ToLarge();
    if |xs| == 0 {
    } else {
      calc {
        ToSmall(ToLarge(xs));
        {
          LemmaModIsZero(|xs|, E());
          Small.LemmaSeqNatBound(xs[..E()]);
          LemmaModSubMultiplesVanishAuto();
        }
        ToSmall([Small.ToNatRight(xs[..E()]) as Large.uint] + ToLarge(xs[E()..]));
        Small.FromNatWithLen(Small.ToNatRight(xs[..E()]), E()) + ToSmall(ToLarge(xs[E()..]));
        {
          Small.LemmaSeqNatSeq(xs[..E()]);
          LemmaSmallLargeSmall(xs[E()..]);
        }
        xs;
      }
    }
  }

  lemma /*{:_induction xs}*/ LemmaLargeSmallLarge(xs: seq<Large.uint>)
    ensures |ToSmall(xs)| % E() == 0
    ensures ToLarge(ToSmall(xs)) == xs
    decreases xs
  {
    reveal ToSmall();
    reveal ToLarge();
    LemmaModMultiplesBasicAuto();
    if |xs| == 0 {
    } else {
      calc {
        ToLarge(ToSmall(xs));
        ToLarge(Small.FromNatWithLen(First(xs), E()) + ToSmall(DropFirst(xs)));
        [Small.ToNatRight(Small.FromNatWithLen(First(xs), E())) as Large.uint] + ToLarge(ToSmall(DropFirst(xs)));
        [First(xs)] + ToLarge(ToSmall(DropFirst(xs)));
        {
          LemmaLargeSmallLarge(DropFirst(xs));
        }
        [First(xs)] + DropFirst(xs);
        xs;
      }
    }
  }

  import opened DivMod

  import opened Mul

  import opened Power

  import opened Seq
}

module srcCollectionsSequencesUint8_16dfyUnitTests {

  import Uint8_16

  import Uint8Seq = Uint8_16.Uint8Seq

  import Uint16Seq = Uint8_16.Uint16Seq

  import DivMod

  import DivInternalsNonlinear

  import DivInternals

  import GeneralInternals

  import ModInternals

  import MulInternals

  import MulInternalsNonlinear

  import Mul

  import ModInternalsNonlinear

  import Power

  import Seq

  import Wrappers

  import Math
  method {:test} test0()
  {
    var d0: seq<Uint8_16.Uint8Seq.uint> := [];
    var r0 := Uint8_16.Uint8Seq.ToNatRight(d0);
  }

  method {:test} test1()
  {
    var d0: seq<Uint8_16.Uint8Seq.uint> := [];
    var r0 := Uint8_16.Uint8Seq.ToNatLeft(d0);
  }

  method {:test} test2()
  {
    var r0 := Uint8_16.Uint8Seq.FromNat(65 as nat);
  }

  method {:test} test3()
  {
    var r0 := Uint8_16.Uint8Seq.FromNat(0 as nat);
  }

  method {:test} test4()
  {
    var d0: seq<Uint8_16.Uint8Seq.uint> := [0 as Uint8_16.Uint8Seq.uint];
    expect |d0| <= 1 as nat, ""Test does not meet preconditions and should be removed""
    var r0 := Uint8_16.Uint8Seq.SeqExtend(d0, 1 as nat);
    expect |r0| == 1 as nat, ""expectation violation""
    expect Uint8_16.Uint8Seq.ToNatRight(r0) == Uint8_16.Uint8Seq.ToNatRight(d0), ""expectation violation""
  }

  method {:test} test5()
  {
    var d0: seq<Uint8_16.Uint8Seq.uint> := [0 as Uint8_16.Uint8Seq.uint, 0 as Uint8_16.Uint8Seq.uint];
    var d1: seq<Uint8_16.Uint8Seq.uint> := [0 as Uint8_16.Uint8Seq.uint, 0 as Uint8_16.Uint8Seq.uint];
    expect |d0| == |d1|, ""Test does not meet preconditions and should be removed""
    var r0 := Uint8_16.Uint8Seq.SeqAdd(d0, d1);
  }

  method {:test} test6()
  {
    var d0: seq<Uint8_16.Uint8Seq.uint> := [12 as Uint8_16.Uint8Seq.uint, 2283 as Uint8_16.Uint8Seq.uint];
    var d1: seq<Uint8_16.Uint8Seq.uint> := [281 as Uint8_16.Uint8Seq.uint, 11138 as Uint8_16.Uint8Seq.uint];
    expect |d0| == |d1|, ""Test does not meet preconditions and should be removed""
    var r0 := Uint8_16.Uint8Seq.SeqAdd(d0, d1);
  }

  method {:test} test7()
  {
    var d0: seq<Uint8_16.Uint8Seq.uint> := [];
    var d1: seq<Uint8_16.Uint8Seq.uint> := [];
    expect |d0| == |d1|, ""Test does not meet preconditions and should be removed""
    var r0 := Uint8_16.Uint8Seq.SeqAdd(d0, d1);
  }

  method {:test} test8()
  {
    var d0: seq<Uint8_16.Uint8Seq.uint> := [1325 as Uint8_16.Uint8Seq.uint, 2331 as Uint8_16.Uint8Seq.uint];
    var d1: seq<Uint8_16.Uint8Seq.uint> := [234 as Uint8_16.Uint8Seq.uint, 1796 as Uint8_16.Uint8Seq.uint];
    expect |d0| == |d1|, ""Test does not meet preconditions and should be removed""
    var r0 := Uint8_16.Uint8Seq.SeqSub(d0, d1);
  }

  method {:test} test9()
  {
    var d0: seq<Uint8_16.Uint8Seq.uint> := [920 as Uint8_16.Uint8Seq.uint, 2061 as Uint8_16.Uint8Seq.uint];
    var d1: seq<Uint8_16.Uint8Seq.uint> := [645 as Uint8_16.Uint8Seq.uint, 2062 as Uint8_16.Uint8Seq.uint];
    expect |d0| == |d1|, ""Test does not meet preconditions and should be removed""
    var r0 := Uint8_16.Uint8Seq.SeqSub(d0, d1);
  }

  method {:test} test10()
  {
    var d0: seq<Uint8_16.Uint8Seq.uint> := [];
    var d1: seq<Uint8_16.Uint8Seq.uint> := [];
    expect |d0| == |d1|, ""Test does not meet preconditions and should be removed""
    var r0 := Uint8_16.Uint8Seq.SeqSub(d0, d1);
  }

  method {:test} test11()
  {
    var d0: seq<Uint8_16.Uint16Seq.uint> := [];
    var r0 := Uint8_16.Uint16Seq.ToNatRight(d0);
  }

  method {:test} test12()
  {
    var d0: seq<Uint8_16.Uint16Seq.uint> := [];
    var r0 := Uint8_16.Uint16Seq.ToNatLeft(d0);
  }

  method {:test} test13()
  {
    var r0 := Uint8_16.Uint16Seq.FromNat(65 as nat);
  }

  method {:test} test14()
  {
    var r0 := Uint8_16.Uint16Seq.FromNat(0 as nat);
  }

  method {:test} test15()
  {
    var d0: seq<Uint8_16.Uint16Seq.uint> := [0 as Uint8_16.Uint16Seq.uint];
    expect |d0| <= 1 as nat, ""Test does not meet preconditions and should be removed""
    var r0 := Uint8_16.Uint16Seq.SeqExtend(d0, 1 as nat);
    expect |r0| == 1 as nat, ""expectation violation""
    expect Uint8_16.Uint16Seq.ToNatRight(r0) == Uint8_16.Uint16Seq.ToNatRight(d0), ""expectation violation""
  }

  method {:test} test16()
  {
    var d0: seq<Uint8_16.Uint16Seq.uint> := [0 as Uint8_16.Uint16Seq.uint, 0 as Uint8_16.Uint16Seq.uint];
    var d1: seq<Uint8_16.Uint16Seq.uint> := [0 as Uint8_16.Uint16Seq.uint, 0 as Uint8_16.Uint16Seq.uint];
    expect |d0| == |d1|, ""Test does not meet preconditions and should be removed""
    var r0 := Uint8_16.Uint16Seq.SeqAdd(d0, d1);
  }

  method {:test} test17()
  {
    var d0: seq<Uint8_16.Uint16Seq.uint> := [342 as Uint8_16.Uint16Seq.uint, 4720 as Uint8_16.Uint16Seq.uint];
    var d1: seq<Uint8_16.Uint16Seq.uint> := [281 as Uint8_16.Uint16Seq.uint, 2283 as Uint8_16.Uint16Seq.uint];
    expect |d0| == |d1|, ""Test does not meet preconditions and should be removed""
    var r0 := Uint8_16.Uint16Seq.SeqAdd(d0, d1);
  }

  method {:test} test18()
  {
    var d0: seq<Uint8_16.Uint16Seq.uint> := [];
    var d1: seq<Uint8_16.Uint16Seq.uint> := [];
    expect |d0| == |d1|, ""Test does not meet preconditions and should be removed""
    var r0 := Uint8_16.Uint16Seq.SeqAdd(d0, d1);
  }

  method {:test} test19()
  {
    var d0: seq<Uint8_16.Uint16Seq.uint> := [1325 as Uint8_16.Uint16Seq.uint, 2331 as Uint8_16.Uint16Seq.uint];
    var d1: seq<Uint8_16.Uint16Seq.uint> := [234 as Uint8_16.Uint16Seq.uint, 1796 as Uint8_16.Uint16Seq.uint];
    expect |d0| == |d1|, ""Test does not meet preconditions and should be removed""
    var r0 := Uint8_16.Uint16Seq.SeqSub(d0, d1);
  }

  method {:test} test20()
  {
    var d0: seq<Uint8_16.Uint16Seq.uint> := [920 as Uint8_16.Uint16Seq.uint, 2061 as Uint8_16.Uint16Seq.uint];
    var d1: seq<Uint8_16.Uint16Seq.uint> := [645 as Uint8_16.Uint16Seq.uint, 2062 as Uint8_16.Uint16Seq.uint];
    expect |d0| == |d1|, ""Test does not meet preconditions and should be removed""
    var r0 := Uint8_16.Uint16Seq.SeqSub(d0, d1);
  }

  method {:test} test21()
  {
    var d0: seq<Uint8_16.Uint16Seq.uint> := [];
    var d1: seq<Uint8_16.Uint16Seq.uint> := [];
    expect |d0| == |d1|, ""Test does not meet preconditions and should be removed""
    var r0 := Uint8_16.Uint16Seq.SeqSub(d0, d1);
  }

  method {:test} test22()
  {
    var d0: seq<Uint8_16.Uint16Seq.uint> := [];
    var r0 := Uint8_16.ToSmall(d0);
    expect |r0| == |d0| * Uint8_16.E(), ""expectation violation""
  }

  method {:test} test23()
  {
    var d0: seq<Uint8_16.Uint8Seq.uint> := [0 as Uint8_16.Uint8Seq.uint, 0 as Uint8_16.Uint8Seq.uint, 0 as Uint8_16.Uint8Seq.uint, 0 as Uint8_16.Uint8Seq.uint, 0 as Uint8_16.Uint8Seq.uint, 0 as Uint8_16.Uint8Seq.uint, 0 as Uint8_16.Uint8Seq.uint, 0 as Uint8_16.Uint8Seq.uint, 0 as Uint8_16.Uint8Seq.uint, 0 as Uint8_16.Uint8Seq.uint, 0 as Uint8_16.Uint8Seq.uint, 0 as Uint8_16.Uint8Seq.uint, 0 as Uint8_16.Uint8Seq.uint, 0 as Uint8_16.Uint8Seq.uint, 0 as Uint8_16.Uint8Seq.uint, 0 as Uint8_16.Uint8Seq.uint, 0 as Uint8_16.Uint8Seq.uint, 0 as Uint8_16.Uint8Seq.uint, 0 as Uint8_16.Uint8Seq.uint, 0 as Uint8_16.Uint8Seq.uint, 0 as Uint8_16.Uint8Seq.uint, 0 as Uint8_16.Uint8Seq.uint, 0 as Uint8_16.Uint8Seq.uint, 0 as Uint8_16.Uint8Seq.uint, 0 as Uint8_16.Uint8Seq.uint, 0 as Uint8_16.Uint8Seq.uint, 0 as Uint8_16.Uint8Seq.uint, 0 as Uint8_16.Uint8Seq.uint, 0 as Uint8_16.Uint8Seq.uint, 0 as Uint8_16.Uint8Seq.uint, 0 as Uint8_16.Uint8Seq.uint, 0 as Uint8_16.Uint8Seq.uint, 0 as Uint8_16.Uint8Seq.uint, 0 as Uint8_16.Uint8Seq.uint, 0 as Uint8_16.Uint8Seq.uint, 0 as Uint8_16.Uint8Seq.uint, 0 as Uint8_16.Uint8Seq.uint, 0 as Uint8_16.Uint8Seq.uint, 0 as Uint8_16.Uint8Seq.uint, 0 as Uint8_16.Uint8Seq.uint, 0 as Uint8_16.Uint8Seq.uint, 0 as Uint8_16.Uint8Seq.uint, 0 as Uint8_16.Uint8Seq.uint, 0 as Uint8_16.Uint8Seq.uint, 0 as Uint8_16.Uint8Seq.uint, 0 as Uint8_16.Uint8Seq.uint, 0 as Uint8_16.Uint8Seq.uint, 0 as Uint8_16.Uint8Seq.uint, 0 as Uint8_16.Uint8Seq.uint, 0 as Uint8_16.Uint8Seq.uint, 0 as Uint8_16.Uint8Seq.uint, 0 as Uint8_16.Uint8Seq.uint, 0 as Uint8_16.Uint8Seq.uint, 0 as Uint8_16.Uint8Seq.uint, 0 as Uint8_16.Uint8Seq.uint, 0 as Uint8_16.Uint8Seq.uint, 0 as Uint8_16.Uint8Seq.uint, 0 as Uint8_16.Uint8Seq.uint, 0 as Uint8_16.Uint8Seq.uint, 0 as Uint8_16.Uint8Seq.uint, 0 as Uint8_16.Uint8Seq.uint, 0 as Uint8_16.Uint8Seq.uint, 0 as Uint8_16.Uint8Seq.uint, 0 as Uint8_16.Uint8Seq.uint, 0 as Uint8_16.Uint8Seq.uint, 0 as Uint8_16.Uint8Seq.uint, 0 as Uint8_16.Uint8Seq.uint, 0 as Uint8_16.Uint8Seq.uint, 0 as Uint8_16.Uint8Seq.uint, 0 as Uint8_16.Uint8Seq.uint, 0 as Uint8_16.Uint8Seq.uint, 0 as Uint8_16.Uint8Seq.uint, 0 as Uint8_16.Uint8Seq.uint, 0 as Uint8_16.Uint8Seq.uint, 0 as Uint8_16.Uint8Seq.uint, 0 as Uint8_16.Uint8Seq.uint, 0 as Uint8_16.Uint8Seq.uint, 0 as Uint8_16.Uint8Seq.uint, 0 as Uint8_16.Uint8Seq.uint, 0 as Uint8_16.Uint8Seq.uint, 0 as Uint8_16.Uint8Seq.uint, 0 as Uint8_16.Uint8Seq.uint, 0 as Uint8_16.Uint8Seq.uint, 0 as Uint8_16.Uint8Seq.uint, 0 as Uint8_16.Uint8Seq.uint, 0 as Uint8_16.Uint8Seq.uint];
    expect |d0| % Uint8_16.E() == 0, ""Test does not meet preconditions and should be removed""
    var r0 := Uint8_16.ToLarge(d0);
    expect |r0| == |d0| / Uint8_16.E(), ""expectation violation""
  }
}

module Uint8_16 refines LittleEndianNatConversions {

  module {:extern ""Uint8__16_mUint8Seq_Compile""} Uint8Seq refines SmallSeq {
    function method BITS(): nat
      ensures BITS() > 1
    {
      8
    }

    function method BASE(): nat
      ensures BASE() > 1
    {
      LemmaPowPositive(2, BITS() - 1);
      LemmaPowStrictlyIncreases(2, BITS() - 1, BITS());
      Pow(2, BITS())
    }

    function method {:opaque} {:fuel 0, 0} ToNatRight(xs: seq<uint>): nat
      decreases xs
    {
      if |xs| == 0 then
        0
      else
        LemmaMulNonnegativeAuto(); ToNatRight(DropFirst(xs)) * BASE() + First(xs)
    }

    function method {:opaque} {:fuel 0, 0} ToNatLeft(xs: seq<uint>): nat
      decreases xs
    {
      if |xs| == 0 then
        0
      else
        LemmaPowPositiveAuto(); LemmaMulNonnegativeAuto(); ToNatLeft(DropLast(xs)) + Last(xs) * Pow(BASE(), |xs| - 1)
    }

    lemma {:vcs_split_on_every_assert} /*{:_induction xs}*/ LemmaToNatLeftEqToNatRight(xs: seq<uint>)
      ensures ToNatRight(xs) == ToNatLeft(xs)
      decreases xs
    {
      reveal ToNatRight();
      reveal ToNatLeft();
      if xs == [] {
      } else {
        if DropLast(xs) == [] {
          calc {
            ToNatLeft(xs);
            Last(xs) * Pow(BASE(), |xs| - 1);
            {
              reveal Pow();
            }
            Last(xs);
            First(xs);
            {
              assert ToNatRight(DropFirst(xs)) == 0;
            }
            ToNatRight(xs);
          }
        } else {
          calc {
            ToNatLeft(xs);
            ToNatLeft(DropLast(xs)) + Last(xs) * Pow(BASE(), |xs| - 1);
            {
              LemmaToNatLeftEqToNatRight(DropLast(xs));
            }
            ToNatRight(DropLast(xs)) + Last(xs) * Pow(BASE(), |xs| - 1);
            ToNatRight(DropFirst(DropLast(xs))) * BASE() + First(xs) + Last(xs) * Pow(BASE(), |xs| - 1);
            {
              LemmaToNatLeftEqToNatRight(DropFirst(DropLast(xs)));
            }
            ToNatLeft(DropFirst(DropLast(xs))) * BASE() + First(xs) + Last(xs) * Pow(BASE(), |xs| - 1);
            {
              assert DropFirst(DropLast(xs)) == DropLast(DropFirst(xs));
              reveal Pow();
              LemmaMulProperties();
            }
            ToNatLeft(DropLast(DropFirst(xs))) * BASE() + First(xs) + Last(xs) * Pow(BASE(), |xs| - 2) * BASE();
            {
              LemmaMulIsDistributiveAddOtherWayAuto();
            }
            ToNatLeft(DropFirst(xs)) * BASE() + First(xs);
            {
              LemmaToNatLeftEqToNatRight(DropFirst(xs));
            }
            ToNatRight(xs);
          }
        }
      }
    }

    lemma LemmaToNatLeftEqToNatRightAuto()
      ensures forall xs: seq<uint> :: ToNatRight(xs) == ToNatLeft(xs)
    {
      reveal ToNatRight();
      reveal ToNatLeft();
      forall xs: seq<uint> | true
        ensures ToNatRight(xs) == ToNatLeft(xs)
      {
        LemmaToNatLeftEqToNatRight(xs);
      }
    }

    lemma /*{:_induction xs}*/ LemmaSeqLen1(xs: seq<uint>)
      requires |xs| == 1
      ensures ToNatRight(xs) == First(xs)
      decreases xs
    {
      reveal ToNatRight();
    }

    lemma /*{:_induction xs}*/ LemmaSeqLen2(xs: seq<uint>)
      requires |xs| == 2
      ensures ToNatRight(xs) == First(xs) + xs[1] * BASE()
      decreases xs
    {
      reveal ToNatRight();
      LemmaSeqLen1(DropLast(xs));
    }

    lemma /*{:_induction xs}*/ LemmaSeqAppendZero(xs: seq<uint>)
      ensures ToNatRight(xs + [0]) == ToNatRight(xs)
      decreases xs
    {
      reveal ToNatLeft();
      LemmaToNatLeftEqToNatRightAuto();
      calc {
        ToNatRight(xs + [0]);
        ToNatLeft(xs + [0]);
        ToNatLeft(xs) + 0 * Pow(BASE(), |xs|);
        {
          LemmaMulBasicsAuto();
        }
        ToNatLeft(xs);
        ToNatRight(xs);
      }
    }

    lemma /*{:_induction xs}*/ LemmaSeqNatBound(xs: seq<uint>)
      ensures ToNatRight(xs) < Pow(BASE(), |xs|)
      decreases xs
    {
      reveal Pow();
      if |xs| == 0 {
        reveal ToNatRight();
      } else {
        ghost var len' := |xs| - 1;
        ghost var pow := Pow(BASE(), len');
        calc {
          ToNatRight(xs);
          {
            LemmaToNatLeftEqToNatRight(xs);
          }
          ToNatLeft(xs);
          {
            reveal ToNatLeft();
          }
          ToNatLeft(DropLast(xs)) + Last(xs) * pow;
        <
          {
            LemmaToNatLeftEqToNatRight(DropLast(xs));
            LemmaSeqNatBound(DropLast(xs));
          }
          pow + Last(xs) * pow;
        <=
          {
            LemmaPowPositiveAuto();
            LemmaMulInequalityAuto();
          }
          pow + (BASE() - 1) * pow;
          {
            LemmaMulIsDistributiveAuto();
          }
          Pow(BASE(), len' + 1);
        }
      }
    }

    lemma /*{:_induction xs, i}*/ LemmaSeqPrefix(xs: seq<uint>, i: nat)
      requires 0 <= i <= |xs|
      ensures ToNatRight(xs[..i]) + ToNatRight(xs[i..]) * Pow(BASE(), i) == ToNatRight(xs)
      decreases xs, i
    {
      reveal ToNatRight();
      reveal Pow();
      if i == 1 {
        assert ToNatRight(xs[..1]) == First(xs);
      } else if i > 1 {
        calc {
          ToNatRight(xs[..i]) + ToNatRight(xs[i..]) * Pow(BASE(), i);
          ToNatRight(DropFirst(xs[..i])) * BASE() + First(xs) + ToNatRight(xs[i..]) * Pow(BASE(), i);
          {
            assert DropFirst(xs[..i]) == DropFirst(xs)[..i - 1];
            LemmaMulProperties();
          }
          ToNatRight(DropFirst(xs)[..i - 1]) * BASE() + First(xs) + ToNatRight(xs[i..]) * Pow(BASE(), i - 1) * BASE();
          {
            LemmaMulIsDistributiveAddOtherWayAuto();
          }
          (ToNatRight(DropFirst(xs)[..i - 1]) + ToNatRight(DropFirst(xs)[i - 1..]) * Pow(BASE(), i - 1)) * BASE() + First(xs);
          {
            LemmaSeqPrefix(DropFirst(xs), i - 1);
          }
          ToNatRight(xs);
        }
      }
    }

    lemma /*{:_induction xs, ys}*/ LemmaSeqMswInequality(xs: seq<uint>, ys: seq<uint>)
      requires |xs| == |ys| > 0
      requires Last(xs) < Last(ys)
      ensures ToNatRight(xs) < ToNatRight(ys)
      decreases xs, ys
    {
      reveal ToNatLeft();
      LemmaToNatLeftEqToNatRightAuto();
      ghost var len' := |xs| - 1;
      calc {
        ToNatRight(xs);
        ToNatLeft(xs);
      <
        {
          LemmaSeqNatBound(DropLast(xs));
        }
        Pow(BASE(), len') + Last(xs) * Pow(BASE(), len');
      ==
        {
          LemmaMulIsDistributiveAuto();
        }
        (1 + Last(xs)) * Pow(BASE(), len');
      <=
        {
          LemmaPowPositiveAuto();
          LemmaMulInequalityAuto();
        }
        ToNatLeft(ys);
        ToNatRight(ys);
      }
    }

    lemma /*{:_induction xs, ys}*/ LemmaSeqPrefixNeq(xs: seq<uint>, ys: seq<uint>, i: nat)
      requires 0 <= i <= |xs| == |ys|
      requires ToNatRight(xs[..i]) != ToNatRight(ys[..i])
      ensures ToNatRight(xs) != ToNatRight(ys)
      decreases |xs| - i
    {
      if i == |xs| {
        assert xs[..i] == xs;
        assert ys[..i] == ys;
      } else {
        if xs[i] == ys[i] {
          reveal ToNatLeft();
          assert DropLast(xs[..i + 1]) == xs[..i];
          assert DropLast(ys[..i + 1]) == ys[..i];
          LemmaToNatLeftEqToNatRightAuto();
          assert ToNatRight(xs[..i + 1]) == ToNatLeft(xs[..i + 1]);
        } else if xs[i] < ys[i] {
          LemmaSeqMswInequality(xs[..i + 1], ys[..i + 1]);
        } else {
          LemmaSeqMswInequality(ys[..i + 1], xs[..i + 1]);
        }
        LemmaSeqPrefixNeq(xs, ys, i + 1);
      }
    }

    lemma /*{:_induction xs, ys}*/ LemmaSeqNeq(xs: seq<uint>, ys: seq<uint>)
      requires |xs| == |ys|
      requires xs != ys
      ensures ToNatRight(xs) != ToNatRight(ys)
      decreases xs, ys
    {
      ghost var i: nat, n: nat := 0, |xs|;
      while i < n
        invariant 0 <= i < n
        invariant xs[..i] == ys[..i]
        decreases n - i
      {
        if xs[i] != ys[i] {
          break;
        }
        i := i + 1;
      }
      assert ToNatLeft(xs[..i]) == ToNatLeft(ys[..i]);
      reveal ToNatLeft();
      assert xs[..i + 1][..i] == xs[..i];
      assert ys[..i + 1][..i] == ys[..i];
      LemmaPowPositiveAuto();
      LemmaMulStrictInequalityAuto();
      assert ToNatLeft(xs[..i + 1]) != ToNatLeft(ys[..i + 1]);
      LemmaToNatLeftEqToNatRightAuto();
      LemmaSeqPrefixNeq(xs, ys, i + 1);
    }

    lemma /*{:_induction xs, ys}*/ LemmaSeqEq(xs: seq<uint>, ys: seq<uint>)
      requires |xs| == |ys|
      requires ToNatRight(xs) == ToNatRight(ys)
      ensures xs == ys
      decreases xs, ys
    {
      calc ==> {
        xs != ys;
        {
          LemmaSeqNeq(xs, ys);
        }
        ToNatRight(xs) != ToNatRight(ys);
        false;
      }
    }

    lemma /*{:_induction xs}*/ LemmaSeqLswModEquivalence(xs: seq<uint>)
      requires |xs| >= 1
      ensures IsModEquivalent(ToNatRight(xs), First(xs), BASE())
      decreases xs
    {
      if |xs| == 1 {
        LemmaSeqLen1(xs);
        LemmaModEquivalenceAuto();
      } else {
        assert IsModEquivalent(ToNatRight(xs), First(xs), BASE()) by {
          reveal ToNatRight();
          calc ==> {
            true;
            {
              LemmaModEquivalenceAuto();
            }
            IsModEquivalent(ToNatRight(xs), ToNatRight(DropFirst(xs)) * BASE() + First(xs), BASE());
            {
              LemmaModMultiplesBasicAuto();
            }
            IsModEquivalent(ToNatRight(xs), First(xs), BASE());
          }
        }
      }
    }

    function method {:opaque} {:fuel 0, 0} FromNat(n: nat): (xs: seq<uint>)
      decreases n
    {
      if n == 0 then
        []
      else
        LemmaDivBasicsAuto(); LemmaDivDecreasesAuto(); [n % BASE()] + FromNat(n / BASE())
    }

    lemma /*{:_induction n, len}*/ LemmaFromNatLen(n: nat, len: nat)
      requires Pow(BASE(), len) > n
      ensures |FromNat(n)| <= len
      decreases n, len
    {
      reveal FromNat();
      if n == 0 {
      } else {
        calc {
          |FromNat(n)|;
        ==
          {
            LemmaDivBasicsAuto();
          }
          1 + |FromNat(n / BASE())|;
        <=
          {
            LemmaMultiplyDivideLtAuto();
            LemmaDivDecreasesAuto();
            reveal Pow();
            LemmaFromNatLen(n / BASE(), len - 1);
          }
          len;
        }
      }
    }

    lemma /*{:_induction n}*/ LemmaNatSeqNat(n: nat)
      ensures ToNatRight(FromNat(n)) == n
      decreases n
    {
      reveal ToNatRight();
      reveal FromNat();
      if n == 0 {
      } else {
        calc {
          ToNatRight(FromNat(n));
          {
            LemmaDivBasicsAuto();
          }
          ToNatRight([n % BASE()] + FromNat(n / BASE()));
          n % BASE() + ToNatRight(FromNat(n / BASE())) * BASE();
          {
            LemmaDivDecreasesAuto();
            LemmaNatSeqNat(n / BASE());
          }
          n % BASE() + n / BASE() * BASE();
          {
            LemmaFundamentalDivMod(n, BASE());
          }
          n;
        }
      }
    }

    function method {:opaque} {:fuel 0, 0} SeqExtend(xs: seq<uint>, n: nat): (ys: seq<uint>)
      requires |xs| <= n
      ensures |ys| == n
      ensures ToNatRight(ys) == ToNatRight(xs)
      decreases n - |xs|
    {
      if |xs| >= n then
        xs
      else
        LemmaSeqAppendZero(xs); SeqExtend(xs + [0], n)
    }

    function method {:opaque} {:fuel 0, 0} SeqExtendMultiple(xs: seq<uint>, n: nat): (ys: seq<uint>)
      requires n > 0
      ensures |ys| % n == 0
      ensures ToNatRight(ys) == ToNatRight(xs)
      decreases xs, n
    {
      var newLen: int := |xs| + n - |xs| % n;
      LemmaSubModNoopRight(|xs| + n, |xs|, n);
      LemmaModBasicsAuto();
      assert newLen % n == 0;
      LemmaSeqNatBound(xs);
      LemmaPowIncreasesAuto();
      SeqExtend(xs, newLen)
    }

    function method {:opaque} {:fuel 0, 0} FromNatWithLen(n: nat, len: nat): (xs: seq<uint>)
      requires Pow(BASE(), len) > n
      ensures |xs| == len
      ensures ToNatRight(xs) == n
      decreases n, len
    {
      LemmaFromNatLen(n, len);
      LemmaNatSeqNat(n);
      SeqExtend(FromNat(n), len)
    }

    lemma /*{:_induction xs}*/ LemmaSeqZero(xs: seq<uint>)
      requires ToNatRight(xs) == 0
      ensures forall i: int :: 0 <= i < |xs| ==> xs[i] == 0
      decreases xs
    {
      reveal ToNatRight();
      if |xs| == 0 {
      } else {
        LemmaMulNonnegativeAuto();
        assert First(xs) == 0;
        LemmaMulNonzeroAuto();
        LemmaSeqZero(DropFirst(xs));
      }
    }

    function method {:opaque} {:fuel 0, 0} SeqZero(len: nat): (xs: seq<uint>)
      ensures |xs| == len
      ensures forall i: int :: 0 <= i < |xs| ==> xs[i] == 0
      ensures ToNatRight(xs) == 0
      decreases len
    {
      LemmaPowPositive(BASE(), len);
      var xs: seq<uint> := FromNatWithLen(0, len);
      LemmaSeqZero(xs);
      xs
    }

    lemma /*{:_induction xs}*/ LemmaSeqNatSeq(xs: seq<uint>)
      ensures Pow(BASE(), |xs|) > ToNatRight(xs)
      ensures FromNatWithLen(ToNatRight(xs), |xs|) == xs
      decreases xs
    {
      reveal FromNat();
      reveal ToNatRight();
      LemmaSeqNatBound(xs);
      if |xs| > 0 {
        calc {
          FromNatWithLen(ToNatRight(xs), |xs|) != xs;
          {
            LemmaSeqNeq(FromNatWithLen(ToNatRight(xs), |xs|), xs);
          }
          ToNatRight(FromNatWithLen(ToNatRight(xs), |xs|)) != ToNatRight(xs);
          ToNatRight(xs) != ToNatRight(xs);
          false;
        }
      }
    }

    function method {:opaque} {:fuel 0, 0} SeqAdd(xs: seq<uint>, ys: seq<uint>): (seq<uint>, nat)
      requires |xs| == |ys|
      ensures var (zs: seq<uint>, cout: nat) := SeqAdd(xs, ys); |zs| == |xs| && 0 <= cout <= 1
      decreases xs
    {
      if |xs| == 0 then
        ([], 0)
      else
        var (zs': seq<uint>, cin: nat) := SeqAdd(DropLast(xs), DropLast(ys)); var sum: int := Last(xs) + Last(ys) + cin; var (sum_out: int, cout: int) := if sum < BASE() then (sum, 0) else (sum - BASE(), 1); (zs' + [sum_out], cout)
    }

    lemma /*{:_induction xs, ys, zs}*/ LemmaSeqAdd(xs: seq<uint>, ys: seq<uint>, zs: seq<uint>, cout: nat)
      requires |xs| == |ys|
      requires SeqAdd(xs, ys) == (zs, cout)
      ensures ToNatRight(xs) + ToNatRight(ys) == ToNatRight(zs) + cout * Pow(BASE(), |xs|)
      decreases xs, ys, zs, cout
    {
      reveal SeqAdd();
      if |xs| == 0 {
        reveal ToNatRight();
      } else {
        ghost var pow := Pow(BASE(), |xs| - 1);
        var (zs', cin) := SeqAdd(DropLast(xs), DropLast(ys));
        ghost var sum: int := Last(xs) + Last(ys) + cin;
        ghost var z := if sum < BASE() then sum else sum - BASE();
        assert sum == z + cout * BASE();
        reveal ToNatLeft();
        LemmaToNatLeftEqToNatRightAuto();
        calc {
          ToNatRight(zs);
          ToNatLeft(zs);
          ToNatLeft(zs') + z * pow;
          {
            LemmaSeqAdd(DropLast(xs), DropLast(ys), zs', cin);
          }
          ToNatLeft(DropLast(xs)) + ToNatLeft(DropLast(ys)) - cin * pow + z * pow;
          {
            LemmaMulEqualityAuto();
            assert sum * pow == (z + cout * BASE()) * pow;
            LemmaMulIsDistributiveAuto();
          }
          ToNatLeft(xs) + ToNatLeft(ys) - cout * BASE() * pow;
          {
            LemmaMulIsAssociative(cout, BASE(), pow);
            reveal Pow();
          }
          ToNatLeft(xs) + ToNatLeft(ys) - cout * Pow(BASE(), |xs|);
          ToNatRight(xs) + ToNatRight(ys) - cout * Pow(BASE(), |xs|);
        }
      }
    }

    function method {:opaque} {:fuel 0, 0} SeqSub(xs: seq<uint>, ys: seq<uint>): (seq<uint>, nat)
      requires |xs| == |ys|
      ensures var (zs: seq<uint>, cout: nat) := SeqSub(xs, ys); |zs| == |xs| && 0 <= cout <= 1
      decreases xs
    {
      if |xs| == 0 then
        ([], 0)
      else
        var (zs: seq<uint>, cin: nat) := SeqSub(DropLast(xs), DropLast(ys)); var (diff_out: int, cout: int) := if Last(xs) >= Last(ys) + cin then (Last(xs) - Last(ys) - cin, 0) else (BASE() + Last(xs) - Last(ys) - cin, 1); (zs + [diff_out], cout)
    }

    lemma /*{:_induction xs, ys, zs}*/ LemmaSeqSub(xs: seq<uint>, ys: seq<uint>, zs: seq<uint>, cout: nat)
      requires |xs| == |ys|
      requires SeqSub(xs, ys) == (zs, cout)
      ensures ToNatRight(xs) - ToNatRight(ys) + cout * Pow(BASE(), |xs|) == ToNatRight(zs)
      decreases xs, ys, zs, cout
    {
      reveal SeqSub();
      if |xs| == 0 {
        reveal ToNatRight();
      } else {
        ghost var pow := Pow(BASE(), |xs| - 1);
        var (zs', cin) := SeqSub(DropLast(xs), DropLast(ys));
        ghost var z := if Last(xs) >= Last(ys) + cin then Last(xs) - Last(ys) - cin else BASE() + Last(xs) - Last(ys) - cin;
        assert cout * BASE() + Last(xs) - cin - Last(ys) == z;
        reveal ToNatLeft();
        LemmaToNatLeftEqToNatRightAuto();
        calc {
          ToNatRight(zs);
          ToNatLeft(zs);
          ToNatLeft(zs') + z * pow;
          {
            LemmaSeqSub(DropLast(xs), DropLast(ys), zs', cin);
          }
          ToNatLeft(DropLast(xs)) - ToNatLeft(DropLast(ys)) + cin * pow + z * pow;
          {
            LemmaMulEqualityAuto();
            assert pow * (cout * BASE() + Last(xs) - cin - Last(ys)) == pow * z;
            LemmaMulIsDistributiveAuto();
          }
          ToNatLeft(xs) - ToNatLeft(ys) + cout * BASE() * pow;
          {
            LemmaMulIsAssociative(cout, BASE(), pow);
            reveal Pow();
          }
          ToNatLeft(xs) - ToNatLeft(ys) + cout * Pow(BASE(), |xs|);
          ToNatRight(xs) - ToNatRight(ys) + cout * Pow(BASE(), |xs|);
        }
      }
    }

    import opened DivMod

    import opened Mul

    import opened Power

    import opened Seq

    type uint = i: int
      | 0 <= i < BASE()
  }

  module {:extern ""Uint8__16_mUint16Seq_Compile""} Uint16Seq refines LargeSeq {

    import Small = Uint8Seq
    function method BITS(): nat
      ensures BITS() > Small.BITS() && BITS() % Small.BITS() == 0
    {
      16
    }

    function method BASE(): nat
      ensures BASE() > 1
    {
      LemmaPowPositive(2, BITS() - 1);
      LemmaPowStrictlyIncreases(2, BITS() - 1, BITS());
      Pow(2, BITS())
    }

    function method {:opaque} {:fuel 0, 0} ToNatRight(xs: seq<uint>): nat
      decreases xs
    {
      if |xs| == 0 then
        0
      else
        LemmaMulNonnegativeAuto(); ToNatRight(DropFirst(xs)) * BASE() + First(xs)
    }

    function method {:opaque} {:fuel 0, 0} ToNatLeft(xs: seq<uint>): nat
      decreases xs
    {
      if |xs| == 0 then
        0
      else
        LemmaPowPositiveAuto(); LemmaMulNonnegativeAuto(); ToNatLeft(DropLast(xs)) + Last(xs) * Pow(BASE(), |xs| - 1)
    }

    lemma {:vcs_split_on_every_assert} /*{:_induction xs}*/ LemmaToNatLeftEqToNatRight(xs: seq<uint>)
      ensures ToNatRight(xs) == ToNatLeft(xs)
      decreases xs
    {
      reveal ToNatRight();
      reveal ToNatLeft();
      if xs == [] {
      } else {
        if DropLast(xs) == [] {
          calc {
            ToNatLeft(xs);
            Last(xs) * Pow(BASE(), |xs| - 1);
            {
              reveal Pow();
            }
            Last(xs);
            First(xs);
            {
              assert ToNatRight(DropFirst(xs)) == 0;
            }
            ToNatRight(xs);
          }
        } else {
          calc {
            ToNatLeft(xs);
            ToNatLeft(DropLast(xs)) + Last(xs) * Pow(BASE(), |xs| - 1);
            {
              LemmaToNatLeftEqToNatRight(DropLast(xs));
            }
            ToNatRight(DropLast(xs)) + Last(xs) * Pow(BASE(), |xs| - 1);
            ToNatRight(DropFirst(DropLast(xs))) * BASE() + First(xs) + Last(xs) * Pow(BASE(), |xs| - 1);
            {
              LemmaToNatLeftEqToNatRight(DropFirst(DropLast(xs)));
            }
            ToNatLeft(DropFirst(DropLast(xs))) * BASE() + First(xs) + Last(xs) * Pow(BASE(), |xs| - 1);
            {
              assert DropFirst(DropLast(xs)) == DropLast(DropFirst(xs));
              reveal Pow();
              LemmaMulProperties();
            }
            ToNatLeft(DropLast(DropFirst(xs))) * BASE() + First(xs) + Last(xs) * Pow(BASE(), |xs| - 2) * BASE();
            {
              LemmaMulIsDistributiveAddOtherWayAuto();
            }
            ToNatLeft(DropFirst(xs)) * BASE() + First(xs);
            {
              LemmaToNatLeftEqToNatRight(DropFirst(xs));
            }
            ToNatRight(xs);
          }
        }
      }
    }

    lemma LemmaToNatLeftEqToNatRightAuto()
      ensures forall xs: seq<uint> :: ToNatRight(xs) == ToNatLeft(xs)
    {
      reveal ToNatRight();
      reveal ToNatLeft();
      forall xs: seq<uint> | true
        ensures ToNatRight(xs) == ToNatLeft(xs)
      {
        LemmaToNatLeftEqToNatRight(xs);
      }
    }

    lemma /*{:_induction xs}*/ LemmaSeqLen1(xs: seq<uint>)
      requires |xs| == 1
      ensures ToNatRight(xs) == First(xs)
      decreases xs
    {
      reveal ToNatRight();
    }

    lemma /*{:_induction xs}*/ LemmaSeqLen2(xs: seq<uint>)
      requires |xs| == 2
      ensures ToNatRight(xs) == First(xs) + xs[1] * BASE()
      decreases xs
    {
      reveal ToNatRight();
      LemmaSeqLen1(DropLast(xs));
    }

    lemma /*{:_induction xs}*/ LemmaSeqAppendZero(xs: seq<uint>)
      ensures ToNatRight(xs + [0]) == ToNatRight(xs)
      decreases xs
    {
      reveal ToNatLeft();
      LemmaToNatLeftEqToNatRightAuto();
      calc {
        ToNatRight(xs + [0]);
        ToNatLeft(xs + [0]);
        ToNatLeft(xs) + 0 * Pow(BASE(), |xs|);
        {
          LemmaMulBasicsAuto();
        }
        ToNatLeft(xs);
        ToNatRight(xs);
      }
    }

    lemma /*{:_induction xs}*/ LemmaSeqNatBound(xs: seq<uint>)
      ensures ToNatRight(xs) < Pow(BASE(), |xs|)
      decreases xs
    {
      reveal Pow();
      if |xs| == 0 {
        reveal ToNatRight();
      } else {
        ghost var len' := |xs| - 1;
        ghost var pow := Pow(BASE(), len');
        calc {
          ToNatRight(xs);
          {
            LemmaToNatLeftEqToNatRight(xs);
          }
          ToNatLeft(xs);
          {
            reveal ToNatLeft();
          }
          ToNatLeft(DropLast(xs)) + Last(xs) * pow;
        <
          {
            LemmaToNatLeftEqToNatRight(DropLast(xs));
            LemmaSeqNatBound(DropLast(xs));
          }
          pow + Last(xs) * pow;
        <=
          {
            LemmaPowPositiveAuto();
            LemmaMulInequalityAuto();
          }
          pow + (BASE() - 1) * pow;
          {
            LemmaMulIsDistributiveAuto();
          }
          Pow(BASE(), len' + 1);
        }
      }
    }

    lemma /*{:_induction xs, i}*/ LemmaSeqPrefix(xs: seq<uint>, i: nat)
      requires 0 <= i <= |xs|
      ensures ToNatRight(xs[..i]) + ToNatRight(xs[i..]) * Pow(BASE(), i) == ToNatRight(xs)
      decreases xs, i
    {
      reveal ToNatRight();
      reveal Pow();
      if i == 1 {
        assert ToNatRight(xs[..1]) == First(xs);
      } else if i > 1 {
        calc {
          ToNatRight(xs[..i]) + ToNatRight(xs[i..]) * Pow(BASE(), i);
          ToNatRight(DropFirst(xs[..i])) * BASE() + First(xs) + ToNatRight(xs[i..]) * Pow(BASE(), i);
          {
            assert DropFirst(xs[..i]) == DropFirst(xs)[..i - 1];
            LemmaMulProperties();
          }
          ToNatRight(DropFirst(xs)[..i - 1]) * BASE() + First(xs) + ToNatRight(xs[i..]) * Pow(BASE(), i - 1) * BASE();
          {
            LemmaMulIsDistributiveAddOtherWayAuto();
          }
          (ToNatRight(DropFirst(xs)[..i - 1]) + ToNatRight(DropFirst(xs)[i - 1..]) * Pow(BASE(), i - 1)) * BASE() + First(xs);
          {
            LemmaSeqPrefix(DropFirst(xs), i - 1);
          }
          ToNatRight(xs);
        }
      }
    }

    lemma /*{:_induction xs, ys}*/ LemmaSeqMswInequality(xs: seq<uint>, ys: seq<uint>)
      requires |xs| == |ys| > 0
      requires Last(xs) < Last(ys)
      ensures ToNatRight(xs) < ToNatRight(ys)
      decreases xs, ys
    {
      reveal ToNatLeft();
      LemmaToNatLeftEqToNatRightAuto();
      ghost var len' := |xs| - 1;
      calc {
        ToNatRight(xs);
        ToNatLeft(xs);
      <
        {
          LemmaSeqNatBound(DropLast(xs));
        }
        Pow(BASE(), len') + Last(xs) * Pow(BASE(), len');
      ==
        {
          LemmaMulIsDistributiveAuto();
        }
        (1 + Last(xs)) * Pow(BASE(), len');
      <=
        {
          LemmaPowPositiveAuto();
          LemmaMulInequalityAuto();
        }
        ToNatLeft(ys);
        ToNatRight(ys);
      }
    }

    lemma /*{:_induction xs, ys}*/ LemmaSeqPrefixNeq(xs: seq<uint>, ys: seq<uint>, i: nat)
      requires 0 <= i <= |xs| == |ys|
      requires ToNatRight(xs[..i]) != ToNatRight(ys[..i])
      ensures ToNatRight(xs) != ToNatRight(ys)
      decreases |xs| - i
    {
      if i == |xs| {
        assert xs[..i] == xs;
        assert ys[..i] == ys;
      } else {
        if xs[i] == ys[i] {
          reveal ToNatLeft();
          assert DropLast(xs[..i + 1]) == xs[..i];
          assert DropLast(ys[..i + 1]) == ys[..i];
          LemmaToNatLeftEqToNatRightAuto();
          assert ToNatRight(xs[..i + 1]) == ToNatLeft(xs[..i + 1]);
        } else if xs[i] < ys[i] {
          LemmaSeqMswInequality(xs[..i + 1], ys[..i + 1]);
        } else {
          LemmaSeqMswInequality(ys[..i + 1], xs[..i + 1]);
        }
        LemmaSeqPrefixNeq(xs, ys, i + 1);
      }
    }

    lemma /*{:_induction xs, ys}*/ LemmaSeqNeq(xs: seq<uint>, ys: seq<uint>)
      requires |xs| == |ys|
      requires xs != ys
      ensures ToNatRight(xs) != ToNatRight(ys)
      decreases xs, ys
    {
      ghost var i: nat, n: nat := 0, |xs|;
      while i < n
        invariant 0 <= i < n
        invariant xs[..i] == ys[..i]
        decreases n - i
      {
        if xs[i] != ys[i] {
          break;
        }
        i := i + 1;
      }
      assert ToNatLeft(xs[..i]) == ToNatLeft(ys[..i]);
      reveal ToNatLeft();
      assert xs[..i + 1][..i] == xs[..i];
      assert ys[..i + 1][..i] == ys[..i];
      LemmaPowPositiveAuto();
      LemmaMulStrictInequalityAuto();
      assert ToNatLeft(xs[..i + 1]) != ToNatLeft(ys[..i + 1]);
      LemmaToNatLeftEqToNatRightAuto();
      LemmaSeqPrefixNeq(xs, ys, i + 1);
    }

    lemma /*{:_induction xs, ys}*/ LemmaSeqEq(xs: seq<uint>, ys: seq<uint>)
      requires |xs| == |ys|
      requires ToNatRight(xs) == ToNatRight(ys)
      ensures xs == ys
      decreases xs, ys
    {
      calc ==> {
        xs != ys;
        {
          LemmaSeqNeq(xs, ys);
        }
        ToNatRight(xs) != ToNatRight(ys);
        false;
      }
    }

    lemma /*{:_induction xs}*/ LemmaSeqLswModEquivalence(xs: seq<uint>)
      requires |xs| >= 1
      ensures IsModEquivalent(ToNatRight(xs), First(xs), BASE())
      decreases xs
    {
      if |xs| == 1 {
        LemmaSeqLen1(xs);
        LemmaModEquivalenceAuto();
      } else {
        assert IsModEquivalent(ToNatRight(xs), First(xs), BASE()) by {
          reveal ToNatRight();
          calc ==> {
            true;
            {
              LemmaModEquivalenceAuto();
            }
            IsModEquivalent(ToNatRight(xs), ToNatRight(DropFirst(xs)) * BASE() + First(xs), BASE());
            {
              LemmaModMultiplesBasicAuto();
            }
            IsModEquivalent(ToNatRight(xs), First(xs), BASE());
          }
        }
      }
    }

    function method {:opaque} {:fuel 0, 0} FromNat(n: nat): (xs: seq<uint>)
      decreases n
    {
      if n == 0 then
        []
      else
        LemmaDivBasicsAuto(); LemmaDivDecreasesAuto(); [n % BASE()] + FromNat(n / BASE())
    }

    lemma /*{:_induction n, len}*/ LemmaFromNatLen(n: nat, len: nat)
      requires Pow(BASE(), len) > n
      ensures |FromNat(n)| <= len
      decreases n, len
    {
      reveal FromNat();
      if n == 0 {
      } else {
        calc {
          |FromNat(n)|;
        ==
          {
            LemmaDivBasicsAuto();
          }
          1 + |FromNat(n / BASE())|;
        <=
          {
            LemmaMultiplyDivideLtAuto();
            LemmaDivDecreasesAuto();
            reveal Pow();
            LemmaFromNatLen(n / BASE(), len - 1);
          }
          len;
        }
      }
    }

    lemma /*{:_induction n}*/ LemmaNatSeqNat(n: nat)
      ensures ToNatRight(FromNat(n)) == n
      decreases n
    {
      reveal ToNatRight();
      reveal FromNat();
      if n == 0 {
      } else {
        calc {
          ToNatRight(FromNat(n));
          {
            LemmaDivBasicsAuto();
          }
          ToNatRight([n % BASE()] + FromNat(n / BASE()));
          n % BASE() + ToNatRight(FromNat(n / BASE())) * BASE();
          {
            LemmaDivDecreasesAuto();
            LemmaNatSeqNat(n / BASE());
          }
          n % BASE() + n / BASE() * BASE();
          {
            LemmaFundamentalDivMod(n, BASE());
          }
          n;
        }
      }
    }

    function method {:opaque} {:fuel 0, 0} SeqExtend(xs: seq<uint>, n: nat): (ys: seq<uint>)
      requires |xs| <= n
      ensures |ys| == n
      ensures ToNatRight(ys) == ToNatRight(xs)
      decreases n - |xs|
    {
      if |xs| >= n then
        xs
      else
        LemmaSeqAppendZero(xs); SeqExtend(xs + [0], n)
    }

    function method {:opaque} {:fuel 0, 0} SeqExtendMultiple(xs: seq<uint>, n: nat): (ys: seq<uint>)
      requires n > 0
      ensures |ys| % n == 0
      ensures ToNatRight(ys) == ToNatRight(xs)
      decreases xs, n
    {
      var newLen: int := |xs| + n - |xs| % n;
      LemmaSubModNoopRight(|xs| + n, |xs|, n);
      LemmaModBasicsAuto();
      assert newLen % n == 0;
      LemmaSeqNatBound(xs);
      LemmaPowIncreasesAuto();
      SeqExtend(xs, newLen)
    }

    function method {:opaque} {:fuel 0, 0} FromNatWithLen(n: nat, len: nat): (xs: seq<uint>)
      requires Pow(BASE(), len) > n
      ensures |xs| == len
      ensures ToNatRight(xs) == n
      decreases n, len
    {
      LemmaFromNatLen(n, len);
      LemmaNatSeqNat(n);
      SeqExtend(FromNat(n), len)
    }

    lemma /*{:_induction xs}*/ LemmaSeqZero(xs: seq<uint>)
      requires ToNatRight(xs) == 0
      ensures forall i: int :: 0 <= i < |xs| ==> xs[i] == 0
      decreases xs
    {
      reveal ToNatRight();
      if |xs| == 0 {
      } else {
        LemmaMulNonnegativeAuto();
        assert First(xs) == 0;
        LemmaMulNonzeroAuto();
        LemmaSeqZero(DropFirst(xs));
      }
    }

    function method {:opaque} {:fuel 0, 0} SeqZero(len: nat): (xs: seq<uint>)
      ensures |xs| == len
      ensures forall i: int :: 0 <= i < |xs| ==> xs[i] == 0
      ensures ToNatRight(xs) == 0
      decreases len
    {
      LemmaPowPositive(BASE(), len);
      var xs: seq<uint> := FromNatWithLen(0, len);
      LemmaSeqZero(xs);
      xs
    }

    lemma /*{:_induction xs}*/ LemmaSeqNatSeq(xs: seq<uint>)
      ensures Pow(BASE(), |xs|) > ToNatRight(xs)
      ensures FromNatWithLen(ToNatRight(xs), |xs|) == xs
      decreases xs
    {
      reveal FromNat();
      reveal ToNatRight();
      LemmaSeqNatBound(xs);
      if |xs| > 0 {
        calc {
          FromNatWithLen(ToNatRight(xs), |xs|) != xs;
          {
            LemmaSeqNeq(FromNatWithLen(ToNatRight(xs), |xs|), xs);
          }
          ToNatRight(FromNatWithLen(ToNatRight(xs), |xs|)) != ToNatRight(xs);
          ToNatRight(xs) != ToNatRight(xs);
          false;
        }
      }
    }

    function method {:opaque} {:fuel 0, 0} SeqAdd(xs: seq<uint>, ys: seq<uint>): (seq<uint>, nat)
      requires |xs| == |ys|
      ensures var (zs: seq<uint>, cout: nat) := SeqAdd(xs, ys); |zs| == |xs| && 0 <= cout <= 1
      decreases xs
    {
      if |xs| == 0 then
        ([], 0)
      else
        var (zs': seq<uint>, cin: nat) := SeqAdd(DropLast(xs), DropLast(ys)); var sum: int := Last(xs) + Last(ys) + cin; var (sum_out: int, cout: int) := if sum < BASE() then (sum, 0) else (sum - BASE(), 1); (zs' + [sum_out], cout)
    }

    lemma /*{:_induction xs, ys, zs}*/ LemmaSeqAdd(xs: seq<uint>, ys: seq<uint>, zs: seq<uint>, cout: nat)
      requires |xs| == |ys|
      requires SeqAdd(xs, ys) == (zs, cout)
      ensures ToNatRight(xs) + ToNatRight(ys) == ToNatRight(zs) + cout * Pow(BASE(), |xs|)
      decreases xs, ys, zs, cout
    {
      reveal SeqAdd();
      if |xs| == 0 {
        reveal ToNatRight();
      } else {
        ghost var pow := Pow(BASE(), |xs| - 1);
        var (zs', cin) := SeqAdd(DropLast(xs), DropLast(ys));
        ghost var sum: int := Last(xs) + Last(ys) + cin;
        ghost var z := if sum < BASE() then sum else sum - BASE();
        assert sum == z + cout * BASE();
        reveal ToNatLeft();
        LemmaToNatLeftEqToNatRightAuto();
        calc {
          ToNatRight(zs);
          ToNatLeft(zs);
          ToNatLeft(zs') + z * pow;
          {
            LemmaSeqAdd(DropLast(xs), DropLast(ys), zs', cin);
          }
          ToNatLeft(DropLast(xs)) + ToNatLeft(DropLast(ys)) - cin * pow + z * pow;
          {
            LemmaMulEqualityAuto();
            assert sum * pow == (z + cout * BASE()) * pow;
            LemmaMulIsDistributiveAuto();
          }
          ToNatLeft(xs) + ToNatLeft(ys) - cout * BASE() * pow;
          {
            LemmaMulIsAssociative(cout, BASE(), pow);
            reveal Pow();
          }
          ToNatLeft(xs) + ToNatLeft(ys) - cout * Pow(BASE(), |xs|);
          ToNatRight(xs) + ToNatRight(ys) - cout * Pow(BASE(), |xs|);
        }
      }
    }

    function method {:opaque} {:fuel 0, 0} SeqSub(xs: seq<uint>, ys: seq<uint>): (seq<uint>, nat)
      requires |xs| == |ys|
      ensures var (zs: seq<uint>, cout: nat) := SeqSub(xs, ys); |zs| == |xs| && 0 <= cout <= 1
      decreases xs
    {
      if |xs| == 0 then
        ([], 0)
      else
        var (zs: seq<uint>, cin: nat) := SeqSub(DropLast(xs), DropLast(ys)); var (diff_out: int, cout: int) := if Last(xs) >= Last(ys) + cin then (Last(xs) - Last(ys) - cin, 0) else (BASE() + Last(xs) - Last(ys) - cin, 1); (zs + [diff_out], cout)
    }

    lemma /*{:_induction xs, ys, zs}*/ LemmaSeqSub(xs: seq<uint>, ys: seq<uint>, zs: seq<uint>, cout: nat)
      requires |xs| == |ys|
      requires SeqSub(xs, ys) == (zs, cout)
      ensures ToNatRight(xs) - ToNatRight(ys) + cout * Pow(BASE(), |xs|) == ToNatRight(zs)
      decreases xs, ys, zs, cout
    {
      reveal SeqSub();
      if |xs| == 0 {
        reveal ToNatRight();
      } else {
        ghost var pow := Pow(BASE(), |xs| - 1);
        var (zs', cin) := SeqSub(DropLast(xs), DropLast(ys));
        ghost var z := if Last(xs) >= Last(ys) + cin then Last(xs) - Last(ys) - cin else BASE() + Last(xs) - Last(ys) - cin;
        assert cout * BASE() + Last(xs) - cin - Last(ys) == z;
        reveal ToNatLeft();
        LemmaToNatLeftEqToNatRightAuto();
        calc {
          ToNatRight(zs);
          ToNatLeft(zs);
          ToNatLeft(zs') + z * pow;
          {
            LemmaSeqSub(DropLast(xs), DropLast(ys), zs', cin);
          }
          ToNatLeft(DropLast(xs)) - ToNatLeft(DropLast(ys)) + cin * pow + z * pow;
          {
            LemmaMulEqualityAuto();
            assert pow * (cout * BASE() + Last(xs) - cin - Last(ys)) == pow * z;
            LemmaMulIsDistributiveAuto();
          }
          ToNatLeft(xs) - ToNatLeft(ys) + cout * BASE() * pow;
          {
            LemmaMulIsAssociative(cout, BASE(), pow);
            reveal Pow();
          }
          ToNatLeft(xs) - ToNatLeft(ys) + cout * Pow(BASE(), |xs|);
          ToNatRight(xs) - ToNatRight(ys) + cout * Pow(BASE(), |xs|);
        }
      }
    }

    import opened DivMod

    import opened Mul

    import opened Power

    import opened Seq

    type uint = i: int
      | 0 <= i < BASE()
  }

  import opened Large = Uint16Seq

  import Small = Large.Small
  function method E(): (E: nat)
    ensures Pow(Small.BASE(), E) == Large.BASE()
    ensures E > 0
  {
    LemmaDivBasicsAuto();
    LemmaPowMultipliesAuto();
    LemmaFundamentalDivMod(Large.BITS(), Small.BITS());
    Large.BITS() / Small.BITS()
  }

  function method {:opaque} {:fuel 0, 0} ToSmall(xs: seq<Large.uint>): (ys: seq<Small.uint>)
    ensures |ys| == |xs| * E()
    decreases xs
  {
    if |xs| == 0 then
      []
    else
      LemmaMulIsDistributiveAddOtherWay(E(), 1, |xs| - 1); Small.FromNatWithLen(First(xs), E()) + ToSmall(DropFirst(xs))
  }

  function method {:opaque} {:fuel 0, 0} ToLarge(xs: seq<Small.uint>): (ys: seq<Large.uint>)
    requires |xs| % E() == 0
    ensures |ys| == |xs| / E()
    decreases xs
  {
    if |xs| == 0 then
      LemmaDivBasicsAuto();
      []
    else
      LemmaModIsZero(|xs|, E()); assert |xs| >= E(); Small.LemmaSeqNatBound(xs[..E()]); LemmaModSubMultiplesVanishAuto(); LemmaDivMinusOne(|xs|, E()); [Small.ToNatRight(xs[..E()]) as Large.uint] + ToLarge(xs[E()..])
  }

  lemma /*{:_induction xs}*/ LemmaToSmall(xs: seq<Large.uint>)
    ensures Small.ToNatRight(ToSmall(xs)) == Large.ToNatRight(xs)
    decreases xs
  {
    reveal Small.ToNatRight();
    reveal Large.ToNatRight();
    reveal ToSmall();
    if |xs| == 0 {
    } else {
      calc {
        Small.ToNatRight(ToSmall(xs));
        Small.ToNatRight(Small.FromNatWithLen(First(xs), E()) + ToSmall(DropFirst(xs)));
        {
          Small.LemmaSeqPrefix(Small.FromNatWithLen(First(xs), E()) + ToSmall(DropFirst(xs)), E());
          LemmaToSmall(DropFirst(xs));
        }
        First(xs) + Large.ToNatRight(DropFirst(xs)) * Pow(Small.BASE(), E());
        {
          assert Pow(Small.BASE(), E()) == Large.BASE();
        }
        Large.ToNatRight(xs);
      }
    }
  }

  lemma /*{:_induction xs}*/ LemmaToLarge(xs: seq<Small.uint>)
    requires |xs| % E() == 0
    ensures Large.ToNatRight(ToLarge(xs)) == Small.ToNatRight(xs)
    decreases xs
  {
    reveal Large.ToNatRight();
    reveal Small.ToNatRight();
    reveal ToLarge();
    if |xs| == 0 {
    } else {
      calc {
        Large.ToNatRight(ToLarge(xs));
        {
          LemmaModIsZero(|xs|, E());
          LemmaModSubMultiplesVanishAuto();
          Small.LemmaSeqNatBound(xs[..E()]);
        }
        Large.ToNatRight([Small.ToNatRight(xs[..E()]) as Large.uint] + ToLarge(xs[E()..]));
        {
          LemmaToLarge(xs[E()..]);
        }
        Small.ToNatRight(xs[..E()]) + Small.ToNatRight(xs[E()..]) * Pow(Small.BASE(), E());
        {
          Small.LemmaSeqPrefix(xs, E());
        }
        Small.ToNatRight(xs);
      }
    }
  }

  lemma /*{:_induction xs, ys}*/ LemmaToSmallIsInjective(xs: seq<Large.uint>, ys: seq<Large.uint>)
    requires ToSmall(xs) == ToSmall(ys)
    requires |xs| == |ys|
    ensures xs == ys
    decreases xs, ys
  {
    LemmaToSmall(xs);
    LemmaToSmall(ys);
    assert Large.ToNatRight(xs) == Large.ToNatRight(ys);
    Large.LemmaSeqEq(xs, ys);
  }

  lemma /*{:_induction xs, ys}*/ LemmaToLargeIsInjective(xs: seq<Small.uint>, ys: seq<Small.uint>)
    requires |xs| % E() == |ys| % E() == 0
    requires ToLarge(xs) == ToLarge(ys)
    requires |xs| == |ys|
    ensures xs == ys
    decreases xs, ys
  {
    LemmaToLarge(xs);
    LemmaToLarge(ys);
    assert Small.ToNatRight(xs) == Small.ToNatRight(ys);
    Small.LemmaSeqEq(xs, ys);
  }

  lemma /*{:_induction xs}*/ LemmaSmallLargeSmall(xs: seq<Small.uint>)
    requires |xs| % E() == 0
    ensures ToSmall(ToLarge(xs)) == xs
    decreases xs
  {
    reveal ToSmall();
    reveal ToLarge();
    if |xs| == 0 {
    } else {
      calc {
        ToSmall(ToLarge(xs));
        {
          LemmaModIsZero(|xs|, E());
          Small.LemmaSeqNatBound(xs[..E()]);
          LemmaModSubMultiplesVanishAuto();
        }
        ToSmall([Small.ToNatRight(xs[..E()]) as Large.uint] + ToLarge(xs[E()..]));
        Small.FromNatWithLen(Small.ToNatRight(xs[..E()]), E()) + ToSmall(ToLarge(xs[E()..]));
        {
          Small.LemmaSeqNatSeq(xs[..E()]);
          LemmaSmallLargeSmall(xs[E()..]);
        }
        xs;
      }
    }
  }

  lemma /*{:_induction xs}*/ LemmaLargeSmallLarge(xs: seq<Large.uint>)
    ensures |ToSmall(xs)| % E() == 0
    ensures ToLarge(ToSmall(xs)) == xs
    decreases xs
  {
    reveal ToSmall();
    reveal ToLarge();
    LemmaModMultiplesBasicAuto();
    if |xs| == 0 {
    } else {
      calc {
        ToLarge(ToSmall(xs));
        ToLarge(Small.FromNatWithLen(First(xs), E()) + ToSmall(DropFirst(xs)));
        [Small.ToNatRight(Small.FromNatWithLen(First(xs), E())) as Large.uint] + ToLarge(ToSmall(DropFirst(xs)));
        [First(xs)] + ToLarge(ToSmall(DropFirst(xs)));
        {
          LemmaLargeSmallLarge(DropFirst(xs));
        }
        [First(xs)] + DropFirst(xs);
        xs;
      }
    }
  }

  import opened DivMod

  import opened Mul

  import opened Power

  import opened Seq
}

module srcCollectionsSequencesUint32_64dfyUnitTests {

  import Uint32_64

  import Uint32Seq = Uint32_64.Uint32Seq

  import Uint64Seq = Uint32_64.Uint64Seq

  import DivMod

  import DivInternalsNonlinear

  import DivInternals

  import GeneralInternals

  import ModInternals

  import MulInternals

  import MulInternalsNonlinear

  import Mul

  import ModInternalsNonlinear

  import Power

  import Seq

  import Wrappers

  import Math
  method {:test} test0()
  {
    var d0: seq<Uint32_64.Uint32Seq.uint> := [];
    var r0 := Uint32_64.Uint32Seq.ToNatRight(d0);
  }

  method {:test} test1()
  {
    var d0: seq<Uint32_64.Uint32Seq.uint> := [];
    var r0 := Uint32_64.Uint32Seq.ToNatLeft(d0);
  }

  method {:test} test2()
  {
    var r0 := Uint32_64.Uint32Seq.FromNat(65 as nat);
  }

  method {:test} test3()
  {
    var r0 := Uint32_64.Uint32Seq.FromNat(0 as nat);
  }

  method {:test} test4()
  {
    var d0: seq<Uint32_64.Uint32Seq.uint> := [0 as Uint32_64.Uint32Seq.uint];
    expect |d0| <= 1 as nat, ""Test does not meet preconditions and should be removed""
    var r0 := Uint32_64.Uint32Seq.SeqExtend(d0, 1 as nat);
    expect |r0| == 1 as nat, ""expectation violation""
    expect Uint32_64.Uint32Seq.ToNatRight(r0) == Uint32_64.Uint32Seq.ToNatRight(d0), ""expectation violation""
  }

  method {:test} test5()
  {
    var d0: seq<Uint32_64.Uint32Seq.uint> := [0 as Uint32_64.Uint32Seq.uint, 0 as Uint32_64.Uint32Seq.uint];
    var d1: seq<Uint32_64.Uint32Seq.uint> := [0 as Uint32_64.Uint32Seq.uint, 0 as Uint32_64.Uint32Seq.uint];
    expect |d0| == |d1|, ""Test does not meet preconditions and should be removed""
    var r0 := Uint32_64.Uint32Seq.SeqAdd(d0, d1);
  }

  method {:test} test6()
  {
    var d0: seq<Uint32_64.Uint32Seq.uint> := [12 as Uint32_64.Uint32Seq.uint, 2283 as Uint32_64.Uint32Seq.uint];
    var d1: seq<Uint32_64.Uint32Seq.uint> := [281 as Uint32_64.Uint32Seq.uint, 11138 as Uint32_64.Uint32Seq.uint];
    expect |d0| == |d1|, ""Test does not meet preconditions and should be removed""
    var r0 := Uint32_64.Uint32Seq.SeqAdd(d0, d1);
  }

  method {:test} test7()
  {
    var d0: seq<Uint32_64.Uint32Seq.uint> := [];
    var d1: seq<Uint32_64.Uint32Seq.uint> := [];
    expect |d0| == |d1|, ""Test does not meet preconditions and should be removed""
    var r0 := Uint32_64.Uint32Seq.SeqAdd(d0, d1);
  }

  method {:test} test8()
  {
    var d0: seq<Uint32_64.Uint32Seq.uint> := [1325 as Uint32_64.Uint32Seq.uint, 2331 as Uint32_64.Uint32Seq.uint];
    var d1: seq<Uint32_64.Uint32Seq.uint> := [234 as Uint32_64.Uint32Seq.uint, 1796 as Uint32_64.Uint32Seq.uint];
    expect |d0| == |d1|, ""Test does not meet preconditions and should be removed""
    var r0 := Uint32_64.Uint32Seq.SeqSub(d0, d1);
  }

  method {:test} test9()
  {
    var d0: seq<Uint32_64.Uint32Seq.uint> := [920 as Uint32_64.Uint32Seq.uint, 2061 as Uint32_64.Uint32Seq.uint];
    var d1: seq<Uint32_64.Uint32Seq.uint> := [645 as Uint32_64.Uint32Seq.uint, 2062 as Uint32_64.Uint32Seq.uint];
    expect |d0| == |d1|, ""Test does not meet preconditions and should be removed""
    var r0 := Uint32_64.Uint32Seq.SeqSub(d0, d1);
  }

  method {:test} test10()
  {
    var d0: seq<Uint32_64.Uint32Seq.uint> := [];
    var d1: seq<Uint32_64.Uint32Seq.uint> := [];
    expect |d0| == |d1|, ""Test does not meet preconditions and should be removed""
    var r0 := Uint32_64.Uint32Seq.SeqSub(d0, d1);
  }

  method {:test} test11()
  {
    var d0: seq<Uint32_64.Uint64Seq.uint> := [];
    var r0 := Uint32_64.Uint64Seq.ToNatRight(d0);
  }

  method {:test} test12()
  {
    var d0: seq<Uint32_64.Uint64Seq.uint> := [];
    var r0 := Uint32_64.Uint64Seq.ToNatLeft(d0);
  }

  method {:test} test13()
  {
    var r0 := Uint32_64.Uint64Seq.FromNat(65 as nat);
  }

  method {:test} test14()
  {
    var r0 := Uint32_64.Uint64Seq.FromNat(0 as nat);
  }

  method {:test} test15()
  {
    var d0: seq<Uint32_64.Uint64Seq.uint> := [0 as Uint32_64.Uint64Seq.uint];
    expect |d0| <= 1 as nat, ""Test does not meet preconditions and should be removed""
    var r0 := Uint32_64.Uint64Seq.SeqExtend(d0, 1 as nat);
    expect |r0| == 1 as nat, ""expectation violation""
    expect Uint32_64.Uint64Seq.ToNatRight(r0) == Uint32_64.Uint64Seq.ToNatRight(d0), ""expectation violation""
  }

  method {:test} test16()
  {
    var d0: seq<Uint32_64.Uint64Seq.uint> := [0 as Uint32_64.Uint64Seq.uint, 0 as Uint32_64.Uint64Seq.uint];
    var d1: seq<Uint32_64.Uint64Seq.uint> := [0 as Uint32_64.Uint64Seq.uint, 0 as Uint32_64.Uint64Seq.uint];
    expect |d0| == |d1|, ""Test does not meet preconditions and should be removed""
    var r0 := Uint32_64.Uint64Seq.SeqAdd(d0, d1);
  }

  method {:test} test17()
  {
    var d0: seq<Uint32_64.Uint64Seq.uint> := [342 as Uint32_64.Uint64Seq.uint, 4720 as Uint32_64.Uint64Seq.uint];
    var d1: seq<Uint32_64.Uint64Seq.uint> := [281 as Uint32_64.Uint64Seq.uint, 2283 as Uint32_64.Uint64Seq.uint];
    expect |d0| == |d1|, ""Test does not meet preconditions and should be removed""
    var r0 := Uint32_64.Uint64Seq.SeqAdd(d0, d1);
  }

  method {:test} test18()
  {
    var d0: seq<Uint32_64.Uint64Seq.uint> := [];
    var d1: seq<Uint32_64.Uint64Seq.uint> := [];
    expect |d0| == |d1|, ""Test does not meet preconditions and should be removed""
    var r0 := Uint32_64.Uint64Seq.SeqAdd(d0, d1);
  }

  method {:test} test19()
  {
    var d0: seq<Uint32_64.Uint64Seq.uint> := [1325 as Uint32_64.Uint64Seq.uint, 2331 as Uint32_64.Uint64Seq.uint];
    var d1: seq<Uint32_64.Uint64Seq.uint> := [234 as Uint32_64.Uint64Seq.uint, 1796 as Uint32_64.Uint64Seq.uint];
    expect |d0| == |d1|, ""Test does not meet preconditions and should be removed""
    var r0 := Uint32_64.Uint64Seq.SeqSub(d0, d1);
  }

  method {:test} test20()
  {
    var d0: seq<Uint32_64.Uint64Seq.uint> := [920 as Uint32_64.Uint64Seq.uint, 2061 as Uint32_64.Uint64Seq.uint];
    var d1: seq<Uint32_64.Uint64Seq.uint> := [645 as Uint32_64.Uint64Seq.uint, 2062 as Uint32_64.Uint64Seq.uint];
    expect |d0| == |d1|, ""Test does not meet preconditions and should be removed""
    var r0 := Uint32_64.Uint64Seq.SeqSub(d0, d1);
  }

  method {:test} test21()
  {
    var d0: seq<Uint32_64.Uint64Seq.uint> := [];
    var d1: seq<Uint32_64.Uint64Seq.uint> := [];
    expect |d0| == |d1|, ""Test does not meet preconditions and should be removed""
    var r0 := Uint32_64.Uint64Seq.SeqSub(d0, d1);
  }

  method {:test} test22()
  {
    var d0: seq<Uint32_64.Uint64Seq.uint> := [];
    var r0 := Uint32_64.ToSmall(d0);
    expect |r0| == |d0| * Uint32_64.E(), ""expectation violation""
  }

  method {:test} test23()
  {
    var d0: seq<Uint32_64.Uint32Seq.uint> := [0 as Uint32_64.Uint32Seq.uint, 0 as Uint32_64.Uint32Seq.uint, 0 as Uint32_64.Uint32Seq.uint, 0 as Uint32_64.Uint32Seq.uint, 0 as Uint32_64.Uint32Seq.uint, 0 as Uint32_64.Uint32Seq.uint, 0 as Uint32_64.Uint32Seq.uint, 0 as Uint32_64.Uint32Seq.uint, 0 as Uint32_64.Uint32Seq.uint, 0 as Uint32_64.Uint32Seq.uint, 0 as Uint32_64.Uint32Seq.uint, 0 as Uint32_64.Uint32Seq.uint, 0 as Uint32_64.Uint32Seq.uint, 0 as Uint32_64.Uint32Seq.uint, 0 as Uint32_64.Uint32Seq.uint, 0 as Uint32_64.Uint32Seq.uint, 0 as Uint32_64.Uint32Seq.uint, 0 as Uint32_64.Uint32Seq.uint, 0 as Uint32_64.Uint32Seq.uint, 0 as Uint32_64.Uint32Seq.uint, 0 as Uint32_64.Uint32Seq.uint, 0 as Uint32_64.Uint32Seq.uint, 0 as Uint32_64.Uint32Seq.uint, 0 as Uint32_64.Uint32Seq.uint, 0 as Uint32_64.Uint32Seq.uint, 0 as Uint32_64.Uint32Seq.uint, 0 as Uint32_64.Uint32Seq.uint, 0 as Uint32_64.Uint32Seq.uint, 0 as Uint32_64.Uint32Seq.uint, 0 as Uint32_64.Uint32Seq.uint, 0 as Uint32_64.Uint32Seq.uint, 0 as Uint32_64.Uint32Seq.uint, 0 as Uint32_64.Uint32Seq.uint, 0 as Uint32_64.Uint32Seq.uint, 0 as Uint32_64.Uint32Seq.uint, 0 as Uint32_64.Uint32Seq.uint, 0 as Uint32_64.Uint32Seq.uint, 0 as Uint32_64.Uint32Seq.uint, 0 as Uint32_64.Uint32Seq.uint, 0 as Uint32_64.Uint32Seq.uint, 0 as Uint32_64.Uint32Seq.uint, 0 as Uint32_64.Uint32Seq.uint, 0 as Uint32_64.Uint32Seq.uint, 0 as Uint32_64.Uint32Seq.uint, 0 as Uint32_64.Uint32Seq.uint, 0 as Uint32_64.Uint32Seq.uint, 0 as Uint32_64.Uint32Seq.uint, 0 as Uint32_64.Uint32Seq.uint, 0 as Uint32_64.Uint32Seq.uint, 0 as Uint32_64.Uint32Seq.uint, 0 as Uint32_64.Uint32Seq.uint, 0 as Uint32_64.Uint32Seq.uint, 0 as Uint32_64.Uint32Seq.uint, 0 as Uint32_64.Uint32Seq.uint, 0 as Uint32_64.Uint32Seq.uint, 0 as Uint32_64.Uint32Seq.uint, 0 as Uint32_64.Uint32Seq.uint, 0 as Uint32_64.Uint32Seq.uint, 0 as Uint32_64.Uint32Seq.uint, 0 as Uint32_64.Uint32Seq.uint, 0 as Uint32_64.Uint32Seq.uint, 0 as Uint32_64.Uint32Seq.uint, 0 as Uint32_64.Uint32Seq.uint, 0 as Uint32_64.Uint32Seq.uint, 0 as Uint32_64.Uint32Seq.uint, 0 as Uint32_64.Uint32Seq.uint, 0 as Uint32_64.Uint32Seq.uint, 0 as Uint32_64.Uint32Seq.uint, 0 as Uint32_64.Uint32Seq.uint, 0 as Uint32_64.Uint32Seq.uint, 0 as Uint32_64.Uint32Seq.uint, 0 as Uint32_64.Uint32Seq.uint, 0 as Uint32_64.Uint32Seq.uint, 0 as Uint32_64.Uint32Seq.uint, 0 as Uint32_64.Uint32Seq.uint, 0 as Uint32_64.Uint32Seq.uint, 0 as Uint32_64.Uint32Seq.uint, 0 as Uint32_64.Uint32Seq.uint, 0 as Uint32_64.Uint32Seq.uint, 0 as Uint32_64.Uint32Seq.uint, 0 as Uint32_64.Uint32Seq.uint, 0 as Uint32_64.Uint32Seq.uint, 0 as Uint32_64.Uint32Seq.uint, 0 as Uint32_64.Uint32Seq.uint, 0 as Uint32_64.Uint32Seq.uint, 0 as Uint32_64.Uint32Seq.uint];
    expect |d0| % Uint32_64.E() == 0, ""Test does not meet preconditions and should be removed""
    var r0 := Uint32_64.ToLarge(d0);
    expect |r0| == |d0| / Uint32_64.E(), ""expectation violation""
  }
}

module Uint32_64 refines LittleEndianNatConversions {

  module {:extern ""Uint32__64_mUint32Seq_Compile""} Uint32Seq refines SmallSeq {
    function method BITS(): nat
      ensures BITS() > 1
    {
      32
    }

    function method BASE(): nat
      ensures BASE() > 1
    {
      LemmaPowPositive(2, BITS() - 1);
      LemmaPowStrictlyIncreases(2, BITS() - 1, BITS());
      Pow(2, BITS())
    }

    function method {:opaque} {:fuel 0, 0} ToNatRight(xs: seq<uint>): nat
      decreases xs
    {
      if |xs| == 0 then
        0
      else
        LemmaMulNonnegativeAuto(); ToNatRight(DropFirst(xs)) * BASE() + First(xs)
    }

    function method {:opaque} {:fuel 0, 0} ToNatLeft(xs: seq<uint>): nat
      decreases xs
    {
      if |xs| == 0 then
        0
      else
        LemmaPowPositiveAuto(); LemmaMulNonnegativeAuto(); ToNatLeft(DropLast(xs)) + Last(xs) * Pow(BASE(), |xs| - 1)
    }

    lemma {:vcs_split_on_every_assert} /*{:_induction xs}*/ LemmaToNatLeftEqToNatRight(xs: seq<uint>)
      ensures ToNatRight(xs) == ToNatLeft(xs)
      decreases xs
    {
      reveal ToNatRight();
      reveal ToNatLeft();
      if xs == [] {
      } else {
        if DropLast(xs) == [] {
          calc {
            ToNatLeft(xs);
            Last(xs) * Pow(BASE(), |xs| - 1);
            {
              reveal Pow();
            }
            Last(xs);
            First(xs);
            {
              assert ToNatRight(DropFirst(xs)) == 0;
            }
            ToNatRight(xs);
          }
        } else {
          calc {
            ToNatLeft(xs);
            ToNatLeft(DropLast(xs)) + Last(xs) * Pow(BASE(), |xs| - 1);
            {
              LemmaToNatLeftEqToNatRight(DropLast(xs));
            }
            ToNatRight(DropLast(xs)) + Last(xs) * Pow(BASE(), |xs| - 1);
            ToNatRight(DropFirst(DropLast(xs))) * BASE() + First(xs) + Last(xs) * Pow(BASE(), |xs| - 1);
            {
              LemmaToNatLeftEqToNatRight(DropFirst(DropLast(xs)));
            }
            ToNatLeft(DropFirst(DropLast(xs))) * BASE() + First(xs) + Last(xs) * Pow(BASE(), |xs| - 1);
            {
              assert DropFirst(DropLast(xs)) == DropLast(DropFirst(xs));
              reveal Pow();
              LemmaMulProperties();
            }
            ToNatLeft(DropLast(DropFirst(xs))) * BASE() + First(xs) + Last(xs) * Pow(BASE(), |xs| - 2) * BASE();
            {
              LemmaMulIsDistributiveAddOtherWayAuto();
            }
            ToNatLeft(DropFirst(xs)) * BASE() + First(xs);
            {
              LemmaToNatLeftEqToNatRight(DropFirst(xs));
            }
            ToNatRight(xs);
          }
        }
      }
    }

    lemma LemmaToNatLeftEqToNatRightAuto()
      ensures forall xs: seq<uint> :: ToNatRight(xs) == ToNatLeft(xs)
    {
      reveal ToNatRight();
      reveal ToNatLeft();
      forall xs: seq<uint> | true
        ensures ToNatRight(xs) == ToNatLeft(xs)
      {
        LemmaToNatLeftEqToNatRight(xs);
      }
    }

    lemma /*{:_induction xs}*/ LemmaSeqLen1(xs: seq<uint>)
      requires |xs| == 1
      ensures ToNatRight(xs) == First(xs)
      decreases xs
    {
      reveal ToNatRight();
    }

    lemma /*{:_induction xs}*/ LemmaSeqLen2(xs: seq<uint>)
      requires |xs| == 2
      ensures ToNatRight(xs) == First(xs) + xs[1] * BASE()
      decreases xs
    {
      reveal ToNatRight();
      LemmaSeqLen1(DropLast(xs));
    }

    lemma /*{:_induction xs}*/ LemmaSeqAppendZero(xs: seq<uint>)
      ensures ToNatRight(xs + [0]) == ToNatRight(xs)
      decreases xs
    {
      reveal ToNatLeft();
      LemmaToNatLeftEqToNatRightAuto();
      calc {
        ToNatRight(xs + [0]);
        ToNatLeft(xs + [0]);
        ToNatLeft(xs) + 0 * Pow(BASE(), |xs|);
        {
          LemmaMulBasicsAuto();
        }
        ToNatLeft(xs);
        ToNatRight(xs);
      }
    }

    lemma /*{:_induction xs}*/ LemmaSeqNatBound(xs: seq<uint>)
      ensures ToNatRight(xs) < Pow(BASE(), |xs|)
      decreases xs
    {
      reveal Pow();
      if |xs| == 0 {
        reveal ToNatRight();
      } else {
        ghost var len' := |xs| - 1;
        ghost var pow := Pow(BASE(), len');
        calc {
          ToNatRight(xs);
          {
            LemmaToNatLeftEqToNatRight(xs);
          }
          ToNatLeft(xs);
          {
            reveal ToNatLeft();
          }
          ToNatLeft(DropLast(xs)) + Last(xs) * pow;
        <
          {
            LemmaToNatLeftEqToNatRight(DropLast(xs));
            LemmaSeqNatBound(DropLast(xs));
          }
          pow + Last(xs) * pow;
        <=
          {
            LemmaPowPositiveAuto();
            LemmaMulInequalityAuto();
          }
          pow + (BASE() - 1) * pow;
          {
            LemmaMulIsDistributiveAuto();
          }
          Pow(BASE(), len' + 1);
        }
      }
    }

    lemma /*{:_induction xs, i}*/ LemmaSeqPrefix(xs: seq<uint>, i: nat)
      requires 0 <= i <= |xs|
      ensures ToNatRight(xs[..i]) + ToNatRight(xs[i..]) * Pow(BASE(), i) == ToNatRight(xs)
      decreases xs, i
    {
      reveal ToNatRight();
      reveal Pow();
      if i == 1 {
        assert ToNatRight(xs[..1]) == First(xs);
      } else if i > 1 {
        calc {
          ToNatRight(xs[..i]) + ToNatRight(xs[i..]) * Pow(BASE(), i);
          ToNatRight(DropFirst(xs[..i])) * BASE() + First(xs) + ToNatRight(xs[i..]) * Pow(BASE(), i);
          {
            assert DropFirst(xs[..i]) == DropFirst(xs)[..i - 1];
            LemmaMulProperties();
          }
          ToNatRight(DropFirst(xs)[..i - 1]) * BASE() + First(xs) + ToNatRight(xs[i..]) * Pow(BASE(), i - 1) * BASE();
          {
            LemmaMulIsDistributiveAddOtherWayAuto();
          }
          (ToNatRight(DropFirst(xs)[..i - 1]) + ToNatRight(DropFirst(xs)[i - 1..]) * Pow(BASE(), i - 1)) * BASE() + First(xs);
          {
            LemmaSeqPrefix(DropFirst(xs), i - 1);
          }
          ToNatRight(xs);
        }
      }
    }

    lemma /*{:_induction xs, ys}*/ LemmaSeqMswInequality(xs: seq<uint>, ys: seq<uint>)
      requires |xs| == |ys| > 0
      requires Last(xs) < Last(ys)
      ensures ToNatRight(xs) < ToNatRight(ys)
      decreases xs, ys
    {
      reveal ToNatLeft();
      LemmaToNatLeftEqToNatRightAuto();
      ghost var len' := |xs| - 1;
      calc {
        ToNatRight(xs);
        ToNatLeft(xs);
      <
        {
          LemmaSeqNatBound(DropLast(xs));
        }
        Pow(BASE(), len') + Last(xs) * Pow(BASE(), len');
      ==
        {
          LemmaMulIsDistributiveAuto();
        }
        (1 + Last(xs)) * Pow(BASE(), len');
      <=
        {
          LemmaPowPositiveAuto();
          LemmaMulInequalityAuto();
        }
        ToNatLeft(ys);
        ToNatRight(ys);
      }
    }

    lemma /*{:_induction xs, ys}*/ LemmaSeqPrefixNeq(xs: seq<uint>, ys: seq<uint>, i: nat)
      requires 0 <= i <= |xs| == |ys|
      requires ToNatRight(xs[..i]) != ToNatRight(ys[..i])
      ensures ToNatRight(xs) != ToNatRight(ys)
      decreases |xs| - i
    {
      if i == |xs| {
        assert xs[..i] == xs;
        assert ys[..i] == ys;
      } else {
        if xs[i] == ys[i] {
          reveal ToNatLeft();
          assert DropLast(xs[..i + 1]) == xs[..i];
          assert DropLast(ys[..i + 1]) == ys[..i];
          LemmaToNatLeftEqToNatRightAuto();
          assert ToNatRight(xs[..i + 1]) == ToNatLeft(xs[..i + 1]);
        } else if xs[i] < ys[i] {
          LemmaSeqMswInequality(xs[..i + 1], ys[..i + 1]);
        } else {
          LemmaSeqMswInequality(ys[..i + 1], xs[..i + 1]);
        }
        LemmaSeqPrefixNeq(xs, ys, i + 1);
      }
    }

    lemma /*{:_induction xs, ys}*/ LemmaSeqNeq(xs: seq<uint>, ys: seq<uint>)
      requires |xs| == |ys|
      requires xs != ys
      ensures ToNatRight(xs) != ToNatRight(ys)
      decreases xs, ys
    {
      ghost var i: nat, n: nat := 0, |xs|;
      while i < n
        invariant 0 <= i < n
        invariant xs[..i] == ys[..i]
        decreases n - i
      {
        if xs[i] != ys[i] {
          break;
        }
        i := i + 1;
      }
      assert ToNatLeft(xs[..i]) == ToNatLeft(ys[..i]);
      reveal ToNatLeft();
      assert xs[..i + 1][..i] == xs[..i];
      assert ys[..i + 1][..i] == ys[..i];
      LemmaPowPositiveAuto();
      LemmaMulStrictInequalityAuto();
      assert ToNatLeft(xs[..i + 1]) != ToNatLeft(ys[..i + 1]);
      LemmaToNatLeftEqToNatRightAuto();
      LemmaSeqPrefixNeq(xs, ys, i + 1);
    }

    lemma /*{:_induction xs, ys}*/ LemmaSeqEq(xs: seq<uint>, ys: seq<uint>)
      requires |xs| == |ys|
      requires ToNatRight(xs) == ToNatRight(ys)
      ensures xs == ys
      decreases xs, ys
    {
      calc ==> {
        xs != ys;
        {
          LemmaSeqNeq(xs, ys);
        }
        ToNatRight(xs) != ToNatRight(ys);
        false;
      }
    }

    lemma /*{:_induction xs}*/ LemmaSeqLswModEquivalence(xs: seq<uint>)
      requires |xs| >= 1
      ensures IsModEquivalent(ToNatRight(xs), First(xs), BASE())
      decreases xs
    {
      if |xs| == 1 {
        LemmaSeqLen1(xs);
        LemmaModEquivalenceAuto();
      } else {
        assert IsModEquivalent(ToNatRight(xs), First(xs), BASE()) by {
          reveal ToNatRight();
          calc ==> {
            true;
            {
              LemmaModEquivalenceAuto();
            }
            IsModEquivalent(ToNatRight(xs), ToNatRight(DropFirst(xs)) * BASE() + First(xs), BASE());
            {
              LemmaModMultiplesBasicAuto();
            }
            IsModEquivalent(ToNatRight(xs), First(xs), BASE());
          }
        }
      }
    }

    function method {:opaque} {:fuel 0, 0} FromNat(n: nat): (xs: seq<uint>)
      decreases n
    {
      if n == 0 then
        []
      else
        LemmaDivBasicsAuto(); LemmaDivDecreasesAuto(); [n % BASE()] + FromNat(n / BASE())
    }

    lemma /*{:_induction n, len}*/ LemmaFromNatLen(n: nat, len: nat)
      requires Pow(BASE(), len) > n
      ensures |FromNat(n)| <= len
      decreases n, len
    {
      reveal FromNat();
      if n == 0 {
      } else {
        calc {
          |FromNat(n)|;
        ==
          {
            LemmaDivBasicsAuto();
          }
          1 + |FromNat(n / BASE())|;
        <=
          {
            LemmaMultiplyDivideLtAuto();
            LemmaDivDecreasesAuto();
            reveal Pow();
            LemmaFromNatLen(n / BASE(), len - 1);
          }
          len;
        }
      }
    }

    lemma /*{:_induction n}*/ LemmaNatSeqNat(n: nat)
      ensures ToNatRight(FromNat(n)) == n
      decreases n
    {
      reveal ToNatRight();
      reveal FromNat();
      if n == 0 {
      } else {
        calc {
          ToNatRight(FromNat(n));
          {
            LemmaDivBasicsAuto();
          }
          ToNatRight([n % BASE()] + FromNat(n / BASE()));
          n % BASE() + ToNatRight(FromNat(n / BASE())) * BASE();
          {
            LemmaDivDecreasesAuto();
            LemmaNatSeqNat(n / BASE());
          }
          n % BASE() + n / BASE() * BASE();
          {
            LemmaFundamentalDivMod(n, BASE());
          }
          n;
        }
      }
    }

    function method {:opaque} {:fuel 0, 0} SeqExtend(xs: seq<uint>, n: nat): (ys: seq<uint>)
      requires |xs| <= n
      ensures |ys| == n
      ensures ToNatRight(ys) == ToNatRight(xs)
      decreases n - |xs|
    {
      if |xs| >= n then
        xs
      else
        LemmaSeqAppendZero(xs); SeqExtend(xs + [0], n)
    }

    function method {:opaque} {:fuel 0, 0} SeqExtendMultiple(xs: seq<uint>, n: nat): (ys: seq<uint>)
      requires n > 0
      ensures |ys| % n == 0
      ensures ToNatRight(ys) == ToNatRight(xs)
      decreases xs, n
    {
      var newLen: int := |xs| + n - |xs| % n;
      LemmaSubModNoopRight(|xs| + n, |xs|, n);
      LemmaModBasicsAuto();
      assert newLen % n == 0;
      LemmaSeqNatBound(xs);
      LemmaPowIncreasesAuto();
      SeqExtend(xs, newLen)
    }

    function method {:opaque} {:fuel 0, 0} FromNatWithLen(n: nat, len: nat): (xs: seq<uint>)
      requires Pow(BASE(), len) > n
      ensures |xs| == len
      ensures ToNatRight(xs) == n
      decreases n, len
    {
      LemmaFromNatLen(n, len);
      LemmaNatSeqNat(n);
      SeqExtend(FromNat(n), len)
    }

    lemma /*{:_induction xs}*/ LemmaSeqZero(xs: seq<uint>)
      requires ToNatRight(xs) == 0
      ensures forall i: int :: 0 <= i < |xs| ==> xs[i] == 0
      decreases xs
    {
      reveal ToNatRight();
      if |xs| == 0 {
      } else {
        LemmaMulNonnegativeAuto();
        assert First(xs) == 0;
        LemmaMulNonzeroAuto();
        LemmaSeqZero(DropFirst(xs));
      }
    }

    function method {:opaque} {:fuel 0, 0} SeqZero(len: nat): (xs: seq<uint>)
      ensures |xs| == len
      ensures forall i: int :: 0 <= i < |xs| ==> xs[i] == 0
      ensures ToNatRight(xs) == 0
      decreases len
    {
      LemmaPowPositive(BASE(), len);
      var xs: seq<uint> := FromNatWithLen(0, len);
      LemmaSeqZero(xs);
      xs
    }

    lemma /*{:_induction xs}*/ LemmaSeqNatSeq(xs: seq<uint>)
      ensures Pow(BASE(), |xs|) > ToNatRight(xs)
      ensures FromNatWithLen(ToNatRight(xs), |xs|) == xs
      decreases xs
    {
      reveal FromNat();
      reveal ToNatRight();
      LemmaSeqNatBound(xs);
      if |xs| > 0 {
        calc {
          FromNatWithLen(ToNatRight(xs), |xs|) != xs;
          {
            LemmaSeqNeq(FromNatWithLen(ToNatRight(xs), |xs|), xs);
          }
          ToNatRight(FromNatWithLen(ToNatRight(xs), |xs|)) != ToNatRight(xs);
          ToNatRight(xs) != ToNatRight(xs);
          false;
        }
      }
    }

    function method {:opaque} {:fuel 0, 0} SeqAdd(xs: seq<uint>, ys: seq<uint>): (seq<uint>, nat)
      requires |xs| == |ys|
      ensures var (zs: seq<uint>, cout: nat) := SeqAdd(xs, ys); |zs| == |xs| && 0 <= cout <= 1
      decreases xs
    {
      if |xs| == 0 then
        ([], 0)
      else
        var (zs': seq<uint>, cin: nat) := SeqAdd(DropLast(xs), DropLast(ys)); var sum: int := Last(xs) + Last(ys) + cin; var (sum_out: int, cout: int) := if sum < BASE() then (sum, 0) else (sum - BASE(), 1); (zs' + [sum_out], cout)
    }

    lemma /*{:_induction xs, ys, zs}*/ LemmaSeqAdd(xs: seq<uint>, ys: seq<uint>, zs: seq<uint>, cout: nat)
      requires |xs| == |ys|
      requires SeqAdd(xs, ys) == (zs, cout)
      ensures ToNatRight(xs) + ToNatRight(ys) == ToNatRight(zs) + cout * Pow(BASE(), |xs|)
      decreases xs, ys, zs, cout
    {
      reveal SeqAdd();
      if |xs| == 0 {
        reveal ToNatRight();
      } else {
        ghost var pow := Pow(BASE(), |xs| - 1);
        var (zs', cin) := SeqAdd(DropLast(xs), DropLast(ys));
        ghost var sum: int := Last(xs) + Last(ys) + cin;
        ghost var z := if sum < BASE() then sum else sum - BASE();
        assert sum == z + cout * BASE();
        reveal ToNatLeft();
        LemmaToNatLeftEqToNatRightAuto();
        calc {
          ToNatRight(zs);
          ToNatLeft(zs);
          ToNatLeft(zs') + z * pow;
          {
            LemmaSeqAdd(DropLast(xs), DropLast(ys), zs', cin);
          }
          ToNatLeft(DropLast(xs)) + ToNatLeft(DropLast(ys)) - cin * pow + z * pow;
          {
            LemmaMulEqualityAuto();
            assert sum * pow == (z + cout * BASE()) * pow;
            LemmaMulIsDistributiveAuto();
          }
          ToNatLeft(xs) + ToNatLeft(ys) - cout * BASE() * pow;
          {
            LemmaMulIsAssociative(cout, BASE(), pow);
            reveal Pow();
          }
          ToNatLeft(xs) + ToNatLeft(ys) - cout * Pow(BASE(), |xs|);
          ToNatRight(xs) + ToNatRight(ys) - cout * Pow(BASE(), |xs|);
        }
      }
    }

    function method {:opaque} {:fuel 0, 0} SeqSub(xs: seq<uint>, ys: seq<uint>): (seq<uint>, nat)
      requires |xs| == |ys|
      ensures var (zs: seq<uint>, cout: nat) := SeqSub(xs, ys); |zs| == |xs| && 0 <= cout <= 1
      decreases xs
    {
      if |xs| == 0 then
        ([], 0)
      else
        var (zs: seq<uint>, cin: nat) := SeqSub(DropLast(xs), DropLast(ys)); var (diff_out: int, cout: int) := if Last(xs) >= Last(ys) + cin then (Last(xs) - Last(ys) - cin, 0) else (BASE() + Last(xs) - Last(ys) - cin, 1); (zs + [diff_out], cout)
    }

    lemma /*{:_induction xs, ys, zs}*/ LemmaSeqSub(xs: seq<uint>, ys: seq<uint>, zs: seq<uint>, cout: nat)
      requires |xs| == |ys|
      requires SeqSub(xs, ys) == (zs, cout)
      ensures ToNatRight(xs) - ToNatRight(ys) + cout * Pow(BASE(), |xs|) == ToNatRight(zs)
      decreases xs, ys, zs, cout
    {
      reveal SeqSub();
      if |xs| == 0 {
        reveal ToNatRight();
      } else {
        ghost var pow := Pow(BASE(), |xs| - 1);
        var (zs', cin) := SeqSub(DropLast(xs), DropLast(ys));
        ghost var z := if Last(xs) >= Last(ys) + cin then Last(xs) - Last(ys) - cin else BASE() + Last(xs) - Last(ys) - cin;
        assert cout * BASE() + Last(xs) - cin - Last(ys) == z;
        reveal ToNatLeft();
        LemmaToNatLeftEqToNatRightAuto();
        calc {
          ToNatRight(zs);
          ToNatLeft(zs);
          ToNatLeft(zs') + z * pow;
          {
            LemmaSeqSub(DropLast(xs), DropLast(ys), zs', cin);
          }
          ToNatLeft(DropLast(xs)) - ToNatLeft(DropLast(ys)) + cin * pow + z * pow;
          {
            LemmaMulEqualityAuto();
            assert pow * (cout * BASE() + Last(xs) - cin - Last(ys)) == pow * z;
            LemmaMulIsDistributiveAuto();
          }
          ToNatLeft(xs) - ToNatLeft(ys) + cout * BASE() * pow;
          {
            LemmaMulIsAssociative(cout, BASE(), pow);
            reveal Pow();
          }
          ToNatLeft(xs) - ToNatLeft(ys) + cout * Pow(BASE(), |xs|);
          ToNatRight(xs) - ToNatRight(ys) + cout * Pow(BASE(), |xs|);
        }
      }
    }

    import opened DivMod

    import opened Mul

    import opened Power

    import opened Seq

    type uint = i: int
      | 0 <= i < BASE()
  }

  module {:extern ""Uint32__64_mUint64Seq_Compile""} Uint64Seq refines LargeSeq {

    import Small = Uint32Seq
    function method BITS(): nat
      ensures BITS() > Small.BITS() && BITS() % Small.BITS() == 0
    {
      64
    }

    function method BASE(): nat
      ensures BASE() > 1
    {
      LemmaPowPositive(2, BITS() - 1);
      LemmaPowStrictlyIncreases(2, BITS() - 1, BITS());
      Pow(2, BITS())
    }

    function method {:opaque} {:fuel 0, 0} ToNatRight(xs: seq<uint>): nat
      decreases xs
    {
      if |xs| == 0 then
        0
      else
        LemmaMulNonnegativeAuto(); ToNatRight(DropFirst(xs)) * BASE() + First(xs)
    }

    function method {:opaque} {:fuel 0, 0} ToNatLeft(xs: seq<uint>): nat
      decreases xs
    {
      if |xs| == 0 then
        0
      else
        LemmaPowPositiveAuto(); LemmaMulNonnegativeAuto(); ToNatLeft(DropLast(xs)) + Last(xs) * Pow(BASE(), |xs| - 1)
    }

    lemma {:vcs_split_on_every_assert} /*{:_induction xs}*/ LemmaToNatLeftEqToNatRight(xs: seq<uint>)
      ensures ToNatRight(xs) == ToNatLeft(xs)
      decreases xs
    {
      reveal ToNatRight();
      reveal ToNatLeft();
      if xs == [] {
      } else {
        if DropLast(xs) == [] {
          calc {
            ToNatLeft(xs);
            Last(xs) * Pow(BASE(), |xs| - 1);
            {
              reveal Pow();
            }
            Last(xs);
            First(xs);
            {
              assert ToNatRight(DropFirst(xs)) == 0;
            }
            ToNatRight(xs);
          }
        } else {
          calc {
            ToNatLeft(xs);
            ToNatLeft(DropLast(xs)) + Last(xs) * Pow(BASE(), |xs| - 1);
            {
              LemmaToNatLeftEqToNatRight(DropLast(xs));
            }
            ToNatRight(DropLast(xs)) + Last(xs) * Pow(BASE(), |xs| - 1);
            ToNatRight(DropFirst(DropLast(xs))) * BASE() + First(xs) + Last(xs) * Pow(BASE(), |xs| - 1);
            {
              LemmaToNatLeftEqToNatRight(DropFirst(DropLast(xs)));
            }
            ToNatLeft(DropFirst(DropLast(xs))) * BASE() + First(xs) + Last(xs) * Pow(BASE(), |xs| - 1);
            {
              assert DropFirst(DropLast(xs)) == DropLast(DropFirst(xs));
              reveal Pow();
              LemmaMulProperties();
            }
            ToNatLeft(DropLast(DropFirst(xs))) * BASE() + First(xs) + Last(xs) * Pow(BASE(), |xs| - 2) * BASE();
            {
              LemmaMulIsDistributiveAddOtherWayAuto();
            }
            ToNatLeft(DropFirst(xs)) * BASE() + First(xs);
            {
              LemmaToNatLeftEqToNatRight(DropFirst(xs));
            }
            ToNatRight(xs);
          }
        }
      }
    }

    lemma LemmaToNatLeftEqToNatRightAuto()
      ensures forall xs: seq<uint> :: ToNatRight(xs) == ToNatLeft(xs)
    {
      reveal ToNatRight();
      reveal ToNatLeft();
      forall xs: seq<uint> | true
        ensures ToNatRight(xs) == ToNatLeft(xs)
      {
        LemmaToNatLeftEqToNatRight(xs);
      }
    }

    lemma /*{:_induction xs}*/ LemmaSeqLen1(xs: seq<uint>)
      requires |xs| == 1
      ensures ToNatRight(xs) == First(xs)
      decreases xs
    {
      reveal ToNatRight();
    }

    lemma /*{:_induction xs}*/ LemmaSeqLen2(xs: seq<uint>)
      requires |xs| == 2
      ensures ToNatRight(xs) == First(xs) + xs[1] * BASE()
      decreases xs
    {
      reveal ToNatRight();
      LemmaSeqLen1(DropLast(xs));
    }

    lemma /*{:_induction xs}*/ LemmaSeqAppendZero(xs: seq<uint>)
      ensures ToNatRight(xs + [0]) == ToNatRight(xs)
      decreases xs
    {
      reveal ToNatLeft();
      LemmaToNatLeftEqToNatRightAuto();
      calc {
        ToNatRight(xs + [0]);
        ToNatLeft(xs + [0]);
        ToNatLeft(xs) + 0 * Pow(BASE(), |xs|);
        {
          LemmaMulBasicsAuto();
        }
        ToNatLeft(xs);
        ToNatRight(xs);
      }
    }

    lemma /*{:_induction xs}*/ LemmaSeqNatBound(xs: seq<uint>)
      ensures ToNatRight(xs) < Pow(BASE(), |xs|)
      decreases xs
    {
      reveal Pow();
      if |xs| == 0 {
        reveal ToNatRight();
      } else {
        ghost var len' := |xs| - 1;
        ghost var pow := Pow(BASE(), len');
        calc {
          ToNatRight(xs);
          {
            LemmaToNatLeftEqToNatRight(xs);
          }
          ToNatLeft(xs);
          {
            reveal ToNatLeft();
          }
          ToNatLeft(DropLast(xs)) + Last(xs) * pow;
        <
          {
            LemmaToNatLeftEqToNatRight(DropLast(xs));
            LemmaSeqNatBound(DropLast(xs));
          }
          pow + Last(xs) * pow;
        <=
          {
            LemmaPowPositiveAuto();
            LemmaMulInequalityAuto();
          }
          pow + (BASE() - 1) * pow;
          {
            LemmaMulIsDistributiveAuto();
          }
          Pow(BASE(), len' + 1);
        }
      }
    }

    lemma /*{:_induction xs, i}*/ LemmaSeqPrefix(xs: seq<uint>, i: nat)
      requires 0 <= i <= |xs|
      ensures ToNatRight(xs[..i]) + ToNatRight(xs[i..]) * Pow(BASE(), i) == ToNatRight(xs)
      decreases xs, i
    {
      reveal ToNatRight();
      reveal Pow();
      if i == 1 {
        assert ToNatRight(xs[..1]) == First(xs);
      } else if i > 1 {
        calc {
          ToNatRight(xs[..i]) + ToNatRight(xs[i..]) * Pow(BASE(), i);
          ToNatRight(DropFirst(xs[..i])) * BASE() + First(xs) + ToNatRight(xs[i..]) * Pow(BASE(), i);
          {
            assert DropFirst(xs[..i]) == DropFirst(xs)[..i - 1];
            LemmaMulProperties();
          }
          ToNatRight(DropFirst(xs)[..i - 1]) * BASE() + First(xs) + ToNatRight(xs[i..]) * Pow(BASE(), i - 1) * BASE();
          {
            LemmaMulIsDistributiveAddOtherWayAuto();
          }
          (ToNatRight(DropFirst(xs)[..i - 1]) + ToNatRight(DropFirst(xs)[i - 1..]) * Pow(BASE(), i - 1)) * BASE() + First(xs);
          {
            LemmaSeqPrefix(DropFirst(xs), i - 1);
          }
          ToNatRight(xs);
        }
      }
    }

    lemma /*{:_induction xs, ys}*/ LemmaSeqMswInequality(xs: seq<uint>, ys: seq<uint>)
      requires |xs| == |ys| > 0
      requires Last(xs) < Last(ys)
      ensures ToNatRight(xs) < ToNatRight(ys)
      decreases xs, ys
    {
      reveal ToNatLeft();
      LemmaToNatLeftEqToNatRightAuto();
      ghost var len' := |xs| - 1;
      calc {
        ToNatRight(xs);
        ToNatLeft(xs);
      <
        {
          LemmaSeqNatBound(DropLast(xs));
        }
        Pow(BASE(), len') + Last(xs) * Pow(BASE(), len');
      ==
        {
          LemmaMulIsDistributiveAuto();
        }
        (1 + Last(xs)) * Pow(BASE(), len');
      <=
        {
          LemmaPowPositiveAuto();
          LemmaMulInequalityAuto();
        }
        ToNatLeft(ys);
        ToNatRight(ys);
      }
    }

    lemma /*{:_induction xs, ys}*/ LemmaSeqPrefixNeq(xs: seq<uint>, ys: seq<uint>, i: nat)
      requires 0 <= i <= |xs| == |ys|
      requires ToNatRight(xs[..i]) != ToNatRight(ys[..i])
      ensures ToNatRight(xs) != ToNatRight(ys)
      decreases |xs| - i
    {
      if i == |xs| {
        assert xs[..i] == xs;
        assert ys[..i] == ys;
      } else {
        if xs[i] == ys[i] {
          reveal ToNatLeft();
          assert DropLast(xs[..i + 1]) == xs[..i];
          assert DropLast(ys[..i + 1]) == ys[..i];
          LemmaToNatLeftEqToNatRightAuto();
          assert ToNatRight(xs[..i + 1]) == ToNatLeft(xs[..i + 1]);
        } else if xs[i] < ys[i] {
          LemmaSeqMswInequality(xs[..i + 1], ys[..i + 1]);
        } else {
          LemmaSeqMswInequality(ys[..i + 1], xs[..i + 1]);
        }
        LemmaSeqPrefixNeq(xs, ys, i + 1);
      }
    }

    lemma /*{:_induction xs, ys}*/ LemmaSeqNeq(xs: seq<uint>, ys: seq<uint>)
      requires |xs| == |ys|
      requires xs != ys
      ensures ToNatRight(xs) != ToNatRight(ys)
      decreases xs, ys
    {
      ghost var i: nat, n: nat := 0, |xs|;
      while i < n
        invariant 0 <= i < n
        invariant xs[..i] == ys[..i]
        decreases n - i
      {
        if xs[i] != ys[i] {
          break;
        }
        i := i + 1;
      }
      assert ToNatLeft(xs[..i]) == ToNatLeft(ys[..i]);
      reveal ToNatLeft();
      assert xs[..i + 1][..i] == xs[..i];
      assert ys[..i + 1][..i] == ys[..i];
      LemmaPowPositiveAuto();
      LemmaMulStrictInequalityAuto();
      assert ToNatLeft(xs[..i + 1]) != ToNatLeft(ys[..i + 1]);
      LemmaToNatLeftEqToNatRightAuto();
      LemmaSeqPrefixNeq(xs, ys, i + 1);
    }

    lemma /*{:_induction xs, ys}*/ LemmaSeqEq(xs: seq<uint>, ys: seq<uint>)
      requires |xs| == |ys|
      requires ToNatRight(xs) == ToNatRight(ys)
      ensures xs == ys
      decreases xs, ys
    {
      calc ==> {
        xs != ys;
        {
          LemmaSeqNeq(xs, ys);
        }
        ToNatRight(xs) != ToNatRight(ys);
        false;
      }
    }

    lemma /*{:_induction xs}*/ LemmaSeqLswModEquivalence(xs: seq<uint>)
      requires |xs| >= 1
      ensures IsModEquivalent(ToNatRight(xs), First(xs), BASE())
      decreases xs
    {
      if |xs| == 1 {
        LemmaSeqLen1(xs);
        LemmaModEquivalenceAuto();
      } else {
        assert IsModEquivalent(ToNatRight(xs), First(xs), BASE()) by {
          reveal ToNatRight();
          calc ==> {
            true;
            {
              LemmaModEquivalenceAuto();
            }
            IsModEquivalent(ToNatRight(xs), ToNatRight(DropFirst(xs)) * BASE() + First(xs), BASE());
            {
              LemmaModMultiplesBasicAuto();
            }
            IsModEquivalent(ToNatRight(xs), First(xs), BASE());
          }
        }
      }
    }

    function method {:opaque} {:fuel 0, 0} FromNat(n: nat): (xs: seq<uint>)
      decreases n
    {
      if n == 0 then
        []
      else
        LemmaDivBasicsAuto(); LemmaDivDecreasesAuto(); [n % BASE()] + FromNat(n / BASE())
    }

    lemma /*{:_induction n, len}*/ LemmaFromNatLen(n: nat, len: nat)
      requires Pow(BASE(), len) > n
      ensures |FromNat(n)| <= len
      decreases n, len
    {
      reveal FromNat();
      if n == 0 {
      } else {
        calc {
          |FromNat(n)|;
        ==
          {
            LemmaDivBasicsAuto();
          }
          1 + |FromNat(n / BASE())|;
        <=
          {
            LemmaMultiplyDivideLtAuto();
            LemmaDivDecreasesAuto();
            reveal Pow();
            LemmaFromNatLen(n / BASE(), len - 1);
          }
          len;
        }
      }
    }

    lemma /*{:_induction n}*/ LemmaNatSeqNat(n: nat)
      ensures ToNatRight(FromNat(n)) == n
      decreases n
    {
      reveal ToNatRight();
      reveal FromNat();
      if n == 0 {
      } else {
        calc {
          ToNatRight(FromNat(n));
          {
            LemmaDivBasicsAuto();
          }
          ToNatRight([n % BASE()] + FromNat(n / BASE()));
          n % BASE() + ToNatRight(FromNat(n / BASE())) * BASE();
          {
            LemmaDivDecreasesAuto();
            LemmaNatSeqNat(n / BASE());
          }
          n % BASE() + n / BASE() * BASE();
          {
            LemmaFundamentalDivMod(n, BASE());
          }
          n;
        }
      }
    }

    function method {:opaque} {:fuel 0, 0} SeqExtend(xs: seq<uint>, n: nat): (ys: seq<uint>)
      requires |xs| <= n
      ensures |ys| == n
      ensures ToNatRight(ys) == ToNatRight(xs)
      decreases n - |xs|
    {
      if |xs| >= n then
        xs
      else
        LemmaSeqAppendZero(xs); SeqExtend(xs + [0], n)
    }

    function method {:opaque} {:fuel 0, 0} SeqExtendMultiple(xs: seq<uint>, n: nat): (ys: seq<uint>)
      requires n > 0
      ensures |ys| % n == 0
      ensures ToNatRight(ys) == ToNatRight(xs)
      decreases xs, n
    {
      var newLen: int := |xs| + n - |xs| % n;
      LemmaSubModNoopRight(|xs| + n, |xs|, n);
      LemmaModBasicsAuto();
      assert newLen % n == 0;
      LemmaSeqNatBound(xs);
      LemmaPowIncreasesAuto();
      SeqExtend(xs, newLen)
    }

    function method {:opaque} {:fuel 0, 0} FromNatWithLen(n: nat, len: nat): (xs: seq<uint>)
      requires Pow(BASE(), len) > n
      ensures |xs| == len
      ensures ToNatRight(xs) == n
      decreases n, len
    {
      LemmaFromNatLen(n, len);
      LemmaNatSeqNat(n);
      SeqExtend(FromNat(n), len)
    }

    lemma /*{:_induction xs}*/ LemmaSeqZero(xs: seq<uint>)
      requires ToNatRight(xs) == 0
      ensures forall i: int :: 0 <= i < |xs| ==> xs[i] == 0
      decreases xs
    {
      reveal ToNatRight();
      if |xs| == 0 {
      } else {
        LemmaMulNonnegativeAuto();
        assert First(xs) == 0;
        LemmaMulNonzeroAuto();
        LemmaSeqZero(DropFirst(xs));
      }
    }

    function method {:opaque} {:fuel 0, 0} SeqZero(len: nat): (xs: seq<uint>)
      ensures |xs| == len
      ensures forall i: int :: 0 <= i < |xs| ==> xs[i] == 0
      ensures ToNatRight(xs) == 0
      decreases len
    {
      LemmaPowPositive(BASE(), len);
      var xs: seq<uint> := FromNatWithLen(0, len);
      LemmaSeqZero(xs);
      xs
    }

    lemma /*{:_induction xs}*/ LemmaSeqNatSeq(xs: seq<uint>)
      ensures Pow(BASE(), |xs|) > ToNatRight(xs)
      ensures FromNatWithLen(ToNatRight(xs), |xs|) == xs
      decreases xs
    {
      reveal FromNat();
      reveal ToNatRight();
      LemmaSeqNatBound(xs);
      if |xs| > 0 {
        calc {
          FromNatWithLen(ToNatRight(xs), |xs|) != xs;
          {
            LemmaSeqNeq(FromNatWithLen(ToNatRight(xs), |xs|), xs);
          }
          ToNatRight(FromNatWithLen(ToNatRight(xs), |xs|)) != ToNatRight(xs);
          ToNatRight(xs) != ToNatRight(xs);
          false;
        }
      }
    }

    function method {:opaque} {:fuel 0, 0} SeqAdd(xs: seq<uint>, ys: seq<uint>): (seq<uint>, nat)
      requires |xs| == |ys|
      ensures var (zs: seq<uint>, cout: nat) := SeqAdd(xs, ys); |zs| == |xs| && 0 <= cout <= 1
      decreases xs
    {
      if |xs| == 0 then
        ([], 0)
      else
        var (zs': seq<uint>, cin: nat) := SeqAdd(DropLast(xs), DropLast(ys)); var sum: int := Last(xs) + Last(ys) + cin; var (sum_out: int, cout: int) := if sum < BASE() then (sum, 0) else (sum - BASE(), 1); (zs' + [sum_out], cout)
    }

    lemma /*{:_induction xs, ys, zs}*/ LemmaSeqAdd(xs: seq<uint>, ys: seq<uint>, zs: seq<uint>, cout: nat)
      requires |xs| == |ys|
      requires SeqAdd(xs, ys) == (zs, cout)
      ensures ToNatRight(xs) + ToNatRight(ys) == ToNatRight(zs) + cout * Pow(BASE(), |xs|)
      decreases xs, ys, zs, cout
    {
      reveal SeqAdd();
      if |xs| == 0 {
        reveal ToNatRight();
      } else {
        ghost var pow := Pow(BASE(), |xs| - 1);
        var (zs', cin) := SeqAdd(DropLast(xs), DropLast(ys));
        ghost var sum: int := Last(xs) + Last(ys) + cin;
        ghost var z := if sum < BASE() then sum else sum - BASE();
        assert sum == z + cout * BASE();
        reveal ToNatLeft();
        LemmaToNatLeftEqToNatRightAuto();
        calc {
          ToNatRight(zs);
          ToNatLeft(zs);
          ToNatLeft(zs') + z * pow;
          {
            LemmaSeqAdd(DropLast(xs), DropLast(ys), zs', cin);
          }
          ToNatLeft(DropLast(xs)) + ToNatLeft(DropLast(ys)) - cin * pow + z * pow;
          {
            LemmaMulEqualityAuto();
            assert sum * pow == (z + cout * BASE()) * pow;
            LemmaMulIsDistributiveAuto();
          }
          ToNatLeft(xs) + ToNatLeft(ys) - cout * BASE() * pow;
          {
            LemmaMulIsAssociative(cout, BASE(), pow);
            reveal Pow();
          }
          ToNatLeft(xs) + ToNatLeft(ys) - cout * Pow(BASE(), |xs|);
          ToNatRight(xs) + ToNatRight(ys) - cout * Pow(BASE(), |xs|);
        }
      }
    }

    function method {:opaque} {:fuel 0, 0} SeqSub(xs: seq<uint>, ys: seq<uint>): (seq<uint>, nat)
      requires |xs| == |ys|
      ensures var (zs: seq<uint>, cout: nat) := SeqSub(xs, ys); |zs| == |xs| && 0 <= cout <= 1
      decreases xs
    {
      if |xs| == 0 then
        ([], 0)
      else
        var (zs: seq<uint>, cin: nat) := SeqSub(DropLast(xs), DropLast(ys)); var (diff_out: int, cout: int) := if Last(xs) >= Last(ys) + cin then (Last(xs) - Last(ys) - cin, 0) else (BASE() + Last(xs) - Last(ys) - cin, 1); (zs + [diff_out], cout)
    }

    lemma /*{:_induction xs, ys, zs}*/ LemmaSeqSub(xs: seq<uint>, ys: seq<uint>, zs: seq<uint>, cout: nat)
      requires |xs| == |ys|
      requires SeqSub(xs, ys) == (zs, cout)
      ensures ToNatRight(xs) - ToNatRight(ys) + cout * Pow(BASE(), |xs|) == ToNatRight(zs)
      decreases xs, ys, zs, cout
    {
      reveal SeqSub();
      if |xs| == 0 {
        reveal ToNatRight();
      } else {
        ghost var pow := Pow(BASE(), |xs| - 1);
        var (zs', cin) := SeqSub(DropLast(xs), DropLast(ys));
        ghost var z := if Last(xs) >= Last(ys) + cin then Last(xs) - Last(ys) - cin else BASE() + Last(xs) - Last(ys) - cin;
        assert cout * BASE() + Last(xs) - cin - Last(ys) == z;
        reveal ToNatLeft();
        LemmaToNatLeftEqToNatRightAuto();
        calc {
          ToNatRight(zs);
          ToNatLeft(zs);
          ToNatLeft(zs') + z * pow;
          {
            LemmaSeqSub(DropLast(xs), DropLast(ys), zs', cin);
          }
          ToNatLeft(DropLast(xs)) - ToNatLeft(DropLast(ys)) + cin * pow + z * pow;
          {
            LemmaMulEqualityAuto();
            assert pow * (cout * BASE() + Last(xs) - cin - Last(ys)) == pow * z;
            LemmaMulIsDistributiveAuto();
          }
          ToNatLeft(xs) - ToNatLeft(ys) + cout * BASE() * pow;
          {
            LemmaMulIsAssociative(cout, BASE(), pow);
            reveal Pow();
          }
          ToNatLeft(xs) - ToNatLeft(ys) + cout * Pow(BASE(), |xs|);
          ToNatRight(xs) - ToNatRight(ys) + cout * Pow(BASE(), |xs|);
        }
      }
    }

    import opened DivMod

    import opened Mul

    import opened Power

    import opened Seq

    type uint = i: int
      | 0 <= i < BASE()
  }

  import opened Large = Uint64Seq

  import Small = Large.Small
  function method E(): (E: nat)
    ensures Pow(Small.BASE(), E) == Large.BASE()
    ensures E > 0
  {
    LemmaDivBasicsAuto();
    LemmaPowMultipliesAuto();
    LemmaFundamentalDivMod(Large.BITS(), Small.BITS());
    Large.BITS() / Small.BITS()
  }

  function method {:opaque} {:fuel 0, 0} ToSmall(xs: seq<Large.uint>): (ys: seq<Small.uint>)
    ensures |ys| == |xs| * E()
    decreases xs
  {
    if |xs| == 0 then
      []
    else
      LemmaMulIsDistributiveAddOtherWay(E(), 1, |xs| - 1); Small.FromNatWithLen(First(xs), E()) + ToSmall(DropFirst(xs))
  }

  function method {:opaque} {:fuel 0, 0} ToLarge(xs: seq<Small.uint>): (ys: seq<Large.uint>)
    requires |xs| % E() == 0
    ensures |ys| == |xs| / E()
    decreases xs
  {
    if |xs| == 0 then
      LemmaDivBasicsAuto();
      []
    else
      LemmaModIsZero(|xs|, E()); assert |xs| >= E(); Small.LemmaSeqNatBound(xs[..E()]); LemmaModSubMultiplesVanishAuto(); LemmaDivMinusOne(|xs|, E()); [Small.ToNatRight(xs[..E()]) as Large.uint] + ToLarge(xs[E()..])
  }

  lemma /*{:_induction xs}*/ LemmaToSmall(xs: seq<Large.uint>)
    ensures Small.ToNatRight(ToSmall(xs)) == Large.ToNatRight(xs)
    decreases xs
  {
    reveal Small.ToNatRight();
    reveal Large.ToNatRight();
    reveal ToSmall();
    if |xs| == 0 {
    } else {
      calc {
        Small.ToNatRight(ToSmall(xs));
        Small.ToNatRight(Small.FromNatWithLen(First(xs), E()) + ToSmall(DropFirst(xs)));
        {
          Small.LemmaSeqPrefix(Small.FromNatWithLen(First(xs), E()) + ToSmall(DropFirst(xs)), E());
          LemmaToSmall(DropFirst(xs));
        }
        First(xs) + Large.ToNatRight(DropFirst(xs)) * Pow(Small.BASE(), E());
        {
          assert Pow(Small.BASE(), E()) == Large.BASE();
        }
        Large.ToNatRight(xs);
      }
    }
  }

  lemma /*{:_induction xs}*/ LemmaToLarge(xs: seq<Small.uint>)
    requires |xs| % E() == 0
    ensures Large.ToNatRight(ToLarge(xs)) == Small.ToNatRight(xs)
    decreases xs
  {
    reveal Large.ToNatRight();
    reveal Small.ToNatRight();
    reveal ToLarge();
    if |xs| == 0 {
    } else {
      calc {
        Large.ToNatRight(ToLarge(xs));
        {
          LemmaModIsZero(|xs|, E());
          LemmaModSubMultiplesVanishAuto();
          Small.LemmaSeqNatBound(xs[..E()]);
        }
        Large.ToNatRight([Small.ToNatRight(xs[..E()]) as Large.uint] + ToLarge(xs[E()..]));
        {
          LemmaToLarge(xs[E()..]);
        }
        Small.ToNatRight(xs[..E()]) + Small.ToNatRight(xs[E()..]) * Pow(Small.BASE(), E());
        {
          Small.LemmaSeqPrefix(xs, E());
        }
        Small.ToNatRight(xs);
      }
    }
  }

  lemma /*{:_induction xs, ys}*/ LemmaToSmallIsInjective(xs: seq<Large.uint>, ys: seq<Large.uint>)
    requires ToSmall(xs) == ToSmall(ys)
    requires |xs| == |ys|
    ensures xs == ys
    decreases xs, ys
  {
    LemmaToSmall(xs);
    LemmaToSmall(ys);
    assert Large.ToNatRight(xs) == Large.ToNatRight(ys);
    Large.LemmaSeqEq(xs, ys);
  }

  lemma /*{:_induction xs, ys}*/ LemmaToLargeIsInjective(xs: seq<Small.uint>, ys: seq<Small.uint>)
    requires |xs| % E() == |ys| % E() == 0
    requires ToLarge(xs) == ToLarge(ys)
    requires |xs| == |ys|
    ensures xs == ys
    decreases xs, ys
  {
    LemmaToLarge(xs);
    LemmaToLarge(ys);
    assert Small.ToNatRight(xs) == Small.ToNatRight(ys);
    Small.LemmaSeqEq(xs, ys);
  }

  lemma /*{:_induction xs}*/ LemmaSmallLargeSmall(xs: seq<Small.uint>)
    requires |xs| % E() == 0
    ensures ToSmall(ToLarge(xs)) == xs
    decreases xs
  {
    reveal ToSmall();
    reveal ToLarge();
    if |xs| == 0 {
    } else {
      calc {
        ToSmall(ToLarge(xs));
        {
          LemmaModIsZero(|xs|, E());
          Small.LemmaSeqNatBound(xs[..E()]);
          LemmaModSubMultiplesVanishAuto();
        }
        ToSmall([Small.ToNatRight(xs[..E()]) as Large.uint] + ToLarge(xs[E()..]));
        Small.FromNatWithLen(Small.ToNatRight(xs[..E()]), E()) + ToSmall(ToLarge(xs[E()..]));
        {
          Small.LemmaSeqNatSeq(xs[..E()]);
          LemmaSmallLargeSmall(xs[E()..]);
        }
        xs;
      }
    }
  }

  lemma /*{:_induction xs}*/ LemmaLargeSmallLarge(xs: seq<Large.uint>)
    ensures |ToSmall(xs)| % E() == 0
    ensures ToLarge(ToSmall(xs)) == xs
    decreases xs
  {
    reveal ToSmall();
    reveal ToLarge();
    LemmaModMultiplesBasicAuto();
    if |xs| == 0 {
    } else {
      calc {
        ToLarge(ToSmall(xs));
        ToLarge(Small.FromNatWithLen(First(xs), E()) + ToSmall(DropFirst(xs)));
        [Small.ToNatRight(Small.FromNatWithLen(First(xs), E())) as Large.uint] + ToLarge(ToSmall(DropFirst(xs)));
        [First(xs)] + ToLarge(ToSmall(DropFirst(xs)));
        {
          LemmaLargeSmallLarge(DropFirst(xs));
        }
        [First(xs)] + DropFirst(xs);
        xs;
      }
    }
  }

  import opened DivMod

  import opened Mul

  import opened Power

  import opened Seq
}

module srcCollectionsSetsIsetsdfyUnitTests {

  import Isets

  import Functions
}

module Isets {

  import opened Functions
  lemma LemmaSubset<T>(x: iset<T>, y: iset<T>)
    requires forall e: T {:trigger e in y} :: e in x ==> e in y
    ensures x <= y
  {
  }

  function {:opaque} {:fuel 0, 0} Map<X(!new), Y>(xs: iset<X>, f: X --> Y): (ys: iset<Y>)
    requires forall x: X {:trigger f.requires(x)} :: f.requires(x)
    requires Injective(f)
    reads f.reads
    ensures forall x: X {:trigger f(x)} :: x in xs <==> f(x) in ys
    decreases set _x0: X, _o0: object? | _o0 in f.reads(_x0) :: _o0
  {
    ghost var ys: iset<Y> := iset x: X {:trigger f(x)} {:trigger x in xs} | x in xs :: f(x);
    ys
  }

  function {:opaque} {:fuel 0, 0} Filter<X(!new)>(xs: iset<X>, f: X ~> bool): (ys: iset<X>)
    requires forall x: X {:trigger f.requires(x)} {:trigger x in xs} :: x in xs ==> f.requires(x)
    reads f.reads
    ensures forall y: X {:trigger f(y)} {:trigger y in xs} :: y in ys <==> y in xs && f(y)
    decreases set _x0: X, _o0: object? | _o0 in f.reads(_x0) :: _o0
  {
    ghost var ys: iset<X> := iset x: X {:trigger f(x)} {:trigger x in xs} | x in xs && f(x);
    ys
  }
}

module srcCollectionsSetsSetsdfyUnitTests {

  import Sets

  import Functions
  method {:test} test1()
  {
    var d0: set<int> := {};
    var r0 := Sets.Map<int, int>(d0, (a0: int) => 0);
    expect |d0| == |r0|, ""expectation violation""
  }

  method {:test} test3()
  {
    var d0: set<int> := {0, 1, 2};
    var r0 := Sets.Filter<int>(d0, (a0: int) => false);
    expect |r0| <= |d0|, ""expectation violation""
  }

  method {:test} test4()
  {
    var d0: set<int> := {};
    var r0 := Sets.Filter<int>(d0, (a0: int) => false);
    expect |r0| <= |d0|, ""expectation violation""
  }

  method {:test} test5()
  {
    var d0: set<int> := {0};
    var r0 := Sets.Filter<int>(d0, (a0: int) => false);
    expect |r0| <= |d0|, ""expectation violation""
  }

  method {:test} test7()
  {
    expect 2275 <= 2279, ""Test does not meet preconditions and should be removed""
    var r0 := Sets.SetRange(2275, 2279);
    expect |r0| == 2279 - 2275, ""expectation violation""
  }

  method {:test} test8()
  {
    expect 7719 <= 7719, ""Test does not meet preconditions and should be removed""
    var r0 := Sets.SetRange(7719, 7719);
    expect |r0| == 7719 - 7719, ""expectation violation""
  }

  method {:test} test9()
  {
    expect 3 >= 0, ""Test does not meet preconditions and should be removed""
    var r0 := Sets.SetRangeZeroBound(3);
    expect |r0| == 3, ""expectation violation""
  }
}

module Sets {

  import opened Functions
  lemma LemmaSubset<T>(x: set<T>, y: set<T>)
    requires forall e: T {:trigger e in y} :: e in x ==> e in y
    ensures x <= y
    decreases x, y
  {
  }

  lemma LemmaSubsetSize<T>(x: set<T>, y: set<T>)
    ensures x < y ==> |x| < |y|
    ensures x <= y ==> |x| <= |y|
    decreases x, y
  {
  }

  lemma LemmaSubsetEquality<T>(x: set<T>, y: set<T>)
    requires x <= y
    requires |x| == |y|
    ensures x == y
    decreases x, y
  {
  }

  lemma LemmaSingletonSize<T>(x: set<T>, e: T)
    requires x == {e}
    ensures |x| == 1
    decreases x
  {
  }

  lemma LemmaSingletonEquality<T>(x: set<T>, a: T, b: T)
    requires |x| == 1
    requires a in x
    requires b in x
    ensures a == b
    decreases x
  {
  }

  lemma LemmaMapSize<X(!new), Y>(xs: set<X>, ys: set<Y>, f: X --> Y)
    requires forall x: X {:trigger f.requires(x)} :: f.requires(x)
    requires Injective(f)
    requires forall x: X {:trigger f(x)} :: x in xs <==> f(x) in ys
    requires forall y: Y {:trigger y in ys} :: y in ys ==> exists x: X :: x in xs && y == f(x)
    ensures |xs| == |ys|
    decreases xs, ys
  {
  }

  function method {:opaque} {:fuel 0, 0} Map<X(!new), Y>(xs: set<X>, f: X --> Y): (ys: set<Y>)
    requires forall x: X {:trigger f.requires(x)} :: f.requires(x)
    requires Injective(f)
    reads f.reads
    ensures forall x: X {:trigger f(x)} :: x in xs <==> f(x) in ys
    ensures |xs| == |ys|
    decreases set _x0: X, _o0: object? | _o0 in f.reads(_x0) :: _o0, xs
  {
    var ys: set<Y> := set x: X {:trigger f(x)} {:trigger x in xs} | x in xs :: f(x);
    LemmaMapSize(xs, ys, f);
    ys
  }

  lemma LemmaFilterSize<X>(xs: set<X>, ys: set<X>, f: X ~> bool)
    requires forall x: X {:trigger f.requires(x)} {:trigger x in xs} :: x in xs ==> f.requires(x)
    requires forall y: X {:trigger f(y)} {:trigger y in xs} :: y in ys ==> y in xs && f(y)
    ensures |ys| <= |xs|
    decreases xs, ys
  {
  }

  function method {:opaque} {:fuel 0, 0} Filter<X(!new)>(xs: set<X>, f: X ~> bool): (ys: set<X>)
    requires forall x: X {:trigger f.requires(x)} {:trigger x in xs} :: x in xs ==> f.requires(x)
    reads f.reads
    ensures forall y: X {:trigger f(y)} {:trigger y in xs} :: y in ys <==> y in xs && f(y)
    ensures |ys| <= |xs|
    decreases set _x0: X, _o0: object? | _o0 in f.reads(_x0) :: _o0, xs
  {
    var ys: set<X> := set x: X {:trigger f(x)} {:trigger x in xs} | x in xs && f(x);
    LemmaFilterSize(xs, ys, f);
    ys
  }

  lemma LemmaUnionSize<X>(xs: set<X>, ys: set<X>)
    ensures |xs + ys| >= |xs|
    ensures |xs + ys| >= |ys|
    decreases xs, ys
  {
  }

  function method {:opaque} {:fuel 0, 0} SetRange(a: int, b: int): (s: set<int>)
    requires a <= b
    ensures forall i: int {:trigger i in s} :: a <= i < b <==> i in s
    ensures |s| == b - a
    decreases b - a
  {
    if a == b then
      {}
    else
      {a} + SetRange(a + 1, b)
  }

  function method {:opaque} {:fuel 0, 0} SetRangeZeroBound(n: int): (s: set<int>)
    requires n >= 0
    ensures forall i: int {:trigger i in s} :: 0 <= i < n <==> i in s
    ensures |s| == n
    decreases n
  {
    SetRange(0, n)
  }

  lemma LemmaBoundedSetSize(x: set<int>, a: int, b: int)
    requires forall i: int {:trigger i in x} :: i in x ==> a <= i < b
    requires a <= b
    ensures |x| <= b - a
    decreases x, a, b
  {
  }
}
")]

//-----------------------------------------------------------------------------
//
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------

#if ISDAFNYRUNTIMELIB
using System; // for Func
using System.Numerics;
using System.Collections;
#endif

namespace DafnyAssembly {
  [AttributeUsage(AttributeTargets.Assembly)]
  public class DafnySourceAttribute : Attribute {
    public readonly string dafnySourceText;
    public DafnySourceAttribute(string txt) { dafnySourceText = txt; }
  }
}

namespace Dafny {
  using System.Collections.Generic;
  using System.Collections.Immutable;
  using System.Linq;

  public interface ISet<out T> {
    int Count { get; }
    long LongCount { get; }
    IEnumerable<T> Elements { get; }
    IEnumerable<ISet<T>> AllSubsets { get; }
    bool Contains<G>(G t);
    bool EqualsAux(ISet<object> other);
    ISet<U> DowncastClone<U>(Func<T, U> converter);
  }

  public class Set<T> : ISet<T> {
    readonly ImmutableHashSet<T> setImpl;
    readonly bool containsNull;
    Set(ImmutableHashSet<T> d, bool containsNull) {
      this.setImpl = d;
      this.containsNull = containsNull;
    }

    public static readonly ISet<T> Empty = new Set<T>(ImmutableHashSet<T>.Empty, false);

    private static readonly TypeDescriptor<ISet<T>> _TYPE = new Dafny.TypeDescriptor<ISet<T>>(Empty);
    public static TypeDescriptor<ISet<T>> _TypeDescriptor() {
      return _TYPE;
    }

    public static ISet<T> FromElements(params T[] values) {
      return FromCollection(values);
    }

    public static Set<T> FromISet(ISet<T> s) {
      return s as Set<T> ?? FromCollection(s.Elements);
    }

    public static Set<T> FromCollection(IEnumerable<T> values) {
      var d = ImmutableHashSet<T>.Empty.ToBuilder();
      var containsNull = false;
      foreach (T t in values) {
        if (t == null) {
          containsNull = true;
        } else {
          d.Add(t);
        }
      }

      return new Set<T>(d.ToImmutable(), containsNull);
    }

    public static ISet<T> FromCollectionPlusOne(IEnumerable<T> values, T oneMoreValue) {
      var d = ImmutableHashSet<T>.Empty.ToBuilder();
      var containsNull = false;
      if (oneMoreValue == null) {
        containsNull = true;
      } else {
        d.Add(oneMoreValue);
      }

      foreach (T t in values) {
        if (t == null) {
          containsNull = true;
        } else {
          d.Add(t);
        }
      }

      return new Set<T>(d.ToImmutable(), containsNull);
    }

    public ISet<U> DowncastClone<U>(Func<T, U> converter) {
      if (this is ISet<U> th) {
        return th;
      } else {
        var d = ImmutableHashSet<U>.Empty.ToBuilder();
        foreach (var t in this.setImpl) {
          var u = converter(t);
          d.Add(u);
        }

        return new Set<U>(d.ToImmutable(), this.containsNull);
      }
    }

    public int Count {
      get { return this.setImpl.Count + (containsNull ? 1 : 0); }
    }

    public long LongCount {
      get { return this.setImpl.Count + (containsNull ? 1 : 0); }
    }

    public IEnumerable<T> Elements {
      get {
        if (containsNull) {
          yield return default(T);
        }

        foreach (var t in this.setImpl) {
          yield return t;
        }
      }
    }

    /// <summary>
    /// This is an inefficient iterator for producing all subsets of "this".
    /// </summary>
    public IEnumerable<ISet<T>> AllSubsets {
      get {
        // Start by putting all set elements into a list, but don't include null
        var elmts = new List<T>();
        elmts.AddRange(this.setImpl);
        var n = elmts.Count;
        var which = new bool[n];
        var s = ImmutableHashSet<T>.Empty.ToBuilder();
        while (true) {
          // yield both the subset without null and, if null is in the original set, the subset with null included
          var ihs = s.ToImmutable();
          yield return new Set<T>(ihs, false);
          if (containsNull) {
            yield return new Set<T>(ihs, true);
          }

          // "add 1" to "which", as if doing a carry chain.  For every digit changed, change the membership of the corresponding element in "s".
          int i = 0;
          for (; i < n && which[i]; i++) {
            which[i] = false;
            s.Remove(elmts[i]);
          }

          if (i == n) {
            // we have cycled through all the subsets
            break;
          }

          which[i] = true;
          s.Add(elmts[i]);
        }
      }
    }

    public bool Equals(ISet<T> other) {
      if (ReferenceEquals(this, other)) {
        return true;
      }

      if (other == null || Count != other.Count) {
        return false;
      }

      foreach (var elmt in Elements) {
        if (!other.Contains(elmt)) {
          return false;
        }
      }

      return true;
    }

    public override bool Equals(object other) {
      if (other is ISet<T>) {
        return Equals((ISet<T>)other);
      }

      var th = this as ISet<object>;
      var oth = other as ISet<object>;
      if (th != null && oth != null) {
        // We'd like to obtain the more specific type parameter U for oth's type ISet<U>.
        // We do that by making a dynamically dispatched call, like:
        //     oth.Equals(this)
        // The hope is then that its comparison "this is ISet<U>" (that is, the first "if" test
        // above, but in the call "oth.Equals(this)") will be true and the non-virtual Equals
        // can be called. However, such a recursive call to "oth.Equals(this)" could turn
        // into infinite recursion. Therefore, we instead call "oth.EqualsAux(this)", which
        // performs the desired type test, but doesn't recurse any further.
        return oth.EqualsAux(th);
      } else {
        return false;
      }
    }

    public bool EqualsAux(ISet<object> other) {
      var s = other as ISet<T>;
      if (s != null) {
        return Equals(s);
      } else {
        return false;
      }
    }

    public override int GetHashCode() {
      var hashCode = 1;
      if (containsNull) {
        hashCode = hashCode * (Dafny.Helpers.GetHashCode(default(T)) + 3);
      }

      foreach (var t in this.setImpl) {
        hashCode = hashCode * (Dafny.Helpers.GetHashCode(t) + 3);
      }

      return hashCode;
    }

    public override string ToString() {
      var s = "{";
      var sep = "";
      if (containsNull) {
        s += sep + Dafny.Helpers.ToString(default(T));
        sep = ", ";
      }

      foreach (var t in this.setImpl) {
        s += sep + Dafny.Helpers.ToString(t);
        sep = ", ";
      }

      return s + "}";
    }
    public static bool IsProperSubsetOf(ISet<T> th, ISet<T> other) {
      return th.Count < other.Count && IsSubsetOf(th, other);
    }
    public static bool IsSubsetOf(ISet<T> th, ISet<T> other) {
      if (other.Count < th.Count) {
        return false;
      }
      foreach (T t in th.Elements) {
        if (!other.Contains(t)) {
          return false;
        }
      }
      return true;
    }
    public static bool IsDisjointFrom(ISet<T> th, ISet<T> other) {
      ISet<T> a, b;
      if (th.Count < other.Count) {
        a = th; b = other;
      } else {
        a = other; b = th;
      }
      foreach (T t in a.Elements) {
        if (b.Contains(t)) {
          return false;
        }
      }
      return true;
    }
    public bool Contains<G>(G t) {
      return t == null ? containsNull : t is T && this.setImpl.Contains((T)(object)t);
    }
    public static ISet<T> Union(ISet<T> th, ISet<T> other) {
      var a = FromISet(th);
      var b = FromISet(other);
      return new Set<T>(a.setImpl.Union(b.setImpl), a.containsNull || b.containsNull);
    }
    public static ISet<T> Intersect(ISet<T> th, ISet<T> other) {
      var a = FromISet(th);
      var b = FromISet(other);
      return new Set<T>(a.setImpl.Intersect(b.setImpl), a.containsNull && b.containsNull);
    }
    public static ISet<T> Difference(ISet<T> th, ISet<T> other) {
      var a = FromISet(th);
      var b = FromISet(other);
      return new Set<T>(a.setImpl.Except(b.setImpl), a.containsNull && !b.containsNull);
    }
  }

  public interface IMultiSet<out T> {
    bool IsEmpty { get; }
    int Count { get; }
    long LongCount { get; }
    IEnumerable<T> Elements { get; }
    IEnumerable<T> UniqueElements { get; }
    bool Contains<G>(G t);
    BigInteger Select<G>(G t);
    IMultiSet<T> Update<G>(G t, BigInteger i);
    bool EqualsAux(IMultiSet<object> other);
    IMultiSet<U> DowncastClone<U>(Func<T, U> converter);
  }

  public class MultiSet<T> : IMultiSet<T> {
    readonly ImmutableDictionary<T, BigInteger> dict;
    readonly BigInteger occurrencesOfNull;  // stupidly, a Dictionary in .NET cannot use "null" as a key
    MultiSet(ImmutableDictionary<T, BigInteger>.Builder d, BigInteger occurrencesOfNull) {
      dict = d.ToImmutable();
      this.occurrencesOfNull = occurrencesOfNull;
    }
    public static readonly MultiSet<T> Empty = new MultiSet<T>(ImmutableDictionary<T, BigInteger>.Empty.ToBuilder(), BigInteger.Zero);

    private static readonly TypeDescriptor<IMultiSet<T>> _TYPE = new Dafny.TypeDescriptor<IMultiSet<T>>(Empty);
    public static TypeDescriptor<IMultiSet<T>> _TypeDescriptor() {
      return _TYPE;
    }

    public static MultiSet<T> FromIMultiSet(IMultiSet<T> s) {
      return s as MultiSet<T> ?? FromCollection(s.Elements);
    }
    public static MultiSet<T> FromElements(params T[] values) {
      var d = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      var occurrencesOfNull = BigInteger.Zero;
      foreach (T t in values) {
        if (t == null) {
          occurrencesOfNull++;
        } else {
          BigInteger i;
          if (!d.TryGetValue(t, out i)) {
            i = BigInteger.Zero;
          }
          d[t] = i + 1;
        }
      }
      return new MultiSet<T>(d, occurrencesOfNull);
    }

    public static MultiSet<T> FromCollection(IEnumerable<T> values) {
      var d = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      var occurrencesOfNull = BigInteger.Zero;
      foreach (T t in values) {
        if (t == null) {
          occurrencesOfNull++;
        } else {
          BigInteger i;
          if (!d.TryGetValue(t,
            out i)) {
            i = BigInteger.Zero;
          }

          d[t] = i + 1;
        }
      }

      return new MultiSet<T>(d,
        occurrencesOfNull);
    }

    public static MultiSet<T> FromSeq(ISequence<T> values) {
      var d = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      var occurrencesOfNull = BigInteger.Zero;
      foreach (var t in values) {
        if (t == null) {
          occurrencesOfNull++;
        } else {
          BigInteger i;
          if (!d.TryGetValue(t,
            out i)) {
            i = BigInteger.Zero;
          }

          d[t] = i + 1;
        }
      }

      return new MultiSet<T>(d,
        occurrencesOfNull);
    }
    public static MultiSet<T> FromSet(ISet<T> values) {
      var d = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      var containsNull = false;
      foreach (T t in values.Elements) {
        if (t == null) {
          containsNull = true;
        } else {
          d[t] = BigInteger.One;
        }
      }
      return new MultiSet<T>(d, containsNull ? BigInteger.One : BigInteger.Zero);
    }
    public IMultiSet<U> DowncastClone<U>(Func<T, U> converter) {
      if (this is IMultiSet<U> th) {
        return th;
      } else {
        var d = ImmutableDictionary<U, BigInteger>.Empty.ToBuilder();
        foreach (var item in this.dict) {
          var k = converter(item.Key);
          d.Add(k, item.Value);
        }
        return new MultiSet<U>(d, this.occurrencesOfNull);
      }
    }

    public bool Equals(IMultiSet<T> other) {
      return IsSubsetOf(this, other) && IsSubsetOf(other, this);
    }
    public override bool Equals(object other) {
      if (other is IMultiSet<T>) {
        return Equals((IMultiSet<T>)other);
      }
      var th = this as IMultiSet<object>;
      var oth = other as IMultiSet<object>;
      if (th != null && oth != null) {
        // See comment in Set.Equals
        return oth.EqualsAux(th);
      } else {
        return false;
      }
    }

    public bool EqualsAux(IMultiSet<object> other) {
      var s = other as IMultiSet<T>;
      if (s != null) {
        return Equals(s);
      } else {
        return false;
      }
    }

    public override int GetHashCode() {
      var hashCode = 1;
      if (occurrencesOfNull > 0) {
        var key = Dafny.Helpers.GetHashCode(default(T));
        key = (key << 3) | (key >> 29) ^ occurrencesOfNull.GetHashCode();
        hashCode = hashCode * (key + 3);
      }
      foreach (var kv in dict) {
        var key = Dafny.Helpers.GetHashCode(kv.Key);
        key = (key << 3) | (key >> 29) ^ kv.Value.GetHashCode();
        hashCode = hashCode * (key + 3);
      }
      return hashCode;
    }
    public override string ToString() {
      var s = "multiset{";
      var sep = "";
      for (var i = BigInteger.Zero; i < occurrencesOfNull; i++) {
        s += sep + Dafny.Helpers.ToString(default(T));
        sep = ", ";
      }
      foreach (var kv in dict) {
        var t = Dafny.Helpers.ToString(kv.Key);
        for (var i = BigInteger.Zero; i < kv.Value; i++) {
          s += sep + t;
          sep = ", ";
        }
      }
      return s + "}";
    }
    public static bool IsProperSubsetOf(IMultiSet<T> th, IMultiSet<T> other) {
      return th.Count < other.Count && IsSubsetOf(th, other);
    }
    public static bool IsSubsetOf(IMultiSet<T> th, IMultiSet<T> other) {
      var a = FromIMultiSet(th);
      var b = FromIMultiSet(other);
      if (b.occurrencesOfNull < a.occurrencesOfNull) {
        return false;
      }
      foreach (T t in a.dict.Keys) {
        if (b.dict.ContainsKey(t)) {
          if (b.dict[t] < a.dict[t]) {
            return false;
          }
        } else {
          if (a.dict[t] != BigInteger.Zero) {
            return false;
          }
        }
      }
      return true;
    }
    public static bool IsDisjointFrom(IMultiSet<T> th, IMultiSet<T> other) {
      foreach (T t in th.UniqueElements) {
        if (other.Contains(t)) {
          return false;
        }
      }
      return true;
    }

    public bool Contains<G>(G t) {
      return Select(t) != 0;
    }
    public BigInteger Select<G>(G t) {
      if (t == null) {
        return occurrencesOfNull;
      }
      BigInteger m;
      if (t is T && dict.TryGetValue((T)(object)t, out m)) {
        return m;
      } else {
        return BigInteger.Zero;
      }
    }
    public IMultiSet<T> Update<G>(G t, BigInteger i) {
      if (Select(t) == i) {
        return this;
      } else if (t == null) {
        var r = dict.ToBuilder();
        return new MultiSet<T>(r, i);
      } else {
        var r = dict.ToBuilder();
        r[(T)(object)t] = i;
        return new MultiSet<T>(r, occurrencesOfNull);
      }
    }
    public static IMultiSet<T> Union(IMultiSet<T> th, IMultiSet<T> other) {
      if (th.IsEmpty) {
        return other;
      } else if (other.IsEmpty) {
        return th;
      }
      var a = FromIMultiSet(th);
      var b = FromIMultiSet(other);
      var r = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      foreach (T t in a.dict.Keys) {
        BigInteger i;
        if (!r.TryGetValue(t, out i)) {
          i = BigInteger.Zero;
        }
        r[t] = i + a.dict[t];
      }
      foreach (T t in b.dict.Keys) {
        BigInteger i;
        if (!r.TryGetValue(t, out i)) {
          i = BigInteger.Zero;
        }
        r[t] = i + b.dict[t];
      }
      return new MultiSet<T>(r, a.occurrencesOfNull + b.occurrencesOfNull);
    }
    public static IMultiSet<T> Intersect(IMultiSet<T> th, IMultiSet<T> other) {
      if (th.IsEmpty) {
        return th;
      } else if (other.IsEmpty) {
        return other;
      }
      var a = FromIMultiSet(th);
      var b = FromIMultiSet(other);
      var r = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      foreach (T t in a.dict.Keys) {
        if (b.dict.ContainsKey(t)) {
          r.Add(t, a.dict[t] < b.dict[t] ? a.dict[t] : b.dict[t]);
        }
      }
      return new MultiSet<T>(r, a.occurrencesOfNull < b.occurrencesOfNull ? a.occurrencesOfNull : b.occurrencesOfNull);
    }
    public static IMultiSet<T> Difference(IMultiSet<T> th, IMultiSet<T> other) { // \result == this - other
      if (other.IsEmpty) {
        return th;
      }
      var a = FromIMultiSet(th);
      var b = FromIMultiSet(other);
      var r = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      foreach (T t in a.dict.Keys) {
        if (!b.dict.ContainsKey(t)) {
          r.Add(t, a.dict[t]);
        } else if (b.dict[t] < a.dict[t]) {
          r.Add(t, a.dict[t] - b.dict[t]);
        }
      }
      return new MultiSet<T>(r, b.occurrencesOfNull < a.occurrencesOfNull ? a.occurrencesOfNull - b.occurrencesOfNull : BigInteger.Zero);
    }

    public bool IsEmpty { get { return occurrencesOfNull == 0 && dict.IsEmpty; } }

    public int Count {
      get { return (int)ElementCount(); }
    }
    public long LongCount {
      get { return (long)ElementCount(); }
    }
    private BigInteger ElementCount() {
      // This is inefficient
      var c = occurrencesOfNull;
      foreach (var item in dict) {
        c += item.Value;
      }
      return c;
    }

    public IEnumerable<T> Elements {
      get {
        for (var i = BigInteger.Zero; i < occurrencesOfNull; i++) {
          yield return default(T);
        }
        foreach (var item in dict) {
          for (var i = BigInteger.Zero; i < item.Value; i++) {
            yield return item.Key;
          }
        }
      }
    }

    public IEnumerable<T> UniqueElements {
      get {
        if (!occurrencesOfNull.IsZero) {
          yield return default(T);
        }
        foreach (var key in dict.Keys) {
          if (dict[key] != 0) {
            yield return key;
          }
        }
      }
    }
  }

  public interface IMap<out U, out V> {
    int Count { get; }
    long LongCount { get; }
    ISet<U> Keys { get; }
    ISet<V> Values { get; }
    IEnumerable<IPair<U, V>> ItemEnumerable { get; }
    bool Contains<G>(G t);
    /// <summary>
    /// Returns "true" iff "this is IMap<object, object>" and "this" equals "other".
    /// </summary>
    bool EqualsObjObj(IMap<object, object> other);
    IMap<UU, VV> DowncastClone<UU, VV>(Func<U, UU> keyConverter, Func<V, VV> valueConverter);
  }

  public class Map<U, V> : IMap<U, V> {
    readonly ImmutableDictionary<U, V> dict;
    readonly bool hasNullKey;  // true when "null" is a key of the Map
    readonly V nullValue;  // if "hasNullKey", the value that "null" maps to

    private Map(ImmutableDictionary<U, V>.Builder d, bool hasNullKey, V nullValue) {
      dict = d.ToImmutable();
      this.hasNullKey = hasNullKey;
      this.nullValue = nullValue;
    }
    public static readonly Map<U, V> Empty = new Map<U, V>(ImmutableDictionary<U, V>.Empty.ToBuilder(), false, default(V));

    private Map(ImmutableDictionary<U, V> d, bool hasNullKey, V nullValue) {
      dict = d;
      this.hasNullKey = hasNullKey;
      this.nullValue = nullValue;
    }

    private static readonly TypeDescriptor<IMap<U, V>> _TYPE = new Dafny.TypeDescriptor<IMap<U, V>>(Empty);
    public static TypeDescriptor<IMap<U, V>> _TypeDescriptor() {
      return _TYPE;
    }

    public static Map<U, V> FromElements(params IPair<U, V>[] values) {
      var d = ImmutableDictionary<U, V>.Empty.ToBuilder();
      var hasNullKey = false;
      var nullValue = default(V);
      foreach (var p in values) {
        if (p.Car == null) {
          hasNullKey = true;
          nullValue = p.Cdr;
        } else {
          d[p.Car] = p.Cdr;
        }
      }
      return new Map<U, V>(d, hasNullKey, nullValue);
    }
    public static Map<U, V> FromCollection(IEnumerable<IPair<U, V>> values) {
      var d = ImmutableDictionary<U, V>.Empty.ToBuilder();
      var hasNullKey = false;
      var nullValue = default(V);
      foreach (var p in values) {
        if (p.Car == null) {
          hasNullKey = true;
          nullValue = p.Cdr;
        } else {
          d[p.Car] = p.Cdr;
        }
      }
      return new Map<U, V>(d, hasNullKey, nullValue);
    }
    public static Map<U, V> FromIMap(IMap<U, V> m) {
      return m as Map<U, V> ?? FromCollection(m.ItemEnumerable);
    }
    public IMap<UU, VV> DowncastClone<UU, VV>(Func<U, UU> keyConverter, Func<V, VV> valueConverter) {
      if (this is IMap<UU, VV> th) {
        return th;
      } else {
        var d = ImmutableDictionary<UU, VV>.Empty.ToBuilder();
        foreach (var item in this.dict) {
          var k = keyConverter(item.Key);
          var v = valueConverter(item.Value);
          d.Add(k, v);
        }
        return new Map<UU, VV>(d, this.hasNullKey, (VV)(object)this.nullValue);
      }
    }
    public int Count {
      get { return dict.Count + (hasNullKey ? 1 : 0); }
    }
    public long LongCount {
      get { return dict.Count + (hasNullKey ? 1 : 0); }
    }

    public bool Equals(IMap<U, V> other) {
      if (ReferenceEquals(this, other)) {
        return true;
      }

      if (other == null || LongCount != other.LongCount) {
        return false;
      }

      if (hasNullKey) {
        if (!other.Contains(default(U)) || !object.Equals(nullValue, Select(other, default(U)))) {
          return false;
        }
      }

      foreach (var item in dict) {
        if (!other.Contains(item.Key) || !object.Equals(item.Value, Select(other, item.Key))) {
          return false;
        }
      }
      return true;
    }
    public bool EqualsObjObj(IMap<object, object> other) {
      if (ReferenceEquals(this, other)) {
        return true;
      }
      if (!(this is IMap<object, object>) || other == null || LongCount != other.LongCount) {
        return false;
      }
      var oth = Map<object, object>.FromIMap(other);
      if (hasNullKey) {
        if (!oth.Contains(default(U)) || !object.Equals(nullValue, Map<object, object>.Select(oth, default(U)))) {
          return false;
        }
      }
      foreach (var item in dict) {
        if (!other.Contains(item.Key) || !object.Equals(item.Value, Map<object, object>.Select(oth, item.Key))) {
          return false;
        }
      }
      return true;
    }
    public override bool Equals(object other) {
      // See comment in Set.Equals
      var m = other as IMap<U, V>;
      if (m != null) {
        return Equals(m);
      }
      var imapoo = other as IMap<object, object>;
      if (imapoo != null) {
        return EqualsObjObj(imapoo);
      } else {
        return false;
      }
    }

    public override int GetHashCode() {
      var hashCode = 1;
      if (hasNullKey) {
        var key = Dafny.Helpers.GetHashCode(default(U));
        key = (key << 3) | (key >> 29) ^ Dafny.Helpers.GetHashCode(nullValue);
        hashCode = hashCode * (key + 3);
      }
      foreach (var kv in dict) {
        var key = Dafny.Helpers.GetHashCode(kv.Key);
        key = (key << 3) | (key >> 29) ^ Dafny.Helpers.GetHashCode(kv.Value);
        hashCode = hashCode * (key + 3);
      }
      return hashCode;
    }
    public override string ToString() {
      var s = "map[";
      var sep = "";
      if (hasNullKey) {
        s += sep + Dafny.Helpers.ToString(default(U)) + " := " + Dafny.Helpers.ToString(nullValue);
        sep = ", ";
      }
      foreach (var kv in dict) {
        s += sep + Dafny.Helpers.ToString(kv.Key) + " := " + Dafny.Helpers.ToString(kv.Value);
        sep = ", ";
      }
      return s + "]";
    }
    public bool Contains<G>(G u) {
      return u == null ? hasNullKey : u is U && dict.ContainsKey((U)(object)u);
    }
    public static V Select(IMap<U, V> th, U index) {
      // the following will throw an exception if "index" in not a key of the map
      var m = FromIMap(th);
      return index == null && m.hasNullKey ? m.nullValue : m.dict[index];
    }
    public static IMap<U, V> Update(IMap<U, V> th, U index, V val) {
      var m = FromIMap(th);
      var d = m.dict.ToBuilder();
      if (index == null) {
        return new Map<U, V>(d, true, val);
      } else {
        d[index] = val;
        return new Map<U, V>(d, m.hasNullKey, m.nullValue);
      }
    }

    public static IMap<U, V> Merge(IMap<U, V> th, IMap<U, V> other) {
      var a = FromIMap(th);
      var b = FromIMap(other);
      ImmutableDictionary<U, V> d = a.dict.SetItems(b.dict);
      return new Map<U, V>(d, a.hasNullKey || b.hasNullKey, b.hasNullKey ? b.nullValue : a.nullValue);
    }

    public static IMap<U, V> Subtract(IMap<U, V> th, ISet<U> keys) {
      var a = FromIMap(th);
      ImmutableDictionary<U, V> d = a.dict.RemoveRange(keys.Elements);
      return new Map<U, V>(d, a.hasNullKey && !keys.Contains<object>(null), a.nullValue);
    }

    public ISet<U> Keys {
      get {
        if (hasNullKey) {
          return Dafny.Set<U>.FromCollectionPlusOne(dict.Keys, default(U));
        } else {
          return Dafny.Set<U>.FromCollection(dict.Keys);
        }
      }
    }
    public ISet<V> Values {
      get {
        if (hasNullKey) {
          return Dafny.Set<V>.FromCollectionPlusOne(dict.Values, nullValue);
        } else {
          return Dafny.Set<V>.FromCollection(dict.Values);
        }
      }
    }

    public IEnumerable<IPair<U, V>> ItemEnumerable {
      get {
        if (hasNullKey) {
          yield return new Pair<U, V>(default(U), nullValue);
        }
        foreach (KeyValuePair<U, V> kvp in dict) {
          yield return new Pair<U, V>(kvp.Key, kvp.Value);
        }
      }
    }

    public static ISet<_System._ITuple2<U, V>> Items(IMap<U, V> m) {
      var result = new HashSet<_System._ITuple2<U, V>>();
      foreach (var item in m.ItemEnumerable) {
        result.Add(_System.Tuple2<U, V>.create(item.Car, item.Cdr));
      }
      return Dafny.Set<_System._ITuple2<U, V>>.FromCollection(result);
    }
  }

  public interface ISequence<out T> : IEnumerable<T> {
    long LongCount { get; }
    int Count { get; }
    [Obsolete("Use CloneAsArray() instead of Elements (both perform a copy).")]
    T[] Elements { get; }
    T[] CloneAsArray();
    IEnumerable<T> UniqueElements { get; }
    T Select(ulong index);
    T Select(long index);
    T Select(uint index);
    T Select(int index);
    T Select(BigInteger index);
    bool Contains<G>(G g);
    ISequence<T> Take(long m);
    ISequence<T> Take(ulong n);
    ISequence<T> Take(BigInteger n);
    ISequence<T> Drop(long m);
    ISequence<T> Drop(ulong n);
    ISequence<T> Drop(BigInteger n);
    ISequence<T> Subsequence(long lo, long hi);
    ISequence<T> Subsequence(long lo, ulong hi);
    ISequence<T> Subsequence(long lo, BigInteger hi);
    ISequence<T> Subsequence(ulong lo, long hi);
    ISequence<T> Subsequence(ulong lo, ulong hi);
    ISequence<T> Subsequence(ulong lo, BigInteger hi);
    ISequence<T> Subsequence(BigInteger lo, long hi);
    ISequence<T> Subsequence(BigInteger lo, ulong hi);
    ISequence<T> Subsequence(BigInteger lo, BigInteger hi);
    bool EqualsAux(ISequence<object> other);
    ISequence<U> DowncastClone<U>(Func<T, U> converter);
  }

  public abstract class Sequence<T> : ISequence<T> {
    public static readonly ISequence<T> Empty = new ArraySequence<T>(Array.Empty<T>());

    private static readonly TypeDescriptor<ISequence<T>> _TYPE = new Dafny.TypeDescriptor<ISequence<T>>(Empty);
    public static TypeDescriptor<ISequence<T>> _TypeDescriptor() {
      return _TYPE;
    }

    public static ISequence<T> Create(BigInteger length, System.Func<BigInteger, T> init) {
      var len = (int)length;
      var builder = ImmutableArray.CreateBuilder<T>(len);
      for (int i = 0; i < len; i++) {
        builder.Add(init(new BigInteger(i)));
      }
      return new ArraySequence<T>(builder.MoveToImmutable());
    }
    public static ISequence<T> FromArray(T[] values) {
      return new ArraySequence<T>(values);
    }
    public static ISequence<T> FromElements(params T[] values) {
      return new ArraySequence<T>(values);
    }
    public static ISequence<char> FromString(string s) {
      return new ArraySequence<char>(s.ToCharArray());
    }
    public ISequence<U> DowncastClone<U>(Func<T, U> converter) {
      if (this is ISequence<U> th) {
        return th;
      } else {
        var values = new U[this.LongCount];
        for (long i = 0; i < this.LongCount; i++) {
          var val = converter(this.Select(i));
          values[i] = val;
        }
        return new ArraySequence<U>(values);
      }
    }
    public static ISequence<T> Update(ISequence<T> sequence, long index, T t) {
      T[] tmp = sequence.CloneAsArray();
      tmp[index] = t;
      return new ArraySequence<T>(tmp);
    }
    public static ISequence<T> Update(ISequence<T> sequence, ulong index, T t) {
      return Update(sequence, (long)index, t);
    }
    public static ISequence<T> Update(ISequence<T> sequence, BigInteger index, T t) {
      return Update(sequence, (long)index, t);
    }
    public static bool EqualUntil(ISequence<T> left, ISequence<T> right, int n) {
      for (int i = 0; i < n; i++) {
        if (!Equals(left.Select(i), right.Select(i))) {
          return false;
        }
      }
      return true;
    }
    public static bool IsPrefixOf(ISequence<T> left, ISequence<T> right) {
      int n = left.Count;
      return n <= right.Count && EqualUntil(left, right, n);
    }
    public static bool IsProperPrefixOf(ISequence<T> left, ISequence<T> right) {
      int n = left.Count;
      return n < right.Count && EqualUntil(left, right, n);
    }
    public static ISequence<T> Concat(ISequence<T> left, ISequence<T> right) {
      if (left.Count == 0) {
        return right;
      }
      if (right.Count == 0) {
        return left;
      }
      return new ConcatSequence<T>(left, right);
    }
    // Make Count a public abstract instead of LongCount, since the "array size is limited to a total of 4 billion
    // elements, and to a maximum index of 0X7FEFFFFF". Therefore, as a protection, limit this to int32.
    // https://docs.microsoft.com/en-us/dotnet/api/system.array
    public abstract int Count { get; }
    public long LongCount {
      get { return Count; }
    }
    // ImmutableElements cannot be public in the interface since ImmutableArray<T> leads to a
    // "covariant type T occurs in invariant position" error. There do not appear to be interfaces for ImmutableArray<T>
    // that resolve this.
    internal abstract ImmutableArray<T> ImmutableElements { get; }

    public T[] Elements { get { return CloneAsArray(); } }

    public T[] CloneAsArray() {
      return ImmutableElements.ToArray();
    }

    public IEnumerable<T> UniqueElements {
      get {
        return Set<T>.FromCollection(ImmutableElements).Elements;
      }
    }

    public IEnumerator<T> GetEnumerator() {
      foreach (var el in ImmutableElements) {
        yield return el;
      }
    }

    IEnumerator IEnumerable.GetEnumerator() {
      return GetEnumerator();
    }

    public T Select(ulong index) {
      return ImmutableElements[checked((int)index)];
    }
    public T Select(long index) {
      return ImmutableElements[checked((int)index)];
    }
    public T Select(uint index) {
      return ImmutableElements[checked((int)index)];
    }
    public T Select(int index) {
      return ImmutableElements[index];
    }
    public T Select(BigInteger index) {
      return ImmutableElements[(int)index];
    }
    public bool Equals(ISequence<T> other) {
      return ReferenceEquals(this, other) || (Count == other.Count && EqualUntil(this, other, Count));
    }
    public override bool Equals(object other) {
      if (other is ISequence<T>) {
        return Equals((ISequence<T>)other);
      }
      var th = this as ISequence<object>;
      var oth = other as ISequence<object>;
      if (th != null && oth != null) {
        // see explanation in Set.Equals
        return oth.EqualsAux(th);
      } else {
        return false;
      }
    }
    public bool EqualsAux(ISequence<object> other) {
      var s = other as ISequence<T>;
      if (s != null) {
        return Equals(s);
      } else {
        return false;
      }
    }
    public override int GetHashCode() {
      ImmutableArray<T> elmts = ImmutableElements;
      // https://devblogs.microsoft.com/dotnet/please-welcome-immutablearrayt/
      if (elmts.IsDefaultOrEmpty) {
        return 0;
      }

      var hashCode = 0;
      for (var i = 0; i < elmts.Length; i++) {
        hashCode = (hashCode << 3) | (hashCode >> 29) ^ Dafny.Helpers.GetHashCode(elmts[i]);
      }
      return hashCode;
    }
    public override string ToString() {
      if (typeof(T) == typeof(char)) {
        return string.Concat(this);
      } else {
        return "[" + string.Join(", ", ImmutableElements.Select(Dafny.Helpers.ToString)) + "]";
      }
    }

    public bool Contains<G>(G g) {
      if (g == null || g is T) {
        var t = (T)(object)g;
        return ImmutableElements.Contains(t);
      }
      return false;
    }
    public ISequence<T> Take(long m) {
      return Subsequence(0, m);
    }
    public ISequence<T> Take(ulong n) {
      return Take((long)n);
    }
    public ISequence<T> Take(BigInteger n) {
      return Take((long)n);
    }
    public ISequence<T> Drop(long m) {
      return Subsequence(m, Count);
    }
    public ISequence<T> Drop(ulong n) {
      return Drop((long)n);
    }
    public ISequence<T> Drop(BigInteger n) {
      return Drop((long)n);
    }
    public ISequence<T> Subsequence(long lo, long hi) {
      if (lo == 0 && hi == Count) {
        return this;
      }
      int startingIndex = checked((int)lo);
      var length = checked((int)hi) - startingIndex;
      return new ArraySequence<T>(ImmutableArray.Create<T>(ImmutableElements, startingIndex, length));
    }
    public ISequence<T> Subsequence(long lo, ulong hi) {
      return Subsequence(lo, (long)hi);
    }
    public ISequence<T> Subsequence(long lo, BigInteger hi) {
      return Subsequence(lo, (long)hi);
    }
    public ISequence<T> Subsequence(ulong lo, long hi) {
      return Subsequence((long)lo, hi);
    }
    public ISequence<T> Subsequence(ulong lo, ulong hi) {
      return Subsequence((long)lo, (long)hi);
    }
    public ISequence<T> Subsequence(ulong lo, BigInteger hi) {
      return Subsequence((long)lo, (long)hi);
    }
    public ISequence<T> Subsequence(BigInteger lo, long hi) {
      return Subsequence((long)lo, hi);
    }
    public ISequence<T> Subsequence(BigInteger lo, ulong hi) {
      return Subsequence((long)lo, (long)hi);
    }
    public ISequence<T> Subsequence(BigInteger lo, BigInteger hi) {
      return Subsequence((long)lo, (long)hi);
    }
  }

  internal class ArraySequence<T> : Sequence<T> {
    private readonly ImmutableArray<T> elmts;

    internal ArraySequence(ImmutableArray<T> ee) {
      elmts = ee;
    }
    internal ArraySequence(T[] ee) {
      elmts = ImmutableArray.Create<T>(ee);
    }

    internal override ImmutableArray<T> ImmutableElements {
      get {
        return elmts;
      }
    }

    public override int Count {
      get {
        return elmts.Length;
      }
    }
  }

  internal class ConcatSequence<T> : Sequence<T> {
    // INVARIANT: Either left != null, right != null, and elmts's underlying array == null or
    // left == null, right == null, and elmts's underlying array != null
    private volatile ISequence<T> left, right;
    private ImmutableArray<T> elmts;
    private readonly int count;

    internal ConcatSequence(ISequence<T> left, ISequence<T> right) {
      this.left = left;
      this.right = right;
      this.count = left.Count + right.Count;
    }

    internal override ImmutableArray<T> ImmutableElements {
      get {
        // IsDefault returns true if the underlying array is a null reference
        // https://devblogs.microsoft.com/dotnet/please-welcome-immutablearrayt/
        if (elmts.IsDefault) {
          elmts = ComputeElements();
          // We don't need the original sequences anymore; let them be
          // garbage-collected
          left = null;
          right = null;
        }
        return elmts;
      }
    }

    public override int Count {
      get {
        return count;
      }
    }

    private ImmutableArray<T> ComputeElements() {
      // Traverse the tree formed by all descendants which are ConcatSequences
      var ansBuilder = ImmutableArray.CreateBuilder<T>(count);
      var toVisit = new Stack<ISequence<T>>();
      var (leftBuffer, rightBuffer) = (left, right);
      if (left == null || right == null) {
        // elmts can't be .IsDefault while either left, or right are null
        return elmts;
      }
      toVisit.Push(rightBuffer);
      toVisit.Push(leftBuffer);

      while (toVisit.Count != 0) {
        var seq = toVisit.Pop();
        if (seq is ConcatSequence<T> cs && cs.elmts.IsDefault) {
          (leftBuffer, rightBuffer) = (cs.left, cs.right);
          if (cs.left == null || cs.right == null) {
            // !cs.elmts.IsDefault, due to concurrent enumeration
            toVisit.Push(cs);
          } else {
            toVisit.Push(rightBuffer);
            toVisit.Push(leftBuffer);
          }
        } else {
          if (seq is Sequence<T> sq) {
            ansBuilder.AddRange(sq.ImmutableElements); // Optimized path for ImmutableArray
          } else {
            ansBuilder.AddRange(seq); // Slower path using IEnumerable
          }
        }
      }
      return ansBuilder.MoveToImmutable();
    }
  }

  public interface IPair<out A, out B> {
    A Car { get; }
    B Cdr { get; }
  }

  public class Pair<A, B> : IPair<A, B> {
    private A car;
    private B cdr;
    public A Car { get { return car; } }
    public B Cdr { get { return cdr; } }
    public Pair(A a, B b) {
      this.car = a;
      this.cdr = b;
    }
  }

  public class TypeDescriptor<T> {
    private readonly T initValue;
    public TypeDescriptor(T initValue) {
      this.initValue = initValue;
    }
    public T Default() {
      return initValue;
    }
  }

  public partial class Helpers {
    public static int GetHashCode<G>(G g) {
      return g == null ? 1001 : g.GetHashCode();
    }

    public static int ToIntChecked(BigInteger i, string msg) {
      if (i > Int32.MaxValue || i < Int32.MinValue) {
        if (msg == null) {
          msg = "value out of range for a 32-bit int";
        }

        throw new HaltException(msg + ": " + i);
      }
      return (int)i;
    }
    public static int ToIntChecked(long i, string msg) {
      if (i > Int32.MaxValue || i < Int32.MinValue) {
        if (msg == null) {
          msg = "value out of range for a 32-bit int";
        }

        throw new HaltException(msg + ": " + i);
      }
      return (int)i;
    }
    public static int ToIntChecked(int i, string msg) {
      return i;
    }

    public static string ToString<G>(G g) {
      if (g == null) {
        return "null";
      } else if (g is bool) {
        return (bool)(object)g ? "true" : "false";  // capitalize boolean literals like in Dafny
      } else {
        return g.ToString();
      }
    }
    public static void Print<G>(G g) {
      System.Console.Write(ToString(g));
    }

    public static readonly TypeDescriptor<bool> BOOL = new TypeDescriptor<bool>(false);
    public static readonly TypeDescriptor<char> CHAR = new TypeDescriptor<char>('D');  // See CharType.DefaultValue in Dafny source code
    public static readonly TypeDescriptor<BigInteger> INT = new TypeDescriptor<BigInteger>(BigInteger.Zero);
    public static readonly TypeDescriptor<BigRational> REAL = new TypeDescriptor<BigRational>(BigRational.ZERO);
    public static readonly TypeDescriptor<byte> UINT8 = new TypeDescriptor<byte>(0);
    public static readonly TypeDescriptor<ushort> UINT16 = new TypeDescriptor<ushort>(0);
    public static readonly TypeDescriptor<uint> UINT32 = new TypeDescriptor<uint>(0);
    public static readonly TypeDescriptor<ulong> UINT64 = new TypeDescriptor<ulong>(0);

    public static TypeDescriptor<T> NULL<T>() where T : class {
      return new TypeDescriptor<T>(null);
    }

    public static TypeDescriptor<A[]> ARRAY<A>() {
      return new TypeDescriptor<A[]>(new A[0]);
    }

    public static bool Quantifier<T>(IEnumerable<T> vals, bool frall, System.Predicate<T> pred) {
      foreach (var u in vals) {
        if (pred(u) != frall) { return !frall; }
      }
      return frall;
    }
    // Enumerating other collections
    public static IEnumerable<bool> AllBooleans() {
      yield return false;
      yield return true;
    }
    public static IEnumerable<char> AllChars() {
      for (int i = 0; i < 0x10000; i++) {
        yield return (char)i;
      }
    }
    public static IEnumerable<BigInteger> AllIntegers() {
      yield return new BigInteger(0);
      for (var j = new BigInteger(1); ; j++) {
        yield return j;
        yield return -j;
      }
    }
    public static IEnumerable<BigInteger> IntegerRange(Nullable<BigInteger> lo, Nullable<BigInteger> hi) {
      if (lo == null) {
        for (var j = (BigInteger)hi; true;) {
          j--;
          yield return j;
        }
      } else if (hi == null) {
        for (var j = (BigInteger)lo; true; j++) {
          yield return j;
        }
      } else {
        for (var j = (BigInteger)lo; j < hi; j++) {
          yield return j;
        }
      }
    }
    public static IEnumerable<T> SingleValue<T>(T e) {
      yield return e;
    }
    // pre: b != 0
    // post: result == a/b, as defined by Euclidean Division (http://en.wikipedia.org/wiki/Modulo_operation)
    public static sbyte EuclideanDivision_sbyte(sbyte a, sbyte b) {
      return (sbyte)EuclideanDivision_int(a, b);
    }
    public static short EuclideanDivision_short(short a, short b) {
      return (short)EuclideanDivision_int(a, b);
    }
    public static int EuclideanDivision_int(int a, int b) {
      if (0 <= a) {
        if (0 <= b) {
          // +a +b: a/b
          return (int)(((uint)(a)) / ((uint)(b)));
        } else {
          // +a -b: -(a/(-b))
          return -((int)(((uint)(a)) / ((uint)(unchecked(-b)))));
        }
      } else {
        if (0 <= b) {
          // -a +b: -((-a-1)/b) - 1
          return -((int)(((uint)(-(a + 1))) / ((uint)(b)))) - 1;
        } else {
          // -a -b: ((-a-1)/(-b)) + 1
          return ((int)(((uint)(-(a + 1))) / ((uint)(unchecked(-b))))) + 1;
        }
      }
    }
    public static long EuclideanDivision_long(long a, long b) {
      if (0 <= a) {
        if (0 <= b) {
          // +a +b: a/b
          return (long)(((ulong)(a)) / ((ulong)(b)));
        } else {
          // +a -b: -(a/(-b))
          return -((long)(((ulong)(a)) / ((ulong)(unchecked(-b)))));
        }
      } else {
        if (0 <= b) {
          // -a +b: -((-a-1)/b) - 1
          return -((long)(((ulong)(-(a + 1))) / ((ulong)(b)))) - 1;
        } else {
          // -a -b: ((-a-1)/(-b)) + 1
          return ((long)(((ulong)(-(a + 1))) / ((ulong)(unchecked(-b))))) + 1;
        }
      }
    }
    public static BigInteger EuclideanDivision(BigInteger a, BigInteger b) {
      if (0 <= a.Sign) {
        if (0 <= b.Sign) {
          // +a +b: a/b
          return BigInteger.Divide(a, b);
        } else {
          // +a -b: -(a/(-b))
          return BigInteger.Negate(BigInteger.Divide(a, BigInteger.Negate(b)));
        }
      } else {
        if (0 <= b.Sign) {
          // -a +b: -((-a-1)/b) - 1
          return BigInteger.Negate(BigInteger.Divide(BigInteger.Negate(a) - 1, b)) - 1;
        } else {
          // -a -b: ((-a-1)/(-b)) + 1
          return BigInteger.Divide(BigInteger.Negate(a) - 1, BigInteger.Negate(b)) + 1;
        }
      }
    }
    // pre: b != 0
    // post: result == a%b, as defined by Euclidean Division (http://en.wikipedia.org/wiki/Modulo_operation)
    public static sbyte EuclideanModulus_sbyte(sbyte a, sbyte b) {
      return (sbyte)EuclideanModulus_int(a, b);
    }
    public static short EuclideanModulus_short(short a, short b) {
      return (short)EuclideanModulus_int(a, b);
    }
    public static int EuclideanModulus_int(int a, int b) {
      uint bp = (0 <= b) ? (uint)b : (uint)(unchecked(-b));
      if (0 <= a) {
        // +a: a % b'
        return (int)(((uint)a) % bp);
      } else {
        // c = ((-a) % b')
        // -a: b' - c if c > 0
        // -a: 0 if c == 0
        uint c = ((uint)(unchecked(-a))) % bp;
        return (int)(c == 0 ? c : bp - c);
      }
    }
    public static long EuclideanModulus_long(long a, long b) {
      ulong bp = (0 <= b) ? (ulong)b : (ulong)(unchecked(-b));
      if (0 <= a) {
        // +a: a % b'
        return (long)(((ulong)a) % bp);
      } else {
        // c = ((-a) % b')
        // -a: b' - c if c > 0
        // -a: 0 if c == 0
        ulong c = ((ulong)(unchecked(-a))) % bp;
        return (long)(c == 0 ? c : bp - c);
      }
    }
    public static BigInteger EuclideanModulus(BigInteger a, BigInteger b) {
      var bp = BigInteger.Abs(b);
      if (0 <= a.Sign) {
        // +a: a % b'
        return BigInteger.Remainder(a, bp);
      } else {
        // c = ((-a) % b')
        // -a: b' - c if c > 0
        // -a: 0 if c == 0
        var c = BigInteger.Remainder(BigInteger.Negate(a), bp);
        return c.IsZero ? c : BigInteger.Subtract(bp, c);
      }
    }

    public static U CastConverter<T, U>(T t) {
      return (U)(object)t;
    }

    public static Sequence<T> SeqFromArray<T>(T[] array) {
      return new ArraySequence<T>(array);
    }
    // In .NET version 4.5, it is possible to mark a method with "AggressiveInlining", which says to inline the
    // method if possible.  Method "ExpressionSequence" would be a good candidate for it:
    // [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.AggressiveInlining)]
    public static U ExpressionSequence<T, U>(T t, U u) {
      return u;
    }

    public static U Let<T, U>(T t, Func<T, U> f) {
      return f(t);
    }

    public static A Id<A>(A a) {
      return a;
    }

    public static void WithHaltHandling(Action action) {
      try {
        action();
      } catch (HaltException e) {
        Console.WriteLine("[Program halted] " + e.Message);
      }
    }
  }

  public class BigOrdinal {
    public static bool IsLimit(BigInteger ord) {
      return ord == 0;
    }
    public static bool IsSucc(BigInteger ord) {
      return 0 < ord;
    }
    public static BigInteger Offset(BigInteger ord) {
      return ord;
    }
    public static bool IsNat(BigInteger ord) {
      return true;  // at run time, every ORDINAL is a natural number
    }
  }

  public struct BigRational {
    public static readonly BigRational ZERO = new BigRational(0);

    // We need to deal with the special case "num == 0 && den == 0", because
    // that's what C#'s default struct constructor will produce for BigRational. :(
    // To deal with it, we ignore "den" when "num" is 0.
    internal readonly BigInteger num, den;  // invariant 1 <= den || (num == 0 && den == 0)

    public override string ToString() {
      int log10;
      if (num.IsZero || den.IsOne) {
        return string.Format("{0}.0", num);
      } else if (IsPowerOf10(den, out log10)) {
        string sign;
        string digits;
        if (num.Sign < 0) {
          sign = "-"; digits = (-num).ToString();
        } else {
          sign = ""; digits = num.ToString();
        }
        if (log10 < digits.Length) {
          var n = digits.Length - log10;
          return string.Format("{0}{1}.{2}", sign, digits.Substring(0, n), digits.Substring(n));
        } else {
          return string.Format("{0}0.{1}{2}", sign, new string('0', log10 - digits.Length), digits);
        }
      } else {
        return string.Format("({0}.0 / {1}.0)", num, den);
      }
    }
    public bool IsPowerOf10(BigInteger x, out int log10) {
      log10 = 0;
      if (x.IsZero) {
        return false;
      }
      while (true) {  // invariant: x != 0 && x * 10^log10 == old(x)
        if (x.IsOne) {
          return true;
        } else if (x % 10 == 0) {
          log10++;
          x /= 10;
        } else {
          return false;
        }
      }
    }
    public BigRational(int n) {
      num = new BigInteger(n);
      den = BigInteger.One;
    }
    public BigRational(uint n) {
      num = new BigInteger(n);
      den = BigInteger.One;
    }
    public BigRational(long n) {
      num = new BigInteger(n);
      den = BigInteger.One;
    }
    public BigRational(ulong n) {
      num = new BigInteger(n);
      den = BigInteger.One;
    }
    public BigRational(BigInteger n, BigInteger d) {
      // requires 1 <= d
      num = n;
      den = d;
    }
    /// <summary>
    /// Construct an exact rational representation of a double value.
    /// Throw an exception on NaN or infinite values. Does not support
    /// subnormal values, though it would be possible to extend it to.
    /// </summary>
    public BigRational(double n) {
      if (Double.IsNaN(n)) {
        throw new ArgumentException("Can't convert NaN to a rational.");
      }
      if (Double.IsInfinity(n)) {
        throw new ArgumentException(
          "Can't convert +/- infinity to a rational.");
      }

      // Double-specific values
      const int exptBias = 1023;
      const ulong signMask = 0x8000000000000000;
      const ulong exptMask = 0x7FF0000000000000;
      const ulong mantMask = 0x000FFFFFFFFFFFFF;
      const int mantBits = 52;
      ulong bits = BitConverter.ToUInt64(BitConverter.GetBytes(n), 0);

      // Generic conversion
      bool isNeg = (bits & signMask) != 0;
      int expt = ((int)((bits & exptMask) >> mantBits)) - exptBias;
      var mant = (bits & mantMask);

      if (expt == -exptBias && mant != 0) {
        throw new ArgumentException(
          "Can't convert a subnormal value to a rational (yet).");
      }

      var one = BigInteger.One;
      var negFactor = isNeg ? BigInteger.Negate(one) : one;
      var two = new BigInteger(2);
      var exptBI = BigInteger.Pow(two, Math.Abs(expt));
      var twoToMantBits = BigInteger.Pow(two, mantBits);
      var mantNum = negFactor * (twoToMantBits + new BigInteger(mant));
      if (expt == -exptBias && mant == 0) {
        num = den = 0;
      } else if (expt < 0) {
        num = mantNum;
        den = twoToMantBits * exptBI;
      } else {
        num = exptBI * mantNum;
        den = twoToMantBits;
      }
    }
    public BigInteger ToBigInteger() {
      if (num.IsZero || den.IsOne) {
        return num;
      } else if (0 < num.Sign) {
        return num / den;
      } else {
        return (num - den + 1) / den;
      }
    }
    /// <summary>
    /// Returns values such that aa/dd == a and bb/dd == b.
    /// </summary>
    private static void Normalize(BigRational a, BigRational b, out BigInteger aa, out BigInteger bb, out BigInteger dd) {
      if (a.num.IsZero) {
        aa = a.num;
        bb = b.num;
        dd = b.den;
      } else if (b.num.IsZero) {
        aa = a.num;
        dd = a.den;
        bb = b.num;
      } else {
        var gcd = BigInteger.GreatestCommonDivisor(a.den, b.den);
        var xx = a.den / gcd;
        var yy = b.den / gcd;
        // We now have a == a.num / (xx * gcd) and b == b.num / (yy * gcd).
        aa = a.num * yy;
        bb = b.num * xx;
        dd = a.den * yy;
      }
    }
    public int CompareTo(BigRational that) {
      // simple things first
      int asign = this.num.Sign;
      int bsign = that.num.Sign;
      if (asign < 0 && 0 <= bsign) {
        return -1;
      } else if (asign <= 0 && 0 < bsign) {
        return -1;
      } else if (bsign < 0 && 0 <= asign) {
        return 1;
      } else if (bsign <= 0 && 0 < asign) {
        return 1;
      }
      BigInteger aa, bb, dd;
      Normalize(this, that, out aa, out bb, out dd);
      return aa.CompareTo(bb);
    }
    public int Sign {
      get {
        return num.Sign;
      }
    }
    public override int GetHashCode() {
      return num.GetHashCode() + 29 * den.GetHashCode();
    }
    public override bool Equals(object obj) {
      if (obj is BigRational) {
        return this == (BigRational)obj;
      } else {
        return false;
      }
    }
    public static bool operator ==(BigRational a, BigRational b) {
      return a.CompareTo(b) == 0;
    }
    public static bool operator !=(BigRational a, BigRational b) {
      return a.CompareTo(b) != 0;
    }
    public static bool operator >(BigRational a, BigRational b) {
      return a.CompareTo(b) > 0;
    }
    public static bool operator >=(BigRational a, BigRational b) {
      return a.CompareTo(b) >= 0;
    }
    public static bool operator <(BigRational a, BigRational b) {
      return a.CompareTo(b) < 0;
    }
    public static bool operator <=(BigRational a, BigRational b) {
      return a.CompareTo(b) <= 0;
    }
    public static BigRational operator +(BigRational a, BigRational b) {
      BigInteger aa, bb, dd;
      Normalize(a, b, out aa, out bb, out dd);
      return new BigRational(aa + bb, dd);
    }
    public static BigRational operator -(BigRational a, BigRational b) {
      BigInteger aa, bb, dd;
      Normalize(a, b, out aa, out bb, out dd);
      return new BigRational(aa - bb, dd);
    }
    public static BigRational operator -(BigRational a) {
      return new BigRational(-a.num, a.den);
    }
    public static BigRational operator *(BigRational a, BigRational b) {
      return new BigRational(a.num * b.num, a.den * b.den);
    }
    public static BigRational operator /(BigRational a, BigRational b) {
      // Compute the reciprocal of b
      BigRational bReciprocal;
      if (0 < b.num.Sign) {
        bReciprocal = new BigRational(b.den, b.num);
      } else {
        // this is the case b.num < 0
        bReciprocal = new BigRational(-b.den, -b.num);
      }
      return a * bReciprocal;
    }
  }

  public class HaltException : Exception {
    public HaltException(object message) : base(message.ToString()) {
    }
  }
}

namespace @_System {

  public interface _ITuple0 {
    _ITuple0 DowncastClone();
  }
  public class Tuple0 : _ITuple0 {
    public Tuple0() {
    }
    public _ITuple0 DowncastClone() {
      if (this is _ITuple0 dt) { return dt; }
      return new Tuple0();
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple0;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int)hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += ")";
      return s;
    }
    private static readonly _ITuple0 theDefault = create();
    public static _ITuple0 Default() {
      return theDefault;
    }
    public static Dafny.TypeDescriptor<_System._ITuple0> _TypeDescriptor() {
      return new Dafny.TypeDescriptor<_System._ITuple0>(_System.Tuple0.Default());
    }
    public static _ITuple0 create() {
      return new Tuple0();
    }
  }

  public interface _ITuple1<out T1> {
    T1 dtor__0 { get; }
    _ITuple1<__T1> DowncastClone<__T1>(Func<T1, __T1> converter0);
  }
  public class Tuple1<T1> : _ITuple1<T1> {
    public readonly T1 _0;
    public Tuple1(T1 _0) {
      this._0 = _0;
    }
    public _ITuple1<__T1> DowncastClone<__T1>(Func<T1, __T1> converter0) {
      if (this is _ITuple1<__T1> dt) { return dt; }
      return new Tuple1<__T1>(converter0(_0));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple1<T1>;
      return oth != null && object.Equals(this._0, oth._0);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._0));
      return (int)hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this._0);
      s += ")";
      return s;
    }
    public static _ITuple1<T1> Default(T1 _default_T1) {
      return create(_default_T1);
    }
    public static Dafny.TypeDescriptor<_System._ITuple1<T1>> _TypeDescriptor(Dafny.TypeDescriptor<T1> _td_T1) {
      return new Dafny.TypeDescriptor<_System._ITuple1<T1>>(_System.Tuple1<T1>.Default(_td_T1.Default()));
    }
    public static _ITuple1<T1> create(T1 _0) {
      return new Tuple1<T1>(_0);
    }
    public T1 dtor__0 {
      get {
        return this._0;
      }
    }
  }

  public interface _ITuple2<out T0, out T1> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
  }

  public class Tuple2<T0, T1> : _ITuple2<T0, T1> {
    public readonly T0 _0;
    public readonly T1 _1;
    public Tuple2(T0 _0, T1 _1) {
      this._0 = _0;
      this._1 = _1;
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple2<T0, T1>;
      return oth != null && object.Equals(this._0, oth._0) && object.Equals(this._1, oth._1);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._1));
      return (int)hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this._0);
      s += ", ";
      s += Dafny.Helpers.ToString(this._1);
      s += ")";
      return s;
    }
    public static _ITuple2<T0, T1> Default(T0 _default_T0, T1 _default_T1) {
      return create(_default_T0, _default_T1);
    }
    public static Dafny.TypeDescriptor<_System._ITuple2<T0, T1>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1) {
      return new Dafny.TypeDescriptor<_System._ITuple2<T0, T1>>(_System.Tuple2<T0, T1>.Default(_td_T0.Default(), _td_T1.Default()));
    }
    public static _ITuple2<T0, T1> create(T0 _0, T1 _1) {
      return new Tuple2<T0, T1>(_0, _1);
    }
    public T0 dtor__0 {
      get {
        return this._0;
      }
    }
    public T1 dtor__1 {
      get {
        return this._1;
      }
    }
  }

  public interface _ITuple3<out T0, out T1, out T2> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    _ITuple3<__T0, __T1, __T2> DowncastClone<__T0, __T1, __T2>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2);
  }
  public class Tuple3<T0, T1, T2> : _ITuple3<T0, T1, T2> {
    public readonly T0 _0;
    public readonly T1 _1;
    public readonly T2 _2;
    public Tuple3(T0 _0, T1 _1, T2 _2) {
      this._0 = _0;
      this._1 = _1;
      this._2 = _2;
    }
    public _ITuple3<__T0, __T1, __T2> DowncastClone<__T0, __T1, __T2>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2) {
      if (this is _ITuple3<__T0, __T1, __T2> dt) { return dt; }
      return new Tuple3<__T0, __T1, __T2>(converter0(_0), converter1(_1), converter2(_2));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple3<T0, T1, T2>;
      return oth != null && object.Equals(this._0, oth._0) && object.Equals(this._1, oth._1) && object.Equals(this._2, oth._2);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._2));
      return (int)hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this._0);
      s += ", ";
      s += Dafny.Helpers.ToString(this._1);
      s += ", ";
      s += Dafny.Helpers.ToString(this._2);
      s += ")";
      return s;
    }
    public static _ITuple3<T0, T1, T2> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2) {
      return create(_default_T0, _default_T1, _default_T2);
    }
    public static Dafny.TypeDescriptor<_System._ITuple3<T0, T1, T2>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2) {
      return new Dafny.TypeDescriptor<_System._ITuple3<T0, T1, T2>>(_System.Tuple3<T0, T1, T2>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default()));
    }
    public static _ITuple3<T0, T1, T2> create(T0 _0, T1 _1, T2 _2) {
      return new Tuple3<T0, T1, T2>(_0, _1, _2);
    }
    public T0 dtor__0 {
      get {
        return this._0;
      }
    }
    public T1 dtor__1 {
      get {
        return this._1;
      }
    }
    public T2 dtor__2 {
      get {
        return this._2;
      }
    }
  }

  public interface _ITuple4<out T0, out T1, out T2, out T3> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    _ITuple4<__T0, __T1, __T2, __T3> DowncastClone<__T0, __T1, __T2, __T3>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3);
  }
  public class Tuple4<T0, T1, T2, T3> : _ITuple4<T0, T1, T2, T3> {
    public readonly T0 _0;
    public readonly T1 _1;
    public readonly T2 _2;
    public readonly T3 _3;
    public Tuple4(T0 _0, T1 _1, T2 _2, T3 _3) {
      this._0 = _0;
      this._1 = _1;
      this._2 = _2;
      this._3 = _3;
    }
    public _ITuple4<__T0, __T1, __T2, __T3> DowncastClone<__T0, __T1, __T2, __T3>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3) {
      if (this is _ITuple4<__T0, __T1, __T2, __T3> dt) { return dt; }
      return new Tuple4<__T0, __T1, __T2, __T3>(converter0(_0), converter1(_1), converter2(_2), converter3(_3));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple4<T0, T1, T2, T3>;
      return oth != null && object.Equals(this._0, oth._0) && object.Equals(this._1, oth._1) && object.Equals(this._2, oth._2) && object.Equals(this._3, oth._3);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._3));
      return (int)hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this._0);
      s += ", ";
      s += Dafny.Helpers.ToString(this._1);
      s += ", ";
      s += Dafny.Helpers.ToString(this._2);
      s += ", ";
      s += Dafny.Helpers.ToString(this._3);
      s += ")";
      return s;
    }
    public static _ITuple4<T0, T1, T2, T3> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3);
    }
    public static Dafny.TypeDescriptor<_System._ITuple4<T0, T1, T2, T3>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3) {
      return new Dafny.TypeDescriptor<_System._ITuple4<T0, T1, T2, T3>>(_System.Tuple4<T0, T1, T2, T3>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default()));
    }
    public static _ITuple4<T0, T1, T2, T3> create(T0 _0, T1 _1, T2 _2, T3 _3) {
      return new Tuple4<T0, T1, T2, T3>(_0, _1, _2, _3);
    }
    public T0 dtor__0 {
      get {
        return this._0;
      }
    }
    public T1 dtor__1 {
      get {
        return this._1;
      }
    }
    public T2 dtor__2 {
      get {
        return this._2;
      }
    }
    public T3 dtor__3 {
      get {
        return this._3;
      }
    }
  }

  public interface _ITuple5<out T0, out T1, out T2, out T3, out T4> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    _ITuple5<__T0, __T1, __T2, __T3, __T4> DowncastClone<__T0, __T1, __T2, __T3, __T4>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4);
  }
  public class Tuple5<T0, T1, T2, T3, T4> : _ITuple5<T0, T1, T2, T3, T4> {
    public readonly T0 _0;
    public readonly T1 _1;
    public readonly T2 _2;
    public readonly T3 _3;
    public readonly T4 _4;
    public Tuple5(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4) {
      this._0 = _0;
      this._1 = _1;
      this._2 = _2;
      this._3 = _3;
      this._4 = _4;
    }
    public _ITuple5<__T0, __T1, __T2, __T3, __T4> DowncastClone<__T0, __T1, __T2, __T3, __T4>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4) {
      if (this is _ITuple5<__T0, __T1, __T2, __T3, __T4> dt) { return dt; }
      return new Tuple5<__T0, __T1, __T2, __T3, __T4>(converter0(_0), converter1(_1), converter2(_2), converter3(_3), converter4(_4));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple5<T0, T1, T2, T3, T4>;
      return oth != null && object.Equals(this._0, oth._0) && object.Equals(this._1, oth._1) && object.Equals(this._2, oth._2) && object.Equals(this._3, oth._3) && object.Equals(this._4, oth._4);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._4));
      return (int)hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this._0);
      s += ", ";
      s += Dafny.Helpers.ToString(this._1);
      s += ", ";
      s += Dafny.Helpers.ToString(this._2);
      s += ", ";
      s += Dafny.Helpers.ToString(this._3);
      s += ", ";
      s += Dafny.Helpers.ToString(this._4);
      s += ")";
      return s;
    }
    public static _ITuple5<T0, T1, T2, T3, T4> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4);
    }
    public static Dafny.TypeDescriptor<_System._ITuple5<T0, T1, T2, T3, T4>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4) {
      return new Dafny.TypeDescriptor<_System._ITuple5<T0, T1, T2, T3, T4>>(_System.Tuple5<T0, T1, T2, T3, T4>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default()));
    }
    public static _ITuple5<T0, T1, T2, T3, T4> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4) {
      return new Tuple5<T0, T1, T2, T3, T4>(_0, _1, _2, _3, _4);
    }
    public T0 dtor__0 {
      get {
        return this._0;
      }
    }
    public T1 dtor__1 {
      get {
        return this._1;
      }
    }
    public T2 dtor__2 {
      get {
        return this._2;
      }
    }
    public T3 dtor__3 {
      get {
        return this._3;
      }
    }
    public T4 dtor__4 {
      get {
        return this._4;
      }
    }
  }

  public interface _ITuple6<out T0, out T1, out T2, out T3, out T4, out T5> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    _ITuple6<__T0, __T1, __T2, __T3, __T4, __T5> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5);
  }
  public class Tuple6<T0, T1, T2, T3, T4, T5> : _ITuple6<T0, T1, T2, T3, T4, T5> {
    public readonly T0 _0;
    public readonly T1 _1;
    public readonly T2 _2;
    public readonly T3 _3;
    public readonly T4 _4;
    public readonly T5 _5;
    public Tuple6(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5) {
      this._0 = _0;
      this._1 = _1;
      this._2 = _2;
      this._3 = _3;
      this._4 = _4;
      this._5 = _5;
    }
    public _ITuple6<__T0, __T1, __T2, __T3, __T4, __T5> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5) {
      if (this is _ITuple6<__T0, __T1, __T2, __T3, __T4, __T5> dt) { return dt; }
      return new Tuple6<__T0, __T1, __T2, __T3, __T4, __T5>(converter0(_0), converter1(_1), converter2(_2), converter3(_3), converter4(_4), converter5(_5));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple6<T0, T1, T2, T3, T4, T5>;
      return oth != null && object.Equals(this._0, oth._0) && object.Equals(this._1, oth._1) && object.Equals(this._2, oth._2) && object.Equals(this._3, oth._3) && object.Equals(this._4, oth._4) && object.Equals(this._5, oth._5);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._5));
      return (int)hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this._0);
      s += ", ";
      s += Dafny.Helpers.ToString(this._1);
      s += ", ";
      s += Dafny.Helpers.ToString(this._2);
      s += ", ";
      s += Dafny.Helpers.ToString(this._3);
      s += ", ";
      s += Dafny.Helpers.ToString(this._4);
      s += ", ";
      s += Dafny.Helpers.ToString(this._5);
      s += ")";
      return s;
    }
    public static _ITuple6<T0, T1, T2, T3, T4, T5> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5);
    }
    public static Dafny.TypeDescriptor<_System._ITuple6<T0, T1, T2, T3, T4, T5>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5) {
      return new Dafny.TypeDescriptor<_System._ITuple6<T0, T1, T2, T3, T4, T5>>(_System.Tuple6<T0, T1, T2, T3, T4, T5>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default()));
    }
    public static _ITuple6<T0, T1, T2, T3, T4, T5> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5) {
      return new Tuple6<T0, T1, T2, T3, T4, T5>(_0, _1, _2, _3, _4, _5);
    }
    public T0 dtor__0 {
      get {
        return this._0;
      }
    }
    public T1 dtor__1 {
      get {
        return this._1;
      }
    }
    public T2 dtor__2 {
      get {
        return this._2;
      }
    }
    public T3 dtor__3 {
      get {
        return this._3;
      }
    }
    public T4 dtor__4 {
      get {
        return this._4;
      }
    }
    public T5 dtor__5 {
      get {
        return this._5;
      }
    }
  }

  public interface _ITuple7<out T0, out T1, out T2, out T3, out T4, out T5, out T6> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    _ITuple7<__T0, __T1, __T2, __T3, __T4, __T5, __T6> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6);
  }
  public class Tuple7<T0, T1, T2, T3, T4, T5, T6> : _ITuple7<T0, T1, T2, T3, T4, T5, T6> {
    public readonly T0 _0;
    public readonly T1 _1;
    public readonly T2 _2;
    public readonly T3 _3;
    public readonly T4 _4;
    public readonly T5 _5;
    public readonly T6 _6;
    public Tuple7(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6) {
      this._0 = _0;
      this._1 = _1;
      this._2 = _2;
      this._3 = _3;
      this._4 = _4;
      this._5 = _5;
      this._6 = _6;
    }
    public _ITuple7<__T0, __T1, __T2, __T3, __T4, __T5, __T6> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6) {
      if (this is _ITuple7<__T0, __T1, __T2, __T3, __T4, __T5, __T6> dt) { return dt; }
      return new Tuple7<__T0, __T1, __T2, __T3, __T4, __T5, __T6>(converter0(_0), converter1(_1), converter2(_2), converter3(_3), converter4(_4), converter5(_5), converter6(_6));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple7<T0, T1, T2, T3, T4, T5, T6>;
      return oth != null && object.Equals(this._0, oth._0) && object.Equals(this._1, oth._1) && object.Equals(this._2, oth._2) && object.Equals(this._3, oth._3) && object.Equals(this._4, oth._4) && object.Equals(this._5, oth._5) && object.Equals(this._6, oth._6);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._6));
      return (int)hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this._0);
      s += ", ";
      s += Dafny.Helpers.ToString(this._1);
      s += ", ";
      s += Dafny.Helpers.ToString(this._2);
      s += ", ";
      s += Dafny.Helpers.ToString(this._3);
      s += ", ";
      s += Dafny.Helpers.ToString(this._4);
      s += ", ";
      s += Dafny.Helpers.ToString(this._5);
      s += ", ";
      s += Dafny.Helpers.ToString(this._6);
      s += ")";
      return s;
    }
    public static _ITuple7<T0, T1, T2, T3, T4, T5, T6> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6);
    }
    public static Dafny.TypeDescriptor<_System._ITuple7<T0, T1, T2, T3, T4, T5, T6>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6) {
      return new Dafny.TypeDescriptor<_System._ITuple7<T0, T1, T2, T3, T4, T5, T6>>(_System.Tuple7<T0, T1, T2, T3, T4, T5, T6>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default()));
    }
    public static _ITuple7<T0, T1, T2, T3, T4, T5, T6> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6) {
      return new Tuple7<T0, T1, T2, T3, T4, T5, T6>(_0, _1, _2, _3, _4, _5, _6);
    }
    public T0 dtor__0 {
      get {
        return this._0;
      }
    }
    public T1 dtor__1 {
      get {
        return this._1;
      }
    }
    public T2 dtor__2 {
      get {
        return this._2;
      }
    }
    public T3 dtor__3 {
      get {
        return this._3;
      }
    }
    public T4 dtor__4 {
      get {
        return this._4;
      }
    }
    public T5 dtor__5 {
      get {
        return this._5;
      }
    }
    public T6 dtor__6 {
      get {
        return this._6;
      }
    }
  }

  public interface _ITuple8<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    _ITuple8<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7);
  }
  public class Tuple8<T0, T1, T2, T3, T4, T5, T6, T7> : _ITuple8<T0, T1, T2, T3, T4, T5, T6, T7> {
    public readonly T0 _0;
    public readonly T1 _1;
    public readonly T2 _2;
    public readonly T3 _3;
    public readonly T4 _4;
    public readonly T5 _5;
    public readonly T6 _6;
    public readonly T7 _7;
    public Tuple8(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7) {
      this._0 = _0;
      this._1 = _1;
      this._2 = _2;
      this._3 = _3;
      this._4 = _4;
      this._5 = _5;
      this._6 = _6;
      this._7 = _7;
    }
    public _ITuple8<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7) {
      if (this is _ITuple8<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7> dt) { return dt; }
      return new Tuple8<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7>(converter0(_0), converter1(_1), converter2(_2), converter3(_3), converter4(_4), converter5(_5), converter6(_6), converter7(_7));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple8<T0, T1, T2, T3, T4, T5, T6, T7>;
      return oth != null && object.Equals(this._0, oth._0) && object.Equals(this._1, oth._1) && object.Equals(this._2, oth._2) && object.Equals(this._3, oth._3) && object.Equals(this._4, oth._4) && object.Equals(this._5, oth._5) && object.Equals(this._6, oth._6) && object.Equals(this._7, oth._7);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._7));
      return (int)hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this._0);
      s += ", ";
      s += Dafny.Helpers.ToString(this._1);
      s += ", ";
      s += Dafny.Helpers.ToString(this._2);
      s += ", ";
      s += Dafny.Helpers.ToString(this._3);
      s += ", ";
      s += Dafny.Helpers.ToString(this._4);
      s += ", ";
      s += Dafny.Helpers.ToString(this._5);
      s += ", ";
      s += Dafny.Helpers.ToString(this._6);
      s += ", ";
      s += Dafny.Helpers.ToString(this._7);
      s += ")";
      return s;
    }
    public static _ITuple8<T0, T1, T2, T3, T4, T5, T6, T7> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7);
    }
    public static Dafny.TypeDescriptor<_System._ITuple8<T0, T1, T2, T3, T4, T5, T6, T7>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7) {
      return new Dafny.TypeDescriptor<_System._ITuple8<T0, T1, T2, T3, T4, T5, T6, T7>>(_System.Tuple8<T0, T1, T2, T3, T4, T5, T6, T7>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default()));
    }
    public static _ITuple8<T0, T1, T2, T3, T4, T5, T6, T7> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7) {
      return new Tuple8<T0, T1, T2, T3, T4, T5, T6, T7>(_0, _1, _2, _3, _4, _5, _6, _7);
    }
    public T0 dtor__0 {
      get {
        return this._0;
      }
    }
    public T1 dtor__1 {
      get {
        return this._1;
      }
    }
    public T2 dtor__2 {
      get {
        return this._2;
      }
    }
    public T3 dtor__3 {
      get {
        return this._3;
      }
    }
    public T4 dtor__4 {
      get {
        return this._4;
      }
    }
    public T5 dtor__5 {
      get {
        return this._5;
      }
    }
    public T6 dtor__6 {
      get {
        return this._6;
      }
    }
    public T7 dtor__7 {
      get {
        return this._7;
      }
    }
  }

  public interface _ITuple9<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    _ITuple9<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8);
  }
  public class Tuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8> : _ITuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8> {
    public readonly T0 _0;
    public readonly T1 _1;
    public readonly T2 _2;
    public readonly T3 _3;
    public readonly T4 _4;
    public readonly T5 _5;
    public readonly T6 _6;
    public readonly T7 _7;
    public readonly T8 _8;
    public Tuple9(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8) {
      this._0 = _0;
      this._1 = _1;
      this._2 = _2;
      this._3 = _3;
      this._4 = _4;
      this._5 = _5;
      this._6 = _6;
      this._7 = _7;
      this._8 = _8;
    }
    public _ITuple9<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8) {
      if (this is _ITuple9<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8> dt) { return dt; }
      return new Tuple9<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8>(converter0(_0), converter1(_1), converter2(_2), converter3(_3), converter4(_4), converter5(_5), converter6(_6), converter7(_7), converter8(_8));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8>;
      return oth != null && object.Equals(this._0, oth._0) && object.Equals(this._1, oth._1) && object.Equals(this._2, oth._2) && object.Equals(this._3, oth._3) && object.Equals(this._4, oth._4) && object.Equals(this._5, oth._5) && object.Equals(this._6, oth._6) && object.Equals(this._7, oth._7) && object.Equals(this._8, oth._8);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._8));
      return (int)hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this._0);
      s += ", ";
      s += Dafny.Helpers.ToString(this._1);
      s += ", ";
      s += Dafny.Helpers.ToString(this._2);
      s += ", ";
      s += Dafny.Helpers.ToString(this._3);
      s += ", ";
      s += Dafny.Helpers.ToString(this._4);
      s += ", ";
      s += Dafny.Helpers.ToString(this._5);
      s += ", ";
      s += Dafny.Helpers.ToString(this._6);
      s += ", ";
      s += Dafny.Helpers.ToString(this._7);
      s += ", ";
      s += Dafny.Helpers.ToString(this._8);
      s += ")";
      return s;
    }
    public static _ITuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8);
    }
    public static Dafny.TypeDescriptor<_System._ITuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8) {
      return new Dafny.TypeDescriptor<_System._ITuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8>>(_System.Tuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default()));
    }
    public static _ITuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8) {
      return new Tuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8>(_0, _1, _2, _3, _4, _5, _6, _7, _8);
    }
    public T0 dtor__0 {
      get {
        return this._0;
      }
    }
    public T1 dtor__1 {
      get {
        return this._1;
      }
    }
    public T2 dtor__2 {
      get {
        return this._2;
      }
    }
    public T3 dtor__3 {
      get {
        return this._3;
      }
    }
    public T4 dtor__4 {
      get {
        return this._4;
      }
    }
    public T5 dtor__5 {
      get {
        return this._5;
      }
    }
    public T6 dtor__6 {
      get {
        return this._6;
      }
    }
    public T7 dtor__7 {
      get {
        return this._7;
      }
    }
    public T8 dtor__8 {
      get {
        return this._8;
      }
    }
  }

  public interface _ITuple10<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    _ITuple10<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9);
  }
  public class Tuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9> : _ITuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9> {
    public readonly T0 _0;
    public readonly T1 _1;
    public readonly T2 _2;
    public readonly T3 _3;
    public readonly T4 _4;
    public readonly T5 _5;
    public readonly T6 _6;
    public readonly T7 _7;
    public readonly T8 _8;
    public readonly T9 _9;
    public Tuple10(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9) {
      this._0 = _0;
      this._1 = _1;
      this._2 = _2;
      this._3 = _3;
      this._4 = _4;
      this._5 = _5;
      this._6 = _6;
      this._7 = _7;
      this._8 = _8;
      this._9 = _9;
    }
    public _ITuple10<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9) {
      if (this is _ITuple10<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9> dt) { return dt; }
      return new Tuple10<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9>(converter0(_0), converter1(_1), converter2(_2), converter3(_3), converter4(_4), converter5(_5), converter6(_6), converter7(_7), converter8(_8), converter9(_9));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9>;
      return oth != null && object.Equals(this._0, oth._0) && object.Equals(this._1, oth._1) && object.Equals(this._2, oth._2) && object.Equals(this._3, oth._3) && object.Equals(this._4, oth._4) && object.Equals(this._5, oth._5) && object.Equals(this._6, oth._6) && object.Equals(this._7, oth._7) && object.Equals(this._8, oth._8) && object.Equals(this._9, oth._9);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._9));
      return (int)hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this._0);
      s += ", ";
      s += Dafny.Helpers.ToString(this._1);
      s += ", ";
      s += Dafny.Helpers.ToString(this._2);
      s += ", ";
      s += Dafny.Helpers.ToString(this._3);
      s += ", ";
      s += Dafny.Helpers.ToString(this._4);
      s += ", ";
      s += Dafny.Helpers.ToString(this._5);
      s += ", ";
      s += Dafny.Helpers.ToString(this._6);
      s += ", ";
      s += Dafny.Helpers.ToString(this._7);
      s += ", ";
      s += Dafny.Helpers.ToString(this._8);
      s += ", ";
      s += Dafny.Helpers.ToString(this._9);
      s += ")";
      return s;
    }
    public static _ITuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9);
    }
    public static Dafny.TypeDescriptor<_System._ITuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9) {
      return new Dafny.TypeDescriptor<_System._ITuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9>>(_System.Tuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default()));
    }
    public static _ITuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9) {
      return new Tuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9);
    }
    public T0 dtor__0 {
      get {
        return this._0;
      }
    }
    public T1 dtor__1 {
      get {
        return this._1;
      }
    }
    public T2 dtor__2 {
      get {
        return this._2;
      }
    }
    public T3 dtor__3 {
      get {
        return this._3;
      }
    }
    public T4 dtor__4 {
      get {
        return this._4;
      }
    }
    public T5 dtor__5 {
      get {
        return this._5;
      }
    }
    public T6 dtor__6 {
      get {
        return this._6;
      }
    }
    public T7 dtor__7 {
      get {
        return this._7;
      }
    }
    public T8 dtor__8 {
      get {
        return this._8;
      }
    }
    public T9 dtor__9 {
      get {
        return this._9;
      }
    }
  }

  public interface _ITuple11<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    _ITuple11<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10);
  }
  public class Tuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10> : _ITuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10> {
    public readonly T0 _0;
    public readonly T1 _1;
    public readonly T2 _2;
    public readonly T3 _3;
    public readonly T4 _4;
    public readonly T5 _5;
    public readonly T6 _6;
    public readonly T7 _7;
    public readonly T8 _8;
    public readonly T9 _9;
    public readonly T10 _10;
    public Tuple11(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10) {
      this._0 = _0;
      this._1 = _1;
      this._2 = _2;
      this._3 = _3;
      this._4 = _4;
      this._5 = _5;
      this._6 = _6;
      this._7 = _7;
      this._8 = _8;
      this._9 = _9;
      this._10 = _10;
    }
    public _ITuple11<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10) {
      if (this is _ITuple11<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10> dt) { return dt; }
      return new Tuple11<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10>(converter0(_0), converter1(_1), converter2(_2), converter3(_3), converter4(_4), converter5(_5), converter6(_6), converter7(_7), converter8(_8), converter9(_9), converter10(_10));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10>;
      return oth != null && object.Equals(this._0, oth._0) && object.Equals(this._1, oth._1) && object.Equals(this._2, oth._2) && object.Equals(this._3, oth._3) && object.Equals(this._4, oth._4) && object.Equals(this._5, oth._5) && object.Equals(this._6, oth._6) && object.Equals(this._7, oth._7) && object.Equals(this._8, oth._8) && object.Equals(this._9, oth._9) && object.Equals(this._10, oth._10);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._10));
      return (int)hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this._0);
      s += ", ";
      s += Dafny.Helpers.ToString(this._1);
      s += ", ";
      s += Dafny.Helpers.ToString(this._2);
      s += ", ";
      s += Dafny.Helpers.ToString(this._3);
      s += ", ";
      s += Dafny.Helpers.ToString(this._4);
      s += ", ";
      s += Dafny.Helpers.ToString(this._5);
      s += ", ";
      s += Dafny.Helpers.ToString(this._6);
      s += ", ";
      s += Dafny.Helpers.ToString(this._7);
      s += ", ";
      s += Dafny.Helpers.ToString(this._8);
      s += ", ";
      s += Dafny.Helpers.ToString(this._9);
      s += ", ";
      s += Dafny.Helpers.ToString(this._10);
      s += ")";
      return s;
    }
    public static _ITuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10);
    }
    public static Dafny.TypeDescriptor<_System._ITuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10) {
      return new Dafny.TypeDescriptor<_System._ITuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10>>(_System.Tuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default()));
    }
    public static _ITuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10) {
      return new Tuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10);
    }
    public T0 dtor__0 {
      get {
        return this._0;
      }
    }
    public T1 dtor__1 {
      get {
        return this._1;
      }
    }
    public T2 dtor__2 {
      get {
        return this._2;
      }
    }
    public T3 dtor__3 {
      get {
        return this._3;
      }
    }
    public T4 dtor__4 {
      get {
        return this._4;
      }
    }
    public T5 dtor__5 {
      get {
        return this._5;
      }
    }
    public T6 dtor__6 {
      get {
        return this._6;
      }
    }
    public T7 dtor__7 {
      get {
        return this._7;
      }
    }
    public T8 dtor__8 {
      get {
        return this._8;
      }
    }
    public T9 dtor__9 {
      get {
        return this._9;
      }
    }
    public T10 dtor__10 {
      get {
        return this._10;
      }
    }
  }

  public interface _ITuple12<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    _ITuple12<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11);
  }
  public class Tuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11> : _ITuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11> {
    public readonly T0 _0;
    public readonly T1 _1;
    public readonly T2 _2;
    public readonly T3 _3;
    public readonly T4 _4;
    public readonly T5 _5;
    public readonly T6 _6;
    public readonly T7 _7;
    public readonly T8 _8;
    public readonly T9 _9;
    public readonly T10 _10;
    public readonly T11 _11;
    public Tuple12(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11) {
      this._0 = _0;
      this._1 = _1;
      this._2 = _2;
      this._3 = _3;
      this._4 = _4;
      this._5 = _5;
      this._6 = _6;
      this._7 = _7;
      this._8 = _8;
      this._9 = _9;
      this._10 = _10;
      this._11 = _11;
    }
    public _ITuple12<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11) {
      if (this is _ITuple12<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11> dt) { return dt; }
      return new Tuple12<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11>(converter0(_0), converter1(_1), converter2(_2), converter3(_3), converter4(_4), converter5(_5), converter6(_6), converter7(_7), converter8(_8), converter9(_9), converter10(_10), converter11(_11));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11>;
      return oth != null && object.Equals(this._0, oth._0) && object.Equals(this._1, oth._1) && object.Equals(this._2, oth._2) && object.Equals(this._3, oth._3) && object.Equals(this._4, oth._4) && object.Equals(this._5, oth._5) && object.Equals(this._6, oth._6) && object.Equals(this._7, oth._7) && object.Equals(this._8, oth._8) && object.Equals(this._9, oth._9) && object.Equals(this._10, oth._10) && object.Equals(this._11, oth._11);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._11));
      return (int)hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this._0);
      s += ", ";
      s += Dafny.Helpers.ToString(this._1);
      s += ", ";
      s += Dafny.Helpers.ToString(this._2);
      s += ", ";
      s += Dafny.Helpers.ToString(this._3);
      s += ", ";
      s += Dafny.Helpers.ToString(this._4);
      s += ", ";
      s += Dafny.Helpers.ToString(this._5);
      s += ", ";
      s += Dafny.Helpers.ToString(this._6);
      s += ", ";
      s += Dafny.Helpers.ToString(this._7);
      s += ", ";
      s += Dafny.Helpers.ToString(this._8);
      s += ", ";
      s += Dafny.Helpers.ToString(this._9);
      s += ", ";
      s += Dafny.Helpers.ToString(this._10);
      s += ", ";
      s += Dafny.Helpers.ToString(this._11);
      s += ")";
      return s;
    }
    public static _ITuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11);
    }
    public static Dafny.TypeDescriptor<_System._ITuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11) {
      return new Dafny.TypeDescriptor<_System._ITuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11>>(_System.Tuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default()));
    }
    public static _ITuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11) {
      return new Tuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11);
    }
    public T0 dtor__0 {
      get {
        return this._0;
      }
    }
    public T1 dtor__1 {
      get {
        return this._1;
      }
    }
    public T2 dtor__2 {
      get {
        return this._2;
      }
    }
    public T3 dtor__3 {
      get {
        return this._3;
      }
    }
    public T4 dtor__4 {
      get {
        return this._4;
      }
    }
    public T5 dtor__5 {
      get {
        return this._5;
      }
    }
    public T6 dtor__6 {
      get {
        return this._6;
      }
    }
    public T7 dtor__7 {
      get {
        return this._7;
      }
    }
    public T8 dtor__8 {
      get {
        return this._8;
      }
    }
    public T9 dtor__9 {
      get {
        return this._9;
      }
    }
    public T10 dtor__10 {
      get {
        return this._10;
      }
    }
    public T11 dtor__11 {
      get {
        return this._11;
      }
    }
  }

  public interface _ITuple13<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    _ITuple13<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12);
  }
  public class Tuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12> : _ITuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12> {
    public readonly T0 _0;
    public readonly T1 _1;
    public readonly T2 _2;
    public readonly T3 _3;
    public readonly T4 _4;
    public readonly T5 _5;
    public readonly T6 _6;
    public readonly T7 _7;
    public readonly T8 _8;
    public readonly T9 _9;
    public readonly T10 _10;
    public readonly T11 _11;
    public readonly T12 _12;
    public Tuple13(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12) {
      this._0 = _0;
      this._1 = _1;
      this._2 = _2;
      this._3 = _3;
      this._4 = _4;
      this._5 = _5;
      this._6 = _6;
      this._7 = _7;
      this._8 = _8;
      this._9 = _9;
      this._10 = _10;
      this._11 = _11;
      this._12 = _12;
    }
    public _ITuple13<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12) {
      if (this is _ITuple13<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12> dt) { return dt; }
      return new Tuple13<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12>(converter0(_0), converter1(_1), converter2(_2), converter3(_3), converter4(_4), converter5(_5), converter6(_6), converter7(_7), converter8(_8), converter9(_9), converter10(_10), converter11(_11), converter12(_12));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12>;
      return oth != null && object.Equals(this._0, oth._0) && object.Equals(this._1, oth._1) && object.Equals(this._2, oth._2) && object.Equals(this._3, oth._3) && object.Equals(this._4, oth._4) && object.Equals(this._5, oth._5) && object.Equals(this._6, oth._6) && object.Equals(this._7, oth._7) && object.Equals(this._8, oth._8) && object.Equals(this._9, oth._9) && object.Equals(this._10, oth._10) && object.Equals(this._11, oth._11) && object.Equals(this._12, oth._12);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._12));
      return (int)hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this._0);
      s += ", ";
      s += Dafny.Helpers.ToString(this._1);
      s += ", ";
      s += Dafny.Helpers.ToString(this._2);
      s += ", ";
      s += Dafny.Helpers.ToString(this._3);
      s += ", ";
      s += Dafny.Helpers.ToString(this._4);
      s += ", ";
      s += Dafny.Helpers.ToString(this._5);
      s += ", ";
      s += Dafny.Helpers.ToString(this._6);
      s += ", ";
      s += Dafny.Helpers.ToString(this._7);
      s += ", ";
      s += Dafny.Helpers.ToString(this._8);
      s += ", ";
      s += Dafny.Helpers.ToString(this._9);
      s += ", ";
      s += Dafny.Helpers.ToString(this._10);
      s += ", ";
      s += Dafny.Helpers.ToString(this._11);
      s += ", ";
      s += Dafny.Helpers.ToString(this._12);
      s += ")";
      return s;
    }
    public static _ITuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12);
    }
    public static Dafny.TypeDescriptor<_System._ITuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12) {
      return new Dafny.TypeDescriptor<_System._ITuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12>>(_System.Tuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default()));
    }
    public static _ITuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12) {
      return new Tuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12);
    }
    public T0 dtor__0 {
      get {
        return this._0;
      }
    }
    public T1 dtor__1 {
      get {
        return this._1;
      }
    }
    public T2 dtor__2 {
      get {
        return this._2;
      }
    }
    public T3 dtor__3 {
      get {
        return this._3;
      }
    }
    public T4 dtor__4 {
      get {
        return this._4;
      }
    }
    public T5 dtor__5 {
      get {
        return this._5;
      }
    }
    public T6 dtor__6 {
      get {
        return this._6;
      }
    }
    public T7 dtor__7 {
      get {
        return this._7;
      }
    }
    public T8 dtor__8 {
      get {
        return this._8;
      }
    }
    public T9 dtor__9 {
      get {
        return this._9;
      }
    }
    public T10 dtor__10 {
      get {
        return this._10;
      }
    }
    public T11 dtor__11 {
      get {
        return this._11;
      }
    }
    public T12 dtor__12 {
      get {
        return this._12;
      }
    }
  }

  public interface _ITuple14<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12, out T13> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    T13 dtor__13 { get; }
    _ITuple14<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13);
  }
  public class Tuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13> : _ITuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13> {
    public readonly T0 _0;
    public readonly T1 _1;
    public readonly T2 _2;
    public readonly T3 _3;
    public readonly T4 _4;
    public readonly T5 _5;
    public readonly T6 _6;
    public readonly T7 _7;
    public readonly T8 _8;
    public readonly T9 _9;
    public readonly T10 _10;
    public readonly T11 _11;
    public readonly T12 _12;
    public readonly T13 _13;
    public Tuple14(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13) {
      this._0 = _0;
      this._1 = _1;
      this._2 = _2;
      this._3 = _3;
      this._4 = _4;
      this._5 = _5;
      this._6 = _6;
      this._7 = _7;
      this._8 = _8;
      this._9 = _9;
      this._10 = _10;
      this._11 = _11;
      this._12 = _12;
      this._13 = _13;
    }
    public _ITuple14<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13) {
      if (this is _ITuple14<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13> dt) { return dt; }
      return new Tuple14<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13>(converter0(_0), converter1(_1), converter2(_2), converter3(_3), converter4(_4), converter5(_5), converter6(_6), converter7(_7), converter8(_8), converter9(_9), converter10(_10), converter11(_11), converter12(_12), converter13(_13));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13>;
      return oth != null && object.Equals(this._0, oth._0) && object.Equals(this._1, oth._1) && object.Equals(this._2, oth._2) && object.Equals(this._3, oth._3) && object.Equals(this._4, oth._4) && object.Equals(this._5, oth._5) && object.Equals(this._6, oth._6) && object.Equals(this._7, oth._7) && object.Equals(this._8, oth._8) && object.Equals(this._9, oth._9) && object.Equals(this._10, oth._10) && object.Equals(this._11, oth._11) && object.Equals(this._12, oth._12) && object.Equals(this._13, oth._13);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._12));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._13));
      return (int)hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this._0);
      s += ", ";
      s += Dafny.Helpers.ToString(this._1);
      s += ", ";
      s += Dafny.Helpers.ToString(this._2);
      s += ", ";
      s += Dafny.Helpers.ToString(this._3);
      s += ", ";
      s += Dafny.Helpers.ToString(this._4);
      s += ", ";
      s += Dafny.Helpers.ToString(this._5);
      s += ", ";
      s += Dafny.Helpers.ToString(this._6);
      s += ", ";
      s += Dafny.Helpers.ToString(this._7);
      s += ", ";
      s += Dafny.Helpers.ToString(this._8);
      s += ", ";
      s += Dafny.Helpers.ToString(this._9);
      s += ", ";
      s += Dafny.Helpers.ToString(this._10);
      s += ", ";
      s += Dafny.Helpers.ToString(this._11);
      s += ", ";
      s += Dafny.Helpers.ToString(this._12);
      s += ", ";
      s += Dafny.Helpers.ToString(this._13);
      s += ")";
      return s;
    }
    public static _ITuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12, T13 _default_T13) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12, _default_T13);
    }
    public static Dafny.TypeDescriptor<_System._ITuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12, Dafny.TypeDescriptor<T13> _td_T13) {
      return new Dafny.TypeDescriptor<_System._ITuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13>>(_System.Tuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default(), _td_T13.Default()));
    }
    public static _ITuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13) {
      return new Tuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13);
    }
    public T0 dtor__0 {
      get {
        return this._0;
      }
    }
    public T1 dtor__1 {
      get {
        return this._1;
      }
    }
    public T2 dtor__2 {
      get {
        return this._2;
      }
    }
    public T3 dtor__3 {
      get {
        return this._3;
      }
    }
    public T4 dtor__4 {
      get {
        return this._4;
      }
    }
    public T5 dtor__5 {
      get {
        return this._5;
      }
    }
    public T6 dtor__6 {
      get {
        return this._6;
      }
    }
    public T7 dtor__7 {
      get {
        return this._7;
      }
    }
    public T8 dtor__8 {
      get {
        return this._8;
      }
    }
    public T9 dtor__9 {
      get {
        return this._9;
      }
    }
    public T10 dtor__10 {
      get {
        return this._10;
      }
    }
    public T11 dtor__11 {
      get {
        return this._11;
      }
    }
    public T12 dtor__12 {
      get {
        return this._12;
      }
    }
    public T13 dtor__13 {
      get {
        return this._13;
      }
    }
  }

  public interface _ITuple15<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12, out T13, out T14> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    T13 dtor__13 { get; }
    T14 dtor__14 { get; }
    _ITuple15<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14);
  }
  public class Tuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14> : _ITuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14> {
    public readonly T0 _0;
    public readonly T1 _1;
    public readonly T2 _2;
    public readonly T3 _3;
    public readonly T4 _4;
    public readonly T5 _5;
    public readonly T6 _6;
    public readonly T7 _7;
    public readonly T8 _8;
    public readonly T9 _9;
    public readonly T10 _10;
    public readonly T11 _11;
    public readonly T12 _12;
    public readonly T13 _13;
    public readonly T14 _14;
    public Tuple15(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14) {
      this._0 = _0;
      this._1 = _1;
      this._2 = _2;
      this._3 = _3;
      this._4 = _4;
      this._5 = _5;
      this._6 = _6;
      this._7 = _7;
      this._8 = _8;
      this._9 = _9;
      this._10 = _10;
      this._11 = _11;
      this._12 = _12;
      this._13 = _13;
      this._14 = _14;
    }
    public _ITuple15<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14) {
      if (this is _ITuple15<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14> dt) { return dt; }
      return new Tuple15<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14>(converter0(_0), converter1(_1), converter2(_2), converter3(_3), converter4(_4), converter5(_5), converter6(_6), converter7(_7), converter8(_8), converter9(_9), converter10(_10), converter11(_11), converter12(_12), converter13(_13), converter14(_14));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14>;
      return oth != null && object.Equals(this._0, oth._0) && object.Equals(this._1, oth._1) && object.Equals(this._2, oth._2) && object.Equals(this._3, oth._3) && object.Equals(this._4, oth._4) && object.Equals(this._5, oth._5) && object.Equals(this._6, oth._6) && object.Equals(this._7, oth._7) && object.Equals(this._8, oth._8) && object.Equals(this._9, oth._9) && object.Equals(this._10, oth._10) && object.Equals(this._11, oth._11) && object.Equals(this._12, oth._12) && object.Equals(this._13, oth._13) && object.Equals(this._14, oth._14);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._12));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._13));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._14));
      return (int)hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this._0);
      s += ", ";
      s += Dafny.Helpers.ToString(this._1);
      s += ", ";
      s += Dafny.Helpers.ToString(this._2);
      s += ", ";
      s += Dafny.Helpers.ToString(this._3);
      s += ", ";
      s += Dafny.Helpers.ToString(this._4);
      s += ", ";
      s += Dafny.Helpers.ToString(this._5);
      s += ", ";
      s += Dafny.Helpers.ToString(this._6);
      s += ", ";
      s += Dafny.Helpers.ToString(this._7);
      s += ", ";
      s += Dafny.Helpers.ToString(this._8);
      s += ", ";
      s += Dafny.Helpers.ToString(this._9);
      s += ", ";
      s += Dafny.Helpers.ToString(this._10);
      s += ", ";
      s += Dafny.Helpers.ToString(this._11);
      s += ", ";
      s += Dafny.Helpers.ToString(this._12);
      s += ", ";
      s += Dafny.Helpers.ToString(this._13);
      s += ", ";
      s += Dafny.Helpers.ToString(this._14);
      s += ")";
      return s;
    }
    public static _ITuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12, T13 _default_T13, T14 _default_T14) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12, _default_T13, _default_T14);
    }
    public static Dafny.TypeDescriptor<_System._ITuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12, Dafny.TypeDescriptor<T13> _td_T13, Dafny.TypeDescriptor<T14> _td_T14) {
      return new Dafny.TypeDescriptor<_System._ITuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14>>(_System.Tuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default(), _td_T13.Default(), _td_T14.Default()));
    }
    public static _ITuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14) {
      return new Tuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14);
    }
    public T0 dtor__0 {
      get {
        return this._0;
      }
    }
    public T1 dtor__1 {
      get {
        return this._1;
      }
    }
    public T2 dtor__2 {
      get {
        return this._2;
      }
    }
    public T3 dtor__3 {
      get {
        return this._3;
      }
    }
    public T4 dtor__4 {
      get {
        return this._4;
      }
    }
    public T5 dtor__5 {
      get {
        return this._5;
      }
    }
    public T6 dtor__6 {
      get {
        return this._6;
      }
    }
    public T7 dtor__7 {
      get {
        return this._7;
      }
    }
    public T8 dtor__8 {
      get {
        return this._8;
      }
    }
    public T9 dtor__9 {
      get {
        return this._9;
      }
    }
    public T10 dtor__10 {
      get {
        return this._10;
      }
    }
    public T11 dtor__11 {
      get {
        return this._11;
      }
    }
    public T12 dtor__12 {
      get {
        return this._12;
      }
    }
    public T13 dtor__13 {
      get {
        return this._13;
      }
    }
    public T14 dtor__14 {
      get {
        return this._14;
      }
    }
  }

  public interface _ITuple16<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12, out T13, out T14, out T15> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    T13 dtor__13 { get; }
    T14 dtor__14 { get; }
    T15 dtor__15 { get; }
    _ITuple16<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15);
  }
  public class Tuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15> : _ITuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15> {
    public readonly T0 _0;
    public readonly T1 _1;
    public readonly T2 _2;
    public readonly T3 _3;
    public readonly T4 _4;
    public readonly T5 _5;
    public readonly T6 _6;
    public readonly T7 _7;
    public readonly T8 _8;
    public readonly T9 _9;
    public readonly T10 _10;
    public readonly T11 _11;
    public readonly T12 _12;
    public readonly T13 _13;
    public readonly T14 _14;
    public readonly T15 _15;
    public Tuple16(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15) {
      this._0 = _0;
      this._1 = _1;
      this._2 = _2;
      this._3 = _3;
      this._4 = _4;
      this._5 = _5;
      this._6 = _6;
      this._7 = _7;
      this._8 = _8;
      this._9 = _9;
      this._10 = _10;
      this._11 = _11;
      this._12 = _12;
      this._13 = _13;
      this._14 = _14;
      this._15 = _15;
    }
    public _ITuple16<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15) {
      if (this is _ITuple16<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15> dt) { return dt; }
      return new Tuple16<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15>(converter0(_0), converter1(_1), converter2(_2), converter3(_3), converter4(_4), converter5(_5), converter6(_6), converter7(_7), converter8(_8), converter9(_9), converter10(_10), converter11(_11), converter12(_12), converter13(_13), converter14(_14), converter15(_15));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15>;
      return oth != null && object.Equals(this._0, oth._0) && object.Equals(this._1, oth._1) && object.Equals(this._2, oth._2) && object.Equals(this._3, oth._3) && object.Equals(this._4, oth._4) && object.Equals(this._5, oth._5) && object.Equals(this._6, oth._6) && object.Equals(this._7, oth._7) && object.Equals(this._8, oth._8) && object.Equals(this._9, oth._9) && object.Equals(this._10, oth._10) && object.Equals(this._11, oth._11) && object.Equals(this._12, oth._12) && object.Equals(this._13, oth._13) && object.Equals(this._14, oth._14) && object.Equals(this._15, oth._15);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._12));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._13));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._14));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._15));
      return (int)hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this._0);
      s += ", ";
      s += Dafny.Helpers.ToString(this._1);
      s += ", ";
      s += Dafny.Helpers.ToString(this._2);
      s += ", ";
      s += Dafny.Helpers.ToString(this._3);
      s += ", ";
      s += Dafny.Helpers.ToString(this._4);
      s += ", ";
      s += Dafny.Helpers.ToString(this._5);
      s += ", ";
      s += Dafny.Helpers.ToString(this._6);
      s += ", ";
      s += Dafny.Helpers.ToString(this._7);
      s += ", ";
      s += Dafny.Helpers.ToString(this._8);
      s += ", ";
      s += Dafny.Helpers.ToString(this._9);
      s += ", ";
      s += Dafny.Helpers.ToString(this._10);
      s += ", ";
      s += Dafny.Helpers.ToString(this._11);
      s += ", ";
      s += Dafny.Helpers.ToString(this._12);
      s += ", ";
      s += Dafny.Helpers.ToString(this._13);
      s += ", ";
      s += Dafny.Helpers.ToString(this._14);
      s += ", ";
      s += Dafny.Helpers.ToString(this._15);
      s += ")";
      return s;
    }
    public static _ITuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12, T13 _default_T13, T14 _default_T14, T15 _default_T15) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12, _default_T13, _default_T14, _default_T15);
    }
    public static Dafny.TypeDescriptor<_System._ITuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12, Dafny.TypeDescriptor<T13> _td_T13, Dafny.TypeDescriptor<T14> _td_T14, Dafny.TypeDescriptor<T15> _td_T15) {
      return new Dafny.TypeDescriptor<_System._ITuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15>>(_System.Tuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default(), _td_T13.Default(), _td_T14.Default(), _td_T15.Default()));
    }
    public static _ITuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15) {
      return new Tuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15);
    }
    public T0 dtor__0 {
      get {
        return this._0;
      }
    }
    public T1 dtor__1 {
      get {
        return this._1;
      }
    }
    public T2 dtor__2 {
      get {
        return this._2;
      }
    }
    public T3 dtor__3 {
      get {
        return this._3;
      }
    }
    public T4 dtor__4 {
      get {
        return this._4;
      }
    }
    public T5 dtor__5 {
      get {
        return this._5;
      }
    }
    public T6 dtor__6 {
      get {
        return this._6;
      }
    }
    public T7 dtor__7 {
      get {
        return this._7;
      }
    }
    public T8 dtor__8 {
      get {
        return this._8;
      }
    }
    public T9 dtor__9 {
      get {
        return this._9;
      }
    }
    public T10 dtor__10 {
      get {
        return this._10;
      }
    }
    public T11 dtor__11 {
      get {
        return this._11;
      }
    }
    public T12 dtor__12 {
      get {
        return this._12;
      }
    }
    public T13 dtor__13 {
      get {
        return this._13;
      }
    }
    public T14 dtor__14 {
      get {
        return this._14;
      }
    }
    public T15 dtor__15 {
      get {
        return this._15;
      }
    }
  }

  public interface _ITuple17<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12, out T13, out T14, out T15, out T16> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    T13 dtor__13 { get; }
    T14 dtor__14 { get; }
    T15 dtor__15 { get; }
    T16 dtor__16 { get; }
    _ITuple17<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16);
  }
  public class Tuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16> : _ITuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16> {
    public readonly T0 _0;
    public readonly T1 _1;
    public readonly T2 _2;
    public readonly T3 _3;
    public readonly T4 _4;
    public readonly T5 _5;
    public readonly T6 _6;
    public readonly T7 _7;
    public readonly T8 _8;
    public readonly T9 _9;
    public readonly T10 _10;
    public readonly T11 _11;
    public readonly T12 _12;
    public readonly T13 _13;
    public readonly T14 _14;
    public readonly T15 _15;
    public readonly T16 _16;
    public Tuple17(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16) {
      this._0 = _0;
      this._1 = _1;
      this._2 = _2;
      this._3 = _3;
      this._4 = _4;
      this._5 = _5;
      this._6 = _6;
      this._7 = _7;
      this._8 = _8;
      this._9 = _9;
      this._10 = _10;
      this._11 = _11;
      this._12 = _12;
      this._13 = _13;
      this._14 = _14;
      this._15 = _15;
      this._16 = _16;
    }
    public _ITuple17<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16) {
      if (this is _ITuple17<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16> dt) { return dt; }
      return new Tuple17<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16>(converter0(_0), converter1(_1), converter2(_2), converter3(_3), converter4(_4), converter5(_5), converter6(_6), converter7(_7), converter8(_8), converter9(_9), converter10(_10), converter11(_11), converter12(_12), converter13(_13), converter14(_14), converter15(_15), converter16(_16));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16>;
      return oth != null && object.Equals(this._0, oth._0) && object.Equals(this._1, oth._1) && object.Equals(this._2, oth._2) && object.Equals(this._3, oth._3) && object.Equals(this._4, oth._4) && object.Equals(this._5, oth._5) && object.Equals(this._6, oth._6) && object.Equals(this._7, oth._7) && object.Equals(this._8, oth._8) && object.Equals(this._9, oth._9) && object.Equals(this._10, oth._10) && object.Equals(this._11, oth._11) && object.Equals(this._12, oth._12) && object.Equals(this._13, oth._13) && object.Equals(this._14, oth._14) && object.Equals(this._15, oth._15) && object.Equals(this._16, oth._16);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._12));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._13));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._14));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._15));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._16));
      return (int)hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this._0);
      s += ", ";
      s += Dafny.Helpers.ToString(this._1);
      s += ", ";
      s += Dafny.Helpers.ToString(this._2);
      s += ", ";
      s += Dafny.Helpers.ToString(this._3);
      s += ", ";
      s += Dafny.Helpers.ToString(this._4);
      s += ", ";
      s += Dafny.Helpers.ToString(this._5);
      s += ", ";
      s += Dafny.Helpers.ToString(this._6);
      s += ", ";
      s += Dafny.Helpers.ToString(this._7);
      s += ", ";
      s += Dafny.Helpers.ToString(this._8);
      s += ", ";
      s += Dafny.Helpers.ToString(this._9);
      s += ", ";
      s += Dafny.Helpers.ToString(this._10);
      s += ", ";
      s += Dafny.Helpers.ToString(this._11);
      s += ", ";
      s += Dafny.Helpers.ToString(this._12);
      s += ", ";
      s += Dafny.Helpers.ToString(this._13);
      s += ", ";
      s += Dafny.Helpers.ToString(this._14);
      s += ", ";
      s += Dafny.Helpers.ToString(this._15);
      s += ", ";
      s += Dafny.Helpers.ToString(this._16);
      s += ")";
      return s;
    }
    public static _ITuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12, T13 _default_T13, T14 _default_T14, T15 _default_T15, T16 _default_T16) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12, _default_T13, _default_T14, _default_T15, _default_T16);
    }
    public static Dafny.TypeDescriptor<_System._ITuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12, Dafny.TypeDescriptor<T13> _td_T13, Dafny.TypeDescriptor<T14> _td_T14, Dafny.TypeDescriptor<T15> _td_T15, Dafny.TypeDescriptor<T16> _td_T16) {
      return new Dafny.TypeDescriptor<_System._ITuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16>>(_System.Tuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default(), _td_T13.Default(), _td_T14.Default(), _td_T15.Default(), _td_T16.Default()));
    }
    public static _ITuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16) {
      return new Tuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16);
    }
    public T0 dtor__0 {
      get {
        return this._0;
      }
    }
    public T1 dtor__1 {
      get {
        return this._1;
      }
    }
    public T2 dtor__2 {
      get {
        return this._2;
      }
    }
    public T3 dtor__3 {
      get {
        return this._3;
      }
    }
    public T4 dtor__4 {
      get {
        return this._4;
      }
    }
    public T5 dtor__5 {
      get {
        return this._5;
      }
    }
    public T6 dtor__6 {
      get {
        return this._6;
      }
    }
    public T7 dtor__7 {
      get {
        return this._7;
      }
    }
    public T8 dtor__8 {
      get {
        return this._8;
      }
    }
    public T9 dtor__9 {
      get {
        return this._9;
      }
    }
    public T10 dtor__10 {
      get {
        return this._10;
      }
    }
    public T11 dtor__11 {
      get {
        return this._11;
      }
    }
    public T12 dtor__12 {
      get {
        return this._12;
      }
    }
    public T13 dtor__13 {
      get {
        return this._13;
      }
    }
    public T14 dtor__14 {
      get {
        return this._14;
      }
    }
    public T15 dtor__15 {
      get {
        return this._15;
      }
    }
    public T16 dtor__16 {
      get {
        return this._16;
      }
    }
  }

  public interface _ITuple18<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12, out T13, out T14, out T15, out T16, out T17> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    T13 dtor__13 { get; }
    T14 dtor__14 { get; }
    T15 dtor__15 { get; }
    T16 dtor__16 { get; }
    T17 dtor__17 { get; }
    _ITuple18<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16, Func<T17, __T17> converter17);
  }
  public class Tuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17> : _ITuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17> {
    public readonly T0 _0;
    public readonly T1 _1;
    public readonly T2 _2;
    public readonly T3 _3;
    public readonly T4 _4;
    public readonly T5 _5;
    public readonly T6 _6;
    public readonly T7 _7;
    public readonly T8 _8;
    public readonly T9 _9;
    public readonly T10 _10;
    public readonly T11 _11;
    public readonly T12 _12;
    public readonly T13 _13;
    public readonly T14 _14;
    public readonly T15 _15;
    public readonly T16 _16;
    public readonly T17 _17;
    public Tuple18(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17) {
      this._0 = _0;
      this._1 = _1;
      this._2 = _2;
      this._3 = _3;
      this._4 = _4;
      this._5 = _5;
      this._6 = _6;
      this._7 = _7;
      this._8 = _8;
      this._9 = _9;
      this._10 = _10;
      this._11 = _11;
      this._12 = _12;
      this._13 = _13;
      this._14 = _14;
      this._15 = _15;
      this._16 = _16;
      this._17 = _17;
    }
    public _ITuple18<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16, Func<T17, __T17> converter17) {
      if (this is _ITuple18<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17> dt) { return dt; }
      return new Tuple18<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17>(converter0(_0), converter1(_1), converter2(_2), converter3(_3), converter4(_4), converter5(_5), converter6(_6), converter7(_7), converter8(_8), converter9(_9), converter10(_10), converter11(_11), converter12(_12), converter13(_13), converter14(_14), converter15(_15), converter16(_16), converter17(_17));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17>;
      return oth != null && object.Equals(this._0, oth._0) && object.Equals(this._1, oth._1) && object.Equals(this._2, oth._2) && object.Equals(this._3, oth._3) && object.Equals(this._4, oth._4) && object.Equals(this._5, oth._5) && object.Equals(this._6, oth._6) && object.Equals(this._7, oth._7) && object.Equals(this._8, oth._8) && object.Equals(this._9, oth._9) && object.Equals(this._10, oth._10) && object.Equals(this._11, oth._11) && object.Equals(this._12, oth._12) && object.Equals(this._13, oth._13) && object.Equals(this._14, oth._14) && object.Equals(this._15, oth._15) && object.Equals(this._16, oth._16) && object.Equals(this._17, oth._17);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._12));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._13));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._14));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._15));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._16));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._17));
      return (int)hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this._0);
      s += ", ";
      s += Dafny.Helpers.ToString(this._1);
      s += ", ";
      s += Dafny.Helpers.ToString(this._2);
      s += ", ";
      s += Dafny.Helpers.ToString(this._3);
      s += ", ";
      s += Dafny.Helpers.ToString(this._4);
      s += ", ";
      s += Dafny.Helpers.ToString(this._5);
      s += ", ";
      s += Dafny.Helpers.ToString(this._6);
      s += ", ";
      s += Dafny.Helpers.ToString(this._7);
      s += ", ";
      s += Dafny.Helpers.ToString(this._8);
      s += ", ";
      s += Dafny.Helpers.ToString(this._9);
      s += ", ";
      s += Dafny.Helpers.ToString(this._10);
      s += ", ";
      s += Dafny.Helpers.ToString(this._11);
      s += ", ";
      s += Dafny.Helpers.ToString(this._12);
      s += ", ";
      s += Dafny.Helpers.ToString(this._13);
      s += ", ";
      s += Dafny.Helpers.ToString(this._14);
      s += ", ";
      s += Dafny.Helpers.ToString(this._15);
      s += ", ";
      s += Dafny.Helpers.ToString(this._16);
      s += ", ";
      s += Dafny.Helpers.ToString(this._17);
      s += ")";
      return s;
    }
    public static _ITuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12, T13 _default_T13, T14 _default_T14, T15 _default_T15, T16 _default_T16, T17 _default_T17) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12, _default_T13, _default_T14, _default_T15, _default_T16, _default_T17);
    }
    public static Dafny.TypeDescriptor<_System._ITuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12, Dafny.TypeDescriptor<T13> _td_T13, Dafny.TypeDescriptor<T14> _td_T14, Dafny.TypeDescriptor<T15> _td_T15, Dafny.TypeDescriptor<T16> _td_T16, Dafny.TypeDescriptor<T17> _td_T17) {
      return new Dafny.TypeDescriptor<_System._ITuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17>>(_System.Tuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default(), _td_T13.Default(), _td_T14.Default(), _td_T15.Default(), _td_T16.Default(), _td_T17.Default()));
    }
    public static _ITuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17) {
      return new Tuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17);
    }
    public T0 dtor__0 {
      get {
        return this._0;
      }
    }
    public T1 dtor__1 {
      get {
        return this._1;
      }
    }
    public T2 dtor__2 {
      get {
        return this._2;
      }
    }
    public T3 dtor__3 {
      get {
        return this._3;
      }
    }
    public T4 dtor__4 {
      get {
        return this._4;
      }
    }
    public T5 dtor__5 {
      get {
        return this._5;
      }
    }
    public T6 dtor__6 {
      get {
        return this._6;
      }
    }
    public T7 dtor__7 {
      get {
        return this._7;
      }
    }
    public T8 dtor__8 {
      get {
        return this._8;
      }
    }
    public T9 dtor__9 {
      get {
        return this._9;
      }
    }
    public T10 dtor__10 {
      get {
        return this._10;
      }
    }
    public T11 dtor__11 {
      get {
        return this._11;
      }
    }
    public T12 dtor__12 {
      get {
        return this._12;
      }
    }
    public T13 dtor__13 {
      get {
        return this._13;
      }
    }
    public T14 dtor__14 {
      get {
        return this._14;
      }
    }
    public T15 dtor__15 {
      get {
        return this._15;
      }
    }
    public T16 dtor__16 {
      get {
        return this._16;
      }
    }
    public T17 dtor__17 {
      get {
        return this._17;
      }
    }
  }

  public interface _ITuple19<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12, out T13, out T14, out T15, out T16, out T17, out T18> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    T13 dtor__13 { get; }
    T14 dtor__14 { get; }
    T15 dtor__15 { get; }
    T16 dtor__16 { get; }
    T17 dtor__17 { get; }
    T18 dtor__18 { get; }
    _ITuple19<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16, Func<T17, __T17> converter17, Func<T18, __T18> converter18);
  }
  public class Tuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18> : _ITuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18> {
    public readonly T0 _0;
    public readonly T1 _1;
    public readonly T2 _2;
    public readonly T3 _3;
    public readonly T4 _4;
    public readonly T5 _5;
    public readonly T6 _6;
    public readonly T7 _7;
    public readonly T8 _8;
    public readonly T9 _9;
    public readonly T10 _10;
    public readonly T11 _11;
    public readonly T12 _12;
    public readonly T13 _13;
    public readonly T14 _14;
    public readonly T15 _15;
    public readonly T16 _16;
    public readonly T17 _17;
    public readonly T18 _18;
    public Tuple19(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17, T18 _18) {
      this._0 = _0;
      this._1 = _1;
      this._2 = _2;
      this._3 = _3;
      this._4 = _4;
      this._5 = _5;
      this._6 = _6;
      this._7 = _7;
      this._8 = _8;
      this._9 = _9;
      this._10 = _10;
      this._11 = _11;
      this._12 = _12;
      this._13 = _13;
      this._14 = _14;
      this._15 = _15;
      this._16 = _16;
      this._17 = _17;
      this._18 = _18;
    }
    public _ITuple19<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16, Func<T17, __T17> converter17, Func<T18, __T18> converter18) {
      if (this is _ITuple19<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18> dt) { return dt; }
      return new Tuple19<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18>(converter0(_0), converter1(_1), converter2(_2), converter3(_3), converter4(_4), converter5(_5), converter6(_6), converter7(_7), converter8(_8), converter9(_9), converter10(_10), converter11(_11), converter12(_12), converter13(_13), converter14(_14), converter15(_15), converter16(_16), converter17(_17), converter18(_18));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18>;
      return oth != null && object.Equals(this._0, oth._0) && object.Equals(this._1, oth._1) && object.Equals(this._2, oth._2) && object.Equals(this._3, oth._3) && object.Equals(this._4, oth._4) && object.Equals(this._5, oth._5) && object.Equals(this._6, oth._6) && object.Equals(this._7, oth._7) && object.Equals(this._8, oth._8) && object.Equals(this._9, oth._9) && object.Equals(this._10, oth._10) && object.Equals(this._11, oth._11) && object.Equals(this._12, oth._12) && object.Equals(this._13, oth._13) && object.Equals(this._14, oth._14) && object.Equals(this._15, oth._15) && object.Equals(this._16, oth._16) && object.Equals(this._17, oth._17) && object.Equals(this._18, oth._18);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._12));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._13));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._14));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._15));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._16));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._17));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._18));
      return (int)hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this._0);
      s += ", ";
      s += Dafny.Helpers.ToString(this._1);
      s += ", ";
      s += Dafny.Helpers.ToString(this._2);
      s += ", ";
      s += Dafny.Helpers.ToString(this._3);
      s += ", ";
      s += Dafny.Helpers.ToString(this._4);
      s += ", ";
      s += Dafny.Helpers.ToString(this._5);
      s += ", ";
      s += Dafny.Helpers.ToString(this._6);
      s += ", ";
      s += Dafny.Helpers.ToString(this._7);
      s += ", ";
      s += Dafny.Helpers.ToString(this._8);
      s += ", ";
      s += Dafny.Helpers.ToString(this._9);
      s += ", ";
      s += Dafny.Helpers.ToString(this._10);
      s += ", ";
      s += Dafny.Helpers.ToString(this._11);
      s += ", ";
      s += Dafny.Helpers.ToString(this._12);
      s += ", ";
      s += Dafny.Helpers.ToString(this._13);
      s += ", ";
      s += Dafny.Helpers.ToString(this._14);
      s += ", ";
      s += Dafny.Helpers.ToString(this._15);
      s += ", ";
      s += Dafny.Helpers.ToString(this._16);
      s += ", ";
      s += Dafny.Helpers.ToString(this._17);
      s += ", ";
      s += Dafny.Helpers.ToString(this._18);
      s += ")";
      return s;
    }
    public static _ITuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12, T13 _default_T13, T14 _default_T14, T15 _default_T15, T16 _default_T16, T17 _default_T17, T18 _default_T18) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12, _default_T13, _default_T14, _default_T15, _default_T16, _default_T17, _default_T18);
    }
    public static Dafny.TypeDescriptor<_System._ITuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12, Dafny.TypeDescriptor<T13> _td_T13, Dafny.TypeDescriptor<T14> _td_T14, Dafny.TypeDescriptor<T15> _td_T15, Dafny.TypeDescriptor<T16> _td_T16, Dafny.TypeDescriptor<T17> _td_T17, Dafny.TypeDescriptor<T18> _td_T18) {
      return new Dafny.TypeDescriptor<_System._ITuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18>>(_System.Tuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default(), _td_T13.Default(), _td_T14.Default(), _td_T15.Default(), _td_T16.Default(), _td_T17.Default(), _td_T18.Default()));
    }
    public static _ITuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17, T18 _18) {
      return new Tuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18);
    }
    public T0 dtor__0 {
      get {
        return this._0;
      }
    }
    public T1 dtor__1 {
      get {
        return this._1;
      }
    }
    public T2 dtor__2 {
      get {
        return this._2;
      }
    }
    public T3 dtor__3 {
      get {
        return this._3;
      }
    }
    public T4 dtor__4 {
      get {
        return this._4;
      }
    }
    public T5 dtor__5 {
      get {
        return this._5;
      }
    }
    public T6 dtor__6 {
      get {
        return this._6;
      }
    }
    public T7 dtor__7 {
      get {
        return this._7;
      }
    }
    public T8 dtor__8 {
      get {
        return this._8;
      }
    }
    public T9 dtor__9 {
      get {
        return this._9;
      }
    }
    public T10 dtor__10 {
      get {
        return this._10;
      }
    }
    public T11 dtor__11 {
      get {
        return this._11;
      }
    }
    public T12 dtor__12 {
      get {
        return this._12;
      }
    }
    public T13 dtor__13 {
      get {
        return this._13;
      }
    }
    public T14 dtor__14 {
      get {
        return this._14;
      }
    }
    public T15 dtor__15 {
      get {
        return this._15;
      }
    }
    public T16 dtor__16 {
      get {
        return this._16;
      }
    }
    public T17 dtor__17 {
      get {
        return this._17;
      }
    }
    public T18 dtor__18 {
      get {
        return this._18;
      }
    }
  }

  public interface _ITuple20<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12, out T13, out T14, out T15, out T16, out T17, out T18, out T19> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    T13 dtor__13 { get; }
    T14 dtor__14 { get; }
    T15 dtor__15 { get; }
    T16 dtor__16 { get; }
    T17 dtor__17 { get; }
    T18 dtor__18 { get; }
    T19 dtor__19 { get; }
    _ITuple20<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18, __T19> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18, __T19>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16, Func<T17, __T17> converter17, Func<T18, __T18> converter18, Func<T19, __T19> converter19);
  }
  public class Tuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19> : _ITuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19> {
    public readonly T0 _0;
    public readonly T1 _1;
    public readonly T2 _2;
    public readonly T3 _3;
    public readonly T4 _4;
    public readonly T5 _5;
    public readonly T6 _6;
    public readonly T7 _7;
    public readonly T8 _8;
    public readonly T9 _9;
    public readonly T10 _10;
    public readonly T11 _11;
    public readonly T12 _12;
    public readonly T13 _13;
    public readonly T14 _14;
    public readonly T15 _15;
    public readonly T16 _16;
    public readonly T17 _17;
    public readonly T18 _18;
    public readonly T19 _19;
    public Tuple20(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17, T18 _18, T19 _19) {
      this._0 = _0;
      this._1 = _1;
      this._2 = _2;
      this._3 = _3;
      this._4 = _4;
      this._5 = _5;
      this._6 = _6;
      this._7 = _7;
      this._8 = _8;
      this._9 = _9;
      this._10 = _10;
      this._11 = _11;
      this._12 = _12;
      this._13 = _13;
      this._14 = _14;
      this._15 = _15;
      this._16 = _16;
      this._17 = _17;
      this._18 = _18;
      this._19 = _19;
    }
    public _ITuple20<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18, __T19> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18, __T19>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16, Func<T17, __T17> converter17, Func<T18, __T18> converter18, Func<T19, __T19> converter19) {
      if (this is _ITuple20<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18, __T19> dt) { return dt; }
      return new Tuple20<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18, __T19>(converter0(_0), converter1(_1), converter2(_2), converter3(_3), converter4(_4), converter5(_5), converter6(_6), converter7(_7), converter8(_8), converter9(_9), converter10(_10), converter11(_11), converter12(_12), converter13(_13), converter14(_14), converter15(_15), converter16(_16), converter17(_17), converter18(_18), converter19(_19));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19>;
      return oth != null && object.Equals(this._0, oth._0) && object.Equals(this._1, oth._1) && object.Equals(this._2, oth._2) && object.Equals(this._3, oth._3) && object.Equals(this._4, oth._4) && object.Equals(this._5, oth._5) && object.Equals(this._6, oth._6) && object.Equals(this._7, oth._7) && object.Equals(this._8, oth._8) && object.Equals(this._9, oth._9) && object.Equals(this._10, oth._10) && object.Equals(this._11, oth._11) && object.Equals(this._12, oth._12) && object.Equals(this._13, oth._13) && object.Equals(this._14, oth._14) && object.Equals(this._15, oth._15) && object.Equals(this._16, oth._16) && object.Equals(this._17, oth._17) && object.Equals(this._18, oth._18) && object.Equals(this._19, oth._19);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._12));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._13));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._14));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._15));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._16));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._17));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._18));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._19));
      return (int)hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this._0);
      s += ", ";
      s += Dafny.Helpers.ToString(this._1);
      s += ", ";
      s += Dafny.Helpers.ToString(this._2);
      s += ", ";
      s += Dafny.Helpers.ToString(this._3);
      s += ", ";
      s += Dafny.Helpers.ToString(this._4);
      s += ", ";
      s += Dafny.Helpers.ToString(this._5);
      s += ", ";
      s += Dafny.Helpers.ToString(this._6);
      s += ", ";
      s += Dafny.Helpers.ToString(this._7);
      s += ", ";
      s += Dafny.Helpers.ToString(this._8);
      s += ", ";
      s += Dafny.Helpers.ToString(this._9);
      s += ", ";
      s += Dafny.Helpers.ToString(this._10);
      s += ", ";
      s += Dafny.Helpers.ToString(this._11);
      s += ", ";
      s += Dafny.Helpers.ToString(this._12);
      s += ", ";
      s += Dafny.Helpers.ToString(this._13);
      s += ", ";
      s += Dafny.Helpers.ToString(this._14);
      s += ", ";
      s += Dafny.Helpers.ToString(this._15);
      s += ", ";
      s += Dafny.Helpers.ToString(this._16);
      s += ", ";
      s += Dafny.Helpers.ToString(this._17);
      s += ", ";
      s += Dafny.Helpers.ToString(this._18);
      s += ", ";
      s += Dafny.Helpers.ToString(this._19);
      s += ")";
      return s;
    }
    public static _ITuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12, T13 _default_T13, T14 _default_T14, T15 _default_T15, T16 _default_T16, T17 _default_T17, T18 _default_T18, T19 _default_T19) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12, _default_T13, _default_T14, _default_T15, _default_T16, _default_T17, _default_T18, _default_T19);
    }
    public static Dafny.TypeDescriptor<_System._ITuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12, Dafny.TypeDescriptor<T13> _td_T13, Dafny.TypeDescriptor<T14> _td_T14, Dafny.TypeDescriptor<T15> _td_T15, Dafny.TypeDescriptor<T16> _td_T16, Dafny.TypeDescriptor<T17> _td_T17, Dafny.TypeDescriptor<T18> _td_T18, Dafny.TypeDescriptor<T19> _td_T19) {
      return new Dafny.TypeDescriptor<_System._ITuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19>>(_System.Tuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default(), _td_T13.Default(), _td_T14.Default(), _td_T15.Default(), _td_T16.Default(), _td_T17.Default(), _td_T18.Default(), _td_T19.Default()));
    }
    public static _ITuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17, T18 _18, T19 _19) {
      return new Tuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, _19);
    }
    public T0 dtor__0 {
      get {
        return this._0;
      }
    }
    public T1 dtor__1 {
      get {
        return this._1;
      }
    }
    public T2 dtor__2 {
      get {
        return this._2;
      }
    }
    public T3 dtor__3 {
      get {
        return this._3;
      }
    }
    public T4 dtor__4 {
      get {
        return this._4;
      }
    }
    public T5 dtor__5 {
      get {
        return this._5;
      }
    }
    public T6 dtor__6 {
      get {
        return this._6;
      }
    }
    public T7 dtor__7 {
      get {
        return this._7;
      }
    }
    public T8 dtor__8 {
      get {
        return this._8;
      }
    }
    public T9 dtor__9 {
      get {
        return this._9;
      }
    }
    public T10 dtor__10 {
      get {
        return this._10;
      }
    }
    public T11 dtor__11 {
      get {
        return this._11;
      }
    }
    public T12 dtor__12 {
      get {
        return this._12;
      }
    }
    public T13 dtor__13 {
      get {
        return this._13;
      }
    }
    public T14 dtor__14 {
      get {
        return this._14;
      }
    }
    public T15 dtor__15 {
      get {
        return this._15;
      }
    }
    public T16 dtor__16 {
      get {
        return this._16;
      }
    }
    public T17 dtor__17 {
      get {
        return this._17;
      }
    }
    public T18 dtor__18 {
      get {
        return this._18;
      }
    }
    public T19 dtor__19 {
      get {
        return this._19;
      }
    }
  }
} // end of namespace _System
namespace Dafny {
  internal class ArrayHelpers {
    public static T[] InitNewArray1<T>(T z, BigInteger size0) {
      int s0 = (int)size0;
      T[] a = new T[s0];
      for (int i0 = 0; i0 < s0; i0++) {
        a[i0] = z;
      }
      return a;
    }
  }
} // end of namespace Dafny
public static class FuncExtensions {
  public static Func<U, UResult> DowncastClone<T, TResult, U, UResult>(this Func<T, TResult> F, Func<U, T> ArgConv, Func<TResult, UResult> ResConv) {
    return arg => ResConv(F(ArgConv(arg)));
  }
  public static Func<UResult> DowncastClone<TResult, UResult>(this Func<TResult> F, Func<TResult, UResult> ResConv) {
    return () => ResConv(F());
  }
  public static Func<U1, U2, UResult> DowncastClone<T1, T2, TResult, U1, U2, UResult>(this Func<T1, T2, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<TResult, UResult> ResConv) {
    return (arg1, arg2) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2)));
  }
  public static Func<U1, U2, U3, UResult> DowncastClone<T1, T2, T3, TResult, U1, U2, U3, UResult>(this Func<T1, T2, T3, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3)));
  }
}
namespace _System {

  public partial class nat {
    private static readonly Dafny.TypeDescriptor<BigInteger> _TYPE = new Dafny.TypeDescriptor<BigInteger>(BigInteger.Zero);
    public static Dafny.TypeDescriptor<BigInteger> _TypeDescriptor() {
      return _TYPE;
    }
  }
} // end of namespace _System
namespace BoundedInts_Compile {

  public partial class uint8 {
    public static System.Collections.Generic.IEnumerable<byte> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (byte)j; }
    }
    private static readonly Dafny.TypeDescriptor<byte> _TYPE = new Dafny.TypeDescriptor<byte>(0);
    public static Dafny.TypeDescriptor<byte> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class uint16 {
    public static System.Collections.Generic.IEnumerable<ushort> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (ushort)j; }
    }
    private static readonly Dafny.TypeDescriptor<ushort> _TYPE = new Dafny.TypeDescriptor<ushort>(0);
    public static Dafny.TypeDescriptor<ushort> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class uint32 {
    public static System.Collections.Generic.IEnumerable<uint> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (uint)j; }
    }
    private static readonly Dafny.TypeDescriptor<uint> _TYPE = new Dafny.TypeDescriptor<uint>(0);
    public static Dafny.TypeDescriptor<uint> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class uint64 {
    public static System.Collections.Generic.IEnumerable<ulong> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (ulong)j; }
    }
    private static readonly Dafny.TypeDescriptor<ulong> _TYPE = new Dafny.TypeDescriptor<ulong>(0);
    public static Dafny.TypeDescriptor<ulong> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class int8 {
    public static System.Collections.Generic.IEnumerable<sbyte> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (sbyte)j; }
    }
    private static readonly Dafny.TypeDescriptor<sbyte> _TYPE = new Dafny.TypeDescriptor<sbyte>(0);
    public static Dafny.TypeDescriptor<sbyte> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class int16 {
    public static System.Collections.Generic.IEnumerable<short> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (short)j; }
    }
    private static readonly Dafny.TypeDescriptor<short> _TYPE = new Dafny.TypeDescriptor<short>(0);
    public static Dafny.TypeDescriptor<short> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class int32 {
    public static System.Collections.Generic.IEnumerable<int> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (int)j; }
    }
    private static readonly Dafny.TypeDescriptor<int> _TYPE = new Dafny.TypeDescriptor<int>(0);
    public static Dafny.TypeDescriptor<int> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class int64 {
    public static System.Collections.Generic.IEnumerable<long> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (long)j; }
    }
    private static readonly Dafny.TypeDescriptor<long> _TYPE = new Dafny.TypeDescriptor<long>(0);
    public static Dafny.TypeDescriptor<long> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class nat8 {
    public static System.Collections.Generic.IEnumerable<byte> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (byte)j; }
    }
    private static readonly Dafny.TypeDescriptor<byte> _TYPE = new Dafny.TypeDescriptor<byte>(0);
    public static Dafny.TypeDescriptor<byte> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class nat16 {
    public static System.Collections.Generic.IEnumerable<ushort> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (ushort)j; }
    }
    private static readonly Dafny.TypeDescriptor<ushort> _TYPE = new Dafny.TypeDescriptor<ushort>(0);
    public static Dafny.TypeDescriptor<ushort> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class nat32 {
    public static System.Collections.Generic.IEnumerable<uint> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (uint)j; }
    }
    private static readonly Dafny.TypeDescriptor<uint> _TYPE = new Dafny.TypeDescriptor<uint>(0);
    public static Dafny.TypeDescriptor<uint> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class nat64 {
    public static System.Collections.Generic.IEnumerable<ulong> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (ulong)j; }
    }
    private static readonly Dafny.TypeDescriptor<ulong> _TYPE = new Dafny.TypeDescriptor<ulong>(0);
    public static Dafny.TypeDescriptor<ulong> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class __default {
    public static BigInteger TWO__TO__THE__8 { get {
      return new BigInteger(256);
    } }
    public static BigInteger TWO__TO__THE__16 { get {
      return new BigInteger(65536);
    } }
    public static BigInteger TWO__TO__THE__32 { get {
      return new BigInteger(4294967296L);
    } }
    public static BigInteger TWO__TO__THE__64 { get {
      return BigInteger.Parse("18446744073709551616");
    } }
    public static BigInteger TWO__TO__THE__0 { get {
      return BigInteger.One;
    } }
    public static BigInteger TWO__TO__THE__1 { get {
      return new BigInteger(2);
    } }
    public static BigInteger TWO__TO__THE__2 { get {
      return new BigInteger(4);
    } }
    public static BigInteger TWO__TO__THE__4 { get {
      return new BigInteger(16);
    } }
    public static BigInteger TWO__TO__THE__5 { get {
      return new BigInteger(32);
    } }
    public static BigInteger TWO__TO__THE__24 { get {
      return new BigInteger(16777216);
    } }
    public static BigInteger TWO__TO__THE__40 { get {
      return new BigInteger(1099511627776L);
    } }
    public static BigInteger TWO__TO__THE__48 { get {
      return new BigInteger(281474976710656L);
    } }
    public static BigInteger TWO__TO__THE__56 { get {
      return new BigInteger(72057594037927936L);
    } }
    public static BigInteger TWO__TO__THE__128 { get {
      return BigInteger.Parse("340282366920938463463374607431768211456");
    } }
    public static BigInteger TWO__TO__THE__256 { get {
      return BigInteger.Parse("115792089237316195423570985008687907853269984665640564039457584007913129639936");
    } }
    public static BigInteger TWO__TO__THE__512 { get {
      return BigInteger.Parse("13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096");
    } }
  }
} // end of namespace BoundedInts_Compile
namespace srcBoundedIntsdfyUnitTests_Compile {

} // end of namespace srcBoundedIntsdfyUnitTests_Compile
namespace GeneralInternals_Compile {

} // end of namespace GeneralInternals_Compile
namespace MulInternalsNonlinear_Compile {

} // end of namespace MulInternalsNonlinear_Compile
namespace MulInternals_Compile {

  public partial class __default {
    public static BigInteger MulPos(BigInteger x, BigInteger y)
    {
      BigInteger _0___accumulator = BigInteger.Zero;
    TAIL_CALL_START: ;
      if ((x).Sign == 0) {
        return (BigInteger.Zero) + (_0___accumulator);
      } else {
        _0___accumulator = (_0___accumulator) + (y);
        BigInteger _in0 = (x) - (BigInteger.One);
        BigInteger _in1 = y;
        x = _in0;
        y = _in1;
        goto TAIL_CALL_START;
      }
    }
    public static BigInteger MulRecursive(BigInteger x, BigInteger y)
    {
      if ((x).Sign != -1) {
        return MulInternals_Compile.__default.MulPos(x, y);
      } else {
        return (new BigInteger(-1)) * (MulInternals_Compile.__default.MulPos((new BigInteger(-1)) * (x), y));
      }
    }
  }
} // end of namespace MulInternals_Compile
namespace Mul_Compile {

} // end of namespace Mul_Compile
namespace ModInternalsNonlinear_Compile {

} // end of namespace ModInternalsNonlinear_Compile
namespace DivInternalsNonlinear_Compile {

} // end of namespace DivInternalsNonlinear_Compile
namespace ModInternals_Compile {

  public partial class __default {
    public static BigInteger ModRecursive(BigInteger x, BigInteger d)
    {
    TAIL_CALL_START: ;
      if ((x).Sign == -1) {
        BigInteger _in2 = (d) + (x);
        BigInteger _in3 = d;
        x = _in2;
        d = _in3;
        goto TAIL_CALL_START;
      } else if ((x) < (d)) {
        return x;
      } else {
        BigInteger _in4 = (x) - (d);
        BigInteger _in5 = d;
        x = _in4;
        d = _in5;
        goto TAIL_CALL_START;
      }
    }
  }
} // end of namespace ModInternals_Compile
namespace DivInternals_Compile {

  public partial class __default {
    public static BigInteger DivPos(BigInteger x, BigInteger d)
    {
      BigInteger _1___accumulator = BigInteger.Zero;
    TAIL_CALL_START: ;
      if ((x).Sign == -1) {
        _1___accumulator = (_1___accumulator) + (new BigInteger(-1));
        BigInteger _in6 = (x) + (d);
        BigInteger _in7 = d;
        x = _in6;
        d = _in7;
        goto TAIL_CALL_START;
      } else if ((x) < (d)) {
        return (BigInteger.Zero) + (_1___accumulator);
      } else {
        _1___accumulator = (_1___accumulator) + (BigInteger.One);
        BigInteger _in8 = (x) - (d);
        BigInteger _in9 = d;
        x = _in8;
        d = _in9;
        goto TAIL_CALL_START;
      }
    }
    public static BigInteger DivRecursive(BigInteger x, BigInteger d)
    {
      if ((d).Sign == 1) {
        return DivInternals_Compile.__default.DivPos(x, d);
      } else {
        return (new BigInteger(-1)) * (DivInternals_Compile.__default.DivPos(x, (new BigInteger(-1)) * (d)));
      }
    }
  }
} // end of namespace DivInternals_Compile
namespace srcNonlinearArithmeticInternalsDivInternalsdfyUnitTests_Compile {

  public partial class __default {
    [Xunit.Fact]
    public static void test0()
    {
      if (!((new BigInteger(1797)).Sign == 1)) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/NonlinearArithmetic/Internals/DivInternals.dfy(22,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      BigInteger _2_r0;
      _2_r0 = DivInternals_Compile.__default.DivPos(new BigInteger(-1798), new BigInteger(1797));
    }
    [Xunit.Fact]
    public static void test1()
    {
      if (!((new BigInteger(2460)).Sign == 1)) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/NonlinearArithmetic/Internals/DivInternals.dfy(30,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      BigInteger _3_r0;
      _3_r0 = DivInternals_Compile.__default.DivPos(new BigInteger(4417), new BigInteger(2460));
    }
    [Xunit.Fact]
    public static void test2()
    {
      if (!((BigInteger.One).Sign == 1)) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/NonlinearArithmetic/Internals/DivInternals.dfy(38,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      BigInteger _4_r0;
      _4_r0 = DivInternals_Compile.__default.DivPos(BigInteger.Zero, BigInteger.One);
    }
    [Xunit.Fact]
    public static void test3()
    {
      if (!((new BigInteger(11)).Sign != 0)) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/NonlinearArithmetic/Internals/DivInternals.dfy(47,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      BigInteger _5_r0;
      _5_r0 = DivInternals_Compile.__default.DivRecursive(BigInteger.Zero, new BigInteger(11));
    }
  }
} // end of namespace srcNonlinearArithmeticInternalsDivInternalsdfyUnitTests_Compile
namespace srcNonlinearArithmeticInternalsDivInternalsNonlineardfyUnitTests_Compile {

} // end of namespace srcNonlinearArithmeticInternalsDivInternalsNonlineardfyUnitTests_Compile
namespace DivMod_Compile {

} // end of namespace DivMod_Compile
namespace srcNonlinearArithmeticDivModdfyUnitTests_Compile {

} // end of namespace srcNonlinearArithmeticDivModdfyUnitTests_Compile
namespace Functions_Compile {

} // end of namespace Functions_Compile
namespace srcFunctionsdfyUnitTests_Compile {

} // end of namespace srcFunctionsdfyUnitTests_Compile
namespace srcNonlinearArithmeticInternalsGeneralInternalsdfyUnitTests_Compile {

} // end of namespace srcNonlinearArithmeticInternalsGeneralInternalsdfyUnitTests_Compile
namespace Wrappers_Compile {

  public interface _IOption<out T> {
    bool is_None { get; }
    bool is_Some { get; }
    T dtor_value { get; }
    _IOption<__T> DowncastClone<__T>(Func<T, __T> converter0);
    Wrappers_Compile._IResult<T, Dafny.ISequence<char>> ToResult();
    bool IsFailure();
    Wrappers_Compile._IOption<__U> PropagateFailure<__U>();
    T Extract();
  }
  public abstract class Option<T> : _IOption<T> {
    public Option() { }
    public static _IOption<T> Default() {
      return create_None();
    }
    public static Dafny.TypeDescriptor<Wrappers_Compile._IOption<T>> _TypeDescriptor() {
      return new Dafny.TypeDescriptor<Wrappers_Compile._IOption<T>>(Wrappers_Compile.Option<T>.Default());
    }
    public static _IOption<T> create_None() {
      return new Option_None<T>();
    }
    public static _IOption<T> create_Some(T @value) {
      return new Option_Some<T>(@value);
    }
    public bool is_None { get { return this is Option_None<T>; } }
    public bool is_Some { get { return this is Option_Some<T>; } }
    public T dtor_value {
      get {
        var d = this;
        return ((Option_Some<T>)d).@value;
      }
    }
    public abstract _IOption<__T> DowncastClone<__T>(Func<T, __T> converter0);
    public Wrappers_Compile._IResult<T, Dafny.ISequence<char>> ToResult() {
      Wrappers_Compile._IOption<T> _source0 = this;
      if (_source0.is_None) {
        return Wrappers_Compile.Result<T, Dafny.ISequence<char>>.create_Failure(Dafny.Sequence<char>.FromString("Option is None"));
      } else {
        T _6___mcc_h0 = _source0.dtor_value;
        T _7_v = _6___mcc_h0;
        return Wrappers_Compile.Result<T, Dafny.ISequence<char>>.create_Success(_7_v);
      }
    }
    public static T UnwrapOr(Wrappers_Compile._IOption<T> _this, T @default) {
      Wrappers_Compile._IOption<T> _source1 = _this;
      if (_source1.is_None) {
        return @default;
      } else {
        T _8___mcc_h0 = _source1.dtor_value;
        T _9_v = _8___mcc_h0;
        return _9_v;
      }
    }
    public bool IsFailure() {
      return (this).is_None;
    }
    public Wrappers_Compile._IOption<__U> PropagateFailure<__U>() {
      return Wrappers_Compile.Option<__U>.create_None();
    }
    public T Extract() {
      return (this).dtor_value;
    }
  }
  public class Option_None<T> : Option<T> {
    public Option_None() {
    }
    public override _IOption<__T> DowncastClone<__T>(Func<T, __T> converter0) {
      if (this is _IOption<__T> dt) { return dt; }
      return new Option_None<__T>();
    }
    public override bool Equals(object other) {
      var oth = other as Wrappers_Compile.Option_None<T>;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Wrappers_Compile.Option.None";
      return s;
    }
  }
  public class Option_Some<T> : Option<T> {
    public readonly T @value;
    public Option_Some(T @value) {
      this.@value = @value;
    }
    public override _IOption<__T> DowncastClone<__T>(Func<T, __T> converter0) {
      if (this is _IOption<__T> dt) { return dt; }
      return new Option_Some<__T>(converter0(@value));
    }
    public override bool Equals(object other) {
      var oth = other as Wrappers_Compile.Option_Some<T>;
      return oth != null && object.Equals(this.@value, oth.@value);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.@value));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Wrappers_Compile.Option.Some";
      s += "(";
      s += Dafny.Helpers.ToString(this.@value);
      s += ")";
      return s;
    }
  }

  public interface _IResult<out T, out R> {
    bool is_Success { get; }
    bool is_Failure { get; }
    T dtor_value { get; }
    R dtor_error { get; }
    _IResult<__T, __R> DowncastClone<__T, __R>(Func<T, __T> converter0, Func<R, __R> converter1);
    Wrappers_Compile._IOption<T> ToOption();
    bool IsFailure();
    Wrappers_Compile._IResult<__U, R> PropagateFailure<__U>();
    T Extract();
  }
  public abstract class Result<T, R> : _IResult<T, R> {
    public Result() { }
    public static _IResult<T, R> Default(T _default_T) {
      return create_Success(_default_T);
    }
    public static Dafny.TypeDescriptor<Wrappers_Compile._IResult<T, R>> _TypeDescriptor(Dafny.TypeDescriptor<T> _td_T) {
      return new Dafny.TypeDescriptor<Wrappers_Compile._IResult<T, R>>(Wrappers_Compile.Result<T, R>.Default(_td_T.Default()));
    }
    public static _IResult<T, R> create_Success(T @value) {
      return new Result_Success<T, R>(@value);
    }
    public static _IResult<T, R> create_Failure(R error) {
      return new Result_Failure<T, R>(error);
    }
    public bool is_Success { get { return this is Result_Success<T, R>; } }
    public bool is_Failure { get { return this is Result_Failure<T, R>; } }
    public T dtor_value {
      get {
        var d = this;
        return ((Result_Success<T, R>)d).@value;
      }
    }
    public R dtor_error {
      get {
        var d = this;
        return ((Result_Failure<T, R>)d).error;
      }
    }
    public abstract _IResult<__T, __R> DowncastClone<__T, __R>(Func<T, __T> converter0, Func<R, __R> converter1);
    public Wrappers_Compile._IOption<T> ToOption() {
      Wrappers_Compile._IResult<T, R> _source2 = this;
      if (_source2.is_Success) {
        T _10___mcc_h0 = _source2.dtor_value;
        T _11_s = _10___mcc_h0;
        return Wrappers_Compile.Option<T>.create_Some(_11_s);
      } else {
        R _12___mcc_h1 = _source2.dtor_error;
        R _13_e = _12___mcc_h1;
        return Wrappers_Compile.Option<T>.create_None();
      }
    }
    public static T UnwrapOr(Wrappers_Compile._IResult<T, R> _this, T @default) {
      Wrappers_Compile._IResult<T, R> _source3 = _this;
      if (_source3.is_Success) {
        T _14___mcc_h0 = _source3.dtor_value;
        T _15_s = _14___mcc_h0;
        return _15_s;
      } else {
        R _16___mcc_h1 = _source3.dtor_error;
        R _17_e = _16___mcc_h1;
        return @default;
      }
    }
    public bool IsFailure() {
      return (this).is_Failure;
    }
    public Wrappers_Compile._IResult<__U, R> PropagateFailure<__U>() {
      return Wrappers_Compile.Result<__U, R>.create_Failure((this).dtor_error);
    }
    public static Wrappers_Compile._IResult<T, __NewR> MapFailure<__NewR>(Wrappers_Compile._IResult<T, R> _this, Func<R, __NewR> reWrap) {
      Wrappers_Compile._IResult<T, R> _source4 = _this;
      if (_source4.is_Success) {
        T _18___mcc_h0 = _source4.dtor_value;
        T _19_s = _18___mcc_h0;
        return Wrappers_Compile.Result<T, __NewR>.create_Success(_19_s);
      } else {
        R _20___mcc_h1 = _source4.dtor_error;
        R _21_e = _20___mcc_h1;
        return Wrappers_Compile.Result<T, __NewR>.create_Failure(Dafny.Helpers.Id<Func<R, __NewR>>(reWrap)(_21_e));
      }
    }
    public T Extract() {
      return (this).dtor_value;
    }
  }
  public class Result_Success<T, R> : Result<T, R> {
    public readonly T @value;
    public Result_Success(T @value) {
      this.@value = @value;
    }
    public override _IResult<__T, __R> DowncastClone<__T, __R>(Func<T, __T> converter0, Func<R, __R> converter1) {
      if (this is _IResult<__T, __R> dt) { return dt; }
      return new Result_Success<__T, __R>(converter0(@value));
    }
    public override bool Equals(object other) {
      var oth = other as Wrappers_Compile.Result_Success<T, R>;
      return oth != null && object.Equals(this.@value, oth.@value);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.@value));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Wrappers_Compile.Result.Success";
      s += "(";
      s += Dafny.Helpers.ToString(this.@value);
      s += ")";
      return s;
    }
  }
  public class Result_Failure<T, R> : Result<T, R> {
    public readonly R error;
    public Result_Failure(R error) {
      this.error = error;
    }
    public override _IResult<__T, __R> DowncastClone<__T, __R>(Func<T, __T> converter0, Func<R, __R> converter1) {
      if (this is _IResult<__T, __R> dt) { return dt; }
      return new Result_Failure<__T, __R>(converter1(error));
    }
    public override bool Equals(object other) {
      var oth = other as Wrappers_Compile.Result_Failure<T, R>;
      return oth != null && object.Equals(this.error, oth.error);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.error));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Wrappers_Compile.Result.Failure";
      s += "(";
      s += Dafny.Helpers.ToString(this.error);
      s += ")";
      return s;
    }
  }

  public interface _IOutcome<E> {
    bool is_Pass { get; }
    bool is_Fail { get; }
    E dtor_error { get; }
    _IOutcome<__E> DowncastClone<__E>(Func<E, __E> converter0);
    bool IsFailure();
    Wrappers_Compile._IResult<__U, E> PropagateFailure<__U>();
  }
  public abstract class Outcome<E> : _IOutcome<E> {
    public Outcome() { }
    public static _IOutcome<E> Default() {
      return create_Pass();
    }
    public static Dafny.TypeDescriptor<Wrappers_Compile._IOutcome<E>> _TypeDescriptor() {
      return new Dafny.TypeDescriptor<Wrappers_Compile._IOutcome<E>>(Wrappers_Compile.Outcome<E>.Default());
    }
    public static _IOutcome<E> create_Pass() {
      return new Outcome_Pass<E>();
    }
    public static _IOutcome<E> create_Fail(E error) {
      return new Outcome_Fail<E>(error);
    }
    public bool is_Pass { get { return this is Outcome_Pass<E>; } }
    public bool is_Fail { get { return this is Outcome_Fail<E>; } }
    public E dtor_error {
      get {
        var d = this;
        return ((Outcome_Fail<E>)d).error;
      }
    }
    public abstract _IOutcome<__E> DowncastClone<__E>(Func<E, __E> converter0);
    public bool IsFailure() {
      return (this).is_Fail;
    }
    public Wrappers_Compile._IResult<__U, E> PropagateFailure<__U>() {
      return Wrappers_Compile.Result<__U, E>.create_Failure((this).dtor_error);
    }
  }
  public class Outcome_Pass<E> : Outcome<E> {
    public Outcome_Pass() {
    }
    public override _IOutcome<__E> DowncastClone<__E>(Func<E, __E> converter0) {
      if (this is _IOutcome<__E> dt) { return dt; }
      return new Outcome_Pass<__E>();
    }
    public override bool Equals(object other) {
      var oth = other as Wrappers_Compile.Outcome_Pass<E>;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Wrappers_Compile.Outcome.Pass";
      return s;
    }
  }
  public class Outcome_Fail<E> : Outcome<E> {
    public readonly E error;
    public Outcome_Fail(E error) {
      this.error = error;
    }
    public override _IOutcome<__E> DowncastClone<__E>(Func<E, __E> converter0) {
      if (this is _IOutcome<__E> dt) { return dt; }
      return new Outcome_Fail<__E>(converter0(error));
    }
    public override bool Equals(object other) {
      var oth = other as Wrappers_Compile.Outcome_Fail<E>;
      return oth != null && object.Equals(this.error, oth.error);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.error));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Wrappers_Compile.Outcome.Fail";
      s += "(";
      s += Dafny.Helpers.ToString(this.error);
      s += ")";
      return s;
    }
  }

  public partial class __default {
    public static Wrappers_Compile._IOutcome<__E> Need<__E>(bool condition, __E error)
    {
      if (condition) {
        return Wrappers_Compile.Outcome<__E>.create_Pass();
      } else {
        return Wrappers_Compile.Outcome<__E>.create_Fail(error);
      }
    }
  }
} // end of namespace Wrappers_Compile
namespace Imaps_Compile {

  public partial class __default {
    public static Wrappers_Compile._IOption<__Y> Get<__X, __Y>(Dafny.IMap<__X,__Y> m, __X x)
    {
      if ((m).Contains((x))) {
        return Wrappers_Compile.Option<__Y>.create_Some(Dafny.Map<__X, __Y>.Select(m,x));
      } else {
        return Wrappers_Compile.Option<__Y>.create_None();
      }
    }
  }
} // end of namespace Imaps_Compile
namespace srcCollectionsMapsImapsdfyUnitTests_Compile {

  public partial class __default {
    [Xunit.Fact]
    public static void test0()
    {
      Dafny.IMap<BigInteger,BigInteger> _22_d0;
      _22_d0 = Dafny.Map<BigInteger, BigInteger>.FromElements();
      Wrappers_Compile._IOption<BigInteger> _23_r0;
      _23_r0 = Imaps_Compile.__default.Get<BigInteger, BigInteger>(_22_d0, BigInteger.Zero);
    }
  }
} // end of namespace srcCollectionsMapsImapsdfyUnitTests_Compile
namespace Isets_Compile {

} // end of namespace Isets_Compile
namespace srcCollectionsSetsIsetsdfyUnitTests_Compile {

} // end of namespace srcCollectionsSetsIsetsdfyUnitTests_Compile
namespace Power_Compile {

  public partial class __default {
    public static BigInteger Pow(BigInteger b, BigInteger e)
    {
      BigInteger _24___accumulator = BigInteger.One;
    TAIL_CALL_START: ;
      if ((e).Sign == 0) {
        return (BigInteger.One) * (_24___accumulator);
      } else {
        _24___accumulator = (_24___accumulator) * (b);
        BigInteger _in10 = b;
        BigInteger _in11 = (e) - (BigInteger.One);
        b = _in10;
        e = _in11;
        goto TAIL_CALL_START;
      }
    }
  }
} // end of namespace Power_Compile
namespace Math_Compile {

  public partial class __default {
    public static BigInteger Min(BigInteger a, BigInteger b)
    {
      if ((a) < (b)) {
        return a;
      } else {
        return b;
      }
    }
    public static BigInteger Max(BigInteger a, BigInteger b)
    {
      if ((a) < (b)) {
        return b;
      } else {
        return a;
      }
    }
  }
} // end of namespace Math_Compile
namespace Seq_Compile {

  public partial class __default {
    public static __T First<__T>(Dafny.ISequence<__T> s) {
      return (s).Select(BigInteger.Zero);
    }
    public static Dafny.ISequence<__T> DropFirst<__T>(Dafny.ISequence<__T> s) {
      return (s).Drop(BigInteger.One);
    }
    public static __T Last<__T>(Dafny.ISequence<__T> s) {
      return (s).Select((new BigInteger((s).Count)) - (BigInteger.One));
    }
    public static Dafny.ISequence<__T> DropLast<__T>(Dafny.ISequence<__T> s) {
      return (s).Take((new BigInteger((s).Count)) - (BigInteger.One));
    }
    public static __T[] ToArray<__T>(Dafny.ISequence<__T> s)
    {
      __T[] a = new __T[0];
      __T[] _nw0 = new __T[Dafny.Helpers.ToIntChecked(Dafny.Helpers.ToIntChecked(new BigInteger((s).Count), "C# arrays may not be larger than the max 32-bit integer"),"C# array size must not be larger than max 32-bit int")];
      Func<BigInteger, __T> _arrayinit0 = Dafny.Helpers.Id<Func<Dafny.ISequence<__T>, Func<BigInteger, __T>>>((_25_s) => ((System.Func<BigInteger, __T>)((_26_i) => {
        return (_25_s).Select(_26_i);
      })))(s);
      for (var _arrayinit_00 = 0; _arrayinit_00 < new BigInteger(_nw0.Length); _arrayinit_00++) {
        _nw0[(int)(_arrayinit_00)] = _arrayinit0(_arrayinit_00);
      }
      a = _nw0;
      return a;
    }
    public static Dafny.ISet<__T> ToSet<__T>(Dafny.ISequence<__T> s) {
      return Dafny.Helpers.Id<Func<Dafny.ISequence<__T>, Dafny.ISet<__T>>>((_27_s) => ((System.Func<Dafny.ISet<__T>>)(() => {
        var _coll0 = new System.Collections.Generic.List<__T>();
        foreach (__T _compr_0 in (_27_s).Elements) {
          __T _28_x = (__T)_compr_0;
          if ((_27_s).Contains((_28_x))) {
            _coll0.Add(_28_x);
          }
        }
        return Dafny.Set<__T>.FromCollection(_coll0);
      }))())(s);
    }
    public static BigInteger IndexOf<__T>(Dafny.ISequence<__T> s, __T v)
    {
      BigInteger _29___accumulator = BigInteger.Zero;
    TAIL_CALL_START: ;
      if (object.Equals((s).Select(BigInteger.Zero), v)) {
        return (BigInteger.Zero) + (_29___accumulator);
      } else {
        _29___accumulator = (_29___accumulator) + (BigInteger.One);
        Dafny.ISequence<__T> _in12 = (s).Drop(BigInteger.One);
        __T _in13 = v;
        s = _in12;
        v = _in13;
        goto TAIL_CALL_START;
      }
    }
    public static Wrappers_Compile._IOption<BigInteger> IndexOfOption<__T>(Dafny.ISequence<__T> s, __T v)
    {
      if ((new BigInteger((s).Count)).Sign == 0) {
        return Wrappers_Compile.Option<BigInteger>.create_None();
      } else if (object.Equals((s).Select(BigInteger.Zero), v)) {
        return Wrappers_Compile.Option<BigInteger>.create_Some(BigInteger.Zero);
      } else {
        Wrappers_Compile._IOption<BigInteger> _30_o_k = Seq_Compile.__default.IndexOfOption<__T>((s).Drop(BigInteger.One), v);
        if ((_30_o_k).is_Some) {
          return Wrappers_Compile.Option<BigInteger>.create_Some(((_30_o_k).dtor_value) + (BigInteger.One));
        } else {
          return Wrappers_Compile.Option<BigInteger>.create_None();
        }
      }
    }
    public static BigInteger LastIndexOf<__T>(Dafny.ISequence<__T> s, __T v)
    {
    TAIL_CALL_START: ;
      if (object.Equals((s).Select((new BigInteger((s).Count)) - (BigInteger.One)), v)) {
        return (new BigInteger((s).Count)) - (BigInteger.One);
      } else {
        Dafny.ISequence<__T> _in14 = (s).Take((new BigInteger((s).Count)) - (BigInteger.One));
        __T _in15 = v;
        s = _in14;
        v = _in15;
        goto TAIL_CALL_START;
      }
    }
    public static Wrappers_Compile._IOption<BigInteger> LastIndexOfOption<__T>(Dafny.ISequence<__T> s, __T v)
    {
    TAIL_CALL_START: ;
      if ((new BigInteger((s).Count)).Sign == 0) {
        return Wrappers_Compile.Option<BigInteger>.create_None();
      } else if (object.Equals((s).Select((new BigInteger((s).Count)) - (BigInteger.One)), v)) {
        return Wrappers_Compile.Option<BigInteger>.create_Some((new BigInteger((s).Count)) - (BigInteger.One));
      } else {
        Dafny.ISequence<__T> _in16 = (s).Take((new BigInteger((s).Count)) - (BigInteger.One));
        __T _in17 = v;
        s = _in16;
        v = _in17;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<__T> Remove<__T>(Dafny.ISequence<__T> s, BigInteger pos)
    {
      return Dafny.Sequence<__T>.Concat((s).Take(pos), (s).Drop((pos) + (BigInteger.One)));
    }
    public static Dafny.ISequence<__T> RemoveValue<__T>(Dafny.ISequence<__T> s, __T v)
    {
      if (!(s).Contains((v))) {
        return s;
      } else {
        BigInteger _31_i = Seq_Compile.__default.IndexOf<__T>(s, v);
        return Dafny.Sequence<__T>.Concat((s).Take(_31_i), (s).Drop((_31_i) + (BigInteger.One)));
      }
    }
    public static Dafny.ISequence<__T> Insert<__T>(Dafny.ISequence<__T> s, __T a, BigInteger pos)
    {
      return Dafny.Sequence<__T>.Concat(Dafny.Sequence<__T>.Concat((s).Take(pos), Dafny.Sequence<__T>.FromElements(a)), (s).Drop(pos));
    }
    public static Dafny.ISequence<__T> Reverse<__T>(Dafny.ISequence<__T> s) {
      Dafny.ISequence<__T> _32___accumulator = Dafny.Sequence<__T>.FromElements();
    TAIL_CALL_START: ;
      if ((s).Equals((Dafny.Sequence<__T>.FromElements()))) {
        return Dafny.Sequence<__T>.Concat(_32___accumulator, Dafny.Sequence<__T>.FromElements());
      } else {
        _32___accumulator = Dafny.Sequence<__T>.Concat(_32___accumulator, Dafny.Sequence<__T>.FromElements((s).Select((new BigInteger((s).Count)) - (BigInteger.One))));
        Dafny.ISequence<__T> _in18 = (s).Subsequence(BigInteger.Zero, (new BigInteger((s).Count)) - (BigInteger.One));
        s = _in18;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<__T> Repeat<__T>(__T v, BigInteger length)
    {
      Dafny.ISequence<__T> _33___accumulator = Dafny.Sequence<__T>.FromElements();
    TAIL_CALL_START: ;
      if ((length).Sign == 0) {
        return Dafny.Sequence<__T>.Concat(_33___accumulator, Dafny.Sequence<__T>.FromElements());
      } else {
        _33___accumulator = Dafny.Sequence<__T>.Concat(_33___accumulator, Dafny.Sequence<__T>.FromElements(v));
        __T _in19 = v;
        BigInteger _in20 = (length) - (BigInteger.One);
        v = _in19;
        length = _in20;
        goto TAIL_CALL_START;
      }
    }
    public static _System._ITuple2<Dafny.ISequence<__A>, Dafny.ISequence<__B>> Unzip<__A, __B>(Dafny.ISequence<_System._ITuple2<__A, __B>> s) {
      if ((new BigInteger((s).Count)).Sign == 0) {
        return _System.Tuple2<Dafny.ISequence<__A>, Dafny.ISequence<__B>>.create(Dafny.Sequence<__A>.FromElements(), Dafny.Sequence<__B>.FromElements());
      } else {
        _System._ITuple2<Dafny.ISequence<__A>, Dafny.ISequence<__B>> _let_tmp_rhs0 = Seq_Compile.__default.Unzip<__A, __B>(Seq_Compile.__default.DropLast<_System._ITuple2<__A, __B>>(s));
        Dafny.ISequence<__A> _34_a = _let_tmp_rhs0.dtor__0;
        Dafny.ISequence<__B> _35_b = _let_tmp_rhs0.dtor__1;
        return _System.Tuple2<Dafny.ISequence<__A>, Dafny.ISequence<__B>>.create(Dafny.Sequence<__A>.Concat(_34_a, Dafny.Sequence<__A>.FromElements((Seq_Compile.__default.Last<_System._ITuple2<__A, __B>>(s)).dtor__0)), Dafny.Sequence<__B>.Concat(_35_b, Dafny.Sequence<__B>.FromElements((Seq_Compile.__default.Last<_System._ITuple2<__A, __B>>(s)).dtor__1)));
      }
    }
    public static Dafny.ISequence<_System._ITuple2<__A, __B>> Zip<__A, __B>(Dafny.ISequence<__A> a, Dafny.ISequence<__B> b)
    {
      Dafny.ISequence<_System._ITuple2<__A, __B>> _36___accumulator = Dafny.Sequence<_System._ITuple2<__A, __B>>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((a).Count)).Sign == 0) {
        return Dafny.Sequence<_System._ITuple2<__A, __B>>.Concat(Dafny.Sequence<_System._ITuple2<__A, __B>>.FromElements(), _36___accumulator);
      } else {
        _36___accumulator = Dafny.Sequence<_System._ITuple2<__A, __B>>.Concat(Dafny.Sequence<_System._ITuple2<__A, __B>>.FromElements(_System.Tuple2<__A, __B>.create(Seq_Compile.__default.Last<__A>(a), Seq_Compile.__default.Last<__B>(b))), _36___accumulator);
        Dafny.ISequence<__A> _in21 = Seq_Compile.__default.DropLast<__A>(a);
        Dafny.ISequence<__B> _in22 = Seq_Compile.__default.DropLast<__B>(b);
        a = _in21;
        b = _in22;
        goto TAIL_CALL_START;
      }
    }
    public static BigInteger Max(Dafny.ISequence<BigInteger> s) {
      if ((new BigInteger((s).Count)) == (BigInteger.One)) {
        return (s).Select(BigInteger.Zero);
      } else {
        return Math_Compile.__default.Max((s).Select(BigInteger.Zero), Seq_Compile.__default.Max((s).Drop(BigInteger.One)));
      }
    }
    public static BigInteger Min(Dafny.ISequence<BigInteger> s) {
      if ((new BigInteger((s).Count)) == (BigInteger.One)) {
        return (s).Select(BigInteger.Zero);
      } else {
        return Math_Compile.__default.Min((s).Select(BigInteger.Zero), Seq_Compile.__default.Min((s).Drop(BigInteger.One)));
      }
    }
    public static Dafny.ISequence<__T> Flatten<__T>(Dafny.ISequence<Dafny.ISequence<__T>> s) {
      Dafny.ISequence<__T> _37___accumulator = Dafny.Sequence<__T>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((s).Count)).Sign == 0) {
        return Dafny.Sequence<__T>.Concat(_37___accumulator, Dafny.Sequence<__T>.FromElements());
      } else {
        _37___accumulator = Dafny.Sequence<__T>.Concat(_37___accumulator, (s).Select(BigInteger.Zero));
        Dafny.ISequence<Dafny.ISequence<__T>> _in23 = (s).Drop(BigInteger.One);
        s = _in23;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<__T> FlattenReverse<__T>(Dafny.ISequence<Dafny.ISequence<__T>> s) {
      Dafny.ISequence<__T> _38___accumulator = Dafny.Sequence<__T>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((s).Count)).Sign == 0) {
        return Dafny.Sequence<__T>.Concat(Dafny.Sequence<__T>.FromElements(), _38___accumulator);
      } else {
        _38___accumulator = Dafny.Sequence<__T>.Concat(Seq_Compile.__default.Last<Dafny.ISequence<__T>>(s), _38___accumulator);
        Dafny.ISequence<Dafny.ISequence<__T>> _in24 = Seq_Compile.__default.DropLast<Dafny.ISequence<__T>>(s);
        s = _in24;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<__R> Map<__T, __R>(Func<__T, __R> f, Dafny.ISequence<__T> s)
    {
      Dafny.ISequence<__R> _39___accumulator = Dafny.Sequence<__R>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((s).Count)).Sign == 0) {
        return Dafny.Sequence<__R>.Concat(_39___accumulator, Dafny.Sequence<__R>.FromElements());
      } else {
        _39___accumulator = Dafny.Sequence<__R>.Concat(_39___accumulator, Dafny.Sequence<__R>.FromElements(Dafny.Helpers.Id<Func<__T, __R>>(f)((s).Select(BigInteger.Zero))));
        Func<__T, __R> _in25 = f;
        Dafny.ISequence<__T> _in26 = (s).Drop(BigInteger.One);
        f = _in25;
        s = _in26;
        goto TAIL_CALL_START;
      }
    }
    public static Wrappers_Compile._IResult<Dafny.ISequence<__R>, __E> MapWithResult<__T, __R, __E>(Func<__T, Wrappers_Compile._IResult<__R, __E>> f, Dafny.ISequence<__T> s)
    {
      if ((new BigInteger((s).Count)).Sign == 0) {
        return Wrappers_Compile.Result<Dafny.ISequence<__R>, __E>.create_Success(Dafny.Sequence<__R>.FromElements());
      } else {
        Wrappers_Compile._IResult<__R, __E> _40_valueOrError0 = Dafny.Helpers.Id<Func<__T, Wrappers_Compile._IResult<__R, __E>>>(f)((s).Select(BigInteger.Zero));
        if ((_40_valueOrError0).IsFailure()) {
          return (_40_valueOrError0).PropagateFailure<Dafny.ISequence<__R>>();
        } else {
          __R _41_head = (_40_valueOrError0).Extract();
          Wrappers_Compile._IResult<Dafny.ISequence<__R>, __E> _42_valueOrError1 = Seq_Compile.__default.MapWithResult<__T, __R, __E>(f, (s).Drop(BigInteger.One));
          if ((_42_valueOrError1).IsFailure()) {
            return (_42_valueOrError1).PropagateFailure<Dafny.ISequence<__R>>();
          } else {
            Dafny.ISequence<__R> _43_tail = (_42_valueOrError1).Extract();
            return Wrappers_Compile.Result<Dafny.ISequence<__R>, __E>.create_Success(Dafny.Sequence<__R>.Concat(Dafny.Sequence<__R>.FromElements(_41_head), _43_tail));
          }
        }
      }
    }
    public static Dafny.ISequence<__T> Filter<__T>(Func<__T, bool> f, Dafny.ISequence<__T> s)
    {
      Dafny.ISequence<__T> _44___accumulator = Dafny.Sequence<__T>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((s).Count)).Sign == 0) {
        return Dafny.Sequence<__T>.Concat(_44___accumulator, Dafny.Sequence<__T>.FromElements());
      } else {
        _44___accumulator = Dafny.Sequence<__T>.Concat(_44___accumulator, ((Dafny.Helpers.Id<Func<__T, bool>>(f)((s).Select(BigInteger.Zero))) ? (Dafny.Sequence<__T>.FromElements((s).Select(BigInteger.Zero))) : (Dafny.Sequence<__T>.FromElements())));
        Func<__T, bool> _in27 = f;
        Dafny.ISequence<__T> _in28 = (s).Drop(BigInteger.One);
        f = _in27;
        s = _in28;
        goto TAIL_CALL_START;
      }
    }
    public static __A FoldLeft<__A, __T>(Func<__A, __T, __A> f, __A init, Dafny.ISequence<__T> s)
    {
    TAIL_CALL_START: ;
      if ((new BigInteger((s).Count)).Sign == 0) {
        return init;
      } else {
        Func<__A, __T, __A> _in29 = f;
        __A _in30 = Dafny.Helpers.Id<Func<__A, __T, __A>>(f)(init, (s).Select(BigInteger.Zero));
        Dafny.ISequence<__T> _in31 = (s).Drop(BigInteger.One);
        f = _in29;
        init = _in30;
        s = _in31;
        goto TAIL_CALL_START;
      }
    }
    public static __A FoldRight<__A, __T>(Func<__T, __A, __A> f, Dafny.ISequence<__T> s, __A init)
    {
      if ((new BigInteger((s).Count)).Sign == 0) {
        return init;
      } else {
        return Dafny.Helpers.Id<Func<__T, __A, __A>>(f)((s).Select(BigInteger.Zero), Seq_Compile.__default.FoldRight<__A, __T>(f, (s).Drop(BigInteger.One), init));
      }
    }
  }
} // end of namespace Seq_Compile
namespace srcCollectionsSequencesLittleEndianNatdfyUnitTests_Compile {

} // end of namespace srcCollectionsSequencesLittleEndianNatdfyUnitTests_Compile
namespace srcCollectionsSequencesLittleEndianNatConversionsdfyUnitTests_Compile {

} // end of namespace srcCollectionsSequencesLittleEndianNatConversionsdfyUnitTests_Compile
namespace Maps_Compile {

  public partial class __default {
    public static Wrappers_Compile._IOption<__Y> Get<__X, __Y>(Dafny.IMap<__X,__Y> m, __X x)
    {
      if ((m).Contains((x))) {
        return Wrappers_Compile.Option<__Y>.create_Some(Dafny.Map<__X, __Y>.Select(m,x));
      } else {
        return Wrappers_Compile.Option<__Y>.create_None();
      }
    }
    public static Dafny.IMap<__X,__Y> ToImap<__X, __Y>(Dafny.IMap<__X,__Y> m) {
      return Dafny.Helpers.Id<Func<Dafny.IMap<__X,__Y>, Dafny.IMap<__X,__Y>>>((_45_m) => ((System.Func<Dafny.IMap<__X,__Y>>)(() => {
        var _coll1 = new System.Collections.Generic.List<Dafny.Pair<__X,__Y>>();
        foreach (__X _compr_1 in (_45_m).Keys.Elements) {
          __X _46_x = (__X)_compr_1;
          if ((_45_m).Contains((_46_x))) {
            _coll1.Add(new Dafny.Pair<__X,__Y>(_46_x, Dafny.Map<__X, __Y>.Select(_45_m,_46_x)));
          }
        }
        return Dafny.Map<__X,__Y>.FromCollection(_coll1);
      }))())(m);
    }
    public static Dafny.IMap<__X,__Y> RemoveKeys<__X, __Y>(Dafny.IMap<__X,__Y> m, Dafny.ISet<__X> xs)
    {
      return Dafny.Map<__X, __Y>.Subtract(m, xs);
    }
    public static Dafny.IMap<__X,__Y> Remove<__X, __Y>(Dafny.IMap<__X,__Y> m, __X x)
    {
      Dafny.IMap<__X,__Y> _47_m_k = Dafny.Helpers.Id<Func<Dafny.IMap<__X,__Y>, __X, Dafny.IMap<__X,__Y>>>((_48_m, _49_x) => ((System.Func<Dafny.IMap<__X,__Y>>)(() => {
        var _coll2 = new System.Collections.Generic.List<Dafny.Pair<__X,__Y>>();
        foreach (__X _compr_2 in (_48_m).Keys.Elements) {
          __X _50_x_k = (__X)_compr_2;
          if (((_48_m).Contains((_50_x_k))) && (!object.Equals(_50_x_k, _49_x))) {
            _coll2.Add(new Dafny.Pair<__X,__Y>(_50_x_k, Dafny.Map<__X, __Y>.Select(_48_m,_50_x_k)));
          }
        }
        return Dafny.Map<__X,__Y>.FromCollection(_coll2);
      }))())(m, x);
      return _47_m_k;
    }
    public static Dafny.IMap<__X,__Y> Restrict<__X, __Y>(Dafny.IMap<__X,__Y> m, Dafny.ISet<__X> xs)
    {
      return Dafny.Helpers.Id<Func<Dafny.ISet<__X>, Dafny.IMap<__X,__Y>, Dafny.IMap<__X,__Y>>>((_51_xs, _52_m) => ((System.Func<Dafny.IMap<__X,__Y>>)(() => {
        var _coll3 = new System.Collections.Generic.List<Dafny.Pair<__X,__Y>>();
        foreach (__X _compr_3 in (_51_xs).Elements) {
          __X _53_x = (__X)_compr_3;
          if (((_51_xs).Contains((_53_x))) && ((_52_m).Contains((_53_x)))) {
            _coll3.Add(new Dafny.Pair<__X,__Y>(_53_x, Dafny.Map<__X, __Y>.Select(_52_m,_53_x)));
          }
        }
        return Dafny.Map<__X,__Y>.FromCollection(_coll3);
      }))())(xs, m);
    }
    public static Dafny.IMap<__X,__Y> Union<__X, __Y>(Dafny.IMap<__X,__Y> m, Dafny.IMap<__X,__Y> m_k)
    {
      return Dafny.Map<__X, __Y>.Merge(m, m_k);
    }
  }
} // end of namespace Maps_Compile
namespace srcCollectionsMapsMapsdfyUnitTests_Compile {

  public partial class __default {
    [Xunit.Fact]
    public static void test0()
    {
      Dafny.IMap<BigInteger,BigInteger> _54_d0;
      _54_d0 = Dafny.Map<BigInteger, BigInteger>.FromElements(new Dafny.Pair<BigInteger, BigInteger>(BigInteger.Zero, BigInteger.One), new Dafny.Pair<BigInteger, BigInteger>(new BigInteger(2), new BigInteger(3)), new Dafny.Pair<BigInteger, BigInteger>(new BigInteger(4), new BigInteger(5)), new Dafny.Pair<BigInteger, BigInteger>(new BigInteger(6), new BigInteger(7)));
      Wrappers_Compile._IOption<BigInteger> _55_r0;
      _55_r0 = Maps_Compile.__default.Get<BigInteger, BigInteger>(_54_d0, BigInteger.Zero);
    }
    [Xunit.Fact]
    public static void test1()
    {
      Dafny.IMap<BigInteger,BigInteger> _56_d0;
      _56_d0 = Dafny.Map<BigInteger, BigInteger>.FromElements();
      Wrappers_Compile._IOption<BigInteger> _57_r0;
      _57_r0 = Maps_Compile.__default.Get<BigInteger, BigInteger>(_56_d0, BigInteger.Zero);
    }
    [Xunit.Fact]
    public static void test2()
    {
      Dafny.IMap<BigInteger,BigInteger> _58_d0;
      _58_d0 = Dafny.Map<BigInteger, BigInteger>.FromElements(new Dafny.Pair<BigInteger, BigInteger>(BigInteger.Zero, BigInteger.One), new Dafny.Pair<BigInteger, BigInteger>(new BigInteger(2), new BigInteger(3)), new Dafny.Pair<BigInteger, BigInteger>(new BigInteger(4), new BigInteger(5)), new Dafny.Pair<BigInteger, BigInteger>(new BigInteger(6), new BigInteger(7)));
      Dafny.IMap<BigInteger,BigInteger> _59_r0;
      _59_r0 = Maps_Compile.__default.ToImap<BigInteger, BigInteger>(_58_d0);
    }
    [Xunit.Fact]
    public static void test3()
    {
      Dafny.IMap<BigInteger,BigInteger> _60_d0;
      _60_d0 = Dafny.Map<BigInteger, BigInteger>.FromElements();
      Dafny.IMap<BigInteger,BigInteger> _61_r0;
      _61_r0 = Maps_Compile.__default.ToImap<BigInteger, BigInteger>(_60_d0);
    }
    [Xunit.Fact]
    public static void test5()
    {
      Dafny.IMap<BigInteger,BigInteger> _62_d0;
      _62_d0 = Dafny.Map<BigInteger, BigInteger>.FromElements();
      Dafny.ISet<BigInteger> _63_d1;
      _63_d1 = Dafny.Set<BigInteger>.FromElements();
      Dafny.IMap<BigInteger,BigInteger> _64_r0;
      _64_r0 = Maps_Compile.__default.RemoveKeys<BigInteger, BigInteger>(_62_d0, _63_d1);
      if (!(((_64_r0).Keys).Equals((Dafny.Set<BigInteger>.Difference((_62_d0).Keys, _63_d1))))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Maps/Maps.dfy(53,0): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
    }
    [Xunit.Fact]
    public static void test6()
    {
      Dafny.IMap<BigInteger,BigInteger> _65_d0;
      _65_d0 = Dafny.Map<BigInteger, BigInteger>.FromElements(new Dafny.Pair<BigInteger, BigInteger>(BigInteger.Zero, BigInteger.One), new Dafny.Pair<BigInteger, BigInteger>(new BigInteger(2), new BigInteger(3)), new Dafny.Pair<BigInteger, BigInteger>(new BigInteger(4), new BigInteger(5)), new Dafny.Pair<BigInteger, BigInteger>(new BigInteger(6), new BigInteger(7)));
      Dafny.IMap<BigInteger,BigInteger> _66_r0;
      _66_r0 = Maps_Compile.__default.Remove<BigInteger, BigInteger>(_65_d0, new BigInteger(8));
      if (!((_66_r0).Equals((Maps_Compile.__default.RemoveKeys<BigInteger, BigInteger>(_65_d0, Dafny.Set<BigInteger>.FromElements(new BigInteger(8))))))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Maps/Maps.dfy(64,0): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
      if (!((new BigInteger(((_66_r0).Keys).Count)) <= (new BigInteger(((_65_d0).Keys).Count)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Maps/Maps.dfy(65,0): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
      if (!(!((_65_d0).Contains((new BigInteger(8)))) || ((new BigInteger((_66_r0).Count)) == ((new BigInteger((_65_d0).Count)) - (BigInteger.One))))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Maps/Maps.dfy(66,0): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
      if (!(!(!(_65_d0).Contains((new BigInteger(8)))) || ((new BigInteger((_66_r0).Count)) == (new BigInteger((_65_d0).Count))))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Maps/Maps.dfy(67,0): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
    }
    [Xunit.Fact]
    public static void test7()
    {
      Dafny.IMap<BigInteger,BigInteger> _67_d0;
      _67_d0 = Dafny.Map<BigInteger, BigInteger>.FromElements();
      Dafny.IMap<BigInteger,BigInteger> _68_r0;
      _68_r0 = Maps_Compile.__default.Remove<BigInteger, BigInteger>(_67_d0, BigInteger.Zero);
      if (!((_68_r0).Equals((Maps_Compile.__default.RemoveKeys<BigInteger, BigInteger>(_67_d0, Dafny.Set<BigInteger>.FromElements(BigInteger.Zero)))))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Maps/Maps.dfy(75,0): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
      if (!((new BigInteger(((_68_r0).Keys).Count)) <= (new BigInteger(((_67_d0).Keys).Count)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Maps/Maps.dfy(76,0): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
      if (!(!((_67_d0).Contains((BigInteger.Zero))) || ((new BigInteger((_68_r0).Count)) == ((new BigInteger((_67_d0).Count)) - (BigInteger.One))))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Maps/Maps.dfy(77,0): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
      if (!(!(!(_67_d0).Contains((BigInteger.Zero))) || ((new BigInteger((_68_r0).Count)) == (new BigInteger((_67_d0).Count))))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Maps/Maps.dfy(78,0): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
    }
    [Xunit.Fact]
    public static void test8()
    {
      Dafny.IMap<BigInteger,BigInteger> _69_d0;
      _69_d0 = Dafny.Map<BigInteger, BigInteger>.FromElements(new Dafny.Pair<BigInteger, BigInteger>(BigInteger.Zero, BigInteger.One), new Dafny.Pair<BigInteger, BigInteger>(new BigInteger(2), new BigInteger(3)), new Dafny.Pair<BigInteger, BigInteger>(new BigInteger(4), new BigInteger(5)), new Dafny.Pair<BigInteger, BigInteger>(new BigInteger(6), new BigInteger(7)));
      Dafny.IMap<BigInteger,BigInteger> _70_r0;
      _70_r0 = Maps_Compile.__default.Remove<BigInteger, BigInteger>(_69_d0, new BigInteger(6));
      if (!((_70_r0).Equals((Maps_Compile.__default.RemoveKeys<BigInteger, BigInteger>(_69_d0, Dafny.Set<BigInteger>.FromElements(new BigInteger(6))))))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Maps/Maps.dfy(88,0): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
      if (!((new BigInteger(((_70_r0).Keys).Count)) <= (new BigInteger(((_69_d0).Keys).Count)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Maps/Maps.dfy(89,0): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
      if (!(!((_69_d0).Contains((new BigInteger(6)))) || ((new BigInteger((_70_r0).Count)) == ((new BigInteger((_69_d0).Count)) - (BigInteger.One))))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Maps/Maps.dfy(90,0): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
      if (!(!(!(_69_d0).Contains((new BigInteger(6)))) || ((new BigInteger((_70_r0).Count)) == (new BigInteger((_69_d0).Count))))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Maps/Maps.dfy(91,0): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
    }
    [Xunit.Fact]
    public static void test10()
    {
      Dafny.IMap<BigInteger,BigInteger> _71_d0;
      _71_d0 = Dafny.Map<BigInteger, BigInteger>.FromElements(new Dafny.Pair<BigInteger, BigInteger>(BigInteger.Zero, BigInteger.One), new Dafny.Pair<BigInteger, BigInteger>(new BigInteger(2), new BigInteger(3)), new Dafny.Pair<BigInteger, BigInteger>(new BigInteger(4), new BigInteger(5)), new Dafny.Pair<BigInteger, BigInteger>(new BigInteger(6), new BigInteger(7)));
      Dafny.ISet<BigInteger> _72_d1;
      _72_d1 = Dafny.Set<BigInteger>.FromElements(BigInteger.Zero);
      Dafny.IMap<BigInteger,BigInteger> _73_r0;
      _73_r0 = Maps_Compile.__default.Restrict<BigInteger, BigInteger>(_71_d0, _72_d1);
      if (!((_73_r0).Equals((Maps_Compile.__default.RemoveKeys<BigInteger, BigInteger>(_71_d0, Dafny.Set<BigInteger>.Difference((_71_d0).Keys, _72_d1)))))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Maps/Maps.dfy(108,0): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
    }
    [Xunit.Fact]
    public static void test11()
    {
      Dafny.IMap<BigInteger,BigInteger> _74_d0;
      _74_d0 = Dafny.Map<BigInteger, BigInteger>.FromElements();
      Dafny.ISet<BigInteger> _75_d1;
      _75_d1 = Dafny.Set<BigInteger>.FromElements();
      Dafny.IMap<BigInteger,BigInteger> _76_r0;
      _76_r0 = Maps_Compile.__default.Restrict<BigInteger, BigInteger>(_74_d0, _75_d1);
      if (!((_76_r0).Equals((Maps_Compile.__default.RemoveKeys<BigInteger, BigInteger>(_74_d0, Dafny.Set<BigInteger>.Difference((_74_d0).Keys, _75_d1)))))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Maps/Maps.dfy(117,0): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
    }
    [Xunit.Fact]
    public static void test12()
    {
      Dafny.IMap<BigInteger,BigInteger> _77_d0;
      _77_d0 = Dafny.Map<BigInteger, BigInteger>.FromElements();
      Dafny.ISet<BigInteger> _78_d1;
      _78_d1 = Dafny.Set<BigInteger>.FromElements(BigInteger.Zero);
      Dafny.IMap<BigInteger,BigInteger> _79_r0;
      _79_r0 = Maps_Compile.__default.Restrict<BigInteger, BigInteger>(_77_d0, _78_d1);
      if (!((_79_r0).Equals((Maps_Compile.__default.RemoveKeys<BigInteger, BigInteger>(_77_d0, Dafny.Set<BigInteger>.Difference((_77_d0).Keys, _78_d1)))))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Maps/Maps.dfy(128,0): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
    }
    [Xunit.Fact]
    public static void test14()
    {
      Dafny.IMap<BigInteger,BigInteger> _80_d0;
      _80_d0 = Dafny.Map<BigInteger, BigInteger>.FromElements();
      Dafny.IMap<BigInteger,BigInteger> _81_d1;
      _81_d1 = Dafny.Map<BigInteger, BigInteger>.FromElements();
      Dafny.IMap<BigInteger,BigInteger> _82_r0;
      _82_r0 = Maps_Compile.__default.Union<BigInteger, BigInteger>(_80_d0, _81_d1);
      if (!(((_82_r0).Keys).Equals((Dafny.Set<BigInteger>.Union((_80_d0).Keys, (_81_d1).Keys))))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Maps/Maps.dfy(141,0): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
    }
  }
} // end of namespace srcCollectionsMapsMapsdfyUnitTests_Compile
namespace srcMathdfyUnitTests_Compile {

  public partial class __default {
    [Xunit.Fact]
    public static void test0()
    {
      BigInteger _83_r0;
      _83_r0 = Math_Compile.__default.Min(new BigInteger(7719), new BigInteger(7720));
    }
    [Xunit.Fact]
    public static void test1()
    {
      BigInteger _84_r0;
      _84_r0 = Math_Compile.__default.Min(BigInteger.Zero, BigInteger.Zero);
    }
    [Xunit.Fact]
    public static void test2()
    {
      BigInteger _85_r0;
      _85_r0 = Math_Compile.__default.Max(BigInteger.Zero, BigInteger.One);
    }
    [Xunit.Fact]
    public static void test3()
    {
      BigInteger _86_r0;
      _86_r0 = Math_Compile.__default.Max(BigInteger.Zero, BigInteger.Zero);
    }
  }
} // end of namespace srcMathdfyUnitTests_Compile
namespace srcNonlinearArithmeticInternalsModInternalsdfyUnitTests_Compile {

  public partial class __default {
    [Xunit.Fact]
    public static void test0()
    {
      if (!((new BigInteger(8856)).Sign == 1)) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/NonlinearArithmetic/Internals/ModInternals.dfy(21,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      BigInteger _87_r0;
      _87_r0 = ModInternals_Compile.__default.ModRecursive(new BigInteger(-8857), new BigInteger(8856));
    }
    [Xunit.Fact]
    public static void test1()
    {
      if (!((new BigInteger(2460)).Sign == 1)) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/NonlinearArithmetic/Internals/ModInternals.dfy(29,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      BigInteger _88_r0;
      _88_r0 = ModInternals_Compile.__default.ModRecursive(new BigInteger(4417), new BigInteger(2460));
    }
    [Xunit.Fact]
    public static void test2()
    {
      if (!((BigInteger.One).Sign == 1)) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/NonlinearArithmetic/Internals/ModInternals.dfy(37,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      BigInteger _89_r0;
      _89_r0 = ModInternals_Compile.__default.ModRecursive(BigInteger.Zero, BigInteger.One);
    }
  }
} // end of namespace srcNonlinearArithmeticInternalsModInternalsdfyUnitTests_Compile
namespace srcNonlinearArithmeticInternalsModInternalsNonlineardfyUnitTests_Compile {

} // end of namespace srcNonlinearArithmeticInternalsModInternalsNonlineardfyUnitTests_Compile
namespace srcNonlinearArithmeticMuldfyUnitTests_Compile {

} // end of namespace srcNonlinearArithmeticMuldfyUnitTests_Compile
namespace srcNonlinearArithmeticInternalsMulInternalsdfyUnitTests_Compile {

  public partial class __default {
    [Xunit.Fact]
    public static void test0()
    {
      if (!((new BigInteger(1799)).Sign != -1)) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/NonlinearArithmetic/Internals/MulInternals.dfy(17,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      BigInteger _90_r0;
      _90_r0 = MulInternals_Compile.__default.MulPos(new BigInteger(1799), new BigInteger(-7719));
    }
    [Xunit.Fact]
    public static void test1()
    {
      if (!((BigInteger.Zero).Sign != -1)) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/NonlinearArithmetic/Internals/MulInternals.dfy(24,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      BigInteger _91_r0;
      _91_r0 = MulInternals_Compile.__default.MulPos(BigInteger.Zero, BigInteger.Zero);
    }
    [Xunit.Fact]
    public static void test2()
    {
      BigInteger _92_r0;
      _92_r0 = MulInternals_Compile.__default.MulRecursive(new BigInteger(1238), new BigInteger(-7719));
    }
  }
} // end of namespace srcNonlinearArithmeticInternalsMulInternalsdfyUnitTests_Compile
namespace srcNonlinearArithmeticInternalsMulInternalsNonlineardfyUnitTests_Compile {

} // end of namespace srcNonlinearArithmeticInternalsMulInternalsNonlineardfyUnitTests_Compile
namespace srcNonlinearArithmeticPowerdfyUnitTests_Compile {

  public partial class __default {
    [Xunit.Fact]
    public static void test0()
    {
      BigInteger _93_r0;
      _93_r0 = Power_Compile.__default.Pow(BigInteger.Zero, BigInteger.Zero);
    }
  }
} // end of namespace srcNonlinearArithmeticPowerdfyUnitTests_Compile
namespace Power2_Compile {

  public partial class __default {
    public static BigInteger Pow2(BigInteger e) {
      return Power_Compile.__default.Pow(new BigInteger(2), e);
    }
  }
} // end of namespace Power2_Compile
namespace srcNonlinearArithmeticPower2dfyUnitTests_Compile {

} // end of namespace srcNonlinearArithmeticPower2dfyUnitTests_Compile
namespace srcCollectionsSequencesSeqdfyUnitTests_Compile {

  public partial class __default {
    [Xunit.Fact]
    public static void test0()
    {
      Dafny.ISequence<BigInteger> _94_d0;
      _94_d0 = Dafny.Sequence<BigInteger>.FromElements(BigInteger.Zero);
      if (!((new BigInteger((_94_d0).Count)).Sign == 1)) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Seq.dfy(16,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      BigInteger _95_r0;
      _95_r0 = Seq_Compile.__default.First<BigInteger>(_94_d0);
    }
    [Xunit.Fact]
    public static void test1()
    {
      Dafny.ISequence<BigInteger> _96_d0;
      _96_d0 = Dafny.Sequence<BigInteger>.FromElements(BigInteger.Zero);
      if (!((new BigInteger((_96_d0).Count)).Sign == 1)) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Seq.dfy(23,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      Dafny.ISequence<BigInteger> _97_r0;
      _97_r0 = Seq_Compile.__default.DropFirst<BigInteger>(_96_d0);
    }
    [Xunit.Fact]
    public static void test2()
    {
      Dafny.ISequence<BigInteger> _98_d0;
      _98_d0 = Dafny.Sequence<BigInteger>.FromElements(BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero);
      if (!((new BigInteger((_98_d0).Count)).Sign == 1)) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Seq.dfy(30,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      BigInteger _99_r0;
      _99_r0 = Seq_Compile.__default.Last<BigInteger>(_98_d0);
    }
    [Xunit.Fact]
    public static void test3()
    {
      Dafny.ISequence<BigInteger> _100_d0;
      _100_d0 = Dafny.Sequence<BigInteger>.FromElements(BigInteger.Zero, BigInteger.Zero);
      if (!((new BigInteger((_100_d0).Count)).Sign == 1)) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Seq.dfy(37,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      Dafny.ISequence<BigInteger> _101_r0;
      _101_r0 = Seq_Compile.__default.DropLast<BigInteger>(_100_d0);
    }
    [Xunit.Fact]
    public static void test4()
    {
      Dafny.ISequence<BigInteger> _102_d0;
      _102_d0 = Dafny.Sequence<BigInteger>.FromElements(BigInteger.Zero);
      BigInteger[] _103_r0;
      BigInteger[] _out0;
      _out0 = Seq_Compile.__default.ToArray<BigInteger>(_102_d0);
      _103_r0 = _out0;
      if (!((new BigInteger((_103_r0).Length)) == (new BigInteger((_102_d0).Count)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Seq.dfy(46,0): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
    }
    [Xunit.Fact]
    public static void test6()
    {
      Dafny.ISequence<BigInteger> _104_d0;
      _104_d0 = Dafny.Sequence<BigInteger>.FromElements(BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero);
      BigInteger[] _105_r0;
      BigInteger[] _out1;
      _out1 = Seq_Compile.__default.ToArray<BigInteger>(_104_d0);
      _105_r0 = _out1;
      if (!((new BigInteger((_105_r0).Length)) == (new BigInteger((_104_d0).Count)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Seq.dfy(66,0): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
    }
    [Xunit.Fact]
    public static void test8()
    {
      Dafny.ISequence<BigInteger> _106_d0;
      _106_d0 = Dafny.Sequence<BigInteger>.FromElements(BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero);
      Dafny.ISet<BigInteger> _107_r0;
      _107_r0 = Seq_Compile.__default.ToSet<BigInteger>(_106_d0);
    }
    [Xunit.Fact]
    public static void test9()
    {
      Dafny.ISequence<BigInteger> _108_d0;
      _108_d0 = Dafny.Sequence<BigInteger>.FromElements();
      Dafny.ISet<BigInteger> _109_r0;
      _109_r0 = Seq_Compile.__default.ToSet<BigInteger>(_108_d0);
    }
    [Xunit.Fact]
    public static void test11()
    {
      Dafny.ISequence<BigInteger> _110_d0;
      _110_d0 = Dafny.Sequence<BigInteger>.FromElements(BigInteger.One);
      if (!((_110_d0).Contains((BigInteger.One)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Seq.dfy(101,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      BigInteger _111_r0;
      _111_r0 = Seq_Compile.__default.IndexOf<BigInteger>(_110_d0, BigInteger.One);
      if (!(((_111_r0) < (new BigInteger((_110_d0).Count))) && (((_110_d0).Select(_111_r0)) == (BigInteger.One)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Seq.dfy(103,0): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
    }
    [Xunit.Fact]
    public static void test12()
    {
      Dafny.ISequence<BigInteger> _112_d0;
      _112_d0 = Dafny.Sequence<BigInteger>.FromElements(BigInteger.Zero, BigInteger.One, BigInteger.One, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.One, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.One);
      if (!((_112_d0).Contains((BigInteger.One)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Seq.dfy(110,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      BigInteger _113_r0;
      _113_r0 = Seq_Compile.__default.IndexOf<BigInteger>(_112_d0, BigInteger.One);
      if (!(((_113_r0) < (new BigInteger((_112_d0).Count))) && (((_112_d0).Select(_113_r0)) == (BigInteger.One)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Seq.dfy(112,0): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
    }
    [Xunit.Fact]
    public static void test13()
    {
      Dafny.ISequence<BigInteger> _114_d0;
      _114_d0 = Dafny.Sequence<BigInteger>.FromElements();
      Wrappers_Compile._IOption<BigInteger> _115_r0;
      _115_r0 = Seq_Compile.__default.IndexOfOption<BigInteger>(_114_d0, BigInteger.Zero);
    }
    [Xunit.Fact]
    public static void test14()
    {
      Dafny.ISequence<BigInteger> _116_d0;
      _116_d0 = Dafny.Sequence<BigInteger>.FromElements(BigInteger.Zero);
      Wrappers_Compile._IOption<BigInteger> _117_r0;
      _117_r0 = Seq_Compile.__default.IndexOfOption<BigInteger>(_116_d0, BigInteger.One);
    }
    [Xunit.Fact]
    public static void test15()
    {
      Dafny.ISequence<BigInteger> _118_d0;
      _118_d0 = Dafny.Sequence<BigInteger>.FromElements(BigInteger.One, new BigInteger(2));
      Wrappers_Compile._IOption<BigInteger> _119_r0;
      _119_r0 = Seq_Compile.__default.IndexOfOption<BigInteger>(_118_d0, new BigInteger(2));
    }
    [Xunit.Fact]
    public static void test16()
    {
      Dafny.ISequence<BigInteger> _120_d0;
      _120_d0 = Dafny.Sequence<BigInteger>.FromElements(BigInteger.Zero);
      Wrappers_Compile._IOption<BigInteger> _121_r0;
      _121_r0 = Seq_Compile.__default.IndexOfOption<BigInteger>(_120_d0, BigInteger.Zero);
    }
    [Xunit.Fact]
    public static void test17()
    {
      Dafny.ISequence<BigInteger> _122_d0;
      _122_d0 = Dafny.Sequence<BigInteger>.FromElements(BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero);
      if (!((_122_d0).Contains((BigInteger.Zero)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Seq.dfy(154,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      BigInteger _123_r0;
      _123_r0 = Seq_Compile.__default.LastIndexOf<BigInteger>(_122_d0, BigInteger.Zero);
      if (!(((_123_r0) < (new BigInteger((_122_d0).Count))) && (((_122_d0).Select(_123_r0)).Sign == 0))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Seq.dfy(156,0): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
    }
    [Xunit.Fact]
    public static void test18()
    {
      Dafny.ISequence<BigInteger> _124_d0;
      _124_d0 = Dafny.Sequence<BigInteger>.FromElements(BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.One);
      if (!((_124_d0).Contains((BigInteger.Zero)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Seq.dfy(163,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      BigInteger _125_r0;
      _125_r0 = Seq_Compile.__default.LastIndexOf<BigInteger>(_124_d0, BigInteger.Zero);
      if (!(((_125_r0) < (new BigInteger((_124_d0).Count))) && (((_124_d0).Select(_125_r0)).Sign == 0))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Seq.dfy(165,0): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
    }
    [Xunit.Fact]
    public static void test19()
    {
      Dafny.ISequence<BigInteger> _126_d0;
      _126_d0 = Dafny.Sequence<BigInteger>.FromElements();
      Wrappers_Compile._IOption<BigInteger> _127_r0;
      _127_r0 = Seq_Compile.__default.LastIndexOfOption<BigInteger>(_126_d0, BigInteger.Zero);
    }
    [Xunit.Fact]
    public static void test20()
    {
      Dafny.ISequence<BigInteger> _128_d0;
      _128_d0 = Dafny.Sequence<BigInteger>.FromElements(BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.One, new BigInteger(2));
      Wrappers_Compile._IOption<BigInteger> _129_r0;
      _129_r0 = Seq_Compile.__default.LastIndexOfOption<BigInteger>(_128_d0, new BigInteger(3));
    }
    [Xunit.Fact]
    public static void test21()
    {
      Dafny.ISequence<BigInteger> _130_d0;
      _130_d0 = Dafny.Sequence<BigInteger>.FromElements(BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero);
      Wrappers_Compile._IOption<BigInteger> _131_r0;
      _131_r0 = Seq_Compile.__default.LastIndexOfOption<BigInteger>(_130_d0, BigInteger.Zero);
    }
    [Xunit.Fact]
    public static void test22()
    {
      Dafny.ISequence<BigInteger> _132_d0;
      _132_d0 = Dafny.Sequence<BigInteger>.FromElements(BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero);
      if (!((new BigInteger(39)) < (new BigInteger((_132_d0).Count)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Seq.dfy(195,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      Dafny.ISequence<BigInteger> _133_r0;
      _133_r0 = Seq_Compile.__default.Remove<BigInteger>(_132_d0, new BigInteger(39));
      if (!((new BigInteger((_133_r0).Count)) == ((new BigInteger((_132_d0).Count)) - (BigInteger.One)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Seq.dfy(197,0): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
    }
    [Xunit.Fact]
    public static void test23()
    {
      Dafny.ISequence<BigInteger> _134_d0;
      _134_d0 = Dafny.Sequence<BigInteger>.FromElements();
      Dafny.ISequence<BigInteger> _135_r0;
      _135_r0 = Seq_Compile.__default.RemoveValue<BigInteger>(_134_d0, BigInteger.Zero);
      if (!(!(!(_134_d0).Contains((BigInteger.Zero))) || ((_134_d0).Equals((_135_r0))))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Seq.dfy(206,0): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
      if (!(!((_134_d0).Contains((BigInteger.Zero))) || ((new BigInteger((Dafny.MultiSet<BigInteger>.FromSeq(_135_r0)).Count)) == ((new BigInteger((Dafny.MultiSet<BigInteger>.FromSeq(_134_d0)).Count)) - (BigInteger.One))))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Seq.dfy(207,0): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
      if (!(!((_134_d0).Contains((BigInteger.Zero))) || (((Dafny.MultiSet<BigInteger>.FromSeq(_135_r0)).Select(BigInteger.Zero)) == (((Dafny.MultiSet<BigInteger>.FromSeq(_134_d0)).Select(BigInteger.Zero)) - (BigInteger.One))))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Seq.dfy(208,0): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
    }
    [Xunit.Fact]
    public static void test24()
    {
      Dafny.ISequence<BigInteger> _136_d0;
      _136_d0 = Dafny.Sequence<BigInteger>.FromElements(BigInteger.Zero, new BigInteger(2), BigInteger.Zero);
      Dafny.ISequence<BigInteger> _137_r0;
      _137_r0 = Seq_Compile.__default.RemoveValue<BigInteger>(_136_d0, new BigInteger(2));
      if (!(!(!(_136_d0).Contains((new BigInteger(2)))) || ((_136_d0).Equals((_137_r0))))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Seq.dfy(216,0): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
      if (!(!((_136_d0).Contains((new BigInteger(2)))) || ((new BigInteger((Dafny.MultiSet<BigInteger>.FromSeq(_137_r0)).Count)) == ((new BigInteger((Dafny.MultiSet<BigInteger>.FromSeq(_136_d0)).Count)) - (BigInteger.One))))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Seq.dfy(217,0): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
      if (!(!((_136_d0).Contains((new BigInteger(2)))) || (((Dafny.MultiSet<BigInteger>.FromSeq(_137_r0)).Select(new BigInteger(2))) == (((Dafny.MultiSet<BigInteger>.FromSeq(_136_d0)).Select(new BigInteger(2))) - (BigInteger.One))))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Seq.dfy(218,0): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
    }
    [Xunit.Fact]
    public static void test25()
    {
      Dafny.ISequence<BigInteger> _138_d0;
      _138_d0 = Dafny.Sequence<BigInteger>.FromElements(BigInteger.Zero, BigInteger.Zero);
      if (!((BigInteger.One) <= (new BigInteger((_138_d0).Count)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Seq.dfy(224,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      Dafny.ISequence<BigInteger> _139_r0;
      _139_r0 = Seq_Compile.__default.Insert<BigInteger>(_138_d0, BigInteger.Zero, BigInteger.One);
      if (!((new BigInteger((Seq_Compile.__default.Insert<BigInteger>(_138_d0, BigInteger.Zero, BigInteger.One)).Count)) == ((new BigInteger((_138_d0).Count)) + (BigInteger.One)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Seq.dfy(226,0): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
      if (!(((Seq_Compile.__default.Insert<BigInteger>(_138_d0, BigInteger.Zero, BigInteger.One)).Select(BigInteger.One)).Sign == 0)) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Seq.dfy(227,0): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
      if (!((Dafny.MultiSet<BigInteger>.FromSeq(Seq_Compile.__default.Insert<BigInteger>(_138_d0, BigInteger.Zero, BigInteger.One))).Equals((Dafny.MultiSet<BigInteger>.Union(Dafny.MultiSet<BigInteger>.FromSeq(_138_d0), Dafny.MultiSet<BigInteger>.FromElements(BigInteger.Zero)))))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Seq.dfy(228,0): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
    }
    [Xunit.Fact]
    public static void test26()
    {
      Dafny.ISequence<BigInteger> _140_d0;
      _140_d0 = Dafny.Sequence<BigInteger>.FromElements();
      Dafny.ISequence<BigInteger> _141_r0;
      _141_r0 = Seq_Compile.__default.Reverse<BigInteger>(_140_d0);
      if (!((new BigInteger((_141_r0).Count)) == (new BigInteger((_140_d0).Count)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Seq.dfy(237,0): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
    }
    [Xunit.Fact]
    public static void test27()
    {
      Dafny.ISequence<BigInteger> _142_d0;
      _142_d0 = Dafny.Sequence<BigInteger>.FromElements(BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.One, BigInteger.Zero);
      Dafny.ISequence<BigInteger> _143_r0;
      _143_r0 = Seq_Compile.__default.Reverse<BigInteger>(_142_d0);
      if (!((new BigInteger((_143_r0).Count)) == (new BigInteger((_142_d0).Count)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Seq.dfy(245,0): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
    }
    [Xunit.Fact]
    public static void test28()
    {
      Dafny.ISequence<BigInteger> _144_r0;
      _144_r0 = Seq_Compile.__default.Repeat<BigInteger>(BigInteger.Zero, new BigInteger(76));
      if (!((new BigInteger((_144_r0).Count)) == (new BigInteger(76)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Seq.dfy(253,0): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
    }
    [Xunit.Fact]
    public static void test29()
    {
      Dafny.ISequence<BigInteger> _145_r0;
      _145_r0 = Seq_Compile.__default.Repeat<BigInteger>(BigInteger.Zero, BigInteger.Zero);
      if (!((new BigInteger((_145_r0).Count)) == (BigInteger.Zero))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Seq.dfy(260,0): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
    }
    [Xunit.Fact]
    public static void test32()
    {
      Dafny.ISequence<BigInteger> _146_d0;
      _146_d0 = Dafny.Sequence<BigInteger>.FromElements(BigInteger.Zero, BigInteger.Zero);
      Dafny.ISequence<BigInteger> _147_d1;
      _147_d1 = Dafny.Sequence<BigInteger>.FromElements(BigInteger.Zero, BigInteger.Zero);
      if (!((new BigInteger((_146_d0).Count)) == (new BigInteger((_147_d1).Count)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Seq.dfy(279,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      Dafny.ISequence<_System._ITuple2<BigInteger, BigInteger>> _148_r0;
      _148_r0 = Seq_Compile.__default.Zip<BigInteger, BigInteger>(_146_d0, _147_d1);
      if (!((new BigInteger((Seq_Compile.__default.Zip<BigInteger, BigInteger>(_146_d0, _147_d1)).Count)) == (new BigInteger((_146_d0).Count)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Seq.dfy(281,0): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
      if (!(((Seq_Compile.__default.Unzip<BigInteger, BigInteger>(Seq_Compile.__default.Zip<BigInteger, BigInteger>(_146_d0, _147_d1))).dtor__0).Equals((_146_d0)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Seq.dfy(282,0): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
      if (!(((Seq_Compile.__default.Unzip<BigInteger, BigInteger>(Seq_Compile.__default.Zip<BigInteger, BigInteger>(_146_d0, _147_d1))).dtor__1).Equals((_147_d1)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Seq.dfy(283,0): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
    }
    [Xunit.Fact]
    public static void test33()
    {
      Dafny.ISequence<BigInteger> _149_d0;
      _149_d0 = Dafny.Sequence<BigInteger>.FromElements();
      Dafny.ISequence<BigInteger> _150_d1;
      _150_d1 = Dafny.Sequence<BigInteger>.FromElements();
      if (!((new BigInteger((_149_d0).Count)) == (new BigInteger((_150_d1).Count)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Seq.dfy(292,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      Dafny.ISequence<_System._ITuple2<BigInteger, BigInteger>> _151_r0;
      _151_r0 = Seq_Compile.__default.Zip<BigInteger, BigInteger>(_149_d0, _150_d1);
      if (!((new BigInteger((Seq_Compile.__default.Zip<BigInteger, BigInteger>(_149_d0, _150_d1)).Count)) == (new BigInteger((_149_d0).Count)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Seq.dfy(294,0): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
      if (!(((Seq_Compile.__default.Unzip<BigInteger, BigInteger>(Seq_Compile.__default.Zip<BigInteger, BigInteger>(_149_d0, _150_d1))).dtor__0).Equals((_149_d0)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Seq.dfy(295,0): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
      if (!(((Seq_Compile.__default.Unzip<BigInteger, BigInteger>(Seq_Compile.__default.Zip<BigInteger, BigInteger>(_149_d0, _150_d1))).dtor__1).Equals((_150_d1)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Seq.dfy(296,0): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
    }
    [Xunit.Fact]
    public static void test34()
    {
      Dafny.ISequence<BigInteger> _152_d0;
      _152_d0 = Dafny.Sequence<BigInteger>.FromElements(new BigInteger(8855), new BigInteger(8878), new BigInteger(8879));
      if (!((new BigInteger((_152_d0).Count)).Sign == 1)) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Seq.dfy(304,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      BigInteger _153_r0;
      _153_r0 = Seq_Compile.__default.Max(_152_d0);
      if (!((_152_d0).Contains((Seq_Compile.__default.Max(_152_d0))))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Seq.dfy(306,0): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
    }
    [Xunit.Fact]
    public static void test35()
    {
      Dafny.ISequence<BigInteger> _154_d0;
      _154_d0 = Dafny.Sequence<BigInteger>.FromElements(BigInteger.Zero);
      if (!((new BigInteger((_154_d0).Count)).Sign == 1)) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Seq.dfy(313,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      BigInteger _155_r0;
      _155_r0 = Seq_Compile.__default.Max(_154_d0);
      if (!((_154_d0).Contains((Seq_Compile.__default.Max(_154_d0))))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Seq.dfy(315,0): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
    }
    [Xunit.Fact]
    public static void test36()
    {
      Dafny.ISequence<BigInteger> _156_d0;
      _156_d0 = Dafny.Sequence<BigInteger>.FromElements(new BigInteger(8855), new BigInteger(1141), new BigInteger(1142));
      if (!((new BigInteger((_156_d0).Count)).Sign == 1)) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Seq.dfy(323,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      BigInteger _157_r0;
      _157_r0 = Seq_Compile.__default.Min(_156_d0);
      if (!((_156_d0).Contains((Seq_Compile.__default.Min(_156_d0))))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Seq.dfy(325,0): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
    }
    [Xunit.Fact]
    public static void test37()
    {
      Dafny.ISequence<BigInteger> _158_d0;
      _158_d0 = Dafny.Sequence<BigInteger>.FromElements(BigInteger.Zero);
      if (!((new BigInteger((_158_d0).Count)).Sign == 1)) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Seq.dfy(332,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      BigInteger _159_r0;
      _159_r0 = Seq_Compile.__default.Min(_158_d0);
      if (!((_158_d0).Contains((Seq_Compile.__default.Min(_158_d0))))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Seq.dfy(334,0): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
    }
    [Xunit.Fact]
    public static void test38()
    {
      Dafny.ISequence<Dafny.ISequence<BigInteger>> _160_d0;
      _160_d0 = Dafny.Sequence<Dafny.ISequence<BigInteger>>.FromElements();
      Dafny.ISequence<BigInteger> _161_r0;
      _161_r0 = Seq_Compile.__default.Flatten<BigInteger>(_160_d0);
    }
    [Xunit.Fact]
    public static void test39()
    {
      Dafny.ISequence<BigInteger> _162_d0;
      _162_d0 = Dafny.Sequence<BigInteger>.FromElements();
      Dafny.ISequence<BigInteger> _163_d1;
      _163_d1 = Dafny.Sequence<BigInteger>.FromElements(BigInteger.Zero);
      Dafny.ISequence<Dafny.ISequence<BigInteger>> _164_d2;
      _164_d2 = Dafny.Sequence<Dafny.ISequence<BigInteger>>.FromElements(_162_d0, _163_d1);
      Dafny.ISequence<BigInteger> _165_r0;
      _165_r0 = Seq_Compile.__default.Flatten<BigInteger>(_164_d2);
    }
    [Xunit.Fact]
    public static void test40()
    {
      Dafny.ISequence<Dafny.ISequence<BigInteger>> _166_d0;
      _166_d0 = Dafny.Sequence<Dafny.ISequence<BigInteger>>.FromElements();
      Dafny.ISequence<BigInteger> _167_r0;
      _167_r0 = Seq_Compile.__default.FlattenReverse<BigInteger>(_166_d0);
    }
    [Xunit.Fact]
    public static void test41()
    {
      Dafny.ISequence<BigInteger> _168_d0;
      _168_d0 = Dafny.Sequence<BigInteger>.FromElements();
      Dafny.ISequence<BigInteger> _169_d1;
      _169_d1 = Dafny.Sequence<BigInteger>.FromElements();
      Dafny.ISequence<Dafny.ISequence<BigInteger>> _170_d2;
      _170_d2 = Dafny.Sequence<Dafny.ISequence<BigInteger>>.FromElements(_168_d0, _169_d1);
      Dafny.ISequence<BigInteger> _171_r0;
      _171_r0 = Seq_Compile.__default.FlattenReverse<BigInteger>(_170_d2);
    }
    [Xunit.Fact]
    public static void test42()
    {
      Dafny.ISequence<BigInteger> _172_d0;
      _172_d0 = Dafny.Sequence<BigInteger>.FromElements();
      Dafny.ISequence<BigInteger> _173_r0;
      _173_r0 = Seq_Compile.__default.Map<BigInteger, BigInteger>(((System.Func<BigInteger, BigInteger>)((_174_a0) => {
        return BigInteger.Zero;
      })), _172_d0);
      if (!((new BigInteger((_173_r0).Count)) == (new BigInteger((_172_d0).Count)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Seq.dfy(377,0): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
    }
    [Xunit.Fact]
    public static void test43()
    {
      Dafny.ISequence<BigInteger> _175_d0;
      _175_d0 = Dafny.Sequence<BigInteger>.FromElements(BigInteger.Zero, BigInteger.One);
      Dafny.ISequence<BigInteger> _176_r0;
      _176_r0 = Seq_Compile.__default.Map<BigInteger, BigInteger>(((System.Func<BigInteger, BigInteger>)((_177_a0) => {
        return BigInteger.Zero;
      })), _175_d0);
      if (!((new BigInteger((_176_r0).Count)) == (new BigInteger((_175_d0).Count)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Seq.dfy(385,0): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
    }
    [Xunit.Fact]
    public static void test44()
    {
      Wrappers_Compile._IResult<BigInteger, BigInteger> _178_d0;
      _178_d0 = Wrappers_Compile.Result<BigInteger, BigInteger>.create_Success(BigInteger.Zero);
      Dafny.ISequence<BigInteger> _179_d1;
      _179_d1 = Dafny.Sequence<BigInteger>.FromElements();
      Wrappers_Compile._IResult<Dafny.ISequence<BigInteger>, BigInteger> _180_r0;
      _180_r0 = Seq_Compile.__default.MapWithResult<BigInteger, BigInteger, BigInteger>(Dafny.Helpers.Id<Func<Wrappers_Compile._IResult<BigInteger, BigInteger>, Func<BigInteger, Wrappers_Compile._IResult<BigInteger, BigInteger>>>>((_181_d0) => ((System.Func<BigInteger, Wrappers_Compile._IResult<BigInteger, BigInteger>>)((_182_a0) => {
        return _181_d0;
      })))(_178_d0), _179_d1);
    }
    [Xunit.Fact]
    public static void test45()
    {
      Wrappers_Compile._IResult<BigInteger, BigInteger> _183_d0;
      _183_d0 = Wrappers_Compile.Result<BigInteger, BigInteger>.create_Success(BigInteger.Zero);
      Dafny.ISequence<BigInteger> _184_d1;
      _184_d1 = Dafny.Sequence<BigInteger>.FromElements(BigInteger.Zero, BigInteger.One);
      Wrappers_Compile._IResult<Dafny.ISequence<BigInteger>, BigInteger> _185_r0;
      _185_r0 = Seq_Compile.__default.MapWithResult<BigInteger, BigInteger, BigInteger>(Dafny.Helpers.Id<Func<Wrappers_Compile._IResult<BigInteger, BigInteger>, Func<BigInteger, Wrappers_Compile._IResult<BigInteger, BigInteger>>>>((_186_d0) => ((System.Func<BigInteger, Wrappers_Compile._IResult<BigInteger, BigInteger>>)((_187_a0) => {
        return _186_d0;
      })))(_183_d0), _184_d1);
    }
    [Xunit.Fact]
    public static void test46()
    {
      Wrappers_Compile._IResult<BigInteger, BigInteger> _188_d0;
      _188_d0 = Wrappers_Compile.Result<BigInteger, BigInteger>.create_Success(BigInteger.Zero);
      Dafny.ISequence<BigInteger> _189_d1;
      _189_d1 = Dafny.Sequence<BigInteger>.FromElements(BigInteger.Zero, BigInteger.One, new BigInteger(2), BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero);
      Wrappers_Compile._IResult<Dafny.ISequence<BigInteger>, BigInteger> _190_r0;
      _190_r0 = Seq_Compile.__default.MapWithResult<BigInteger, BigInteger, BigInteger>(Dafny.Helpers.Id<Func<Wrappers_Compile._IResult<BigInteger, BigInteger>, Func<BigInteger, Wrappers_Compile._IResult<BigInteger, BigInteger>>>>((_191_d0) => ((System.Func<BigInteger, Wrappers_Compile._IResult<BigInteger, BigInteger>>)((_192_a0) => {
        return _191_d0;
      })))(_188_d0), _189_d1);
    }
    [Xunit.Fact]
    public static void test47()
    {
      Wrappers_Compile._IResult<BigInteger, BigInteger> _193_d0;
      _193_d0 = Wrappers_Compile.Result<BigInteger, BigInteger>.create_Success(BigInteger.Zero);
      Dafny.ISequence<BigInteger> _194_d1;
      _194_d1 = Dafny.Sequence<BigInteger>.FromElements(BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero);
      Wrappers_Compile._IResult<Dafny.ISequence<BigInteger>, BigInteger> _195_r0;
      _195_r0 = Seq_Compile.__default.MapWithResult<BigInteger, BigInteger, BigInteger>(Dafny.Helpers.Id<Func<Wrappers_Compile._IResult<BigInteger, BigInteger>, Func<BigInteger, Wrappers_Compile._IResult<BigInteger, BigInteger>>>>((_196_d0) => ((System.Func<BigInteger, Wrappers_Compile._IResult<BigInteger, BigInteger>>)((_197_a0) => {
        return _196_d0;
      })))(_193_d0), _194_d1);
    }
    [Xunit.Fact]
    public static void test48()
    {
      Dafny.ISequence<BigInteger> _198_d0;
      _198_d0 = Dafny.Sequence<BigInteger>.FromElements();
      Dafny.ISequence<BigInteger> _199_r0;
      _199_r0 = Seq_Compile.__default.Filter<BigInteger>(((System.Func<BigInteger, bool>)((_200_a0) => {
        return false;
      })), _198_d0);
      if (!((new BigInteger((_199_r0).Count)) <= (new BigInteger((_198_d0).Count)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Seq.dfy(432,0): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
    }
    [Xunit.Fact]
    public static void test49()
    {
      Dafny.ISequence<BigInteger> _201_d0;
      _201_d0 = Dafny.Sequence<BigInteger>.FromElements(BigInteger.Zero);
      Dafny.ISequence<BigInteger> _202_r0;
      _202_r0 = Seq_Compile.__default.Filter<BigInteger>(((System.Func<BigInteger, bool>)((_203_a0) => {
        return false;
      })), _201_d0);
      if (!((new BigInteger((_202_r0).Count)) <= (new BigInteger((_201_d0).Count)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Seq.dfy(442,0): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
    }
    [Xunit.Fact]
    public static void test51()
    {
      Dafny.ISequence<BigInteger> _204_d0;
      _204_d0 = Dafny.Sequence<BigInteger>.FromElements();
      BigInteger _205_r0;
      _205_r0 = Seq_Compile.__default.FoldLeft<BigInteger, BigInteger>(((System.Func<BigInteger, BigInteger, BigInteger>)((_206_a0, _207_a1) => {
        return BigInteger.Zero;
      })), BigInteger.Zero, _204_d0);
    }
    [Xunit.Fact]
    public static void test52()
    {
      Dafny.ISequence<BigInteger> _208_d0;
      _208_d0 = Dafny.Sequence<BigInteger>.FromElements(BigInteger.One);
      BigInteger _209_r0;
      _209_r0 = Seq_Compile.__default.FoldLeft<BigInteger, BigInteger>(((System.Func<BigInteger, BigInteger, BigInteger>)((_210_a0, _211_a1) => {
        return BigInteger.Zero;
      })), BigInteger.Zero, _208_d0);
    }
    [Xunit.Fact]
    public static void test53()
    {
      Dafny.ISequence<BigInteger> _212_d0;
      _212_d0 = Dafny.Sequence<BigInteger>.FromElements();
      BigInteger _213_r0;
      _213_r0 = Seq_Compile.__default.FoldRight<BigInteger, BigInteger>(((System.Func<BigInteger, BigInteger, BigInteger>)((_214_a0, _215_a1) => {
        return BigInteger.Zero;
      })), _212_d0, BigInteger.Zero);
    }
    [Xunit.Fact]
    public static void test54()
    {
      Dafny.ISequence<BigInteger> _216_d0;
      _216_d0 = Dafny.Sequence<BigInteger>.FromElements(BigInteger.Zero);
      BigInteger _217_r0;
      _217_r0 = Seq_Compile.__default.FoldRight<BigInteger, BigInteger>(((System.Func<BigInteger, BigInteger, BigInteger>)((_218_a0, _219_a1) => {
        return BigInteger.Zero;
      })), _216_d0, BigInteger.Zero);
    }
  }
} // end of namespace srcCollectionsSequencesSeqdfyUnitTests_Compile
namespace Sets_Compile {

  public partial class __default {
    public static Dafny.ISet<__Y> Map<__X, __Y>(Dafny.ISet<__X> xs, Func<__X, __Y> f)
    {
      Dafny.ISet<__Y> _220_ys = Dafny.Helpers.Id<Func<Dafny.ISet<__X>, Func<__X, __Y>, Dafny.ISet<__Y>>>((_221_xs, _222_f) => ((System.Func<Dafny.ISet<__Y>>)(() => {
        var _coll4 = new System.Collections.Generic.List<__Y>();
        foreach (__X _compr_4 in (_221_xs).Elements) {
          __X _223_x = (__X)_compr_4;
          if ((_221_xs).Contains((_223_x))) {
            _coll4.Add(Dafny.Helpers.Id<Func<__X, __Y>>(_222_f)(_223_x));
          }
        }
        return Dafny.Set<__Y>.FromCollection(_coll4);
      }))())(xs, f);
      return _220_ys;
    }
    public static Dafny.ISet<__X> Filter<__X>(Dafny.ISet<__X> xs, Func<__X, bool> f)
    {
      Dafny.ISet<__X> _224_ys = Dafny.Helpers.Id<Func<Dafny.ISet<__X>, Func<__X, bool>, Dafny.ISet<__X>>>((_225_xs, _226_f) => ((System.Func<Dafny.ISet<__X>>)(() => {
        var _coll5 = new System.Collections.Generic.List<__X>();
        foreach (__X _compr_5 in (_225_xs).Elements) {
          __X _227_x = (__X)_compr_5;
          if (((_225_xs).Contains((_227_x))) && (Dafny.Helpers.Id<Func<__X, bool>>(_226_f)(_227_x))) {
            _coll5.Add(_227_x);
          }
        }
        return Dafny.Set<__X>.FromCollection(_coll5);
      }))())(xs, f);
      return _224_ys;
    }
    public static Dafny.ISet<BigInteger> SetRange(BigInteger a, BigInteger b)
    {
      Dafny.ISet<BigInteger> _228___accumulator = Dafny.Set<BigInteger>.FromElements();
    TAIL_CALL_START: ;
      if ((a) == (b)) {
        return Dafny.Set<BigInteger>.Union(Dafny.Set<BigInteger>.FromElements(), _228___accumulator);
      } else {
        _228___accumulator = Dafny.Set<BigInteger>.Union(_228___accumulator, Dafny.Set<BigInteger>.FromElements(a));
        BigInteger _in32 = (a) + (BigInteger.One);
        BigInteger _in33 = b;
        a = _in32;
        b = _in33;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISet<BigInteger> SetRangeZeroBound(BigInteger n) {
      return Sets_Compile.__default.SetRange(BigInteger.Zero, n);
    }
  }
} // end of namespace Sets_Compile
namespace srcCollectionsSetsSetsdfyUnitTests_Compile {

  public partial class __default {
    [Xunit.Fact]
    public static void test1()
    {
      Dafny.ISet<BigInteger> _229_d0;
      _229_d0 = Dafny.Set<BigInteger>.FromElements();
      Dafny.ISet<BigInteger> _230_r0;
      _230_r0 = Sets_Compile.__default.Map<BigInteger, BigInteger>(_229_d0, ((System.Func<BigInteger, BigInteger>)((_231_a0) => {
        return BigInteger.Zero;
      })));
      if (!((new BigInteger((_229_d0).Count)) == (new BigInteger((_230_r0).Count)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sets/Sets.dfy(27,0): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
    }
    [Xunit.Fact]
    public static void test3()
    {
      Dafny.ISet<BigInteger> _232_d0;
      _232_d0 = Dafny.Set<BigInteger>.FromElements(BigInteger.Zero, BigInteger.One, new BigInteger(2));
      Dafny.ISet<BigInteger> _233_r0;
      _233_r0 = Sets_Compile.__default.Filter<BigInteger>(_232_d0, ((System.Func<BigInteger, bool>)((_234_a0) => {
        return false;
      })));
      if (!((new BigInteger((_233_r0).Count)) <= (new BigInteger((_232_d0).Count)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sets/Sets.dfy(43,0): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
    }
    [Xunit.Fact]
    public static void test4()
    {
      Dafny.ISet<BigInteger> _235_d0;
      _235_d0 = Dafny.Set<BigInteger>.FromElements();
      Dafny.ISet<BigInteger> _236_r0;
      _236_r0 = Sets_Compile.__default.Filter<BigInteger>(_235_d0, ((System.Func<BigInteger, bool>)((_237_a0) => {
        return false;
      })));
      if (!((new BigInteger((_236_r0).Count)) <= (new BigInteger((_235_d0).Count)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sets/Sets.dfy(51,0): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
    }
    [Xunit.Fact]
    public static void test5()
    {
      Dafny.ISet<BigInteger> _238_d0;
      _238_d0 = Dafny.Set<BigInteger>.FromElements(BigInteger.Zero);
      Dafny.ISet<BigInteger> _239_r0;
      _239_r0 = Sets_Compile.__default.Filter<BigInteger>(_238_d0, ((System.Func<BigInteger, bool>)((_240_a0) => {
        return false;
      })));
      if (!((new BigInteger((_239_r0).Count)) <= (new BigInteger((_238_d0).Count)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sets/Sets.dfy(61,0): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
    }
    [Xunit.Fact]
    public static void test7()
    {
      if (!((new BigInteger(2275)) <= (new BigInteger(2279)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sets/Sets.dfy(73,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      Dafny.ISet<BigInteger> _241_r0;
      _241_r0 = Sets_Compile.__default.SetRange(new BigInteger(2275), new BigInteger(2279));
      if (!((new BigInteger((_241_r0).Count)) == ((new BigInteger(2279)) - (new BigInteger(2275))))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sets/Sets.dfy(75,0): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
    }
    [Xunit.Fact]
    public static void test8()
    {
      if (!((new BigInteger(7719)) <= (new BigInteger(7719)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sets/Sets.dfy(81,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      Dafny.ISet<BigInteger> _242_r0;
      _242_r0 = Sets_Compile.__default.SetRange(new BigInteger(7719), new BigInteger(7719));
      if (!((new BigInteger((_242_r0).Count)).Sign == 0)) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sets/Sets.dfy(83,0): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
    }
    [Xunit.Fact]
    public static void test9()
    {
      if (!((new BigInteger(3)).Sign != -1)) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sets/Sets.dfy(88,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      Dafny.ISet<BigInteger> _243_r0;
      _243_r0 = Sets_Compile.__default.SetRangeZeroBound(new BigInteger(3));
      if (!((new BigInteger((_243_r0).Count)) == (new BigInteger(3)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sets/Sets.dfy(90,0): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
    }
  }
} // end of namespace srcCollectionsSetsSetsdfyUnitTests_Compile
namespace Uint8__16_mUint8Seq_Compile {

  public partial class __default {
    public static BigInteger BITS() {
      return new BigInteger(8);
    }
    public static BigInteger BASE() {
      return Power_Compile.__default.Pow(new BigInteger(2), Uint8__16_mUint8Seq_Compile.__default.BITS());
    }
    public static BigInteger ToNatRight(Dafny.ISequence<BigInteger> xs) {
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return BigInteger.Zero;
      } else {
        return ((Uint8__16_mUint8Seq_Compile.__default.ToNatRight(Seq_Compile.__default.DropFirst<BigInteger>(xs))) * (Uint8__16_mUint8Seq_Compile.__default.BASE())) + (Seq_Compile.__default.First<BigInteger>(xs));
      }
    }
    public static BigInteger ToNatLeft(Dafny.ISequence<BigInteger> xs) {
      BigInteger _244___accumulator = BigInteger.Zero;
    TAIL_CALL_START: ;
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return (BigInteger.Zero) + (_244___accumulator);
      } else {
        _244___accumulator = ((Seq_Compile.__default.Last<BigInteger>(xs)) * (Power_Compile.__default.Pow(Uint8__16_mUint8Seq_Compile.__default.BASE(), (new BigInteger((xs).Count)) - (BigInteger.One)))) + (_244___accumulator);
        Dafny.ISequence<BigInteger> _in34 = Seq_Compile.__default.DropLast<BigInteger>(xs);
        xs = _in34;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<BigInteger> FromNat(BigInteger n) {
      Dafny.ISequence<BigInteger> _245___accumulator = Dafny.Sequence<BigInteger>.FromElements();
    TAIL_CALL_START: ;
      if ((n).Sign == 0) {
        return Dafny.Sequence<BigInteger>.Concat(_245___accumulator, Dafny.Sequence<BigInteger>.FromElements());
      } else {
        _245___accumulator = Dafny.Sequence<BigInteger>.Concat(_245___accumulator, Dafny.Sequence<BigInteger>.FromElements(Dafny.Helpers.EuclideanModulus(n, Uint8__16_mUint8Seq_Compile.__default.BASE())));
        BigInteger _in35 = Dafny.Helpers.EuclideanDivision(n, Uint8__16_mUint8Seq_Compile.__default.BASE());
        n = _in35;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<BigInteger> SeqExtend(Dafny.ISequence<BigInteger> xs, BigInteger n)
    {
    TAIL_CALL_START: ;
      if ((new BigInteger((xs).Count)) >= (n)) {
        return xs;
      } else {
        Dafny.ISequence<BigInteger> _in36 = Dafny.Sequence<BigInteger>.Concat(xs, Dafny.Sequence<BigInteger>.FromElements(BigInteger.Zero));
        BigInteger _in37 = n;
        xs = _in36;
        n = _in37;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<BigInteger> SeqExtendMultiple(Dafny.ISequence<BigInteger> xs, BigInteger n)
    {
      BigInteger _246_newLen = ((new BigInteger((xs).Count)) + (n)) - (Dafny.Helpers.EuclideanModulus(new BigInteger((xs).Count), n));
      return Uint8__16_mUint8Seq_Compile.__default.SeqExtend(xs, _246_newLen);
    }
    public static Dafny.ISequence<BigInteger> FromNatWithLen(BigInteger n, BigInteger len)
    {
      return Uint8__16_mUint8Seq_Compile.__default.SeqExtend(Uint8__16_mUint8Seq_Compile.__default.FromNat(n), len);
    }
    public static Dafny.ISequence<BigInteger> SeqZero(BigInteger len) {
      Dafny.ISequence<BigInteger> _247_xs = Uint8__16_mUint8Seq_Compile.__default.FromNatWithLen(BigInteger.Zero, len);
      return _247_xs;
    }
    public static _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> SeqAdd(Dafny.ISequence<BigInteger> xs, Dafny.ISequence<BigInteger> ys)
    {
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return _System.Tuple2<Dafny.ISequence<BigInteger>, BigInteger>.create(Dafny.Sequence<BigInteger>.FromElements(), BigInteger.Zero);
      } else {
        _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> _let_tmp_rhs1 = Uint8__16_mUint8Seq_Compile.__default.SeqAdd(Seq_Compile.__default.DropLast<BigInteger>(xs), Seq_Compile.__default.DropLast<BigInteger>(ys));
        Dafny.ISequence<BigInteger> _248_zs_k = _let_tmp_rhs1.dtor__0;
        BigInteger _249_cin = _let_tmp_rhs1.dtor__1;
        BigInteger _250_sum = ((Seq_Compile.__default.Last<BigInteger>(xs)) + (Seq_Compile.__default.Last<BigInteger>(ys))) + (_249_cin);
        _System._ITuple2<BigInteger, BigInteger> _let_tmp_rhs2 = (((_250_sum) < (Uint8__16_mUint8Seq_Compile.__default.BASE())) ? (_System.Tuple2<BigInteger, BigInteger>.create(_250_sum, BigInteger.Zero)) : (_System.Tuple2<BigInteger, BigInteger>.create((_250_sum) - (Uint8__16_mUint8Seq_Compile.__default.BASE()), BigInteger.One)));
        BigInteger _251_sum__out = _let_tmp_rhs2.dtor__0;
        BigInteger _252_cout = _let_tmp_rhs2.dtor__1;
        return _System.Tuple2<Dafny.ISequence<BigInteger>, BigInteger>.create(Dafny.Sequence<BigInteger>.Concat(_248_zs_k, Dafny.Sequence<BigInteger>.FromElements(_251_sum__out)), _252_cout);
      }
    }
    public static _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> SeqSub(Dafny.ISequence<BigInteger> xs, Dafny.ISequence<BigInteger> ys)
    {
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return _System.Tuple2<Dafny.ISequence<BigInteger>, BigInteger>.create(Dafny.Sequence<BigInteger>.FromElements(), BigInteger.Zero);
      } else {
        _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> _let_tmp_rhs3 = Uint8__16_mUint8Seq_Compile.__default.SeqSub(Seq_Compile.__default.DropLast<BigInteger>(xs), Seq_Compile.__default.DropLast<BigInteger>(ys));
        Dafny.ISequence<BigInteger> _253_zs = _let_tmp_rhs3.dtor__0;
        BigInteger _254_cin = _let_tmp_rhs3.dtor__1;
        _System._ITuple2<BigInteger, BigInteger> _let_tmp_rhs4 = (((Seq_Compile.__default.Last<BigInteger>(xs)) >= ((Seq_Compile.__default.Last<BigInteger>(ys)) + (_254_cin))) ? (_System.Tuple2<BigInteger, BigInteger>.create(((Seq_Compile.__default.Last<BigInteger>(xs)) - (Seq_Compile.__default.Last<BigInteger>(ys))) - (_254_cin), BigInteger.Zero)) : (_System.Tuple2<BigInteger, BigInteger>.create((((Uint8__16_mUint8Seq_Compile.__default.BASE()) + (Seq_Compile.__default.Last<BigInteger>(xs))) - (Seq_Compile.__default.Last<BigInteger>(ys))) - (_254_cin), BigInteger.One)));
        BigInteger _255_diff__out = _let_tmp_rhs4.dtor__0;
        BigInteger _256_cout = _let_tmp_rhs4.dtor__1;
        return _System.Tuple2<Dafny.ISequence<BigInteger>, BigInteger>.create(Dafny.Sequence<BigInteger>.Concat(_253_zs, Dafny.Sequence<BigInteger>.FromElements(_255_diff__out)), _256_cout);
      }
    }
  }

  public partial class @uint {
    private static readonly Dafny.TypeDescriptor<BigInteger> _TYPE = new Dafny.TypeDescriptor<BigInteger>(BigInteger.Zero);
    public static Dafny.TypeDescriptor<BigInteger> _TypeDescriptor() {
      return _TYPE;
    }
  }
} // end of namespace Uint8__16_mUint8Seq_Compile
namespace Uint8__16_mUint16Seq_Compile {

  public partial class __default {
    public static BigInteger BITS() {
      return new BigInteger(16);
    }
    public static BigInteger BASE() {
      return Power_Compile.__default.Pow(new BigInteger(2), Uint8__16_mUint16Seq_Compile.__default.BITS());
    }
    public static BigInteger ToNatRight(Dafny.ISequence<BigInteger> xs) {
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return BigInteger.Zero;
      } else {
        return ((Uint8__16_mUint16Seq_Compile.__default.ToNatRight(Seq_Compile.__default.DropFirst<BigInteger>(xs))) * (Uint8__16_mUint16Seq_Compile.__default.BASE())) + (Seq_Compile.__default.First<BigInteger>(xs));
      }
    }
    public static BigInteger ToNatLeft(Dafny.ISequence<BigInteger> xs) {
      BigInteger _257___accumulator = BigInteger.Zero;
    TAIL_CALL_START: ;
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return (BigInteger.Zero) + (_257___accumulator);
      } else {
        _257___accumulator = ((Seq_Compile.__default.Last<BigInteger>(xs)) * (Power_Compile.__default.Pow(Uint8__16_mUint16Seq_Compile.__default.BASE(), (new BigInteger((xs).Count)) - (BigInteger.One)))) + (_257___accumulator);
        Dafny.ISequence<BigInteger> _in38 = Seq_Compile.__default.DropLast<BigInteger>(xs);
        xs = _in38;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<BigInteger> FromNat(BigInteger n) {
      Dafny.ISequence<BigInteger> _258___accumulator = Dafny.Sequence<BigInteger>.FromElements();
    TAIL_CALL_START: ;
      if ((n).Sign == 0) {
        return Dafny.Sequence<BigInteger>.Concat(_258___accumulator, Dafny.Sequence<BigInteger>.FromElements());
      } else {
        _258___accumulator = Dafny.Sequence<BigInteger>.Concat(_258___accumulator, Dafny.Sequence<BigInteger>.FromElements(Dafny.Helpers.EuclideanModulus(n, Uint8__16_mUint16Seq_Compile.__default.BASE())));
        BigInteger _in39 = Dafny.Helpers.EuclideanDivision(n, Uint8__16_mUint16Seq_Compile.__default.BASE());
        n = _in39;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<BigInteger> SeqExtend(Dafny.ISequence<BigInteger> xs, BigInteger n)
    {
    TAIL_CALL_START: ;
      if ((new BigInteger((xs).Count)) >= (n)) {
        return xs;
      } else {
        Dafny.ISequence<BigInteger> _in40 = Dafny.Sequence<BigInteger>.Concat(xs, Dafny.Sequence<BigInteger>.FromElements(BigInteger.Zero));
        BigInteger _in41 = n;
        xs = _in40;
        n = _in41;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<BigInteger> SeqExtendMultiple(Dafny.ISequence<BigInteger> xs, BigInteger n)
    {
      BigInteger _259_newLen = ((new BigInteger((xs).Count)) + (n)) - (Dafny.Helpers.EuclideanModulus(new BigInteger((xs).Count), n));
      return Uint8__16_mUint16Seq_Compile.__default.SeqExtend(xs, _259_newLen);
    }
    public static Dafny.ISequence<BigInteger> FromNatWithLen(BigInteger n, BigInteger len)
    {
      return Uint8__16_mUint16Seq_Compile.__default.SeqExtend(Uint8__16_mUint16Seq_Compile.__default.FromNat(n), len);
    }
    public static Dafny.ISequence<BigInteger> SeqZero(BigInteger len) {
      Dafny.ISequence<BigInteger> _260_xs = Uint8__16_mUint16Seq_Compile.__default.FromNatWithLen(BigInteger.Zero, len);
      return _260_xs;
    }
    public static _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> SeqAdd(Dafny.ISequence<BigInteger> xs, Dafny.ISequence<BigInteger> ys)
    {
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return _System.Tuple2<Dafny.ISequence<BigInteger>, BigInteger>.create(Dafny.Sequence<BigInteger>.FromElements(), BigInteger.Zero);
      } else {
        _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> _let_tmp_rhs5 = Uint8__16_mUint16Seq_Compile.__default.SeqAdd(Seq_Compile.__default.DropLast<BigInteger>(xs), Seq_Compile.__default.DropLast<BigInteger>(ys));
        Dafny.ISequence<BigInteger> _261_zs_k = _let_tmp_rhs5.dtor__0;
        BigInteger _262_cin = _let_tmp_rhs5.dtor__1;
        BigInteger _263_sum = ((Seq_Compile.__default.Last<BigInteger>(xs)) + (Seq_Compile.__default.Last<BigInteger>(ys))) + (_262_cin);
        _System._ITuple2<BigInteger, BigInteger> _let_tmp_rhs6 = (((_263_sum) < (Uint8__16_mUint16Seq_Compile.__default.BASE())) ? (_System.Tuple2<BigInteger, BigInteger>.create(_263_sum, BigInteger.Zero)) : (_System.Tuple2<BigInteger, BigInteger>.create((_263_sum) - (Uint8__16_mUint16Seq_Compile.__default.BASE()), BigInteger.One)));
        BigInteger _264_sum__out = _let_tmp_rhs6.dtor__0;
        BigInteger _265_cout = _let_tmp_rhs6.dtor__1;
        return _System.Tuple2<Dafny.ISequence<BigInteger>, BigInteger>.create(Dafny.Sequence<BigInteger>.Concat(_261_zs_k, Dafny.Sequence<BigInteger>.FromElements(_264_sum__out)), _265_cout);
      }
    }
    public static _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> SeqSub(Dafny.ISequence<BigInteger> xs, Dafny.ISequence<BigInteger> ys)
    {
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return _System.Tuple2<Dafny.ISequence<BigInteger>, BigInteger>.create(Dafny.Sequence<BigInteger>.FromElements(), BigInteger.Zero);
      } else {
        _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> _let_tmp_rhs7 = Uint8__16_mUint16Seq_Compile.__default.SeqSub(Seq_Compile.__default.DropLast<BigInteger>(xs), Seq_Compile.__default.DropLast<BigInteger>(ys));
        Dafny.ISequence<BigInteger> _266_zs = _let_tmp_rhs7.dtor__0;
        BigInteger _267_cin = _let_tmp_rhs7.dtor__1;
        _System._ITuple2<BigInteger, BigInteger> _let_tmp_rhs8 = (((Seq_Compile.__default.Last<BigInteger>(xs)) >= ((Seq_Compile.__default.Last<BigInteger>(ys)) + (_267_cin))) ? (_System.Tuple2<BigInteger, BigInteger>.create(((Seq_Compile.__default.Last<BigInteger>(xs)) - (Seq_Compile.__default.Last<BigInteger>(ys))) - (_267_cin), BigInteger.Zero)) : (_System.Tuple2<BigInteger, BigInteger>.create((((Uint8__16_mUint16Seq_Compile.__default.BASE()) + (Seq_Compile.__default.Last<BigInteger>(xs))) - (Seq_Compile.__default.Last<BigInteger>(ys))) - (_267_cin), BigInteger.One)));
        BigInteger _268_diff__out = _let_tmp_rhs8.dtor__0;
        BigInteger _269_cout = _let_tmp_rhs8.dtor__1;
        return _System.Tuple2<Dafny.ISequence<BigInteger>, BigInteger>.create(Dafny.Sequence<BigInteger>.Concat(_266_zs, Dafny.Sequence<BigInteger>.FromElements(_268_diff__out)), _269_cout);
      }
    }
  }

  public partial class @uint {
    private static readonly Dafny.TypeDescriptor<BigInteger> _TYPE = new Dafny.TypeDescriptor<BigInteger>(BigInteger.Zero);
    public static Dafny.TypeDescriptor<BigInteger> _TypeDescriptor() {
      return _TYPE;
    }
  }
} // end of namespace Uint8__16_mUint16Seq_Compile
namespace Uint8__16_Compile {

  public partial class __default {
    public static BigInteger E() {
      return Dafny.Helpers.EuclideanDivision(Uint8__16_mUint16Seq_Compile.__default.BITS(), Uint8__16_mUint8Seq_Compile.__default.BITS());
    }
    public static Dafny.ISequence<BigInteger> ToSmall(Dafny.ISequence<BigInteger> xs) {
      Dafny.ISequence<BigInteger> _270___accumulator = Dafny.Sequence<BigInteger>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return Dafny.Sequence<BigInteger>.Concat(_270___accumulator, Dafny.Sequence<BigInteger>.FromElements());
      } else {
        _270___accumulator = Dafny.Sequence<BigInteger>.Concat(_270___accumulator, Uint8__16_mUint8Seq_Compile.__default.FromNatWithLen(Seq_Compile.__default.First<BigInteger>(xs), Uint8__16_Compile.__default.E()));
        Dafny.ISequence<BigInteger> _in42 = Seq_Compile.__default.DropFirst<BigInteger>(xs);
        xs = _in42;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<BigInteger> ToLarge(Dafny.ISequence<BigInteger> xs) {
      Dafny.ISequence<BigInteger> _271___accumulator = Dafny.Sequence<BigInteger>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return Dafny.Sequence<BigInteger>.Concat(_271___accumulator, Dafny.Sequence<BigInteger>.FromElements());
      } else {
        _271___accumulator = Dafny.Sequence<BigInteger>.Concat(_271___accumulator, Dafny.Sequence<BigInteger>.FromElements(Uint8__16_mUint8Seq_Compile.__default.ToNatRight((xs).Take(Uint8__16_Compile.__default.E()))));
        Dafny.ISequence<BigInteger> _in43 = (xs).Drop(Uint8__16_Compile.__default.E());
        xs = _in43;
        goto TAIL_CALL_START;
      }
    }
  }
} // end of namespace Uint8__16_Compile
namespace srcCollectionsSequencesUint8__16dfyUnitTests_Compile {

  public partial class __default {
    [Xunit.Fact]
    public static void test0()
    {
      Dafny.ISequence<BigInteger> _272_d0;
      _272_d0 = Dafny.Sequence<BigInteger>.FromElements();
      BigInteger _273_r0;
      _273_r0 = Uint8__16_mUint8Seq_Compile.__default.ToNatRight(_272_d0);
    }
    [Xunit.Fact]
    public static void test1()
    {
      Dafny.ISequence<BigInteger> _274_d0;
      _274_d0 = Dafny.Sequence<BigInteger>.FromElements();
      BigInteger _275_r0;
      _275_r0 = Uint8__16_mUint8Seq_Compile.__default.ToNatLeft(_274_d0);
    }
    [Xunit.Fact]
    public static void test2()
    {
      Dafny.ISequence<BigInteger> _276_r0;
      _276_r0 = Uint8__16_mUint8Seq_Compile.__default.FromNat(new BigInteger(65));
    }
    [Xunit.Fact]
    public static void test3()
    {
      Dafny.ISequence<BigInteger> _277_r0;
      _277_r0 = Uint8__16_mUint8Seq_Compile.__default.FromNat(BigInteger.Zero);
    }
    [Xunit.Fact]
    public static void test4()
    {
      Dafny.ISequence<BigInteger> _278_d0;
      _278_d0 = Dafny.Sequence<BigInteger>.FromElements(BigInteger.Zero);
      if (!((new BigInteger((_278_d0).Count)) <= (BigInteger.One))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint8_16.dfy(69,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      Dafny.ISequence<BigInteger> _279_r0;
      _279_r0 = Uint8__16_mUint8Seq_Compile.__default.SeqExtend(_278_d0, BigInteger.One);
      if (!((new BigInteger((_279_r0).Count)) == (BigInteger.One))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint8_16.dfy(71,0): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
      if (!((Uint8__16_mUint8Seq_Compile.__default.ToNatRight(_279_r0)) == (Uint8__16_mUint8Seq_Compile.__default.ToNatRight(_278_d0)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint8_16.dfy(72,0): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
    }
    [Xunit.Fact]
    public static void test5()
    {
      Dafny.ISequence<BigInteger> _280_d0;
      _280_d0 = Dafny.Sequence<BigInteger>.FromElements(BigInteger.Zero, BigInteger.Zero);
      Dafny.ISequence<BigInteger> _281_d1;
      _281_d1 = Dafny.Sequence<BigInteger>.FromElements(BigInteger.Zero, BigInteger.Zero);
      if (!((new BigInteger((_280_d0).Count)) == (new BigInteger((_281_d1).Count)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint8_16.dfy(86,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> _282_r0;
      _282_r0 = Uint8__16_mUint8Seq_Compile.__default.SeqAdd(_280_d0, _281_d1);
    }
    [Xunit.Fact]
    public static void test6()
    {
      Dafny.ISequence<BigInteger> _283_d0;
      _283_d0 = Dafny.Sequence<BigInteger>.FromElements(new BigInteger(12), new BigInteger(2283));
      Dafny.ISequence<BigInteger> _284_d1;
      _284_d1 = Dafny.Sequence<BigInteger>.FromElements(new BigInteger(281), new BigInteger(11138));
      if (!((new BigInteger((_283_d0).Count)) == (new BigInteger((_284_d1).Count)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint8_16.dfy(96,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> _285_r0;
      _285_r0 = Uint8__16_mUint8Seq_Compile.__default.SeqAdd(_283_d0, _284_d1);
    }
    [Xunit.Fact]
    public static void test7()
    {
      Dafny.ISequence<BigInteger> _286_d0;
      _286_d0 = Dafny.Sequence<BigInteger>.FromElements();
      Dafny.ISequence<BigInteger> _287_d1;
      _287_d1 = Dafny.Sequence<BigInteger>.FromElements();
      if (!((new BigInteger((_286_d0).Count)) == (new BigInteger((_287_d1).Count)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint8_16.dfy(105,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> _288_r0;
      _288_r0 = Uint8__16_mUint8Seq_Compile.__default.SeqAdd(_286_d0, _287_d1);
    }
    [Xunit.Fact]
    public static void test8()
    {
      Dafny.ISequence<BigInteger> _289_d0;
      _289_d0 = Dafny.Sequence<BigInteger>.FromElements(new BigInteger(1325), new BigInteger(2331));
      Dafny.ISequence<BigInteger> _290_d1;
      _290_d1 = Dafny.Sequence<BigInteger>.FromElements(new BigInteger(234), new BigInteger(1796));
      if (!((new BigInteger((_289_d0).Count)) == (new BigInteger((_290_d1).Count)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint8_16.dfy(117,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> _291_r0;
      _291_r0 = Uint8__16_mUint8Seq_Compile.__default.SeqSub(_289_d0, _290_d1);
    }
    [Xunit.Fact]
    public static void test9()
    {
      Dafny.ISequence<BigInteger> _292_d0;
      _292_d0 = Dafny.Sequence<BigInteger>.FromElements(new BigInteger(920), new BigInteger(2061));
      Dafny.ISequence<BigInteger> _293_d1;
      _293_d1 = Dafny.Sequence<BigInteger>.FromElements(new BigInteger(645), new BigInteger(2062));
      if (!((new BigInteger((_292_d0).Count)) == (new BigInteger((_293_d1).Count)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint8_16.dfy(127,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> _294_r0;
      _294_r0 = Uint8__16_mUint8Seq_Compile.__default.SeqSub(_292_d0, _293_d1);
    }
    [Xunit.Fact]
    public static void test10()
    {
      Dafny.ISequence<BigInteger> _295_d0;
      _295_d0 = Dafny.Sequence<BigInteger>.FromElements();
      Dafny.ISequence<BigInteger> _296_d1;
      _296_d1 = Dafny.Sequence<BigInteger>.FromElements();
      if (!((new BigInteger((_295_d0).Count)) == (new BigInteger((_296_d1).Count)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint8_16.dfy(136,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> _297_r0;
      _297_r0 = Uint8__16_mUint8Seq_Compile.__default.SeqSub(_295_d0, _296_d1);
    }
    [Xunit.Fact]
    public static void test11()
    {
      Dafny.ISequence<BigInteger> _298_d0;
      _298_d0 = Dafny.Sequence<BigInteger>.FromElements();
      BigInteger _299_r0;
      _299_r0 = Uint8__16_mUint16Seq_Compile.__default.ToNatRight(_298_d0);
    }
    [Xunit.Fact]
    public static void test12()
    {
      Dafny.ISequence<BigInteger> _300_d0;
      _300_d0 = Dafny.Sequence<BigInteger>.FromElements();
      BigInteger _301_r0;
      _301_r0 = Uint8__16_mUint16Seq_Compile.__default.ToNatLeft(_300_d0);
    }
    [Xunit.Fact]
    public static void test13()
    {
      Dafny.ISequence<BigInteger> _302_r0;
      _302_r0 = Uint8__16_mUint16Seq_Compile.__default.FromNat(new BigInteger(65));
    }
    [Xunit.Fact]
    public static void test14()
    {
      Dafny.ISequence<BigInteger> _303_r0;
      _303_r0 = Uint8__16_mUint16Seq_Compile.__default.FromNat(BigInteger.Zero);
    }
    [Xunit.Fact]
    public static void test15()
    {
      Dafny.ISequence<BigInteger> _304_d0;
      _304_d0 = Dafny.Sequence<BigInteger>.FromElements(BigInteger.Zero);
      if (!((new BigInteger((_304_d0).Count)) <= (BigInteger.One))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint8_16.dfy(177,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      Dafny.ISequence<BigInteger> _305_r0;
      _305_r0 = Uint8__16_mUint16Seq_Compile.__default.SeqExtend(_304_d0, BigInteger.One);
      if (!((new BigInteger((_305_r0).Count)) == (BigInteger.One))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint8_16.dfy(179,0): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
      if (!((Uint8__16_mUint16Seq_Compile.__default.ToNatRight(_305_r0)) == (Uint8__16_mUint16Seq_Compile.__default.ToNatRight(_304_d0)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint8_16.dfy(180,0): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
    }
    [Xunit.Fact]
    public static void test16()
    {
      Dafny.ISequence<BigInteger> _306_d0;
      _306_d0 = Dafny.Sequence<BigInteger>.FromElements(BigInteger.Zero, BigInteger.Zero);
      Dafny.ISequence<BigInteger> _307_d1;
      _307_d1 = Dafny.Sequence<BigInteger>.FromElements(BigInteger.Zero, BigInteger.Zero);
      if (!((new BigInteger((_306_d0).Count)) == (new BigInteger((_307_d1).Count)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint8_16.dfy(194,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> _308_r0;
      _308_r0 = Uint8__16_mUint16Seq_Compile.__default.SeqAdd(_306_d0, _307_d1);
    }
    [Xunit.Fact]
    public static void test17()
    {
      Dafny.ISequence<BigInteger> _309_d0;
      _309_d0 = Dafny.Sequence<BigInteger>.FromElements(new BigInteger(342), new BigInteger(4720));
      Dafny.ISequence<BigInteger> _310_d1;
      _310_d1 = Dafny.Sequence<BigInteger>.FromElements(new BigInteger(281), new BigInteger(2283));
      if (!((new BigInteger((_309_d0).Count)) == (new BigInteger((_310_d1).Count)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint8_16.dfy(204,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> _311_r0;
      _311_r0 = Uint8__16_mUint16Seq_Compile.__default.SeqAdd(_309_d0, _310_d1);
    }
    [Xunit.Fact]
    public static void test18()
    {
      Dafny.ISequence<BigInteger> _312_d0;
      _312_d0 = Dafny.Sequence<BigInteger>.FromElements();
      Dafny.ISequence<BigInteger> _313_d1;
      _313_d1 = Dafny.Sequence<BigInteger>.FromElements();
      if (!((new BigInteger((_312_d0).Count)) == (new BigInteger((_313_d1).Count)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint8_16.dfy(213,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> _314_r0;
      _314_r0 = Uint8__16_mUint16Seq_Compile.__default.SeqAdd(_312_d0, _313_d1);
    }
    [Xunit.Fact]
    public static void test19()
    {
      Dafny.ISequence<BigInteger> _315_d0;
      _315_d0 = Dafny.Sequence<BigInteger>.FromElements(new BigInteger(1325), new BigInteger(2331));
      Dafny.ISequence<BigInteger> _316_d1;
      _316_d1 = Dafny.Sequence<BigInteger>.FromElements(new BigInteger(234), new BigInteger(1796));
      if (!((new BigInteger((_315_d0).Count)) == (new BigInteger((_316_d1).Count)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint8_16.dfy(225,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> _317_r0;
      _317_r0 = Uint8__16_mUint16Seq_Compile.__default.SeqSub(_315_d0, _316_d1);
    }
    [Xunit.Fact]
    public static void test20()
    {
      Dafny.ISequence<BigInteger> _318_d0;
      _318_d0 = Dafny.Sequence<BigInteger>.FromElements(new BigInteger(920), new BigInteger(2061));
      Dafny.ISequence<BigInteger> _319_d1;
      _319_d1 = Dafny.Sequence<BigInteger>.FromElements(new BigInteger(645), new BigInteger(2062));
      if (!((new BigInteger((_318_d0).Count)) == (new BigInteger((_319_d1).Count)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint8_16.dfy(235,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> _320_r0;
      _320_r0 = Uint8__16_mUint16Seq_Compile.__default.SeqSub(_318_d0, _319_d1);
    }
    [Xunit.Fact]
    public static void test21()
    {
      Dafny.ISequence<BigInteger> _321_d0;
      _321_d0 = Dafny.Sequence<BigInteger>.FromElements();
      Dafny.ISequence<BigInteger> _322_d1;
      _322_d1 = Dafny.Sequence<BigInteger>.FromElements();
      if (!((new BigInteger((_321_d0).Count)) == (new BigInteger((_322_d1).Count)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint8_16.dfy(244,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> _323_r0;
      _323_r0 = Uint8__16_mUint16Seq_Compile.__default.SeqSub(_321_d0, _322_d1);
    }
    [Xunit.Fact]
    public static void test22()
    {
      Dafny.ISequence<BigInteger> _324_d0;
      _324_d0 = Dafny.Sequence<BigInteger>.FromElements();
      Dafny.ISequence<BigInteger> _325_r0;
      _325_r0 = Uint8__16_Compile.__default.ToSmall(_324_d0);
      if (!((new BigInteger((_325_r0).Count)) == ((new BigInteger((_324_d0).Count)) * (Uint8__16_Compile.__default.E())))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint8_16.dfy(256,0): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
    }
    [Xunit.Fact]
    public static void test23()
    {
      Dafny.ISequence<BigInteger> _326_d0;
      _326_d0 = Dafny.Sequence<BigInteger>.FromElements(BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero);
      if (!((Dafny.Helpers.EuclideanModulus(new BigInteger((_326_d0).Count), Uint8__16_Compile.__default.E())).Sign == 0)) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint8_16.dfy(265,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      Dafny.ISequence<BigInteger> _327_r0;
      _327_r0 = Uint8__16_Compile.__default.ToLarge(_326_d0);
      if (!((new BigInteger((_327_r0).Count)) == (Dafny.Helpers.EuclideanDivision(new BigInteger((_326_d0).Count), Uint8__16_Compile.__default.E())))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint8_16.dfy(267,0): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
    }
  }
} // end of namespace srcCollectionsSequencesUint8__16dfyUnitTests_Compile
namespace Uint8__32_mUint8Seq_Compile {

  public partial class __default {
    public static BigInteger BITS() {
      return new BigInteger(8);
    }
    public static BigInteger BASE() {
      return Power_Compile.__default.Pow(new BigInteger(2), Uint8__32_mUint8Seq_Compile.__default.BITS());
    }
    public static BigInteger ToNatRight(Dafny.ISequence<BigInteger> xs) {
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return BigInteger.Zero;
      } else {
        return ((Uint8__32_mUint8Seq_Compile.__default.ToNatRight(Seq_Compile.__default.DropFirst<BigInteger>(xs))) * (Uint8__32_mUint8Seq_Compile.__default.BASE())) + (Seq_Compile.__default.First<BigInteger>(xs));
      }
    }
    public static BigInteger ToNatLeft(Dafny.ISequence<BigInteger> xs) {
      BigInteger _328___accumulator = BigInteger.Zero;
    TAIL_CALL_START: ;
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return (BigInteger.Zero) + (_328___accumulator);
      } else {
        _328___accumulator = ((Seq_Compile.__default.Last<BigInteger>(xs)) * (Power_Compile.__default.Pow(Uint8__32_mUint8Seq_Compile.__default.BASE(), (new BigInteger((xs).Count)) - (BigInteger.One)))) + (_328___accumulator);
        Dafny.ISequence<BigInteger> _in44 = Seq_Compile.__default.DropLast<BigInteger>(xs);
        xs = _in44;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<BigInteger> FromNat(BigInteger n) {
      Dafny.ISequence<BigInteger> _329___accumulator = Dafny.Sequence<BigInteger>.FromElements();
    TAIL_CALL_START: ;
      if ((n).Sign == 0) {
        return Dafny.Sequence<BigInteger>.Concat(_329___accumulator, Dafny.Sequence<BigInteger>.FromElements());
      } else {
        _329___accumulator = Dafny.Sequence<BigInteger>.Concat(_329___accumulator, Dafny.Sequence<BigInteger>.FromElements(Dafny.Helpers.EuclideanModulus(n, Uint8__32_mUint8Seq_Compile.__default.BASE())));
        BigInteger _in45 = Dafny.Helpers.EuclideanDivision(n, Uint8__32_mUint8Seq_Compile.__default.BASE());
        n = _in45;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<BigInteger> SeqExtend(Dafny.ISequence<BigInteger> xs, BigInteger n)
    {
    TAIL_CALL_START: ;
      if ((new BigInteger((xs).Count)) >= (n)) {
        return xs;
      } else {
        Dafny.ISequence<BigInteger> _in46 = Dafny.Sequence<BigInteger>.Concat(xs, Dafny.Sequence<BigInteger>.FromElements(BigInteger.Zero));
        BigInteger _in47 = n;
        xs = _in46;
        n = _in47;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<BigInteger> SeqExtendMultiple(Dafny.ISequence<BigInteger> xs, BigInteger n)
    {
      BigInteger _330_newLen = ((new BigInteger((xs).Count)) + (n)) - (Dafny.Helpers.EuclideanModulus(new BigInteger((xs).Count), n));
      return Uint8__32_mUint8Seq_Compile.__default.SeqExtend(xs, _330_newLen);
    }
    public static Dafny.ISequence<BigInteger> FromNatWithLen(BigInteger n, BigInteger len)
    {
      return Uint8__32_mUint8Seq_Compile.__default.SeqExtend(Uint8__32_mUint8Seq_Compile.__default.FromNat(n), len);
    }
    public static Dafny.ISequence<BigInteger> SeqZero(BigInteger len) {
      Dafny.ISequence<BigInteger> _331_xs = Uint8__32_mUint8Seq_Compile.__default.FromNatWithLen(BigInteger.Zero, len);
      return _331_xs;
    }
    public static _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> SeqAdd(Dafny.ISequence<BigInteger> xs, Dafny.ISequence<BigInteger> ys)
    {
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return _System.Tuple2<Dafny.ISequence<BigInteger>, BigInteger>.create(Dafny.Sequence<BigInteger>.FromElements(), BigInteger.Zero);
      } else {
        _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> _let_tmp_rhs9 = Uint8__32_mUint8Seq_Compile.__default.SeqAdd(Seq_Compile.__default.DropLast<BigInteger>(xs), Seq_Compile.__default.DropLast<BigInteger>(ys));
        Dafny.ISequence<BigInteger> _332_zs_k = _let_tmp_rhs9.dtor__0;
        BigInteger _333_cin = _let_tmp_rhs9.dtor__1;
        BigInteger _334_sum = ((Seq_Compile.__default.Last<BigInteger>(xs)) + (Seq_Compile.__default.Last<BigInteger>(ys))) + (_333_cin);
        _System._ITuple2<BigInteger, BigInteger> _let_tmp_rhs10 = (((_334_sum) < (Uint8__32_mUint8Seq_Compile.__default.BASE())) ? (_System.Tuple2<BigInteger, BigInteger>.create(_334_sum, BigInteger.Zero)) : (_System.Tuple2<BigInteger, BigInteger>.create((_334_sum) - (Uint8__32_mUint8Seq_Compile.__default.BASE()), BigInteger.One)));
        BigInteger _335_sum__out = _let_tmp_rhs10.dtor__0;
        BigInteger _336_cout = _let_tmp_rhs10.dtor__1;
        return _System.Tuple2<Dafny.ISequence<BigInteger>, BigInteger>.create(Dafny.Sequence<BigInteger>.Concat(_332_zs_k, Dafny.Sequence<BigInteger>.FromElements(_335_sum__out)), _336_cout);
      }
    }
    public static _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> SeqSub(Dafny.ISequence<BigInteger> xs, Dafny.ISequence<BigInteger> ys)
    {
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return _System.Tuple2<Dafny.ISequence<BigInteger>, BigInteger>.create(Dafny.Sequence<BigInteger>.FromElements(), BigInteger.Zero);
      } else {
        _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> _let_tmp_rhs11 = Uint8__32_mUint8Seq_Compile.__default.SeqSub(Seq_Compile.__default.DropLast<BigInteger>(xs), Seq_Compile.__default.DropLast<BigInteger>(ys));
        Dafny.ISequence<BigInteger> _337_zs = _let_tmp_rhs11.dtor__0;
        BigInteger _338_cin = _let_tmp_rhs11.dtor__1;
        _System._ITuple2<BigInteger, BigInteger> _let_tmp_rhs12 = (((Seq_Compile.__default.Last<BigInteger>(xs)) >= ((Seq_Compile.__default.Last<BigInteger>(ys)) + (_338_cin))) ? (_System.Tuple2<BigInteger, BigInteger>.create(((Seq_Compile.__default.Last<BigInteger>(xs)) - (Seq_Compile.__default.Last<BigInteger>(ys))) - (_338_cin), BigInteger.Zero)) : (_System.Tuple2<BigInteger, BigInteger>.create((((Uint8__32_mUint8Seq_Compile.__default.BASE()) + (Seq_Compile.__default.Last<BigInteger>(xs))) - (Seq_Compile.__default.Last<BigInteger>(ys))) - (_338_cin), BigInteger.One)));
        BigInteger _339_diff__out = _let_tmp_rhs12.dtor__0;
        BigInteger _340_cout = _let_tmp_rhs12.dtor__1;
        return _System.Tuple2<Dafny.ISequence<BigInteger>, BigInteger>.create(Dafny.Sequence<BigInteger>.Concat(_337_zs, Dafny.Sequence<BigInteger>.FromElements(_339_diff__out)), _340_cout);
      }
    }
  }

  public partial class @uint {
    private static readonly Dafny.TypeDescriptor<BigInteger> _TYPE = new Dafny.TypeDescriptor<BigInteger>(BigInteger.Zero);
    public static Dafny.TypeDescriptor<BigInteger> _TypeDescriptor() {
      return _TYPE;
    }
  }
} // end of namespace Uint8__32_mUint8Seq_Compile
namespace Uint8__32_mUint32Seq_Compile {

  public partial class __default {
    public static BigInteger BITS() {
      return new BigInteger(32);
    }
    public static BigInteger BASE() {
      return Power_Compile.__default.Pow(new BigInteger(2), Uint8__32_mUint32Seq_Compile.__default.BITS());
    }
    public static BigInteger ToNatRight(Dafny.ISequence<BigInteger> xs) {
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return BigInteger.Zero;
      } else {
        return ((Uint8__32_mUint32Seq_Compile.__default.ToNatRight(Seq_Compile.__default.DropFirst<BigInteger>(xs))) * (Uint8__32_mUint32Seq_Compile.__default.BASE())) + (Seq_Compile.__default.First<BigInteger>(xs));
      }
    }
    public static BigInteger ToNatLeft(Dafny.ISequence<BigInteger> xs) {
      BigInteger _341___accumulator = BigInteger.Zero;
    TAIL_CALL_START: ;
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return (BigInteger.Zero) + (_341___accumulator);
      } else {
        _341___accumulator = ((Seq_Compile.__default.Last<BigInteger>(xs)) * (Power_Compile.__default.Pow(Uint8__32_mUint32Seq_Compile.__default.BASE(), (new BigInteger((xs).Count)) - (BigInteger.One)))) + (_341___accumulator);
        Dafny.ISequence<BigInteger> _in48 = Seq_Compile.__default.DropLast<BigInteger>(xs);
        xs = _in48;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<BigInteger> FromNat(BigInteger n) {
      Dafny.ISequence<BigInteger> _342___accumulator = Dafny.Sequence<BigInteger>.FromElements();
    TAIL_CALL_START: ;
      if ((n).Sign == 0) {
        return Dafny.Sequence<BigInteger>.Concat(_342___accumulator, Dafny.Sequence<BigInteger>.FromElements());
      } else {
        _342___accumulator = Dafny.Sequence<BigInteger>.Concat(_342___accumulator, Dafny.Sequence<BigInteger>.FromElements(Dafny.Helpers.EuclideanModulus(n, Uint8__32_mUint32Seq_Compile.__default.BASE())));
        BigInteger _in49 = Dafny.Helpers.EuclideanDivision(n, Uint8__32_mUint32Seq_Compile.__default.BASE());
        n = _in49;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<BigInteger> SeqExtend(Dafny.ISequence<BigInteger> xs, BigInteger n)
    {
    TAIL_CALL_START: ;
      if ((new BigInteger((xs).Count)) >= (n)) {
        return xs;
      } else {
        Dafny.ISequence<BigInteger> _in50 = Dafny.Sequence<BigInteger>.Concat(xs, Dafny.Sequence<BigInteger>.FromElements(BigInteger.Zero));
        BigInteger _in51 = n;
        xs = _in50;
        n = _in51;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<BigInteger> SeqExtendMultiple(Dafny.ISequence<BigInteger> xs, BigInteger n)
    {
      BigInteger _343_newLen = ((new BigInteger((xs).Count)) + (n)) - (Dafny.Helpers.EuclideanModulus(new BigInteger((xs).Count), n));
      return Uint8__32_mUint32Seq_Compile.__default.SeqExtend(xs, _343_newLen);
    }
    public static Dafny.ISequence<BigInteger> FromNatWithLen(BigInteger n, BigInteger len)
    {
      return Uint8__32_mUint32Seq_Compile.__default.SeqExtend(Uint8__32_mUint32Seq_Compile.__default.FromNat(n), len);
    }
    public static Dafny.ISequence<BigInteger> SeqZero(BigInteger len) {
      Dafny.ISequence<BigInteger> _344_xs = Uint8__32_mUint32Seq_Compile.__default.FromNatWithLen(BigInteger.Zero, len);
      return _344_xs;
    }
    public static _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> SeqAdd(Dafny.ISequence<BigInteger> xs, Dafny.ISequence<BigInteger> ys)
    {
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return _System.Tuple2<Dafny.ISequence<BigInteger>, BigInteger>.create(Dafny.Sequence<BigInteger>.FromElements(), BigInteger.Zero);
      } else {
        _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> _let_tmp_rhs13 = Uint8__32_mUint32Seq_Compile.__default.SeqAdd(Seq_Compile.__default.DropLast<BigInteger>(xs), Seq_Compile.__default.DropLast<BigInteger>(ys));
        Dafny.ISequence<BigInteger> _345_zs_k = _let_tmp_rhs13.dtor__0;
        BigInteger _346_cin = _let_tmp_rhs13.dtor__1;
        BigInteger _347_sum = ((Seq_Compile.__default.Last<BigInteger>(xs)) + (Seq_Compile.__default.Last<BigInteger>(ys))) + (_346_cin);
        _System._ITuple2<BigInteger, BigInteger> _let_tmp_rhs14 = (((_347_sum) < (Uint8__32_mUint32Seq_Compile.__default.BASE())) ? (_System.Tuple2<BigInteger, BigInteger>.create(_347_sum, BigInteger.Zero)) : (_System.Tuple2<BigInteger, BigInteger>.create((_347_sum) - (Uint8__32_mUint32Seq_Compile.__default.BASE()), BigInteger.One)));
        BigInteger _348_sum__out = _let_tmp_rhs14.dtor__0;
        BigInteger _349_cout = _let_tmp_rhs14.dtor__1;
        return _System.Tuple2<Dafny.ISequence<BigInteger>, BigInteger>.create(Dafny.Sequence<BigInteger>.Concat(_345_zs_k, Dafny.Sequence<BigInteger>.FromElements(_348_sum__out)), _349_cout);
      }
    }
    public static _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> SeqSub(Dafny.ISequence<BigInteger> xs, Dafny.ISequence<BigInteger> ys)
    {
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return _System.Tuple2<Dafny.ISequence<BigInteger>, BigInteger>.create(Dafny.Sequence<BigInteger>.FromElements(), BigInteger.Zero);
      } else {
        _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> _let_tmp_rhs15 = Uint8__32_mUint32Seq_Compile.__default.SeqSub(Seq_Compile.__default.DropLast<BigInteger>(xs), Seq_Compile.__default.DropLast<BigInteger>(ys));
        Dafny.ISequence<BigInteger> _350_zs = _let_tmp_rhs15.dtor__0;
        BigInteger _351_cin = _let_tmp_rhs15.dtor__1;
        _System._ITuple2<BigInteger, BigInteger> _let_tmp_rhs16 = (((Seq_Compile.__default.Last<BigInteger>(xs)) >= ((Seq_Compile.__default.Last<BigInteger>(ys)) + (_351_cin))) ? (_System.Tuple2<BigInteger, BigInteger>.create(((Seq_Compile.__default.Last<BigInteger>(xs)) - (Seq_Compile.__default.Last<BigInteger>(ys))) - (_351_cin), BigInteger.Zero)) : (_System.Tuple2<BigInteger, BigInteger>.create((((Uint8__32_mUint32Seq_Compile.__default.BASE()) + (Seq_Compile.__default.Last<BigInteger>(xs))) - (Seq_Compile.__default.Last<BigInteger>(ys))) - (_351_cin), BigInteger.One)));
        BigInteger _352_diff__out = _let_tmp_rhs16.dtor__0;
        BigInteger _353_cout = _let_tmp_rhs16.dtor__1;
        return _System.Tuple2<Dafny.ISequence<BigInteger>, BigInteger>.create(Dafny.Sequence<BigInteger>.Concat(_350_zs, Dafny.Sequence<BigInteger>.FromElements(_352_diff__out)), _353_cout);
      }
    }
  }

  public partial class @uint {
    private static readonly Dafny.TypeDescriptor<BigInteger> _TYPE = new Dafny.TypeDescriptor<BigInteger>(BigInteger.Zero);
    public static Dafny.TypeDescriptor<BigInteger> _TypeDescriptor() {
      return _TYPE;
    }
  }
} // end of namespace Uint8__32_mUint32Seq_Compile
namespace Uint8__32_Compile {

  public partial class __default {
    public static BigInteger E() {
      return Dafny.Helpers.EuclideanDivision(Uint8__32_mUint32Seq_Compile.__default.BITS(), Uint8__32_mUint8Seq_Compile.__default.BITS());
    }
    public static Dafny.ISequence<BigInteger> ToSmall(Dafny.ISequence<BigInteger> xs) {
      Dafny.ISequence<BigInteger> _354___accumulator = Dafny.Sequence<BigInteger>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return Dafny.Sequence<BigInteger>.Concat(_354___accumulator, Dafny.Sequence<BigInteger>.FromElements());
      } else {
        _354___accumulator = Dafny.Sequence<BigInteger>.Concat(_354___accumulator, Uint8__32_mUint8Seq_Compile.__default.FromNatWithLen(Seq_Compile.__default.First<BigInteger>(xs), Uint8__32_Compile.__default.E()));
        Dafny.ISequence<BigInteger> _in52 = Seq_Compile.__default.DropFirst<BigInteger>(xs);
        xs = _in52;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<BigInteger> ToLarge(Dafny.ISequence<BigInteger> xs) {
      Dafny.ISequence<BigInteger> _355___accumulator = Dafny.Sequence<BigInteger>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return Dafny.Sequence<BigInteger>.Concat(_355___accumulator, Dafny.Sequence<BigInteger>.FromElements());
      } else {
        _355___accumulator = Dafny.Sequence<BigInteger>.Concat(_355___accumulator, Dafny.Sequence<BigInteger>.FromElements(Uint8__32_mUint8Seq_Compile.__default.ToNatRight((xs).Take(Uint8__32_Compile.__default.E()))));
        Dafny.ISequence<BigInteger> _in53 = (xs).Drop(Uint8__32_Compile.__default.E());
        xs = _in53;
        goto TAIL_CALL_START;
      }
    }
  }
} // end of namespace Uint8__32_Compile
namespace srcCollectionsSequencesUint8__32dfyUnitTests_Compile {

  public partial class __default {
    [Xunit.Fact]
    public static void test0()
    {
      Dafny.ISequence<BigInteger> _356_d0;
      _356_d0 = Dafny.Sequence<BigInteger>.FromElements();
      BigInteger _357_r0;
      _357_r0 = Uint8__32_mUint8Seq_Compile.__default.ToNatRight(_356_d0);
    }
    [Xunit.Fact]
    public static void test1()
    {
      Dafny.ISequence<BigInteger> _358_d0;
      _358_d0 = Dafny.Sequence<BigInteger>.FromElements();
      BigInteger _359_r0;
      _359_r0 = Uint8__32_mUint8Seq_Compile.__default.ToNatLeft(_358_d0);
    }
    [Xunit.Fact]
    public static void test2()
    {
      Dafny.ISequence<BigInteger> _360_r0;
      _360_r0 = Uint8__32_mUint8Seq_Compile.__default.FromNat(new BigInteger(65));
    }
    [Xunit.Fact]
    public static void test3()
    {
      Dafny.ISequence<BigInteger> _361_r0;
      _361_r0 = Uint8__32_mUint8Seq_Compile.__default.FromNat(BigInteger.Zero);
    }
    [Xunit.Fact]
    public static void test4()
    {
      Dafny.ISequence<BigInteger> _362_d0;
      _362_d0 = Dafny.Sequence<BigInteger>.FromElements(BigInteger.Zero);
      if (!((new BigInteger((_362_d0).Count)) <= (BigInteger.One))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint8_32.dfy(69,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      Dafny.ISequence<BigInteger> _363_r0;
      _363_r0 = Uint8__32_mUint8Seq_Compile.__default.SeqExtend(_362_d0, BigInteger.One);
      if (!((new BigInteger((_363_r0).Count)) == (BigInteger.One))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint8_32.dfy(71,0): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
      if (!((Uint8__32_mUint8Seq_Compile.__default.ToNatRight(_363_r0)) == (Uint8__32_mUint8Seq_Compile.__default.ToNatRight(_362_d0)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint8_32.dfy(72,0): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
    }
    [Xunit.Fact]
    public static void test5()
    {
      Dafny.ISequence<BigInteger> _364_d0;
      _364_d0 = Dafny.Sequence<BigInteger>.FromElements(BigInteger.Zero, BigInteger.Zero);
      Dafny.ISequence<BigInteger> _365_d1;
      _365_d1 = Dafny.Sequence<BigInteger>.FromElements(BigInteger.Zero, BigInteger.Zero);
      if (!((new BigInteger((_364_d0).Count)) == (new BigInteger((_365_d1).Count)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint8_32.dfy(86,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> _366_r0;
      _366_r0 = Uint8__32_mUint8Seq_Compile.__default.SeqAdd(_364_d0, _365_d1);
    }
    [Xunit.Fact]
    public static void test6()
    {
      Dafny.ISequence<BigInteger> _367_d0;
      _367_d0 = Dafny.Sequence<BigInteger>.FromElements(new BigInteger(12), new BigInteger(2283));
      Dafny.ISequence<BigInteger> _368_d1;
      _368_d1 = Dafny.Sequence<BigInteger>.FromElements(new BigInteger(281), new BigInteger(11138));
      if (!((new BigInteger((_367_d0).Count)) == (new BigInteger((_368_d1).Count)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint8_32.dfy(96,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> _369_r0;
      _369_r0 = Uint8__32_mUint8Seq_Compile.__default.SeqAdd(_367_d0, _368_d1);
    }
    [Xunit.Fact]
    public static void test7()
    {
      Dafny.ISequence<BigInteger> _370_d0;
      _370_d0 = Dafny.Sequence<BigInteger>.FromElements();
      Dafny.ISequence<BigInteger> _371_d1;
      _371_d1 = Dafny.Sequence<BigInteger>.FromElements();
      if (!((new BigInteger((_370_d0).Count)) == (new BigInteger((_371_d1).Count)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint8_32.dfy(105,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> _372_r0;
      _372_r0 = Uint8__32_mUint8Seq_Compile.__default.SeqAdd(_370_d0, _371_d1);
    }
    [Xunit.Fact]
    public static void test8()
    {
      Dafny.ISequence<BigInteger> _373_d0;
      _373_d0 = Dafny.Sequence<BigInteger>.FromElements(new BigInteger(1325), new BigInteger(2331));
      Dafny.ISequence<BigInteger> _374_d1;
      _374_d1 = Dafny.Sequence<BigInteger>.FromElements(new BigInteger(234), new BigInteger(1796));
      if (!((new BigInteger((_373_d0).Count)) == (new BigInteger((_374_d1).Count)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint8_32.dfy(117,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> _375_r0;
      _375_r0 = Uint8__32_mUint8Seq_Compile.__default.SeqSub(_373_d0, _374_d1);
    }
    [Xunit.Fact]
    public static void test9()
    {
      Dafny.ISequence<BigInteger> _376_d0;
      _376_d0 = Dafny.Sequence<BigInteger>.FromElements(new BigInteger(920), new BigInteger(2061));
      Dafny.ISequence<BigInteger> _377_d1;
      _377_d1 = Dafny.Sequence<BigInteger>.FromElements(new BigInteger(645), new BigInteger(2062));
      if (!((new BigInteger((_376_d0).Count)) == (new BigInteger((_377_d1).Count)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint8_32.dfy(127,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> _378_r0;
      _378_r0 = Uint8__32_mUint8Seq_Compile.__default.SeqSub(_376_d0, _377_d1);
    }
    [Xunit.Fact]
    public static void test10()
    {
      Dafny.ISequence<BigInteger> _379_d0;
      _379_d0 = Dafny.Sequence<BigInteger>.FromElements();
      Dafny.ISequence<BigInteger> _380_d1;
      _380_d1 = Dafny.Sequence<BigInteger>.FromElements();
      if (!((new BigInteger((_379_d0).Count)) == (new BigInteger((_380_d1).Count)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint8_32.dfy(136,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> _381_r0;
      _381_r0 = Uint8__32_mUint8Seq_Compile.__default.SeqSub(_379_d0, _380_d1);
    }
    [Xunit.Fact]
    public static void test11()
    {
      Dafny.ISequence<BigInteger> _382_d0;
      _382_d0 = Dafny.Sequence<BigInteger>.FromElements();
      BigInteger _383_r0;
      _383_r0 = Uint8__32_mUint32Seq_Compile.__default.ToNatRight(_382_d0);
    }
    [Xunit.Fact]
    public static void test12()
    {
      Dafny.ISequence<BigInteger> _384_d0;
      _384_d0 = Dafny.Sequence<BigInteger>.FromElements();
      BigInteger _385_r0;
      _385_r0 = Uint8__32_mUint32Seq_Compile.__default.ToNatLeft(_384_d0);
    }
    [Xunit.Fact]
    public static void test13()
    {
      Dafny.ISequence<BigInteger> _386_r0;
      _386_r0 = Uint8__32_mUint32Seq_Compile.__default.FromNat(new BigInteger(65));
    }
    [Xunit.Fact]
    public static void test14()
    {
      Dafny.ISequence<BigInteger> _387_r0;
      _387_r0 = Uint8__32_mUint32Seq_Compile.__default.FromNat(BigInteger.Zero);
    }
    [Xunit.Fact]
    public static void test15()
    {
      Dafny.ISequence<BigInteger> _388_d0;
      _388_d0 = Dafny.Sequence<BigInteger>.FromElements(BigInteger.Zero);
      if (!((new BigInteger((_388_d0).Count)) <= (BigInteger.One))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint8_32.dfy(177,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      Dafny.ISequence<BigInteger> _389_r0;
      _389_r0 = Uint8__32_mUint32Seq_Compile.__default.SeqExtend(_388_d0, BigInteger.One);
      if (!((new BigInteger((_389_r0).Count)) == (BigInteger.One))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint8_32.dfy(179,0): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
      if (!((Uint8__32_mUint32Seq_Compile.__default.ToNatRight(_389_r0)) == (Uint8__32_mUint32Seq_Compile.__default.ToNatRight(_388_d0)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint8_32.dfy(180,0): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
    }
    [Xunit.Fact]
    public static void test16()
    {
      Dafny.ISequence<BigInteger> _390_d0;
      _390_d0 = Dafny.Sequence<BigInteger>.FromElements(BigInteger.Zero, BigInteger.Zero);
      Dafny.ISequence<BigInteger> _391_d1;
      _391_d1 = Dafny.Sequence<BigInteger>.FromElements(BigInteger.Zero, BigInteger.Zero);
      if (!((new BigInteger((_390_d0).Count)) == (new BigInteger((_391_d1).Count)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint8_32.dfy(194,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> _392_r0;
      _392_r0 = Uint8__32_mUint32Seq_Compile.__default.SeqAdd(_390_d0, _391_d1);
    }
    [Xunit.Fact]
    public static void test17()
    {
      Dafny.ISequence<BigInteger> _393_d0;
      _393_d0 = Dafny.Sequence<BigInteger>.FromElements(new BigInteger(342), new BigInteger(4720));
      Dafny.ISequence<BigInteger> _394_d1;
      _394_d1 = Dafny.Sequence<BigInteger>.FromElements(new BigInteger(281), new BigInteger(2283));
      if (!((new BigInteger((_393_d0).Count)) == (new BigInteger((_394_d1).Count)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint8_32.dfy(204,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> _395_r0;
      _395_r0 = Uint8__32_mUint32Seq_Compile.__default.SeqAdd(_393_d0, _394_d1);
    }
    [Xunit.Fact]
    public static void test18()
    {
      Dafny.ISequence<BigInteger> _396_d0;
      _396_d0 = Dafny.Sequence<BigInteger>.FromElements();
      Dafny.ISequence<BigInteger> _397_d1;
      _397_d1 = Dafny.Sequence<BigInteger>.FromElements();
      if (!((new BigInteger((_396_d0).Count)) == (new BigInteger((_397_d1).Count)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint8_32.dfy(213,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> _398_r0;
      _398_r0 = Uint8__32_mUint32Seq_Compile.__default.SeqAdd(_396_d0, _397_d1);
    }
    [Xunit.Fact]
    public static void test19()
    {
      Dafny.ISequence<BigInteger> _399_d0;
      _399_d0 = Dafny.Sequence<BigInteger>.FromElements(new BigInteger(1325), new BigInteger(2331));
      Dafny.ISequence<BigInteger> _400_d1;
      _400_d1 = Dafny.Sequence<BigInteger>.FromElements(new BigInteger(234), new BigInteger(1796));
      if (!((new BigInteger((_399_d0).Count)) == (new BigInteger((_400_d1).Count)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint8_32.dfy(225,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> _401_r0;
      _401_r0 = Uint8__32_mUint32Seq_Compile.__default.SeqSub(_399_d0, _400_d1);
    }
    [Xunit.Fact]
    public static void test20()
    {
      Dafny.ISequence<BigInteger> _402_d0;
      _402_d0 = Dafny.Sequence<BigInteger>.FromElements(new BigInteger(920), new BigInteger(2061));
      Dafny.ISequence<BigInteger> _403_d1;
      _403_d1 = Dafny.Sequence<BigInteger>.FromElements(new BigInteger(645), new BigInteger(2062));
      if (!((new BigInteger((_402_d0).Count)) == (new BigInteger((_403_d1).Count)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint8_32.dfy(235,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> _404_r0;
      _404_r0 = Uint8__32_mUint32Seq_Compile.__default.SeqSub(_402_d0, _403_d1);
    }
    [Xunit.Fact]
    public static void test21()
    {
      Dafny.ISequence<BigInteger> _405_d0;
      _405_d0 = Dafny.Sequence<BigInteger>.FromElements();
      Dafny.ISequence<BigInteger> _406_d1;
      _406_d1 = Dafny.Sequence<BigInteger>.FromElements();
      if (!((new BigInteger((_405_d0).Count)) == (new BigInteger((_406_d1).Count)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint8_32.dfy(244,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> _407_r0;
      _407_r0 = Uint8__32_mUint32Seq_Compile.__default.SeqSub(_405_d0, _406_d1);
    }
    [Xunit.Fact]
    public static void test22()
    {
      Dafny.ISequence<BigInteger> _408_d0;
      _408_d0 = Dafny.Sequence<BigInteger>.FromElements();
      Dafny.ISequence<BigInteger> _409_r0;
      _409_r0 = Uint8__32_Compile.__default.ToSmall(_408_d0);
      if (!((new BigInteger((_409_r0).Count)) == ((new BigInteger((_408_d0).Count)) * (Uint8__32_Compile.__default.E())))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint8_32.dfy(256,0): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
    }
  }
} // end of namespace srcCollectionsSequencesUint8__32dfyUnitTests_Compile
namespace Uint8__64_mUint8Seq_Compile {

  public partial class __default {
    public static BigInteger BITS() {
      return new BigInteger(8);
    }
    public static BigInteger BASE() {
      return Power_Compile.__default.Pow(new BigInteger(2), Uint8__64_mUint8Seq_Compile.__default.BITS());
    }
    public static BigInteger ToNatRight(Dafny.ISequence<BigInteger> xs) {
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return BigInteger.Zero;
      } else {
        return ((Uint8__64_mUint8Seq_Compile.__default.ToNatRight(Seq_Compile.__default.DropFirst<BigInteger>(xs))) * (Uint8__64_mUint8Seq_Compile.__default.BASE())) + (Seq_Compile.__default.First<BigInteger>(xs));
      }
    }
    public static BigInteger ToNatLeft(Dafny.ISequence<BigInteger> xs) {
      BigInteger _410___accumulator = BigInteger.Zero;
    TAIL_CALL_START: ;
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return (BigInteger.Zero) + (_410___accumulator);
      } else {
        _410___accumulator = ((Seq_Compile.__default.Last<BigInteger>(xs)) * (Power_Compile.__default.Pow(Uint8__64_mUint8Seq_Compile.__default.BASE(), (new BigInteger((xs).Count)) - (BigInteger.One)))) + (_410___accumulator);
        Dafny.ISequence<BigInteger> _in54 = Seq_Compile.__default.DropLast<BigInteger>(xs);
        xs = _in54;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<BigInteger> FromNat(BigInteger n) {
      Dafny.ISequence<BigInteger> _411___accumulator = Dafny.Sequence<BigInteger>.FromElements();
    TAIL_CALL_START: ;
      if ((n).Sign == 0) {
        return Dafny.Sequence<BigInteger>.Concat(_411___accumulator, Dafny.Sequence<BigInteger>.FromElements());
      } else {
        _411___accumulator = Dafny.Sequence<BigInteger>.Concat(_411___accumulator, Dafny.Sequence<BigInteger>.FromElements(Dafny.Helpers.EuclideanModulus(n, Uint8__64_mUint8Seq_Compile.__default.BASE())));
        BigInteger _in55 = Dafny.Helpers.EuclideanDivision(n, Uint8__64_mUint8Seq_Compile.__default.BASE());
        n = _in55;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<BigInteger> SeqExtend(Dafny.ISequence<BigInteger> xs, BigInteger n)
    {
    TAIL_CALL_START: ;
      if ((new BigInteger((xs).Count)) >= (n)) {
        return xs;
      } else {
        Dafny.ISequence<BigInteger> _in56 = Dafny.Sequence<BigInteger>.Concat(xs, Dafny.Sequence<BigInteger>.FromElements(BigInteger.Zero));
        BigInteger _in57 = n;
        xs = _in56;
        n = _in57;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<BigInteger> SeqExtendMultiple(Dafny.ISequence<BigInteger> xs, BigInteger n)
    {
      BigInteger _412_newLen = ((new BigInteger((xs).Count)) + (n)) - (Dafny.Helpers.EuclideanModulus(new BigInteger((xs).Count), n));
      return Uint8__64_mUint8Seq_Compile.__default.SeqExtend(xs, _412_newLen);
    }
    public static Dafny.ISequence<BigInteger> FromNatWithLen(BigInteger n, BigInteger len)
    {
      return Uint8__64_mUint8Seq_Compile.__default.SeqExtend(Uint8__64_mUint8Seq_Compile.__default.FromNat(n), len);
    }
    public static Dafny.ISequence<BigInteger> SeqZero(BigInteger len) {
      Dafny.ISequence<BigInteger> _413_xs = Uint8__64_mUint8Seq_Compile.__default.FromNatWithLen(BigInteger.Zero, len);
      return _413_xs;
    }
    public static _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> SeqAdd(Dafny.ISequence<BigInteger> xs, Dafny.ISequence<BigInteger> ys)
    {
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return _System.Tuple2<Dafny.ISequence<BigInteger>, BigInteger>.create(Dafny.Sequence<BigInteger>.FromElements(), BigInteger.Zero);
      } else {
        _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> _let_tmp_rhs17 = Uint8__64_mUint8Seq_Compile.__default.SeqAdd(Seq_Compile.__default.DropLast<BigInteger>(xs), Seq_Compile.__default.DropLast<BigInteger>(ys));
        Dafny.ISequence<BigInteger> _414_zs_k = _let_tmp_rhs17.dtor__0;
        BigInteger _415_cin = _let_tmp_rhs17.dtor__1;
        BigInteger _416_sum = ((Seq_Compile.__default.Last<BigInteger>(xs)) + (Seq_Compile.__default.Last<BigInteger>(ys))) + (_415_cin);
        _System._ITuple2<BigInteger, BigInteger> _let_tmp_rhs18 = (((_416_sum) < (Uint8__64_mUint8Seq_Compile.__default.BASE())) ? (_System.Tuple2<BigInteger, BigInteger>.create(_416_sum, BigInteger.Zero)) : (_System.Tuple2<BigInteger, BigInteger>.create((_416_sum) - (Uint8__64_mUint8Seq_Compile.__default.BASE()), BigInteger.One)));
        BigInteger _417_sum__out = _let_tmp_rhs18.dtor__0;
        BigInteger _418_cout = _let_tmp_rhs18.dtor__1;
        return _System.Tuple2<Dafny.ISequence<BigInteger>, BigInteger>.create(Dafny.Sequence<BigInteger>.Concat(_414_zs_k, Dafny.Sequence<BigInteger>.FromElements(_417_sum__out)), _418_cout);
      }
    }
    public static _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> SeqSub(Dafny.ISequence<BigInteger> xs, Dafny.ISequence<BigInteger> ys)
    {
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return _System.Tuple2<Dafny.ISequence<BigInteger>, BigInteger>.create(Dafny.Sequence<BigInteger>.FromElements(), BigInteger.Zero);
      } else {
        _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> _let_tmp_rhs19 = Uint8__64_mUint8Seq_Compile.__default.SeqSub(Seq_Compile.__default.DropLast<BigInteger>(xs), Seq_Compile.__default.DropLast<BigInteger>(ys));
        Dafny.ISequence<BigInteger> _419_zs = _let_tmp_rhs19.dtor__0;
        BigInteger _420_cin = _let_tmp_rhs19.dtor__1;
        _System._ITuple2<BigInteger, BigInteger> _let_tmp_rhs20 = (((Seq_Compile.__default.Last<BigInteger>(xs)) >= ((Seq_Compile.__default.Last<BigInteger>(ys)) + (_420_cin))) ? (_System.Tuple2<BigInteger, BigInteger>.create(((Seq_Compile.__default.Last<BigInteger>(xs)) - (Seq_Compile.__default.Last<BigInteger>(ys))) - (_420_cin), BigInteger.Zero)) : (_System.Tuple2<BigInteger, BigInteger>.create((((Uint8__64_mUint8Seq_Compile.__default.BASE()) + (Seq_Compile.__default.Last<BigInteger>(xs))) - (Seq_Compile.__default.Last<BigInteger>(ys))) - (_420_cin), BigInteger.One)));
        BigInteger _421_diff__out = _let_tmp_rhs20.dtor__0;
        BigInteger _422_cout = _let_tmp_rhs20.dtor__1;
        return _System.Tuple2<Dafny.ISequence<BigInteger>, BigInteger>.create(Dafny.Sequence<BigInteger>.Concat(_419_zs, Dafny.Sequence<BigInteger>.FromElements(_421_diff__out)), _422_cout);
      }
    }
  }

  public partial class @uint {
    private static readonly Dafny.TypeDescriptor<BigInteger> _TYPE = new Dafny.TypeDescriptor<BigInteger>(BigInteger.Zero);
    public static Dafny.TypeDescriptor<BigInteger> _TypeDescriptor() {
      return _TYPE;
    }
  }
} // end of namespace Uint8__64_mUint8Seq_Compile
namespace Uint8__64_mUint64Seq_Compile {

  public partial class __default {
    public static BigInteger BITS() {
      return new BigInteger(64);
    }
    public static BigInteger BASE() {
      return Power_Compile.__default.Pow(new BigInteger(2), Uint8__64_mUint64Seq_Compile.__default.BITS());
    }
    public static BigInteger ToNatRight(Dafny.ISequence<BigInteger> xs) {
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return BigInteger.Zero;
      } else {
        return ((Uint8__64_mUint64Seq_Compile.__default.ToNatRight(Seq_Compile.__default.DropFirst<BigInteger>(xs))) * (Uint8__64_mUint64Seq_Compile.__default.BASE())) + (Seq_Compile.__default.First<BigInteger>(xs));
      }
    }
    public static BigInteger ToNatLeft(Dafny.ISequence<BigInteger> xs) {
      BigInteger _423___accumulator = BigInteger.Zero;
    TAIL_CALL_START: ;
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return (BigInteger.Zero) + (_423___accumulator);
      } else {
        _423___accumulator = ((Seq_Compile.__default.Last<BigInteger>(xs)) * (Power_Compile.__default.Pow(Uint8__64_mUint64Seq_Compile.__default.BASE(), (new BigInteger((xs).Count)) - (BigInteger.One)))) + (_423___accumulator);
        Dafny.ISequence<BigInteger> _in58 = Seq_Compile.__default.DropLast<BigInteger>(xs);
        xs = _in58;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<BigInteger> FromNat(BigInteger n) {
      Dafny.ISequence<BigInteger> _424___accumulator = Dafny.Sequence<BigInteger>.FromElements();
    TAIL_CALL_START: ;
      if ((n).Sign == 0) {
        return Dafny.Sequence<BigInteger>.Concat(_424___accumulator, Dafny.Sequence<BigInteger>.FromElements());
      } else {
        _424___accumulator = Dafny.Sequence<BigInteger>.Concat(_424___accumulator, Dafny.Sequence<BigInteger>.FromElements(Dafny.Helpers.EuclideanModulus(n, Uint8__64_mUint64Seq_Compile.__default.BASE())));
        BigInteger _in59 = Dafny.Helpers.EuclideanDivision(n, Uint8__64_mUint64Seq_Compile.__default.BASE());
        n = _in59;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<BigInteger> SeqExtend(Dafny.ISequence<BigInteger> xs, BigInteger n)
    {
    TAIL_CALL_START: ;
      if ((new BigInteger((xs).Count)) >= (n)) {
        return xs;
      } else {
        Dafny.ISequence<BigInteger> _in60 = Dafny.Sequence<BigInteger>.Concat(xs, Dafny.Sequence<BigInteger>.FromElements(BigInteger.Zero));
        BigInteger _in61 = n;
        xs = _in60;
        n = _in61;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<BigInteger> SeqExtendMultiple(Dafny.ISequence<BigInteger> xs, BigInteger n)
    {
      BigInteger _425_newLen = ((new BigInteger((xs).Count)) + (n)) - (Dafny.Helpers.EuclideanModulus(new BigInteger((xs).Count), n));
      return Uint8__64_mUint64Seq_Compile.__default.SeqExtend(xs, _425_newLen);
    }
    public static Dafny.ISequence<BigInteger> FromNatWithLen(BigInteger n, BigInteger len)
    {
      return Uint8__64_mUint64Seq_Compile.__default.SeqExtend(Uint8__64_mUint64Seq_Compile.__default.FromNat(n), len);
    }
    public static Dafny.ISequence<BigInteger> SeqZero(BigInteger len) {
      Dafny.ISequence<BigInteger> _426_xs = Uint8__64_mUint64Seq_Compile.__default.FromNatWithLen(BigInteger.Zero, len);
      return _426_xs;
    }
    public static _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> SeqAdd(Dafny.ISequence<BigInteger> xs, Dafny.ISequence<BigInteger> ys)
    {
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return _System.Tuple2<Dafny.ISequence<BigInteger>, BigInteger>.create(Dafny.Sequence<BigInteger>.FromElements(), BigInteger.Zero);
      } else {
        _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> _let_tmp_rhs21 = Uint8__64_mUint64Seq_Compile.__default.SeqAdd(Seq_Compile.__default.DropLast<BigInteger>(xs), Seq_Compile.__default.DropLast<BigInteger>(ys));
        Dafny.ISequence<BigInteger> _427_zs_k = _let_tmp_rhs21.dtor__0;
        BigInteger _428_cin = _let_tmp_rhs21.dtor__1;
        BigInteger _429_sum = ((Seq_Compile.__default.Last<BigInteger>(xs)) + (Seq_Compile.__default.Last<BigInteger>(ys))) + (_428_cin);
        _System._ITuple2<BigInteger, BigInteger> _let_tmp_rhs22 = (((_429_sum) < (Uint8__64_mUint64Seq_Compile.__default.BASE())) ? (_System.Tuple2<BigInteger, BigInteger>.create(_429_sum, BigInteger.Zero)) : (_System.Tuple2<BigInteger, BigInteger>.create((_429_sum) - (Uint8__64_mUint64Seq_Compile.__default.BASE()), BigInteger.One)));
        BigInteger _430_sum__out = _let_tmp_rhs22.dtor__0;
        BigInteger _431_cout = _let_tmp_rhs22.dtor__1;
        return _System.Tuple2<Dafny.ISequence<BigInteger>, BigInteger>.create(Dafny.Sequence<BigInteger>.Concat(_427_zs_k, Dafny.Sequence<BigInteger>.FromElements(_430_sum__out)), _431_cout);
      }
    }
    public static _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> SeqSub(Dafny.ISequence<BigInteger> xs, Dafny.ISequence<BigInteger> ys)
    {
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return _System.Tuple2<Dafny.ISequence<BigInteger>, BigInteger>.create(Dafny.Sequence<BigInteger>.FromElements(), BigInteger.Zero);
      } else {
        _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> _let_tmp_rhs23 = Uint8__64_mUint64Seq_Compile.__default.SeqSub(Seq_Compile.__default.DropLast<BigInteger>(xs), Seq_Compile.__default.DropLast<BigInteger>(ys));
        Dafny.ISequence<BigInteger> _432_zs = _let_tmp_rhs23.dtor__0;
        BigInteger _433_cin = _let_tmp_rhs23.dtor__1;
        _System._ITuple2<BigInteger, BigInteger> _let_tmp_rhs24 = (((Seq_Compile.__default.Last<BigInteger>(xs)) >= ((Seq_Compile.__default.Last<BigInteger>(ys)) + (_433_cin))) ? (_System.Tuple2<BigInteger, BigInteger>.create(((Seq_Compile.__default.Last<BigInteger>(xs)) - (Seq_Compile.__default.Last<BigInteger>(ys))) - (_433_cin), BigInteger.Zero)) : (_System.Tuple2<BigInteger, BigInteger>.create((((Uint8__64_mUint64Seq_Compile.__default.BASE()) + (Seq_Compile.__default.Last<BigInteger>(xs))) - (Seq_Compile.__default.Last<BigInteger>(ys))) - (_433_cin), BigInteger.One)));
        BigInteger _434_diff__out = _let_tmp_rhs24.dtor__0;
        BigInteger _435_cout = _let_tmp_rhs24.dtor__1;
        return _System.Tuple2<Dafny.ISequence<BigInteger>, BigInteger>.create(Dafny.Sequence<BigInteger>.Concat(_432_zs, Dafny.Sequence<BigInteger>.FromElements(_434_diff__out)), _435_cout);
      }
    }
  }

  public partial class @uint {
    private static readonly Dafny.TypeDescriptor<BigInteger> _TYPE = new Dafny.TypeDescriptor<BigInteger>(BigInteger.Zero);
    public static Dafny.TypeDescriptor<BigInteger> _TypeDescriptor() {
      return _TYPE;
    }
  }
} // end of namespace Uint8__64_mUint64Seq_Compile
namespace Uint8__64_Compile {

  public partial class __default {
    public static BigInteger E() {
      return Dafny.Helpers.EuclideanDivision(Uint8__64_mUint64Seq_Compile.__default.BITS(), Uint8__64_mUint8Seq_Compile.__default.BITS());
    }
    public static Dafny.ISequence<BigInteger> ToSmall(Dafny.ISequence<BigInteger> xs) {
      Dafny.ISequence<BigInteger> _436___accumulator = Dafny.Sequence<BigInteger>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return Dafny.Sequence<BigInteger>.Concat(_436___accumulator, Dafny.Sequence<BigInteger>.FromElements());
      } else {
        _436___accumulator = Dafny.Sequence<BigInteger>.Concat(_436___accumulator, Uint8__64_mUint8Seq_Compile.__default.FromNatWithLen(Seq_Compile.__default.First<BigInteger>(xs), Uint8__64_Compile.__default.E()));
        Dafny.ISequence<BigInteger> _in62 = Seq_Compile.__default.DropFirst<BigInteger>(xs);
        xs = _in62;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<BigInteger> ToLarge(Dafny.ISequence<BigInteger> xs) {
      Dafny.ISequence<BigInteger> _437___accumulator = Dafny.Sequence<BigInteger>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return Dafny.Sequence<BigInteger>.Concat(_437___accumulator, Dafny.Sequence<BigInteger>.FromElements());
      } else {
        _437___accumulator = Dafny.Sequence<BigInteger>.Concat(_437___accumulator, Dafny.Sequence<BigInteger>.FromElements(Uint8__64_mUint8Seq_Compile.__default.ToNatRight((xs).Take(Uint8__64_Compile.__default.E()))));
        Dafny.ISequence<BigInteger> _in63 = (xs).Drop(Uint8__64_Compile.__default.E());
        xs = _in63;
        goto TAIL_CALL_START;
      }
    }
  }
} // end of namespace Uint8__64_Compile
namespace srcCollectionsSequencesUint8__64dfyUnitTests_Compile {

  public partial class __default {
    [Xunit.Fact]
    public static void test0()
    {
      Dafny.ISequence<BigInteger> _438_d0;
      _438_d0 = Dafny.Sequence<BigInteger>.FromElements();
      BigInteger _439_r0;
      _439_r0 = Uint8__64_mUint8Seq_Compile.__default.ToNatRight(_438_d0);
    }
    [Xunit.Fact]
    public static void test1()
    {
      Dafny.ISequence<BigInteger> _440_d0;
      _440_d0 = Dafny.Sequence<BigInteger>.FromElements();
      BigInteger _441_r0;
      _441_r0 = Uint8__64_mUint8Seq_Compile.__default.ToNatLeft(_440_d0);
    }
    [Xunit.Fact]
    public static void test2()
    {
      Dafny.ISequence<BigInteger> _442_r0;
      _442_r0 = Uint8__64_mUint8Seq_Compile.__default.FromNat(new BigInteger(65));
    }
    [Xunit.Fact]
    public static void test3()
    {
      Dafny.ISequence<BigInteger> _443_r0;
      _443_r0 = Uint8__64_mUint8Seq_Compile.__default.FromNat(BigInteger.Zero);
    }
    [Xunit.Fact]
    public static void test4()
    {
      Dafny.ISequence<BigInteger> _444_d0;
      _444_d0 = Dafny.Sequence<BigInteger>.FromElements(BigInteger.Zero);
      if (!((new BigInteger((_444_d0).Count)) <= (BigInteger.One))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint8_64.dfy(69,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      Dafny.ISequence<BigInteger> _445_r0;
      _445_r0 = Uint8__64_mUint8Seq_Compile.__default.SeqExtend(_444_d0, BigInteger.One);
      if (!((new BigInteger((_445_r0).Count)) == (BigInteger.One))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint8_64.dfy(71,0): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
      if (!((Uint8__64_mUint8Seq_Compile.__default.ToNatRight(_445_r0)) == (Uint8__64_mUint8Seq_Compile.__default.ToNatRight(_444_d0)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint8_64.dfy(72,0): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
    }
    [Xunit.Fact]
    public static void test5()
    {
      Dafny.ISequence<BigInteger> _446_d0;
      _446_d0 = Dafny.Sequence<BigInteger>.FromElements(BigInteger.Zero, BigInteger.Zero);
      Dafny.ISequence<BigInteger> _447_d1;
      _447_d1 = Dafny.Sequence<BigInteger>.FromElements(BigInteger.Zero, BigInteger.Zero);
      if (!((new BigInteger((_446_d0).Count)) == (new BigInteger((_447_d1).Count)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint8_64.dfy(86,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> _448_r0;
      _448_r0 = Uint8__64_mUint8Seq_Compile.__default.SeqAdd(_446_d0, _447_d1);
    }
    [Xunit.Fact]
    public static void test6()
    {
      Dafny.ISequence<BigInteger> _449_d0;
      _449_d0 = Dafny.Sequence<BigInteger>.FromElements(new BigInteger(12), new BigInteger(2283));
      Dafny.ISequence<BigInteger> _450_d1;
      _450_d1 = Dafny.Sequence<BigInteger>.FromElements(new BigInteger(281), new BigInteger(11138));
      if (!((new BigInteger((_449_d0).Count)) == (new BigInteger((_450_d1).Count)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint8_64.dfy(96,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> _451_r0;
      _451_r0 = Uint8__64_mUint8Seq_Compile.__default.SeqAdd(_449_d0, _450_d1);
    }
    [Xunit.Fact]
    public static void test7()
    {
      Dafny.ISequence<BigInteger> _452_d0;
      _452_d0 = Dafny.Sequence<BigInteger>.FromElements();
      Dafny.ISequence<BigInteger> _453_d1;
      _453_d1 = Dafny.Sequence<BigInteger>.FromElements();
      if (!((new BigInteger((_452_d0).Count)) == (new BigInteger((_453_d1).Count)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint8_64.dfy(105,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> _454_r0;
      _454_r0 = Uint8__64_mUint8Seq_Compile.__default.SeqAdd(_452_d0, _453_d1);
    }
    [Xunit.Fact]
    public static void test8()
    {
      Dafny.ISequence<BigInteger> _455_d0;
      _455_d0 = Dafny.Sequence<BigInteger>.FromElements(new BigInteger(1325), new BigInteger(2331));
      Dafny.ISequence<BigInteger> _456_d1;
      _456_d1 = Dafny.Sequence<BigInteger>.FromElements(new BigInteger(234), new BigInteger(1796));
      if (!((new BigInteger((_455_d0).Count)) == (new BigInteger((_456_d1).Count)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint8_64.dfy(117,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> _457_r0;
      _457_r0 = Uint8__64_mUint8Seq_Compile.__default.SeqSub(_455_d0, _456_d1);
    }
    [Xunit.Fact]
    public static void test9()
    {
      Dafny.ISequence<BigInteger> _458_d0;
      _458_d0 = Dafny.Sequence<BigInteger>.FromElements(new BigInteger(920), new BigInteger(2061));
      Dafny.ISequence<BigInteger> _459_d1;
      _459_d1 = Dafny.Sequence<BigInteger>.FromElements(new BigInteger(645), new BigInteger(2062));
      if (!((new BigInteger((_458_d0).Count)) == (new BigInteger((_459_d1).Count)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint8_64.dfy(127,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> _460_r0;
      _460_r0 = Uint8__64_mUint8Seq_Compile.__default.SeqSub(_458_d0, _459_d1);
    }
    [Xunit.Fact]
    public static void test10()
    {
      Dafny.ISequence<BigInteger> _461_d0;
      _461_d0 = Dafny.Sequence<BigInteger>.FromElements();
      Dafny.ISequence<BigInteger> _462_d1;
      _462_d1 = Dafny.Sequence<BigInteger>.FromElements();
      if (!((new BigInteger((_461_d0).Count)) == (new BigInteger((_462_d1).Count)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint8_64.dfy(136,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> _463_r0;
      _463_r0 = Uint8__64_mUint8Seq_Compile.__default.SeqSub(_461_d0, _462_d1);
    }
    [Xunit.Fact]
    public static void test11()
    {
      Dafny.ISequence<BigInteger> _464_d0;
      _464_d0 = Dafny.Sequence<BigInteger>.FromElements();
      BigInteger _465_r0;
      _465_r0 = Uint8__64_mUint64Seq_Compile.__default.ToNatRight(_464_d0);
    }
    [Xunit.Fact]
    public static void test12()
    {
      Dafny.ISequence<BigInteger> _466_d0;
      _466_d0 = Dafny.Sequence<BigInteger>.FromElements();
      BigInteger _467_r0;
      _467_r0 = Uint8__64_mUint64Seq_Compile.__default.ToNatLeft(_466_d0);
    }
    [Xunit.Fact]
    public static void test13()
    {
      Dafny.ISequence<BigInteger> _468_r0;
      _468_r0 = Uint8__64_mUint64Seq_Compile.__default.FromNat(new BigInteger(65));
    }
    [Xunit.Fact]
    public static void test14()
    {
      Dafny.ISequence<BigInteger> _469_r0;
      _469_r0 = Uint8__64_mUint64Seq_Compile.__default.FromNat(BigInteger.Zero);
    }
    [Xunit.Fact]
    public static void test15()
    {
      Dafny.ISequence<BigInteger> _470_d0;
      _470_d0 = Dafny.Sequence<BigInteger>.FromElements(BigInteger.Zero);
      if (!((new BigInteger((_470_d0).Count)) <= (BigInteger.One))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint8_64.dfy(177,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      Dafny.ISequence<BigInteger> _471_r0;
      _471_r0 = Uint8__64_mUint64Seq_Compile.__default.SeqExtend(_470_d0, BigInteger.One);
      if (!((new BigInteger((_471_r0).Count)) == (BigInteger.One))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint8_64.dfy(179,0): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
      if (!((Uint8__64_mUint64Seq_Compile.__default.ToNatRight(_471_r0)) == (Uint8__64_mUint64Seq_Compile.__default.ToNatRight(_470_d0)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint8_64.dfy(180,0): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
    }
    [Xunit.Fact]
    public static void test16()
    {
      Dafny.ISequence<BigInteger> _472_d0;
      _472_d0 = Dafny.Sequence<BigInteger>.FromElements(BigInteger.Zero, BigInteger.Zero);
      Dafny.ISequence<BigInteger> _473_d1;
      _473_d1 = Dafny.Sequence<BigInteger>.FromElements(BigInteger.Zero, BigInteger.Zero);
      if (!((new BigInteger((_472_d0).Count)) == (new BigInteger((_473_d1).Count)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint8_64.dfy(194,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> _474_r0;
      _474_r0 = Uint8__64_mUint64Seq_Compile.__default.SeqAdd(_472_d0, _473_d1);
    }
    [Xunit.Fact]
    public static void test17()
    {
      Dafny.ISequence<BigInteger> _475_d0;
      _475_d0 = Dafny.Sequence<BigInteger>.FromElements(new BigInteger(342), new BigInteger(4720));
      Dafny.ISequence<BigInteger> _476_d1;
      _476_d1 = Dafny.Sequence<BigInteger>.FromElements(new BigInteger(281), new BigInteger(2283));
      if (!((new BigInteger((_475_d0).Count)) == (new BigInteger((_476_d1).Count)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint8_64.dfy(204,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> _477_r0;
      _477_r0 = Uint8__64_mUint64Seq_Compile.__default.SeqAdd(_475_d0, _476_d1);
    }
    [Xunit.Fact]
    public static void test18()
    {
      Dafny.ISequence<BigInteger> _478_d0;
      _478_d0 = Dafny.Sequence<BigInteger>.FromElements();
      Dafny.ISequence<BigInteger> _479_d1;
      _479_d1 = Dafny.Sequence<BigInteger>.FromElements();
      if (!((new BigInteger((_478_d0).Count)) == (new BigInteger((_479_d1).Count)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint8_64.dfy(213,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> _480_r0;
      _480_r0 = Uint8__64_mUint64Seq_Compile.__default.SeqAdd(_478_d0, _479_d1);
    }
    [Xunit.Fact]
    public static void test19()
    {
      Dafny.ISequence<BigInteger> _481_d0;
      _481_d0 = Dafny.Sequence<BigInteger>.FromElements(new BigInteger(1325), new BigInteger(2331));
      Dafny.ISequence<BigInteger> _482_d1;
      _482_d1 = Dafny.Sequence<BigInteger>.FromElements(new BigInteger(234), new BigInteger(1796));
      if (!((new BigInteger((_481_d0).Count)) == (new BigInteger((_482_d1).Count)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint8_64.dfy(225,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> _483_r0;
      _483_r0 = Uint8__64_mUint64Seq_Compile.__default.SeqSub(_481_d0, _482_d1);
    }
    [Xunit.Fact]
    public static void test20()
    {
      Dafny.ISequence<BigInteger> _484_d0;
      _484_d0 = Dafny.Sequence<BigInteger>.FromElements(new BigInteger(920), new BigInteger(2061));
      Dafny.ISequence<BigInteger> _485_d1;
      _485_d1 = Dafny.Sequence<BigInteger>.FromElements(new BigInteger(645), new BigInteger(2062));
      if (!((new BigInteger((_484_d0).Count)) == (new BigInteger((_485_d1).Count)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint8_64.dfy(235,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> _486_r0;
      _486_r0 = Uint8__64_mUint64Seq_Compile.__default.SeqSub(_484_d0, _485_d1);
    }
    [Xunit.Fact]
    public static void test21()
    {
      Dafny.ISequence<BigInteger> _487_d0;
      _487_d0 = Dafny.Sequence<BigInteger>.FromElements();
      Dafny.ISequence<BigInteger> _488_d1;
      _488_d1 = Dafny.Sequence<BigInteger>.FromElements();
      if (!((new BigInteger((_487_d0).Count)) == (new BigInteger((_488_d1).Count)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint8_64.dfy(244,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> _489_r0;
      _489_r0 = Uint8__64_mUint64Seq_Compile.__default.SeqSub(_487_d0, _488_d1);
    }
    [Xunit.Fact]
    public static void test22()
    {
      Dafny.ISequence<BigInteger> _490_d0;
      _490_d0 = Dafny.Sequence<BigInteger>.FromElements();
      Dafny.ISequence<BigInteger> _491_r0;
      _491_r0 = Uint8__64_Compile.__default.ToSmall(_490_d0);
      if (!((new BigInteger((_491_r0).Count)) == ((new BigInteger((_490_d0).Count)) * (Uint8__64_Compile.__default.E())))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint8_64.dfy(256,0): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
    }
  }
} // end of namespace srcCollectionsSequencesUint8__64dfyUnitTests_Compile
namespace Uint16__32_mUint16Seq_Compile {

  public partial class __default {
    public static BigInteger BITS() {
      return new BigInteger(16);
    }
    public static BigInteger BASE() {
      return Power_Compile.__default.Pow(new BigInteger(2), Uint16__32_mUint16Seq_Compile.__default.BITS());
    }
    public static BigInteger ToNatRight(Dafny.ISequence<BigInteger> xs) {
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return BigInteger.Zero;
      } else {
        return ((Uint16__32_mUint16Seq_Compile.__default.ToNatRight(Seq_Compile.__default.DropFirst<BigInteger>(xs))) * (Uint16__32_mUint16Seq_Compile.__default.BASE())) + (Seq_Compile.__default.First<BigInteger>(xs));
      }
    }
    public static BigInteger ToNatLeft(Dafny.ISequence<BigInteger> xs) {
      BigInteger _492___accumulator = BigInteger.Zero;
    TAIL_CALL_START: ;
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return (BigInteger.Zero) + (_492___accumulator);
      } else {
        _492___accumulator = ((Seq_Compile.__default.Last<BigInteger>(xs)) * (Power_Compile.__default.Pow(Uint16__32_mUint16Seq_Compile.__default.BASE(), (new BigInteger((xs).Count)) - (BigInteger.One)))) + (_492___accumulator);
        Dafny.ISequence<BigInteger> _in64 = Seq_Compile.__default.DropLast<BigInteger>(xs);
        xs = _in64;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<BigInteger> FromNat(BigInteger n) {
      Dafny.ISequence<BigInteger> _493___accumulator = Dafny.Sequence<BigInteger>.FromElements();
    TAIL_CALL_START: ;
      if ((n).Sign == 0) {
        return Dafny.Sequence<BigInteger>.Concat(_493___accumulator, Dafny.Sequence<BigInteger>.FromElements());
      } else {
        _493___accumulator = Dafny.Sequence<BigInteger>.Concat(_493___accumulator, Dafny.Sequence<BigInteger>.FromElements(Dafny.Helpers.EuclideanModulus(n, Uint16__32_mUint16Seq_Compile.__default.BASE())));
        BigInteger _in65 = Dafny.Helpers.EuclideanDivision(n, Uint16__32_mUint16Seq_Compile.__default.BASE());
        n = _in65;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<BigInteger> SeqExtend(Dafny.ISequence<BigInteger> xs, BigInteger n)
    {
    TAIL_CALL_START: ;
      if ((new BigInteger((xs).Count)) >= (n)) {
        return xs;
      } else {
        Dafny.ISequence<BigInteger> _in66 = Dafny.Sequence<BigInteger>.Concat(xs, Dafny.Sequence<BigInteger>.FromElements(BigInteger.Zero));
        BigInteger _in67 = n;
        xs = _in66;
        n = _in67;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<BigInteger> SeqExtendMultiple(Dafny.ISequence<BigInteger> xs, BigInteger n)
    {
      BigInteger _494_newLen = ((new BigInteger((xs).Count)) + (n)) - (Dafny.Helpers.EuclideanModulus(new BigInteger((xs).Count), n));
      return Uint16__32_mUint16Seq_Compile.__default.SeqExtend(xs, _494_newLen);
    }
    public static Dafny.ISequence<BigInteger> FromNatWithLen(BigInteger n, BigInteger len)
    {
      return Uint16__32_mUint16Seq_Compile.__default.SeqExtend(Uint16__32_mUint16Seq_Compile.__default.FromNat(n), len);
    }
    public static Dafny.ISequence<BigInteger> SeqZero(BigInteger len) {
      Dafny.ISequence<BigInteger> _495_xs = Uint16__32_mUint16Seq_Compile.__default.FromNatWithLen(BigInteger.Zero, len);
      return _495_xs;
    }
    public static _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> SeqAdd(Dafny.ISequence<BigInteger> xs, Dafny.ISequence<BigInteger> ys)
    {
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return _System.Tuple2<Dafny.ISequence<BigInteger>, BigInteger>.create(Dafny.Sequence<BigInteger>.FromElements(), BigInteger.Zero);
      } else {
        _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> _let_tmp_rhs25 = Uint16__32_mUint16Seq_Compile.__default.SeqAdd(Seq_Compile.__default.DropLast<BigInteger>(xs), Seq_Compile.__default.DropLast<BigInteger>(ys));
        Dafny.ISequence<BigInteger> _496_zs_k = _let_tmp_rhs25.dtor__0;
        BigInteger _497_cin = _let_tmp_rhs25.dtor__1;
        BigInteger _498_sum = ((Seq_Compile.__default.Last<BigInteger>(xs)) + (Seq_Compile.__default.Last<BigInteger>(ys))) + (_497_cin);
        _System._ITuple2<BigInteger, BigInteger> _let_tmp_rhs26 = (((_498_sum) < (Uint16__32_mUint16Seq_Compile.__default.BASE())) ? (_System.Tuple2<BigInteger, BigInteger>.create(_498_sum, BigInteger.Zero)) : (_System.Tuple2<BigInteger, BigInteger>.create((_498_sum) - (Uint16__32_mUint16Seq_Compile.__default.BASE()), BigInteger.One)));
        BigInteger _499_sum__out = _let_tmp_rhs26.dtor__0;
        BigInteger _500_cout = _let_tmp_rhs26.dtor__1;
        return _System.Tuple2<Dafny.ISequence<BigInteger>, BigInteger>.create(Dafny.Sequence<BigInteger>.Concat(_496_zs_k, Dafny.Sequence<BigInteger>.FromElements(_499_sum__out)), _500_cout);
      }
    }
    public static _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> SeqSub(Dafny.ISequence<BigInteger> xs, Dafny.ISequence<BigInteger> ys)
    {
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return _System.Tuple2<Dafny.ISequence<BigInteger>, BigInteger>.create(Dafny.Sequence<BigInteger>.FromElements(), BigInteger.Zero);
      } else {
        _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> _let_tmp_rhs27 = Uint16__32_mUint16Seq_Compile.__default.SeqSub(Seq_Compile.__default.DropLast<BigInteger>(xs), Seq_Compile.__default.DropLast<BigInteger>(ys));
        Dafny.ISequence<BigInteger> _501_zs = _let_tmp_rhs27.dtor__0;
        BigInteger _502_cin = _let_tmp_rhs27.dtor__1;
        _System._ITuple2<BigInteger, BigInteger> _let_tmp_rhs28 = (((Seq_Compile.__default.Last<BigInteger>(xs)) >= ((Seq_Compile.__default.Last<BigInteger>(ys)) + (_502_cin))) ? (_System.Tuple2<BigInteger, BigInteger>.create(((Seq_Compile.__default.Last<BigInteger>(xs)) - (Seq_Compile.__default.Last<BigInteger>(ys))) - (_502_cin), BigInteger.Zero)) : (_System.Tuple2<BigInteger, BigInteger>.create((((Uint16__32_mUint16Seq_Compile.__default.BASE()) + (Seq_Compile.__default.Last<BigInteger>(xs))) - (Seq_Compile.__default.Last<BigInteger>(ys))) - (_502_cin), BigInteger.One)));
        BigInteger _503_diff__out = _let_tmp_rhs28.dtor__0;
        BigInteger _504_cout = _let_tmp_rhs28.dtor__1;
        return _System.Tuple2<Dafny.ISequence<BigInteger>, BigInteger>.create(Dafny.Sequence<BigInteger>.Concat(_501_zs, Dafny.Sequence<BigInteger>.FromElements(_503_diff__out)), _504_cout);
      }
    }
  }

  public partial class @uint {
    private static readonly Dafny.TypeDescriptor<BigInteger> _TYPE = new Dafny.TypeDescriptor<BigInteger>(BigInteger.Zero);
    public static Dafny.TypeDescriptor<BigInteger> _TypeDescriptor() {
      return _TYPE;
    }
  }
} // end of namespace Uint16__32_mUint16Seq_Compile
namespace Uint16__32_mUint32Seq_Compile {

  public partial class __default {
    public static BigInteger BITS() {
      return new BigInteger(32);
    }
    public static BigInteger BASE() {
      return Power_Compile.__default.Pow(new BigInteger(2), Uint16__32_mUint32Seq_Compile.__default.BITS());
    }
    public static BigInteger ToNatRight(Dafny.ISequence<BigInteger> xs) {
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return BigInteger.Zero;
      } else {
        return ((Uint16__32_mUint32Seq_Compile.__default.ToNatRight(Seq_Compile.__default.DropFirst<BigInteger>(xs))) * (Uint16__32_mUint32Seq_Compile.__default.BASE())) + (Seq_Compile.__default.First<BigInteger>(xs));
      }
    }
    public static BigInteger ToNatLeft(Dafny.ISequence<BigInteger> xs) {
      BigInteger _505___accumulator = BigInteger.Zero;
    TAIL_CALL_START: ;
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return (BigInteger.Zero) + (_505___accumulator);
      } else {
        _505___accumulator = ((Seq_Compile.__default.Last<BigInteger>(xs)) * (Power_Compile.__default.Pow(Uint16__32_mUint32Seq_Compile.__default.BASE(), (new BigInteger((xs).Count)) - (BigInteger.One)))) + (_505___accumulator);
        Dafny.ISequence<BigInteger> _in68 = Seq_Compile.__default.DropLast<BigInteger>(xs);
        xs = _in68;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<BigInteger> FromNat(BigInteger n) {
      Dafny.ISequence<BigInteger> _506___accumulator = Dafny.Sequence<BigInteger>.FromElements();
    TAIL_CALL_START: ;
      if ((n).Sign == 0) {
        return Dafny.Sequence<BigInteger>.Concat(_506___accumulator, Dafny.Sequence<BigInteger>.FromElements());
      } else {
        _506___accumulator = Dafny.Sequence<BigInteger>.Concat(_506___accumulator, Dafny.Sequence<BigInteger>.FromElements(Dafny.Helpers.EuclideanModulus(n, Uint16__32_mUint32Seq_Compile.__default.BASE())));
        BigInteger _in69 = Dafny.Helpers.EuclideanDivision(n, Uint16__32_mUint32Seq_Compile.__default.BASE());
        n = _in69;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<BigInteger> SeqExtend(Dafny.ISequence<BigInteger> xs, BigInteger n)
    {
    TAIL_CALL_START: ;
      if ((new BigInteger((xs).Count)) >= (n)) {
        return xs;
      } else {
        Dafny.ISequence<BigInteger> _in70 = Dafny.Sequence<BigInteger>.Concat(xs, Dafny.Sequence<BigInteger>.FromElements(BigInteger.Zero));
        BigInteger _in71 = n;
        xs = _in70;
        n = _in71;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<BigInteger> SeqExtendMultiple(Dafny.ISequence<BigInteger> xs, BigInteger n)
    {
      BigInteger _507_newLen = ((new BigInteger((xs).Count)) + (n)) - (Dafny.Helpers.EuclideanModulus(new BigInteger((xs).Count), n));
      return Uint16__32_mUint32Seq_Compile.__default.SeqExtend(xs, _507_newLen);
    }
    public static Dafny.ISequence<BigInteger> FromNatWithLen(BigInteger n, BigInteger len)
    {
      return Uint16__32_mUint32Seq_Compile.__default.SeqExtend(Uint16__32_mUint32Seq_Compile.__default.FromNat(n), len);
    }
    public static Dafny.ISequence<BigInteger> SeqZero(BigInteger len) {
      Dafny.ISequence<BigInteger> _508_xs = Uint16__32_mUint32Seq_Compile.__default.FromNatWithLen(BigInteger.Zero, len);
      return _508_xs;
    }
    public static _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> SeqAdd(Dafny.ISequence<BigInteger> xs, Dafny.ISequence<BigInteger> ys)
    {
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return _System.Tuple2<Dafny.ISequence<BigInteger>, BigInteger>.create(Dafny.Sequence<BigInteger>.FromElements(), BigInteger.Zero);
      } else {
        _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> _let_tmp_rhs29 = Uint16__32_mUint32Seq_Compile.__default.SeqAdd(Seq_Compile.__default.DropLast<BigInteger>(xs), Seq_Compile.__default.DropLast<BigInteger>(ys));
        Dafny.ISequence<BigInteger> _509_zs_k = _let_tmp_rhs29.dtor__0;
        BigInteger _510_cin = _let_tmp_rhs29.dtor__1;
        BigInteger _511_sum = ((Seq_Compile.__default.Last<BigInteger>(xs)) + (Seq_Compile.__default.Last<BigInteger>(ys))) + (_510_cin);
        _System._ITuple2<BigInteger, BigInteger> _let_tmp_rhs30 = (((_511_sum) < (Uint16__32_mUint32Seq_Compile.__default.BASE())) ? (_System.Tuple2<BigInteger, BigInteger>.create(_511_sum, BigInteger.Zero)) : (_System.Tuple2<BigInteger, BigInteger>.create((_511_sum) - (Uint16__32_mUint32Seq_Compile.__default.BASE()), BigInteger.One)));
        BigInteger _512_sum__out = _let_tmp_rhs30.dtor__0;
        BigInteger _513_cout = _let_tmp_rhs30.dtor__1;
        return _System.Tuple2<Dafny.ISequence<BigInteger>, BigInteger>.create(Dafny.Sequence<BigInteger>.Concat(_509_zs_k, Dafny.Sequence<BigInteger>.FromElements(_512_sum__out)), _513_cout);
      }
    }
    public static _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> SeqSub(Dafny.ISequence<BigInteger> xs, Dafny.ISequence<BigInteger> ys)
    {
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return _System.Tuple2<Dafny.ISequence<BigInteger>, BigInteger>.create(Dafny.Sequence<BigInteger>.FromElements(), BigInteger.Zero);
      } else {
        _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> _let_tmp_rhs31 = Uint16__32_mUint32Seq_Compile.__default.SeqSub(Seq_Compile.__default.DropLast<BigInteger>(xs), Seq_Compile.__default.DropLast<BigInteger>(ys));
        Dafny.ISequence<BigInteger> _514_zs = _let_tmp_rhs31.dtor__0;
        BigInteger _515_cin = _let_tmp_rhs31.dtor__1;
        _System._ITuple2<BigInteger, BigInteger> _let_tmp_rhs32 = (((Seq_Compile.__default.Last<BigInteger>(xs)) >= ((Seq_Compile.__default.Last<BigInteger>(ys)) + (_515_cin))) ? (_System.Tuple2<BigInteger, BigInteger>.create(((Seq_Compile.__default.Last<BigInteger>(xs)) - (Seq_Compile.__default.Last<BigInteger>(ys))) - (_515_cin), BigInteger.Zero)) : (_System.Tuple2<BigInteger, BigInteger>.create((((Uint16__32_mUint32Seq_Compile.__default.BASE()) + (Seq_Compile.__default.Last<BigInteger>(xs))) - (Seq_Compile.__default.Last<BigInteger>(ys))) - (_515_cin), BigInteger.One)));
        BigInteger _516_diff__out = _let_tmp_rhs32.dtor__0;
        BigInteger _517_cout = _let_tmp_rhs32.dtor__1;
        return _System.Tuple2<Dafny.ISequence<BigInteger>, BigInteger>.create(Dafny.Sequence<BigInteger>.Concat(_514_zs, Dafny.Sequence<BigInteger>.FromElements(_516_diff__out)), _517_cout);
      }
    }
  }

  public partial class @uint {
    private static readonly Dafny.TypeDescriptor<BigInteger> _TYPE = new Dafny.TypeDescriptor<BigInteger>(BigInteger.Zero);
    public static Dafny.TypeDescriptor<BigInteger> _TypeDescriptor() {
      return _TYPE;
    }
  }
} // end of namespace Uint16__32_mUint32Seq_Compile
namespace Uint16__32_Compile {

  public partial class __default {
    public static BigInteger E() {
      return Dafny.Helpers.EuclideanDivision(Uint16__32_mUint32Seq_Compile.__default.BITS(), Uint16__32_mUint16Seq_Compile.__default.BITS());
    }
    public static Dafny.ISequence<BigInteger> ToSmall(Dafny.ISequence<BigInteger> xs) {
      Dafny.ISequence<BigInteger> _518___accumulator = Dafny.Sequence<BigInteger>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return Dafny.Sequence<BigInteger>.Concat(_518___accumulator, Dafny.Sequence<BigInteger>.FromElements());
      } else {
        _518___accumulator = Dafny.Sequence<BigInteger>.Concat(_518___accumulator, Uint16__32_mUint16Seq_Compile.__default.FromNatWithLen(Seq_Compile.__default.First<BigInteger>(xs), Uint16__32_Compile.__default.E()));
        Dafny.ISequence<BigInteger> _in72 = Seq_Compile.__default.DropFirst<BigInteger>(xs);
        xs = _in72;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<BigInteger> ToLarge(Dafny.ISequence<BigInteger> xs) {
      Dafny.ISequence<BigInteger> _519___accumulator = Dafny.Sequence<BigInteger>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return Dafny.Sequence<BigInteger>.Concat(_519___accumulator, Dafny.Sequence<BigInteger>.FromElements());
      } else {
        _519___accumulator = Dafny.Sequence<BigInteger>.Concat(_519___accumulator, Dafny.Sequence<BigInteger>.FromElements(Uint16__32_mUint16Seq_Compile.__default.ToNatRight((xs).Take(Uint16__32_Compile.__default.E()))));
        Dafny.ISequence<BigInteger> _in73 = (xs).Drop(Uint16__32_Compile.__default.E());
        xs = _in73;
        goto TAIL_CALL_START;
      }
    }
  }
} // end of namespace Uint16__32_Compile
namespace srcCollectionsSequencesUint16__32dfyUnitTests_Compile {

  public partial class __default {
    [Xunit.Fact]
    public static void test0()
    {
      Dafny.ISequence<BigInteger> _520_d0;
      _520_d0 = Dafny.Sequence<BigInteger>.FromElements();
      BigInteger _521_r0;
      _521_r0 = Uint16__32_mUint16Seq_Compile.__default.ToNatRight(_520_d0);
    }
    [Xunit.Fact]
    public static void test1()
    {
      Dafny.ISequence<BigInteger> _522_d0;
      _522_d0 = Dafny.Sequence<BigInteger>.FromElements();
      BigInteger _523_r0;
      _523_r0 = Uint16__32_mUint16Seq_Compile.__default.ToNatLeft(_522_d0);
    }
    [Xunit.Fact]
    public static void test2()
    {
      Dafny.ISequence<BigInteger> _524_r0;
      _524_r0 = Uint16__32_mUint16Seq_Compile.__default.FromNat(new BigInteger(65));
    }
    [Xunit.Fact]
    public static void test3()
    {
      Dafny.ISequence<BigInteger> _525_r0;
      _525_r0 = Uint16__32_mUint16Seq_Compile.__default.FromNat(BigInteger.Zero);
    }
    [Xunit.Fact]
    public static void test4()
    {
      Dafny.ISequence<BigInteger> _526_d0;
      _526_d0 = Dafny.Sequence<BigInteger>.FromElements(BigInteger.Zero);
      if (!((new BigInteger((_526_d0).Count)) <= (BigInteger.One))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint16_32.dfy(69,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      Dafny.ISequence<BigInteger> _527_r0;
      _527_r0 = Uint16__32_mUint16Seq_Compile.__default.SeqExtend(_526_d0, BigInteger.One);
      if (!((new BigInteger((_527_r0).Count)) == (BigInteger.One))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint16_32.dfy(71,0): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
      if (!((Uint16__32_mUint16Seq_Compile.__default.ToNatRight(_527_r0)) == (Uint16__32_mUint16Seq_Compile.__default.ToNatRight(_526_d0)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint16_32.dfy(72,0): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
    }
    [Xunit.Fact]
    public static void test5()
    {
      Dafny.ISequence<BigInteger> _528_d0;
      _528_d0 = Dafny.Sequence<BigInteger>.FromElements(BigInteger.Zero, BigInteger.Zero);
      Dafny.ISequence<BigInteger> _529_d1;
      _529_d1 = Dafny.Sequence<BigInteger>.FromElements(BigInteger.Zero, BigInteger.Zero);
      if (!((new BigInteger((_528_d0).Count)) == (new BigInteger((_529_d1).Count)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint16_32.dfy(86,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> _530_r0;
      _530_r0 = Uint16__32_mUint16Seq_Compile.__default.SeqAdd(_528_d0, _529_d1);
    }
    [Xunit.Fact]
    public static void test6()
    {
      Dafny.ISequence<BigInteger> _531_d0;
      _531_d0 = Dafny.Sequence<BigInteger>.FromElements(new BigInteger(12), new BigInteger(2283));
      Dafny.ISequence<BigInteger> _532_d1;
      _532_d1 = Dafny.Sequence<BigInteger>.FromElements(new BigInteger(281), new BigInteger(11138));
      if (!((new BigInteger((_531_d0).Count)) == (new BigInteger((_532_d1).Count)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint16_32.dfy(96,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> _533_r0;
      _533_r0 = Uint16__32_mUint16Seq_Compile.__default.SeqAdd(_531_d0, _532_d1);
    }
    [Xunit.Fact]
    public static void test7()
    {
      Dafny.ISequence<BigInteger> _534_d0;
      _534_d0 = Dafny.Sequence<BigInteger>.FromElements();
      Dafny.ISequence<BigInteger> _535_d1;
      _535_d1 = Dafny.Sequence<BigInteger>.FromElements();
      if (!((new BigInteger((_534_d0).Count)) == (new BigInteger((_535_d1).Count)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint16_32.dfy(105,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> _536_r0;
      _536_r0 = Uint16__32_mUint16Seq_Compile.__default.SeqAdd(_534_d0, _535_d1);
    }
    [Xunit.Fact]
    public static void test8()
    {
      Dafny.ISequence<BigInteger> _537_d0;
      _537_d0 = Dafny.Sequence<BigInteger>.FromElements(new BigInteger(1325), new BigInteger(2331));
      Dafny.ISequence<BigInteger> _538_d1;
      _538_d1 = Dafny.Sequence<BigInteger>.FromElements(new BigInteger(234), new BigInteger(1796));
      if (!((new BigInteger((_537_d0).Count)) == (new BigInteger((_538_d1).Count)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint16_32.dfy(117,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> _539_r0;
      _539_r0 = Uint16__32_mUint16Seq_Compile.__default.SeqSub(_537_d0, _538_d1);
    }
    [Xunit.Fact]
    public static void test9()
    {
      Dafny.ISequence<BigInteger> _540_d0;
      _540_d0 = Dafny.Sequence<BigInteger>.FromElements(new BigInteger(920), new BigInteger(2061));
      Dafny.ISequence<BigInteger> _541_d1;
      _541_d1 = Dafny.Sequence<BigInteger>.FromElements(new BigInteger(645), new BigInteger(2062));
      if (!((new BigInteger((_540_d0).Count)) == (new BigInteger((_541_d1).Count)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint16_32.dfy(127,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> _542_r0;
      _542_r0 = Uint16__32_mUint16Seq_Compile.__default.SeqSub(_540_d0, _541_d1);
    }
    [Xunit.Fact]
    public static void test10()
    {
      Dafny.ISequence<BigInteger> _543_d0;
      _543_d0 = Dafny.Sequence<BigInteger>.FromElements();
      Dafny.ISequence<BigInteger> _544_d1;
      _544_d1 = Dafny.Sequence<BigInteger>.FromElements();
      if (!((new BigInteger((_543_d0).Count)) == (new BigInteger((_544_d1).Count)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint16_32.dfy(136,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> _545_r0;
      _545_r0 = Uint16__32_mUint16Seq_Compile.__default.SeqSub(_543_d0, _544_d1);
    }
    [Xunit.Fact]
    public static void test11()
    {
      Dafny.ISequence<BigInteger> _546_d0;
      _546_d0 = Dafny.Sequence<BigInteger>.FromElements();
      BigInteger _547_r0;
      _547_r0 = Uint16__32_mUint32Seq_Compile.__default.ToNatRight(_546_d0);
    }
    [Xunit.Fact]
    public static void test12()
    {
      Dafny.ISequence<BigInteger> _548_d0;
      _548_d0 = Dafny.Sequence<BigInteger>.FromElements();
      BigInteger _549_r0;
      _549_r0 = Uint16__32_mUint32Seq_Compile.__default.ToNatLeft(_548_d0);
    }
    [Xunit.Fact]
    public static void test13()
    {
      Dafny.ISequence<BigInteger> _550_r0;
      _550_r0 = Uint16__32_mUint32Seq_Compile.__default.FromNat(new BigInteger(65));
    }
    [Xunit.Fact]
    public static void test14()
    {
      Dafny.ISequence<BigInteger> _551_r0;
      _551_r0 = Uint16__32_mUint32Seq_Compile.__default.FromNat(BigInteger.Zero);
    }
    [Xunit.Fact]
    public static void test15()
    {
      Dafny.ISequence<BigInteger> _552_d0;
      _552_d0 = Dafny.Sequence<BigInteger>.FromElements(BigInteger.Zero);
      if (!((new BigInteger((_552_d0).Count)) <= (BigInteger.One))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint16_32.dfy(177,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      Dafny.ISequence<BigInteger> _553_r0;
      _553_r0 = Uint16__32_mUint32Seq_Compile.__default.SeqExtend(_552_d0, BigInteger.One);
      if (!((new BigInteger((_553_r0).Count)) == (BigInteger.One))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint16_32.dfy(179,0): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
      if (!((Uint16__32_mUint32Seq_Compile.__default.ToNatRight(_553_r0)) == (Uint16__32_mUint32Seq_Compile.__default.ToNatRight(_552_d0)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint16_32.dfy(180,0): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
    }
    [Xunit.Fact]
    public static void test16()
    {
      Dafny.ISequence<BigInteger> _554_d0;
      _554_d0 = Dafny.Sequence<BigInteger>.FromElements(BigInteger.Zero, BigInteger.Zero);
      Dafny.ISequence<BigInteger> _555_d1;
      _555_d1 = Dafny.Sequence<BigInteger>.FromElements(BigInteger.Zero, BigInteger.Zero);
      if (!((new BigInteger((_554_d0).Count)) == (new BigInteger((_555_d1).Count)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint16_32.dfy(194,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> _556_r0;
      _556_r0 = Uint16__32_mUint32Seq_Compile.__default.SeqAdd(_554_d0, _555_d1);
    }
    [Xunit.Fact]
    public static void test17()
    {
      Dafny.ISequence<BigInteger> _557_d0;
      _557_d0 = Dafny.Sequence<BigInteger>.FromElements(new BigInteger(342), new BigInteger(4720));
      Dafny.ISequence<BigInteger> _558_d1;
      _558_d1 = Dafny.Sequence<BigInteger>.FromElements(new BigInteger(281), new BigInteger(2283));
      if (!((new BigInteger((_557_d0).Count)) == (new BigInteger((_558_d1).Count)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint16_32.dfy(204,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> _559_r0;
      _559_r0 = Uint16__32_mUint32Seq_Compile.__default.SeqAdd(_557_d0, _558_d1);
    }
    [Xunit.Fact]
    public static void test18()
    {
      Dafny.ISequence<BigInteger> _560_d0;
      _560_d0 = Dafny.Sequence<BigInteger>.FromElements();
      Dafny.ISequence<BigInteger> _561_d1;
      _561_d1 = Dafny.Sequence<BigInteger>.FromElements();
      if (!((new BigInteger((_560_d0).Count)) == (new BigInteger((_561_d1).Count)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint16_32.dfy(213,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> _562_r0;
      _562_r0 = Uint16__32_mUint32Seq_Compile.__default.SeqAdd(_560_d0, _561_d1);
    }
    [Xunit.Fact]
    public static void test19()
    {
      Dafny.ISequence<BigInteger> _563_d0;
      _563_d0 = Dafny.Sequence<BigInteger>.FromElements(new BigInteger(1325), new BigInteger(2331));
      Dafny.ISequence<BigInteger> _564_d1;
      _564_d1 = Dafny.Sequence<BigInteger>.FromElements(new BigInteger(234), new BigInteger(1796));
      if (!((new BigInteger((_563_d0).Count)) == (new BigInteger((_564_d1).Count)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint16_32.dfy(225,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> _565_r0;
      _565_r0 = Uint16__32_mUint32Seq_Compile.__default.SeqSub(_563_d0, _564_d1);
    }
    [Xunit.Fact]
    public static void test20()
    {
      Dafny.ISequence<BigInteger> _566_d0;
      _566_d0 = Dafny.Sequence<BigInteger>.FromElements(new BigInteger(920), new BigInteger(2061));
      Dafny.ISequence<BigInteger> _567_d1;
      _567_d1 = Dafny.Sequence<BigInteger>.FromElements(new BigInteger(645), new BigInteger(2062));
      if (!((new BigInteger((_566_d0).Count)) == (new BigInteger((_567_d1).Count)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint16_32.dfy(235,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> _568_r0;
      _568_r0 = Uint16__32_mUint32Seq_Compile.__default.SeqSub(_566_d0, _567_d1);
    }
    [Xunit.Fact]
    public static void test21()
    {
      Dafny.ISequence<BigInteger> _569_d0;
      _569_d0 = Dafny.Sequence<BigInteger>.FromElements();
      Dafny.ISequence<BigInteger> _570_d1;
      _570_d1 = Dafny.Sequence<BigInteger>.FromElements();
      if (!((new BigInteger((_569_d0).Count)) == (new BigInteger((_570_d1).Count)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint16_32.dfy(244,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> _571_r0;
      _571_r0 = Uint16__32_mUint32Seq_Compile.__default.SeqSub(_569_d0, _570_d1);
    }
    [Xunit.Fact]
    public static void test22()
    {
      Dafny.ISequence<BigInteger> _572_d0;
      _572_d0 = Dafny.Sequence<BigInteger>.FromElements();
      Dafny.ISequence<BigInteger> _573_r0;
      _573_r0 = Uint16__32_Compile.__default.ToSmall(_572_d0);
      if (!((new BigInteger((_573_r0).Count)) == ((new BigInteger((_572_d0).Count)) * (Uint16__32_Compile.__default.E())))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint16_32.dfy(256,0): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
    }
    [Xunit.Fact]
    public static void test23()
    {
      Dafny.ISequence<BigInteger> _574_d0;
      _574_d0 = Dafny.Sequence<BigInteger>.FromElements(BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero);
      if (!((Dafny.Helpers.EuclideanModulus(new BigInteger((_574_d0).Count), Uint16__32_Compile.__default.E())).Sign == 0)) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint16_32.dfy(265,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      Dafny.ISequence<BigInteger> _575_r0;
      _575_r0 = Uint16__32_Compile.__default.ToLarge(_574_d0);
      if (!((new BigInteger((_575_r0).Count)) == (Dafny.Helpers.EuclideanDivision(new BigInteger((_574_d0).Count), Uint16__32_Compile.__default.E())))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint16_32.dfy(267,0): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
    }
  }
} // end of namespace srcCollectionsSequencesUint16__32dfyUnitTests_Compile
namespace Uint32__64_mUint32Seq_Compile {

  public partial class __default {
    public static BigInteger BITS() {
      return new BigInteger(32);
    }
    public static BigInteger BASE() {
      return Power_Compile.__default.Pow(new BigInteger(2), Uint32__64_mUint32Seq_Compile.__default.BITS());
    }
    public static BigInteger ToNatRight(Dafny.ISequence<BigInteger> xs) {
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return BigInteger.Zero;
      } else {
        return ((Uint32__64_mUint32Seq_Compile.__default.ToNatRight(Seq_Compile.__default.DropFirst<BigInteger>(xs))) * (Uint32__64_mUint32Seq_Compile.__default.BASE())) + (Seq_Compile.__default.First<BigInteger>(xs));
      }
    }
    public static BigInteger ToNatLeft(Dafny.ISequence<BigInteger> xs) {
      BigInteger _576___accumulator = BigInteger.Zero;
    TAIL_CALL_START: ;
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return (BigInteger.Zero) + (_576___accumulator);
      } else {
        _576___accumulator = ((Seq_Compile.__default.Last<BigInteger>(xs)) * (Power_Compile.__default.Pow(Uint32__64_mUint32Seq_Compile.__default.BASE(), (new BigInteger((xs).Count)) - (BigInteger.One)))) + (_576___accumulator);
        Dafny.ISequence<BigInteger> _in74 = Seq_Compile.__default.DropLast<BigInteger>(xs);
        xs = _in74;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<BigInteger> FromNat(BigInteger n) {
      Dafny.ISequence<BigInteger> _577___accumulator = Dafny.Sequence<BigInteger>.FromElements();
    TAIL_CALL_START: ;
      if ((n).Sign == 0) {
        return Dafny.Sequence<BigInteger>.Concat(_577___accumulator, Dafny.Sequence<BigInteger>.FromElements());
      } else {
        _577___accumulator = Dafny.Sequence<BigInteger>.Concat(_577___accumulator, Dafny.Sequence<BigInteger>.FromElements(Dafny.Helpers.EuclideanModulus(n, Uint32__64_mUint32Seq_Compile.__default.BASE())));
        BigInteger _in75 = Dafny.Helpers.EuclideanDivision(n, Uint32__64_mUint32Seq_Compile.__default.BASE());
        n = _in75;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<BigInteger> SeqExtend(Dafny.ISequence<BigInteger> xs, BigInteger n)
    {
    TAIL_CALL_START: ;
      if ((new BigInteger((xs).Count)) >= (n)) {
        return xs;
      } else {
        Dafny.ISequence<BigInteger> _in76 = Dafny.Sequence<BigInteger>.Concat(xs, Dafny.Sequence<BigInteger>.FromElements(BigInteger.Zero));
        BigInteger _in77 = n;
        xs = _in76;
        n = _in77;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<BigInteger> SeqExtendMultiple(Dafny.ISequence<BigInteger> xs, BigInteger n)
    {
      BigInteger _578_newLen = ((new BigInteger((xs).Count)) + (n)) - (Dafny.Helpers.EuclideanModulus(new BigInteger((xs).Count), n));
      return Uint32__64_mUint32Seq_Compile.__default.SeqExtend(xs, _578_newLen);
    }
    public static Dafny.ISequence<BigInteger> FromNatWithLen(BigInteger n, BigInteger len)
    {
      return Uint32__64_mUint32Seq_Compile.__default.SeqExtend(Uint32__64_mUint32Seq_Compile.__default.FromNat(n), len);
    }
    public static Dafny.ISequence<BigInteger> SeqZero(BigInteger len) {
      Dafny.ISequence<BigInteger> _579_xs = Uint32__64_mUint32Seq_Compile.__default.FromNatWithLen(BigInteger.Zero, len);
      return _579_xs;
    }
    public static _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> SeqAdd(Dafny.ISequence<BigInteger> xs, Dafny.ISequence<BigInteger> ys)
    {
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return _System.Tuple2<Dafny.ISequence<BigInteger>, BigInteger>.create(Dafny.Sequence<BigInteger>.FromElements(), BigInteger.Zero);
      } else {
        _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> _let_tmp_rhs33 = Uint32__64_mUint32Seq_Compile.__default.SeqAdd(Seq_Compile.__default.DropLast<BigInteger>(xs), Seq_Compile.__default.DropLast<BigInteger>(ys));
        Dafny.ISequence<BigInteger> _580_zs_k = _let_tmp_rhs33.dtor__0;
        BigInteger _581_cin = _let_tmp_rhs33.dtor__1;
        BigInteger _582_sum = ((Seq_Compile.__default.Last<BigInteger>(xs)) + (Seq_Compile.__default.Last<BigInteger>(ys))) + (_581_cin);
        _System._ITuple2<BigInteger, BigInteger> _let_tmp_rhs34 = (((_582_sum) < (Uint32__64_mUint32Seq_Compile.__default.BASE())) ? (_System.Tuple2<BigInteger, BigInteger>.create(_582_sum, BigInteger.Zero)) : (_System.Tuple2<BigInteger, BigInteger>.create((_582_sum) - (Uint32__64_mUint32Seq_Compile.__default.BASE()), BigInteger.One)));
        BigInteger _583_sum__out = _let_tmp_rhs34.dtor__0;
        BigInteger _584_cout = _let_tmp_rhs34.dtor__1;
        return _System.Tuple2<Dafny.ISequence<BigInteger>, BigInteger>.create(Dafny.Sequence<BigInteger>.Concat(_580_zs_k, Dafny.Sequence<BigInteger>.FromElements(_583_sum__out)), _584_cout);
      }
    }
    public static _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> SeqSub(Dafny.ISequence<BigInteger> xs, Dafny.ISequence<BigInteger> ys)
    {
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return _System.Tuple2<Dafny.ISequence<BigInteger>, BigInteger>.create(Dafny.Sequence<BigInteger>.FromElements(), BigInteger.Zero);
      } else {
        _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> _let_tmp_rhs35 = Uint32__64_mUint32Seq_Compile.__default.SeqSub(Seq_Compile.__default.DropLast<BigInteger>(xs), Seq_Compile.__default.DropLast<BigInteger>(ys));
        Dafny.ISequence<BigInteger> _585_zs = _let_tmp_rhs35.dtor__0;
        BigInteger _586_cin = _let_tmp_rhs35.dtor__1;
        _System._ITuple2<BigInteger, BigInteger> _let_tmp_rhs36 = (((Seq_Compile.__default.Last<BigInteger>(xs)) >= ((Seq_Compile.__default.Last<BigInteger>(ys)) + (_586_cin))) ? (_System.Tuple2<BigInteger, BigInteger>.create(((Seq_Compile.__default.Last<BigInteger>(xs)) - (Seq_Compile.__default.Last<BigInteger>(ys))) - (_586_cin), BigInteger.Zero)) : (_System.Tuple2<BigInteger, BigInteger>.create((((Uint32__64_mUint32Seq_Compile.__default.BASE()) + (Seq_Compile.__default.Last<BigInteger>(xs))) - (Seq_Compile.__default.Last<BigInteger>(ys))) - (_586_cin), BigInteger.One)));
        BigInteger _587_diff__out = _let_tmp_rhs36.dtor__0;
        BigInteger _588_cout = _let_tmp_rhs36.dtor__1;
        return _System.Tuple2<Dafny.ISequence<BigInteger>, BigInteger>.create(Dafny.Sequence<BigInteger>.Concat(_585_zs, Dafny.Sequence<BigInteger>.FromElements(_587_diff__out)), _588_cout);
      }
    }
  }

  public partial class @uint {
    private static readonly Dafny.TypeDescriptor<BigInteger> _TYPE = new Dafny.TypeDescriptor<BigInteger>(BigInteger.Zero);
    public static Dafny.TypeDescriptor<BigInteger> _TypeDescriptor() {
      return _TYPE;
    }
  }
} // end of namespace Uint32__64_mUint32Seq_Compile
namespace Uint32__64_mUint64Seq_Compile {

  public partial class __default {
    public static BigInteger BITS() {
      return new BigInteger(64);
    }
    public static BigInteger BASE() {
      return Power_Compile.__default.Pow(new BigInteger(2), Uint32__64_mUint64Seq_Compile.__default.BITS());
    }
    public static BigInteger ToNatRight(Dafny.ISequence<BigInteger> xs) {
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return BigInteger.Zero;
      } else {
        return ((Uint32__64_mUint64Seq_Compile.__default.ToNatRight(Seq_Compile.__default.DropFirst<BigInteger>(xs))) * (Uint32__64_mUint64Seq_Compile.__default.BASE())) + (Seq_Compile.__default.First<BigInteger>(xs));
      }
    }
    public static BigInteger ToNatLeft(Dafny.ISequence<BigInteger> xs) {
      BigInteger _589___accumulator = BigInteger.Zero;
    TAIL_CALL_START: ;
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return (BigInteger.Zero) + (_589___accumulator);
      } else {
        _589___accumulator = ((Seq_Compile.__default.Last<BigInteger>(xs)) * (Power_Compile.__default.Pow(Uint32__64_mUint64Seq_Compile.__default.BASE(), (new BigInteger((xs).Count)) - (BigInteger.One)))) + (_589___accumulator);
        Dafny.ISequence<BigInteger> _in78 = Seq_Compile.__default.DropLast<BigInteger>(xs);
        xs = _in78;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<BigInteger> FromNat(BigInteger n) {
      Dafny.ISequence<BigInteger> _590___accumulator = Dafny.Sequence<BigInteger>.FromElements();
    TAIL_CALL_START: ;
      if ((n).Sign == 0) {
        return Dafny.Sequence<BigInteger>.Concat(_590___accumulator, Dafny.Sequence<BigInteger>.FromElements());
      } else {
        _590___accumulator = Dafny.Sequence<BigInteger>.Concat(_590___accumulator, Dafny.Sequence<BigInteger>.FromElements(Dafny.Helpers.EuclideanModulus(n, Uint32__64_mUint64Seq_Compile.__default.BASE())));
        BigInteger _in79 = Dafny.Helpers.EuclideanDivision(n, Uint32__64_mUint64Seq_Compile.__default.BASE());
        n = _in79;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<BigInteger> SeqExtend(Dafny.ISequence<BigInteger> xs, BigInteger n)
    {
    TAIL_CALL_START: ;
      if ((new BigInteger((xs).Count)) >= (n)) {
        return xs;
      } else {
        Dafny.ISequence<BigInteger> _in80 = Dafny.Sequence<BigInteger>.Concat(xs, Dafny.Sequence<BigInteger>.FromElements(BigInteger.Zero));
        BigInteger _in81 = n;
        xs = _in80;
        n = _in81;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<BigInteger> SeqExtendMultiple(Dafny.ISequence<BigInteger> xs, BigInteger n)
    {
      BigInteger _591_newLen = ((new BigInteger((xs).Count)) + (n)) - (Dafny.Helpers.EuclideanModulus(new BigInteger((xs).Count), n));
      return Uint32__64_mUint64Seq_Compile.__default.SeqExtend(xs, _591_newLen);
    }
    public static Dafny.ISequence<BigInteger> FromNatWithLen(BigInteger n, BigInteger len)
    {
      return Uint32__64_mUint64Seq_Compile.__default.SeqExtend(Uint32__64_mUint64Seq_Compile.__default.FromNat(n), len);
    }
    public static Dafny.ISequence<BigInteger> SeqZero(BigInteger len) {
      Dafny.ISequence<BigInteger> _592_xs = Uint32__64_mUint64Seq_Compile.__default.FromNatWithLen(BigInteger.Zero, len);
      return _592_xs;
    }
    public static _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> SeqAdd(Dafny.ISequence<BigInteger> xs, Dafny.ISequence<BigInteger> ys)
    {
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return _System.Tuple2<Dafny.ISequence<BigInteger>, BigInteger>.create(Dafny.Sequence<BigInteger>.FromElements(), BigInteger.Zero);
      } else {
        _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> _let_tmp_rhs37 = Uint32__64_mUint64Seq_Compile.__default.SeqAdd(Seq_Compile.__default.DropLast<BigInteger>(xs), Seq_Compile.__default.DropLast<BigInteger>(ys));
        Dafny.ISequence<BigInteger> _593_zs_k = _let_tmp_rhs37.dtor__0;
        BigInteger _594_cin = _let_tmp_rhs37.dtor__1;
        BigInteger _595_sum = ((Seq_Compile.__default.Last<BigInteger>(xs)) + (Seq_Compile.__default.Last<BigInteger>(ys))) + (_594_cin);
        _System._ITuple2<BigInteger, BigInteger> _let_tmp_rhs38 = (((_595_sum) < (Uint32__64_mUint64Seq_Compile.__default.BASE())) ? (_System.Tuple2<BigInteger, BigInteger>.create(_595_sum, BigInteger.Zero)) : (_System.Tuple2<BigInteger, BigInteger>.create((_595_sum) - (Uint32__64_mUint64Seq_Compile.__default.BASE()), BigInteger.One)));
        BigInteger _596_sum__out = _let_tmp_rhs38.dtor__0;
        BigInteger _597_cout = _let_tmp_rhs38.dtor__1;
        return _System.Tuple2<Dafny.ISequence<BigInteger>, BigInteger>.create(Dafny.Sequence<BigInteger>.Concat(_593_zs_k, Dafny.Sequence<BigInteger>.FromElements(_596_sum__out)), _597_cout);
      }
    }
    public static _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> SeqSub(Dafny.ISequence<BigInteger> xs, Dafny.ISequence<BigInteger> ys)
    {
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return _System.Tuple2<Dafny.ISequence<BigInteger>, BigInteger>.create(Dafny.Sequence<BigInteger>.FromElements(), BigInteger.Zero);
      } else {
        _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> _let_tmp_rhs39 = Uint32__64_mUint64Seq_Compile.__default.SeqSub(Seq_Compile.__default.DropLast<BigInteger>(xs), Seq_Compile.__default.DropLast<BigInteger>(ys));
        Dafny.ISequence<BigInteger> _598_zs = _let_tmp_rhs39.dtor__0;
        BigInteger _599_cin = _let_tmp_rhs39.dtor__1;
        _System._ITuple2<BigInteger, BigInteger> _let_tmp_rhs40 = (((Seq_Compile.__default.Last<BigInteger>(xs)) >= ((Seq_Compile.__default.Last<BigInteger>(ys)) + (_599_cin))) ? (_System.Tuple2<BigInteger, BigInteger>.create(((Seq_Compile.__default.Last<BigInteger>(xs)) - (Seq_Compile.__default.Last<BigInteger>(ys))) - (_599_cin), BigInteger.Zero)) : (_System.Tuple2<BigInteger, BigInteger>.create((((Uint32__64_mUint64Seq_Compile.__default.BASE()) + (Seq_Compile.__default.Last<BigInteger>(xs))) - (Seq_Compile.__default.Last<BigInteger>(ys))) - (_599_cin), BigInteger.One)));
        BigInteger _600_diff__out = _let_tmp_rhs40.dtor__0;
        BigInteger _601_cout = _let_tmp_rhs40.dtor__1;
        return _System.Tuple2<Dafny.ISequence<BigInteger>, BigInteger>.create(Dafny.Sequence<BigInteger>.Concat(_598_zs, Dafny.Sequence<BigInteger>.FromElements(_600_diff__out)), _601_cout);
      }
    }
  }

  public partial class @uint {
    private static readonly Dafny.TypeDescriptor<BigInteger> _TYPE = new Dafny.TypeDescriptor<BigInteger>(BigInteger.Zero);
    public static Dafny.TypeDescriptor<BigInteger> _TypeDescriptor() {
      return _TYPE;
    }
  }
} // end of namespace Uint32__64_mUint64Seq_Compile
namespace Uint32__64_Compile {

  public partial class __default {
    public static BigInteger E() {
      return Dafny.Helpers.EuclideanDivision(Uint32__64_mUint64Seq_Compile.__default.BITS(), Uint32__64_mUint32Seq_Compile.__default.BITS());
    }
    public static Dafny.ISequence<BigInteger> ToSmall(Dafny.ISequence<BigInteger> xs) {
      Dafny.ISequence<BigInteger> _602___accumulator = Dafny.Sequence<BigInteger>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return Dafny.Sequence<BigInteger>.Concat(_602___accumulator, Dafny.Sequence<BigInteger>.FromElements());
      } else {
        _602___accumulator = Dafny.Sequence<BigInteger>.Concat(_602___accumulator, Uint32__64_mUint32Seq_Compile.__default.FromNatWithLen(Seq_Compile.__default.First<BigInteger>(xs), Uint32__64_Compile.__default.E()));
        Dafny.ISequence<BigInteger> _in82 = Seq_Compile.__default.DropFirst<BigInteger>(xs);
        xs = _in82;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<BigInteger> ToLarge(Dafny.ISequence<BigInteger> xs) {
      Dafny.ISequence<BigInteger> _603___accumulator = Dafny.Sequence<BigInteger>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return Dafny.Sequence<BigInteger>.Concat(_603___accumulator, Dafny.Sequence<BigInteger>.FromElements());
      } else {
        _603___accumulator = Dafny.Sequence<BigInteger>.Concat(_603___accumulator, Dafny.Sequence<BigInteger>.FromElements(Uint32__64_mUint32Seq_Compile.__default.ToNatRight((xs).Take(Uint32__64_Compile.__default.E()))));
        Dafny.ISequence<BigInteger> _in83 = (xs).Drop(Uint32__64_Compile.__default.E());
        xs = _in83;
        goto TAIL_CALL_START;
      }
    }
  }
} // end of namespace Uint32__64_Compile
namespace srcCollectionsSequencesUint32__64dfyUnitTests_Compile {

  public partial class __default {
    [Xunit.Fact]
    public static void test0()
    {
      Dafny.ISequence<BigInteger> _604_d0;
      _604_d0 = Dafny.Sequence<BigInteger>.FromElements();
      BigInteger _605_r0;
      _605_r0 = Uint32__64_mUint32Seq_Compile.__default.ToNatRight(_604_d0);
    }
    [Xunit.Fact]
    public static void test1()
    {
      Dafny.ISequence<BigInteger> _606_d0;
      _606_d0 = Dafny.Sequence<BigInteger>.FromElements();
      BigInteger _607_r0;
      _607_r0 = Uint32__64_mUint32Seq_Compile.__default.ToNatLeft(_606_d0);
    }
    [Xunit.Fact]
    public static void test2()
    {
      Dafny.ISequence<BigInteger> _608_r0;
      _608_r0 = Uint32__64_mUint32Seq_Compile.__default.FromNat(new BigInteger(65));
    }
    [Xunit.Fact]
    public static void test3()
    {
      Dafny.ISequence<BigInteger> _609_r0;
      _609_r0 = Uint32__64_mUint32Seq_Compile.__default.FromNat(BigInteger.Zero);
    }
    [Xunit.Fact]
    public static void test4()
    {
      Dafny.ISequence<BigInteger> _610_d0;
      _610_d0 = Dafny.Sequence<BigInteger>.FromElements(BigInteger.Zero);
      if (!((new BigInteger((_610_d0).Count)) <= (BigInteger.One))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint32_64.dfy(69,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      Dafny.ISequence<BigInteger> _611_r0;
      _611_r0 = Uint32__64_mUint32Seq_Compile.__default.SeqExtend(_610_d0, BigInteger.One);
      if (!((new BigInteger((_611_r0).Count)) == (BigInteger.One))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint32_64.dfy(71,0): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
      if (!((Uint32__64_mUint32Seq_Compile.__default.ToNatRight(_611_r0)) == (Uint32__64_mUint32Seq_Compile.__default.ToNatRight(_610_d0)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint32_64.dfy(72,0): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
    }
    [Xunit.Fact]
    public static void test5()
    {
      Dafny.ISequence<BigInteger> _612_d0;
      _612_d0 = Dafny.Sequence<BigInteger>.FromElements(BigInteger.Zero, BigInteger.Zero);
      Dafny.ISequence<BigInteger> _613_d1;
      _613_d1 = Dafny.Sequence<BigInteger>.FromElements(BigInteger.Zero, BigInteger.Zero);
      if (!((new BigInteger((_612_d0).Count)) == (new BigInteger((_613_d1).Count)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint32_64.dfy(86,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> _614_r0;
      _614_r0 = Uint32__64_mUint32Seq_Compile.__default.SeqAdd(_612_d0, _613_d1);
    }
    [Xunit.Fact]
    public static void test6()
    {
      Dafny.ISequence<BigInteger> _615_d0;
      _615_d0 = Dafny.Sequence<BigInteger>.FromElements(new BigInteger(12), new BigInteger(2283));
      Dafny.ISequence<BigInteger> _616_d1;
      _616_d1 = Dafny.Sequence<BigInteger>.FromElements(new BigInteger(281), new BigInteger(11138));
      if (!((new BigInteger((_615_d0).Count)) == (new BigInteger((_616_d1).Count)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint32_64.dfy(96,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> _617_r0;
      _617_r0 = Uint32__64_mUint32Seq_Compile.__default.SeqAdd(_615_d0, _616_d1);
    }
    [Xunit.Fact]
    public static void test7()
    {
      Dafny.ISequence<BigInteger> _618_d0;
      _618_d0 = Dafny.Sequence<BigInteger>.FromElements();
      Dafny.ISequence<BigInteger> _619_d1;
      _619_d1 = Dafny.Sequence<BigInteger>.FromElements();
      if (!((new BigInteger((_618_d0).Count)) == (new BigInteger((_619_d1).Count)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint32_64.dfy(105,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> _620_r0;
      _620_r0 = Uint32__64_mUint32Seq_Compile.__default.SeqAdd(_618_d0, _619_d1);
    }
    [Xunit.Fact]
    public static void test8()
    {
      Dafny.ISequence<BigInteger> _621_d0;
      _621_d0 = Dafny.Sequence<BigInteger>.FromElements(new BigInteger(1325), new BigInteger(2331));
      Dafny.ISequence<BigInteger> _622_d1;
      _622_d1 = Dafny.Sequence<BigInteger>.FromElements(new BigInteger(234), new BigInteger(1796));
      if (!((new BigInteger((_621_d0).Count)) == (new BigInteger((_622_d1).Count)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint32_64.dfy(117,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> _623_r0;
      _623_r0 = Uint32__64_mUint32Seq_Compile.__default.SeqSub(_621_d0, _622_d1);
    }
    [Xunit.Fact]
    public static void test9()
    {
      Dafny.ISequence<BigInteger> _624_d0;
      _624_d0 = Dafny.Sequence<BigInteger>.FromElements(new BigInteger(920), new BigInteger(2061));
      Dafny.ISequence<BigInteger> _625_d1;
      _625_d1 = Dafny.Sequence<BigInteger>.FromElements(new BigInteger(645), new BigInteger(2062));
      if (!((new BigInteger((_624_d0).Count)) == (new BigInteger((_625_d1).Count)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint32_64.dfy(127,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> _626_r0;
      _626_r0 = Uint32__64_mUint32Seq_Compile.__default.SeqSub(_624_d0, _625_d1);
    }
    [Xunit.Fact]
    public static void test10()
    {
      Dafny.ISequence<BigInteger> _627_d0;
      _627_d0 = Dafny.Sequence<BigInteger>.FromElements();
      Dafny.ISequence<BigInteger> _628_d1;
      _628_d1 = Dafny.Sequence<BigInteger>.FromElements();
      if (!((new BigInteger((_627_d0).Count)) == (new BigInteger((_628_d1).Count)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint32_64.dfy(136,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> _629_r0;
      _629_r0 = Uint32__64_mUint32Seq_Compile.__default.SeqSub(_627_d0, _628_d1);
    }
    [Xunit.Fact]
    public static void test11()
    {
      Dafny.ISequence<BigInteger> _630_d0;
      _630_d0 = Dafny.Sequence<BigInteger>.FromElements();
      BigInteger _631_r0;
      _631_r0 = Uint32__64_mUint64Seq_Compile.__default.ToNatRight(_630_d0);
    }
    [Xunit.Fact]
    public static void test12()
    {
      Dafny.ISequence<BigInteger> _632_d0;
      _632_d0 = Dafny.Sequence<BigInteger>.FromElements();
      BigInteger _633_r0;
      _633_r0 = Uint32__64_mUint64Seq_Compile.__default.ToNatLeft(_632_d0);
    }
    [Xunit.Fact]
    public static void test13()
    {
      Dafny.ISequence<BigInteger> _634_r0;
      _634_r0 = Uint32__64_mUint64Seq_Compile.__default.FromNat(new BigInteger(65));
    }
    [Xunit.Fact]
    public static void test14()
    {
      Dafny.ISequence<BigInteger> _635_r0;
      _635_r0 = Uint32__64_mUint64Seq_Compile.__default.FromNat(BigInteger.Zero);
    }
    [Xunit.Fact]
    public static void test15()
    {
      Dafny.ISequence<BigInteger> _636_d0;
      _636_d0 = Dafny.Sequence<BigInteger>.FromElements(BigInteger.Zero);
      if (!((new BigInteger((_636_d0).Count)) <= (BigInteger.One))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint32_64.dfy(177,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      Dafny.ISequence<BigInteger> _637_r0;
      _637_r0 = Uint32__64_mUint64Seq_Compile.__default.SeqExtend(_636_d0, BigInteger.One);
      if (!((new BigInteger((_637_r0).Count)) == (BigInteger.One))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint32_64.dfy(179,0): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
      if (!((Uint32__64_mUint64Seq_Compile.__default.ToNatRight(_637_r0)) == (Uint32__64_mUint64Seq_Compile.__default.ToNatRight(_636_d0)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint32_64.dfy(180,0): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
    }
    [Xunit.Fact]
    public static void test16()
    {
      Dafny.ISequence<BigInteger> _638_d0;
      _638_d0 = Dafny.Sequence<BigInteger>.FromElements(BigInteger.Zero, BigInteger.Zero);
      Dafny.ISequence<BigInteger> _639_d1;
      _639_d1 = Dafny.Sequence<BigInteger>.FromElements(BigInteger.Zero, BigInteger.Zero);
      if (!((new BigInteger((_638_d0).Count)) == (new BigInteger((_639_d1).Count)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint32_64.dfy(194,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> _640_r0;
      _640_r0 = Uint32__64_mUint64Seq_Compile.__default.SeqAdd(_638_d0, _639_d1);
    }
    [Xunit.Fact]
    public static void test17()
    {
      Dafny.ISequence<BigInteger> _641_d0;
      _641_d0 = Dafny.Sequence<BigInteger>.FromElements(new BigInteger(342), new BigInteger(4720));
      Dafny.ISequence<BigInteger> _642_d1;
      _642_d1 = Dafny.Sequence<BigInteger>.FromElements(new BigInteger(281), new BigInteger(2283));
      if (!((new BigInteger((_641_d0).Count)) == (new BigInteger((_642_d1).Count)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint32_64.dfy(204,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> _643_r0;
      _643_r0 = Uint32__64_mUint64Seq_Compile.__default.SeqAdd(_641_d0, _642_d1);
    }
    [Xunit.Fact]
    public static void test18()
    {
      Dafny.ISequence<BigInteger> _644_d0;
      _644_d0 = Dafny.Sequence<BigInteger>.FromElements();
      Dafny.ISequence<BigInteger> _645_d1;
      _645_d1 = Dafny.Sequence<BigInteger>.FromElements();
      if (!((new BigInteger((_644_d0).Count)) == (new BigInteger((_645_d1).Count)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint32_64.dfy(213,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> _646_r0;
      _646_r0 = Uint32__64_mUint64Seq_Compile.__default.SeqAdd(_644_d0, _645_d1);
    }
    [Xunit.Fact]
    public static void test19()
    {
      Dafny.ISequence<BigInteger> _647_d0;
      _647_d0 = Dafny.Sequence<BigInteger>.FromElements(new BigInteger(1325), new BigInteger(2331));
      Dafny.ISequence<BigInteger> _648_d1;
      _648_d1 = Dafny.Sequence<BigInteger>.FromElements(new BigInteger(234), new BigInteger(1796));
      if (!((new BigInteger((_647_d0).Count)) == (new BigInteger((_648_d1).Count)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint32_64.dfy(225,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> _649_r0;
      _649_r0 = Uint32__64_mUint64Seq_Compile.__default.SeqSub(_647_d0, _648_d1);
    }
    [Xunit.Fact]
    public static void test20()
    {
      Dafny.ISequence<BigInteger> _650_d0;
      _650_d0 = Dafny.Sequence<BigInteger>.FromElements(new BigInteger(920), new BigInteger(2061));
      Dafny.ISequence<BigInteger> _651_d1;
      _651_d1 = Dafny.Sequence<BigInteger>.FromElements(new BigInteger(645), new BigInteger(2062));
      if (!((new BigInteger((_650_d0).Count)) == (new BigInteger((_651_d1).Count)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint32_64.dfy(235,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> _652_r0;
      _652_r0 = Uint32__64_mUint64Seq_Compile.__default.SeqSub(_650_d0, _651_d1);
    }
    [Xunit.Fact]
    public static void test21()
    {
      Dafny.ISequence<BigInteger> _653_d0;
      _653_d0 = Dafny.Sequence<BigInteger>.FromElements();
      Dafny.ISequence<BigInteger> _654_d1;
      _654_d1 = Dafny.Sequence<BigInteger>.FromElements();
      if (!((new BigInteger((_653_d0).Count)) == (new BigInteger((_654_d1).Count)))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint32_64.dfy(244,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      _System._ITuple2<Dafny.ISequence<BigInteger>, BigInteger> _655_r0;
      _655_r0 = Uint32__64_mUint64Seq_Compile.__default.SeqSub(_653_d0, _654_d1);
    }
    [Xunit.Fact]
    public static void test22()
    {
      Dafny.ISequence<BigInteger> _656_d0;
      _656_d0 = Dafny.Sequence<BigInteger>.FromElements();
      Dafny.ISequence<BigInteger> _657_r0;
      _657_r0 = Uint32__64_Compile.__default.ToSmall(_656_d0);
      if (!((new BigInteger((_657_r0).Count)) == ((new BigInteger((_656_d0).Count)) * (Uint32__64_Compile.__default.E())))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint32_64.dfy(256,0): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
    }
    [Xunit.Fact]
    public static void test23()
    {
      Dafny.ISequence<BigInteger> _658_d0;
      _658_d0 = Dafny.Sequence<BigInteger>.FromElements(BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero);
      if (!((Dafny.Helpers.EuclideanModulus(new BigInteger((_658_d0).Count), Uint32__64_Compile.__default.E())).Sign == 0)) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint32_64.dfy(265,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      Dafny.ISequence<BigInteger> _659_r0;
      _659_r0 = Uint32__64_Compile.__default.ToLarge(_658_d0);
      if (!((new BigInteger((_659_r0).Count)) == (Dafny.Helpers.EuclideanDivision(new BigInteger((_658_d0).Count), Uint32__64_Compile.__default.E())))) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Collections/Sequences/Uint32_64.dfy(267,0): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
    }
  }
} // end of namespace srcCollectionsSequencesUint32__64dfyUnitTests_Compile
namespace srcWrappersdfyUnitTests_Compile {

  public partial class __default {
    [Xunit.Fact]
    public static void test0()
    {
      Wrappers_Compile._IOption<BigInteger> _660_d0;
      _660_d0 = Wrappers_Compile.Option<BigInteger>.create_Some(BigInteger.Zero);
      Wrappers_Compile._IResult<BigInteger, Dafny.ISequence<char>> _661_r0;
      _661_r0 = (_660_d0).ToResult();
    }
    [Xunit.Fact]
    public static void test2()
    {
      Wrappers_Compile._IOption<BigInteger> _662_d0;
      _662_d0 = Wrappers_Compile.Option<BigInteger>.create_Some(BigInteger.Zero);
      BigInteger _663_r0;
      _663_r0 = Wrappers_Compile.Option<BigInteger>.UnwrapOr(_662_d0, BigInteger.One);
    }
    [Xunit.Fact]
    public static void test4()
    {
      Wrappers_Compile._IOption<BigInteger> _664_d0;
      _664_d0 = Wrappers_Compile.Option<BigInteger>.create_Some(BigInteger.Zero);
      bool _665_r0;
      _665_r0 = (_664_d0).IsFailure();
    }
    [Xunit.Fact]
    public static void test5()
    {
      Wrappers_Compile._IOption<BigInteger> _666_d0;
      _666_d0 = Wrappers_Compile.Option<BigInteger>.create_None();
      if (!((_666_d0).is_None)) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Wrappers.dfy(48,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      Wrappers_Compile._IOption<BigInteger> _667_r0;
      _667_r0 = (_666_d0).PropagateFailure<BigInteger>();
    }
    [Xunit.Fact]
    public static void test6()
    {
      Wrappers_Compile._IOption<BigInteger> _668_d0;
      _668_d0 = Wrappers_Compile.Option<BigInteger>.create_Some(BigInteger.Zero);
      if (!((_668_d0).is_Some)) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Wrappers.dfy(55,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      BigInteger _669_r0;
      _669_r0 = (_668_d0).Extract();
    }
    [Xunit.Fact]
    public static void test7()
    {
      Wrappers_Compile._IResult<BigInteger, BigInteger> _670_d0;
      _670_d0 = Wrappers_Compile.Result<BigInteger, BigInteger>.create_Success(BigInteger.Zero);
      Wrappers_Compile._IOption<BigInteger> _671_r0;
      _671_r0 = (_670_d0).ToOption();
    }
    [Xunit.Fact]
    public static void test8()
    {
      Wrappers_Compile._IResult<BigInteger, BigInteger> _672_d0;
      _672_d0 = Wrappers_Compile.Result<BigInteger, BigInteger>.create_Failure(BigInteger.Zero);
      Wrappers_Compile._IOption<BigInteger> _673_r0;
      _673_r0 = (_672_d0).ToOption();
    }
    [Xunit.Fact]
    public static void test9()
    {
      Wrappers_Compile._IResult<BigInteger, BigInteger> _674_d0;
      _674_d0 = Wrappers_Compile.Result<BigInteger, BigInteger>.create_Success(BigInteger.Zero);
      BigInteger _675_r0;
      _675_r0 = Wrappers_Compile.Result<BigInteger, BigInteger>.UnwrapOr(_674_d0, BigInteger.One);
    }
    [Xunit.Fact]
    public static void test10()
    {
      Wrappers_Compile._IResult<BigInteger, BigInteger> _676_d0;
      _676_d0 = Wrappers_Compile.Result<BigInteger, BigInteger>.create_Failure(BigInteger.Zero);
      BigInteger _677_r0;
      _677_r0 = Wrappers_Compile.Result<BigInteger, BigInteger>.UnwrapOr(_676_d0, BigInteger.One);
    }
    [Xunit.Fact]
    public static void test11()
    {
      Wrappers_Compile._IResult<BigInteger, BigInteger> _678_d0;
      _678_d0 = Wrappers_Compile.Result<BigInteger, BigInteger>.create_Success(BigInteger.Zero);
      bool _679_r0;
      _679_r0 = (_678_d0).IsFailure();
    }
    [Xunit.Fact]
    public static void test12()
    {
      Wrappers_Compile._IResult<BigInteger, BigInteger> _680_d0;
      _680_d0 = Wrappers_Compile.Result<BigInteger, BigInteger>.create_Failure(BigInteger.Zero);
      if (!((_680_d0).is_Failure)) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Wrappers.dfy(102,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      Wrappers_Compile._IResult<BigInteger, BigInteger> _681_r0;
      _681_r0 = (_680_d0).PropagateFailure<BigInteger>();
    }
    [Xunit.Fact]
    public static void test13()
    {
      Wrappers_Compile._IResult<BigInteger, BigInteger> _682_d0;
      _682_d0 = Wrappers_Compile.Result<BigInteger, BigInteger>.create_Success(BigInteger.Zero);
      Wrappers_Compile._IResult<BigInteger, BigInteger> _683_r0;
      _683_r0 = Wrappers_Compile.Result<BigInteger, BigInteger>.MapFailure<BigInteger>(_682_d0, ((System.Func<BigInteger, BigInteger>)((_684_a0) => {
        return BigInteger.Zero;
      })));
    }
    [Xunit.Fact]
    public static void test14()
    {
      Wrappers_Compile._IResult<BigInteger, BigInteger> _685_d0;
      _685_d0 = Wrappers_Compile.Result<BigInteger, BigInteger>.create_Failure(BigInteger.Zero);
      Wrappers_Compile._IResult<BigInteger, BigInteger> _686_r0;
      _686_r0 = Wrappers_Compile.Result<BigInteger, BigInteger>.MapFailure<BigInteger>(_685_d0, ((System.Func<BigInteger, BigInteger>)((_687_a0) => {
        return BigInteger.Zero;
      })));
    }
    [Xunit.Fact]
    public static void test15()
    {
      Wrappers_Compile._IResult<BigInteger, BigInteger> _688_d0;
      _688_d0 = Wrappers_Compile.Result<BigInteger, BigInteger>.create_Success(BigInteger.Zero);
      if (!((_688_d0).is_Success)) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Wrappers.dfy(126,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      BigInteger _689_r0;
      _689_r0 = (_688_d0).Extract();
    }
    [Xunit.Fact]
    public static void test16()
    {
      Wrappers_Compile._IOutcome<BigInteger> _690_d0;
      _690_d0 = Wrappers_Compile.Outcome<BigInteger>.create_Pass();
      bool _691_r0;
      _691_r0 = (_690_d0).IsFailure();
    }
    [Xunit.Fact]
    public static void test17()
    {
      Wrappers_Compile._IOutcome<BigInteger> _692_d0;
      _692_d0 = Wrappers_Compile.Outcome<BigInteger>.create_Fail(BigInteger.Zero);
      if (!((_692_d0).is_Fail)) {
        throw new Dafny.HaltException("/Users/fedchina/Desktop/libraries/test/Wrappers.dfy(139,0): " + Dafny.Sequence<char>.FromString("Test does not meet preconditions and should be removed"));
      }
      Wrappers_Compile._IResult<BigInteger, BigInteger> _693_r0;
      _693_r0 = (_692_d0).PropagateFailure<BigInteger>();
    }
    [Xunit.Fact]
    public static void test18()
    {
      Wrappers_Compile._IOutcome<BigInteger> _694_r0;
      _694_r0 = Wrappers_Compile.__default.Need<BigInteger>(true, BigInteger.Zero);
    }
    [Xunit.Fact]
    public static void test19()
    {
      Wrappers_Compile._IOutcome<BigInteger> _695_r0;
      _695_r0 = Wrappers_Compile.__default.Need<BigInteger>(false, BigInteger.Zero);
    }
  }
} // end of namespace srcWrappersdfyUnitTests_Compile
namespace AllTests_Compile {

} // end of namespace AllTests_Compile
namespace _module {

} // end of namespace _module
