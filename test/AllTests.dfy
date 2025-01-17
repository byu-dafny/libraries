include "Wrappers.dfy"
include "Math.dfy"
include "BoundedInts.dfy"
include "Functions.dfy"
include "NonlinearArithmetic/Mul.dfy"
include "NonlinearArithmetic/Internals/ModInternals.dfy"
include "NonlinearArithmetic/Internals/MulInternals.dfy"
include "NonlinearArithmetic/Internals/MulInternalsNonlinear.dfy"
include "NonlinearArithmetic/Internals/DivInternals.dfy"
include "NonlinearArithmetic/Internals/GeneralInternals.dfy"
include "NonlinearArithmetic/Internals/ModInternalsNonlinear.dfy"
include "NonlinearArithmetic/Internals/DivInternalsNonlinear.dfy"
include "NonlinearArithmetic/Power.dfy"
include "NonlinearArithmetic/DivMod.dfy"
include "NonlinearArithmetic/Power2.dfy"
include "Collections/Maps/Maps.dfy"
include "Collections/Maps/Imaps.dfy"
include "Collections/Sequences/LittleEndianNatConversions.dfy"
include "Collections/Sequences/Uint8_32.dfy"
include "Collections/Sequences/LittleEndianNat.dfy"
include "Collections/Sequences/Seq.dfy"
include "Collections/Sequences/Uint16_32.dfy"
include "Collections/Sequences/Uint8_64.dfy"
include "Collections/Sequences/Uint8_16.dfy"
include "Collections/Sequences/Uint32_64.dfy"
include "Collections/Sets/Isets.dfy"
include "Collections/Sets/Sets.dfy"

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