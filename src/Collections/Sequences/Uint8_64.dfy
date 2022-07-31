include "LittleEndianNatConversions.dfy"

/* Conversions between sequences of uint8 and uint64. */
module Uint8_64 refines LittleEndianNatConversions {

  module {:extern "Uint8__64_mUint8Seq_Compile"} Uint8Seq refines SmallSeq {
    function method BITS(): nat { 8 }
  }

  module {:extern "Uint8__64_mUint64Seq_Compile"} Uint64Seq refines LargeSeq {
    import Small = Uint8Seq
    function method BITS(): nat { 64 }
  }

  import opened Large = Uint64Seq
  import Small = Large.Small

}