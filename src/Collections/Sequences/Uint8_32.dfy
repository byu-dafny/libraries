include "LittleEndianNatConversions.dfy"

/* Conversions between sequences of uint8 and uint32. */
module Uint8_32 refines LittleEndianNatConversions {

  module {:extern "Uint8__32_mUint8Seq_Compile"} Uint8Seq refines SmallSeq {
    function method BITS(): nat { 8 }
  }

  module {:extern "Uint8__32_mUint32Seq_Compile"} Uint32Seq refines LargeSeq {
    import Small = Uint8Seq
    function method BITS(): nat { 32 }
  }

  import opened Large = Uint32Seq
  import Small = Large.Small

}
