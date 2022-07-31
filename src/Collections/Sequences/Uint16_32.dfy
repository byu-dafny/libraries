include "LittleEndianNatConversions.dfy"

/* Conversions between sequences of uint16 and uint32. */
module Uint16_32 refines LittleEndianNatConversions {

  module {:extern "Uint16__32_mUint16Seq_Compile"} Uint16Seq refines SmallSeq {
    function method BITS(): nat { 16 }
  }

  module {:extern "Uint16__32_mUint32Seq_Compile"} Uint32Seq refines LargeSeq {
    import Small = Uint16Seq
    function method BITS(): nat { 32 }
  }

  import opened Large = Uint32Seq
  import Small = Large.Small

}