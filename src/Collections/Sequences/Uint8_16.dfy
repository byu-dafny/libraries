include "LittleEndianNatConversions.dfy"

/* Conversions between sequences of uint8 and uint16. */
module Uint8_16 refines LittleEndianNatConversions {

  module {:extern "Uint8__16_mUint8Seq_Compile"} Uint8Seq refines SmallSeq {
    function method BITS(): nat { 8 }
  }

  module {:extern "Uint8__16_mUint16Seq_Compile"} Uint16Seq refines LargeSeq {
    import Small = Uint8Seq
    function method BITS(): nat { 16 }
  }

  import opened Large = Uint16Seq
  import Small = Large.Small

}