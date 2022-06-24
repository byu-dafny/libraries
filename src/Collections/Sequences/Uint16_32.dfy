include "LittleEndianNatConversions.dfy"

/* Conversions between sequences of uint16 and uint32. */
module Uint16_32 refines LittleEndianNatConversions {

  module Uint16Seq refines SmallSeq {
    function method BITS(): nat { 16 }
  }

  module Uint32Seq refines LargeSeq {
    import Small = Uint16Seq
    function method BITS(): nat { 32 }
  }

  import opened Large = Uint32Seq
  import Small = Large.Small

}