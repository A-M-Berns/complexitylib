/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.FrameCodec.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.FrameCodec.Internal

/-!
# Radix codec for neighborhood-scheduler frames

The public interface exposes the exact twenty-four-digit allocation used by
the concrete fixed-register encoder and decoder.
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace FrameCodec

/-- Little-endian list encoding splits exactly at list append. -/
theorem encodeList_append
    (base : ℕ) (leading trailing : List ℕ) :
    encodeList base (leading ++ trailing) =
      encodeList base leading +
        base ^ leading.length * encodeList base trailing :=
  Internal.encodeList_append_internal base leading trailing

/-- A list of zero digits encodes as zero. -/
theorem encodeList_replicate_zero
    (base count : ℕ) :
    encodeList base (List.replicate count 0) = 0 :=
  Internal.encodeList_replicate_zero_internal base count

/-- Repeated packed-word pops drop the corresponding fitting digit prefix. -/
theorem pop_iterate_encodeList
    {base : ℕ} (hbase : 0 < base)
    (digits : List ℕ)
    (hdigits : ∀ digit ∈ digits, digit < base)
    (count : ℕ) (hcount : count ≤ digits.length) :
    (PackedDigits.pop base)^[count]
        (encodeList base digits) =
      encodeList base (digits.drop count) :=
  Internal.pop_iterate_encodeList_internal
    hbase digits hdigits count hcount

/-- A fitting two-digit scalar encoding reconstructs the scalar exactly. -/
theorem encodeList_scalarDigits
    {base value : ℕ}
    (hbase : 0 < base)
    (hvalue : value < base ^ scalarDigitCount) :
    encodeList base (scalarDigits base value) = value :=
  Internal.encodeList_scalarDigits_internal hbase hvalue

/-- One fitting frame code occupies fewer than twenty-four radix digits. -/
theorem encodeFrame_lt_pow
    {base : ℕ}
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (hfits : FrameFits base frame) :
    encodeFrame base frame < base ^ frameDigitCount :=
  Internal.encodeFrame_lt_pow_internal frame hfits

/-- The nine reserved high zero digits leave room to shift every frame code
by one while retaining the advertised twenty-four-digit radix bound. -/
theorem encodeFrame_succ_lt_pow
    {base : ℕ}
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (hbase : 1 < base)
    (hfits : FrameFits base frame) :
    encodeFrame base frame + 1 < base ^ frameDigitCount :=
  Internal.encodeFrame_succ_lt_pow_internal frame hbase hfits

/-- Digit zero of a fitting frame is its recursion fuel. -/
theorem encodeFrame_fuel
    {base : ℕ}
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (hfits : FrameFits base frame) :
    PackedDigits.digit base (encodeFrame base frame) 0 =
      frame.fuel :=
  Internal.encodeFrame_fuel_internal frame hfits

/-- Digits one through four are the active query-node code. -/
theorem encodeFrame_nodeDigit
    {base : ℕ}
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (hfits : FrameFits base frame)
    (index : Fin nodeDigitCount) :
    PackedDigits.digit base (encodeFrame base frame)
        (1 + index.val) =
      (nodeDigits frame.node).getD index.val 0 :=
  Internal.encodeFrame_nodeDigit_internal frame hfits index

/-- Digits five and six are the two-digit field scalar. -/
theorem encodeFrame_scalarDigit
    {base : ℕ}
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (hfits : FrameFits base frame)
    (index : Fin scalarDigitCount) :
    PackedDigits.digit base (encodeFrame base frame)
        (5 + index.val) =
      (scalarDigits base frame.scalar).getD index.val 0 :=
  Internal.encodeFrame_scalarDigit_internal frame hfits index

/-- Digit seven is the catalytic output-register index. -/
theorem encodeFrame_out
    {base : ℕ}
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (hfits : FrameFits base frame) :
    PackedDigits.digit base (encodeFrame base frame) 7 =
      frame.out.val :=
  Internal.encodeFrame_out_internal frame hfits

/-- Digits eight through fourteen are the scheduler-phase code. -/
theorem encodeFrame_phaseDigit
    {base : ℕ}
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (hfits : FrameFits base frame)
    (index : Fin phaseDigitCount) :
    PackedDigits.digit base (encodeFrame base frame)
        (8 + index.val) =
      (phaseDigits base frame.phase).getD index.val 0 :=
  Internal.encodeFrame_phaseDigit_internal frame hfits index

end FrameCodec
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
