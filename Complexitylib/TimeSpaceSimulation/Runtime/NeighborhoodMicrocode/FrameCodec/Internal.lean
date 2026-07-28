/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.FrameCodec.Defs
import Complexitylib.TimeSpaceSimulation.Runtime.PackedDigits

/-!
# Radix codec for neighborhood-scheduler frames -- proofs
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace FrameCodec
namespace Internal

theorem encodeList_append_internal
    (base : ℕ) (leading trailing : List ℕ) :
    encodeList base (leading ++ trailing) =
      encodeList base leading +
        base ^ leading.length * encodeList base trailing := by
  induction leading with
  | nil =>
      simp [encodeList]
  | cons digit rest ih =>
      simp only [List.cons_append, encodeList, List.length_cons]
      rw [ih, pow_succ]
      simp only [PackedDigits.push]
      ring

theorem encodeList_replicate_zero_internal
    (base count : ℕ) :
    encodeList base (List.replicate count 0) = 0 := by
  induction count with
  | zero =>
      simp [encodeList]
  | succ count ih =>
      simp [List.replicate_succ, encodeList, PackedDigits.push, ih]

theorem pop_encodeList_cons_internal
    {base digit : ℕ} {digits : List ℕ}
    (hbase : 0 < base) (hdigit : digit < base) :
    PackedDigits.pop base
        (encodeList base (digit :: digits)) =
      encodeList base digits := by
  exact PackedDigits.pop_push hbase hdigit

theorem pop_iterate_encodeList_internal
    {base : ℕ} (hbase : 0 < base)
    (digits : List ℕ)
    (hdigits : ∀ digit ∈ digits, digit < base) :
    ∀ count, count ≤ digits.length →
      (PackedDigits.pop base)^[count]
          (encodeList base digits) =
        encodeList base (digits.drop count) := by
  intro count hcount
  induction count generalizing digits with
  | zero =>
      simp
  | succ count ih =>
      cases digits with
      | nil =>
          simp at hcount
      | cons digit rest =>
          rw [Function.iterate_succ_apply]
          rw [pop_encodeList_cons_internal hbase
            (hdigits digit (by simp))]
          rw [ih rest
            (fun current hcurrent =>
              hdigits current (by simp [hcurrent]))
            (by simp at hcount ⊢; omega)]
          simp

theorem encodeList_scalarDigits_internal
    {base value : ℕ}
    (hbase : 0 < base) (hvalue : value < base ^ scalarDigitCount) :
    encodeList base (scalarDigits base value) = value := by
  have hdiv : value / base < base := by
    rw [Nat.div_lt_iff_lt_mul hbase]
    simpa [scalarDigitCount, pow_two] using hvalue
  simp only [scalarDigits, encodeList, PackedDigits.push,
    PackedDigits.digit, Nat.pow_zero, Nat.pow_one, Nat.div_one]
  rw [Nat.mod_eq_of_lt hdiv]
  simpa [Nat.mul_comm] using Nat.mod_add_div value base

theorem encodeList_digit_internal
    {base : ℕ} (digits : List ℕ)
    (hdigits : ∀ digit ∈ digits, digit < base)
    {index : ℕ} (hindex : index < digits.length) :
    PackedDigits.digit base (encodeList base digits) index =
      digits.getD index 0 := by
  induction digits generalizing index with
  | nil =>
      simp at hindex
  | cons digit rest ih =>
      cases index with
      | zero =>
          simp only [encodeList]
          rw [PackedDigits.digit_push_zero
            (hdigits digit (by simp))]
          rfl
      | succ index =>
          simp only [encodeList]
          rw [PackedDigits.digit_push_succ
            (by
              have hdigit := hdigits digit (by simp)
              omega)
            (hdigits digit (by simp))]
          apply ih
          · intro current hcurrent
            exact hdigits current (by simp [hcurrent])
          ·
            have hsucc : Nat.succ index < Nat.succ rest.length := by
              simpa [Nat.succ_eq_add_one] using hindex
            exact Nat.lt_of_succ_lt_succ hsucc

theorem encodeList_lt_pow_internal
    {base : ℕ} (digits : List ℕ)
    (hdigits : ∀ digit ∈ digits, digit < base) :
    encodeList base digits < base ^ digits.length := by
  induction digits with
  | nil =>
      simp [encodeList]
  | cons digit rest ih =>
      simp only [encodeList, List.length_cons]
      apply PackedDigits.push_lt_pow
      · exact ih fun current hcurrent =>
          hdigits current (by simp [hcurrent])
      · exact hdigits digit (by simp)

theorem scalarDigits_length_internal (base value : ℕ) :
    (scalarDigits base value).length = scalarDigitCount := by
  rfl

theorem nodeDigits_length_internal
    (node : NeighborhoodEvaluator.QueryNode workTapeCount horizon) :
    (nodeDigits node).length = nodeDigitCount := by
  cases node with
  | failure => rfl
  | graph node =>
      cases node <;> rfl

theorem phaseDigits_length_internal
    (base : ℕ) (phase : NeighborhoodScheduler.Phase workTapeCount) :
    (phaseDigits base phase).length = phaseDigitCount := by
  cases phase <;> rfl

theorem frameDigits_length_internal
    (base : ℕ)
    (frame : NeighborhoodScheduler.Frame tm instanceData) :
    (frameDigits base frame).length = frameDigitCount := by
  simp [frameDigits, nodeDigits_length_internal,
    scalarDigits_length_internal, phaseDigits_length_internal,
    reservedDigitCount, frameDigitCount, nodeDigitCount,
    scalarDigitCount, phaseDigitCount]

theorem encodeNode_lt_pow_internal
    {base : ℕ}
    (node : NeighborhoodEvaluator.QueryNode workTapeCount horizon)
    (hfits : ∀ digit ∈ nodeDigits node, digit < base) :
    encodeNode base node < base ^ nodeDigitCount := by
  simpa [encodeNode, nodeDigits_length_internal] using
    encodeList_lt_pow_internal (nodeDigits node) hfits

theorem encodePhase_lt_pow_internal
    {base : ℕ} (phase : NeighborhoodScheduler.Phase workTapeCount)
    (hfits : ∀ digit ∈ phaseDigits base phase, digit < base) :
    encodePhase base phase < base ^ phaseDigitCount := by
  simpa [encodePhase, phaseDigits_length_internal] using
    encodeList_lt_pow_internal (phaseDigits base phase) hfits

theorem encodeFrame_lt_pow_internal
    {base : ℕ}
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (hfits : FrameFits base frame) :
    encodeFrame base frame < base ^ frameDigitCount := by
  simpa [encodeFrame, frameDigits_length_internal] using
    encodeList_lt_pow_internal (frameDigits base frame) hfits

theorem encodeFrame_succ_lt_pow_internal
    {base : ℕ}
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (hbase : 1 < base)
    (hfits : FrameFits base frame) :
    encodeFrame base frame + 1 < base ^ frameDigitCount := by
  let used :=
    frame.fuel ::
      (nodeDigits frame.node ++
        (scalarDigits base frame.scalar ++
          (frame.out.val :: phaseDigits base frame.phase)))
  have hdigits :
      frameDigits base frame =
        used ++ List.replicate reservedDigitCount 0 := by
    simp [frameDigits, used, List.append_assoc]
  have husedFits : ∀ digit ∈ used, digit < base := by
    intro digit hdigit
    apply hfits digit
    rw [hdigits]
    exact List.mem_append_left _ hdigit
  have husedLength : used.length = 15 := by
    simp [used, nodeDigits_length_internal,
      scalarDigits_length_internal, phaseDigits_length_internal,
      nodeDigitCount, scalarDigitCount, phaseDigitCount]
  have hcode : encodeFrame base frame = encodeList base used := by
    rw [encodeFrame, hdigits, encodeList_append_internal,
      encodeList_replicate_zero_internal]
    simp
  have hsmall : encodeFrame base frame < base ^ 15 := by
    rw [hcode]
    simpa [husedLength] using
      encodeList_lt_pow_internal used husedFits
  have hpowers : base ^ 15 < base ^ frameDigitCount := by
    apply Nat.pow_lt_pow_right hbase
    simp [frameDigitCount]
  omega

theorem encodeFrame_digit_internal
    {base : ℕ}
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (hfits : FrameFits base frame)
    (index : Fin frameDigitCount) :
    PackedDigits.digit base (encodeFrame base frame) index.val =
      (frameDigits base frame).getD index.val 0 := by
  apply encodeList_digit_internal (frameDigits base frame) hfits
    (by
      rw [frameDigits_length_internal]
      exact index.isLt)

theorem encodeFrame_fuel_internal
    {base : ℕ}
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (hfits : FrameFits base frame) :
    PackedDigits.digit base (encodeFrame base frame) 0 =
      frame.fuel := by
  simpa [frameDigits] using
    encodeFrame_digit_internal frame hfits
      (⟨0, by simp [frameDigitCount]⟩ : Fin frameDigitCount)

theorem encodeFrame_nodeDigit_internal
    {base : ℕ}
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (hfits : FrameFits base frame)
    (index : Fin nodeDigitCount) :
    PackedDigits.digit base (encodeFrame base frame)
        (1 + index.val) =
      (nodeDigits frame.node).getD index.val 0 := by
  have hposition : 1 + index.val < frameDigitCount := by
    have hindex := index.isLt
    simp only [nodeDigitCount] at hindex
    simp only [frameDigitCount]
    omega
  rw [encodeFrame_digit_internal frame hfits
    ⟨1 + index.val, hposition⟩]
  simp only [frameDigits]
  rw [show 1 + index.val = index.val + 1 by omega]
  rw [List.getD_cons_succ]
  apply List.getD_append
  rw [nodeDigits_length_internal]
  exact index.isLt

theorem encodeFrame_scalarDigit_internal
    {base : ℕ}
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (hfits : FrameFits base frame)
    (index : Fin scalarDigitCount) :
    PackedDigits.digit base (encodeFrame base frame)
        (5 + index.val) =
      (scalarDigits base frame.scalar).getD index.val 0 := by
  have hposition : 5 + index.val < frameDigitCount := by
    have hindex := index.isLt
    simp only [scalarDigitCount] at hindex
    simp only [frameDigitCount]
    omega
  rw [encodeFrame_digit_internal frame hfits
    ⟨5 + index.val, hposition⟩]
  simp only [frameDigits]
  rw [show 5 + index.val = (4 + index.val) + 1 by omega]
  rw [List.getD_cons_succ]
  rw [List.getD_append_right
    (nodeDigits frame.node)
    (scalarDigits base frame.scalar ++
      (frame.out.val ::
        (phaseDigits base frame.phase ++
          List.replicate reservedDigitCount 0)))
    0 (4 + index.val)
    (by
      rw [nodeDigits_length_internal]
      simp only [nodeDigitCount]
      omega)]
  simp only [nodeDigits_length_internal]
  rw [show 4 + index.val - nodeDigitCount = index.val by
    simp [nodeDigitCount]]
  apply List.getD_append
  rw [scalarDigits_length_internal]
  exact index.isLt

theorem encodeFrame_out_internal
    {base : ℕ}
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (hfits : FrameFits base frame) :
    PackedDigits.digit base (encodeFrame base frame) 7 =
      frame.out.val := by
  rw [encodeFrame_digit_internal frame hfits
    (⟨7, by simp [frameDigitCount]⟩ : Fin frameDigitCount)]
  simp only [frameDigits]
  rw [show 7 = 6 + 1 by omega]
  rw [List.getD_cons_succ]
  rw [List.getD_append_right
    (nodeDigits frame.node)
    (scalarDigits base frame.scalar ++
      (frame.out.val ::
        (phaseDigits base frame.phase ++
          List.replicate reservedDigitCount 0)))
    0 6 (by simp [nodeDigits_length_internal, nodeDigitCount])]
  simp only [nodeDigits_length_internal, nodeDigitCount]
  rw [List.getD_append_right
    (scalarDigits base frame.scalar)
    (frame.out.val ::
      (phaseDigits base frame.phase ++
        List.replicate reservedDigitCount 0))
    0 2 (by simp [scalarDigits_length_internal, scalarDigitCount])]
  simp [scalarDigits_length_internal, scalarDigitCount]

theorem encodeFrame_phaseDigit_internal
    {base : ℕ}
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (hfits : FrameFits base frame)
    (index : Fin phaseDigitCount) :
    PackedDigits.digit base (encodeFrame base frame)
        (8 + index.val) =
      (phaseDigits base frame.phase).getD index.val 0 := by
  have hposition : 8 + index.val < frameDigitCount := by
    have hindex := index.isLt
    simp only [phaseDigitCount] at hindex
    simp only [frameDigitCount]
    omega
  rw [encodeFrame_digit_internal frame hfits
    ⟨8 + index.val, hposition⟩]
  simp only [frameDigits]
  rw [show 8 + index.val = (7 + index.val) + 1 by omega]
  rw [List.getD_cons_succ]
  rw [List.getD_append_right
    (nodeDigits frame.node)
    (scalarDigits base frame.scalar ++
      (frame.out.val ::
        (phaseDigits base frame.phase ++
          List.replicate reservedDigitCount 0)))
    0 (7 + index.val)
    (by
      rw [nodeDigits_length_internal]
      simp only [nodeDigitCount]
      omega)]
  simp only [nodeDigits_length_internal, nodeDigitCount]
  rw [show 7 + index.val - 4 = 3 + index.val by omega]
  rw [List.getD_append_right
    (scalarDigits base frame.scalar)
    (frame.out.val ::
      (phaseDigits base frame.phase ++
        List.replicate reservedDigitCount 0))
    0 (3 + index.val)
    (by
      rw [scalarDigits_length_internal]
      simp only [scalarDigitCount]
      omega)]
  simp only [scalarDigits_length_internal, scalarDigitCount]
  rw [show 3 + index.val - 2 = index.val + 1 by omega]
  rw [List.getD_cons_succ]
  apply List.getD_append
  rw [phaseDigits_length_internal]
  exact index.isLt

end Internal
end FrameCodec
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
