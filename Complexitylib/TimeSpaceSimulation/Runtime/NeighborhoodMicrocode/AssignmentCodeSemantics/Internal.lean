/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.AssignmentCodeSemantics.Defs

/-!
# Correctness internals for streamed assignment coordinates
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace AssignmentCodeSemantics
namespace Internal

open TreeEval CookMertz

private theorem toBits_get_eq_radixDigit :
    ∀ (width code : ℕ) (index : Fin width),
      (Nat.toBits width code).get
          (Fin.cast (Nat.length_toBits width code).symm index) =
        decide
          (CombineTerm.radixDigit 2 code
            (width - 1 - index.val) = 1) := by
  intro width
  induction width with
  | zero =>
      intro code index
      exact Fin.elim0 index
  | succ width ih =>
      intro code index
      refine Fin.cases ?_ (fun index => ?_) index
      · simp only [Nat.toBits, Fin.cast_zero, List.get_cons_zero,
          Fin.val_zero, Nat.sub_zero, Nat.succ_sub_one]
        change decide (code / 2 ^ width % 2 = 1) =
          decide (code / 2 ^ width % 2 = 1)
        rfl
      · have hsub :
            width - (index.val + 1) =
              width - 1 - index.val := by
          omega
        simpa [Nat.toBits, hsub] using ih code index

theorem payloadChunkIndex_val_internal
    (payloadWidth fanIn : ℕ) (position : Fin payloadWidth) :
    (payloadChunkIndex payloadWidth fanIn position).val =
      position.val /
        PrimeGrouped.Logarithmic.chunkBits payloadWidth fanIn :=
  rfl

theorem payloadChunkOffset_val_internal
    (payloadWidth fanIn : ℕ) (position : Fin payloadWidth) :
    (payloadChunkOffset payloadWidth fanIn position).val =
      position.val %
        PrimeGrouped.Logarithmic.chunkBits payloadWidth fanIn :=
  rfl

theorem assignmentBits_apply_internal
    (payloadWidth fanIn code : ℕ)
    (child : Fin fanIn) (position : Fin payloadWidth) :
    assignmentBits payloadWidth fanIn code child position =
      assignmentChunks payloadWidth fanIn code
        (groupedCoordinate payloadWidth fanIn child position)
        (payloadChunkOffset payloadWidth fanIn position) :=
  rfl

theorem encodedBitPosition_val_internal
    (payloadWidth fanIn : ℕ)
    (child : Fin fanIn) (position : Fin payloadWidth) :
    (encodedBitPosition payloadWidth fanIn child position).val =
      PrimeGrouped.Logarithmic.chunkBits payloadWidth fanIn *
          PrimeGrouped.Logarithmic.chunkCount payloadWidth fanIn *
          child.val +
        position.val := by
  simp [encodedBitPosition, groupedCoordinate, payloadChunkIndex,
    payloadChunkOffset, GroupedExtension.Evaluation.bitEncoding,
    finProdFinEquiv]
  let chunkBits :=
    PrimeGrouped.Logarithmic.chunkBits payloadWidth fanIn
  let chunkCount :=
    PrimeGrouped.Logarithmic.chunkCount payloadWidth fanIn
  change
    position.val % chunkBits +
        chunkBits *
          (position.val / chunkBits + chunkCount * child.val) =
      chunkBits * chunkCount * child.val + position.val
  calc
    position.val % chunkBits +
          chunkBits *
            (position.val / chunkBits + chunkCount * child.val) =
        (position.val % chunkBits +
            chunkBits * (position.val / chunkBits)) +
          chunkBits * chunkCount * child.val := by
      ring
    _ = position.val +
          chunkBits * chunkCount * child.val := by
      rw [Nat.mod_add_div]
    _ = chunkBits * chunkCount * child.val + position.val := by
      omega

theorem lowOrderChunkIndex_eq_internal
    (payloadWidth fanIn : ℕ)
    (child : Fin fanIn) (position : Fin payloadWidth) :
    lowOrderChunkIndex payloadWidth fanIn child position =
      fanIn *
          PrimeGrouped.Logarithmic.chunkCount payloadWidth fanIn -
        1 -
        ((payloadChunkIndex payloadWidth fanIn position).val +
          PrimeGrouped.Logarithmic.chunkCount payloadWidth fanIn *
            child.val) := by
  simp [lowOrderChunkIndex, CombineTerm.basisCoordinateDigitIndex,
    groupedCoordinate, finProdFinEquiv]

theorem lowOrderBitInChunkIndex_eq_internal
    (payloadWidth fanIn : ℕ) (position : Fin payloadWidth) :
    lowOrderBitInChunkIndex payloadWidth fanIn position =
      PrimeGrouped.Logarithmic.chunkBits payloadWidth fanIn -
        1 -
        (position.val %
          PrimeGrouped.Logarithmic.chunkBits payloadWidth fanIn) :=
  rfl

theorem lowOrderBitIndex_eq_reversed_internal
    (payloadWidth fanIn : ℕ)
    (child : Fin fanIn) (position : Fin payloadWidth) :
    lowOrderBitIndex payloadWidth fanIn child position =
      (fanIn *
          PrimeGrouped.Logarithmic.chunkCount payloadWidth fanIn) *
          PrimeGrouped.Logarithmic.chunkBits payloadWidth fanIn -
        1 -
        (encodedBitPosition payloadWidth fanIn child position).val := by
  let chunkCount :=
    PrimeGrouped.Logarithmic.chunkCount payloadWidth fanIn
  let chunkBits :=
    PrimeGrouped.Logarithmic.chunkBits payloadWidth fanIn
  let chunk :=
    (payloadChunkIndex payloadWidth fanIn position).val
  let offset :=
    (payloadChunkOffset payloadWidth fanIn position).val
  let grouped := chunk + chunkCount * child.val
  let remainingChunks :=
    fanIn * chunkCount - 1 - grouped
  let remainingBits :=
    chunkBits - 1 - offset
  have hgrouped :
      grouped < fanIn * chunkCount := by
    exact
      (finProdFinEquiv
        (groupedCoordinate payloadWidth fanIn child position)).isLt
  have hoffset : offset < chunkBits :=
    (payloadChunkOffset payloadWidth fanIn position).isLt
  have hcount :
      fanIn * chunkCount =
        grouped + 1 + remainingChunks := by
    omega
  have hbits :
      chunkBits =
        offset + 1 + remainingBits := by
    omega
  rw [lowOrderBitIndex, lowOrderChunkIndex_eq_internal,
    lowOrderBitInChunkIndex_eq_internal,
    encodedBitPosition_val_internal]
  change
    chunkBits * remainingChunks + remainingBits =
      fanIn * chunkCount * chunkBits - 1 -
        (chunkBits * chunkCount * child.val + position.val)
  have hposition :
      position.val = chunkBits * chunk + offset := by
    change
      position.val =
        chunkBits *
            (position.val / chunkBits) +
          position.val % chunkBits
    exact (Nat.div_add_mod position.val chunkBits).symm
  rw [hposition]
  have hflat :
      chunkBits * chunkCount * child.val +
          (chunkBits * chunk + offset) =
        chunkBits * grouped + offset := by
    dsimp only [grouped]
    ring
  rw [hflat]
  have hwidth :
      fanIn * chunkCount * chunkBits =
        chunkBits * grouped + offset + 1 +
          (chunkBits * remainingChunks + remainingBits) := by
    calc
      fanIn * chunkCount * chunkBits =
          (grouped + 1 + remainingChunks) * chunkBits := by
        rw [← hcount]
      _ =
          chunkBits * grouped + chunkBits +
            chunkBits * remainingChunks := by
        ring
      _ =
          chunkBits * grouped +
              (offset + 1 + remainingBits) +
            chunkBits * remainingChunks := by
        rw [← hbits]
      _ =
          chunkBits * grouped + offset + 1 +
            (chunkBits * remainingChunks + remainingBits) := by
        ring
  omega

theorem lowOrderBitIndex_eq_internal
    (payloadWidth fanIn : ℕ)
    (child : Fin fanIn) (position : Fin payloadWidth) :
    lowOrderBitIndex payloadWidth fanIn child position =
      (fanIn *
          PrimeGrouped.Logarithmic.chunkCount payloadWidth fanIn) *
          PrimeGrouped.Logarithmic.chunkBits payloadWidth fanIn -
        1 -
        (PrimeGrouped.Logarithmic.chunkBits payloadWidth fanIn *
            PrimeGrouped.Logarithmic.chunkCount payloadWidth fanIn *
            child.val +
          position.val) := by
  rw [lowOrderBitIndex_eq_reversed_internal,
    encodedBitPosition_val_internal]

theorem assignmentBit_eq_decide_radixDigit_internal
    (payloadWidth fanIn code : ℕ)
    (child : Fin fanIn) (position : Fin payloadWidth) :
    assignmentBits payloadWidth fanIn code child position =
      decide
        (CombineTerm.radixDigit 2 code
          (lowOrderBitIndex payloadWidth fanIn child position) = 1) := by
  rw [assignmentBits_apply_internal]
  unfold assignmentChunks
    GroupedExtension.Evaluation.chunkAssignmentOfCode
    BooleanExtension.Evaluation.assignmentOfCode
  rw [toBits_get_eq_radixDigit]
  rw [lowOrderBitIndex_eq_reversed_internal]
  rfl

theorem assignmentBit_toNat_eq_radixDigit_internal
    (payloadWidth fanIn code : ℕ)
    (child : Fin fanIn) (position : Fin payloadWidth) :
    (assignmentBits payloadWidth fanIn code child position).toNat =
      CombineTerm.radixDigit 2 code
        (lowOrderBitIndex payloadWidth fanIn child position) := by
  rw [assignmentBit_eq_decide_radixDigit_internal]
  unfold CombineTerm.radixDigit
  obtain hzero | hone :=
    Nat.mod_two_eq_zero_or_one
      (code /
        2 ^ lowOrderBitIndex payloadWidth fanIn child position)
  · simp [hzero]
  · simp [hone]

theorem packedAssignmentValue_eq_internal
    (payloadWidth fanIn : ℕ)
    (combine :
      (Fin fanIn → Fin payloadWidth → Bool) →
        Fin payloadWidth → Bool)
    (outputChunk :
      Fin (PrimeGrouped.Logarithmic.chunkCount payloadWidth fanIn))
    (code : ℕ) :
    CombineTerm.packedAssignmentValue
        payloadWidth fanIn combine outputChunk code =
      PrimeGrouped.Logarithmic.chunkCodeNat
        (GroupedExtension.Layout.pack
          (chunkBits :=
            PrimeGrouped.Logarithmic.chunkBits payloadWidth fanIn)
          (combine (assignmentBits payloadWidth fanIn code))
          outputChunk) := by
  rfl

end Internal
end AssignmentCodeSemantics
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
