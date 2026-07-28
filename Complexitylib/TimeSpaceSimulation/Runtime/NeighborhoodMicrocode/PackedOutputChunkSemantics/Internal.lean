/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.PackedOutputChunkSemantics.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.PackedLocalConfiguration

/-!
# Packed output chunks from a finite local configuration -- proofs
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace PackedOutputChunkSemantics
namespace Internal

open NeighborhoodGraph
open TreeEval CookMertz

theorem bitPosition_zero_internal
    (chunkCursor chunkBits : ℕ) :
    bitPosition chunkCursor chunkBits 0 =
      chunkStart chunkCursor chunkBits := by
  simp [bitPosition]

theorem bitPosition_succ_internal
    (chunkCursor chunkBits offset : ℕ) :
    bitPosition chunkCursor chunkBits (offset + 1) =
      bitPosition chunkCursor chunkBits offset + 1 := by
  simp [bitPosition, Nat.add_assoc]

theorem bitPosition_lt_chunkEnd_internal
    (chunkCursor chunkBits offset : ℕ)
    (hoffset : offset < chunkBits) :
    bitPosition chunkCursor chunkBits offset <
      chunkStart (chunkCursor + 1) chunkBits := by
  unfold bitPosition chunkStart
  nlinarith

theorem bitPosition_lt_capacity_internal
    (chunkCount chunkBits : ℕ)
    (chunk : Fin chunkCount)
    (offset : Fin chunkBits) :
    bitPosition chunk.val chunkBits offset.val <
      chunkCount * chunkBits := by
  unfold bitPosition chunkStart
  nlinarith [chunk.isLt, offset.isLt]

theorem bitPosition_payload_or_padding_internal
    (tm : TM workTapeCount)
    (blockLength chunkCursor chunkBits offset : ℕ) :
    bitPosition chunkCursor chunkBits offset <
        NeighborhoodExecutableEvaluation.payloadWidth
          tm blockLength ∨
      NeighborhoodExecutableEvaluation.payloadWidth
          tm blockLength ≤
        bitPosition chunkCursor chunkBits offset :=
  Nat.lt_or_ge _ _

theorem boundedOutputBitFromWord_eq_internal
    (tm : TM workTapeCount)
    (blockLength center : ℕ)
    (targetTape : TapeIndex workTapeCount)
    (targetSlot : Slot)
    (word coordinate : ℕ)
    (hcoordinate :
      coordinate <
        NeighborhoodExecutableEvaluation.payloadWidth
          tm blockLength) :
    boundedOutputBitFromWord tm blockLength center
        targetTape targetSlot word coordinate =
      PackedLocalConfiguration.outputBitFromWord
        tm blockLength coordinate center targetTape targetSlot word := by
  simp [boundedOutputBitFromWord, hcoordinate]

theorem boundedOutputBitFromWord_eq_false_internal
    (tm : TM workTapeCount)
    (blockLength center : ℕ)
    (targetTape : TapeIndex workTapeCount)
    (targetSlot : Slot)
    (word coordinate : ℕ)
    (hcoordinate :
      NeighborhoodExecutableEvaluation.payloadWidth
          tm blockLength ≤ coordinate) :
    boundedOutputBitFromWord tm blockLength center
        targetTape targetSlot word coordinate = false := by
  simp [boundedOutputBitFromWord, Nat.not_lt.mpr hcoordinate]

private theorem list_ofFn_succ
    {α : Type*} (function : Fin (count + 1) → α) :
    List.ofFn function =
      function 0 :: List.ofFn (fun index : Fin count =>
        function index.succ) := by
  rw [List.ofFn_succ]

theorem forwardBits_eq_internal
    (bits : ℕ → Bool) (start count accumulator : ℕ) :
    forwardBits
        (fun index =>
          if bits index then 1 else 0)
        start count accumulator =
      accumulator * 2 ^ count +
        Nat.fromBits
          (List.ofFn fun index : Fin count =>
            bits (start + index.val)) := by
  induction count generalizing start accumulator with
  | zero =>
      simp [forwardBits, Nat.fromBits]
  | succ count ih =>
      rw [forwardBits, ih]
      rw [list_ofFn_succ]
      simp only [Nat.fromBits, List.length_ofFn]
      have htail :
          (List.ofFn fun index : Fin count =>
            bits (start + index.succ.val)) =
          List.ofFn
            (fun index : Fin count =>
              bits (start + 1 + index.val)) := by
        apply congrArg List.ofFn
        funext index
        apply congrArg bits
        rw [Fin.val_succ]
        omega
      rw [htail]
      simp only [Fin.val_zero, Nat.add_zero, pow_succ]
      ring_nf

theorem packedOutputChunk_eq_chunkCodeNat_internal
    (tm : TM workTapeCount)
    (blockLength center : ℕ)
    (targetTape : TapeIndex workTapeCount)
    (targetSlot : Slot)
    (word : ℕ)
    (outputChunk :
      Fin
        (PrimeGrouped.Logarithmic.chunkCount
          (NeighborhoodExecutableEvaluation.payloadWidth
            tm blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn
            workTapeCount))) :
    packedOutputChunk tm blockLength center targetTape targetSlot
        word outputChunk.val
        (PrimeGrouped.Logarithmic.chunkBits
          (NeighborhoodExecutableEvaluation.payloadWidth
            tm blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn
            workTapeCount)) =
      PrimeGrouped.Logarithmic.chunkCodeNat
        (GroupedExtension.Layout.pack
          (b :=
            NeighborhoodExecutableEvaluation.payloadWidth
              tm blockLength)
          (chunkBits :=
            PrimeGrouped.Logarithmic.chunkBits
              (NeighborhoodExecutableEvaluation.payloadWidth
                tm blockLength)
              (NeighborhoodExecutableEvaluation.graphFanIn
                workTapeCount))
          (fun position =>
            PackedLocalConfiguration.outputBitFromWord
              tm blockLength position.val center
                targetTape targetSlot word)
          outputChunk) := by
  let payloadWidth :=
    NeighborhoodExecutableEvaluation.payloadWidth tm blockLength
  let fanIn :=
    NeighborhoodExecutableEvaluation.graphFanIn workTapeCount
  let chunkBits :=
    PrimeGrouped.Logarithmic.chunkBits payloadWidth fanIn
  unfold packedOutputChunk boundedOutputBitValue
  rw [forwardBits_eq_internal]
  simp only [zero_mul, zero_add,
    PrimeGrouped.Logarithmic.chunkCodeNat]
  apply congrArg Nat.fromBits
  apply congrArg List.ofFn
  funext offset
  unfold GroupedExtension.Layout.pack
  change
    boundedOutputBitFromWord tm blockLength center targetTape
        targetSlot word
          (outputChunk.val * chunkBits + offset.val) =
      _
  split <;> rename_i hcoordinate
  · have hcoordinate' :
        outputChunk.val * chunkBits + offset.val <
          payloadWidth := by
      simpa [chunkBits, payloadWidth, fanIn] using hcoordinate
    rw [boundedOutputBitFromWord_eq_internal
      tm blockLength center targetTape targetSlot word
        (outputChunk.val * chunkBits + offset.val) hcoordinate']
  · have hcoordinate' :
        payloadWidth ≤
          outputChunk.val * chunkBits + offset.val := by
      apply Nat.le_of_not_gt
      simpa [chunkBits, payloadWidth, fanIn] using hcoordinate
    rw [boundedOutputBitFromWord_eq_false_internal
      tm blockLength center targetTape targetSlot word
        (outputChunk.val * chunkBits + offset.val) hcoordinate']

theorem packedOutputChunk_assignmentFinalWord_internal
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (guess : Guess.CenterGuess workTapeCount horizon)
    (interval : Fin horizon)
    (targetTape : TapeIndex workTapeCount)
    (targetSlot : Slot)
    (outputChunk :
      Fin
        (PrimeGrouped.Logarithmic.chunkCount
          (NeighborhoodExecutableEvaluation.payloadWidth
            tm blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn
            workTapeCount)))
    (code suffix : ℕ) :
    packedOutputChunk tm blockLength
        (Guess.Consistency.guessedCenters
          guess interval.val targetTape)
        targetTape targetSlot
        (PackedLocalConfiguration.assignmentFinalWord
          tm order blockLength hpositive guess interval code suffix)
        outputChunk.val
        (PrimeGrouped.Logarithmic.chunkBits
          (NeighborhoodExecutableEvaluation.payloadWidth
            tm blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn
            workTapeCount)) =
      LocalAssignmentSemantics.outputChunkValue
        tm order blockLength hpositive guess interval
          targetTape targetSlot outputChunk code := by
  rw [packedOutputChunk_eq_chunkCodeNat_internal]
  unfold LocalAssignmentSemantics.outputChunkValue
  apply congrArg PrimeGrouped.Logarithmic.chunkCodeNat
  funext offset
  unfold GroupedExtension.Layout.pack
  split <;> rename_i hcoordinate
  · exact
      PackedLocalConfiguration.outputBit_assignmentFinalWord
        tm order blockLength hpositive guess interval
          targetTape targetSlot code suffix
          (outputChunk.val *
              PrimeGrouped.Logarithmic.chunkBits
                (NeighborhoodExecutableEvaluation.payloadWidth
                  tm blockLength)
                (NeighborhoodExecutableEvaluation.graphFanIn
                  workTapeCount) +
            offset.val)
  · rfl

end Internal
end PackedOutputChunkSemantics
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
