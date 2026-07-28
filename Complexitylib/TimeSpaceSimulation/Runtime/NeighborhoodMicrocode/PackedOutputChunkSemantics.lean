/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.PackedOutputChunkSemantics.Defs
import
Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.PackedOutputChunkSemantics.Internal

/-!
# Packed output chunks from a finite local configuration

This surface exposes the exact grouped-coordinate orientation and the pure
big-endian fold that a later fixed-register RAM loop will implement.
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace PackedOutputChunkSemantics

open NeighborhoodGraph
open TreeEval CookMertz

/-- Offset zero is the first coordinate of the selected runtime chunk. -/
theorem bitPosition_zero
    (chunkCursor chunkBits : ℕ) :
    bitPosition chunkCursor chunkBits 0 =
      chunkStart chunkCursor chunkBits :=
  Internal.bitPosition_zero_internal chunkCursor chunkBits

/-- Advancing the within-chunk offset advances the compact coordinate. -/
theorem bitPosition_succ
    (chunkCursor chunkBits offset : ℕ) :
    bitPosition chunkCursor chunkBits (offset + 1) =
      bitPosition chunkCursor chunkBits offset + 1 :=
  Internal.bitPosition_succ_internal chunkCursor chunkBits offset

/-- Every valid within-chunk offset lies before the next chunk boundary. -/
theorem bitPosition_lt_chunkEnd
    (chunkCursor chunkBits offset : ℕ)
    (hoffset : offset < chunkBits) :
    bitPosition chunkCursor chunkBits offset <
      chunkStart (chunkCursor + 1) chunkBits :=
  Internal.bitPosition_lt_chunkEnd_internal
    chunkCursor chunkBits offset hoffset

/-- A valid grouped chunk and bit offset lie inside total layout capacity. -/
theorem bitPosition_lt_capacity
    (chunkCount chunkBits : ℕ)
    (chunk : Fin chunkCount)
    (offset : Fin chunkBits) :
    bitPosition chunk.val chunkBits offset.val <
      chunkCount * chunkBits :=
  Internal.bitPosition_lt_capacity_internal
    chunkCount chunkBits chunk offset

/-- Every runtime bit coordinate is either meaningful payload or padding. -/
theorem bitPosition_payload_or_padding
    (tm : TM workTapeCount)
    (blockLength chunkCursor chunkBits offset : ℕ) :
    bitPosition chunkCursor chunkBits offset <
        NeighborhoodExecutableEvaluation.payloadWidth
          tm blockLength ∨
      NeighborhoodExecutableEvaluation.payloadWidth
          tm blockLength ≤
        bitPosition chunkCursor chunkBits offset :=
  Internal.bitPosition_payload_or_padding_internal
    tm blockLength chunkCursor chunkBits offset

/-- Inside the payload boundary, bounded decoding is ordinary word
decoding. -/
theorem boundedOutputBitFromWord_eq
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
        tm blockLength coordinate center targetTape targetSlot word :=
  Internal.boundedOutputBitFromWord_eq_internal
    tm blockLength center targetTape targetSlot word coordinate
      hcoordinate

/-- Past the payload boundary, grouped output decoding supplies zero
padding. -/
theorem boundedOutputBitFromWord_eq_false
    (tm : TM workTapeCount)
    (blockLength center : ℕ)
    (targetTape : TapeIndex workTapeCount)
    (targetSlot : Slot)
    (word coordinate : ℕ)
    (hcoordinate :
      NeighborhoodExecutableEvaluation.payloadWidth
          tm blockLength ≤ coordinate) :
    boundedOutputBitFromWord tm blockLength center
        targetTape targetSlot word coordinate = false :=
  Internal.boundedOutputBitFromWord_eq_false_internal
    tm blockLength center targetTape targetSlot word coordinate
      hcoordinate

/-- The recursive big-endian fold is exactly fixed-width binary decoding,
with an arbitrary incoming accumulator as a high prefix. -/
theorem forwardBits_eq
    (bits : ℕ → Bool) (start count accumulator : ℕ) :
    forwardBits
        (fun index =>
          if bits index then 1 else 0)
        start count accumulator =
      accumulator * 2 ^ count +
        Nat.fromBits
          (List.ofFn fun index : Fin count =>
            bits (start + index.val)) :=
  Internal.forwardBits_eq_internal bits start count accumulator

/-- The natural packed from a runtime chunk cursor uses exactly the
canonical grouped-layout orientation. -/
theorem packedOutputChunk_eq_chunkCodeNat
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
          outputChunk) :=
  Internal.packedOutputChunk_eq_chunkCodeNat_internal
    tm blockLength center targetTape targetSlot word outputChunk

/-- Packing the final local-trace word gives exactly the semantic grouped
output chunk required by the Cook--Mertz combine factor. -/
theorem packedOutputChunk_assignmentFinalWord
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
          targetTape targetSlot outputChunk code :=
  Internal.packedOutputChunk_assignmentFinalWord_internal
    tm order blockLength hpositive guess interval
      targetTape targetSlot outputChunk code suffix

end PackedOutputChunkSemantics
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
