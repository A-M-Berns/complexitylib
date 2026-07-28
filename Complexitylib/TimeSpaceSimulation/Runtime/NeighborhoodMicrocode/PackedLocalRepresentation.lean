/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.PackedLocalRepresentation.Defs
import
Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.PackedLocalRepresentation.Internal

/-!
# Semantic representation of mutable packed local configurations
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace PackedLocalRepresentation

open NeighborhoodGraph
open TreeEval CookMertz

/-- The canonical packed constructor satisfies the mutable representation
predicate. -/
theorem encodeAbove_represents
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (blockLength : ℕ)
    (centers : TapeIndex workTapeCount → ℕ)
    (cfg : Cfg workTapeCount tm.Q)
    (suffix : ℕ) :
    Represents tm order blockLength centers cfg suffix
      (PackedLocalConfiguration.encodeAbove
        tm order blockLength centers cfg suffix) :=
  Internal.encodeAbove_represents_internal
    tm order blockLength centers cfg suffix

/-- A semantic packed-local representation determines its complete natural
word uniquely, including the suspended high-order suffix. -/
theorem Represents.eq_encodeAbove
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (blockLength : ℕ)
    (centers : TapeIndex workTapeCount → ℕ)
    (cfg : Cfg workTapeCount tm.Q)
    (suffix word : ℕ)
    (hrep :
      Represents tm order blockLength centers cfg suffix word) :
    word =
      PackedLocalConfiguration.encodeAbove
        tm order blockLength centers cfg suffix :=
  Internal.represents_eq_encodeAbove_internal
    tm order blockLength centers cfg suffix word hrep

/-- Replacing an in-prefix digit preserves the exact dropped suffix. -/
theorem drop_replaceAt
    {base count word index replacement : ℕ}
    (hbase : 0 < base)
    (hindex : index < count)
    (hreplacement : replacement < base) :
    PackedDigits.drop base count
        (NeighborhoodProgram.replaceAt
          base word index replacement) =
      PackedDigits.drop base count word :=
  Internal.drop_replaceAt_internal hbase hindex hreplacement

/-- A one-coordinate semantic digit update is represented by the matching
streamed packed-word replacement. -/
theorem replaceAt_represents
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (blockLength : ℕ)
    (centers : TapeIndex workTapeCount → ℕ)
    (cfg nextCfg : Cfg workTapeCount tm.Q)
    (suffix word index replacement : ℕ)
    (hrep :
      Represents tm order blockLength centers cfg suffix word)
    (hindex :
      index <
        PackedLocalConfiguration.digitCount
          workTapeCount blockLength)
    (hreplacement :
      replacement < PackedLocalConfiguration.radix tm)
    (hupdate :
      ∀ coordinate,
        coordinate <
            PackedLocalConfiguration.digitCount
              workTapeCount blockLength →
          PackedLocalConfiguration.configurationDigit
              tm order blockLength centers nextCfg coordinate =
            if coordinate = index then
              replacement
            else
              PackedLocalConfiguration.configurationDigit
                tm order blockLength centers cfg coordinate) :
    Represents tm order blockLength centers nextCfg suffix
      (NeighborhoodProgram.replaceAt
        (PackedLocalConfiguration.radix tm)
        word index replacement) :=
  Internal.replaceAt_represents_internal
    tm order blockLength centers cfg nextCfg suffix word
      index replacement hrep hindex hreplacement hupdate

/-- A represented word exposes the exact hardwired state digit. -/
theorem represents_state
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (blockLength : ℕ)
    (centers : TapeIndex workTapeCount → ℕ)
    (cfg : Cfg workTapeCount tm.Q)
    (suffix word : ℕ)
    (hrep :
      Represents tm order blockLength centers cfg suffix word) :
    PackedDigits.digit
        (PackedLocalConfiguration.radix tm) word 0 =
      CompactValueCodeSemantics.stateCode order cfg.state :=
  Internal.represents_state_internal
    tm order blockLength centers cfg suffix word hrep

/-- A represented word exposes every exact finite-window cell digit. -/
theorem represents_cell
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (centers : TapeIndex workTapeCount → ℕ)
    (cfg : Cfg workTapeCount tm.Q)
    (suffix word : ℕ)
    (hrep :
      Represents tm order blockLength centers cfg suffix word)
    (tape : TapeIndex workTapeCount)
    (localPosition : ℕ)
    (hlocal :
      localPosition <
        PackedLocalConfiguration.tapeSpan blockLength) :
    PackedDigits.digit
        (PackedLocalConfiguration.radix tm) word
        (PackedLocalConfiguration.cellIndex
          blockLength tape localPosition) =
      PackedLocalConfiguration.cellDigit
        cfg blockLength centers tape localPosition :=
  Internal.represents_cell_internal
    tm order blockLength hpositive centers cfg suffix word
      hrep tape localPosition hlocal

/-- Scanning marker digits in any represented word recovers the exact local
head coordinate. -/
theorem findHeadOffset_represents
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (centers : TapeIndex workTapeCount → ℕ)
    (cfg : Cfg workTapeCount tm.Q)
    (suffix word : ℕ)
    (hrep :
      Represents tm order blockLength centers cfg suffix word)
    (tape : TapeIndex workTapeCount)
    (hlower :
      PackedLocalConfiguration.windowStart
          blockLength (centers tape) ≤
        (tapeAt cfg tape).head)
    (hupper :
      (tapeAt cfg tape).head <
        PackedLocalConfiguration.windowStart
            blockLength (centers tape) +
          PackedLocalConfiguration.tapeSpan blockLength) :
    PackedLocalConfiguration.findHeadOffset
        tm blockLength tape word =
      PackedLocalConfiguration.localHead
        blockLength (centers tape) (tapeAt cfg tape).head :=
  Internal.findHeadOffset_represents_internal
    tm order blockLength hpositive centers cfg suffix word
      hrep tape hlower hupper

/-- Numeric compact output decoding is correct for every represented word
whose selected head lies in its finite window. -/
theorem outputBitFromWord_represents
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (centers : TapeIndex workTapeCount → ℕ)
    (cfg : Cfg workTapeCount tm.Q)
    (suffix word : ℕ)
    (hrep :
      Represents tm order blockLength centers cfg suffix word)
    (targetTape : TapeIndex workTapeCount)
    (targetSlot : Slot)
    (coordinate : ℕ)
    (hlower :
      PackedLocalConfiguration.windowStart
          blockLength (centers targetTape) ≤
        (tapeAt cfg targetTape).head)
    (hupper :
      (tapeAt cfg targetTape).head <
        PackedLocalConfiguration.windowStart
            blockLength (centers targetTape) +
          PackedLocalConfiguration.tapeSpan blockLength) :
    PackedLocalConfiguration.outputBitFromWord
        tm blockLength coordinate (centers targetTape)
          targetTape targetSlot word =
      CompactValueCodeSemantics.coordinateBit
        tm order blockLength coordinate
        (PackedLocalConfiguration.requestedContent
          cfg blockLength hpositive (centers targetTape)
            targetTape targetSlot) :=
  Internal.outputBitFromWord_represents_internal
    tm order blockLength hpositive centers cfg suffix word
      hrep targetTape targetSlot coordinate hlower hupper

/-- The output chunk packed from any represented word is the canonical
grouped encoding of its requested compact content. -/
theorem packedOutputChunk_represents
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (centers : TapeIndex workTapeCount → ℕ)
    (cfg : Cfg workTapeCount tm.Q)
    (suffix word : ℕ)
    (hrep :
      Represents tm order blockLength centers cfg suffix word)
    (targetTape : TapeIndex workTapeCount)
    (targetSlot : Slot)
    (outputChunk :
      Fin
        (PrimeGrouped.Logarithmic.chunkCount
          (NeighborhoodExecutableEvaluation.payloadWidth
            tm blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn
            workTapeCount)))
    (hlower :
      PackedLocalConfiguration.windowStart
          blockLength (centers targetTape) ≤
        (tapeAt cfg targetTape).head)
    (hupper :
      (tapeAt cfg targetTape).head <
        PackedLocalConfiguration.windowStart
            blockLength (centers targetTape) +
          PackedLocalConfiguration.tapeSpan blockLength) :
    PackedOutputChunkSemantics.packedOutputChunk
        tm blockLength (centers targetTape)
          targetTape targetSlot word outputChunk.val
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
            CompactValueCodeSemantics.coordinateBit
              tm order blockLength position.val
              (PackedLocalConfiguration.requestedContent
                cfg blockLength hpositive (centers targetTape)
                  targetTape targetSlot))
          outputChunk) :=
  Internal.packedOutputChunk_represents_internal
    tm order blockLength hpositive centers cfg suffix word
      hrep targetTape targetSlot outputChunk hlower hupper

/-- Any mutable word representing the final local assignment trace packs to
the exact semantic output chunk required by the combine factor. -/
theorem packedOutputChunk_assignmentFinal_represents
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
    (code suffix word : ℕ)
    (hrep :
      Represents tm order blockLength
        (Guess.Consistency.guessedCenters guess interval.val)
        (GuessedLocalEvaluation.localTraceAtCenters
          tm blockLength
          (Guess.Consistency.guessedCenters guess interval.val)
          (LocalAssignmentSemantics.assignmentInputs
            tm order blockLength hpositive code))
        suffix word) :
    PackedOutputChunkSemantics.packedOutputChunk
        tm blockLength
          (Guess.Consistency.guessedCenters
            guess interval.val targetTape)
          targetTape targetSlot word outputChunk.val
          (PrimeGrouped.Logarithmic.chunkBits
            (NeighborhoodExecutableEvaluation.payloadWidth
              tm blockLength)
            (NeighborhoodExecutableEvaluation.graphFanIn
              workTapeCount)) =
      LocalAssignmentSemantics.outputChunkValue
        tm order blockLength hpositive guess interval
          targetTape targetSlot outputChunk code :=
  Internal.packedOutputChunk_assignmentFinal_represents_internal
    tm order blockLength hpositive guess interval
      targetTape targetSlot outputChunk code suffix word hrep

end PackedLocalRepresentation
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
