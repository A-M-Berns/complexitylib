/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.CompactValueCodeSemantics
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.LocalAssignmentSemantics.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.AssignmentCodeSemantics

/-!
# Local-transition semantics of one streamed assignment -- proofs
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace LocalAssignmentSemantics
namespace Internal

open NeighborhoodExecutableEvaluation
open NeighborhoodGraph
open TreeEval CookMertz

theorem booleanCombineAtGuess_assignment_internal
    (tm : TM workTapeCount)
    (order : FiniteEncoding.StateOrder tm)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (guess : Guess.CenterGuess workTapeCount horizon)
    (interval : Fin horizon)
    (targetTape : TapeIndex workTapeCount)
    (targetSlot : Slot)
    (code : ℕ)
    (position : Fin (payloadWidth tm blockLength)) :
    GuessedLocalEvaluation.booleanCombineAtGuess
        tm blockLength (FiniteEncoding.ofStateOrder order blockLength)
        hpositive guess interval targetTape targetSlot
        (AssignmentCodeSemantics.assignmentBits
          (payloadWidth tm blockLength)
          (graphFanIn workTapeCount) code)
        position =
      outputBit tm order blockLength hpositive guess interval
        targetTape targetSlot code position.val := by
  apply CompactValueCodeSemantics.encodeBits_eq_coordinateBit

theorem packedAssignmentValue_eq_outputChunkValue_internal
    (tm : TM workTapeCount)
    (order : FiniteEncoding.StateOrder tm)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (guess : Guess.CenterGuess workTapeCount horizon)
    (interval : Fin horizon)
    (targetTape : TapeIndex workTapeCount)
    (targetSlot : Slot)
    (outputChunk :
      Fin
        (PrimeGrouped.Logarithmic.chunkCount
          (payloadWidth tm blockLength)
          (graphFanIn workTapeCount)))
    (code : ℕ) :
    CombineTerm.packedAssignmentValue
        (payloadWidth tm blockLength)
        (graphFanIn workTapeCount)
        (GuessedLocalEvaluation.booleanCombineAtGuess
          tm blockLength (FiniteEncoding.ofStateOrder order blockLength)
          hpositive guess interval targetTape targetSlot)
        outputChunk code =
      outputChunkValue tm order blockLength hpositive guess interval
        targetTape targetSlot outputChunk code := by
  rw [AssignmentCodeSemantics.packedAssignmentValue_eq]
  unfold outputChunkValue
  congr 2
  funext offset
  exact booleanCombineAtGuess_assignment_internal
    tm order blockLength hpositive guess interval targetTape targetSlot
    code offset

end Internal
end LocalAssignmentSemantics
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
