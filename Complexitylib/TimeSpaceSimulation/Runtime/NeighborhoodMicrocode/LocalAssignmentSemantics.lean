/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.LocalAssignmentSemantics.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.LocalAssignmentSemantics.Internal

/-!
# Local-transition semantics of one streamed assignment
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace LocalAssignmentSemantics

open NeighborhoodExecutableEvaluation
open NeighborhoodGraph
open TreeEval CookMertz

/-- Applying the guessed-center Boolean callback to the bits of one streamed
assignment is exactly the arithmetic coordinate of its decoded local result.
-/
theorem booleanCombineAtGuess_assignment
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
        targetTape targetSlot code position.val :=
  Internal.booleanCombineAtGuess_assignment_internal
    tm order blockLength hpositive guess interval targetTape targetSlot
    code position

/-- The high-order packed-factor specification reduces to the concrete
numeric output chunk of one decoded local transition. -/
theorem packedAssignmentValue_eq_outputChunkValue
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
        targetTape targetSlot outputChunk code :=
  Internal.packedAssignmentValue_eq_outputChunkValue_internal
    tm order blockLength hpositive guess interval targetTape targetSlot
    outputChunk code

end LocalAssignmentSemantics
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
