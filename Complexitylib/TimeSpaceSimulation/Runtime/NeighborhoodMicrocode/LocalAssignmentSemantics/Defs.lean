/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.CompactValueCodeSemantics.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.GuessedLocalEvaluation.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.AssignmentCodeSemantics.Defs

/-!
# Local-transition semantics of one streamed assignment

One outer Cook--Mertz range index encodes every Boolean child payload. This
module decodes those bits into compact predecessor contents, runs the genuine
length-`blockLength` local transition at the streamed guessed centers, and
states its output through the explicit numeric compact-coordinate layout.

The definitions are the pure target for the fixed-register packed local
simulator. No actual center trajectory occurs here.
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace LocalAssignmentSemantics

open NeighborhoodExecutableEvaluation
open NeighborhoodGraph
open TreeEval CookMertz

/-- Compact predecessor vector decoded from one complete assignment code. -/
def assignmentInputs
    (tm : TM workTapeCount)
    (order : FiniteEncoding.StateOrder tm)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (code : ℕ) :
    PredecessorIndex workTapeCount →
      NeighborhoodContent.Content blockLength tm.Q :=
  fun index =>
    decodeBits (FiniteEncoding.ofStateOrder order blockLength)
      tm.qstart hpositive
      (AssignmentCodeSemantics.assignmentBits
        (payloadWidth tm blockLength)
        (graphFanIn workTapeCount) code
        (predecessorIndexEquiv workTapeCount index))

/-- Compact result of the local transition on one decoded assignment. -/
def assignmentResult
    (tm : TM workTapeCount)
    (order : FiniteEncoding.StateOrder tm)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (guess : Guess.CenterGuess workTapeCount horizon)
    (interval : Fin horizon)
    (targetTape : TapeIndex workTapeCount)
    (targetSlot : Slot)
    (code : ℕ) :
    NeighborhoodContent.Content blockLength tm.Q :=
  GuessedLocalEvaluation.localNodeFunctionAtCenters
    tm blockLength hpositive
    (Guess.Consistency.guessedCenters guess interval.val)
    targetTape targetSlot
    (assignmentInputs tm order blockLength hpositive code)

/-- Total natural-indexed output bit of one decoded local transition. -/
def outputBit
    (tm : TM workTapeCount)
    (order : FiniteEncoding.StateOrder tm)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (guess : Guess.CenterGuess workTapeCount horizon)
    (interval : Fin horizon)
    (targetTape : TapeIndex workTapeCount)
    (targetSlot : Slot)
    (code coordinate : ℕ) : Bool :=
  CompactValueCodeSemantics.coordinateBit tm order blockLength coordinate
    (assignmentResult tm order blockLength hpositive guess interval
      targetTape targetSlot code)

/-- Numeric code of one grouped output chunk of the decoded local result. -/
def outputChunkValue
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
    (code : ℕ) : ℕ :=
  PrimeGrouped.Logarithmic.chunkCodeNat
    (GroupedExtension.Layout.pack
      (b := payloadWidth tm blockLength)
      (chunkBits :=
        PrimeGrouped.Logarithmic.chunkBits
          (payloadWidth tm blockLength)
          (graphFanIn workTapeCount))
      (fun position =>
        outputBit tm order blockLength hpositive guess interval
          targetTape targetSlot code position.val)
      outputChunk)

end LocalAssignmentSemantics
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
