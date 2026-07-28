/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.NeighborhoodExecutableEvaluation.Defs
import
  Complexitylib.TimeSpaceSimulation.NeighborhoodGraph.Guess.Consistency.Defs

/-!
# Local neighborhood evaluation from streamed guessed centers

The certificate-level neighborhood callback obtains its interval centers
from the source machine's actual run. A uniform trial command instead has
the current centers in its streamed movement guess. This module states the
same local transition with those centers supplied explicitly.

No actual trajectory occurs in the executable definitions below. Proofs in
the surface layer identify them with the existing callback whenever the
relevant guessed prefix is correct.
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace GuessedLocalEvaluation

open NeighborhoodGraph
open NeighborhoodGraph.Guess

/-- Complete local configuration after one interval from explicit center
metadata and compact predecessor contents. This shared endpoint drives both
the Boolean computation callback and the center-consistency check. -/
def localTraceAtCenters
    (tm : TM workTapeCount) (blockLength : ℕ)
    (centers : TapeIndex workTapeCount → ℕ)
    (inputs :
      PredecessorIndex workTapeCount →
        NeighborhoodContent.Content blockLength tm.Q) :
    Cfg workTapeCount tm.Q :=
  tm.toNTM.trace blockLength (fun _ => false)
    (Consistency.localStartCfg tm blockLength centers inputs)

/-- Final block containing one named head after the shared local trace. -/
def endCenterAtCenters
    (tm : TM workTapeCount) (blockLength : ℕ)
    (centers : TapeIndex workTapeCount → ℕ)
    (inputs :
      PredecessorIndex workTapeCount →
        NeighborhoodContent.Content blockLength tm.Q)
    (tape : TapeIndex workTapeCount) : ℕ :=
  blockIndex blockLength
    (tapeAt
      (localTraceAtCenters tm blockLength centers inputs) tape).head

/-- Run one local interval from explicit center metadata and return the
requested compact tape block. -/
def localNodeFunctionAtCenters
    (tm : TM workTapeCount)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (centers : TapeIndex workTapeCount → ℕ)
    (targetTape : TapeIndex workTapeCount) (targetSlot : Slot)
    (inputs :
      PredecessorIndex workTapeCount →
        NeighborhoodContent.Content blockLength tm.Q) :
    NeighborhoodContent.Content blockLength tm.Q :=
  let final := localTraceAtCenters tm blockLength centers inputs
  { state := final.state
    headRemainder :=
      ⟨(tapeAt final targetTape).head % blockLength,
        Nat.mod_lt _ hpositive⟩
    cells :=
      blockContents (tapeAt final targetTape) blockLength
        (neighborBlock (centers targetTape) targetSlot) }

/-- Boolean local transition whose absolute centers are explicit runtime
data rather than projections of the source machine's actual run. -/
def booleanCombineAtCenters
    (tm : TM workTapeCount)
    (blockLength : ℕ)
    (encoding :
      NeighborhoodExecutableEvaluation.FiniteEncoding tm blockLength)
    (hpositive : 0 < blockLength)
    (centers : TapeIndex workTapeCount → ℕ)
    (targetTape : TapeIndex workTapeCount) (targetSlot : Slot)
    (children :
      Fin (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount) →
        Fin
          (NeighborhoodExecutableEvaluation.payloadWidth
            tm blockLength) →
          Bool) :
    Fin
        (NeighborhoodExecutableEvaluation.payloadWidth tm blockLength) →
      Bool :=
  NeighborhoodExecutableEvaluation.encodeBits encoding
    (localNodeFunctionAtCenters tm blockLength hpositive centers
      targetTape targetSlot fun index =>
        NeighborhoodExecutableEvaluation.decodeBits
          encoding tm.qstart hpositive
          (children
            (predecessorIndexEquiv workTapeCount index)))

/-- Local Boolean transition at the centers decoded from one movement
guess and interval cursor. -/
def booleanCombineAtGuess
    (tm : TM workTapeCount)
    (blockLength : ℕ)
    (encoding :
      NeighborhoodExecutableEvaluation.FiniteEncoding tm blockLength)
    (hpositive : 0 < blockLength)
    (guess : CenterGuess workTapeCount horizon)
    (interval : Fin horizon)
    (targetTape : TapeIndex workTapeCount) (targetSlot : Slot) :=
  booleanCombineAtCenters tm blockLength encoding hpositive
    (Consistency.guessedCenters guess interval.val)
    targetTape targetSlot

/-- Final center computed at one movement guess and interval cursor. -/
def endCenterAtGuess
    (tm : TM workTapeCount) (blockLength : ℕ)
    (guess : CenterGuess workTapeCount horizon)
    (interval : Fin horizon)
    (inputs :
      PredecessorIndex workTapeCount →
        NeighborhoodContent.Content blockLength tm.Q)
    (tape : TapeIndex workTapeCount) : ℕ :=
  endCenterAtCenters tm blockLength
    (Consistency.guessedCenters guess interval.val) inputs tape

/-- Natural-residue grouped callback at explicit runtime centers. -/
def combineResiduesAtCenters
    (tm : TM workTapeCount)
    (blockLength : ℕ)
    (encoding :
      NeighborhoodExecutableEvaluation.FiniteEncoding tm blockLength)
    (hpositive : 0 < blockLength)
    (centers : TapeIndex workTapeCount → ℕ)
    (targetTape : TapeIndex workTapeCount) (targetSlot : Slot)
    (children :
      Fin (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount) →
        NeighborhoodExecutableEvaluation.ResidueValue tm blockLength) :
    NeighborhoodExecutableEvaluation.ResidueValue tm blockLength :=
  NeighborhoodExecutableEvaluation.Residue.evaluateNode
    (NeighborhoodExecutableEvaluation.payloadWidth tm blockLength)
    (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount)
    (booleanCombineAtCenters tm blockLength encoding hpositive centers
      targetTape targetSlot)
    children

/-- Natural-residue grouped callback at the movement guess's current
centers. -/
def combineResiduesAtGuess
    (tm : TM workTapeCount)
    (blockLength : ℕ)
    (encoding :
      NeighborhoodExecutableEvaluation.FiniteEncoding tm blockLength)
    (hpositive : 0 < blockLength)
    (guess : CenterGuess workTapeCount horizon)
    (interval : Fin horizon)
    (targetTape : TapeIndex workTapeCount) (targetSlot : Slot)
    (children :
      Fin (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount) →
        NeighborhoodExecutableEvaluation.ResidueValue tm blockLength) :
    NeighborhoodExecutableEvaluation.ResidueValue tm blockLength :=
  combineResiduesAtCenters tm blockLength encoding hpositive
    (Consistency.guessedCenters guess interval.val)
    targetTape targetSlot children

end GuessedLocalEvaluation
end Runtime
end TimeSpaceSimulation
end Complexity
