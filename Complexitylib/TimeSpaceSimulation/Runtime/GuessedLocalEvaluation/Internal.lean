/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.GuessedLocalEvaluation.Defs

/-!
# Local neighborhood evaluation from streamed guessed centers -- proofs
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace GuessedLocalEvaluation
namespace Internal

open NeighborhoodGraph
open NeighborhoodGraph.Guess

theorem endCenterAtCenters_eq_internal
    (tm : TM workTapeCount) (blockLength : ℕ)
    (centers : TapeIndex workTapeCount → ℕ)
    (inputs :
      PredecessorIndex workTapeCount →
        NeighborhoodContent.Content blockLength tm.Q)
    (tape : TapeIndex workTapeCount) :
    endCenterAtCenters tm blockLength centers inputs tape =
      Consistency.localEndCenter
        tm blockLength centers inputs tape := by
  rfl

theorem endCenterAtGuess_eq_internal
    (tm : TM workTapeCount) (blockLength : ℕ)
    (guess : CenterGuess workTapeCount horizon)
    (interval : Fin horizon)
    (inputs :
      PredecessorIndex workTapeCount →
        NeighborhoodContent.Content blockLength tm.Q)
    (tape : TapeIndex workTapeCount) :
    endCenterAtGuess tm blockLength guess interval inputs tape =
      Consistency.localEndCenter tm blockLength
        (Consistency.guessedCenters guess interval.val) inputs tape := by
  rfl

theorem localNodeFunctionAtCenters_eq_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength timeBlock : ℕ) (hpositive : 0 < blockLength)
    (centers : TapeIndex workTapeCount → ℕ)
    (hcenters :
      centers =
        NeighborhoodGraph.centerBlock tm x blockLength timeBlock)
    (targetTape : TapeIndex workTapeCount) (targetSlot : Slot)
    (inputs :
      PredecessorIndex workTapeCount →
        NeighborhoodContent.Content blockLength tm.Q) :
    localNodeFunctionAtCenters tm blockLength hpositive centers
        targetTape targetSlot inputs =
      NeighborhoodContent.localNodeFunction
        tm x blockLength hpositive timeBlock targetTape targetSlot inputs := by
  subst centers
  rfl

theorem booleanCombineAtCenters_eq_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength timeBlock : ℕ)
    (encoding :
      NeighborhoodExecutableEvaluation.FiniteEncoding tm blockLength)
    (hpositive : 0 < blockLength)
    (centers : TapeIndex workTapeCount → ℕ)
    (hcenters :
      centers =
        NeighborhoodGraph.centerBlock tm x blockLength timeBlock)
    (targetTape : TapeIndex workTapeCount) (targetSlot : Slot) :
    booleanCombineAtCenters tm blockLength encoding hpositive centers
        targetTape targetSlot =
      NeighborhoodExecutableEvaluation.booleanCombine
        tm x blockLength encoding hpositive targetTape targetSlot
          timeBlock := by
  subst centers
  rfl

theorem guessedCenters_eq_actual_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (guess : CenterGuess workTapeCount horizon)
    (interval : Fin horizon)
    (hcenters :
      ∀ tape : TapeIndex workTapeCount,
        guess.derivedCenter tape interval.val =
          some
            (NeighborhoodGraph.centerBlock
              tm x blockLength interval.val tape)) :
    Consistency.guessedCenters guess interval.val =
      NeighborhoodGraph.centerBlock
        tm x blockLength interval.val := by
  funext tape
  simp [Consistency.guessedCenters, hcenters tape]

theorem booleanCombineAtGuess_eq_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ)
    (encoding :
      NeighborhoodExecutableEvaluation.FiniteEncoding tm blockLength)
    (hpositive : 0 < blockLength)
    (guess : CenterGuess workTapeCount horizon)
    (interval : Fin horizon)
    (hcenters :
      ∀ tape : TapeIndex workTapeCount,
        guess.derivedCenter tape interval.val =
          some
            (NeighborhoodGraph.centerBlock
              tm x blockLength interval.val tape))
    (targetTape : TapeIndex workTapeCount) (targetSlot : Slot) :
    booleanCombineAtGuess tm blockLength encoding hpositive
        guess interval targetTape targetSlot =
      NeighborhoodExecutableEvaluation.booleanCombine
        tm x blockLength encoding hpositive targetTape targetSlot
          interval.val := by
  unfold booleanCombineAtGuess
  apply booleanCombineAtCenters_eq_internal
  exact guessedCenters_eq_actual_internal
    tm x blockLength guess interval hcenters

theorem combineResiduesAtCenters_eq_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength timeBlock : ℕ)
    (encoding :
      NeighborhoodExecutableEvaluation.FiniteEncoding tm blockLength)
    (hpositive : 0 < blockLength)
    (centers : TapeIndex workTapeCount → ℕ)
    (hcenters :
      centers =
        NeighborhoodGraph.centerBlock tm x blockLength timeBlock)
    (targetTape : TapeIndex workTapeCount) (targetSlot : Slot)
    (children :
      Fin (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount) →
        NeighborhoodExecutableEvaluation.ResidueValue tm blockLength) :
    combineResiduesAtCenters tm blockLength encoding hpositive centers
        targetTape targetSlot children =
      NeighborhoodExecutableEvaluation.combineResidues
        tm x blockLength encoding hpositive targetTape targetSlot
          timeBlock children := by
  subst centers
  rfl

theorem combineResiduesAtGuess_eq_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ)
    (encoding :
      NeighborhoodExecutableEvaluation.FiniteEncoding tm blockLength)
    (hpositive : 0 < blockLength)
    (guess : CenterGuess workTapeCount horizon)
    (interval : Fin horizon)
    (hcenters :
      ∀ tape : TapeIndex workTapeCount,
        guess.derivedCenter tape interval.val =
          some
            (NeighborhoodGraph.centerBlock
              tm x blockLength interval.val tape))
    (targetTape : TapeIndex workTapeCount) (targetSlot : Slot)
    (children :
      Fin (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount) →
        NeighborhoodExecutableEvaluation.ResidueValue tm blockLength) :
    combineResiduesAtGuess tm blockLength encoding hpositive
        guess interval targetTape targetSlot children =
      NeighborhoodExecutableEvaluation.combineResidues
        tm x blockLength encoding hpositive targetTape targetSlot
          interval.val children := by
  unfold combineResiduesAtGuess
  apply combineResiduesAtCenters_eq_internal
  exact guessedCenters_eq_actual_internal
    tm x blockLength guess interval hcenters

end Internal
end GuessedLocalEvaluation
end Runtime
end TimeSpaceSimulation
end Complexity
