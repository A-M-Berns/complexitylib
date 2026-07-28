/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.GuessedLocalEvaluation.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.GuessedLocalEvaluation.Internal

/-!
# Local neighborhood evaluation from streamed guessed centers

These theorems identify the runtime-center callback with the original
certificate callback on every prefix whose decoded centers are correct.
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace GuessedLocalEvaluation

open NeighborhoodGraph
open NeighborhoodGraph.Guess

/-- The shared explicit-center trace computes exactly the endpoint used by
the consistency check. -/
theorem endCenterAtCenters_eq
    (tm : TM workTapeCount) (blockLength : ℕ)
    (centers : TapeIndex workTapeCount → ℕ)
    (inputs :
      PredecessorIndex workTapeCount →
        NeighborhoodContent.Content blockLength tm.Q)
    (tape : TapeIndex workTapeCount) :
    endCenterAtCenters tm blockLength centers inputs tape =
      Consistency.localEndCenter
        tm blockLength centers inputs tape :=
  Internal.endCenterAtCenters_eq_internal
    tm blockLength centers inputs tape

/-- The movement-guess trace computes exactly the endpoint compared by one
runtime boundary check. -/
theorem endCenterAtGuess_eq
    (tm : TM workTapeCount) (blockLength : ℕ)
    (guess : CenterGuess workTapeCount horizon)
    (interval : Fin horizon)
    (inputs :
      PredecessorIndex workTapeCount →
        NeighborhoodContent.Content blockLength tm.Q)
    (tape : TapeIndex workTapeCount) :
    endCenterAtGuess tm blockLength guess interval inputs tape =
      Consistency.localEndCenter tm blockLength
        (Consistency.guessedCenters guess interval.val) inputs tape :=
  Internal.endCenterAtGuess_eq_internal
    tm blockLength guess interval inputs tape

/-- Explicit true centers recover the certificate-level local transition. -/
theorem localNodeFunctionAtCenters_eq
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
        tm x blockLength hpositive timeBlock targetTape targetSlot inputs :=
  Internal.localNodeFunctionAtCenters_eq_internal
    tm x blockLength timeBlock hpositive centers hcenters
    targetTape targetSlot inputs

/-- Explicit true centers recover the certificate-level Boolean callback. -/
theorem booleanCombineAtCenters_eq
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
          timeBlock :=
  Internal.booleanCombineAtCenters_eq_internal
    tm x blockLength timeBlock encoding hpositive centers hcenters
    targetTape targetSlot

/-- Pointwise-correct movement metadata decodes to the true center family. -/
theorem guessedCenters_eq_actual
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
        tm x blockLength interval.val :=
  Internal.guessedCenters_eq_actual_internal
    tm x blockLength guess interval hcenters

/-- On a correct prefix, the movement-guess Boolean callback is the
certificate callback. -/
theorem booleanCombineAtGuess_eq
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
          interval.val :=
  Internal.booleanCombineAtGuess_eq_internal
    tm x blockLength encoding hpositive guess interval hcenters
    targetTape targetSlot

/-- Explicit true centers recover the certificate-level residue callback. -/
theorem combineResiduesAtCenters_eq
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
          timeBlock children :=
  Internal.combineResiduesAtCenters_eq_internal
    tm x blockLength timeBlock encoding hpositive centers hcenters
    targetTape targetSlot children

/-- On a correct prefix, the movement-guess residue callback is the
certificate callback. -/
theorem combineResiduesAtGuess_eq
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
          interval.val children :=
  Internal.combineResiduesAtGuess_eq_internal
    tm x blockLength encoding hpositive guess interval hcenters
    targetTape targetSlot children

end GuessedLocalEvaluation
end Runtime
end TimeSpaceSimulation
end Complexity
