/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.NeighborhoodGraph.Guess.Consistency.Defs
import Complexitylib.TimeSpaceSimulation.NeighborhoodGraph.Guess.Consistency.Internal

/-!
# Executable center-guess self-consistency and soundness

`passes` is a finite executable check with no access to
`actualCenterTrajectory`. It verifies:

1. every initial guessed center equals the block of the corresponding source
   head;
2. at every interval boundary, the center derived from the next movement
   equals the final head block produced by one local simulation.

The local simulation consumes exactly one compact value for each of the
`4 * (workTapeCount + 2)` neighborhood predecessor roles. A proof-only
`IsExactProvider` certificate states what a future guessed-tree evaluator
must establish about those values on a correct prefix.

Under that certificate, the actual movement guess passes. Conversely, a
passing guess is valid for the actual center trajectory. The soundness proof
uses the least failing boundary: zero contradicts the source anchor, while a
positive failure contradicts the locally reconstructed transition from its
correct prefix. Therefore all guessed predecessor oracles agree with the
direct neighborhood graph.

Each callback value has exactly `Fintype.card tm.Q + 5 * blockLength`
Boolean coordinates. Absolute centers remain graph metadata; subsequent
center choices are three-valued movements, not unary Boolean payloads.
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace NeighborhoodGraph

namespace Guess

namespace Consistency

/-- The source anchor is exactly the actual interval-zero center. This
semantic theorem is used only to prove checker completeness and soundness;
`initialCheck` itself reads the initial configuration directly. -/
theorem sourceCenter_eq_actual
    (tm : TM workTapeCount) (x : List Bool) (blockLength : ℕ)
    (tape : TapeIndex workTapeCount) :
    sourceCenter tm x blockLength tape =
      actualCenterTrajectory tm x blockLength tape 0 :=
  Internal.sourceCenter_eq_actual_internal tm x blockLength tape

/-- Pointwise defined derived centers identify the total center metadata used
by local reconstruction. -/
theorem guessedCenters_eq
    (guess : CenterGuess workTapeCount horizon) (boundary : ℕ)
    (centers : TapeIndex workTapeCount → ℕ)
    (hcenters : ∀ tape,
      guess.derivedCenter tape boundary = some (centers tape)) :
    guessedCenters guess boundary = centers :=
  Internal.guessedCenters_eq_internal
    guess boundary centers hcenters

/-- With true current centers and true compact predecessor values, the
runtime local seed is exactly the canonical three-block localization. -/
theorem localStartCfg_eq_localizedCfg
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength timeBlock : ℕ) (hpositive : 0 < blockLength)
    (centers : TapeIndex workTapeCount → ℕ)
    (hcenters : ∀ tape,
      centers tape =
        actualCenterTrajectory tm x blockLength tape timeBlock) :
    localStartCfg tm blockLength centers
        (NeighborhoodContent.predecessorContents
          tm x blockLength timeBlock hpositive) =
      NeighborhoodContent.localizedCfg blockLength
        (tm.configurationAt x
          (timeBlockStart blockLength timeBlock)) :=
  Internal.localStartCfg_eq_localizedCfg_internal
    tm x blockLength timeBlock hpositive centers hcenters

/-- Locality makes the reconstructed interval's final head block equal the
next actual center. -/
theorem localEndCenter_actual
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength timeBlock : ℕ) (hpositive : 0 < blockLength)
    (centers : TapeIndex workTapeCount → ℕ)
    (hcenters : ∀ tape,
      centers tape =
        actualCenterTrajectory tm x blockLength tape timeBlock)
    (tape : TapeIndex workTapeCount) :
    localEndCenter tm blockLength centers
        (NeighborhoodContent.predecessorContents
          tm x blockLength timeBlock hpositive) tape =
      actualCenterTrajectory tm x blockLength tape (timeBlock + 1) :=
  Internal.localEndCenter_actual_internal
    tm x blockLength timeBlock hpositive centers hcenters tape

/-- Characterization of the finite initial-source check. -/
theorem initialCheck_eq_true_iff
    (tm : TM workTapeCount) (x : List Bool) (blockLength : ℕ)
    (guess : CenterGuess workTapeCount horizon) :
    initialCheck tm x blockLength guess = true ↔
      ∀ tape : TapeIndex workTapeCount,
        guess.initialCenter tape =
          sourceCenter tm x blockLength tape :=
  Internal.initialCheck_eq_true_iff_internal
    tm x blockLength guess

/-- Characterization of one finite local boundary check after resolving the
callback's compact predecessor vector. -/
theorem boundaryCheck_eq_true_iff
    (tm : TM workTapeCount) (blockLength : ℕ)
    (provider : InputProvider tm blockLength horizon)
    (guess : CenterGuess workTapeCount horizon)
    (interval : Fin horizon)
    (inputs : PredecessorIndex workTapeCount →
      NeighborhoodContent.Content blockLength tm.Q)
    (hinputs : provider guess interval = some inputs) :
    boundaryCheck tm blockLength provider guess interval = true ↔
      ∀ tape : TapeIndex workTapeCount,
        guess.derivedCenter tape (interval.val + 1) =
          some (localEndCenter tm blockLength
            (guessedCenters guess interval.val) inputs tape) :=
  Internal.boundaryCheck_eq_true_iff_internal
    tm blockLength provider guess interval inputs hinputs

/-- The complete executable checker is exactly the source anchor together
with all finite boundary checks. -/
theorem passes_eq_true_iff
    (tm : TM workTapeCount) (x : List Bool) (blockLength : ℕ)
    (provider : InputProvider tm blockLength horizon)
    (guess : CenterGuess workTapeCount horizon) :
    passes tm x blockLength provider guess = true ↔
      initialCheck tm x blockLength guess = true ∧
        ∀ interval : Fin horizon,
          boundaryCheck tm blockLength provider guess interval = true :=
  Internal.passes_eq_true_iff_internal
    tm x blockLength provider guess

/-- Completeness: the actual movement guess passes every executable finite
check when the compact-input provider meets its stated prefix obligation. -/
theorem actualCenterGuess_passes
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength horizon : ℕ) (hpositive : 0 < blockLength)
    (provider : InputProvider tm blockLength horizon)
    (hexact : IsExactProvider
      tm x blockLength hpositive provider) :
    Passes tm x blockLength provider
      (actualCenterGuess tm x blockLength horizon) :=
  Internal.actualCenterGuess_passes_internal
    tm x blockLength horizon hpositive provider hexact

/-- Soundness: every guess accepted by the finite local checks agrees with
the actual center trajectory at every in-range boundary. -/
theorem passes_implies_valid
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength horizon : ℕ) (hpositive : 0 < blockLength)
    (provider : InputProvider tm blockLength horizon)
    (hexact : IsExactProvider
      tm x blockLength hpositive provider)
    (guess : CenterGuess workTapeCount horizon)
    (hpasses : Passes tm x blockLength provider guess) :
    guess.IsValidFor
      (actualCenterTrajectory tm x blockLength) :=
  Internal.passes_implies_valid_internal
    tm x blockLength horizon hpositive
    provider hexact guess hpasses

/-- A passing guess has the correct typed predecessor oracle. -/
theorem passes_predecessor?_eq
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength horizon : ℕ) (hpositive : 0 < blockLength)
    (provider : InputProvider tm blockLength horizon)
    (hexact : IsExactProvider
      tm x blockLength hpositive provider)
    (guess : CenterGuess workTapeCount horizon)
    (hpasses : Passes tm x blockLength provider guess)
    (interval : Fin horizon)
    (index : PredecessorIndex workTapeCount) :
    guess.predecessor? interval index =
      some (NeighborhoodGraph.predecessor
        tm x blockLength interval.val index) :=
  Internal.passes_predecessor?_eq_internal
    tm x blockLength horizon hpositive
    provider hexact guess hpasses interval index

/-- A passing guess has the correct fixed-`Fin` predecessor oracle consumed
by the neighborhood tree. -/
theorem passes_predecessorAt?_eq
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength horizon : ℕ) (hpositive : 0 < blockLength)
    (provider : InputProvider tm blockLength horizon)
    (hexact : IsExactProvider
      tm x blockLength hpositive provider)
    (guess : CenterGuess workTapeCount horizon)
    (hpasses : Passes tm x blockLength provider guess)
    (interval : Fin horizon)
    (index : Fin (4 * (workTapeCount + 2))) :
    guess.predecessorAt? interval index =
      some (NeighborhoodGraph.predecessorAt
        tm x blockLength interval.val index) :=
  Internal.passes_predecessorAt?_eq_internal
    tm x blockLength horizon hpositive
    provider hexact guess hpasses interval index

/-- Every compact callback value has the established linear Boolean width;
absolute block indices are not part of this payload. -/
theorem callbackValueWidth_eq
    (tm : TM workTapeCount) (blockLength : ℕ) :
    callbackValueWidth tm blockLength =
      Fintype.card tm.Q + 5 * blockLength :=
  Internal.callbackValueWidth_eq_internal tm blockLength

/-- Every noninitial center update is one three-valued movement. -/
@[simp] theorem centerMove_card :
    Fintype.card CenterMove = 3 :=
  Internal.centerMove_card_internal

end Consistency

end Guess

end NeighborhoodGraph

end TimeSpaceSimulation

end Complexity
