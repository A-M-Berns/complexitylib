/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.NeighborhoodContent
import Complexitylib.TimeSpaceSimulation.NeighborhoodGraph.Guess
import Complexitylib.TimeSpaceSimulation.NeighborhoodGraph.Guess.Consistency.Defs

/-!
# Soundness internals for executable center consistency

The main soundness argument rules out the least mismatching boundary. At
boundary zero the source-anchor check contradicts failure. At a positive
least failure, all earlier centers are correct, so the provider certificate
identifies the callback inputs with the actual compact predecessors. Locality
then identifies the local final head block with the next actual center, and
the boundary check contradicts failure.
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace NeighborhoodGraph

namespace Guess

namespace Consistency

namespace Internal

theorem sourceCenter_eq_actual_internal
    (tm : TM workTapeCount) (x : List Bool) (blockLength : ℕ)
    (tape : TapeIndex workTapeCount) :
    sourceCenter tm x blockLength tape =
      actualCenterTrajectory tm x blockLength tape 0 := by
  unfold sourceCenter actualCenterTrajectory centerBlock TM.activeBlock
    timeBlockStart
  simp only [zero_mul, TM.configurationAt_zero]

theorem guessedCenters_eq_internal
    (guess : CenterGuess workTapeCount horizon) (boundary : ℕ)
    (centers : TapeIndex workTapeCount → ℕ)
    (hcenters : ∀ tape,
      guess.derivedCenter tape boundary = some (centers tape)) :
    guessedCenters guess boundary = centers := by
  funext tape
  simp [guessedCenters, hcenters tape]

theorem localStartCfg_eq_localizedCfg_internal
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
          (timeBlockStart blockLength timeBlock)) := by
  have hcenterFunction :
      centers = centerBlock tm x blockLength timeBlock := by
    funext tape
    simpa [actualCenterTrajectory] using hcenters tape
  rw [hcenterFunction]
  change
    NeighborhoodContent.predecessorCfg tm x blockLength timeBlock
        (NeighborhoodContent.predecessorContents
          tm x blockLength timeBlock hpositive) =
      NeighborhoodContent.localizedCfg blockLength
        (tm.configurationAt x
          (timeBlockStart blockLength timeBlock))
  exact NeighborhoodContent.predecessorCfg_eq_localizedCfg
    tm x blockLength timeBlock hpositive

theorem localEndCenter_actual_internal
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
      actualCenterTrajectory tm x blockLength tape (timeBlock + 1) := by
  have hseed :=
    localStartCfg_eq_localizedCfg_internal
      tm x blockLength timeBlock hpositive centers hcenters
  have hstart :=
    NeighborhoodContent.cfg_localized_agreement
      blockLength hpositive
      (tm.configurationAt x
        (timeBlockStart blockLength timeBlock))
  have hfinal :=
    tm.configurationAt_threeBlock_noninterference
      x blockLength
      (timeBlockStart blockLength timeBlock)
      blockLength
      (NeighborhoodContent.localizedCfg blockLength
        (tm.configurationAt x
          (timeBlockStart blockLength timeBlock)))
      hpositive le_rfl hstart
  have htape :=
    NeighborhoodContent.CfgNeighborhoodAgreement.tapeAt hfinal tape
  unfold localEndCenter
  rw [hseed]
  unfold actualCenterTrajectory centerBlock TM.activeBlock
  have htime :
      timeBlockStart blockLength timeBlock + blockLength =
        timeBlockStart blockLength (timeBlock + 1) := by
    simp [timeBlockStart, Nat.add_mul]
  rw [← htime]
  exact congrArg (blockIndex blockLength) htape.head_eq.symm

theorem initialCheck_eq_true_iff_internal
    (tm : TM workTapeCount) (x : List Bool) (blockLength : ℕ)
    (guess : CenterGuess workTapeCount horizon) :
    initialCheck tm x blockLength guess = true ↔
      ∀ tape : TapeIndex workTapeCount,
        guess.initialCenter tape =
          sourceCenter tm x blockLength tape := by
  constructor
  · intro hcheck tape
    exact beq_iff_eq.mp
      (List.all_eq_true.mp hcheck tape (List.mem_finRange tape))
  · intro hcenter
    apply List.all_eq_true.mpr
    intro tape _
    exact beq_iff_eq.mpr (hcenter tape)

theorem boundaryCheck_eq_true_iff_internal
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
            (guessedCenters guess interval.val) inputs tape) := by
  rw [boundaryCheck, hinputs]
  constructor
  · intro hcheck tape
    exact beq_iff_eq.mp
      (List.all_eq_true.mp hcheck tape (List.mem_finRange tape))
  · intro hcenter
    apply List.all_eq_true.mpr
    intro tape _
    exact beq_iff_eq.mpr (hcenter tape)

theorem passes_eq_true_iff_internal
    (tm : TM workTapeCount) (x : List Bool) (blockLength : ℕ)
    (provider : InputProvider tm blockLength horizon)
    (guess : CenterGuess workTapeCount horizon) :
    passes tm x blockLength provider guess = true ↔
      initialCheck tm x blockLength guess = true ∧
        ∀ interval : Fin horizon,
          boundaryCheck tm blockLength provider guess interval = true := by
  unfold passes
  rw [Bool.and_eq_true, List.all_eq_true]
  constructor
  · rintro ⟨hinitial, hboundaries⟩
    exact ⟨hinitial, fun interval =>
      hboundaries interval (List.mem_finRange interval)⟩
  · rintro ⟨hinitial, hboundaries⟩
    exact ⟨hinitial, fun interval _ => hboundaries interval⟩

theorem actualCenterGuess_passes_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength horizon : ℕ) (hpositive : 0 < blockLength)
    (provider : InputProvider tm blockLength horizon)
    (hexact : IsExactProvider
      tm x blockLength hpositive provider) :
    Passes tm x blockLength provider
      (actualCenterGuess tm x blockLength horizon) := by
  unfold Passes
  apply (passes_eq_true_iff_internal
    tm x blockLength provider
      (actualCenterGuess tm x blockLength horizon)).mpr
  constructor
  · apply (initialCheck_eq_true_iff_internal
      tm x blockLength
        (actualCenterGuess tm x blockLength horizon)).mpr
    intro tape
    change
      actualCenterTrajectory tm x blockLength tape 0 =
        sourceCenter tm x blockLength tape
    exact (sourceCenter_eq_actual_internal
      tm x blockLength tape).symm
  · intro interval
    have hprefix :
        ∀ boundary : Fin (horizon + 1),
          boundary.val ≤ interval.val →
            ∀ tape : TapeIndex workTapeCount,
              (actualCenterGuess tm x blockLength horizon).derivedCenter
                  tape boundary.val =
                some (actualCenterTrajectory
                  tm x blockLength tape boundary.val) := by
      intro boundary _ tape
      exact actualCenterGuess_derivedCenter
        tm x blockLength horizon boundary.val tape
          hpositive (by omega)
    have hinputs :=
      hexact (actualCenterGuess tm x blockLength horizon)
        interval hprefix
    apply (boundaryCheck_eq_true_iff_internal
      tm blockLength provider
      (actualCenterGuess tm x blockLength horizon)
      interval
      (NeighborhoodContent.predecessorContents
        tm x blockLength interval.val hpositive)
      hinputs).mpr
    have hcurrent :
        ∀ tape : TapeIndex workTapeCount,
          (actualCenterGuess tm x blockLength horizon).derivedCenter
              tape interval.val =
            some (actualCenterTrajectory
              tm x blockLength tape interval.val) := by
      intro tape
      exact actualCenterGuess_derivedCenter
        tm x blockLength horizon interval.val tape
          hpositive (by omega)
    have hcenters :
        guessedCenters
            (actualCenterGuess tm x blockLength horizon)
            interval.val =
          fun tape =>
            actualCenterTrajectory
              tm x blockLength tape interval.val :=
      guessedCenters_eq_internal _ _ _ hcurrent
    intro tape
    rw [hcenters]
    calc
      (actualCenterGuess tm x blockLength horizon).derivedCenter
          tape (interval.val + 1) =
          some (actualCenterTrajectory tm x blockLength tape
            (interval.val + 1)) :=
        actualCenterGuess_derivedCenter
          tm x blockLength horizon (interval.val + 1) tape
            hpositive (by omega)
      _ = some (localEndCenter tm blockLength
          (fun currentTape =>
            actualCenterTrajectory tm x blockLength
              currentTape interval.val)
          (NeighborhoodContent.predecessorContents
            tm x blockLength interval.val hpositive) tape) := by
        congr 1
        symm
        exact localEndCenter_actual_internal
          tm x blockLength interval.val hpositive
          (fun currentTape =>
            actualCenterTrajectory tm x blockLength
              currentTape interval.val)
          (fun _ => rfl) tape

theorem passes_implies_valid_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength horizon : ℕ) (hpositive : 0 < blockLength)
    (provider : InputProvider tm blockLength horizon)
    (hexact : IsExactProvider
      tm x blockLength hpositive provider)
    (guess : CenterGuess workTapeCount horizon)
    (hpasses : Passes tm x blockLength provider guess) :
    guess.IsValidFor
      (actualCenterTrajectory tm x blockLength) := by
  unfold Passes at hpasses
  have hchecks :=
    (passes_eq_true_iff_internal
      tm x blockLength provider guess).mp hpasses
  by_contra hinvalid
  obtain ⟨⟨first, hfirstBound⟩, tape, _hfirst,
      hmismatch, hearlier⟩ :=
    guess.not_isValidFor_has_firstFailure
      (actualCenterTrajectory tm x blockLength) hinvalid
  cases first with
  | zero =>
      have hinitial :=
        (initialCheck_eq_true_iff_internal
          tm x blockLength guess).mp hchecks.1 tape
      apply hmismatch
      change
        some (guess.initialCenter tape) =
          some (actualCenterTrajectory tm x blockLength tape 0)
      congr 1
      exact hinitial.trans
        (sourceCenter_eq_actual_internal tm x blockLength tape)
  | succ previous =>
      have hprevious : previous < horizon := by
        omega
      let interval : Fin horizon := ⟨previous, hprevious⟩
      have hprefix :
          ∀ boundary : Fin (horizon + 1),
            boundary.val ≤ interval.val →
              ∀ currentTape : TapeIndex workTapeCount,
                guess.derivedCenter currentTape boundary.val =
                  some (actualCenterTrajectory tm x blockLength
                    currentTape boundary.val) := by
        intro boundary hle currentTape
        apply hearlier boundary
        · change boundary.val < previous + 1
          dsimp only [interval] at hle
          omega
      have hinputs :=
        hexact guess interval hprefix
      have hboundary :=
        (boundaryCheck_eq_true_iff_internal
          tm blockLength provider guess interval
          (NeighborhoodContent.predecessorContents
            tm x blockLength interval.val hpositive)
          hinputs).mp (hchecks.2 interval)
      have hcurrent :
          ∀ currentTape : TapeIndex workTapeCount,
            guess.derivedCenter currentTape interval.val =
              some (actualCenterTrajectory tm x blockLength
                currentTape interval.val) := by
        intro currentTape
        let boundary : Fin (horizon + 1) :=
          ⟨previous, by omega⟩
        exact hearlier boundary (by
          dsimp only [boundary, interval]
          omega) currentTape
      have hcenters :
          guessedCenters guess interval.val =
            fun currentTape =>
              actualCenterTrajectory tm x blockLength
                currentTape interval.val :=
        guessedCenters_eq_internal _ _ _ hcurrent
      have hnext := hboundary tape
      rw [hcenters] at hnext
      apply hmismatch
      calc
        guess.derivedCenter tape (previous + 1) =
            some (localEndCenter tm blockLength
              (fun currentTape =>
                actualCenterTrajectory tm x blockLength
                  currentTape interval.val)
              (NeighborhoodContent.predecessorContents
                tm x blockLength interval.val hpositive) tape) := by
          simpa [interval] using hnext
        _ = some (actualCenterTrajectory tm x blockLength tape
              (previous + 1)) := by
          congr 1
          simpa [interval] using
            localEndCenter_actual_internal
              tm x blockLength interval.val hpositive
              (fun currentTape =>
                actualCenterTrajectory tm x blockLength
                  currentTape interval.val)
              (fun _ => rfl) tape

theorem passes_predecessor?_eq_internal
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
  guess.predecessor?_eq tm x blockLength interval index
    (passes_implies_valid_internal
      tm x blockLength horizon hpositive
      provider hexact guess hpasses)

theorem passes_predecessorAt?_eq_internal
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
  guess.predecessorAt?_eq tm x blockLength interval index
    (passes_implies_valid_internal
      tm x blockLength horizon hpositive
      provider hexact guess hpasses)

theorem callbackValueWidth_eq_internal
    (tm : TM workTapeCount) (blockLength : ℕ) :
    callbackValueWidth tm blockLength =
      Fintype.card tm.Q + 5 * blockLength := by
  rfl

theorem centerMove_card_internal :
    Fintype.card CenterMove = 3 := by
  decide

end Internal

end Consistency

end Guess

end NeighborhoodGraph

end TimeSpaceSimulation

end Complexity
