/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.ChildNode.Defs

/-!
# Correctness internals for child-node regeneration
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace ChildNode
namespace Internal

open RAM Structured

variable {controller : SearchProgram.Registers}

private theorem basics_runs (ops : List Basic) (store : Store) :
    Runs (Cmd.basics ops) store (Basic.execList ops store) := by
  obtain ⟨cost, space, hexec⟩ :=
    RAM.Structured.Internal.exec_basics_exists ops store
  exact ⟨ops.length, cost, space, hexec⟩

private theorem copy_runs
    (destination source : ℕ) (store : Store)
    (hne : destination ≠ source) :
    ∃ final,
      Runs (ControlDecode.copy destination source) store final ∧
      final destination = store source ∧
      ∀ address, address ≠ destination →
        final address = store address := by
  let middle := (Basic.imm destination 0).exec store
  let final := (Basic.add destination source destination).exec middle
  refine ⟨final, ?_, ?_, ?_⟩
  · exact Runs.seq (Runs.basic _ _) (Runs.basic _ _)
  · simp [final, middle, Basic.exec, Ne.symm hne]
  · intro address haddress
    simp [final, middle, Basic.exec, Function.update_of_ne,
      haddress]

private theorem copy_update_runs
    {destination source : ℕ} (store : Store)
    (hne : destination ≠ source) :
    Runs (ControlDecode.copy destination source) store
      (Function.update store destination (store source)) := by
  apply Runs.seq (Runs.basic (.imm destination 0) store)
  simpa [Basic.exec, Function.update_of_ne, hne, Ne.symm hne] using
    Runs.basic
      (.add destination source destination)
      (Basic.exec (.imm destination 0) store)

private theorem division_index_ne_movementIndex
    (regs : NeighborhoodTrial.Registers controller)
    (slot : Fin 5) :
    (movementDivision regs).index slot ≠ movementIndex regs := by
  apply regs.injective.ne
  intro heq
  have hval := congrArg Fin.val heq
  change (movementMap ⟨slot.val, by omega⟩).val =
    (movementMap 5).val at hval
  fin_cases slot <;> simp [movementMap] at hval

private theorem movementIndex_not_mem_division
    (regs : NeighborhoodTrial.Registers controller) :
    movementIndex regs ∉
      (movementDivision regs).writeFootprint := by
  simp only [ControlDecode.DivisionRegisters.writeFootprint,
    Finset.mem_insert, Finset.mem_singleton]
  push Not
  exact ⟨(division_index_ne_movementIndex regs 0).symm,
    (division_index_ne_movementIndex regs 1).symm,
    (division_index_ne_movementIndex regs 2).symm,
    (division_index_ne_movementIndex regs 3).symm⟩

private theorem division_index_ne
    (regs : NeighborhoodTrial.Registers controller)
    {first second : Fin 5} (hne : first ≠ second) :
    (movementDivision regs).index first ≠
      (movementDivision regs).index second :=
  (movementDivision regs).injective.ne hne

private theorem cmdWritesWithin_mono
    {small large : Finset ℕ} {cmd : Cmd}
    (hwrites : Footprint.CmdWritesWithin small cmd)
    (hsubset : small ⊆ large) :
    Footprint.CmdWritesWithin large cmd := by
  induction cmd with
  | skip =>
      trivial
  | basic op =>
      cases op <;>
        simp only [Footprint.CmdWritesWithin,
          Footprint.BasicWritesWithin] at hwrites ⊢
      all_goals
        exact hsubset hwrites
  | seq first second ihFirst ihSecond =>
      exact ⟨ihFirst hwrites.1, ihSecond hwrites.2⟩
  | ifZero test onZero onNonzero ihZero ihNonzero =>
      exact ⟨ihZero hwrites.1, ihNonzero hwrites.2⟩
  | whileNonzero test body ih =>
      exact ih hwrites

private theorem movementDivision_writesWithin
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (movementFootprint regs)
      (ControlDecode.divRem (movementDivision regs)) := by
  apply cmdWritesWithin_mono
    (ControlDecode.divRem_writesWithin (movementDivision regs))
  intro address haddress
  simp only [ControlDecode.DivisionRegisters.writeFootprint,
    Finset.mem_insert, Finset.mem_singleton] at haddress
  rcases haddress with haddress | haddress | haddress |
      haddress
  all_goals
    subst address
    simp [movementFootprint, movementDivision, movementMap]

private theorem copy_movement_writesWithin
    (regs : NeighborhoodTrial.Registers controller)
    (source : ℕ) :
    Footprint.CmdWritesWithin (movementFootprint regs)
      (ControlDecode.copy (movementDivision regs).value source) := by
  apply cmdWritesWithin_mono
    (small := {(movementDivision regs).value})
  · simp [ControlDecode.copy, Footprint.CmdWritesWithin,
      Footprint.BasicWritesWithin]
  · intro address haddress
    simp only [Finset.mem_singleton] at haddress
    subst address
    simp [movementFootprint, movementDivision, movementMap]

theorem ternarySuffix_eq_div_pow_internal
    (word count : ℕ) :
    ternarySuffix word count = word / 3 ^ count := by
  induction count generalizing word with
  | zero =>
      simp [ternarySuffix]
  | succ count ih =>
      rw [ternarySuffix, ih]
      simp [pow_succ, Nat.div_div_eq_div_mul, Nat.mul_comm]

theorem movementDigitValue_eq_digit_internal
    (word index : ℕ) :
    movementDigitValue word index =
      PackedDigits.digit 3 word index := by
  simp [movementDigitValue, ternarySuffix_eq_div_pow_internal,
    PackedDigits.digit]

private theorem getD_digitsAppend
    (base length word index : ℕ) :
    (Nat.digitsAppend base length word).getD index 0 =
      (Nat.digits base word).getD index 0 := by
  unfold Nat.digitsAppend
  by_cases hindex : index < (Nat.digits base word).length
  · rw [List.getD_append _ _ _ _ hindex]
  · rw [List.getD_append_right _ _ _ _
      (Nat.le_of_not_gt hindex)]
    rw [List.getD_eq_default _ _ (Nat.le_of_not_gt hindex)]
    simp

theorem movementDigitValue_candidateGuess_internal
    (code :
      Fin
        (3 ^
          NeighborhoodGraph.Guess.Enumeration.movementCount
            workTapeCount horizon))
    (interval : Fin horizon)
    (tape : TapeIndex workTapeCount) :
    NeighborhoodGraph.Guess.Enumeration.moveOfDigit
        (movementDigitValue code.val
          (interval.val * (workTapeCount + 2) + tape.val)) =
      (NeighborhoodGraph.Guess.Enumeration.candidateGuess code).movement
        interval tape := by
  simp only
    [NeighborhoodGraph.Guess.Enumeration.candidateGuess,
      NeighborhoodGraph.Guess.Enumeration.candidateDigits,
      NeighborhoodGraph.Guess.Enumeration.movementIndex,
      finProdFinEquiv, Equiv.coe_fn_mk]
  rw [getD_digitsAppend]
  rw [Nat.getD_digits code.val
    (tape.val + (workTapeCount + 2) * interval.val) (by omega)]
  simp [movementDigitValue, ternarySuffix_eq_div_pow_internal,
    Nat.mul_comm, Nat.add_comm]

private theorem scanCenter_succ_last
    (word stride remaining index center : ℕ) :
    scanCenter word stride (remaining + 1) index center =
      (scanCenter word stride remaining index center).bind
        (applyMovementDigit
          (movementDigitValue word
            (index + remaining * stride))) := by
  induction remaining generalizing index center with
  | zero =>
      generalize hmove :
        applyMovementDigit
          (movementDigitValue word index) center = result
      cases result <;> simp [scanCenter, hmove]
  | succ remaining ih =>
      change
        (match applyMovementDigit
            (movementDigitValue word index) center with
        | none => none
        | some next =>
            scanCenter word stride (remaining + 1)
              (index + stride) next) =
          (match applyMovementDigit
              (movementDigitValue word index) center with
          | none => none
          | some next =>
              scanCenter word stride remaining
                (index + stride) next).bind
            (applyMovementDigit
              (movementDigitValue word
                (index + (remaining + 1) * stride)))
      generalize hmove :
        applyMovementDigit
          (movementDigitValue word index) center = result
      cases result with
      | none =>
          simp
      | some next =>
          change
            scanCenter word stride (remaining + 1)
                (index + stride) next =
              (scanCenter word stride remaining
                (index + stride) next).bind
                (applyMovementDigit
                  (movementDigitValue word
                    (index + (remaining + 1) * stride)))
          rw [ih (index + stride) next]
          congr 2
          simp [Nat.add_mul, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm]

private theorem applyMovementDigit_eq_apply
    {digit : ℕ} (hdigit : digit < 3) :
    applyMovementDigit digit =
      (NeighborhoodGraph.Guess.Enumeration.moveOfDigit digit).apply := by
  funext center
  interval_cases digit <;> cases center <;>
    simp [applyMovementDigit,
      NeighborhoodGraph.Guess.Enumeration.moveOfDigit,
      NeighborhoodGraph.Guess.CenterMove.apply]

theorem derivedCenterValue_candidateGuess_internal
    (code :
      Fin
        (3 ^
          NeighborhoodGraph.Guess.Enumeration.movementCount
            workTapeCount horizon))
    (tape : TapeIndex workTapeCount)
    (boundary : ℕ) (hboundary : boundary ≤ horizon) :
    derivedCenterValue workTapeCount code.val tape.val boundary =
      (NeighborhoodGraph.Guess.Enumeration.candidateGuess code).derivedCenter
        tape boundary := by
  induction boundary with
  | zero =>
      simp [derivedCenterValue, scanCenter,
        NeighborhoodGraph.Guess.CenterGuess.derivedCenter,
        NeighborhoodGraph.Guess.Enumeration.candidateGuess]
  | succ boundary ih =>
      have hinterval : boundary < horizon := by
        omega
      rw [derivedCenterValue, scanCenter_succ_last]
      change
        (derivedCenterValue workTapeCount code.val tape.val
          boundary).bind
            (applyMovementDigit
              (movementDigitValue code.val
                (tape.val + boundary * (workTapeCount + 2)))) =
          (NeighborhoodGraph.Guess.Enumeration.candidateGuess code).derivedCenter
            tape (boundary + 1)
      rw [ih (by omega)]
      simp only
        [NeighborhoodGraph.Guess.CenterGuess.derivedCenter,
          hinterval, dite_true]
      have hdigit :
          movementDigitValue code.val
              (tape.val + boundary * (workTapeCount + 2)) < 3 := by
        rw [movementDigitValue_eq_digit_internal]
        exact PackedDigits.digit_lt (by omega)
      rw [applyMovementDigit_eq_apply hdigit]
      have hmovement :
          NeighborhoodGraph.Guess.Enumeration.moveOfDigit
              (movementDigitValue code.val
                (tape.val + boundary * (workTapeCount + 2))) =
            (NeighborhoodGraph.Guess.Enumeration.candidateGuess code).movement
              ⟨boundary, hinterval⟩ tape := by
        simpa [Nat.mul_comm, Nat.add_comm] using
          movementDigitValue_candidateGuess_internal code
            (⟨boundary, hinterval⟩ : Fin horizon) tape
      rw [hmovement]

private def IsPriorMatch
    (workTapeCount word tape requested interval : ℕ) : Prop :=
  ∃ center,
    derivedCenterValue workTapeCount word tape interval =
        some center ∧
      NeighborhoodGraph.NeighborhoodContains center requested

private theorem priorSearchValue_ne_none
    (workTapeCount word tape requested count : ℕ)
    (hvalid :
      ∀ interval, interval < count →
        ∃ center,
          derivedCenterValue workTapeCount word tape interval =
            some center) :
    priorSearchValue workTapeCount word tape requested count ≠ none := by
  induction count with
  | zero =>
      simp [priorSearchValue]
  | succ count ih =>
      obtain ⟨center, hcenter⟩ := hvalid count (by omega)
      rw [priorSearchValue, hcenter]
      by_cases hcontains :
          NeighborhoodGraph.NeighborhoodContains center requested
      · simp [hcontains]
      · simp only [if_neg hcontains]
        exact ih fun interval hinterval =>
          hvalid interval (by omega)

private theorem priorSearchValue_some_none_no_match
    (workTapeCount word tape requested count : ℕ)
    (hsearch :
      priorSearchValue workTapeCount word tape requested count =
        some none) :
    ∀ interval, interval < count →
      ¬IsPriorMatch
        workTapeCount word tape requested interval := by
  induction count with
  | zero =>
      intro interval hinterval
      omega
  | succ count ih =>
      generalize hcenter :
        derivedCenterValue workTapeCount word tape count = result
      cases result with
      | none =>
          simp [priorSearchValue, hcenter] at hsearch
      | some center =>
          by_cases hcontains :
              NeighborhoodGraph.NeighborhoodContains center requested
          · simp [priorSearchValue, hcenter, hcontains] at hsearch
          · have hrecursive :
                priorSearchValue workTapeCount word tape requested count =
                  some none := by
              simpa [priorSearchValue, hcenter, hcontains] using
                hsearch
            intro interval hinterval hmatch
            by_cases hlt : interval < count
            · exact ih hrecursive interval hlt hmatch
            · have heq : interval = count := by
                omega
              subst interval
              rcases hmatch with
                ⟨otherCenter, hotherCenter, hotherContains⟩
              rw [hcenter] at hotherCenter
              simp only [Option.some.injEq] at hotherCenter
              subst otherCenter
              exact hcontains hotherContains

private theorem priorSearchValue_some_some_maximal
    (workTapeCount word tape requested count interval center : ℕ)
    (hsearch :
      priorSearchValue workTapeCount word tape requested count =
        some (some (interval, center))) :
    interval < count ∧
      derivedCenterValue workTapeCount word tape interval =
        some center ∧
      NeighborhoodGraph.NeighborhoodContains center requested ∧
      ∀ later, interval < later → later < count →
        ¬IsPriorMatch
          workTapeCount word tape requested later := by
  induction count with
  | zero =>
      simp [priorSearchValue] at hsearch
  | succ count ih =>
      generalize hcurrent :
        derivedCenterValue workTapeCount word tape count = result
      cases result with
      | none =>
          simp [priorSearchValue, hcurrent] at hsearch
      | some current =>
          by_cases hcontains :
              NeighborhoodGraph.NeighborhoodContains current requested
          · have hpairs :
                count = interval ∧ current = center := by
              simpa [priorSearchValue, hcurrent, hcontains] using
                hsearch
            rcases hpairs with ⟨rfl, rfl⟩
            refine ⟨by omega, hcurrent, hcontains, ?_⟩
            intro later hlater hbound
            omega
          · have hrecursive :
                priorSearchValue workTapeCount word tape requested count =
                  some (some (interval, center)) := by
              simpa [priorSearchValue, hcurrent, hcontains] using
                hsearch
            rcases ih hrecursive with
              ⟨hinterval, hcenter, hmatch, hmaximal⟩
            refine
              ⟨by omega, hcenter, hmatch, ?_⟩
            intro later hlater hbound hlaterMatch
            by_cases hlt : later < count
            · exact hmaximal later hlater hlt hlaterMatch
            · have heq : later = count := by
                omega
              subst later
              rcases hlaterMatch with
                ⟨otherCenter, hotherCenter, hotherContains⟩
              rw [hcurrent] at hotherCenter
              simp only [Option.some.injEq] at hotherCenter
              subst otherCenter
              exact hcontains hotherContains

private theorem derivedCenterValue_prefix
    (workTapeCount word tape interval center : ℕ)
    (hcenter :
      derivedCenterValue workTapeCount word tape interval =
        some center) :
    ∀ earlier, earlier ≤ interval →
      ∃ earlierCenter,
        derivedCenterValue workTapeCount word tape earlier =
          some earlierCenter := by
  induction interval generalizing center with
  | zero =>
      intro earlier hearlier
      have heq : earlier = 0 := by
        omega
      subst earlier
      exact ⟨center, hcenter⟩
  | succ interval ih =>
      have hprevious :
          ∃ previousCenter,
            derivedCenterValue workTapeCount word tape interval =
              some previousCenter := by
        rw [derivedCenterValue, scanCenter_succ_last] at hcenter
        change
          (derivedCenterValue
            workTapeCount word tape interval).bind
              (applyMovementDigit
                (movementDigitValue word
                  (tape + interval * (workTapeCount + 2)))) =
            some center at hcenter
        generalize hresult :
          derivedCenterValue workTapeCount word tape interval =
            result at hcenter
        cases result with
        | none =>
            simp at hcenter
        | some previousCenter =>
            exact ⟨previousCenter, rfl⟩
      intro earlier hearlier
      by_cases heq : earlier = interval + 1
      · subst earlier
        exact ⟨center, hcenter⟩
      · obtain ⟨previousCenter, hpreviousCenter⟩ := hprevious
        exact ih previousCenter hpreviousCenter earlier (by omega)

private theorem mem_candidateGuess_priorIntervals_iff
    (code :
      Fin
        (3 ^
          NeighborhoodGraph.Guess.Enumeration.movementCount
            workTapeCount horizon))
    (tape : TapeIndex workTapeCount)
    (requested count : ℕ) (hcount : count ≤ horizon)
    (previous : Fin count) :
    previous ∈
        NeighborhoodGraph.Guess.CenterGuess.priorIntervals
          (NeighborhoodGraph.Guess.Enumeration.candidateGuess code)
          tape requested count ↔
      IsPriorMatch workTapeCount code.val tape.val requested
        previous.val := by
  have hderived :=
    derivedCenterValue_candidateGuess_internal
      code tape previous.val (by omega)
  simp only
    [NeighborhoodGraph.Guess.CenterGuess.priorIntervals,
      Finset.mem_filter, Finset.mem_univ, true_and]
  rw [← hderived]
  generalize hcenter :
    derivedCenterValue workTapeCount code.val tape.val
      previous.val = result
  cases result with
  | none =>
      simp [IsPriorMatch, hcenter]
  | some center =>
      simp [IsPriorMatch, hcenter]

private theorem candidateGuess_previousInterval_eq_none
    (code :
      Fin
        (3 ^
          NeighborhoodGraph.Guess.Enumeration.movementCount
            workTapeCount horizon))
    (tape : TapeIndex workTapeCount)
    (requested count : ℕ) (hcount : count ≤ horizon)
    (hnoMatch :
      ∀ interval, interval < count →
        ¬IsPriorMatch
          workTapeCount code.val tape.val requested interval) :
    NeighborhoodGraph.Guess.CenterGuess.previousInterval
        (NeighborhoodGraph.Guess.Enumeration.candidateGuess code)
        tape requested count =
      none := by
  have hempty :
      ¬(NeighborhoodGraph.Guess.CenterGuess.priorIntervals
          (NeighborhoodGraph.Guess.Enumeration.candidateGuess code)
          tape requested count).Nonempty := by
    intro hnonempty
    rcases hnonempty with ⟨previous, hprevious⟩
    exact hnoMatch previous.val previous.isLt
      ((mem_candidateGuess_priorIntervals_iff
        code tape requested count hcount previous).1 hprevious)
  simp [NeighborhoodGraph.Guess.CenterGuess.previousInterval,
    hempty]

private theorem candidateGuess_previousInterval_eq_some
    (code :
      Fin
        (3 ^
          NeighborhoodGraph.Guess.Enumeration.movementCount
            workTapeCount horizon))
    (tape : TapeIndex workTapeCount)
    (requested count interval center : ℕ)
    (hcount : count ≤ horizon)
    (hinterval : interval < count)
    (hcenter :
      derivedCenterValue workTapeCount code.val tape.val interval =
        some center)
    (hcontains :
      NeighborhoodGraph.NeighborhoodContains center requested)
    (hmaximal :
      ∀ later, interval < later → later < count →
        ¬IsPriorMatch
          workTapeCount code.val tape.val requested later) :
    NeighborhoodGraph.Guess.CenterGuess.previousInterval
        (NeighborhoodGraph.Guess.Enumeration.candidateGuess code)
        tape requested count =
      some ⟨interval, hinterval⟩ := by
  let previous : Fin count := ⟨interval, hinterval⟩
  have hpreviousMatch :
      IsPriorMatch
        workTapeCount code.val tape.val requested previous.val :=
    ⟨center, hcenter, hcontains⟩
  have hpreviousMem :
      previous ∈
        NeighborhoodGraph.Guess.CenterGuess.priorIntervals
          (NeighborhoodGraph.Guess.Enumeration.candidateGuess code)
          tape requested count :=
    (mem_candidateGuess_priorIntervals_iff
      code tape requested count hcount previous).2 hpreviousMatch
  have hnonempty :
      (NeighborhoodGraph.Guess.CenterGuess.priorIntervals
          (NeighborhoodGraph.Guess.Enumeration.candidateGuess code)
          tape requested count).Nonempty :=
    ⟨previous, hpreviousMem⟩
  rw [NeighborhoodGraph.Guess.CenterGuess.previousInterval,
    dif_pos hnonempty]
  congr 1
  apply Fin.ext
  apply Nat.le_antisymm
  · by_contra hle
    change
      ¬((NeighborhoodGraph.Guess.CenterGuess.priorIntervals
          (NeighborhoodGraph.Guess.Enumeration.candidateGuess code)
          tape requested count).max' hnonempty).val ≤ interval at hle
    have hlt :
        interval <
          (NeighborhoodGraph.Guess.CenterGuess.priorIntervals
            (NeighborhoodGraph.Guess.Enumeration.candidateGuess code)
            tape requested count).max' hnonempty := by
      omega
    have hmaxMem :=
      Finset.max'_mem
        (NeighborhoodGraph.Guess.CenterGuess.priorIntervals
          (NeighborhoodGraph.Guess.Enumeration.candidateGuess code)
          tape requested count) hnonempty
    have hmaxMatch :=
      (mem_candidateGuess_priorIntervals_iff
        code tape requested count hcount _).1 hmaxMem
    exact hmaximal _ hlt (Fin.isLt _) hmaxMatch
  · exact Finset.le_max' _ previous hpreviousMem

theorem priorSearchValue_candidateGuess_internal
    (code :
      Fin
        (3 ^
          NeighborhoodGraph.Guess.Enumeration.movementCount
            workTapeCount horizon))
    (tape : TapeIndex workTapeCount)
    (requested interval current : ℕ)
    (hinterval : interval ≤ horizon)
    (hcurrent :
      derivedCenterValue workTapeCount code.val tape.val interval =
        some current) :
    priorSearchValue
        workTapeCount code.val tape.val requested interval =
      match
        NeighborhoodGraph.Guess.CenterGuess.previousInterval
          (NeighborhoodGraph.Guess.Enumeration.candidateGuess code)
          tape requested interval with
      | none => some none
      | some previous =>
          match
            NeighborhoodGraph.Guess.CenterGuess.derivedCenter
              (NeighborhoodGraph.Guess.Enumeration.candidateGuess code)
              tape previous.val with
          | none => none
          | some center => some (some (previous.val, center)) := by
  have hvalid :
      ∀ boundary, boundary < interval →
        ∃ center,
          derivedCenterValue workTapeCount code.val tape.val boundary =
            some center := by
    intro boundary hboundary
    exact derivedCenterValue_prefix
      workTapeCount code.val tape.val interval current hcurrent
      boundary (by omega)
  have hnotNone :=
    priorSearchValue_ne_none
      workTapeCount code.val tape.val requested interval hvalid
  generalize hsearch :
    priorSearchValue
      workTapeCount code.val tape.val requested interval = result
  cases result with
  | none =>
      exact (hnotNone hsearch).elim
  | some result =>
      cases result with
      | none =>
          have hnoMatch :=
            priorSearchValue_some_none_no_match
              workTapeCount code.val tape.val requested interval
              hsearch
          have hprevious :=
            candidateGuess_previousInterval_eq_none
              code tape requested interval hinterval hnoMatch
          rw [hprevious]
      | some result =>
          rcases result with ⟨boundary, center⟩
          rcases priorSearchValue_some_some_maximal
              workTapeCount code.val tape.val requested interval
              boundary center hsearch with
            ⟨hboundary, hcenter, hcontains, hmaximal⟩
          have hprevious :=
            candidateGuess_previousInterval_eq_some
              code tape requested interval boundary center
              hinterval hboundary hcenter hcontains hmaximal
          rw [hprevious]
          simp only
          rw [← derivedCenterValue_candidateGuess_internal
            code tape boundary (by omega)]
          rw [hcenter]

theorem priorQueryValue_candidateGuess_internal
    (code :
      Fin
        (3 ^
          NeighborhoodGraph.Guess.Enumeration.movementCount
            workTapeCount horizon))
    (tape : TapeIndex workTapeCount)
    (slot : NeighborhoodGraph.Slot)
    (interval : ℕ) (hinterval : interval < horizon)
    (current : ℕ)
    (hcurrent :
      derivedCenterValue workTapeCount code.val tape.val interval =
        some current) :
    priorQueryValue
        (horizon := horizon) tape
        (NeighborhoodGraph.neighborBlock current slot)
        (priorSearchValue
          workTapeCount code.val tape.val
          (NeighborhoodGraph.neighborBlock current slot) interval) =
      match
        NeighborhoodGraph.Guess.CenterGuess.contentPredecessor?
          (NeighborhoodGraph.Guess.Enumeration.candidateGuess code)
          ⟨interval, hinterval⟩ tape slot with
      | none => .failure
      | some node => .graph node := by
  rw [priorSearchValue_candidateGuess_internal
    code tape (NeighborhoodGraph.neighborBlock current slot) interval
    current (by omega) hcurrent]
  unfold NeighborhoodGraph.Guess.CenterGuess.contentPredecessor?
  rw [← derivedCenterValue_candidateGuess_internal
    code tape interval (by omega)]
  rw [hcurrent]
  generalize hprevious :
    NeighborhoodGraph.Guess.CenterGuess.previousInterval
      (NeighborhoodGraph.Guess.Enumeration.candidateGuess code)
      tape (NeighborhoodGraph.neighborBlock current slot) interval =
        previous
  cases previous with
  | none =>
      simp [priorQueryValue, hprevious]
  | some previous =>
      generalize hcenter :
        NeighborhoodGraph.Guess.CenterGuess.derivedCenter
          (NeighborhoodGraph.Guess.Enumeration.candidateGuess code)
          tape previous.val = result
      cases result <;> simp [priorQueryValue, hprevious, hcenter]

theorem priorQueryValue_predecessorAt_internal
    (code :
      Fin
        (3 ^
          NeighborhoodGraph.Guess.Enumeration.movementCount
            workTapeCount horizon))
    (tape : TapeIndex workTapeCount)
    (slot : NeighborhoodGraph.Slot)
    (interval : ℕ) (hinterval : interval < horizon)
    (current : ℕ)
    (hcurrent :
      derivedCenterValue workTapeCount code.val tape.val interval =
        some current) :
    priorQueryValue
        (horizon := horizon) tape
        (NeighborhoodGraph.neighborBlock current slot)
        (priorSearchValue
          workTapeCount code.val tape.val
          (NeighborhoodGraph.neighborBlock current slot) interval) =
      match
        NeighborhoodGraph.Guess.CenterGuess.predecessorAt?
          (NeighborhoodGraph.Guess.Enumeration.candidateGuess code)
          ⟨interval, hinterval⟩
          (NeighborhoodGraph.predecessorIndexEquiv workTapeCount
            (.content slot, tape)) with
      | none => .failure
      | some node => .graph node := by
  rw [priorQueryValue_candidateGuess_internal
    code tape slot interval hinterval current hcurrent]
  simp [NeighborhoodGraph.Guess.CenterGuess.predecessorAt?,
    NeighborhoodGraph.Guess.CenterGuess.predecessor?]

theorem priorQueryValue_childAt_internal
    (code :
      Fin
        (3 ^
          NeighborhoodGraph.Guess.Enumeration.movementCount
            workTapeCount horizon))
    (parentTape tape : TapeIndex workTapeCount)
    (parentSlot slot : NeighborhoodGraph.Slot)
    (interval : ℕ) (hinterval : interval < horizon)
    (current : ℕ)
    (hcurrent :
      derivedCenterValue workTapeCount code.val tape.val interval =
        some current) :
    priorQueryValue
        (horizon := horizon) tape
        (NeighborhoodGraph.neighborBlock current slot)
        (priorSearchValue
          workTapeCount code.val tape.val
          (NeighborhoodGraph.neighborBlock current slot) interval) =
      NeighborhoodEvaluator.childAt
        (NeighborhoodGraph.Guess.Enumeration.candidateGuess code)
        (.graph
          (.computation parentTape parentSlot interval))
        (NeighborhoodGraph.predecessorIndexEquiv workTapeCount
          (.content slot, tape)) := by
  rw [priorQueryValue_candidateGuess_internal
    code tape slot interval hinterval current hcurrent]
  simp [NeighborhoodEvaluator.childAt, hinterval,
    NeighborhoodGraph.Guess.CenterGuess.predecessorAt?,
    NeighborhoodGraph.Guess.CenterGuess.predecessor?]
  congr 2

theorem priorQueryValue_frameChild_internal
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (code :
      Fin
        (3 ^
          NeighborhoodGraph.Guess.Enumeration.movementCount
            workTapeCount instanceData.horizon))
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (parentTape tape : TapeIndex workTapeCount)
    (parentSlot slot : NeighborhoodGraph.Slot)
    (interval : ℕ)
    (hinterval : interval < instanceData.horizon)
    (current : ℕ)
    (hcurrent :
      derivedCenterValue
          workTapeCount code.val tape.val interval =
        some current)
    (hguess :
      instanceData.guess =
        NeighborhoodGraph.Guess.Enumeration.candidateGuess code)
    (hnode :
      frame.node =
        .graph (.computation parentTape parentSlot interval)) :
    priorQueryValue
        (horizon := instanceData.horizon) tape
        (NeighborhoodGraph.neighborBlock current slot)
        (priorSearchValue
          workTapeCount code.val tape.val
          (NeighborhoodGraph.neighborBlock current slot) interval) =
      NeighborhoodScheduler.Frame.childNode frame
        (NeighborhoodGraph.predecessorIndexEquiv workTapeCount
          (.content slot, tape)) := by
  rw [NeighborhoodScheduler.Frame.childNode, hnode, hguess]
  exact priorQueryValue_childAt_internal
    code parentTape tape parentSlot slot interval hinterval current hcurrent

theorem chronologicalQueryValue_candidateGuess_internal
    (code :
      Fin
        (3 ^
          NeighborhoodGraph.Guess.Enumeration.movementCount
            workTapeCount horizon))
    (tape : TapeIndex workTapeCount)
    (interval : ℕ) (hinterval : interval < horizon)
    (result : Option ℕ)
    (hresult :
      derivedCenterValue workTapeCount code.val tape.val interval =
        result) :
    chronologicalQueryValue
        (horizon := horizon) tape interval result =
      match
        NeighborhoodGraph.Guess.CenterGuess.chronologicalPredecessor?
          (NeighborhoodGraph.Guess.Enumeration.candidateGuess code)
          ⟨interval, hinterval⟩ tape with
      | none => .failure
      | some node => .graph node := by
  unfold
    NeighborhoodGraph.Guess.CenterGuess.chronologicalPredecessor?
  rw [← derivedCenterValue_candidateGuess_internal
    code tape interval (by omega)]
  rw [hresult]
  cases result <;> cases interval <;> rfl

theorem chronologicalQueryValue_childAt_internal
    (code :
      Fin
        (3 ^
          NeighborhoodGraph.Guess.Enumeration.movementCount
            workTapeCount horizon))
    (parentTape tape : TapeIndex workTapeCount)
    (parentSlot : NeighborhoodGraph.Slot)
    (interval : ℕ) (hinterval : interval < horizon)
    (result : Option ℕ)
    (hresult :
      derivedCenterValue workTapeCount code.val tape.val interval =
        result) :
    chronologicalQueryValue
        (horizon := horizon) tape interval result =
      NeighborhoodEvaluator.childAt
        (NeighborhoodGraph.Guess.Enumeration.candidateGuess code)
        (.graph
          (.computation parentTape parentSlot interval))
        (NeighborhoodGraph.predecessorIndexEquiv workTapeCount
          (.chronological, tape)) := by
  rw [chronologicalQueryValue_candidateGuess_internal
    code tape interval hinterval result hresult]
  simp [NeighborhoodEvaluator.childAt, hinterval,
    NeighborhoodGraph.Guess.CenterGuess.predecessorAt?,
    NeighborhoodGraph.Guess.CenterGuess.predecessor?]
  congr 2

theorem chronologicalQueryValue_frameChild_internal
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (code :
      Fin
        (3 ^
          NeighborhoodGraph.Guess.Enumeration.movementCount
            workTapeCount instanceData.horizon))
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (parentTape tape : TapeIndex workTapeCount)
    (parentSlot : NeighborhoodGraph.Slot)
    (interval : ℕ)
    (hinterval : interval < instanceData.horizon)
    (result : Option ℕ)
    (hresult :
      derivedCenterValue
          workTapeCount code.val tape.val interval =
        result)
    (hguess :
      instanceData.guess =
        NeighborhoodGraph.Guess.Enumeration.candidateGuess code)
    (hnode :
      frame.node =
        .graph (.computation parentTape parentSlot interval)) :
    chronologicalQueryValue
        (horizon := instanceData.horizon) tape interval result =
      NeighborhoodScheduler.Frame.childNode frame
        (NeighborhoodGraph.predecessorIndexEquiv workTapeCount
          (.chronological, tape)) := by
  rw [NeighborhoodScheduler.Frame.childNode, hnode, hguess]
  exact chronologicalQueryValue_childAt_internal
    code parentTape tape parentSlot interval hinterval result hresult

private theorem initializeMovement_runs
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store) (word index : ℕ)
    (hguess : store controller.guess = word)
    (hindex : store (movementIndex regs) = index) :
    ∃ final,
      Runs (initializeMovement controller regs) store final ∧
      final (movementDivision regs).value = word ∧
      final (movementDivision regs).divisor = 3 ∧
      final (movementIndex regs) = index := by
  let final := Basic.execList
    [.imm (movementDivision regs).divisor 3,
      .imm (movementDivision regs).value 0,
      .add (movementDivision regs).value controller.guess
        (movementDivision regs).value] store
  have hvalueGuess :
      (movementDivision regs).value ≠ controller.guess :=
    regs.index_ne_controller (movementMap 0) 2
  have hdivisorGuess :
      (movementDivision regs).divisor ≠ controller.guess :=
    regs.index_ne_controller (movementMap 4) 2
  have hvalueDivisor :
      (movementDivision regs).value ≠
        (movementDivision regs).divisor :=
    division_index_ne regs (by decide)
  refine ⟨final, ?_, ?_, ?_, ?_⟩
  · simpa [initializeMovement] using
      basics_runs
        [.imm (movementDivision regs).divisor 3,
          .imm (movementDivision regs).value 0,
          .add (movementDivision regs).value controller.guess
            (movementDivision regs).value] store
  · simp [final, Basic.execList, Basic.exec,
      Ne.symm hvalueGuess, Ne.symm hdivisorGuess, hguess]
  · simp [final, Basic.execList, Basic.exec,
      Ne.symm hvalueDivisor]
  · simp [final, Basic.execList, Basic.exec, hindex,
      (division_index_ne_movementIndex regs 0).symm,
      (division_index_ne_movementIndex regs 4).symm]

private theorem seekMovementDigit_runs
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store) (word count : ℕ)
    (hword : store (movementDivision regs).value = word)
    (hcount : store (movementIndex regs) = count)
    (hdivisor : store (movementDivision regs).divisor = 3) :
    ∃ final,
      Runs (seekMovementDigit regs) store final ∧
      final (movementDivision regs).value =
        ternarySuffix word count ∧
      final (movementIndex regs) = 0 ∧
      final (movementDivision regs).divisor = 3 := by
  induction count generalizing store word with
  | zero =>
      refine ⟨store, ?_, ?_, hcount, hdivisor⟩
      · exact Runs.whileZero hcount
      · simpa [ternarySuffix] using hword
  | succ count ih =>
      have hcountNonzero :
          store (movementIndex regs) ≠ 0 := by
        rw [hcount]
        omega
      obtain ⟨divided, hdivideRun, hdividePost⟩ :=
        ControlDecode.divRem_runs (movementDivision regs)
          store 3 word (by omega) hword hdivisor
      have hdividedCount :
          divided (movementIndex regs) = count + 1 := by
        rw [hdividePost.eq_outside (movementIndex regs)
          (movementIndex_not_mem_division regs), hcount]
      obtain ⟨copied, hcopyRun, hcopiedValue, hcopyOutside⟩ :=
        copy_runs (movementDivision regs).value
          (movementDivision regs).quotient divided
          (division_index_ne regs (by decide))
      let decremented :=
        (Basic.sub (movementIndex regs) (movementIndex regs)
          (movementDivision regs).one).exec copied
      have hcopiedCount :
          copied (movementIndex regs) = count + 1 := by
        rw [hcopyOutside _
          (division_index_ne_movementIndex regs 0).symm,
          hdividedCount]
      have hcopiedOne :
          copied (movementDivision regs).one = 1 := by
        rw [hcopyOutside _ (division_index_ne regs
          (first := 3) (second := 0) (by decide))]
        exact hdividePost.one_eq
      have hdecrementedValue :
          decremented (movementDivision regs).value = word / 3 := by
        simp [decremented, Basic.exec,
          division_index_ne_movementIndex,
          hcopiedValue, hdividePost.quotient_eq]
      have hdecrementedCount :
          decremented (movementIndex regs) = count := by
        simp [decremented, Basic.exec, hcopiedCount, hcopiedOne]
      have hdecrementedDivisor :
          decremented (movementDivision regs).divisor = 3 := by
        simp [decremented, Basic.exec,
          division_index_ne_movementIndex]
        rw [hcopyOutside _
          (division_index_ne regs
            (first := 4) (second := 0) (by decide))]
        exact hdividePost.divisor_eq
      obtain ⟨final, hloopRun, hfinalValue, hfinalCount,
          hfinalDivisor⟩ :=
        ih decremented (word / 3) hdecrementedValue
          hdecrementedCount hdecrementedDivisor
      have hbody :
          Runs (dropMovementDigit regs) store decremented := by
        simpa [dropMovementDigit, Cmd.seqList] using
          Runs.seq hdivideRun
            (Runs.seq hcopyRun
              (Runs.basic
                (Basic.sub (movementIndex regs)
                  (movementIndex regs)
                  (movementDivision regs).one) copied))
      refine ⟨final,
        Runs.whileNonzero hcountNonzero hbody hloopRun,
        ?_, hfinalCount, hfinalDivisor⟩
      simpa [ternarySuffix] using hfinalValue

theorem movementDigit_writesWithin_internal
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (movementFootprint regs)
      (movementDigit controller regs) := by
  simp only [movementDigit, Cmd.seqList,
    Footprint.CmdWritesWithin]
  refine ⟨?_, ?_, movementDivision_writesWithin regs⟩
  · simp [initializeMovement, Cmd.basics, Cmd.seqList,
      Footprint.CmdWritesWithin, Footprint.BasicWritesWithin,
      movementFootprint, movementDivision, movementMap]
  · simp only [seekMovementDigit, Footprint.CmdWritesWithin,
      dropMovementDigit, Cmd.seqList]
    refine ⟨movementDivision_writesWithin regs, ?_, ?_⟩
    · apply cmdWritesWithin_mono
        (small := {(movementDivision regs).value})
      · simp [ControlDecode.copy, Footprint.CmdWritesWithin,
          Footprint.BasicWritesWithin]
      · intro address haddress
        simp only [Finset.mem_singleton] at haddress
        subst address
        simp [movementFootprint, movementDivision, movementMap]
    · change movementIndex regs ∈ movementFootprint regs
      exact Finset.mem_image.mpr ⟨5, Finset.mem_univ _, rfl⟩

private theorem movementDigit_runs_core
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store) (word index : ℕ)
    (hguess : store controller.guess = word)
    (hindex : store (movementIndex regs) = index) :
    ∃ final,
      Runs (movementDigit controller regs) store final ∧
      MovementDigitPost controller regs word index store final := by
  obtain ⟨initialized, hinitializeRun, hinitializedWord,
      hinitializedDivisor, hinitializedIndex⟩ :=
    initializeMovement_runs controller regs store word index
      hguess hindex
  obtain ⟨sought, hseekRun, hsoughtWord, hsoughtIndex,
      hsoughtDivisor⟩ :=
    seekMovementDigit_runs regs initialized word index
      hinitializedWord hinitializedIndex hinitializedDivisor
  obtain ⟨final, hfinalRun, hfinalPost⟩ :=
    ControlDecode.divRem_runs (movementDivision regs) sought 3
      (ternarySuffix word index) (by omega) hsoughtWord
      hsoughtDivisor
  have hrun :
      Runs (movementDigit controller regs) store final := by
    simpa [movementDigit, Cmd.seqList] using
      Runs.seq hinitializeRun (Runs.seq hseekRun hfinalRun)
  refine ⟨final, hrun, ?_⟩
  refine
    { value_eq := ?_
      index_eq := ?_
      divisor_eq := hfinalPost.divisor_eq
      one_eq := hfinalPost.one_eq
      test_eq := hfinalPost.test_eq
      guess_eq := ?_
      eq_outside := ?_ }
  · simpa [movementDigitValue] using hfinalPost.value_eq
  · rw [hfinalPost.eq_outside (movementIndex regs)
      (movementIndex_not_mem_division regs)]
    exact hsoughtIndex
  · calc
      final controller.guess = store controller.guess :=
        Footprint.runs_eq_outside
          (movementDigit_writesWithin_internal controller regs) hrun
          (by
            intro hmem
            simp only [movementFootprint, Finset.mem_image,
              Finset.mem_univ, true_and] at hmem
            obtain ⟨slot, hslot⟩ := hmem
            exact regs.index_ne_controller (movementMap slot) 2
              hslot)
      _ = word := hguess
  · intro address haddress
    exact Footprint.runs_eq_outside
      (movementDigit_writesWithin_internal controller regs)
      hrun haddress

theorem decodeChildIndex_writesWithin_internal
    (workTapeCount : ℕ)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (movementFootprint regs)
      (decodeChildIndex workTapeCount regs) := by
  simp only [decodeChildIndex, Cmd.seqList,
    Footprint.CmdWritesWithin]
  refine ⟨?_, copy_movement_writesWithin regs _, ?_⟩
  · change (movementDivision regs).divisor ∈
      movementFootprint regs
    simp [movementFootprint, movementDivision, movementMap]
  · exact movementDivision_writesWithin regs

theorem decodeChildIndex_runs_internal
    (workTapeCount child : ℕ)
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store)
    (hchild : store (savedChildIndex regs) = child) :
    ∃ final,
      Runs (decodeChildIndex workTapeCount regs) store final ∧
      ChildIndexPost workTapeCount child regs store final := by
  let initialized :=
    (Basic.imm (movementDivision regs).divisor
      (workTapeCount + 2)).exec store
  have hinitializedChild :
      initialized (savedChildIndex regs) = child := by
    simp [initialized, Basic.exec, savedChildIndex,
      movementDivision, movementMap, hchild, regs.injective.eq_iff]
  obtain ⟨copied, hcopyRun, hcopiedValue, hcopyOutside⟩ :=
    copy_runs (movementDivision regs).value
      (savedChildIndex regs) initialized
      (by
        exact regs.injective.ne (by decide))
  have hcopiedDivisor :
      copied (movementDivision regs).divisor =
        workTapeCount + 2 := by
    rw [hcopyOutside _
      (division_index_ne regs
        (first := 4) (second := 0) (by decide))]
    simp [initialized, Basic.exec]
  obtain ⟨final, hdivideRun, hdividePost⟩ :=
    ControlDecode.divRem_runs (movementDivision regs) copied
      (workTapeCount + 2) child (by omega)
      (by simpa [hinitializedChild] using hcopiedValue)
      hcopiedDivisor
  have hrun :
      Runs (decodeChildIndex workTapeCount regs) store final := by
    simpa [decodeChildIndex, Cmd.seqList] using
      Runs.seq
        (Runs.basic
          (Basic.imm (movementDivision regs).divisor
            (workTapeCount + 2)) store)
        (Runs.seq hcopyRun hdivideRun)
  refine ⟨final, hrun, ?_⟩
  refine
    { tape_eq := hdividePost.value_eq
      kind_eq := hdividePost.quotient_eq
      child_eq := ?_
      divisor_eq := hdividePost.divisor_eq
      one_eq := hdividePost.one_eq
      eq_outside := ?_ }
  · calc
      final (savedChildIndex regs) =
          copied (savedChildIndex regs) :=
        hdividePost.eq_outside _
          (by
            simp [ControlDecode.DivisionRegisters.writeFootprint,
              savedChildIndex, movementDivision, movementMap,
              regs.injective.eq_iff])
      _ = initialized (savedChildIndex regs) :=
        hcopyOutside _ (by
          exact regs.injective.ne (by decide))
      _ = child := hinitializedChild
  · intro address haddress
    exact Footprint.runs_eq_outside
      (decodeChildIndex_writesWithin_internal workTapeCount regs)
      hrun haddress

theorem encodeNodeFields_writesWithin_internal
    (regs : NeighborhoodTrial.Registers controller)
    (tag : ℕ) :
    Footprint.CmdWritesWithin (nodeEncodingFootprint regs)
      (encodeNodeFields regs tag) := by
  simp [encodeNodeFields, encodeNodeFieldsOps, Cmd.basics,
    Cmd.seqList, Footprint.CmdWritesWithin,
    Footprint.BasicWritesWithin, nodeEncodingFootprint]

theorem nodeEncodingFootprint_subset_layout_internal
    (regs : NeighborhoodTrial.Registers controller) :
    nodeEncodingFootprint regs ⊆ regs.layout.footprint := by
  intro address haddress
  simp only [nodeEncodingFootprint, Finset.mem_insert,
    Finset.mem_singleton] at haddress
  rcases haddress with haddress | haddress
  · rw [haddress]
    exact Layout.index_mem_layout_footprint regs 23
  · rw [haddress]
    exact Layout.index_mem_layout_footprint regs 30

theorem encodeNodeFields_runs_internal
    (regs : NeighborhoodTrial.Registers controller)
    (tag : ℕ) (store : Store) :
    ∃ final,
      Runs (encodeNodeFields regs tag) store final ∧
      EncodeNodeFieldsPost regs tag store final := by
  let final :=
    Basic.execList (encodeNodeFieldsOps regs tag) store
  have hrun :
      Runs (encodeNodeFields regs tag) store final := by
    exact basics_runs _ _
  refine ⟨final, hrun, ?_⟩
  refine
    { nodeCode_eq := ?_
      codecDigit_eq := ?_
      eq_outside := ?_ }
  · simp [final, encodeNodeFieldsOps, Basic.execList, Basic.exec,
      nodeFieldValue, regs.injective.eq_iff]
  · simp [final, encodeNodeFieldsOps, Basic.execList, Basic.exec,
      regs.injective.eq_iff]
  · intro address haddress
    exact Footprint.runs_eq_outside
      (encodeNodeFields_writesWithin_internal regs tag)
      hrun haddress

private theorem movementFootprint_subset_center
    (regs : NeighborhoodTrial.Registers controller) :
    movementFootprint regs ⊆ centerFootprint regs :=
  fun _ haddress => Finset.mem_union_left _ haddress

private theorem center_index_mem
    (regs : NeighborhoodTrial.Registers controller)
    (slot : Fin 5) :
    regs.index (centerMap slot) ∈ centerFootprint regs := by
  apply Finset.mem_union_right
  exact Finset.mem_image.mpr ⟨slot, Finset.mem_univ _, rfl⟩

private theorem copy_center_writesWithin
    (regs : NeighborhoodTrial.Registers controller)
    (destination : Fin 5) (source : ℕ) :
    Footprint.CmdWritesWithin (centerFootprint regs)
      (ControlDecode.copy (regs.index (centerMap destination)) source) := by
  apply cmdWritesWithin_mono
    (small := {regs.index (centerMap destination)})
  · simp [ControlDecode.copy, Footprint.CmdWritesWithin,
      Footprint.BasicWritesWithin]
  · intro address haddress
    simp only [Finset.mem_singleton] at haddress
    subst address
    exact center_index_mem regs destination

private theorem advanceCenter_writesWithin
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (centerFootprint regs)
      (advanceCenter regs) := by
  simp [advanceCenter, Cmd.basics, Cmd.seqList,
    Footprint.CmdWritesWithin, Footprint.BasicWritesWithin,
    center_index_mem]

private theorem invalidateCenter_writesWithin
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (centerFootprint regs)
      (invalidateCenter regs) := by
  simp [invalidateCenter, Cmd.basics, Cmd.seqList,
    Footprint.CmdWritesWithin, Footprint.BasicWritesWithin,
    center_index_mem]

private theorem applySelectedMovement_writesWithin
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (centerFootprint regs)
      (applySelectedMovement regs) := by
  simp only [applySelectedMovement, applyLeftMovement,
    applyNonleftMovement, Footprint.CmdWritesWithin]
  refine ⟨⟨invalidateCenter_writesWithin regs, ?_⟩, ?_⟩
  · exact ⟨center_index_mem regs 1,
      advanceCenter_writesWithin regs⟩
  · refine ⟨?_, advanceCenter_writesWithin regs, ?_⟩
    · apply Finset.mem_union_left
      simp [movementFootprint, movementDivision, movementMap]
    · exact ⟨center_index_mem regs 1,
        advanceCenter_writesWithin regs⟩

private theorem applySelectedMovement_runs
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store)
    (digit center remaining index stride : ℕ)
    (hdigit :
      store (movementDivision regs).value = digit)
    (hone : store (movementDivision regs).one = 1)
    (hcenter : store (centerValue regs) = center)
    (hvalid : store (centerValid regs) = 1)
    (hremaining : store (centerRemaining regs) = remaining)
    (hindex : store (centerNextIndex regs) = index)
    (hstride : store (centerStride regs) = stride) :
    ∃ final,
      Runs (applySelectedMovement regs) store final ∧
      let result := applyMovementDigit digit center
      final (centerValid regs) = centerValidValue result ∧
      final (centerValue regs) = centerOutputValue result ∧
      final (centerRemaining regs) =
        centerRemainingValue remaining result ∧
      final (centerNextIndex regs) =
        centerNextIndexValue index stride result ∧
      final (movementDivision regs).one = 1 ∧
      final (centerStride regs) = stride := by
  by_cases hdigitZero : digit = 0
  · have hvalueZero :
        store (movementDivision regs).value = 0 := by
      rw [hdigit, hdigitZero]
    by_cases hcenterZero : center = 0
    · have hstoredCenterZero :
          store (centerValue regs) = 0 := by
        rw [hcenter, hcenterZero]
      let final :=
        Basic.execList
          [.imm (centerValid regs) 0,
            .imm (centerRemaining regs) 0] store
      have hbranch :
          Runs (invalidateCenter regs) store final := by
        simpa [invalidateCenter] using
          basics_runs
            [.imm (centerValid regs) 0,
              .imm (centerRemaining regs) 0] store
      have hrun :
          Runs (applySelectedMovement regs) store final := by
        exact Runs.ifZero hvalueZero
          (Runs.ifZero hstoredCenterZero hbranch)
      refine ⟨final, hrun, ?_⟩
      simp [applyMovementDigit, hdigitZero, hcenterZero,
        centerValidValue, centerOutputValue,
        centerRemainingValue, centerNextIndexValue, final,
        Basic.execList, Basic.exec, hcenter, hindex,
        hstride, centerMap, movementDivision, movementMap,
        regs.injective.eq_iff]
      exact hone
    · let decreased :=
        (Basic.sub (centerValue regs) (centerValue regs)
          (movementDivision regs).one).exec store
      let final :=
        Basic.execList
          [.add (centerNextIndex regs)
              (centerNextIndex regs) (centerStride regs),
            .sub (centerRemaining regs)
              (centerRemaining regs) (movementDivision regs).one]
          decreased
      have hstoredCenterNonzero :
          store (centerValue regs) ≠ 0 := by
        rw [hcenter]
        exact hcenterZero
      have hbranch :
          Runs (applyLeftMovement regs) store final := by
        apply Runs.ifNonzero hstoredCenterNonzero
        apply Runs.seq
          (Runs.basic
            (.sub (centerValue regs) (centerValue regs)
              (movementDivision regs).one) store)
        simpa [advanceCenter] using
          basics_runs
            [.add (centerNextIndex regs)
                (centerNextIndex regs) (centerStride regs),
              .sub (centerRemaining regs)
                (centerRemaining regs)
                (movementDivision regs).one] decreased
      have hrun :
          Runs (applySelectedMovement regs) store final :=
        Runs.ifZero hvalueZero hbranch
      refine ⟨final, hrun, ?_⟩
      simp [applyMovementDigit, hdigitZero, hcenterZero,
        centerValidValue, centerOutputValue,
        centerRemainingValue, centerNextIndexValue, final,
        decreased, Basic.execList, Basic.exec, hcenter, hvalid,
        hremaining, hindex, hstride, centerMap,
        movementDivision, movementMap, regs.injective.eq_iff]
      refine ⟨?_, ?_, ?_⟩
      · exact congrArg (fun value => center - value) hone
      · exact congrArg (fun value => remaining - value) hone
      · exact hone
  · have hvalueNonzero :
        store (movementDivision regs).value ≠ 0 := by
      rw [hdigit]
      exact hdigitZero
    let tested :=
      (Basic.sub (movementDivision regs).test
        (movementDivision regs).value
        (movementDivision regs).one).exec store
    have htested :
        tested (movementDivision regs).test = digit - 1 := by
      simp [tested, Basic.exec, hdigit, hone]
    by_cases hdigitOne : digit = 1
    · have htestedZero :
          tested (movementDivision regs).test = 0 := by
        rw [htested, hdigitOne]
      let final :=
        Basic.execList
          [.add (centerNextIndex regs)
              (centerNextIndex regs) (centerStride regs),
            .sub (centerRemaining regs)
              (centerRemaining regs) (movementDivision regs).one]
          tested
      have hadvance :
          Runs (advanceCenter regs) tested final := by
        simpa [advanceCenter] using
          basics_runs
            [.add (centerNextIndex regs)
                (centerNextIndex regs) (centerStride regs),
              .sub (centerRemaining regs)
                (centerRemaining regs)
                (movementDivision regs).one] tested
      have hbranch :
          Runs (applyNonleftMovement regs) store final := by
        exact Runs.seq
          (Runs.basic
            (.sub (movementDivision regs).test
              (movementDivision regs).value
              (movementDivision regs).one) store)
          (Runs.ifZero htestedZero hadvance)
      have hrun :
          Runs (applySelectedMovement regs) store final :=
        Runs.ifNonzero hvalueNonzero hbranch
      refine ⟨final, hrun, ?_⟩
      simp [applyMovementDigit, hdigitOne,
        centerValidValue, centerOutputValue,
        centerRemainingValue, centerNextIndexValue, final,
        tested, Basic.execList, Basic.exec, hcenter, hvalid,
        hremaining, hindex, hstride, centerMap,
        movementDivision, movementMap, regs.injective.eq_iff]
      exact ⟨congrArg (fun value => remaining - value) hone,
        hone⟩
    · have htestedNonzero :
          tested (movementDivision regs).test ≠ 0 := by
        rw [htested]
        omega
      let increased :=
        (Basic.add (centerValue regs) (centerValue regs)
          (movementDivision regs).one).exec tested
      let final :=
        Basic.execList
          [.add (centerNextIndex regs)
              (centerNextIndex regs) (centerStride regs),
            .sub (centerRemaining regs)
              (centerRemaining regs) (movementDivision regs).one]
          increased
      have hadvance :
          Runs (advanceCenter regs) increased final := by
        simpa [advanceCenter] using
          basics_runs
            [.add (centerNextIndex regs)
                (centerNextIndex regs) (centerStride regs),
              .sub (centerRemaining regs)
                (centerRemaining regs)
                (movementDivision regs).one] increased
      have hright :
          Runs
            (Cmd.seq
              (.basic
                (.add (centerValue regs) (centerValue regs)
                  (movementDivision regs).one))
              (advanceCenter regs))
            tested final :=
        Runs.seq
          (Runs.basic
            (.add (centerValue regs) (centerValue regs)
              (movementDivision regs).one) tested)
          hadvance
      have hbranch :
          Runs (applyNonleftMovement regs) store final := by
        exact Runs.seq
          (Runs.basic
            (.sub (movementDivision regs).test
              (movementDivision regs).value
              (movementDivision regs).one) store)
          (Runs.ifNonzero htestedNonzero hright)
      have hrun :
          Runs (applySelectedMovement regs) store final :=
        Runs.ifNonzero hvalueNonzero hbranch
      refine ⟨final, hrun, ?_⟩
      simp [applyMovementDigit, hdigitZero, hdigitOne,
        centerValidValue, centerOutputValue,
        centerRemainingValue, centerNextIndexValue, final,
        increased, tested, Basic.execList, Basic.exec, hcenter,
        hvalid, hremaining, hindex, hstride, centerMap,
        movementDivision, movementMap, regs.injective.eq_iff]
      exact ⟨hone,
        congrArg (fun value => remaining - value) hone,
        hone⟩

private theorem center_index_not_mem_movement
    (regs : NeighborhoodTrial.Registers controller)
    (slot : Fin 5) :
    regs.index (centerMap slot) ∉ movementFootprint regs := by
  simp only [movementFootprint, Finset.mem_image,
    Finset.mem_univ, true_and, not_exists]
  intro movementSlot heq
  have hslot := regs.injective heq
  fin_cases slot <;> fin_cases movementSlot <;>
    simp [centerMap, movementMap] at hslot

private theorem controller_guess_not_mem_center
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) :
    controller.guess ∉ centerFootprint regs := by
  intro haddress
  simp only [centerFootprint, Finset.mem_union,
    movementFootprint, Finset.mem_image, Finset.mem_univ,
    true_and] at haddress
  rcases haddress with ⟨slot, hslot⟩ | ⟨slot, hslot⟩
  · exact regs.index_ne_controller (movementMap slot) 2 hslot
  · exact regs.index_ne_controller (centerMap slot) 2 hslot

private theorem centerLoop_runs
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store)
    (word remaining index center stride : ℕ)
    (hguess : store controller.guess = word)
    (hremaining : store (centerRemaining regs) = remaining)
    (hindex : store (centerNextIndex regs) = index)
    (hcenter : store (centerValue regs) = center)
    (hvalid : store (centerValid regs) = 1)
    (hone : store (movementDivision regs).one = 1)
    (hstride : store (centerStride regs) = stride) :
    ∃ final,
      Runs
        (.whileNonzero (centerRemaining regs)
          (centerStep controller regs))
        store final ∧
      let result :=
        scanCenter word stride remaining index center
      final (centerValid regs) = centerValidValue result ∧
      final (centerValue regs) = centerOutputValue result ∧
      final (centerRemaining regs) = 0 ∧
      final (movementDivision regs).one = 1 ∧
      final (centerStride regs) = stride ∧
      final controller.guess = word := by
  induction remaining generalizing store index center with
  | zero =>
      refine ⟨store, Runs.whileZero hremaining, ?_⟩
      simp [scanCenter, hvalid, hcenter, hremaining, hstride,
        hguess, hone, centerValidValue, centerOutputValue]
  | succ remaining ih =>
      have hremainingNonzero :
          store (centerRemaining regs) ≠ 0 := by
        rw [hremaining]
        omega
      let copied :=
        Function.update store (movementIndex regs) index
      have hcopyRun :
          Runs
            (ControlDecode.copy
              (movementIndex regs) (centerNextIndex regs))
            store copied := by
        simpa [copied, hindex] using
          copy_update_runs store
            (regs.injective.ne (by decide :
              (19 : Fin 34) ≠ centerMap 4))
      have hcopiedGuess : copied controller.guess = word := by
        simp [copied,
          (regs.index_ne_controller (movementMap 5) 2).symm,
          hguess]
      have hcopiedMovementIndex :
          copied (movementIndex regs) = index := by
        simp [copied]
      obtain ⟨looked, hlookupRun, hlookupPost⟩ :=
        movementDigit_runs_core controller regs copied word index
          hcopiedGuess hcopiedMovementIndex
      let digit := movementDigitValue word index
      have hlookedDigit :
          looked (movementDivision regs).value = digit :=
        hlookupPost.value_eq
      have hlookedCenter :
          looked (centerValue regs) = center := by
        rw [hlookupPost.eq_outside _
          (center_index_not_mem_movement regs 1)]
        have hne :
            centerValue regs ≠ movementIndex regs :=
          regs.injective.ne (by decide)
        simpa [copied, hne] using hcenter
      have hlookedValid :
          looked (centerValid regs) = 1 := by
        rw [hlookupPost.eq_outside _
          (center_index_not_mem_movement regs 2)]
        have hne :
            centerValid regs ≠ movementIndex regs :=
          regs.injective.ne (by decide)
        simpa [copied, hne] using hvalid
      have hlookedRemaining :
          looked (centerRemaining regs) = remaining + 1 := by
        rw [hlookupPost.eq_outside _
          (center_index_not_mem_movement regs 3)]
        have hne :
            centerRemaining regs ≠ movementIndex regs :=
          regs.injective.ne (by decide)
        simpa [copied, hne] using hremaining
      have hlookedIndex :
          looked (centerNextIndex regs) = index := by
        rw [hlookupPost.eq_outside _
          (center_index_not_mem_movement regs 4)]
        have hne :
            centerNextIndex regs ≠ movementIndex regs :=
          regs.injective.ne (by decide)
        simpa [copied, hne] using hindex
      have hlookedStride :
          looked (centerStride regs) = stride := by
        rw [hlookupPost.eq_outside _
          (center_index_not_mem_movement regs 0)]
        have hne :
            centerStride regs ≠ movementIndex regs :=
          regs.injective.ne (by decide)
        simpa [copied, hne] using hstride
      obtain ⟨applied, happlyRun, happlyPost⟩ :=
        applySelectedMovement_runs regs looked digit center
          (remaining + 1) index stride hlookedDigit
          hlookupPost.one_eq hlookedCenter hlookedValid
          hlookedRemaining hlookedIndex hlookedStride
      dsimp only at happlyPost
      rcases happlyPost with
        ⟨happliedValid, happpliedCenter, happpliedRemaining,
          happpliedIndex, happpliedOne, happpliedStride⟩
      have hbody :
          Runs (centerStep controller regs) store applied := by
        simpa [centerStep, Cmd.seqList] using
          Runs.seq hcopyRun (Runs.seq hlookupRun happlyRun)
      have happliedGuess :
          applied controller.guess = word := by
        calc
          applied controller.guess = looked controller.guess :=
            Footprint.runs_eq_outside
              (applySelectedMovement_writesWithin regs)
              happlyRun
              (controller_guess_not_mem_center controller regs)
          _ = word := hlookupPost.guess_eq
      generalize hmovement :
        applyMovementDigit digit center = movementResult
      cases movementResult with
      | none =>
          have happliedRemainingZero :
              applied (centerRemaining regs) = 0 := by
            rw [happpliedRemaining, hmovement]
            rfl
          have hloop :=
            Runs.whileZero
              (body := centerStep controller regs)
              happliedRemainingZero
          refine ⟨applied,
            Runs.whileNonzero hremainingNonzero hbody hloop,
            ?_, ?_, happliedRemainingZero, happpliedOne,
            happpliedStride, happliedGuess⟩
          · simpa [scanCenter, digit, hmovement] using
              happliedValid
          · simpa [scanCenter, digit, hmovement] using
              happpliedCenter
      | some next =>
          have happliedValidOne :
              applied (centerValid regs) = 1 := by
            rw [happliedValid, hmovement]
            rfl
          have happliedCenterNext :
              applied (centerValue regs) = next := by
            rw [happpliedCenter, hmovement]
            rfl
          have happliedRemaining :
              applied (centerRemaining regs) = remaining := by
            rw [happpliedRemaining, hmovement]
            simp [centerRemainingValue]
          have happliedIndex :
              applied (centerNextIndex regs) = index + stride := by
            rw [happpliedIndex, hmovement]
            rfl
          obtain ⟨final, hloopRun, hfinalValid, hfinalCenter,
              hfinalRemaining, hfinalOne, hfinalStride,
              hfinalGuess⟩ :=
            ih applied (index + stride) next happliedGuess
              happliedRemaining happliedIndex happliedCenterNext
              happliedValidOne happpliedOne happpliedStride
          refine ⟨final,
            Runs.whileNonzero hremainingNonzero hbody hloopRun,
            ?_, ?_, hfinalRemaining, hfinalOne, hfinalStride,
            hfinalGuess⟩
          · simpa [scanCenter, digit, hmovement] using
              hfinalValid
          · simpa [scanCenter, digit, hmovement] using
              hfinalCenter

private theorem initializeCenter_writesWithin
    (workTapeCount : ℕ)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (centerFootprint regs)
      (initializeCenter workTapeCount regs) := by
  simp only [initializeCenter, Cmd.seqList,
    Footprint.CmdWritesWithin]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply Finset.mem_union_left
    simp [movementFootprint, movementDivision, movementMap]
  · change centerValue regs ∈ centerFootprint regs
    exact center_index_mem regs 1
  · change centerValid regs ∈ centerFootprint regs
    exact center_index_mem regs 2
  · exact copy_center_writesWithin regs 3 _
  · exact copy_center_writesWithin regs 4 _
  · change centerStride regs ∈ centerFootprint regs
    exact center_index_mem regs 0

private theorem initializeCenter_runs
    (workTapeCount : ℕ)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store) (word tape interval : ℕ)
    (hguess : store controller.guess = word)
    (htape : store (ControlDecode.nodeTape regs) = tape)
    (hinterval :
      store (ControlDecode.nodePayload1 regs) = interval) :
    ∃ final,
      Runs (initializeCenter workTapeCount regs) store final ∧
      final (centerValue regs) = 0 ∧
      final (centerValid regs) = 1 ∧
      final (centerRemaining regs) = interval ∧
      final (centerNextIndex regs) = tape ∧
      final (centerStride regs) = workTapeCount + 2 ∧
      final (movementDivision regs).one = 1 ∧
      final controller.guess = word := by
  let oneStore :=
    (Basic.imm (movementDivision regs).one 1).exec store
  let centered :=
    (Basic.imm (centerValue regs) 0).exec oneStore
  let validated :=
    (Basic.imm (centerValid regs) 1).exec centered
  let remainingStore :=
    Function.update validated (centerRemaining regs)
      (validated (ControlDecode.nodePayload1 regs))
  let indexed :=
    Function.update remainingStore (centerNextIndex regs)
      (remainingStore (ControlDecode.nodeTape regs))
  let final :=
    (Basic.imm (centerStride regs) (workTapeCount + 2)).exec
      indexed
  have hremainingRun :
      Runs
        (ControlDecode.copy
          (centerRemaining regs)
          (ControlDecode.nodePayload1 regs))
        validated remainingStore := by
    exact copy_update_runs validated
      (regs.injective.ne (by decide))
  have hindexRun :
      Runs
        (ControlDecode.copy
          (centerNextIndex regs)
          (ControlDecode.nodeTape regs))
        remainingStore indexed := by
    exact copy_update_runs remainingStore
      (regs.injective.ne (by decide))
  have hrun :
      Runs (initializeCenter workTapeCount regs) store final := by
    simpa [initializeCenter, Cmd.seqList] using
      Runs.seq
        (Runs.basic
          (.imm (movementDivision regs).one 1) store)
        (Runs.seq
          (Runs.basic (.imm (centerValue regs) 0) oneStore)
          (Runs.seq
            (Runs.basic (.imm (centerValid regs) 1) centered)
            (Runs.seq hremainingRun
              (Runs.seq hindexRun
                (Runs.basic
                  (.imm (centerStride regs) (workTapeCount + 2))
                  indexed)))))
  refine ⟨final, hrun, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [final, indexed, remainingStore, validated, centered,
      oneStore,
      Basic.exec, centerMap, regs.injective.eq_iff]
  · simp [final, indexed, remainingStore, validated, centered,
      oneStore,
      Basic.exec, centerMap, regs.injective.eq_iff]
  · simp [final, indexed, remainingStore, validated, centered,
      oneStore, Basic.exec, centerMap, regs.injective.eq_iff,
      ControlDecode.nodePayload1]
    change
      Function.update store (regs.index 17) 1 (regs.index 11) =
        interval
    rw [Function.update_of_ne
      (regs.injective.ne
        (by decide : (11 : Fin 34) ≠ 17))]
    exact hinterval
  · simp [final, indexed, remainingStore, validated, centered,
      oneStore, Basic.exec, centerMap, regs.injective.eq_iff,
      ControlDecode.nodeTape, ControlDecode.first]
    change
      Function.update store (regs.index 17) 1 (regs.index 9) =
        tape
    rw [Function.update_of_ne
      (regs.injective.ne
        (by decide : (9 : Fin 34) ≠ 17))]
    exact htape
  · simp [final, Basic.exec]
  · simp [final, indexed, remainingStore, validated, centered,
      oneStore, Basic.exec, centerMap, movementDivision,
      movementMap, regs.injective.eq_iff]
  · calc
      final controller.guess = store controller.guess :=
        Footprint.runs_eq_outside
          (initializeCenter_writesWithin workTapeCount regs)
          hrun (controller_guess_not_mem_center controller regs)
      _ = word := hguess

private theorem centerStep_writesWithin
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (centerFootprint regs)
      (centerStep controller regs) := by
  simp only [centerStep, Cmd.seqList,
    Footprint.CmdWritesWithin]
  refine ⟨?_, ?_, applySelectedMovement_writesWithin regs⟩
  · apply cmdWritesWithin_mono
      (small := {movementIndex regs})
    · simp [ControlDecode.copy, Footprint.CmdWritesWithin,
        Footprint.BasicWritesWithin]
    · intro address haddress
      simp only [Finset.mem_singleton] at haddress
      subst address
      apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨5, Finset.mem_univ _, rfl⟩
  · apply cmdWritesWithin_mono
      (movementDigit_writesWithin_internal controller regs)
    exact movementFootprint_subset_center regs

theorem deriveCenter_writesWithin_internal
    (workTapeCount : ℕ)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (centerFootprint regs)
      (deriveCenter workTapeCount controller regs) := by
  exact ⟨initializeCenter_writesWithin workTapeCount regs,
    centerStep_writesWithin controller regs⟩

theorem centerFootprint_subset_layout_internal
    (regs : NeighborhoodTrial.Registers controller) :
    centerFootprint regs ⊆ regs.layout.footprint := by
  intro address haddress
  simp only [centerFootprint, Finset.mem_union,
    movementFootprint, Finset.mem_image, Finset.mem_univ,
    true_and] at haddress
  rcases haddress with ⟨slot, rfl⟩ | ⟨slot, rfl⟩
  · exact Layout.index_mem_layout_footprint regs (movementMap slot)
  · exact Layout.index_mem_layout_footprint regs (centerMap slot)

private theorem nodeTape_not_mem_center
    (regs : NeighborhoodTrial.Registers controller) :
    ControlDecode.nodeTape regs ∉ centerFootprint regs := by
  simp only [centerFootprint, Finset.mem_union,
    movementFootprint, Finset.mem_image, Finset.mem_univ,
    true_and, not_or, not_exists]
  constructor
  · intro slot
    fin_cases slot <;>
      simp [movementMap, ControlDecode.nodeTape,
        ControlDecode.first, regs.injective.eq_iff]
  · intro slot
    fin_cases slot <;>
      simp [centerMap, ControlDecode.nodeTape,
        ControlDecode.first, regs.injective.eq_iff]

private theorem nodeInterval_not_mem_center
    (regs : NeighborhoodTrial.Registers controller) :
    ControlDecode.nodePayload1 regs ∉ centerFootprint regs := by
  simp only [centerFootprint, Finset.mem_union,
    movementFootprint, Finset.mem_image, Finset.mem_univ,
    true_and, not_or, not_exists]
  constructor
  · intro slot
    fin_cases slot <;>
      simp [movementMap, ControlDecode.nodePayload1,
        ControlDecode.third, regs.injective.eq_iff]
  · intro slot
    fin_cases slot <;>
      simp [centerMap, ControlDecode.nodePayload1,
        ControlDecode.third, regs.injective.eq_iff]

theorem deriveCenter_runs_internal
    (workTapeCount : ℕ)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store) (word tape interval : ℕ)
    (hguess : store controller.guess = word)
    (htape : store (ControlDecode.nodeTape regs) = tape)
    (hinterval :
      store (ControlDecode.nodePayload1 regs) = interval) :
    ∃ final,
      Runs (deriveCenter workTapeCount controller regs) store final ∧
      DeriveCenterPost workTapeCount word tape interval
        controller regs store final := by
  obtain ⟨initialized, hinitializeRun, hinitializedCenter,
      hinitializedValid, hinitializedRemaining, hinitializedIndex,
      hinitializedStride, hinitializedOne, hinitializedGuess⟩ :=
    initializeCenter_runs workTapeCount controller regs store
      word tape interval hguess htape hinterval
  obtain ⟨final, hloopRun, hfinalValid, hfinalCenter,
      hfinalRemaining, hfinalOne, hfinalStride, hfinalGuess⟩ :=
    centerLoop_runs controller regs initialized word interval tape 0
      (workTapeCount + 2) hinitializedGuess
      hinitializedRemaining hinitializedIndex hinitializedCenter
      hinitializedValid hinitializedOne hinitializedStride
  have hrun :
      Runs (deriveCenter workTapeCount controller regs) store final := by
    exact Runs.seq hinitializeRun hloopRun
  refine ⟨final, hrun, ?_⟩
  refine
    { valid_eq := ?_
      center_eq := ?_
      remaining_eq := hfinalRemaining
      one_eq := hfinalOne
      guess_eq := hfinalGuess
      tape_eq := ?_
      interval_eq := ?_
      eq_outside := ?_ }
  · simpa [derivedCenterValue] using hfinalValid
  · simpa [derivedCenterValue] using hfinalCenter
  · calc
      final (ControlDecode.nodeTape regs) =
          store (ControlDecode.nodeTape regs) :=
        Footprint.runs_eq_outside
          (deriveCenter_writesWithin_internal
            workTapeCount controller regs)
          hrun (nodeTape_not_mem_center regs)
      _ = tape := htape
  · calc
      final (ControlDecode.nodePayload1 regs) =
          store (ControlDecode.nodePayload1 regs) :=
        Footprint.runs_eq_outside
          (deriveCenter_writesWithin_internal
            workTapeCount controller regs)
          hrun (nodeInterval_not_mem_center regs)
      _ = interval := hinterval
  · intro address haddress
    exact Footprint.runs_eq_outside
      (deriveCenter_writesWithin_internal
        workTapeCount controller regs)
      hrun haddress

private theorem centerFootprint_subset_prior
    (regs : NeighborhoodTrial.Registers controller) :
    centerFootprint regs ⊆ priorFootprint regs :=
  Finset.subset_union_left.trans Finset.subset_union_left

private theorem prior_index_mem
    (regs : NeighborhoodTrial.Registers controller)
    (slot : Fin 5) :
    regs.index (priorMap slot) ∈ priorFootprint regs := by
  apply Finset.mem_union_right
  exact Finset.mem_image.mpr ⟨slot, Finset.mem_univ _, rfl⟩

private theorem nodeInterval_mem_prior
    (regs : NeighborhoodTrial.Registers controller) :
    ControlDecode.nodePayload1 regs ∈ priorFootprint regs := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

private theorem copy_prior_writesWithin
    (regs : NeighborhoodTrial.Registers controller)
    (slot : Fin 5) (source : ℕ) :
    Footprint.CmdWritesWithin (priorFootprint regs)
      (ControlDecode.copy (regs.index (priorMap slot)) source) := by
  apply cmdWritesWithin_mono
      (small := {regs.index (priorMap slot)})
  · simp [ControlDecode.copy, Footprint.CmdWritesWithin,
      Footprint.BasicWritesWithin]
  · intro address haddress
    simp only [Finset.mem_singleton] at haddress
    subst address
    exact prior_index_mem regs slot

private theorem copy_nodeInterval_writesWithin
    (regs : NeighborhoodTrial.Registers controller)
    (source : ℕ) :
    Footprint.CmdWritesWithin (priorFootprint regs)
      (ControlDecode.copy (ControlDecode.nodePayload1 regs) source) := by
  apply cmdWritesWithin_mono
      (small := {ControlDecode.nodePayload1 regs})
  · simp [ControlDecode.copy, Footprint.CmdWritesWithin,
      Footprint.BasicWritesWithin]
  · intro address haddress
    simp only [Finset.mem_singleton] at haddress
    subst address
    exact nodeInterval_mem_prior regs

private theorem recordPrior_writesWithin
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (priorFootprint regs)
      (recordPrior regs) := by
  simp only [recordPrior, Cmd.basics]
  exact
    ⟨prior_index_mem regs 2, prior_index_mem regs 3,
      prior_index_mem regs 3, prior_index_mem regs 4,
      prior_index_mem regs 4, prior_index_mem regs 1⟩

private theorem recordPrior_runs
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store) (candidate center : ℕ)
    (hcandidate :
      store (ControlDecode.nodePayload1 regs) = candidate)
    (hcenter : store (centerValue regs) = center) :
    ∃ final,
      Runs (recordPrior regs) store final ∧
      final (priorFound regs) = 1 ∧
      final (priorInterval regs) = candidate ∧
      final (priorCenter regs) = center ∧
      final (priorCountdown regs) = 0 ∧
      ∀ address,
        address ∉
          ({priorFound regs, priorInterval regs,
            priorCenter regs, priorCountdown regs} : Finset ℕ) →
        final address = store address := by
  let ops : List Basic :=
    [.imm (priorFound regs) 1,
      .imm (priorInterval regs) 0,
      .add (priorInterval regs)
        (ControlDecode.nodePayload1 regs) (priorInterval regs),
      .imm (priorCenter regs) 0,
      .add (priorCenter regs)
        (centerValue regs) (priorCenter regs),
      .imm (priorCountdown regs) 0]
  let final := Basic.execList ops store
  refine ⟨final, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [recordPrior, ops] using basics_runs ops store
  · simp [final, ops, Basic.execList, Basic.exec, priorMap,
      regs.injective.eq_iff]
  · simp [final, ops, Basic.execList, Basic.exec, priorMap,
      ControlDecode.nodePayload1, regs.injective.eq_iff,
      hcandidate]
  · simp [final, ops, Basic.execList, Basic.exec, priorMap,
      centerMap, regs.injective.eq_iff, hcenter]
  · simp [final, ops, Basic.execList, Basic.exec, priorMap,
      regs.injective.eq_iff]
  · intro address haddress
    simp only [Finset.mem_insert, Finset.mem_singleton,
      not_or] at haddress
    rcases haddress with
      ⟨hfound, hinterval, hcenterAddress, hcountdown⟩
    simp [final, ops, Basic.execList, Basic.exec,
      Function.update_of_ne, hfound, hinterval,
      hcenterAddress, hcountdown]

private theorem neighborhoodContains_iff_bounds
    (center requested : ℕ) :
    NeighborhoodGraph.NeighborhoodContains center requested ↔
      requested < center + 2 ∧ center < requested + 2 := by
  unfold NeighborhoodGraph.NeighborhoodContains
  omega

theorem recordPriorIfContains_runs_internal
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store)
    (center requested candidate countdown word tape : ℕ)
    (hcenter : store (centerValue regs) = center)
    (hrequested : store (requestedBlock regs) = requested)
    (hcandidate :
      store (ControlDecode.nodePayload1 regs) = candidate)
    (hcountdown : store (priorCountdown regs) = countdown)
    (hfound : store (priorFound regs) = 0)
    (hinterval : store (priorInterval regs) = 0)
    (hpriorCenter : store (priorCenter regs) = 0)
    (hvalid : store (centerValid regs) = 1)
    (hone : store (movementDivision regs).one = 1)
    (htape : store (ControlDecode.nodeTape regs) = tape)
    (hguess : store controller.guess = word) :
    ∃ final,
      Runs (recordPriorIfContains regs) store final ∧
      RecordPriorIfContainsPost regs center requested candidate
        countdown word tape final := by
  change store (regs.index 17) = 1 at hone
  let firstOps : List Basic :=
    [.imm (movementDivision regs).value 0,
      .add (movementDivision regs).value
        (centerValue regs) (movementDivision regs).value,
      .add (movementDivision regs).value
        (movementDivision regs).value (movementDivision regs).one,
      .add (movementDivision regs).value
        (movementDivision regs).value (movementDivision regs).one,
      .sub (movementDivision regs).test
        (movementDivision regs).value (requestedBlock regs)]
  let first := Basic.execList firstOps store
  have hfirstRun :
      Runs (Cmd.basics firstOps) store first := by
    exact basics_runs firstOps store
  have hfirstOutside
      (address : ℕ)
      (hvalue : address ≠ (movementDivision regs).value)
      (htest : address ≠ (movementDivision regs).test) :
      first address = store address := by
    simp [first, firstOps, Basic.execList, Basic.exec,
      Function.update_of_ne, hvalue, htest]
  have hfirstTest :
      first (movementDivision regs).test =
        center + 2 - requested := by
    simp [first, firstOps, Basic.execList, Basic.exec,
      movementDivision, movementMap, centerMap, priorMap,
      regs.injective.eq_iff, hcenter, hrequested]
    change
      center + store (regs.index 17) + store (regs.index 17) -
          requested =
        center + 2 - requested
    rw [hone]
  by_cases hleft : requested < center + 2
  · have hfirstNonzero :
        first (movementDivision regs).test ≠ 0 := by
      rw [hfirstTest]
      omega
    let secondOps : List Basic :=
      [.imm (movementDivision regs).value 0,
        .add (movementDivision regs).value
          (requestedBlock regs) (movementDivision regs).value,
        .add (movementDivision regs).value
          (movementDivision regs).value (movementDivision regs).one,
        .add (movementDivision regs).value
          (movementDivision regs).value (movementDivision regs).one,
        .sub (movementDivision regs).test
          (movementDivision regs).value (centerValue regs)]
    let second := Basic.execList secondOps first
    have hsecondRun :
        Runs (Cmd.basics secondOps) first second := by
      exact basics_runs secondOps first
    have hsecondOutside
        (address : ℕ)
        (hvalue : address ≠ (movementDivision regs).value)
        (htest : address ≠ (movementDivision regs).test) :
        second address = store address := by
      rw [show second address = first address by
        simp [second, secondOps, Basic.execList, Basic.exec,
          Function.update_of_ne, hvalue, htest]]
      exact hfirstOutside address hvalue htest
    have hfirstOne :
        first (regs.index 17) = 1 := by
      rw [hfirstOutside (regs.index 17)
        (regs.injective.ne
          (by decide : (17 : Fin 34) ≠ 0))
        (regs.injective.ne
          (by decide : (17 : Fin 34) ≠ 5))]
      exact hone
    have hfirstRequested :
        first (requestedBlock regs) = requested := by
      rw [hfirstOutside _
        (regs.injective.ne (by decide))
        (regs.injective.ne (by decide))]
      exact hrequested
    have hfirstCenter :
        first (centerValue regs) = center := by
      rw [hfirstOutside _
        (regs.injective.ne (by decide))
        (regs.injective.ne (by decide))]
      exact hcenter
    have hsecondTest :
        second (movementDivision regs).test =
          requested + 2 - center := by
      simp [second, secondOps, Basic.execList, Basic.exec,
        movementDivision, movementMap, centerMap, priorMap,
        regs.injective.eq_iff, hfirstRequested,
        hfirstCenter]
      change
        requested + first (regs.index 17) +
              first (regs.index 17) -
            center =
          requested + 2 - center
      rw [hfirstOne]
    by_cases hright : center < requested + 2
    · have hcontains :
          NeighborhoodGraph.NeighborhoodContains center requested :=
        (neighborhoodContains_iff_bounds center requested).2
          ⟨hleft, hright⟩
      have hsecondNonzero :
          second (movementDivision regs).test ≠ 0 := by
        rw [hsecondTest]
        omega
      have hsecondCandidate :
          second (ControlDecode.nodePayload1 regs) = candidate := by
        rw [hsecondOutside _
          (regs.injective.ne (by decide))
          (regs.injective.ne (by decide))]
        exact hcandidate
      have hsecondCenter :
          second (centerValue regs) = center := by
        rw [hsecondOutside _
          (regs.injective.ne (by decide))
          (regs.injective.ne (by decide))]
        exact hcenter
      obtain ⟨final, hrecordRun, hfinalFound, hfinalInterval,
          hfinalCenter, hfinalCountdown, hrecordOutside⟩ :=
        recordPrior_runs regs second candidate center
          hsecondCandidate hsecondCenter
      have hrun :
          Runs (recordPriorIfContains regs) store final := by
        simpa [recordPriorIfContains, firstOps,
          secondOps] using
          Runs.seq hfirstRun
            (Runs.ifNonzero hfirstNonzero
              (Runs.seq hsecondRun
                (Runs.ifNonzero hsecondNonzero hrecordRun)))
      refine ⟨final, hrun, ?_⟩
      refine
        { found_eq := by simp [hcontains, hfinalFound]
          interval_eq := by simp [hcontains, hfinalInterval]
          priorCenter_eq := by simp [hcontains, hfinalCenter]
          countdown_eq := by simp [hcontains, hfinalCountdown]
          valid_eq := ?_
          one_eq := ?_
          candidate_eq := ?_
          tape_eq := ?_
          requested_eq := ?_
          guess_eq := ?_ }
      · rw [hrecordOutside]
        · rw [hsecondOutside _
            (regs.injective.ne (by decide))
            (regs.injective.ne (by decide))]
          exact hvalid
        · simp [priorMap, centerMap, regs.injective.eq_iff]
      · rw [hrecordOutside]
        · rw [hsecondOutside _
            (division_index_ne regs (by decide))
            (division_index_ne regs (by decide))]
          exact hone
        · simp [priorMap, movementDivision, movementMap,
            regs.injective.eq_iff]
      · rw [hrecordOutside]
        · exact hsecondCandidate
        · simp [priorMap, ControlDecode.nodePayload1,
            regs.injective.eq_iff]
      · rw [hrecordOutside]
        · rw [hsecondOutside _
            (regs.injective.ne (by decide))
            (regs.injective.ne (by decide))]
          exact htape
        · simp [priorMap, ControlDecode.nodeTape,
            ControlDecode.first, regs.injective.eq_iff]
      · rw [hrecordOutside]
        · rw [hsecondOutside _
            (regs.injective.ne (by decide))
            (regs.injective.ne (by decide))]
          exact hrequested
        · simp [priorMap, regs.injective.eq_iff]
      · rw [hrecordOutside]
        · rw [hsecondOutside _
            (regs.index_ne_controller (movementMap 0) 2).symm
            (regs.index_ne_controller (movementMap 2) 2).symm]
          exact hguess
        · simp only [Finset.mem_insert, Finset.mem_singleton,
            not_or]
          exact
            ⟨(regs.index_ne_controller (priorMap 2) 2).symm,
              (regs.index_ne_controller (priorMap 3) 2).symm,
              (regs.index_ne_controller (priorMap 4) 2).symm,
              (regs.index_ne_controller (priorMap 1) 2).symm⟩
    · have hnotContains :
          ¬NeighborhoodGraph.NeighborhoodContains center requested := by
        rw [neighborhoodContains_iff_bounds]
        omega
      have hsecondZero :
          second (movementDivision regs).test = 0 := by
        rw [hsecondTest]
        omega
      have hrun :
          Runs (recordPriorIfContains regs) store second := by
        simpa [recordPriorIfContains, firstOps,
          secondOps] using
          Runs.seq hfirstRun
            (Runs.ifNonzero hfirstNonzero
              (Runs.seq hsecondRun
                (Runs.ifZero hsecondZero (Runs.skip second))))
      refine ⟨second, hrun, ?_⟩
      refine
        { found_eq := ?_
          interval_eq := ?_
          priorCenter_eq := ?_
          countdown_eq := ?_
          valid_eq := ?_
          one_eq := ?_
          candidate_eq := ?_
          tape_eq := ?_
          requested_eq := ?_
          guess_eq := ?_ }
      · simp only [if_neg hnotContains]
        rw [hsecondOutside _
          (regs.injective.ne (by decide))
          (regs.injective.ne (by decide))]
        exact hfound
      · simp only [if_neg hnotContains]
        rw [hsecondOutside _
          (regs.injective.ne (by decide))
          (regs.injective.ne (by decide))]
        exact hinterval
      · simp only [if_neg hnotContains]
        rw [hsecondOutside _
          (regs.injective.ne (by decide))
          (regs.injective.ne (by decide))]
        exact hpriorCenter
      · simp only [if_neg hnotContains]
        rw [hsecondOutside _
          (regs.injective.ne (by decide))
          (regs.injective.ne (by decide))]
        exact hcountdown
      · rw [hsecondOutside _
          (regs.injective.ne (by decide))
          (regs.injective.ne (by decide))]
        exact hvalid
      · rw [hsecondOutside _
          (division_index_ne regs (by decide))
          (division_index_ne regs (by decide))]
        exact hone
      · rw [hsecondOutside _
          (regs.injective.ne (by decide))
          (regs.injective.ne (by decide))]
        exact hcandidate
      · rw [hsecondOutside _
          (regs.injective.ne (by decide))
          (regs.injective.ne (by decide))]
        exact htape
      · rw [hsecondOutside _
          (regs.injective.ne (by decide))
          (regs.injective.ne (by decide))]
        exact hrequested
      · rw [hsecondOutside _
          (regs.index_ne_controller (movementMap 0) 2).symm
          (regs.index_ne_controller (movementMap 2) 2).symm]
        exact hguess
  · have hnotContains :
        ¬NeighborhoodGraph.NeighborhoodContains center requested := by
      rw [neighborhoodContains_iff_bounds]
      omega
    have hfirstZero :
        first (movementDivision regs).test = 0 := by
      rw [hfirstTest]
      omega
    have hrun :
        Runs (recordPriorIfContains regs) store first := by
      simpa [recordPriorIfContains, firstOps] using
        Runs.seq hfirstRun
          (Runs.ifZero hfirstZero (Runs.skip first))
    refine ⟨first, hrun, ?_⟩
    refine
      { found_eq := ?_
        interval_eq := ?_
        priorCenter_eq := ?_
        countdown_eq := ?_
        valid_eq := ?_
        one_eq := ?_
        candidate_eq := ?_
        tape_eq := ?_
        requested_eq := ?_
        guess_eq := ?_ }
    · simp only [if_neg hnotContains]
      rw [hfirstOutside _
        (regs.injective.ne (by decide))
        (regs.injective.ne (by decide))]
      exact hfound
    · simp only [if_neg hnotContains]
      rw [hfirstOutside _
        (regs.injective.ne (by decide))
        (regs.injective.ne (by decide))]
      exact hinterval
    · simp only [if_neg hnotContains]
      rw [hfirstOutside _
        (regs.injective.ne (by decide))
        (regs.injective.ne (by decide))]
      exact hpriorCenter
    · simp only [if_neg hnotContains]
      rw [hfirstOutside _
        (regs.injective.ne (by decide))
        (regs.injective.ne (by decide))]
      exact hcountdown
    · rw [hfirstOutside _
        (regs.injective.ne (by decide))
        (regs.injective.ne (by decide))]
      exact hvalid
    · rw [hfirstOutside _
        (division_index_ne regs (by decide))
        (division_index_ne regs (by decide))]
      exact hone
    · rw [hfirstOutside _
        (regs.injective.ne (by decide))
        (regs.injective.ne (by decide))]
      exact hcandidate
    · rw [hfirstOutside _
        (regs.injective.ne (by decide))
        (regs.injective.ne (by decide))]
      exact htape
    · rw [hfirstOutside _
        (regs.injective.ne (by decide))
        (regs.injective.ne (by decide))]
      exact hrequested
    · rw [hfirstOutside _
        (regs.index_ne_controller (movementMap 0) 2).symm
        (regs.index_ne_controller (movementMap 2) 2).symm]
      exact hguess

theorem recordPriorIfContains_writesWithin_internal
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (priorFootprint regs)
      (recordPriorIfContains regs) := by
  have hmovement :=
    centerFootprint_subset_prior regs
      (movementFootprint_subset_center regs
        (Finset.mem_image.mpr
          ⟨(0 : Fin 6), Finset.mem_univ _, rfl⟩))
  have htest :=
    centerFootprint_subset_prior regs
      (movementFootprint_subset_center regs
        (Finset.mem_image.mpr
          ⟨(2 : Fin 6), Finset.mem_univ _, rfl⟩))
  simp only [recordPriorIfContains, Cmd.basics,
    Footprint.CmdWritesWithin]
  exact
    ⟨⟨hmovement, hmovement, hmovement, hmovement, htest⟩,
      ⟨trivial,
        ⟨⟨hmovement, hmovement, hmovement, hmovement, htest⟩,
          ⟨trivial, recordPrior_writesWithin regs⟩⟩⟩⟩

private theorem priorSearchBody_writesWithin
    (workTapeCount : ℕ)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (priorFootprint regs)
      (priorSearchBody workTapeCount controller regs) := by
  simp only [priorSearchBody, Cmd.seqList,
    Footprint.CmdWritesWithin]
  exact
    ⟨prior_index_mem regs 1,
      copy_nodeInterval_writesWithin regs _,
      cmdWritesWithin_mono
        (deriveCenter_writesWithin_internal
          workTapeCount controller regs)
        (centerFootprint_subset_prior regs),
      ⟨prior_index_mem regs 1,
        recordPriorIfContains_writesWithin_internal regs⟩⟩

private theorem prior_index_not_mem_center
    (regs : NeighborhoodTrial.Registers controller)
    (slot : Fin 5) :
    regs.index (priorMap slot) ∉ centerFootprint regs := by
  simp only [centerFootprint, Finset.mem_union,
    movementFootprint, Finset.mem_image, Finset.mem_univ,
    true_and, not_or, not_exists]
  constructor
  · intro movementSlot heq
    have hslot := regs.injective heq
    fin_cases slot <;> fin_cases movementSlot <;>
      simp [priorMap, movementMap] at hslot
  · intro centerSlot heq
    have hslot := regs.injective heq
    fin_cases slot <;> fin_cases centerSlot <;>
      simp [priorMap, centerMap] at hslot

private theorem priorLoop_runs
    (workTapeCount : ℕ)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store)
    (word tape requested count : ℕ)
    (hguess : store controller.guess = word)
    (htape : store (ControlDecode.nodeTape regs) = tape)
    (hrequested : store (requestedBlock regs) = requested)
    (hcountdown : store (priorCountdown regs) = count)
    (hfound : store (priorFound regs) = 0)
    (hinterval : store (priorInterval regs) = 0)
    (hpriorCenter : store (priorCenter regs) = 0)
    (hvalid : store (centerValid regs) = 1)
    (hone : store (movementDivision regs).one = 1) :
    ∃ final,
      Runs
        (.whileNonzero (priorCountdown regs)
          (priorSearchBody workTapeCount controller regs))
        store final ∧
      final (centerValid regs) =
        priorValidValue
          (priorSearchValue
            workTapeCount word tape requested count) ∧
      final (priorFound regs) =
        priorFoundValue
          (priorSearchValue
            workTapeCount word tape requested count) ∧
      final (priorInterval regs) =
        priorIntervalValue
          (priorSearchValue
            workTapeCount word tape requested count) ∧
      final (priorCenter regs) =
        priorCenterValue
          (priorSearchValue
            workTapeCount word tape requested count) ∧
      final (priorCountdown regs) = 0 ∧
      final (movementDivision regs).one = 1 ∧
      final (ControlDecode.nodeTape regs) = tape ∧
      final (requestedBlock regs) = requested ∧
      final controller.guess = word := by
  induction count generalizing store with
  | zero =>
      refine ⟨store, Runs.whileZero hcountdown, ?_⟩
      simp [priorSearchValue, priorValidValue, priorFoundValue,
        priorIntervalValue, priorCenterValue, hvalid, hfound,
        hinterval, hpriorCenter, hcountdown, hone, htape,
        hrequested, hguess]
  | succ count ih =>
      have hcountdownNonzero :
          store (priorCountdown regs) ≠ 0 := by
        rw [hcountdown]
        omega
      let decremented :=
        (Basic.sub (priorCountdown regs)
          (priorCountdown regs) (movementDivision regs).one).exec
          store
      have hdecrementRun :
          Runs
            (.basic
              (.sub (priorCountdown regs)
                (priorCountdown regs) (movementDivision regs).one))
            store decremented :=
        Runs.basic _ _
      have hdecrementedCount :
          decremented (priorCountdown regs) = count := by
        simp [decremented, Basic.exec, hcountdown]
        change store (regs.index 17) = 1 at hone
        change count + 1 - store (regs.index 17) = count
        rw [hone]
        omega
      have hdecrementedOutside
          (address : ℕ)
          (hne : address ≠ priorCountdown regs) :
          decremented address = store address := by
        simp [decremented, Basic.exec,
          Function.update_of_ne, hne]
      let prepared :=
        Function.update decremented
          (ControlDecode.nodePayload1 regs)
          (decremented (priorCountdown regs))
      have hcopyRun :
          Runs
            (ControlDecode.copy
              (ControlDecode.nodePayload1 regs)
              (priorCountdown regs))
            decremented prepared := by
        exact copy_update_runs decremented
          (regs.injective.ne
            (by decide : (11 : Fin 34) ≠ priorMap 1))
      have hpreparedOutside
          (address : ℕ)
          (hnode :
            address ≠ ControlDecode.nodePayload1 regs)
          (hcount : address ≠ priorCountdown regs) :
          prepared address = store address := by
        rw [show prepared address = decremented address by
          simp [prepared, Function.update_of_ne, hnode]]
        exact hdecrementedOutside address hcount
      have hpreparedCount :
          prepared (priorCountdown regs) = count := by
        rw [show
          prepared (priorCountdown regs) =
              decremented (priorCountdown regs) by
          simp [prepared, regs.injective.eq_iff,
            ControlDecode.nodePayload1, priorMap]]
        exact hdecrementedCount
      have hpreparedCandidate :
          prepared (ControlDecode.nodePayload1 regs) = count := by
        simp [prepared, hdecrementedCount]
      have hpreparedGuess :
          prepared controller.guess = word := by
        rw [hpreparedOutside _
          (regs.index_ne_controller 11 2).symm
          (regs.index_ne_controller (priorMap 1) 2).symm]
        exact hguess
      have hpreparedTape :
          prepared (ControlDecode.nodeTape regs) = tape := by
        rw [hpreparedOutside _
          (regs.injective.ne (by decide))
          (regs.injective.ne (by decide))]
        exact htape
      have hpreparedRequested :
          prepared (requestedBlock regs) = requested := by
        rw [hpreparedOutside _
          (regs.injective.ne (by decide))
          (regs.injective.ne (by decide))]
        exact hrequested
      have hpreparedFound :
          prepared (priorFound regs) = 0 := by
        rw [hpreparedOutside _
          (regs.injective.ne (by decide))
          (regs.injective.ne (by decide))]
        exact hfound
      have hpreparedInterval :
          prepared (priorInterval regs) = 0 := by
        rw [hpreparedOutside _
          (regs.injective.ne (by decide))
          (regs.injective.ne (by decide))]
        exact hinterval
      have hpreparedPriorCenter :
          prepared (priorCenter regs) = 0 := by
        rw [hpreparedOutside _
          (regs.injective.ne (by decide))
          (regs.injective.ne (by decide))]
        exact hpriorCenter
      have hpreparedValid :
          prepared (centerValid regs) = 1 := by
        rw [hpreparedOutside _
          (regs.injective.ne (by decide))
          (regs.injective.ne (by decide))]
        exact hvalid
      obtain ⟨centered, hderiveRun, hderivePost⟩ :=
        deriveCenter_runs_internal
          workTapeCount controller regs prepared
          word tape count hpreparedGuess hpreparedTape
          hpreparedCandidate
      have hcenteredCount :
          centered (priorCountdown regs) = count := by
        rw [hderivePost.eq_outside _
          (prior_index_not_mem_center regs 1)]
        exact hpreparedCount
      have hcenteredFound :
          centered (priorFound regs) = 0 := by
        rw [hderivePost.eq_outside _
          (prior_index_not_mem_center regs 2)]
        exact hpreparedFound
      have hcenteredInterval :
          centered (priorInterval regs) = 0 := by
        rw [hderivePost.eq_outside _
          (prior_index_not_mem_center regs 3)]
        exact hpreparedInterval
      have hcenteredPriorCenter :
          centered (priorCenter regs) = 0 := by
        rw [hderivePost.eq_outside _
          (prior_index_not_mem_center regs 4)]
        exact hpreparedPriorCenter
      have hcenteredRequested :
          centered (requestedBlock regs) = requested := by
        rw [hderivePost.eq_outside _
          (prior_index_not_mem_center regs 0)]
        exact hpreparedRequested
      generalize hresult :
          derivedCenterValue workTapeCount word tape count = result
      cases result with
      | none =>
          have hcenteredInvalid :
              centered (centerValid regs) = 0 := by
            simpa [hresult, centerValidValue] using
              hderivePost.valid_eq
          let stopped :=
            (Basic.imm (priorCountdown regs) 0).exec centered
          have hstopRun :
              Runs
                (.basic (.imm (priorCountdown regs) 0))
                centered stopped :=
            Runs.basic _ _
          have hbody :
              Runs
                (priorSearchBody workTapeCount controller regs)
                store stopped := by
            simpa [priorSearchBody, Cmd.seqList] using
              Runs.seq hdecrementRun
                (Runs.seq hcopyRun
                  (Runs.seq hderiveRun
                    (Runs.ifZero hcenteredInvalid hstopRun)))
          have hstoppedCount :
              stopped (priorCountdown regs) = 0 := by
            simp [stopped, Basic.exec]
          have hloop :
              Runs
                (.whileNonzero (priorCountdown regs)
                  (priorSearchBody workTapeCount controller regs))
                stopped stopped :=
            Runs.whileZero hstoppedCount
          refine ⟨stopped,
            Runs.whileNonzero hcountdownNonzero hbody hloop,
            ?_⟩
          simp [priorSearchValue, hresult, priorValidValue,
            priorFoundValue, priorIntervalValue, priorCenterValue,
            stopped, Basic.exec, priorMap, centerMap,
            movementDivision, movementMap, regs.injective.eq_iff,
            hcenteredInvalid, hcenteredFound, hcenteredInterval,
            hcenteredPriorCenter, hderivePost.tape_eq,
            hcenteredRequested]
          constructor
          · exact hderivePost.one_eq
          · rw [Function.update_of_ne
              (regs.index_ne_controller (priorMap 1) 2).symm]
            exact hderivePost.guess_eq
      | some center =>
          have hcenteredValid :
              centered (centerValid regs) = 1 := by
            simpa [hresult, centerValidValue] using
              hderivePost.valid_eq
          have hcenteredCenter :
              centered (centerValue regs) = center := by
            simpa [hresult, centerOutputValue] using
              hderivePost.center_eq
          obtain ⟨checked, hcheckRun, hcheckPost⟩ :=
            recordPriorIfContains_runs_internal controller regs centered
              center requested count count word tape
              hcenteredCenter hcenteredRequested
              hderivePost.interval_eq hcenteredCount hcenteredFound
              hcenteredInterval hcenteredPriorCenter
              hcenteredValid hderivePost.one_eq
              hderivePost.tape_eq hderivePost.guess_eq
          have hbody :
              Runs
                (priorSearchBody workTapeCount controller regs)
                store checked := by
            simpa [priorSearchBody, Cmd.seqList] using
              Runs.seq hdecrementRun
                (Runs.seq hcopyRun
                  (Runs.seq hderiveRun
                    (Runs.ifNonzero (by
                      rw [hcenteredValid]
                      omega) hcheckRun)))
          by_cases hcontains :
              NeighborhoodGraph.NeighborhoodContains center requested
          · have hcheckedCount :
                checked (priorCountdown regs) = 0 := by
              rw [hcheckPost.countdown_eq]
              simp [hcontains]
            have hloop :
                Runs
                  (.whileNonzero (priorCountdown regs)
                    (priorSearchBody workTapeCount controller regs))
                  checked checked :=
              Runs.whileZero hcheckedCount
            refine ⟨checked,
              Runs.whileNonzero hcountdownNonzero hbody hloop,
              ?_⟩
            simp [priorSearchValue, hresult, hcontains,
              priorValidValue, priorFoundValue, priorIntervalValue,
              priorCenterValue, hcheckPost.valid_eq,
              hcheckPost.found_eq, hcheckPost.interval_eq,
              hcheckPost.priorCenter_eq, hcheckPost.countdown_eq,
              hcheckPost.one_eq, hcheckPost.tape_eq,
              hcheckPost.requested_eq, hcheckPost.guess_eq]
          · have hcheckedCount :
                checked (priorCountdown regs) = count := by
              rw [hcheckPost.countdown_eq]
              simp [hcontains]
            have hcheckedFound :
                checked (priorFound regs) = 0 := by
              rw [hcheckPost.found_eq]
              simp [hcontains]
            have hcheckedInterval :
                checked (priorInterval regs) = 0 := by
              rw [hcheckPost.interval_eq]
              simp [hcontains]
            have hcheckedPriorCenter :
                checked (priorCenter regs) = 0 := by
              rw [hcheckPost.priorCenter_eq]
              simp [hcontains]
            obtain ⟨final, hloop, hfinalValid, hfinalFound,
                hfinalInterval, hfinalPriorCenter, hfinalCount,
                hfinalOne, hfinalTape, hfinalRequested,
                hfinalGuess⟩ :=
              ih checked hcheckPost.guess_eq hcheckPost.tape_eq
                hcheckPost.requested_eq hcheckedCount hcheckedFound
                hcheckedInterval hcheckedPriorCenter
                hcheckPost.valid_eq hcheckPost.one_eq
            refine ⟨final,
              Runs.whileNonzero hcountdownNonzero hbody hloop,
              ?_⟩
            simpa [priorSearchValue, hresult, hcontains] using
              And.intro hfinalValid
                (And.intro hfinalFound
                  (And.intro hfinalInterval
                    (And.intro hfinalPriorCenter
                      (And.intro hfinalCount
                        (And.intro hfinalOne
                          (And.intro hfinalTape
                            (And.intro hfinalRequested
                              hfinalGuess)))))))

theorem scanPrior_writesWithin_internal
    (workTapeCount : ℕ)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (priorFootprint regs)
      (scanPrior workTapeCount controller regs) := by
  have hone :=
    centerFootprint_subset_prior regs
      (movementFootprint_subset_center regs
        (Finset.mem_image.mpr
          ⟨(3 : Fin 6), Finset.mem_univ _, rfl⟩))
  simp only [scanPrior, Cmd.basics,
    Footprint.CmdWritesWithin]
  exact
    ⟨⟨hone,
        centerFootprint_subset_prior regs (center_index_mem regs 2),
        prior_index_mem regs 2, prior_index_mem regs 3,
        prior_index_mem regs 4⟩,
      ⟨copy_prior_writesWithin regs 1 _,
        priorSearchBody_writesWithin workTapeCount controller regs⟩⟩

theorem priorFootprint_subset_layout_internal
    (regs : NeighborhoodTrial.Registers controller) :
    priorFootprint regs ⊆ regs.layout.footprint := by
  intro address haddress
  rw [priorFootprint, Finset.mem_union] at haddress
  rcases haddress with hleft | hright
  · rw [Finset.mem_union] at hleft
    rcases hleft with hcenter | hinterval
    · exact centerFootprint_subset_layout_internal regs hcenter
    · simp only [Finset.mem_singleton] at hinterval
      subst address
      exact Layout.index_mem_layout_footprint regs 11
  · simp only [Finset.mem_image, Finset.mem_univ, true_and] at hright
    obtain ⟨slot, rfl⟩ := hright
    exact Layout.index_mem_layout_footprint regs (priorMap slot)

theorem scanPrior_runs_internal
    (workTapeCount : ℕ)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store) (word tape requested interval : ℕ)
    (hguess : store controller.guess = word)
    (htape : store (ControlDecode.nodeTape regs) = tape)
    (hrequested : store (requestedBlock regs) = requested)
    (hinterval :
      store (ControlDecode.nodePayload1 regs) = interval) :
    ∃ final,
      Runs (scanPrior workTapeCount controller regs) store final ∧
      ScanPriorPost workTapeCount word tape requested interval
        controller regs store final := by
  let ops : List Basic :=
    [.imm (movementDivision regs).one 1,
      .imm (centerValid regs) 1,
      .imm (priorFound regs) 0,
      .imm (priorInterval regs) 0,
      .imm (priorCenter regs) 0]
  let initialized := Basic.execList ops store
  have hinitializeRun :
      Runs (Cmd.basics ops) store initialized :=
    basics_runs ops store
  let counted :=
    Function.update initialized (priorCountdown regs)
      (initialized (ControlDecode.nodePayload1 regs))
  have hcopyRun :
      Runs
        (ControlDecode.copy
          (priorCountdown regs) (ControlDecode.nodePayload1 regs))
        initialized counted := by
    exact copy_update_runs initialized
      (regs.injective.ne
        (by decide : priorMap 1 ≠ (11 : Fin 34)))
  have hcountedCount :
      counted (priorCountdown regs) = interval := by
    simp [counted, initialized, ops, Basic.execList, Basic.exec,
      movementDivision, movementMap, centerMap, priorMap,
      ControlDecode.nodePayload1, regs.injective.eq_iff,
      hinterval]
  have hcountedFound :
      counted (priorFound regs) = 0 := by
    simp [counted, initialized, ops, Basic.execList, Basic.exec,
      movementDivision, movementMap, centerMap, priorMap,
      regs.injective.eq_iff]
  have hcountedInterval :
      counted (priorInterval regs) = 0 := by
    simp [counted, initialized, ops, Basic.execList, Basic.exec,
      movementDivision, movementMap, centerMap, priorMap,
      regs.injective.eq_iff]
  have hcountedPriorCenter :
      counted (priorCenter regs) = 0 := by
    simp [counted, initialized, ops, Basic.execList, Basic.exec,
      movementDivision, movementMap, centerMap, priorMap,
      regs.injective.eq_iff]
  have hcountedValid :
      counted (centerValid regs) = 1 := by
    simp [counted, initialized, ops, Basic.execList, Basic.exec,
      movementDivision, movementMap, centerMap, priorMap,
      regs.injective.eq_iff]
  have hcountedOne :
      counted (movementDivision regs).one = 1 := by
    simp [counted, initialized, ops, Basic.execList, Basic.exec,
      movementDivision, movementMap, centerMap, priorMap,
      regs.injective.eq_iff]
  have hcountedTape :
      counted (ControlDecode.nodeTape regs) = tape := by
    simp [counted, initialized, ops, Basic.execList, Basic.exec,
      movementDivision, movementMap, centerMap, priorMap,
      ControlDecode.nodeTape, ControlDecode.first,
      regs.injective.eq_iff, htape]
  have hcountedRequested :
      counted (requestedBlock regs) = requested := by
    simp [counted, initialized, ops, Basic.execList, Basic.exec,
      movementDivision, movementMap, centerMap, priorMap,
      regs.injective.eq_iff, hrequested]
  have hinitializedGuess :
      initialized controller.guess = word := by
    simp [initialized, ops, Basic.execList, Basic.exec,
      Function.update_of_ne,
      (regs.index_ne_controller (centerMap 2) 2).symm,
      (regs.index_ne_controller (priorMap 2) 2).symm,
      (regs.index_ne_controller (priorMap 3) 2).symm,
      (regs.index_ne_controller (priorMap 4) 2).symm]
    change
      Function.update store (regs.index 17) 1
          controller.guess =
        word
    rw [Function.update_of_ne
      (regs.index_ne_controller (17 : Fin 34) 2).symm]
    exact hguess
  have hcountedGuess :
      counted controller.guess = word := by
    simp [counted, Function.update_of_ne,
      (regs.index_ne_controller (priorMap 1) 2).symm,
      hinitializedGuess]
  obtain ⟨final, hloopRun, hfinalValid, hfinalFound,
      hfinalInterval, hfinalPriorCenter, hfinalCount,
      hfinalOne, hfinalTape, hfinalRequested, hfinalGuess⟩ :=
    priorLoop_runs workTapeCount controller regs counted
      word tape requested interval hcountedGuess hcountedTape
      hcountedRequested hcountedCount hcountedFound
      hcountedInterval hcountedPriorCenter hcountedValid
      hcountedOne
  have hrun :
      Runs (scanPrior workTapeCount controller regs) store final := by
    simpa [scanPrior, ops] using
      Runs.seq hinitializeRun (Runs.seq hcopyRun hloopRun)
  refine ⟨final, hrun, ?_⟩
  exact
    { valid_eq := hfinalValid
      found_eq := hfinalFound
      interval_eq := hfinalInterval
      center_eq := hfinalPriorCenter
      countdown_eq := hfinalCount
      one_eq := hfinalOne
      tape_eq := hfinalTape
      requested_eq := hfinalRequested
      guess_eq := hfinalGuess
      eq_outside := fun address haddress =>
        Footprint.runs_eq_outside
          (scanPrior_writesWithin_internal
            workTapeCount controller regs)
          hrun haddress }

private theorem nodeTape_mem_chronological
    (regs : NeighborhoodTrial.Registers controller) :
    ControlDecode.nodeTape regs ∈ chronologicalFootprint regs := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

private theorem priorFootprint_subset_chronological
    (regs : NeighborhoodTrial.Registers controller) :
    priorFootprint regs ⊆ chronologicalFootprint regs :=
  Finset.subset_union_left.trans Finset.subset_union_left

private theorem nodeEncoding_subset_chronological
    (regs : NeighborhoodTrial.Registers controller) :
    nodeEncodingFootprint regs ⊆ chronologicalFootprint regs :=
  Finset.subset_union_right

private theorem installFailure_writesWithin
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (chronologicalFootprint regs)
      (installFailure regs) := by
  have hpayload0 :
      ControlDecode.nodePayload0 regs ∈
        chronologicalFootprint regs :=
    priorFootprint_subset_chronological regs
      (centerFootprint_subset_prior regs
        (center_index_mem regs 1))
  have hpayload1 :
      ControlDecode.nodePayload1 regs ∈
        chronologicalFootprint regs :=
    priorFootprint_subset_chronological regs
      (nodeInterval_mem_prior regs)
  simp only [installFailure, Cmd.basics,
    Footprint.CmdWritesWithin]
  exact
    ⟨⟨nodeTape_mem_chronological regs, hpayload0, hpayload1⟩,
      cmdWritesWithin_mono
        (encodeNodeFields_writesWithin_internal regs 0)
        (nodeEncoding_subset_chronological regs)⟩

theorem installChronological_writesWithin_internal
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (chronologicalFootprint regs)
      (installChronological regs) := by
  have hpayload0 :
      ControlDecode.nodePayload0 regs ∈
        chronologicalFootprint regs :=
    priorFootprint_subset_chronological regs
      (centerFootprint_subset_prior regs
        (center_index_mem regs 1))
  have hpayload1 :
      ControlDecode.nodePayload1 regs ∈
        chronologicalFootprint regs :=
    priorFootprint_subset_chronological regs
      (nodeInterval_mem_prior regs)
  simp only [installChronological, Cmd.basics,
    Footprint.CmdWritesWithin]
  exact
    ⟨installFailure_writesWithin regs,
      ⟨cmdWritesWithin_mono
          (encodeNodeFields_writesWithin_internal regs 1)
          (nodeEncoding_subset_chronological regs),
        ⟨⟨hpayload1, hpayload0⟩,
          cmdWritesWithin_mono
            (encodeNodeFields_writesWithin_internal regs 2)
            (nodeEncoding_subset_chronological regs)⟩⟩⟩

theorem chronologicalFootprint_subset_layout_internal
    (regs : NeighborhoodTrial.Registers controller) :
    chronologicalFootprint regs ⊆ regs.layout.footprint := by
  intro address haddress
  rw [chronologicalFootprint, Finset.mem_union] at haddress
  rcases haddress with hleft | hencoding
  · rw [Finset.mem_union] at hleft
    rcases hleft with hprior | htape
    · exact priorFootprint_subset_layout_internal regs hprior
    · simp only [Finset.mem_singleton] at htape
      subst address
      exact Layout.index_mem_layout_footprint regs 9
  · exact nodeEncodingFootprint_subset_layout_internal regs hencoding

private theorem priorFootprint_subset_assembly
    (regs : NeighborhoodTrial.Registers controller) :
    priorFootprint regs ⊆ priorAssemblyFootprint regs :=
  Finset.subset_union_left.trans Finset.subset_union_left

private theorem nodeEncoding_subset_priorAssembly
    (regs : NeighborhoodTrial.Registers controller) :
    nodeEncodingFootprint regs ⊆ priorAssemblyFootprint regs :=
  Finset.subset_union_right

private theorem nodeTape_mem_priorAssembly
    (regs : NeighborhoodTrial.Registers controller) :
    ControlDecode.nodeTape regs ∈ priorAssemblyFootprint regs := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

private theorem nodePayload0_mem_priorAssembly
    (regs : NeighborhoodTrial.Registers controller) :
    ControlDecode.nodePayload0 regs ∈
      priorAssemblyFootprint regs :=
  priorFootprint_subset_assembly regs
    (centerFootprint_subset_prior regs
      (center_index_mem regs 1))

private theorem nodePayload1_mem_priorAssembly
    (regs : NeighborhoodTrial.Registers controller) :
    ControlDecode.nodePayload1 regs ∈
      priorAssemblyFootprint regs :=
  priorFootprint_subset_assembly regs
    (nodeInterval_mem_prior regs)

private theorem divisionValue_mem_priorAssembly
    (regs : NeighborhoodTrial.Registers controller) :
    (movementDivision regs).value ∈ priorAssemblyFootprint regs :=
  priorFootprint_subset_assembly regs
    (centerFootprint_subset_prior regs
      (movementFootprint_subset_center regs
        (Finset.mem_image.mpr
          ⟨(0 : Fin 6), Finset.mem_univ _, rfl⟩)))

private theorem divisionTest_mem_priorAssembly
    (regs : NeighborhoodTrial.Registers controller) :
    (movementDivision regs).test ∈ priorAssemblyFootprint regs :=
  priorFootprint_subset_assembly regs
    (centerFootprint_subset_prior regs
      (movementFootprint_subset_center regs
        (Finset.mem_image.mpr
          ⟨(2 : Fin 6), Finset.mem_univ _, rfl⟩)))

private theorem installPriorSource_writesWithin
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (priorAssemblyFootprint regs)
      (installPriorSource regs) := by
  have hcopy :
      Footprint.CmdWritesWithin (priorAssemblyFootprint regs)
        (ControlDecode.copy
          (ControlDecode.nodePayload0 regs)
          (requestedBlock regs)) := by
    simp [ControlDecode.copy, Footprint.CmdWritesWithin,
      Footprint.BasicWritesWithin,
      nodePayload0_mem_priorAssembly regs]
  have hencode :=
    cmdWritesWithin_mono
      (encodeNodeFields_writesWithin_internal regs 1)
      (nodeEncoding_subset_priorAssembly regs)
  simpa only [installPriorSource, Cmd.seqList,
    Footprint.CmdWritesWithin] using
      And.intro hcopy
        (And.intro (nodePayload1_mem_priorAssembly regs) hencode)

private theorem installPriorComputation_writesWithin
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (priorAssemblyFootprint regs)
      (installPriorComputation regs) := by
  have hcopy :
      Footprint.CmdWritesWithin (priorAssemblyFootprint regs)
        (ControlDecode.copy
          (ControlDecode.nodePayload1 regs)
          (priorInterval regs)) := by
    simp [ControlDecode.copy, Footprint.CmdWritesWithin,
      Footprint.BasicWritesWithin,
      nodePayload1_mem_priorAssembly regs]
  have hencode :=
    cmdWritesWithin_mono
      (encodeNodeFields_writesWithin_internal regs 2)
      (nodeEncoding_subset_priorAssembly regs)
  simpa only [installPriorComputation, Cmd.seqList,
    Footprint.CmdWritesWithin] using
      And.intro hcopy
        (And.intro (nodePayload0_mem_priorAssembly regs)
          (And.intro (divisionValue_mem_priorAssembly regs)
            (And.intro (divisionTest_mem_priorAssembly regs)
              (And.intro hencode
                (And.intro (nodePayload0_mem_priorAssembly regs)
                  (And.intro (divisionTest_mem_priorAssembly regs)
                    (And.intro hencode
                      (And.intro
                        (nodePayload0_mem_priorAssembly regs)
                        hencode))))))))

theorem installPrior_writesWithin_internal
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (priorAssemblyFootprint regs)
      (installPrior regs) := by
  have hfailure :
      Footprint.CmdWritesWithin (priorAssemblyFootprint regs)
        (installFailure regs) := by
    simpa [priorAssemblyFootprint, chronologicalFootprint] using
      installFailure_writesWithin regs
  simp only [installPrior, Footprint.CmdWritesWithin]
  exact ⟨hfailure,
    installPriorSource_writesWithin regs,
    installPriorComputation_writesWithin regs⟩

theorem scanAndInstallPrior_writesWithin_internal
    (workTapeCount : ℕ)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (priorAssemblyFootprint regs)
      (scanAndInstallPrior workTapeCount controller regs) := by
  simp only [scanAndInstallPrior, Footprint.CmdWritesWithin]
  exact
    ⟨cmdWritesWithin_mono
        (scanPrior_writesWithin_internal
          workTapeCount controller regs)
        (priorFootprint_subset_assembly regs),
      installPrior_writesWithin_internal regs⟩

private theorem requestedBlock_mem_priorAssembly
    (regs : NeighborhoodTrial.Registers controller) :
    requestedBlock regs ∈ priorAssemblyFootprint regs :=
  priorFootprint_subset_assembly regs (prior_index_mem regs 0)

private theorem divisionQuotient_mem_priorAssembly
    (regs : NeighborhoodTrial.Registers controller) :
    (movementDivision regs).quotient ∈
      priorAssemblyFootprint regs :=
  priorFootprint_subset_assembly regs
    (centerFootprint_subset_prior regs
      (movementFootprint_subset_center regs
        (Finset.mem_image.mpr
          ⟨(1 : Fin 6), Finset.mem_univ _, rfl⟩)))

private theorem installRequestedBlock_writesWithin
    (regs : NeighborhoodTrial.Registers controller)
    (slot : NeighborhoodGraph.Slot) :
    Footprint.CmdWritesWithin (priorAssemblyFootprint regs)
      (installRequestedBlock regs slot) := by
  have hcopy :
      Footprint.CmdWritesWithin (priorAssemblyFootprint regs)
        (ControlDecode.copy
          (requestedBlock regs) (centerValue regs)) := by
    simp [ControlDecode.copy, Footprint.CmdWritesWithin,
      Footprint.BasicWritesWithin,
      requestedBlock_mem_priorAssembly regs]
  cases slot with
  | lower =>
      simp only [installRequestedBlock,
        Footprint.CmdWritesWithin, Footprint.BasicWritesWithin]
      exact ⟨hcopy, requestedBlock_mem_priorAssembly regs⟩
  | center =>
      exact hcopy
  | upper =>
      simp only [installRequestedBlock,
        Footprint.CmdWritesWithin, Footprint.BasicWritesWithin]
      exact ⟨hcopy, requestedBlock_mem_priorAssembly regs⟩

private theorem installContentChild_writesWithin
    (workTapeCount : ℕ)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (slot : NeighborhoodGraph.Slot) :
    Footprint.CmdWritesWithin (priorAssemblyFootprint regs)
      (installContentChild workTapeCount controller regs slot) := by
  have hderive :=
    cmdWritesWithin_mono
      (deriveCenter_writesWithin_internal
        workTapeCount controller regs)
      ((centerFootprint_subset_prior regs).trans
        (priorFootprint_subset_assembly regs))
  have hfailure :
      Footprint.CmdWritesWithin (priorAssemblyFootprint regs)
        (installFailure regs) := by
    simpa [priorAssemblyFootprint, chronologicalFootprint] using
      installFailure_writesWithin regs
  simp only [installContentChild, Footprint.CmdWritesWithin]
  exact
    ⟨hderive, hfailure,
      installRequestedBlock_writesWithin regs slot,
      scanAndInstallPrior_writesWithin_internal
        workTapeCount controller regs⟩

private theorem installChronologicalChild_writesWithin
    (workTapeCount : ℕ)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (priorAssemblyFootprint regs)
      (installChronologicalChild workTapeCount controller regs) := by
  have hderive :=
    cmdWritesWithin_mono
      (deriveCenter_writesWithin_internal
        workTapeCount controller regs)
      ((centerFootprint_subset_prior regs).trans
        (priorFootprint_subset_assembly regs))
  have hinstall :
      Footprint.CmdWritesWithin (priorAssemblyFootprint regs)
        (installChronological regs) := by
    simpa [priorAssemblyFootprint, chronologicalFootprint] using
      installChronological_writesWithin_internal regs
  exact ⟨hderive, hinstall⟩

private theorem dispatchDecodedChild_writesWithin
    (workTapeCount : ℕ)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (priorAssemblyFootprint regs)
      (dispatchDecodedChild workTapeCount controller regs) := by
  simp only [dispatchDecodedChild, Footprint.CmdWritesWithin]
  exact
    ⟨installContentChild_writesWithin
        workTapeCount controller regs .lower,
      ⟨divisionQuotient_mem_priorAssembly regs,
        ⟨installContentChild_writesWithin
            workTapeCount controller regs .center,
          ⟨divisionQuotient_mem_priorAssembly regs,
            ⟨installContentChild_writesWithin
                workTapeCount controller regs .upper,
              installChronologicalChild_writesWithin
                workTapeCount controller regs⟩⟩⟩⟩⟩

theorem regenerateChild_writesWithin_internal
    (workTapeCount : ℕ)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (priorAssemblyFootprint regs)
      (regenerateChild workTapeCount controller regs) := by
  have hdecode :=
    cmdWritesWithin_mono
      (decodeChildIndex_writesWithin_internal workTapeCount regs)
      ((movementFootprint_subset_center regs).trans
        ((centerFootprint_subset_prior regs).trans
          (priorFootprint_subset_assembly regs)))
  have hcopy :
      Footprint.CmdWritesWithin (priorAssemblyFootprint regs)
        (ControlDecode.copy
          (ControlDecode.nodeTape regs)
          (movementDivision regs).value) := by
    simp [ControlDecode.copy, Footprint.CmdWritesWithin,
      Footprint.BasicWritesWithin,
      nodeTape_mem_priorAssembly regs]
  simp only [regenerateChild, Cmd.seqList,
    Footprint.CmdWritesWithin]
  exact ⟨hdecode, hcopy,
    dispatchDecodedChild_writesWithin
      workTapeCount controller regs⟩

theorem priorAssemblyFootprint_subset_layout_internal
    (regs : NeighborhoodTrial.Registers controller) :
    priorAssemblyFootprint regs ⊆ regs.layout.footprint := by
  simpa [priorAssemblyFootprint, chronologicalFootprint] using
    chronologicalFootprint_subset_layout_internal regs

private theorem installFailure_runs
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store) :
    ∃ final,
      Runs (installFailure regs) store final ∧
      final (Layout.nodeCode regs) =
        FrameCodec.encodeNode
          (store (Layout.chunkRadix regs))
          (NeighborhoodEvaluator.QueryNode.failure :
            NeighborhoodEvaluator.QueryNode workTapeCount horizon) ∧
      final (Layout.codecDigit regs) = 0 := by
  let ops : List Basic :=
    [.imm (ControlDecode.nodeTape regs) 0,
      .imm (ControlDecode.nodePayload0 regs) 0,
      .imm (ControlDecode.nodePayload1 regs) 0]
  let cleared := Basic.execList ops store
  have hclearRun :
      Runs (Cmd.basics ops) store cleared :=
    basics_runs ops store
  obtain ⟨final, hencodeRun, hencodePost⟩ :=
    encodeNodeFields_runs_internal regs 0 cleared
  have hrun :
      Runs (installFailure regs) store final := by
    simpa [installFailure, ops] using
      Runs.seq hclearRun hencodeRun
  refine ⟨final, hrun, ?_, hencodePost.codecDigit_eq⟩
  rw [hencodePost.nodeCode_eq]
  simp [cleared, ops, Basic.execList, Basic.exec,
    nodeFieldValue, FrameCodec.encodeNode,
    FrameCodec.nodeDigits, FrameCodec.encodeList,
    PackedDigits.push, Layout.chunkRadix, ControlDecode.nodeTape,
    ControlDecode.nodePayload0, ControlDecode.nodePayload1,
    ControlDecode.first, ControlDecode.second, ControlDecode.third,
    regs.injective.eq_iff]

private theorem installRequestedBlock_runs
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store) (center : ℕ)
    (slot : NeighborhoodGraph.Slot)
    (hcenter : store (centerValue regs) = center)
    (hone : store (movementDivision regs).one = 1) :
    ∃ final,
      Runs (installRequestedBlock regs slot) store final ∧
      final (requestedBlock regs) =
        NeighborhoodGraph.neighborBlock center slot ∧
      ∀ address, address ≠ requestedBlock regs →
        final address = store address := by
  obtain ⟨copied, hcopyRun, hcopyValue, hcopyOutside⟩ :=
    copy_runs (requestedBlock regs) (centerValue regs) store
      (regs.injective.ne (by decide))
  have hcopiedOne :
      copied (movementDivision regs).one = 1 := by
    have honeNe :
        (movementDivision regs).one ≠ requestedBlock regs :=
      regs.injective.ne (by decide)
    rw [hcopyOutside _ honeNe]
    exact hone
  cases slot with
  | lower =>
      let final :=
        (Basic.sub (requestedBlock regs)
          (requestedBlock regs) (movementDivision regs).one).exec
            copied
      have hadjustRun :
          Runs
            (.basic
              (.sub (requestedBlock regs)
                (requestedBlock regs) (movementDivision regs).one))
            copied final :=
        Runs.basic _ _
      refine ⟨final, Runs.seq hcopyRun hadjustRun, ?_, ?_⟩
      · simp [final, Basic.exec, NeighborhoodGraph.neighborBlock,
          hcopyValue, hcenter, hcopiedOne]
      · intro address haddress
        simp [final, Basic.exec, Function.update_of_ne, haddress]
        exact hcopyOutside address haddress
  | center =>
      refine ⟨copied, hcopyRun, ?_, hcopyOutside⟩
      simpa [NeighborhoodGraph.neighborBlock, hcenter] using
        hcopyValue
  | upper =>
      let final :=
        (Basic.add (requestedBlock regs)
          (requestedBlock regs) (movementDivision regs).one).exec
            copied
      have hadjustRun :
          Runs
            (.basic
              (.add (requestedBlock regs)
                (requestedBlock regs) (movementDivision regs).one))
            copied final :=
        Runs.basic _ _
      refine ⟨final, Runs.seq hcopyRun hadjustRun, ?_, ?_⟩
      · simp [final, Basic.exec, NeighborhoodGraph.neighborBlock,
          hcopyValue, hcenter, hcopiedOne]
      · intro address haddress
        simp [final, Basic.exec, Function.update_of_ne, haddress]
        exact hcopyOutside address haddress

private theorem installPriorSource_runs
    {horizon : ℕ}
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store)
    (tape : TapeIndex workTapeCount) (requested : ℕ)
    (htape : store (ControlDecode.nodeTape regs) = tape.val)
    (hrequested : store (requestedBlock regs) = requested) :
    ∃ final,
      Runs (installPriorSource regs) store final ∧
      final (Layout.nodeCode regs) =
        FrameCodec.encodeNode
          (store (Layout.chunkRadix regs))
          (priorQueryValue
            (horizon := horizon) tape requested (some none)) ∧
      final (Layout.codecDigit regs) = 0 := by
  let copied :=
    Function.update store
      (ControlDecode.nodePayload0 regs)
      (store (requestedBlock regs))
  have hcopyRun :
      Runs
        (ControlDecode.copy
          (ControlDecode.nodePayload0 regs)
          (requestedBlock regs))
        store copied := by
    exact copy_update_runs store
      (regs.injective.ne (by decide))
  let prepared :=
    (Basic.imm (ControlDecode.nodePayload1 regs) 0).exec copied
  have hprepareRun :
      Runs
        (.basic (.imm (ControlDecode.nodePayload1 regs) 0))
        copied prepared :=
    Runs.basic _ _
  have hpreparedTape :
      prepared (ControlDecode.nodeTape regs) = tape.val := by
    simp [prepared, copied, Basic.exec,
      ControlDecode.nodeTape, ControlDecode.nodePayload0,
      ControlDecode.nodePayload1, ControlDecode.first,
      ControlDecode.second, ControlDecode.third,
      regs.injective.eq_iff, htape]
  have hpreparedPayload0 :
      prepared (ControlDecode.nodePayload0 regs) = requested := by
    simp [prepared, copied, Basic.exec,
      ControlDecode.nodePayload0, ControlDecode.nodePayload1,
      ControlDecode.second, ControlDecode.third,
      regs.injective.eq_iff, hrequested]
  have hpreparedPayload1 :
      prepared (ControlDecode.nodePayload1 regs) = 0 := by
    simp [prepared, Basic.exec]
  have hpreparedBase :
      prepared (Layout.chunkRadix regs) =
        store (Layout.chunkRadix regs) := by
    simp [prepared, copied, Basic.exec, Layout.chunkRadix,
      ControlDecode.nodePayload0, ControlDecode.nodePayload1,
      ControlDecode.second, ControlDecode.third,
      regs.injective.eq_iff]
  obtain ⟨final, hencodeRun, hencodePost⟩ :=
    encodeNodeFields_runs_internal regs 1 prepared
  have hrun :
      Runs (installPriorSource regs) store final := by
    simpa [installPriorSource, Cmd.seqList] using
      Runs.seq hcopyRun (Runs.seq hprepareRun hencodeRun)
  refine ⟨final, hrun, ?_, hencodePost.codecDigit_eq⟩
  rw [hencodePost.nodeCode_eq]
  rw [hpreparedTape, hpreparedPayload0, hpreparedPayload1,
    hpreparedBase]
  simp [priorQueryValue, nodeFieldValue,
    FrameCodec.encodeNode, FrameCodec.nodeDigits,
    FrameCodec.encodeList, PackedDigits.push]

private theorem installPriorComputation_runs
    {horizon : ℕ}
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store)
    (tape : TapeIndex workTapeCount)
    (requested interval center : ℕ)
    (htape : store (ControlDecode.nodeTape regs) = tape.val)
    (hrequested : store (requestedBlock regs) = requested)
    (hinterval : store (priorInterval regs) = interval)
    (hcenter : store (priorCenter regs) = center)
    (hone : store (movementDivision regs).one = 1)
    (hcontains :
      NeighborhoodGraph.NeighborhoodContains center requested) :
    ∃ final,
      Runs (installPriorComputation regs) store final ∧
      final (Layout.nodeCode regs) =
        FrameCodec.encodeNode
          (store (Layout.chunkRadix regs))
          (priorQueryValue
            (horizon := horizon) tape requested
            (some (some (interval, center)))) ∧
      final (Layout.codecDigit regs) = 0 := by
  let withInterval :=
    Function.update store
      (ControlDecode.nodePayload1 regs)
      (store (priorInterval regs))
  have hcopyRun :
      Runs
        (ControlDecode.copy
          (ControlDecode.nodePayload1 regs)
          (priorInterval regs))
        store withInterval := by
    exact copy_update_runs store
      (regs.injective.ne (by decide))
  let withLowerSlot :=
    (Basic.imm (ControlDecode.nodePayload0 regs) 0).exec
      withInterval
  have hlowerSlotRun :
      Runs
        (.basic (.imm (ControlDecode.nodePayload0 regs) 0))
        withInterval withLowerSlot :=
    Runs.basic _ _
  let withLower :=
    (Basic.sub (movementDivision regs).value
      (priorCenter regs) (movementDivision regs).one).exec
        withLowerSlot
  have hlowerRun :
      Runs
        (.basic
          (.sub (movementDivision regs).value
            (priorCenter regs) (movementDivision regs).one))
        withLowerSlot withLower :=
    Runs.basic _ _
  let testedLower :=
    (Basic.sub (movementDivision regs).test
      (requestedBlock regs) (movementDivision regs).value).exec
        withLower
  have htestLowerRun :
      Runs
        (.basic
          (.sub (movementDivision regs).test
            (requestedBlock regs) (movementDivision regs).value))
        withLower testedLower :=
    Runs.basic _ _
  have htestedLowerTest :
      testedLower (movementDivision regs).test =
        requested - (center - 1) := by
    simp [testedLower, withLower, withLowerSlot, withInterval,
      Basic.exec, movementDivision, movementMap, priorMap,
      ControlDecode.nodePayload0, ControlDecode.nodePayload1,
      ControlDecode.second, ControlDecode.third,
      regs.injective.eq_iff, hrequested, hcenter]
    change
      requested - (center - store (regs.index 17)) =
        requested - (center - 1)
    change store (regs.index 17) = 1 at hone
    rw [hone]
  have htestedLowerTape :
      testedLower (ControlDecode.nodeTape regs) = tape.val := by
    simp [testedLower, withLower, withLowerSlot, withInterval,
      Basic.exec, movementDivision, movementMap, priorMap,
      ControlDecode.nodeTape, ControlDecode.nodePayload0,
      ControlDecode.nodePayload1, ControlDecode.first,
      ControlDecode.second, ControlDecode.third,
      regs.injective.eq_iff, htape]
  have htestedLowerPayload0 :
      testedLower (ControlDecode.nodePayload0 regs) = 0 := by
    simp [testedLower, withLower, withLowerSlot, Basic.exec,
      movementDivision, movementMap, ControlDecode.nodePayload0,
      ControlDecode.second, regs.injective.eq_iff]
  have htestedLowerPayload1 :
      testedLower (ControlDecode.nodePayload1 regs) = interval := by
    simp [testedLower, withLower, withLowerSlot, withInterval,
      Basic.exec, movementDivision, movementMap,
      ControlDecode.nodePayload0, ControlDecode.nodePayload1,
      ControlDecode.second, ControlDecode.third, priorMap,
      regs.injective.eq_iff, hinterval]
  have htestedLowerBase :
      testedLower (Layout.chunkRadix regs) =
        store (Layout.chunkRadix regs) := by
    simp [testedLower, withLower, withLowerSlot, withInterval,
      Basic.exec, movementDivision, movementMap, Layout.chunkRadix,
      ControlDecode.nodePayload0, ControlDecode.nodePayload1,
      ControlDecode.second, ControlDecode.third,
      regs.injective.eq_iff]
  by_cases hlower : requested = center - 1
  · have htestZero :
        testedLower (movementDivision regs).test = 0 := by
      rw [htestedLowerTest, hlower]
      omega
    have hmatching :
        NeighborhoodGraph.matchingSlot center requested =
          .lower := by
      unfold NeighborhoodGraph.matchingSlot
      rw [if_pos hlower]
    obtain ⟨final, hencodeRun, hencodePost⟩ :=
      encodeNodeFields_runs_internal regs 2 testedLower
    have hrun :
        Runs (installPriorComputation regs) store final := by
      simpa [installPriorComputation, Cmd.seqList] using
        Runs.seq hcopyRun
          (Runs.seq hlowerSlotRun
            (Runs.seq hlowerRun
              (Runs.seq htestLowerRun
                (Runs.ifZero htestZero hencodeRun))))
    refine ⟨final, hrun, ?_, hencodePost.codecDigit_eq⟩
    rw [hencodePost.nodeCode_eq]
    rw [htestedLowerTape, htestedLowerPayload0,
      htestedLowerPayload1, htestedLowerBase]
    simp [priorQueryValue, hmatching,
      nodeFieldValue, FrameCodec.encodeNode,
      FrameCodec.nodeDigits, FrameCodec.encodeList,
      PackedDigits.push, NeighborhoodGraph.Slot.toFin]
  · have htestNonzero :
        testedLower (movementDivision regs).test ≠ 0 := by
      rw [htestedLowerTest]
      unfold NeighborhoodGraph.NeighborhoodContains at hcontains
      rcases hcontains with hcontains | hcontains | hcontains
      · exact (hlower hcontains).elim
      · omega
      · omega
    let withCenterSlot :=
      (Basic.imm (ControlDecode.nodePayload0 regs) 1).exec
        testedLower
    have hcenterSlotRun :
        Runs
          (.basic (.imm (ControlDecode.nodePayload0 regs) 1))
          testedLower withCenterSlot :=
      Runs.basic _ _
    let testedCenter :=
      (Basic.sub (movementDivision regs).test
        (requestedBlock regs) (priorCenter regs)).exec
          withCenterSlot
    have htestCenterRun :
        Runs
          (.basic
            (.sub (movementDivision regs).test
              (requestedBlock regs) (priorCenter regs)))
          withCenterSlot testedCenter :=
      Runs.basic _ _
    have htestedCenterTest :
        testedCenter (movementDivision regs).test =
          requested - center := by
      simp [testedCenter, withCenterSlot, testedLower, withLower,
        withLowerSlot, withInterval, Basic.exec, movementDivision,
        movementMap, priorMap, ControlDecode.nodePayload0,
        ControlDecode.nodePayload1, ControlDecode.second,
        ControlDecode.third, regs.injective.eq_iff,
        hrequested, hcenter]
    have htestedCenterTape :
        testedCenter (ControlDecode.nodeTape regs) = tape.val := by
      simp [testedCenter, withCenterSlot,
        ControlDecode.nodePayload0, ControlDecode.second,
        movementDivision, movementMap, Basic.exec,
        regs.injective.eq_iff, htestedLowerTape]
    have htestedCenterPayload0 :
        testedCenter (ControlDecode.nodePayload0 regs) = 1 := by
      simp [testedCenter, withCenterSlot,
        ControlDecode.nodePayload0, ControlDecode.second,
        movementDivision, movementMap, Basic.exec,
        regs.injective.eq_iff]
    have htestedCenterPayload1 :
        testedCenter (ControlDecode.nodePayload1 regs) = interval := by
      simp [testedCenter, withCenterSlot,
        ControlDecode.nodePayload0, ControlDecode.nodePayload1,
        ControlDecode.second, ControlDecode.third,
        movementDivision, movementMap, Basic.exec,
        regs.injective.eq_iff, htestedLowerPayload1]
    have htestedCenterBase :
        testedCenter (Layout.chunkRadix regs) =
          store (Layout.chunkRadix regs) := by
      simp [testedCenter, withCenterSlot,
        Layout.chunkRadix, ControlDecode.nodePayload0,
        ControlDecode.second, movementDivision, movementMap,
        Basic.exec, regs.injective.eq_iff, htestedLowerBase]
    by_cases hmiddle : requested = center
    · have htestZero :
          testedCenter (movementDivision regs).test = 0 := by
        rw [htestedCenterTest, hmiddle]
        omega
      have hmatching :
          NeighborhoodGraph.matchingSlot center requested =
            .center := by
        unfold NeighborhoodGraph.matchingSlot
        rw [if_neg hlower, if_pos hmiddle]
      obtain ⟨final, hencodeRun, hencodePost⟩ :=
        encodeNodeFields_runs_internal regs 2 testedCenter
      have hrun :
          Runs (installPriorComputation regs) store final := by
        simpa [installPriorComputation, Cmd.seqList] using
          Runs.seq hcopyRun
            (Runs.seq hlowerSlotRun
              (Runs.seq hlowerRun
                (Runs.seq htestLowerRun
                  (Runs.ifNonzero htestNonzero
                    (Runs.seq hcenterSlotRun
                      (Runs.seq htestCenterRun
                        (Runs.ifZero htestZero hencodeRun)))))))
      refine ⟨final, hrun, ?_, hencodePost.codecDigit_eq⟩
      rw [hencodePost.nodeCode_eq]
      rw [htestedCenterTape, htestedCenterPayload0,
        htestedCenterPayload1, htestedCenterBase]
      simp [priorQueryValue, hmatching,
        nodeFieldValue, FrameCodec.encodeNode,
        FrameCodec.nodeDigits, FrameCodec.encodeList,
        PackedDigits.push, NeighborhoodGraph.Slot.toFin]
    · have htestNonzeroCenter :
          testedCenter (movementDivision regs).test ≠ 0 := by
        rw [htestedCenterTest]
        unfold NeighborhoodGraph.NeighborhoodContains at hcontains
        rcases hcontains with hcontains | hcontains | hcontains
        · exact (hlower hcontains).elim
        · exact (hmiddle hcontains).elim
        · omega
      have hmatching :
          NeighborhoodGraph.matchingSlot center requested =
            .upper := by
        unfold NeighborhoodGraph.matchingSlot
        rw [if_neg hlower, if_neg hmiddle]
      let withUpperSlot :=
        (Basic.imm (ControlDecode.nodePayload0 regs) 2).exec
          testedCenter
      have hupperSlotRun :
          Runs
            (.basic (.imm (ControlDecode.nodePayload0 regs) 2))
            testedCenter withUpperSlot :=
        Runs.basic _ _
      have hupperTape :
          withUpperSlot (ControlDecode.nodeTape regs) = tape.val := by
        simp [withUpperSlot, Basic.exec,
          ControlDecode.nodeTape, ControlDecode.nodePayload0,
          ControlDecode.first, ControlDecode.second,
          regs.injective.eq_iff, htestedCenterTape]
      have hupperPayload0 :
          withUpperSlot (ControlDecode.nodePayload0 regs) = 2 := by
        simp [withUpperSlot, Basic.exec]
      have hupperPayload1 :
          withUpperSlot (ControlDecode.nodePayload1 regs) =
            interval := by
        simp [withUpperSlot, Basic.exec,
          ControlDecode.nodePayload0, ControlDecode.nodePayload1,
          ControlDecode.second, ControlDecode.third,
          regs.injective.eq_iff, htestedCenterPayload1]
      have hupperBase :
          withUpperSlot (Layout.chunkRadix regs) =
            store (Layout.chunkRadix regs) := by
        simp [withUpperSlot, Basic.exec, Layout.chunkRadix,
          ControlDecode.nodePayload0, ControlDecode.second,
          regs.injective.eq_iff, htestedCenterBase]
      obtain ⟨final, hencodeRun, hencodePost⟩ :=
        encodeNodeFields_runs_internal regs 2 withUpperSlot
      have hrun :
          Runs (installPriorComputation regs) store final := by
        simpa [installPriorComputation, Cmd.seqList] using
          Runs.seq hcopyRun
            (Runs.seq hlowerSlotRun
              (Runs.seq hlowerRun
                (Runs.seq htestLowerRun
                  (Runs.ifNonzero htestNonzero
                    (Runs.seq hcenterSlotRun
                      (Runs.seq htestCenterRun
                        (Runs.ifNonzero htestNonzeroCenter
                          (Runs.seq hupperSlotRun hencodeRun))))))))
      refine ⟨final, hrun, ?_, hencodePost.codecDigit_eq⟩
      rw [hencodePost.nodeCode_eq]
      rw [hupperTape, hupperPayload0, hupperPayload1, hupperBase]
      simp [priorQueryValue, hmatching,
        nodeFieldValue, FrameCodec.encodeNode,
        FrameCodec.nodeDigits, FrameCodec.encodeList,
        PackedDigits.push, NeighborhoodGraph.Slot.toFin]

theorem installPrior_runs_internal
    {horizon : ℕ}
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store)
    (tape : TapeIndex workTapeCount) (requested : ℕ)
    (result : Option (Option (ℕ × ℕ)))
    (hvalid :
      store (centerValid regs) = priorValidValue result)
    (hfound :
      store (priorFound regs) = priorFoundValue result)
    (hinterval :
      store (priorInterval regs) = priorIntervalValue result)
    (hcenter :
      store (priorCenter regs) = priorCenterValue result)
    (htape : store (ControlDecode.nodeTape regs) = tape.val)
    (hrequested : store (requestedBlock regs) = requested)
    (hone : store (movementDivision regs).one = 1)
    (hcontains :
      ∀ interval center,
        result = some (some (interval, center)) →
          NeighborhoodGraph.NeighborhoodContains center requested) :
    ∃ final,
      Runs (installPrior regs) store final ∧
      InstallPriorPost tape requested result regs store final := by
  cases result with
  | none =>
      have hvalidZero :
          store (centerValid regs) = 0 := by
        simpa [priorValidValue] using hvalid
      obtain ⟨final, hfailureRun, hnode, hdigit⟩ :=
        installFailure_runs
          (workTapeCount := workTapeCount) (horizon := horizon)
          regs store
      have hrun : Runs (installPrior regs) store final :=
        Runs.ifZero hvalidZero hfailureRun
      refine ⟨final, hrun, ?_⟩
      exact
        { nodeCode_eq := by
            simpa [priorQueryValue] using hnode
          codecDigit_eq := hdigit
          eq_outside := fun address haddress =>
            Footprint.runs_eq_outside
              (installPrior_writesWithin_internal regs)
              hrun haddress }
  | some result =>
      have hvalidOne :
          store (centerValid regs) = 1 := by
        simpa [priorValidValue] using hvalid
      have hvalidNonzero :
          store (centerValid regs) ≠ 0 := by
        rw [hvalidOne]
        omega
      cases result with
      | none =>
          have hfoundZero :
              store (priorFound regs) = 0 := by
            simpa [priorFoundValue] using hfound
          obtain ⟨final, hsourceRun, hnode, hdigit⟩ :=
            installPriorSource_runs
              (workTapeCount := workTapeCount) (horizon := horizon)
              regs store tape requested htape hrequested
          have hrun : Runs (installPrior regs) store final :=
            Runs.ifNonzero hvalidNonzero
              (Runs.ifZero hfoundZero hsourceRun)
          refine ⟨final, hrun, ?_⟩
          exact
            { nodeCode_eq := hnode
              codecDigit_eq := hdigit
              eq_outside := fun address haddress =>
                Footprint.runs_eq_outside
                  (installPrior_writesWithin_internal regs)
                  hrun haddress }
      | some result =>
          rcases result with ⟨interval, center⟩
          have hfoundOne :
              store (priorFound regs) = 1 := by
            simpa [priorFoundValue] using hfound
          have hfoundNonzero :
              store (priorFound regs) ≠ 0 := by
            rw [hfoundOne]
            omega
          have hintervalEq :
              store (priorInterval regs) = interval := by
            simpa [priorIntervalValue] using hinterval
          have hcenterEq :
              store (priorCenter regs) = center := by
            simpa [priorCenterValue] using hcenter
          have hcontainsPair :
              NeighborhoodGraph.NeighborhoodContains center requested :=
            hcontains interval center rfl
          obtain ⟨final, hcomputationRun, hnode, hdigit⟩ :=
            installPriorComputation_runs
              (workTapeCount := workTapeCount) (horizon := horizon)
              regs store tape requested interval center htape hrequested
              hintervalEq hcenterEq hone hcontainsPair
          have hrun : Runs (installPrior regs) store final :=
            Runs.ifNonzero hvalidNonzero
              (Runs.ifNonzero hfoundNonzero hcomputationRun)
          refine ⟨final, hrun, ?_⟩
          exact
            { nodeCode_eq := hnode
              codecDigit_eq := hdigit
              eq_outside := fun address haddress =>
                Footprint.runs_eq_outside
                  (installPrior_writesWithin_internal regs)
                  hrun haddress }

theorem installPrior_frameChild_runs_internal
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (code :
      Fin
        (3 ^
          NeighborhoodGraph.Guess.Enumeration.movementCount
            workTapeCount instanceData.horizon))
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store)
    (parentTape tape : TapeIndex workTapeCount)
    (parentSlot slot : NeighborhoodGraph.Slot)
    (interval : ℕ)
    (hinterval : interval < instanceData.horizon)
    (current : ℕ)
    (hcurrent :
      derivedCenterValue
          workTapeCount code.val tape.val interval =
        some current)
    (hvalid :
      store (centerValid regs) =
        priorValidValue
          (priorSearchValue
            workTapeCount code.val tape.val
            (NeighborhoodGraph.neighborBlock current slot)
            interval))
    (hfound :
      store (priorFound regs) =
        priorFoundValue
          (priorSearchValue
            workTapeCount code.val tape.val
            (NeighborhoodGraph.neighborBlock current slot)
            interval))
    (hpriorInterval :
      store (priorInterval regs) =
        priorIntervalValue
          (priorSearchValue
            workTapeCount code.val tape.val
            (NeighborhoodGraph.neighborBlock current slot)
            interval))
    (hpriorCenter :
      store (priorCenter regs) =
        priorCenterValue
          (priorSearchValue
            workTapeCount code.val tape.val
            (NeighborhoodGraph.neighborBlock current slot)
            interval))
    (htape : store (ControlDecode.nodeTape regs) = tape.val)
    (hrequested :
      store (requestedBlock regs) =
        NeighborhoodGraph.neighborBlock current slot)
    (hone : store (movementDivision regs).one = 1)
    (hguess :
      instanceData.guess =
        NeighborhoodGraph.Guess.Enumeration.candidateGuess code)
    (hnode :
      frame.node =
        .graph (.computation parentTape parentSlot interval)) :
    ∃ final,
      Runs (installPrior regs) store final ∧
      final (Layout.nodeCode regs) =
        FrameCodec.encodeNode
          (store (Layout.chunkRadix regs))
          (NeighborhoodScheduler.Frame.childNode frame
            (NeighborhoodGraph.predecessorIndexEquiv workTapeCount
              (.content slot, tape))) ∧
      final (Layout.codecDigit regs) = 0 ∧
      ∀ address, address ∉ priorAssemblyFootprint regs →
        final address = store address := by
  let requested := NeighborhoodGraph.neighborBlock current slot
  let result :=
    priorSearchValue
      workTapeCount code.val tape.val requested interval
  have hcontains :
      ∀ previous center,
        result = some (some (previous, center)) →
          NeighborhoodGraph.NeighborhoodContains center requested := by
    intro previous center hsearch
    exact
      (priorSearchValue_some_some_maximal
        workTapeCount code.val tape.val requested interval
        previous center hsearch).2.2.1
  obtain ⟨final, hrun, hpost⟩ :=
    installPrior_runs_internal
      (horizon := instanceData.horizon)
      regs store tape requested result hvalid hfound hpriorInterval
      hpriorCenter htape hrequested hone hcontains
  refine ⟨final, hrun, ?_, hpost.codecDigit_eq, hpost.eq_outside⟩
  rw [hpost.nodeCode_eq]
  rw [priorQueryValue_frameChild_internal
    code frame parentTape tape parentSlot slot interval hinterval
    current hcurrent hguess hnode]

private theorem chunkRadix_not_mem_prior
    (regs : NeighborhoodTrial.Registers controller) :
    Layout.chunkRadix regs ∉ priorFootprint regs := by
  simp [priorFootprint, centerFootprint, movementFootprint,
    movementMap, centerMap, priorMap, Layout.chunkRadix,
    ControlDecode.nodePayload1, ControlDecode.third,
    regs.injective.eq_iff]
  decide

theorem scanAndInstallPrior_frameChild_runs_internal
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (code :
      Fin
        (3 ^
          NeighborhoodGraph.Guess.Enumeration.movementCount
            workTapeCount instanceData.horizon))
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store)
    (parentTape tape : TapeIndex workTapeCount)
    (parentSlot slot : NeighborhoodGraph.Slot)
    (interval : ℕ)
    (hinterval : interval < instanceData.horizon)
    (current : ℕ)
    (hcurrent :
      derivedCenterValue
          workTapeCount code.val tape.val interval =
        some current)
    (hstoreGuess : store controller.guess = code.val)
    (htape : store (ControlDecode.nodeTape regs) = tape.val)
    (hrequested :
      store (requestedBlock regs) =
        NeighborhoodGraph.neighborBlock current slot)
    (hstoreInterval :
      store (ControlDecode.nodePayload1 regs) = interval)
    (hguess :
      instanceData.guess =
        NeighborhoodGraph.Guess.Enumeration.candidateGuess code)
    (hnode :
      frame.node =
        .graph (.computation parentTape parentSlot interval)) :
    ∃ final,
      Runs
        (scanAndInstallPrior workTapeCount controller regs)
        store final ∧
      final (Layout.nodeCode regs) =
        FrameCodec.encodeNode
          (store (Layout.chunkRadix regs))
          (NeighborhoodScheduler.Frame.childNode frame
            (NeighborhoodGraph.predecessorIndexEquiv workTapeCount
              (.content slot, tape))) ∧
      final (Layout.codecDigit regs) = 0 ∧
      ∀ address, address ∉ priorAssemblyFootprint regs →
        final address = store address := by
  let requested := NeighborhoodGraph.neighborBlock current slot
  obtain ⟨scanned, hscanRun, hscanPost⟩ :=
    scanPrior_runs_internal
      workTapeCount controller regs store code.val tape.val
      requested interval hstoreGuess htape hrequested hstoreInterval
  obtain ⟨final, hinstallRun, hnodeCode, hdigit, _hinstallOutside⟩ :=
    installPrior_frameChild_runs_internal
      code frame regs scanned parentTape tape parentSlot slot
      interval hinterval current hcurrent
      hscanPost.valid_eq hscanPost.found_eq
      hscanPost.interval_eq hscanPost.center_eq
      hscanPost.tape_eq hscanPost.requested_eq hscanPost.one_eq
      hguess hnode
  have hrun :
      Runs
        (scanAndInstallPrior workTapeCount controller regs)
        store final := by
    exact Runs.seq hscanRun hinstallRun
  have hbase :
      scanned (Layout.chunkRadix regs) =
        store (Layout.chunkRadix regs) :=
    hscanPost.eq_outside _ (chunkRadix_not_mem_prior regs)
  refine ⟨final, hrun, ?_, hdigit, ?_⟩
  · rw [hnodeCode, hbase]
  · intro address haddress
    exact Footprint.runs_eq_outside
      (scanAndInstallPrior_writesWithin_internal
        workTapeCount controller regs)
      hrun haddress

theorem installChronological_runs_internal
    {horizon : ℕ}
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store)
    (tape : TapeIndex workTapeCount)
    (interval : ℕ) (result : Option ℕ)
    (hvalid :
      store (centerValid regs) = centerValidValue result)
    (hcenter :
      store (centerValue regs) = centerOutputValue result)
    (htape : store (ControlDecode.nodeTape regs) = tape.val)
    (hinterval :
      store (ControlDecode.nodePayload1 regs) = interval)
    (hone : store (movementDivision regs).one = 1) :
    ∃ final,
      Runs (installChronological regs) store final ∧
      InstallChronologicalPost tape interval result regs store final := by
  cases result with
  | none =>
      have hvalidZero :
          store (centerValid regs) = 0 := by
        simpa [centerValidValue] using hvalid
      obtain ⟨final, hfailureRun, hnode, hdigit⟩ :=
        installFailure_runs
          (workTapeCount := workTapeCount) (horizon := horizon)
          regs store
      have hrun :
          Runs (installChronological regs) store final :=
        Runs.ifZero hvalidZero hfailureRun
      refine ⟨final, hrun, ?_⟩
      exact
        { nodeCode_eq := by
            simpa [chronologicalQueryValue] using hnode
          codecDigit_eq := hdigit
          eq_outside := fun address haddress =>
            Footprint.runs_eq_outside
              (installChronological_writesWithin_internal regs)
              hrun haddress }
  | some center =>
      have hvalidOne :
          store (centerValid regs) = 1 := by
        simpa [centerValidValue] using hvalid
      have hvalidNonzero :
          store (centerValid regs) ≠ 0 := by
        rw [hvalidOne]
        omega
      have hcenterEq :
          store (centerValue regs) = center := by
        simpa [centerOutputValue] using hcenter
      have hpayloadEq :
          store (ControlDecode.nodePayload0 regs) = center := by
        change store (regs.index 10) = center
        change store (regs.index 10) = center at hcenterEq
        exact hcenterEq
      cases interval with
      | zero =>
          have hintervalZero :
              store (ControlDecode.nodePayload1 regs) = 0 :=
            hinterval
          obtain ⟨final, hencodeRun, hencodePost⟩ :=
            encodeNodeFields_runs_internal regs 1 store
          have hrun :
              Runs (installChronological regs) store final :=
            Runs.ifNonzero hvalidNonzero
              (Runs.ifZero hintervalZero hencodeRun)
          refine ⟨final, hrun, ?_⟩
          refine
            { nodeCode_eq := ?_
              codecDigit_eq := hencodePost.codecDigit_eq
              eq_outside := fun address haddress =>
                Footprint.runs_eq_outside
                  (installChronological_writesWithin_internal regs)
                  hrun haddress }
          rw [hencodePost.nodeCode_eq]
          rw [htape, hpayloadEq, hintervalZero]
          simp [chronologicalQueryValue, nodeFieldValue,
            FrameCodec.encodeNode, FrameCodec.nodeDigits,
            FrameCodec.encodeList, PackedDigits.push]
      | succ previous =>
          have hintervalNonzero :
              store (ControlDecode.nodePayload1 regs) ≠ 0 := by
            rw [hinterval]
            omega
          let ops : List Basic :=
            [.sub (ControlDecode.nodePayload1 regs)
                (ControlDecode.nodePayload1 regs)
                (movementDivision regs).one,
              .imm (ControlDecode.nodePayload0 regs) 1]
          let prepared := Basic.execList ops store
          have hprepareRun :
              Runs (Cmd.basics ops) store prepared :=
            basics_runs ops store
          have hpreparedInterval :
              prepared (ControlDecode.nodePayload1 regs) = previous := by
            simp [prepared, ops, Basic.execList, Basic.exec,
              ControlDecode.nodePayload0, ControlDecode.nodePayload1,
              ControlDecode.second, ControlDecode.third,
              movementDivision, movementMap,
              regs.injective.eq_iff, hinterval]
            change store (regs.index 17) = 1 at hone
            change
              previous + 1 - store (regs.index 17) = previous
            rw [hone]
            omega
          have hpreparedPayload :
              prepared (ControlDecode.nodePayload0 regs) = 1 := by
            simp [prepared, ops, Basic.execList, Basic.exec]
          have hpreparedTape :
              prepared (ControlDecode.nodeTape regs) = tape.val := by
            simp [prepared, ops, Basic.execList, Basic.exec,
              ControlDecode.nodeTape, ControlDecode.nodePayload0,
              ControlDecode.nodePayload1, ControlDecode.first,
              ControlDecode.second, ControlDecode.third,
              movementDivision, movementMap,
              regs.injective.eq_iff, htape]
          have hpreparedBase :
              prepared (Layout.chunkRadix regs) =
                store (Layout.chunkRadix regs) := by
            simp [prepared, ops, Basic.execList, Basic.exec,
              Layout.chunkRadix, ControlDecode.nodePayload0,
              ControlDecode.nodePayload1, ControlDecode.second,
              ControlDecode.third, movementDivision, movementMap,
              regs.injective.eq_iff]
          obtain ⟨final, hencodeRun, hencodePost⟩ :=
            encodeNodeFields_runs_internal regs 2 prepared
          have hrun :
              Runs (installChronological regs) store final := by
            simpa [installChronological, ops] using
              Runs.ifNonzero hvalidNonzero
                (Runs.ifNonzero hintervalNonzero
                  (Runs.seq hprepareRun hencodeRun))
          refine ⟨final, hrun, ?_⟩
          refine
            { nodeCode_eq := ?_
              codecDigit_eq := hencodePost.codecDigit_eq
              eq_outside := fun address haddress =>
                Footprint.runs_eq_outside
                  (installChronological_writesWithin_internal regs)
                  hrun haddress }
          rw [hencodePost.nodeCode_eq]
          rw [hpreparedTape, hpreparedPayload, hpreparedInterval,
            hpreparedBase]
          simp [chronologicalQueryValue, nodeFieldValue,
            FrameCodec.encodeNode, FrameCodec.nodeDigits,
            FrameCodec.encodeList, PackedDigits.push,
            NeighborhoodGraph.Slot.toFin]

private theorem chunkRadix_not_mem_center
    (regs : NeighborhoodTrial.Registers controller) :
    Layout.chunkRadix regs ∉ centerFootprint regs := by
  intro hmember
  exact chunkRadix_not_mem_prior regs
    (centerFootprint_subset_prior regs hmember)

private theorem installContentChild_frameChild_runs
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (code :
      Fin
        (3 ^
          NeighborhoodGraph.Guess.Enumeration.movementCount
            workTapeCount instanceData.horizon))
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store)
    (parentTape tape : TapeIndex workTapeCount)
    (parentSlot slot : NeighborhoodGraph.Slot)
    (interval : ℕ)
    (hinterval : interval < instanceData.horizon)
    (hstoreGuess : store controller.guess = code.val)
    (htape : store (ControlDecode.nodeTape regs) = tape.val)
    (hstoreInterval :
      store (ControlDecode.nodePayload1 regs) = interval)
    (hguess :
      instanceData.guess =
        NeighborhoodGraph.Guess.Enumeration.candidateGuess code)
    (hnode :
      frame.node =
        .graph (.computation parentTape parentSlot interval)) :
    ∃ final,
      Runs
        (installContentChild workTapeCount controller regs slot)
        store final ∧
      final (Layout.nodeCode regs) =
        FrameCodec.encodeNode
          (store (Layout.chunkRadix regs))
          (NeighborhoodScheduler.Frame.childNode frame
            (NeighborhoodGraph.predecessorIndexEquiv workTapeCount
              (.content slot, tape))) ∧
      final (Layout.codecDigit regs) = 0 ∧
      ∀ address, address ∉ priorAssemblyFootprint regs →
        final address = store address := by
  obtain ⟨centered, hderiveRun, hderivePost⟩ :=
    deriveCenter_runs_internal
      workTapeCount controller regs store code.val tape.val interval
      hstoreGuess htape hstoreInterval
  have hcenteredBase :
      centered (Layout.chunkRadix regs) =
        store (Layout.chunkRadix regs) :=
    hderivePost.eq_outside _
      (chunkRadix_not_mem_center regs)
  generalize hresult :
    derivedCenterValue workTapeCount code.val tape.val interval =
      result
  cases result with
  | none =>
      have hvalidZero :
          centered (centerValid regs) = 0 := by
        simpa [hresult, centerValidValue] using
          hderivePost.valid_eq
      obtain ⟨final, hfailureRun, hfailureNode, hdigit⟩ :=
        installFailure_runs
          (workTapeCount := workTapeCount)
          (horizon := instanceData.horizon) regs centered
      have hrun :
          Runs
            (installContentChild
              workTapeCount controller regs slot)
            store final := by
        simpa [installContentChild] using
          Runs.seq hderiveRun
            (Runs.ifZero hvalidZero hfailureRun)
      have hcandidate :
          NeighborhoodGraph.Guess.CenterGuess.derivedCenter
              (NeighborhoodGraph.Guess.Enumeration.candidateGuess code)
              tape interval =
            none := by
        rw [← derivedCenterValue_candidateGuess_internal
          code tape interval (by omega)]
        exact hresult
      have hchildFailure :
          NeighborhoodScheduler.Frame.childNode frame
              (NeighborhoodGraph.predecessorIndexEquiv
                workTapeCount (.content slot, tape)) =
            .failure := by
        rw [NeighborhoodScheduler.Frame.childNode, hnode, hguess]
        simp [NeighborhoodEvaluator.childAt, hinterval,
          NeighborhoodGraph.Guess.CenterGuess.predecessorAt?,
          NeighborhoodGraph.Guess.CenterGuess.predecessor?,
          NeighborhoodGraph.Guess.CenterGuess.contentPredecessor?,
          hcandidate]
      refine ⟨final, hrun, ?_, hdigit, ?_⟩
      · calc
          final (Layout.nodeCode regs) =
              FrameCodec.encodeNode
                (centered (Layout.chunkRadix regs))
                (NeighborhoodEvaluator.QueryNode.failure :
                  NeighborhoodEvaluator.QueryNode
                    workTapeCount instanceData.horizon) :=
            hfailureNode
          _ = FrameCodec.encodeNode
                (store (Layout.chunkRadix regs))
                (NeighborhoodScheduler.Frame.childNode frame
                  (NeighborhoodGraph.predecessorIndexEquiv
                    workTapeCount (.content slot, tape))) := by
            rw [hcenteredBase, hchildFailure]
      · intro address haddress
        exact Footprint.runs_eq_outside
          (installContentChild_writesWithin
            workTapeCount controller regs slot)
          hrun haddress
  | some current =>
      have hvalidOne :
          centered (centerValid regs) = 1 := by
        simpa [hresult, centerValidValue] using
          hderivePost.valid_eq
      have hvalidNonzero :
          centered (centerValid regs) ≠ 0 := by
        rw [hvalidOne]
        omega
      have hcenterEq :
          centered (centerValue regs) = current := by
        simpa [hresult, centerOutputValue] using
          hderivePost.center_eq
      obtain ⟨adjusted, hadjustRun, hadjustRequested,
          hadjustOutside⟩ :=
        installRequestedBlock_runs
          regs centered current slot hcenterEq hderivePost.one_eq
      have hadjustGuess :
          adjusted controller.guess = code.val := by
        rw [hadjustOutside _
          (regs.index_ne_controller (priorMap 0) 2).symm]
        exact hderivePost.guess_eq
      have hadjustTape :
          adjusted (ControlDecode.nodeTape regs) = tape.val := by
        rw [hadjustOutside _
          (regs.injective.ne (by decide))]
        exact hderivePost.tape_eq
      have hadjustInterval :
          adjusted (ControlDecode.nodePayload1 regs) = interval := by
        rw [hadjustOutside _
          (regs.injective.ne (by decide))]
        exact hderivePost.interval_eq
      have hadjustBase :
          adjusted (Layout.chunkRadix regs) =
            store (Layout.chunkRadix regs) := by
        rw [hadjustOutside _
          (regs.injective.ne (by decide))]
        exact hcenteredBase
      obtain ⟨final, hscanInstallRun, hnodeCode, hdigit,
          _hscanInstallOutside⟩ :=
        scanAndInstallPrior_frameChild_runs_internal
          code frame controller regs adjusted parentTape tape
          parentSlot slot interval hinterval current hresult
          hadjustGuess hadjustTape hadjustRequested hadjustInterval
          hguess hnode
      have hrun :
          Runs
            (installContentChild
              workTapeCount controller regs slot)
            store final := by
        simpa [installContentChild] using
          Runs.seq hderiveRun
            (Runs.ifNonzero hvalidNonzero
              (Runs.seq hadjustRun hscanInstallRun))
      refine ⟨final, hrun, ?_, hdigit, ?_⟩
      · rw [hnodeCode, hadjustBase]
      · intro address haddress
        exact Footprint.runs_eq_outside
          (installContentChild_writesWithin
            workTapeCount controller regs slot)
          hrun haddress

private theorem installChronologicalChild_frameChild_runs
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (code :
      Fin
        (3 ^
          NeighborhoodGraph.Guess.Enumeration.movementCount
            workTapeCount instanceData.horizon))
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store)
    (parentTape tape : TapeIndex workTapeCount)
    (parentSlot : NeighborhoodGraph.Slot)
    (interval : ℕ)
    (hinterval : interval < instanceData.horizon)
    (hstoreGuess : store controller.guess = code.val)
    (htape : store (ControlDecode.nodeTape regs) = tape.val)
    (hstoreInterval :
      store (ControlDecode.nodePayload1 regs) = interval)
    (hguess :
      instanceData.guess =
        NeighborhoodGraph.Guess.Enumeration.candidateGuess code)
    (hnode :
      frame.node =
        .graph (.computation parentTape parentSlot interval)) :
    ∃ final,
      Runs
        (installChronologicalChild
          workTapeCount controller regs)
        store final ∧
      final (Layout.nodeCode regs) =
        FrameCodec.encodeNode
          (store (Layout.chunkRadix regs))
          (NeighborhoodScheduler.Frame.childNode frame
            (NeighborhoodGraph.predecessorIndexEquiv workTapeCount
              (.chronological, tape))) ∧
      final (Layout.codecDigit regs) = 0 ∧
      ∀ address, address ∉ priorAssemblyFootprint regs →
        final address = store address := by
  let result :=
    derivedCenterValue workTapeCount code.val tape.val interval
  obtain ⟨centered, hderiveRun, hderivePost⟩ :=
    deriveCenter_runs_internal
      workTapeCount controller regs store code.val tape.val interval
      hstoreGuess htape hstoreInterval
  obtain ⟨final, hinstallRun, hinstallPost⟩ :=
    installChronological_runs_internal
      (horizon := instanceData.horizon)
      controller regs centered tape interval result
      hderivePost.valid_eq hderivePost.center_eq
      hderivePost.tape_eq hderivePost.interval_eq
      hderivePost.one_eq
  have hrun :
      Runs
        (installChronologicalChild
          workTapeCount controller regs)
        store final :=
    Runs.seq hderiveRun hinstallRun
  have hbase :
      centered (Layout.chunkRadix regs) =
        store (Layout.chunkRadix regs) :=
    hderivePost.eq_outside _
      (chunkRadix_not_mem_center regs)
  have hsemantic :=
    chronologicalQueryValue_frameChild_internal
      code frame parentTape tape parentSlot interval hinterval
      result rfl hguess hnode
  refine ⟨final, hrun, ?_, hinstallPost.codecDigit_eq, ?_⟩
  · rw [hinstallPost.nodeCode_eq, hsemantic, hbase]
  · intro address haddress
    exact Footprint.runs_eq_outside
      (installChronologicalChild_writesWithin
        workTapeCount controller regs)
      hrun haddress

private theorem predecessorIndex_val
    (kind : NeighborhoodGraph.PredecessorKind)
    (tape : TapeIndex workTapeCount) :
    (NeighborhoodGraph.predecessorIndexEquiv
      workTapeCount (kind, tape)).val =
        tape.val +
          (workTapeCount + 2) *
            (NeighborhoodGraph.PredecessorKind.toFin kind).val := by
  rfl

private theorem predecessorIndex_mod
    (kind : NeighborhoodGraph.PredecessorKind)
    (tape : TapeIndex workTapeCount) :
    (NeighborhoodGraph.predecessorIndexEquiv
        workTapeCount (kind, tape)).val %
          (workTapeCount + 2) =
      tape.val := by
  rw [predecessorIndex_val,
    Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt tape.isLt]

private theorem predecessorIndex_div
    (kind : NeighborhoodGraph.PredecessorKind)
    (tape : TapeIndex workTapeCount) :
    (NeighborhoodGraph.predecessorIndexEquiv
        workTapeCount (kind, tape)).val /
          (workTapeCount + 2) =
      (NeighborhoodGraph.PredecessorKind.toFin kind).val := by
  rw [predecessorIndex_val,
    Nat.add_mul_div_left _ _ (by omega),
    Nat.div_eq_of_lt tape.isLt, Nat.zero_add]

private theorem decrementChildKind_runs
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store) (kind : ℕ)
    (hkind : store (movementDivision regs).quotient = kind)
    (hone : store (movementDivision regs).one = 1) :
    ∃ final,
      Runs
        (.basic
          (.sub (movementDivision regs).quotient
            (movementDivision regs).quotient
            (movementDivision regs).one))
        store final ∧
      final (movementDivision regs).quotient = kind - 1 ∧
      ∀ address,
        address ≠ (movementDivision regs).quotient →
          final address = store address := by
  let final :=
    (Basic.sub (movementDivision regs).quotient
      (movementDivision regs).quotient
      (movementDivision regs).one).exec store
  refine ⟨final, Runs.basic _ _, ?_, ?_⟩
  · simp [final, Basic.exec, hkind, hone]
  · intro address haddress
    simp [final, Basic.exec, Function.update_of_ne, haddress]

private theorem dispatchDecodedChild_frameChild_runs
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (code :
      Fin
        (3 ^
          NeighborhoodGraph.Guess.Enumeration.movementCount
            workTapeCount instanceData.horizon))
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store)
    (parentTape tape : TapeIndex workTapeCount)
    (parentSlot : NeighborhoodGraph.Slot)
    (kind : NeighborhoodGraph.PredecessorKind)
    (interval : ℕ)
    (hinterval : interval < instanceData.horizon)
    (hkind :
      store (movementDivision regs).quotient =
        (NeighborhoodGraph.PredecessorKind.toFin kind).val)
    (hone : store (movementDivision regs).one = 1)
    (hstoreGuess : store controller.guess = code.val)
    (htape : store (ControlDecode.nodeTape regs) = tape.val)
    (hstoreInterval :
      store (ControlDecode.nodePayload1 regs) = interval)
    (hguess :
      instanceData.guess =
        NeighborhoodGraph.Guess.Enumeration.candidateGuess code)
    (hnode :
      frame.node =
        .graph (.computation parentTape parentSlot interval)) :
    ∃ final,
      Runs
        (dispatchDecodedChild workTapeCount controller regs)
        store final ∧
      final (Layout.nodeCode regs) =
        FrameCodec.encodeNode
          (store (Layout.chunkRadix regs))
          (NeighborhoodScheduler.Frame.childNode frame
            (NeighborhoodGraph.predecessorIndexEquiv
              workTapeCount (kind, tape))) ∧
      final (Layout.codecDigit regs) = 0 ∧
      ∀ address, address ∉ priorAssemblyFootprint regs →
        final address = store address := by
  cases kind with
  | content slot =>
      cases slot with
      | lower =>
          have hkindZero :
              store (movementDivision regs).quotient = 0 := by
            simpa [NeighborhoodGraph.PredecessorKind.toFin,
              NeighborhoodGraph.Slot.toFin] using hkind
          obtain ⟨final, hbranchRun, hnodeCode, hdigit,
              _hbranchOutside⟩ :=
            installContentChild_frameChild_runs
              code frame controller regs store parentTape tape
              parentSlot .lower interval hinterval hstoreGuess
              htape hstoreInterval hguess hnode
          have hrun :
              Runs
                (dispatchDecodedChild
                  workTapeCount controller regs)
                store final :=
            Runs.ifZero hkindZero hbranchRun
          refine ⟨final, hrun, hnodeCode, hdigit, ?_⟩
          intro address haddress
          exact Footprint.runs_eq_outside
            (dispatchDecodedChild_writesWithin
              workTapeCount controller regs)
            hrun haddress
      | center =>
          have hkindOne :
              store (movementDivision regs).quotient = 1 := by
            simpa [NeighborhoodGraph.PredecessorKind.toFin,
              NeighborhoodGraph.Slot.toFin] using hkind
          have hkindNonzero :
              store (movementDivision regs).quotient ≠ 0 := by
            rw [hkindOne]
            omega
          obtain ⟨decremented, hdecrementRun, hdecrementKind,
              hdecrementOutside⟩ :=
            decrementChildKind_runs regs store 1 hkindOne hone
          have hdecrementZero :
              decremented (movementDivision regs).quotient = 0 := by
            simpa using hdecrementKind
          have hdecrementGuess :
              decremented controller.guess = code.val := by
            rw [hdecrementOutside _
              (regs.index_ne_controller (movementMap 1) 2).symm]
            exact hstoreGuess
          have hdecrementTape :
              decremented (ControlDecode.nodeTape regs) =
                tape.val := by
            rw [hdecrementOutside _
              (regs.injective.ne (by decide))]
            exact htape
          have hdecrementInterval :
              decremented (ControlDecode.nodePayload1 regs) =
                interval := by
            rw [hdecrementOutside _
              (regs.injective.ne (by decide))]
            exact hstoreInterval
          have hdecrementBase :
              decremented (Layout.chunkRadix regs) =
                store (Layout.chunkRadix regs) := by
            rw [hdecrementOutside _
              (regs.injective.ne (by decide))]
          obtain ⟨final, hbranchRun, hnodeCode, hdigit,
              _hbranchOutside⟩ :=
            installContentChild_frameChild_runs
              code frame controller regs decremented parentTape tape
              parentSlot .center interval hinterval hdecrementGuess
              hdecrementTape hdecrementInterval hguess hnode
          have hrun :
              Runs
                (dispatchDecodedChild
                  workTapeCount controller regs)
                store final := by
            exact Runs.ifNonzero hkindNonzero
              (Runs.seq hdecrementRun
                (Runs.ifZero hdecrementZero hbranchRun))
          refine ⟨final, hrun, ?_, hdigit, ?_⟩
          · rw [hnodeCode, hdecrementBase]
          · intro address haddress
            exact Footprint.runs_eq_outside
              (dispatchDecodedChild_writesWithin
                workTapeCount controller regs)
              hrun haddress
      | upper =>
          have hkindTwo :
              store (movementDivision regs).quotient = 2 := by
            simpa [NeighborhoodGraph.PredecessorKind.toFin,
              NeighborhoodGraph.Slot.toFin] using hkind
          have hkindNonzero :
              store (movementDivision regs).quotient ≠ 0 := by
            rw [hkindTwo]
            omega
          obtain ⟨first, hfirstRun, hfirstKind, hfirstOutside⟩ :=
            decrementChildKind_runs regs store 2 hkindTwo hone
          have hfirstOne :
              first (movementDivision regs).quotient = 1 := by
            simpa using hfirstKind
          have hfirstNonzero :
              first (movementDivision regs).quotient ≠ 0 := by
            rw [hfirstOne]
            omega
          have hfirstConstant :
              first (movementDivision regs).one = 1 := by
            rw [hfirstOutside _
              (division_index_ne regs
                (first := 3) (second := 1) (by decide))]
            exact hone
          obtain ⟨second, hsecondRun, hsecondKind,
              hsecondOutside⟩ :=
            decrementChildKind_runs
              regs first 1 hfirstOne hfirstConstant
          have hsecondZero :
              second (movementDivision regs).quotient = 0 := by
            simpa using hsecondKind
          have hsecondGuess :
              second controller.guess = code.val := by
            rw [hsecondOutside _
              (regs.index_ne_controller (movementMap 1) 2).symm]
            rw [hfirstOutside _
              (regs.index_ne_controller (movementMap 1) 2).symm]
            exact hstoreGuess
          have hsecondTape :
              second (ControlDecode.nodeTape regs) = tape.val := by
            rw [hsecondOutside _
              (regs.injective.ne (by decide))]
            rw [hfirstOutside _
              (regs.injective.ne (by decide))]
            exact htape
          have hsecondInterval :
              second (ControlDecode.nodePayload1 regs) =
                interval := by
            rw [hsecondOutside _
              (regs.injective.ne (by decide))]
            rw [hfirstOutside _
              (regs.injective.ne (by decide))]
            exact hstoreInterval
          have hsecondBase :
              second (Layout.chunkRadix regs) =
                store (Layout.chunkRadix regs) := by
            rw [hsecondOutside _
              (regs.injective.ne (by decide))]
            rw [hfirstOutside _
              (regs.injective.ne (by decide))]
          obtain ⟨final, hbranchRun, hnodeCode, hdigit,
              _hbranchOutside⟩ :=
            installContentChild_frameChild_runs
              code frame controller regs second parentTape tape
              parentSlot .upper interval hinterval hsecondGuess
              hsecondTape hsecondInterval hguess hnode
          have hrun :
              Runs
                (dispatchDecodedChild
                  workTapeCount controller regs)
                store final := by
            exact Runs.ifNonzero hkindNonzero
              (Runs.seq hfirstRun
                (Runs.ifNonzero hfirstNonzero
                  (Runs.seq hsecondRun
                    (Runs.ifZero hsecondZero hbranchRun))))
          refine ⟨final, hrun, ?_, hdigit, ?_⟩
          · rw [hnodeCode, hsecondBase]
          · intro address haddress
            exact Footprint.runs_eq_outside
              (dispatchDecodedChild_writesWithin
                workTapeCount controller regs)
              hrun haddress
  | chronological =>
      have hkindThree :
          store (movementDivision regs).quotient = 3 := by
        simpa [NeighborhoodGraph.PredecessorKind.toFin] using hkind
      have hkindNonzero :
          store (movementDivision regs).quotient ≠ 0 := by
        rw [hkindThree]
        omega
      obtain ⟨first, hfirstRun, hfirstKind, hfirstOutside⟩ :=
        decrementChildKind_runs regs store 3 hkindThree hone
      have hfirstTwo :
          first (movementDivision regs).quotient = 2 := by
        simpa using hfirstKind
      have hfirstNonzero :
          first (movementDivision regs).quotient ≠ 0 := by
        rw [hfirstTwo]
        omega
      have hfirstConstant :
          first (movementDivision regs).one = 1 := by
        rw [hfirstOutside _
          (division_index_ne regs
            (first := 3) (second := 1) (by decide))]
        exact hone
      obtain ⟨second, hsecondRun, hsecondKind,
          hsecondOutside⟩ :=
        decrementChildKind_runs
          regs first 2 hfirstTwo hfirstConstant
      have hsecondOne :
          second (movementDivision regs).quotient = 1 := by
        simpa using hsecondKind
      have hsecondNonzero :
          second (movementDivision regs).quotient ≠ 0 := by
        rw [hsecondOne]
        omega
      have hsecondGuess :
          second controller.guess = code.val := by
        rw [hsecondOutside _
          (regs.index_ne_controller (movementMap 1) 2).symm]
        rw [hfirstOutside _
          (regs.index_ne_controller (movementMap 1) 2).symm]
        exact hstoreGuess
      have hsecondTape :
          second (ControlDecode.nodeTape regs) = tape.val := by
        rw [hsecondOutside _
          (regs.injective.ne (by decide))]
        rw [hfirstOutside _
          (regs.injective.ne (by decide))]
        exact htape
      have hsecondInterval :
          second (ControlDecode.nodePayload1 regs) =
            interval := by
        rw [hsecondOutside _
          (regs.injective.ne (by decide))]
        rw [hfirstOutside _
          (regs.injective.ne (by decide))]
        exact hstoreInterval
      have hsecondBase :
          second (Layout.chunkRadix regs) =
            store (Layout.chunkRadix regs) := by
        rw [hsecondOutside _
          (regs.injective.ne (by decide))]
        rw [hfirstOutside _
          (regs.injective.ne (by decide))]
      obtain ⟨final, hbranchRun, hnodeCode, hdigit,
          _hbranchOutside⟩ :=
        installChronologicalChild_frameChild_runs
          code frame controller regs second parentTape tape
          parentSlot interval hinterval hsecondGuess hsecondTape
          hsecondInterval hguess hnode
      have hrun :
          Runs
            (dispatchDecodedChild
              workTapeCount controller regs)
            store final := by
        exact Runs.ifNonzero hkindNonzero
          (Runs.seq hfirstRun
            (Runs.ifNonzero hfirstNonzero
              (Runs.seq hsecondRun
                (Runs.ifNonzero hsecondNonzero hbranchRun))))
      refine ⟨final, hrun, ?_, hdigit, ?_⟩
      · rw [hnodeCode, hsecondBase]
      · intro address haddress
        exact Footprint.runs_eq_outside
          (dispatchDecodedChild_writesWithin
            workTapeCount controller regs)
          hrun haddress

theorem regenerateChild_frameChild_runs_internal
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (code :
      Fin
        (3 ^
          NeighborhoodGraph.Guess.Enumeration.movementCount
            workTapeCount instanceData.horizon))
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store)
    (parentTape tape : TapeIndex workTapeCount)
    (parentSlot : NeighborhoodGraph.Slot)
    (kind : NeighborhoodGraph.PredecessorKind)
    (interval : ℕ)
    (hinterval : interval < instanceData.horizon)
    (hdecoded :
      ControlDecode.EncodedNodePost regs frame.node store)
    (hchild :
      store (savedChildIndex regs) =
        (NeighborhoodGraph.predecessorIndexEquiv
          workTapeCount (kind, tape)).val)
    (hstoreGuess : store controller.guess = code.val)
    (hguess :
      instanceData.guess =
        NeighborhoodGraph.Guess.Enumeration.candidateGuess code)
    (hnode :
      frame.node =
        .graph (.computation parentTape parentSlot interval)) :
    ∃ final,
      Runs
        (regenerateChild workTapeCount controller regs)
        store final ∧
      final (Layout.nodeCode regs) =
        FrameCodec.encodeNode
          (store (Layout.chunkRadix regs))
          (NeighborhoodScheduler.Frame.childNode frame
            (NeighborhoodGraph.predecessorIndexEquiv
              workTapeCount (kind, tape))) ∧
      final (Layout.codecDigit regs) = 0 ∧
      ∀ address, address ∉ priorAssemblyFootprint regs →
        final address = store address := by
  have hstoreInterval :
      store (ControlDecode.nodePayload1 regs) = interval := by
    simpa [hnode, ControlDecode.expectedNodeValues] using
      hdecoded.payload1_eq
  obtain ⟨decoded, hdecodeRun, hdecodePost⟩ :=
    decodeChildIndex_runs_internal
      workTapeCount
      (NeighborhoodGraph.predecessorIndexEquiv
        workTapeCount (kind, tape)).val
      regs store hchild
  obtain ⟨taped, hcopyRun, hcopyValue, hcopyOutside⟩ :=
    copy_runs
      (ControlDecode.nodeTape regs)
      (movementDivision regs).value decoded
      (regs.injective.ne (by decide))
  have htapedTape :
      taped (ControlDecode.nodeTape regs) = tape.val := by
    calc
      taped (ControlDecode.nodeTape regs) =
          decoded (movementDivision regs).value :=
        hcopyValue
      _ =
          (NeighborhoodGraph.predecessorIndexEquiv
            workTapeCount (kind, tape)).val %
              (workTapeCount + 2) :=
        hdecodePost.tape_eq
      _ = tape.val := predecessorIndex_mod kind tape
  have htapedKind :
      taped (movementDivision regs).quotient =
        (NeighborhoodGraph.PredecessorKind.toFin kind).val := by
    have hquotientNeTape :
        (movementDivision regs).quotient ≠
          ControlDecode.nodeTape regs :=
      regs.injective.ne (by decide)
    calc
      taped (movementDivision regs).quotient =
          decoded (movementDivision regs).quotient := by
        rw [hcopyOutside _ hquotientNeTape]
      _ =
          (NeighborhoodGraph.predecessorIndexEquiv
            workTapeCount (kind, tape)).val /
              (workTapeCount + 2) :=
        hdecodePost.kind_eq
      _ =
          (NeighborhoodGraph.PredecessorKind.toFin kind).val :=
        predecessorIndex_div kind tape
  have htapedOne :
      taped (movementDivision regs).one = 1 := by
    have honeNeTape :
        (movementDivision regs).one ≠
          ControlDecode.nodeTape regs :=
      regs.injective.ne (by decide)
    rw [hcopyOutside _ honeNeTape]
    exact hdecodePost.one_eq
  have htapedGuess :
      taped controller.guess = code.val := by
    calc
      taped controller.guess = decoded controller.guess :=
        hcopyOutside _
          (regs.index_ne_controller (9 : Fin 34) 2).symm
      _ = store controller.guess :=
        hdecodePost.eq_outside _ (by
          intro hmember
          exact controller_guess_not_mem_center controller regs
            (movementFootprint_subset_center regs hmember))
      _ = code.val := hstoreGuess
  have htapedInterval :
      taped (ControlDecode.nodePayload1 regs) = interval := by
    calc
      taped (ControlDecode.nodePayload1 regs) =
          decoded (ControlDecode.nodePayload1 regs) := by
        rw [hcopyOutside _
          (regs.injective.ne (by decide))]
      _ = store (ControlDecode.nodePayload1 regs) :=
        hdecodePost.eq_outside _ (by
          intro hmember
          exact nodeInterval_not_mem_center regs
            (movementFootprint_subset_center regs hmember))
      _ = interval := hstoreInterval
  have htapedBase :
      taped (Layout.chunkRadix regs) =
        store (Layout.chunkRadix regs) := by
    calc
      taped (Layout.chunkRadix regs) =
          decoded (Layout.chunkRadix regs) := by
        rw [hcopyOutside _
          (regs.injective.ne (by decide))]
      _ = store (Layout.chunkRadix regs) :=
        hdecodePost.eq_outside _ (by
          intro hmember
          exact chunkRadix_not_mem_center regs
            (movementFootprint_subset_center regs hmember))
  obtain ⟨final, hdispatchRun, hnodeCode, hdigit,
      _hdispatchOutside⟩ :=
    dispatchDecodedChild_frameChild_runs
      code frame controller regs taped parentTape tape parentSlot kind
      interval hinterval htapedKind htapedOne htapedGuess htapedTape
      htapedInterval hguess hnode
  have hrun :
      Runs
        (regenerateChild workTapeCount controller regs)
        store final := by
    simpa [regenerateChild, Cmd.seqList] using
      Runs.seq hdecodeRun
        (Runs.seq hcopyRun hdispatchRun)
  refine ⟨final, hrun, ?_, hdigit, ?_⟩
  · rw [hnodeCode, htapedBase]
  · intro address haddress
    exact Footprint.runs_eq_outside
      (regenerateChild_writesWithin_internal
        workTapeCount controller regs)
      hrun haddress

theorem movementFootprint_subset_layout_internal
    (regs : NeighborhoodTrial.Registers controller) :
    movementFootprint regs ⊆ regs.layout.footprint := by
  intro address haddress
  simp only [movementFootprint, Finset.mem_image,
    Finset.mem_univ, true_and] at haddress
  obtain ⟨slot, rfl⟩ := haddress
  exact Layout.index_mem_layout_footprint regs (movementMap slot)

theorem movementDigit_runs_internal
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store) (word index : ℕ)
    (hguess : store controller.guess = word)
    (hindex : store (movementIndex regs) = index) :
    ∃ final,
      Runs (movementDigit controller regs) store final ∧
      MovementDigitPost controller regs word index store final := by
  exact movementDigit_runs_core
    controller regs store word index hguess hindex

end Internal
end ChildNode
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
