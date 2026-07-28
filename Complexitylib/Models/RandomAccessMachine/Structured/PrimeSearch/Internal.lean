/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Mathlib.Tactic.FinCases
import Complexitylib.Models.RandomAccessMachine.Structured.Internal.Resources
import Complexitylib.Models.RandomAccessMachine.Structured.PrimeSearch.Defs
import Complexitylib.Models.RandomAccessMachine.Structured.RuntimeArithmetic

/-!
# Proof internals for fixed-register primality and prime search
-/

namespace Complexity

namespace RAM

namespace Structured

namespace PrimeSearch

namespace Internal

private theorem runs_basics (ops : List Basic) (store : Store) :
    Runs (Cmd.basics ops) store (Basic.execList ops store) := by
  obtain ⟨cost, space, hexec⟩ :=
    Structured.Internal.exec_basics_exists ops store
  exact ⟨ops.length, cost, space, hexec⟩

private def primalitySetupStore (regs : Registers) (store : Store) :
    Store :=
  Basic.execList (primalitySetupOps regs) store

private def trialSetupStore (regs : Registers) (store : Store) :
    Store :=
  Basic.execList (trialSetupOps regs) store

private structure TrialInv (regs : Registers) (candidate divisor : ℕ)
    (store : Store) : Prop where
  candidate_pos : 2 ≤ candidate
  divisor_lt : divisor < candidate
  checked : ∀ possible, divisor < possible → possible < candidate →
    2 ≤ possible → ¬possible ∣ candidate
  candidate_eq : store regs.candidate = candidate
  result_eq : store regs.result = 1
  divisor_eq : store regs.divisor = divisor
  divisorPred_eq : store regs.divisorPred = divisor - 1
  remainder_le : store regs.remainder ≤ candidate
  reduceTest_eq : store regs.reduceTest = 0
  one_eq : store regs.one = 1
  active_eq : store regs.active = divisor - 1

private structure SearchInv (regs : Registers) (candidate : ℕ)
    (store : Store) : Prop where
  candidate_eq : store regs.candidate = candidate
  result_eq : store regs.result = primalityValue candidate
  divisor_le : store regs.divisor ≤ candidate
  divisorPred_le : store regs.divisorPred ≤ candidate
  remainder_le : store regs.remainder ≤ candidate
  reduceTest_eq : store regs.reduceTest = 0
  one_eq : store regs.one = 1
  active_eq : store regs.active = 1 - primalityValue candidate

private theorem trialLoop_runs
    (regs : Registers) (candidate divisor : ℕ) (store : Store)
    (hinv : TrialInv regs candidate divisor store) :
    ∃ final,
      Runs (trialLoop regs) store final ∧
      PrimalityPost regs candidate final := by
  induction divisor using Nat.strong_induction_on generalizing store with
  | h divisor ih =>
      by_cases hsmall : divisor ≤ 1
      · have hactiveZero : store regs.active = 0 := by
          rw [hinv.active_eq]
          omega
        have hprime : candidate.Prime := by
          rw [Nat.prime_def_lt']
          refine ⟨hinv.candidate_pos, ?_⟩
          intro possible hpossible hpossibleLt
          exact hinv.checked possible (by omega) hpossibleLt hpossible
        refine ⟨store, ?_, ?_⟩
        · simpa [trialLoop] using Runs.whileZero hactiveZero
        · constructor
          · exact hinv.candidate_eq
          · simp [primalityValue, hprime, hinv.result_eq]
          · exact hinv.divisor_eq ▸ hinv.divisor_lt.le
          · rw [hinv.divisorPred_eq]
            exact (Nat.sub_le divisor 1).trans hinv.divisor_lt.le
          · exact hinv.remainder_le
          · exact hinv.reduceTest_eq
          · exact hinv.one_eq
          · exact hactiveZero
      · have hdivisorPos : 0 < divisor := by omega
        have hdivisorTwo : 2 ≤ divisor := by omega
        have hactiveNonzero : store regs.active ≠ 0 := by
          rw [hinv.active_eq]
          omega
        let copied :=
          (Basic.mul regs.remainder regs.candidate regs.result).exec store
        let reduced :=
          RuntimeArithmetic.reduceResultStore regs.reduceRegisters
            (candidate % divisor) copied
        have hcopiedCandidate :
            copied regs.candidate = candidate := by
          simp [copied, Basic.exec, hinv.candidate_eq]
        have hcopiedValue :
            copied regs.remainder = candidate := by
          simp [copied, Basic.exec, hinv.candidate_eq,
            hinv.result_eq]
        have hcopiedDivisor :
            copied regs.divisor = divisor := by
          simp [copied, Basic.exec, hinv.divisor_eq]
        have hcopiedDivisorPred :
            copied regs.divisorPred = divisor - 1 := by
          simp [copied, Basic.exec, hinv.divisorPred_eq]
        have hreduce :
            Runs (RuntimeArithmetic.reduce regs.reduceRegisters)
              copied reduced := by
          apply RuntimeArithmetic.reduce_runs
            regs.reduceRegisters copied divisor candidate hdivisorPos
          · simpa [Registers.reduceRegisters] using hcopiedValue
          · simpa [Registers.reduceRegisters] using hcopiedDivisor
          · simpa [Registers.reduceRegisters] using hcopiedDivisorPred
        have hreducedCandidate :
            reduced regs.candidate = candidate := by
          simp [reduced, RuntimeArithmetic.reduceResultStore,
            Registers.reduceRegisters, hcopiedCandidate]
        have hreducedDivisor :
            reduced regs.divisor = divisor := by
          simp [reduced, RuntimeArithmetic.reduceResultStore,
            Registers.reduceRegisters, hcopiedDivisor]
        have hreducedDivisorPred :
            reduced regs.divisorPred = divisor - 1 := by
          simp [reduced, RuntimeArithmetic.reduceResultStore,
            Registers.reduceRegisters, hcopiedDivisorPred]
        have hreducedRemainder :
            reduced regs.remainder = candidate % divisor := by
          simp [reduced, RuntimeArithmetic.reduceResultStore,
            Registers.reduceRegisters]
        have hreducedResult :
            reduced regs.result = 1 := by
          simp [reduced, RuntimeArithmetic.reduceResultStore,
            Registers.reduceRegisters, copied, Basic.exec,
            hinv.result_eq]
        have hreducedTest :
            reduced regs.reduceTest = 0 := by
          simp [reduced, RuntimeArithmetic.reduceResultStore,
            Registers.reduceRegisters]
        have hreducedOne :
            reduced regs.one = 1 := by
          simp [reduced, RuntimeArithmetic.reduceResultStore,
            Registers.reduceRegisters, copied, Basic.exec,
            hinv.one_eq]
        have hcopyRun :
            Runs
              (.basic
                (.mul regs.remainder regs.candidate regs.result))
              store copied :=
          Runs.basic _ _
        by_cases hmod : candidate % divisor = 0
        · let marked := (Basic.imm regs.result 0).exec reduced
          let next :=
            (Basic.mul regs.active regs.result regs.divisorPred).exec
              marked
          have hremainderZero : reduced regs.remainder = 0 := by
            rw [hreducedRemainder, hmod]
          have hbranch :
              Runs
                (.ifZero regs.remainder
                  (.basic (.imm regs.result 0))
                  (decrementDivisor regs))
                reduced marked :=
            Runs.ifZero hremainderZero (Runs.basic _ _)
          have hnextRun :
              Runs
                (.basic
                  (.mul regs.active regs.result regs.divisorPred))
                marked next :=
            Runs.basic _ _
          have hbody :
              Runs (trialBody regs) store next := by
            simpa [trialBody, copied, reduced, marked, next] using
              Runs.seq hcopyRun
                (Runs.seq hreduce (Runs.seq hbranch hnextRun))
          have hnextActive : next regs.active = 0 := by
            simp [next, marked, Basic.exec]
          have hnextLoop :
              Runs (trialLoop regs) next next := by
            simpa [trialLoop] using Runs.whileZero hnextActive
          have hrun :
              Runs (trialLoop regs) store next := by
            simpa [trialLoop] using
              Runs.whileNonzero hactiveNonzero hbody hnextLoop
          have hdivides : divisor ∣ candidate := by
            exact Nat.dvd_iff_mod_eq_zero.mpr hmod
          have hnotPrime : ¬candidate.Prime := by
            intro hprime
            have honeOrSelf :=
              hprime.eq_one_or_self_of_dvd divisor hdivides
            rcases honeOrSelf with hone | hself
            · have hne : divisor ≠ 1 := by omega
              exact hne hone
            · exact (ne_of_lt hinv.divisor_lt) hself
          refine ⟨next, hrun, ?_⟩
          constructor
          · simp [next, marked, Basic.exec, hreducedCandidate]
          · simp [next, marked, Basic.exec, primalityValue,
              hnotPrime]
          · simp [next, marked, Basic.exec, hreducedDivisor]
            exact hinv.divisor_lt.le
          · have hnextDivisorPred :
                next regs.divisorPred = divisor - 1 := by
              simp [next, marked, Basic.exec,
                hreducedDivisorPred]
            rw [hnextDivisorPred]
            exact (Nat.sub_le divisor 1).trans hinv.divisor_lt.le
          · simp [next, marked, Basic.exec, hreducedRemainder]
            exact (Nat.mod_lt candidate hdivisorPos).le.trans
              hinv.divisor_lt.le
          · simp [next, marked, Basic.exec, hreducedTest]
          · simp [next, marked, Basic.exec, hreducedOne]
          · exact hnextActive
        · let decremented :=
            (Basic.sub regs.divisor regs.divisor regs.one).exec
              reduced
          let predecessor :=
            (Basic.sub regs.divisorPred regs.divisorPred
              regs.one).exec decremented
          let next :=
            (Basic.mul regs.active regs.result regs.divisorPred).exec
              predecessor
          have hremainderNonzero :
              reduced regs.remainder ≠ 0 := by
            rwa [hreducedRemainder]
          have hdecrement :
              Runs (decrementDivisor regs) reduced predecessor := by
            simpa [decrementDivisor, decremented, predecessor] using
              Runs.seq
                (Runs.basic
                  (Basic.sub regs.divisor regs.divisor regs.one)
                  reduced)
                (Runs.basic
                  (Basic.sub regs.divisorPred regs.divisorPred
                    regs.one)
                  decremented)
          have hbranch :
              Runs
                (.ifZero regs.remainder
                  (.basic (.imm regs.result 0))
                  (decrementDivisor regs))
                reduced predecessor :=
            Runs.ifNonzero hremainderNonzero hdecrement
          have hnextRun :
              Runs
                (.basic
                  (.mul regs.active regs.result regs.divisorPred))
                predecessor next :=
            Runs.basic _ _
          have hbody :
              Runs (trialBody regs) store next := by
            simpa [trialBody, copied, reduced, next] using
              Runs.seq hcopyRun
                (Runs.seq hreduce (Runs.seq hbranch hnextRun))
          have hnextInv :
              TrialInv regs candidate (divisor - 1) next := by
            constructor
            · exact hinv.candidate_pos
            · exact (Nat.sub_le divisor 1).trans_lt
                hinv.divisor_lt
            · intro possible hpossible hpossibleLt hpossibleTwo
              by_cases heq : possible = divisor
              · subst possible
                exact fun hdivides =>
                  hmod (Nat.dvd_iff_mod_eq_zero.mp hdivides)
              · exact hinv.checked possible (by omega)
                  hpossibleLt hpossibleTwo
            · simp [next, predecessor, decremented, Basic.exec,
                hreducedCandidate]
            · simp [next, predecessor, decremented, Basic.exec,
                hreducedResult]
            · simp [next, predecessor, decremented, Basic.exec,
                hreducedDivisor,
                hreducedOne]
            · simp [next, predecessor, decremented, Basic.exec,
                hreducedDivisorPred,
                hreducedOne]
            · simp [next, predecessor, decremented, Basic.exec,
                hreducedRemainder]
              exact (Nat.mod_lt candidate hdivisorPos).le.trans
                hinv.divisor_lt.le
            · simp [next, predecessor, decremented, Basic.exec,
                hreducedTest]
            · simp [next, predecessor, decremented, Basic.exec,
                hreducedOne]
            · simp [next, predecessor, decremented, Basic.exec,
                hreducedDivisorPred, hreducedResult, hreducedOne]
          have hnextLess : divisor - 1 < divisor := by omega
          obtain ⟨final, hloop, hpost⟩ :=
            ih (divisor - 1) hnextLess next hnextInv
          exact ⟨final, by
            simpa [trialLoop] using
              Runs.whileNonzero hactiveNonzero hbody hloop,
            hpost⟩

theorem primality_runs_internal
    (regs : Registers) (store : Store) (candidate : ℕ)
    (hcandidate : store regs.candidate = candidate) :
    ∃ final,
      Runs (primality regs) store final ∧
      PrimalityPost regs candidate final := by
  let setupStore := primalitySetupStore regs store
  have hsetup :
      Runs (Cmd.basics (primalitySetupOps regs))
        store setupStore := by
    simpa [setupStore, primalitySetupStore] using
      runs_basics (primalitySetupOps regs) store
  have hsetupCandidate :
      setupStore regs.candidate = candidate := by
    simp [setupStore, primalitySetupStore, primalitySetupOps,
      Basic.execList, Basic.exec, hcandidate]
  have hsetupResult :
      setupStore regs.result = 0 := by
    simp [setupStore, primalitySetupStore, primalitySetupOps,
      Basic.execList, Basic.exec]
  have hsetupDivisor :
      setupStore regs.divisor = 0 := by
    simp [setupStore, primalitySetupStore, primalitySetupOps,
      Basic.execList, Basic.exec]
  have hsetupDivisorPred :
      setupStore regs.divisorPred = 0 := by
    simp [setupStore, primalitySetupStore, primalitySetupOps,
      Basic.execList, Basic.exec]
  have hsetupRemainder :
      setupStore regs.remainder = 0 := by
    simp [setupStore, primalitySetupStore, primalitySetupOps,
      Basic.execList, Basic.exec]
  have hsetupReduceTest :
      setupStore regs.reduceTest = 0 := by
    simp [setupStore, primalitySetupStore, primalitySetupOps,
      Basic.execList, Basic.exec]
  have hsetupOne :
      setupStore regs.one = 1 := by
    simp [setupStore, primalitySetupStore, primalitySetupOps,
      Basic.execList, Basic.exec]
  have hsetupActive :
      setupStore regs.active = candidate - 1 := by
    simp [setupStore, primalitySetupStore, primalitySetupOps,
      Basic.execList, Basic.exec, hcandidate]
  by_cases hsmall : candidate ≤ 1
  · have hactiveZero : setupStore regs.active = 0 := by
      rw [hsetupActive]
      omega
    have hnotPrime : ¬candidate.Prime := by
      intro hprime
      have htwo := hprime.two_le
      omega
    have hbranch :
        Runs
          (.ifZero regs.active .skip
            (Cmd.seq (Cmd.basics (trialSetupOps regs))
              (trialLoop regs)))
          setupStore setupStore :=
      Runs.ifZero hactiveZero (Runs.skip setupStore)
    refine ⟨setupStore, ?_, ?_⟩
    · simpa [primality] using Runs.seq hsetup hbranch
    · constructor
      · exact hsetupCandidate
      · simp [primalityValue, hnotPrime, hsetupResult]
      · rw [hsetupDivisor]
        exact Nat.zero_le candidate
      · rw [hsetupDivisorPred]
        exact Nat.zero_le candidate
      · rw [hsetupRemainder]
        exact Nat.zero_le candidate
      · exact hsetupReduceTest
      · exact hsetupOne
      · exact hactiveZero
  · have hcandidatePos : 2 ≤ candidate := by omega
    have hactiveNonzero : setupStore regs.active ≠ 0 := by
      rw [hsetupActive]
      omega
    let trialStore := trialSetupStore regs setupStore
    have htrialSetup :
        Runs (Cmd.basics (trialSetupOps regs))
          setupStore trialStore := by
      simpa [trialStore, trialSetupStore] using
        runs_basics (trialSetupOps regs) setupStore
    have htrialInv :
        TrialInv regs candidate (candidate - 1) trialStore := by
      constructor
      · exact hcandidatePos
      · omega
      · intro possible hpossible hpossibleLt _
        omega
      · simp [trialStore, trialSetupStore, trialSetupOps,
          Basic.execList, Basic.exec, hsetupCandidate]
      · simp [trialStore, trialSetupStore, trialSetupOps,
          Basic.execList, Basic.exec]
      · simp [trialStore, trialSetupStore, trialSetupOps,
          Basic.execList, Basic.exec, hsetupCandidate, hsetupOne]
      · simp [trialStore, trialSetupStore, trialSetupOps,
          Basic.execList, Basic.exec, hsetupCandidate, hsetupOne]
      · simp [trialStore, trialSetupStore, trialSetupOps,
          Basic.execList, Basic.exec, hsetupRemainder]
      · simp [trialStore, trialSetupStore, trialSetupOps,
          Basic.execList, Basic.exec, hsetupReduceTest]
      · simp [trialStore, trialSetupStore, trialSetupOps,
          Basic.execList, Basic.exec, hsetupOne]
      · simp [trialStore, trialSetupStore, trialSetupOps,
          Basic.execList, Basic.exec, hsetupCandidate, hsetupOne]
    obtain ⟨final, hloop, hpost⟩ :=
      trialLoop_runs regs candidate (candidate - 1)
        trialStore htrialInv
    have hnonzeroBranch :
        Runs
          (Cmd.seq (Cmd.basics (trialSetupOps regs))
            (trialLoop regs))
          setupStore final :=
      Runs.seq htrialSetup hloop
    have hbranch :
        Runs
          (.ifZero regs.active .skip
            (Cmd.seq (Cmd.basics (trialSetupOps regs))
              (trialLoop regs)))
          setupStore final :=
      Runs.ifNonzero hactiveNonzero hnonzeroBranch
    exact ⟨final, by
      simpa [primality] using Runs.seq hsetup hbranch,
      hpost⟩

private theorem searchLoop_runs
    (regs : Registers) (lower selectedPrime candidate : ℕ)
    (store : Store)
    (hselectedPrime : selectedPrime.Prime)
    (hcandidateLower : lower ≤ candidate)
    (hcandidateUpper : candidate ≤ selectedPrime)
    (hprior : ∀ prior, lower ≤ prior → prior < candidate →
      ¬prior.Prime)
    (hinv : SearchInv regs candidate store) :
    ∃ final,
      Runs (.whileNonzero regs.active (searchBody regs)) store final ∧
      SearchPost regs lower final := by
  generalize hgapEq : selectedPrime - candidate = gap
  induction gap using Nat.strong_induction_on generalizing candidate store with
  | h gap ih =>
      by_cases hprime : candidate.Prime
      · have hactiveZero : store regs.active = 0 := by
          rw [hinv.active_eq]
          simp [primalityValue, hprime]
        have hbounded : regs.Bounded candidate store := by
          intro slot
          fin_cases slot
          · change store regs.candidate ≤ candidate
            rw [hinv.candidate_eq]
          · change store regs.result ≤ candidate
            rw [hinv.result_eq]
            simp [primalityValue, hprime]
            have htwo := hprime.two_le
            omega
          · exact hinv.divisor_le
          · exact hinv.divisorPred_le
          · exact hinv.remainder_le
          · change store regs.reduceTest ≤ candidate
            rw [hinv.reduceTest_eq]
            exact Nat.zero_le candidate
          · change store regs.one ≤ candidate
            rw [hinv.one_eq]
            have htwo := hprime.two_le
            omega
          · change store regs.active ≤ candidate
            rw [hactiveZero]
            exact Nat.zero_le candidate
        refine ⟨store, Runs.whileZero hactiveZero, ?_⟩
        constructor
        · simpa [IsFirstPrimeAtOrAbove, hinv.candidate_eq] using
            And.intro hcandidateLower (And.intro hprime hprior)
        · simp [hinv.result_eq, primalityValue, hprime]
        · simpa [hinv.candidate_eq] using hbounded
        · exact hinv.one_eq
        · exact hactiveZero
      · have hcandidateNe : candidate ≠ selectedPrime := by
          intro heq
          exact hprime (heq ▸ hselectedPrime)
        have hcandidateLt : candidate < selectedPrime :=
          lt_of_le_of_ne hcandidateUpper hcandidateNe
        have hactiveNonzero : store regs.active ≠ 0 := by
          rw [hinv.active_eq]
          simp [primalityValue, hprime]
        let incremented :=
          (Basic.add regs.candidate regs.candidate regs.one).exec
            store
        have hincrementedCandidate :
            incremented regs.candidate = candidate + 1 := by
          simp [incremented, Basic.exec, hinv.candidate_eq,
            hinv.one_eq]
        have hincrement :
            Runs
              (.basic
                (.add regs.candidate regs.candidate regs.one))
              store incremented :=
          Runs.basic _ _
        obtain ⟨tested, htest, hpost⟩ :=
          primality_runs_internal regs incremented (candidate + 1)
            hincrementedCandidate
        let refreshed :=
          (Basic.sub regs.active regs.one regs.result).exec tested
        have hrefresh :
            Runs (refreshSearchTest regs) tested refreshed := by
          simpa [refreshSearchTest, refreshed] using
            Runs.basic
              (Basic.sub regs.active regs.one regs.result)
              tested
        have hbody :
            Runs (searchBody regs) store refreshed := by
          simpa [searchBody, incremented] using
            Runs.seq hincrement (Runs.seq htest hrefresh)
        have hnextInv :
            SearchInv regs (candidate + 1) refreshed := by
          constructor
          · simp [refreshed, Basic.exec, hpost.candidate_eq]
          · simp [refreshed, Basic.exec, hpost.result_eq]
          · simpa [refreshed, Basic.exec] using hpost.divisor_le
          · simpa [refreshed, Basic.exec] using
              hpost.divisorPred_le
          · simpa [refreshed, Basic.exec] using hpost.remainder_le
          · simp [refreshed, Basic.exec, hpost.reduceTest_eq]
          · simp [refreshed, Basic.exec, hpost.one_eq]
          · simp [refreshed, Basic.exec, hpost.one_eq,
              hpost.result_eq]
        have hnextLower : lower ≤ candidate + 1 := by omega
        have hnextUpper : candidate + 1 ≤ selectedPrime := by
          omega
        have hnextPrior :
            ∀ prior, lower ≤ prior → prior < candidate + 1 →
              ¬prior.Prime := by
          intro prior hlower hpriorLt
          by_cases heq : prior = candidate
          · subst prior
            exact hprime
          · exact hprior prior hlower (by omega)
        have hnextGap :
            selectedPrime - (candidate + 1) < gap := by
          omega
        obtain ⟨final, hloop, hfinal⟩ :=
          ih (selectedPrime - (candidate + 1)) hnextGap
            (candidate + 1) refreshed hnextLower hnextUpper
            hnextPrior hnextInv rfl
        exact ⟨final,
          Runs.whileNonzero hactiveNonzero hbody hloop,
          hfinal⟩

theorem search_runs_internal
    (regs : Registers) (store : Store) (lower : ℕ)
    (hlower : store regs.candidate = lower) :
    ∃ final,
      Runs (search regs) store final ∧
      SearchPost regs lower final := by
  obtain ⟨selectedPrime, hselected, hselectedPrime⟩ :=
    Nat.exists_infinite_primes lower
  obtain ⟨tested, htest, hpost⟩ :=
    primality_runs_internal regs store lower hlower
  let refreshed :=
    (Basic.sub regs.active regs.one regs.result).exec tested
  have hrefresh :
      Runs (refreshSearchTest regs) tested refreshed := by
    simpa [refreshSearchTest, refreshed] using
      Runs.basic
        (Basic.sub regs.active regs.one regs.result)
        tested
  have hinv : SearchInv regs lower refreshed := by
    constructor
    · simp [refreshed, Basic.exec, hpost.candidate_eq]
    · simp [refreshed, Basic.exec, hpost.result_eq]
    · simpa [refreshed, Basic.exec] using hpost.divisor_le
    · simpa [refreshed, Basic.exec] using hpost.divisorPred_le
    · simpa [refreshed, Basic.exec] using hpost.remainder_le
    · simp [refreshed, Basic.exec, hpost.reduceTest_eq]
    · simp [refreshed, Basic.exec, hpost.one_eq]
    · simp [refreshed, Basic.exec, hpost.one_eq,
        hpost.result_eq]
  obtain ⟨final, hloop, hfinal⟩ :=
    searchLoop_runs regs lower selectedPrime lower refreshed
      hselectedPrime (le_refl lower) hselected
      (by intro prior hlower hprior; omega) hinv
  exact ⟨final, by
    simpa [search] using
      Runs.seq htest (Runs.seq hrefresh hloop),
    hfinal⟩

theorem bounded_dataBits_internal
    (regs : Registers) (bound : ℕ) (store : Store)
    (hbounded : regs.Bounded bound store) :
    regs.dataBits store ≤ registerBitBudget bound := by
  unfold Registers.dataBits registerBitBudget
  calc
    ∑ slot : Fin 8, bitlen (store (regs.index slot)) ≤
        ∑ _slot : Fin 8, bitlen bound := by
      apply Finset.sum_le_sum
      intro slot _
      simpa [bitlen] using Nat.size_le_size (hbounded slot)
    _ = 8 * bitlen bound := by simp

theorem primalityPost_bounded_internal
    (regs : Registers) (candidate : ℕ) (store : Store)
    (hcandidate : 2 ≤ candidate)
    (hpost : PrimalityPost regs candidate store) :
    regs.Bounded candidate store := by
  intro slot
  fin_cases slot
  · change store regs.candidate ≤ candidate
    rw [hpost.candidate_eq]
  · change store regs.result ≤ candidate
    rw [hpost.result_eq]
    simp only [primalityValue]
    split <;> omega
  · exact hpost.divisor_le
  · exact hpost.divisorPred_le
  · exact hpost.remainder_le
  · change store regs.reduceTest ≤ candidate
    rw [hpost.reduceTest_eq]
    omega
  · change store regs.one ≤ candidate
    rw [hpost.one_eq]
    omega
  · change store regs.active ≤ candidate
    rw [hpost.active_eq]
    omega

end Internal

end PrimeSearch

end Structured

end RAM

end Complexity
