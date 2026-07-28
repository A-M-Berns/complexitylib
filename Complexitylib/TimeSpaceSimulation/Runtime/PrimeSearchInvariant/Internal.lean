/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Mathlib.Tactic.FinCases
import Complexitylib.Models.RandomAccessMachine.Structured.Invariant
import
  Complexitylib.TimeSpaceSimulation.Runtime.PrimeSearchInvariant.Defs

/-!
# All-prefix invariants for fixed-register prime search -- proof internals
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace Runtime

namespace PrimeSearchInvariant

open RAM Structured

namespace Internal

private abbrev Within
    (allowed : Finset ℕ) (valueBits : ℕ) : Store → Prop :=
  SearchProgram.MutableValuesWithin allowed valueBits

private theorem bitlen_le_of_le
    {value bound valueBits : ℕ}
    (hvalue : value ≤ bound)
    (hbound : bitlen bound ≤ valueBits) :
    bitlen value ≤ valueBits := by
  have hmono : bitlen value ≤ bitlen bound := by
    simpa [bitlen] using Nat.size_le_size hvalue
  exact hmono.trans hbound

private theorem within_update
    {allowed : Finset ℕ} {valueBits index value : ℕ}
    {store : Store}
    (hindex : index ∈ allowed)
    (hstore : Within allowed valueBits store)
    (hvalue : bitlen value ≤ valueBits) :
    Within allowed valueBits (Function.update store index value) := by
  have hold : bitlen (store index) ≤ valueBits :=
    hstore index hindex
  intro address haddress
  by_cases heq : address = index
  · subst address
    rw [Function.update_self]
    exact (le_max_left _ _).trans (max_le hvalue hold)
  · simpa [Function.update_of_ne heq] using
      hstore address haddress

private theorem within_imm
    {allowed : Finset ℕ} {valueBits destination value : ℕ}
    {store : Store}
    (hdestination : destination ∈ allowed)
    (hstore : Within allowed valueBits store)
    (hvalue : bitlen value ≤ valueBits) :
    Within allowed valueBits
      ((Basic.imm destination value).exec store) := by
  simpa [Basic.exec] using
    within_update hdestination hstore hvalue

private theorem within_add
    {allowed : Finset ℕ} {valueBits destination left right : ℕ}
    {store : Store}
    (hdestination : destination ∈ allowed)
    (hstore : Within allowed valueBits store)
    (hvalue : bitlen (store left + store right) ≤ valueBits) :
    Within allowed valueBits
      ((Basic.add destination left right).exec store) := by
  simpa [Basic.exec] using
    within_update hdestination hstore hvalue

private theorem within_sub
    {allowed : Finset ℕ} {valueBits destination left right : ℕ}
    {store : Store}
    (hdestination : destination ∈ allowed)
    (hstore : Within allowed valueBits store)
    (hvalue : bitlen (store left - store right) ≤ valueBits) :
    Within allowed valueBits
      ((Basic.sub destination left right).exec store) := by
  simpa [Basic.exec] using
    within_update hdestination hstore hvalue

private theorem within_mul
    {allowed : Finset ℕ} {valueBits destination left right : ℕ}
    {store : Store}
    (hdestination : destination ∈ allowed)
    (hstore : Within allowed valueBits store)
    (hvalue : bitlen (store left * store right) ≤ valueBits) :
    Within allowed valueBits
      ((Basic.mul destination left right).exec store) := by
  simpa [Basic.exec] using
    within_update hdestination hstore hvalue

private def ExecListInvariant
    (invariant : Store → Prop) : List Basic → Store → Prop
  | [], store => invariant store
  | op :: rest, store =>
      invariant store ∧
        ExecListInvariant invariant rest (op.exec store)

private theorem execListInvariant_initial
    {invariant : Store → Prop} {ops : List Basic} {store : Store}
    (hinvariant : ExecListInvariant invariant ops store) :
    invariant store := by
  cases ops with
  | nil => exact hinvariant
  | cons op rest => exact hinvariant.1

private theorem invariantRuns_basics
    {invariant : Store → Prop}
    (ops : List Basic) (store : Store)
    (hinvariant : ExecListInvariant invariant ops store) :
    ∃ steps,
      InvariantRuns invariant (Cmd.basics ops) store
        (Basic.execList ops store) steps := by
  induction ops generalizing store with
  | nil =>
      exact ⟨0, InvariantRuns.skip store hinvariant⟩
  | cons op rest ih =>
      cases rest with
      | nil =>
          exact ⟨1,
            InvariantRuns.basic op store
              hinvariant.1 hinvariant.2⟩
      | cons next tail =>
          obtain ⟨steps, hrest⟩ :=
            ih (Basic.exec op store) hinvariant.2
          exact ⟨1 + steps,
            InvariantRuns.seq
              (InvariantRuns.basic op store hinvariant.1
                (execListInvariant_initial hinvariant.2))
              hrest⟩

private theorem exec_final_unique
    {cmd : Cmd} {initial firstFinal secondFinal : Store}
    {firstSteps firstCost firstSpace
      secondSteps secondCost secondSpace : ℕ}
    (hfirst :
      Exec cmd initial firstFinal firstSteps firstCost firstSpace)
    (hsecond :
      Exec cmd initial secondFinal secondSteps secondCost secondSpace) :
    firstFinal = secondFinal := by
  induction hfirst generalizing secondFinal secondSteps secondCost
      secondSpace with
  | skip store =>
      cases hsecond
      rfl
  | basic op store =>
      cases hsecond
      rfl
  | seq hfirst hrest ihFirst ihRest =>
      cases hsecond with
      | seq hsecond hsecondRest =>
          have hmiddle := ihFirst hsecond
          subst hmiddle
          exact ihRest hsecondRest
  | ifZero htest hbranch ih =>
      cases hsecond with
      | ifZero _ hsecondBranch =>
          exact ih hsecondBranch
      | ifNonzero htest' _ =>
          exact False.elim (htest' htest)
  | ifNonzero htest hbranch ih =>
      cases hsecond with
      | ifZero htest' _ =>
          exact False.elim (htest htest')
      | ifNonzero _ hsecondBranch =>
          exact ih hsecondBranch
  | whileZero htest =>
      cases hsecond with
      | whileZero _ => rfl
      | whileNonzero htest' _ _ =>
          exact False.elim (htest' htest)
  | whileNonzero htest hbody hloop ihBody ihLoop =>
      cases hsecond with
      | whileZero htest' =>
          exact False.elim (htest htest')
      | whileNonzero _ hsecondBody hsecondLoop =>
          have hmiddle := ihBody hsecondBody
          subst hmiddle
          exact ihLoop hsecondLoop

private theorem runs_final_unique
    {cmd : Cmd} {initial firstFinal secondFinal : Store}
    (hfirst : Runs cmd initial firstFinal)
    (hsecond : Runs cmd initial secondFinal) :
    firstFinal = secondFinal := by
  obtain ⟨firstSteps, firstCost, firstSpace, hfirst⟩ := hfirst
  obtain ⟨secondSteps, secondCost, secondSpace, hsecond⟩ := hsecond
  exact exec_final_unique hfirst hsecond

private theorem reduceLoop_invariantRuns
    (regs : RuntimeArithmetic.ReduceRegisters)
    (allowed : Finset ℕ) (valueBits bound : ℕ)
    (hvalueMem : regs.value ∈ allowed)
    (htestMem : regs.test ∈ allowed)
    (hbound : bitlen bound ≤ valueBits)
    (store : Store) (modulus remainder quotient : ℕ)
    (hmodulus : 0 < modulus)
    (hremainder : remainder < modulus)
    (hvalue :
      store regs.value = quotient * modulus + remainder)
    (hmodulusValue : store regs.modulus = modulus)
    (hmodulusPred :
      store regs.modulusPred = modulus - 1)
    (htest :
      store regs.test =
        quotient * modulus + remainder - (modulus - 1))
    (htotal : quotient * modulus + remainder ≤ bound)
    (hstore : Within allowed valueBits store) :
    ∃ steps,
      InvariantRuns (Within allowed valueBits)
        (.whileNonzero regs.test
          (RuntimeArithmetic.reduceBody regs))
        store
        (RuntimeArithmetic.reduceResultStore regs remainder store)
        steps := by
  induction quotient generalizing store with
  | zero =>
      have htestZero : store regs.test = 0 := by
        rw [htest]
        omega
      have hresult :
          RuntimeArithmetic.reduceResultStore regs remainder store =
            store := by
        funext index
        by_cases hvalueIndex : index = regs.value
        · subst index
          simp [RuntimeArithmetic.reduceResultStore,
            regs.value_ne_test, hvalue]
        · by_cases htestIndex : index = regs.test
          · subst index
            simp [RuntimeArithmetic.reduceResultStore, htestZero]
          · simp [RuntimeArithmetic.reduceResultStore,
              Function.update_of_ne, hvalueIndex, htestIndex]
      rw [hresult]
      exact ⟨1, InvariantRuns.whileZero htestZero hstore⟩
  | succ quotient ih =>
      have htestNonzero : store regs.test ≠ 0 := by
        rw [htest]
        simp only [Nat.succ_mul]
        omega
      let valueStore :=
        (Basic.sub regs.value regs.value regs.modulus).exec store
      let nextStore :=
        (RuntimeArithmetic.reduceTestOp regs).exec valueStore
      have hvalueStoreValue :
          valueStore regs.value =
            quotient * modulus + remainder := by
        simp only [valueStore, Basic.exec, Function.update_self]
        rw [hvalue, hmodulusValue]
        simp only [Nat.succ_mul]
        omega
      have hvalueStoreBound :
          quotient * modulus + remainder ≤ bound := by
        simp only [Nat.succ_mul] at htotal
        omega
      have hvalueStoreInvariant :
          Within allowed valueBits valueStore := by
        apply within_sub hvalueMem hstore
        apply bitlen_le_of_le _ hbound
        rw [hvalue, hmodulusValue]
        exact (Nat.sub_le _ _).trans htotal
      have hvalueStoreModulusPred :
          valueStore regs.modulusPred = modulus - 1 := by
        simp [valueStore, Basic.exec,
          regs.value_ne_modulusPred.symm, hmodulusPred]
      have hnextInvariant :
          Within allowed valueBits nextStore := by
        apply within_sub htestMem hvalueStoreInvariant
        apply bitlen_le_of_le _ hbound
        rw [hvalueStoreValue, hvalueStoreModulusPred]
        exact (Nat.sub_le _ _).trans hvalueStoreBound
      have hbody :
          InvariantRuns (Within allowed valueBits)
            (RuntimeArithmetic.reduceBody regs)
            store nextStore 2 := by
        exact InvariantRuns.seq
          (InvariantRuns.basic
            (Basic.sub regs.value regs.value regs.modulus)
            store hstore hvalueStoreInvariant)
          (InvariantRuns.basic
            (RuntimeArithmetic.reduceTestOp regs)
            valueStore hvalueStoreInvariant hnextInvariant)
      have hnextValue :
          nextStore regs.value =
            quotient * modulus + remainder := by
        simp [nextStore, RuntimeArithmetic.reduceTestOp,
          Basic.exec, regs.value_ne_test, hvalueStoreValue]
      have hnextModulus :
          nextStore regs.modulus = modulus := by
        simp [nextStore, RuntimeArithmetic.reduceTestOp,
          valueStore, Basic.exec, regs.modulus_ne_test,
          regs.value_ne_modulus.symm, hmodulusValue]
      have hnextModulusPred :
          nextStore regs.modulusPred = modulus - 1 := by
        simp [nextStore, RuntimeArithmetic.reduceTestOp,
          valueStore, Basic.exec, regs.modulusPred_ne_test,
          regs.value_ne_modulusPred.symm, hmodulusPred]
      have hnextTest :
          nextStore regs.test =
            quotient * modulus + remainder - (modulus - 1) := by
        simp only [nextStore, RuntimeArithmetic.reduceTestOp,
          Basic.exec, Function.update_self]
        rw [hvalueStoreValue, hvalueStoreModulusPred]
      obtain ⟨loopSteps, hloop⟩ :=
        ih nextStore hnextValue hnextModulus hnextModulusPred
          hnextTest hvalueStoreBound hnextInvariant
      have hresult :
          RuntimeArithmetic.reduceResultStore regs remainder nextStore =
            RuntimeArithmetic.reduceResultStore regs remainder store := by
        funext index
        by_cases hvalueIndex : index = regs.value
        · subst index
          simp [RuntimeArithmetic.reduceResultStore,
            regs.value_ne_test]
        · by_cases htestIndex : index = regs.test
          · subst index
            simp [RuntimeArithmetic.reduceResultStore]
          · simp [RuntimeArithmetic.reduceResultStore, nextStore,
              RuntimeArithmetic.reduceTestOp, valueStore, Basic.exec,
              Function.update_of_ne, hvalueIndex, htestIndex]
      rw [hresult] at hloop
      exact ⟨2 + loopSteps + 2,
        InvariantRuns.whileNonzero htestNonzero hbody hloop⟩

private theorem reduce_invariantRuns
    (regs : RuntimeArithmetic.ReduceRegisters)
    (allowed : Finset ℕ) (valueBits bound : ℕ)
    (hvalueMem : regs.value ∈ allowed)
    (htestMem : regs.test ∈ allowed)
    (hbound : bitlen bound ≤ valueBits)
    (store : Store) (modulus value : ℕ)
    (hmodulus : 0 < modulus)
    (hvalue : store regs.value = value)
    (hmodulusValue : store regs.modulus = modulus)
    (hmodulusPred :
      store regs.modulusPred = modulus - 1)
    (hvalueBound : value ≤ bound)
    (hstore : Within allowed valueBits store) :
    ∃ steps,
      InvariantRuns (Within allowed valueBits)
        (RuntimeArithmetic.reduce regs) store
        (RuntimeArithmetic.reduceResultStore regs
          (value % modulus) store)
        steps := by
  let testedStore :=
    (RuntimeArithmetic.reduceTestOp regs).exec store
  have htestedInvariant :
      Within allowed valueBits testedStore := by
    apply within_sub htestMem hstore
    apply bitlen_le_of_le _ hbound
    rw [hvalue, hmodulusPred]
    exact (Nat.sub_le _ _).trans hvalueBound
  have htestedValue : testedStore regs.value = value := by
    simp [testedStore, RuntimeArithmetic.reduceTestOp, Basic.exec,
      regs.value_ne_test, hvalue]
  have htestedModulus :
      testedStore regs.modulus = modulus := by
    simp [testedStore, RuntimeArithmetic.reduceTestOp, Basic.exec,
      regs.modulus_ne_test, hmodulusValue]
  have htestedModulusPred :
      testedStore regs.modulusPred = modulus - 1 := by
    simp [testedStore, RuntimeArithmetic.reduceTestOp, Basic.exec,
      regs.modulusPred_ne_test, hmodulusPred]
  have hdecompose :
      value / modulus * modulus + value % modulus = value := by
    simpa [Nat.mul_comm, Nat.add_comm] using
      (Nat.mod_add_div value modulus)
  have htestedQuotient :
      testedStore regs.value =
        value / modulus * modulus + value % modulus := by
    rw [htestedValue, hdecompose]
  have htestedTest :
      testedStore regs.test =
        value / modulus * modulus + value % modulus -
          (modulus - 1) := by
    simp only [testedStore, RuntimeArithmetic.reduceTestOp,
      Basic.exec, Function.update_self]
    rw [hvalue, hmodulusPred, hdecompose]
  have htestedBound :
      value / modulus * modulus + value % modulus ≤ bound := by
    rw [hdecompose]
    exact hvalueBound
  obtain ⟨loopSteps, hloop⟩ :=
    reduceLoop_invariantRuns regs allowed valueBits bound
      hvalueMem htestMem hbound testedStore modulus
      (value % modulus) (value / modulus) hmodulus
      (Nat.mod_lt value hmodulus) htestedQuotient htestedModulus
      htestedModulusPred htestedTest htestedBound htestedInvariant
  have hresult :
      RuntimeArithmetic.reduceResultStore regs
          (value % modulus) testedStore =
        RuntimeArithmetic.reduceResultStore regs
          (value % modulus) store := by
    funext index
    by_cases hvalueIndex : index = regs.value
    · subst index
      simp [RuntimeArithmetic.reduceResultStore,
        regs.value_ne_test]
    · by_cases htestIndex : index = regs.test
      · subst index
        simp [RuntimeArithmetic.reduceResultStore]
      · simp [RuntimeArithmetic.reduceResultStore, testedStore,
          RuntimeArithmetic.reduceTestOp, Basic.exec,
          Function.update_of_ne, hvalueIndex, htestIndex]
  rw [hresult] at hloop
  exact ⟨1 + loopSteps, by
    simpa [RuntimeArithmetic.reduce, testedStore] using
      InvariantRuns.seq
        (InvariantRuns.basic
          (RuntimeArithmetic.reduceTestOp regs)
          store hstore htestedInvariant)
        hloop⟩

private def primalitySetupStore
    (regs : PrimeSearch.Registers) (store : Store) : Store :=
  Basic.execList (PrimeSearch.primalitySetupOps regs) store

private def trialSetupStore
    (regs : PrimeSearch.Registers) (store : Store) : Store :=
  Basic.execList (PrimeSearch.trialSetupOps regs) store

private structure TrialShape
    (regs : PrimeSearch.Registers) (candidate divisor : ℕ)
    (store : Store) : Prop where
  candidate_pos : 2 ≤ candidate
  divisor_lt : divisor < candidate
  candidate_eq : store regs.candidate = candidate
  result_eq : store regs.result = 1
  divisor_eq : store regs.divisor = divisor
  divisorPred_eq : store regs.divisorPred = divisor - 1
  one_eq : store regs.one = 1
  active_eq : store regs.active = divisor - 1

private theorem primalitySetup_invariantRuns
    (regs : PrimeSearch.Registers)
    (allowed : Finset ℕ) (valueBits bound candidate : ℕ)
    (hfootprint : footprint regs ⊆ allowed)
    (hbound : bitlen bound ≤ valueBits)
    (hboundPos : 0 < bound)
    (hcandidateBound : candidate ≤ bound)
    (store : Store)
    (hcandidate : store regs.candidate = candidate)
    (hstore : Within allowed valueBits store) :
    ∃ steps,
      InvariantRuns (Within allowed valueBits)
        (Cmd.basics (PrimeSearch.primalitySetupOps regs))
        store (primalitySetupStore regs store) steps := by
  have honeBound : 1 ≤ bound := by omega
  have hzeroBits : bitlen 0 ≤ valueBits :=
    bitlen_le_of_le (Nat.zero_le bound) hbound
  have honeBits : bitlen 1 ≤ valueBits :=
    bitlen_le_of_le honeBound hbound
  have hactiveBits : bitlen (candidate - 1) ≤ valueBits :=
    bitlen_le_of_le
      ((Nat.sub_le candidate 1).trans hcandidateBound) hbound
  let oneStore := (Basic.imm regs.one 1).exec store
  let resultStore := (Basic.imm regs.result 0).exec oneStore
  let divisorStore := (Basic.imm regs.divisor 0).exec resultStore
  let divisorPredStore :=
    (Basic.imm regs.divisorPred 0).exec divisorStore
  let remainderStore :=
    (Basic.imm regs.remainder 0).exec divisorPredStore
  let reduceTestStore :=
    (Basic.imm regs.reduceTest 0).exec remainderStore
  let activeStore :=
    (Basic.sub regs.active regs.candidate regs.one).exec
      reduceTestStore
  have honeStore : Within allowed valueBits oneStore :=
    within_imm
      (hfootprint (index_mem_footprint regs 6)) hstore honeBits
  have hresultStore : Within allowed valueBits resultStore :=
    within_imm
      (hfootprint (index_mem_footprint regs 1))
      honeStore hzeroBits
  have hdivisorStore : Within allowed valueBits divisorStore :=
    within_imm
      (hfootprint (index_mem_footprint regs 2))
      hresultStore hzeroBits
  have hdivisorPredStore :
      Within allowed valueBits divisorPredStore :=
    within_imm
      (hfootprint (index_mem_footprint regs 3))
      hdivisorStore hzeroBits
  have hremainderStore : Within allowed valueBits remainderStore :=
    within_imm
      (hfootprint (index_mem_footprint regs 4))
      hdivisorPredStore hzeroBits
  have hreduceTestStore :
      Within allowed valueBits reduceTestStore :=
    within_imm
      (hfootprint (index_mem_footprint regs 5))
      hremainderStore hzeroBits
  have hactiveValue :
      reduceTestStore regs.candidate -
          reduceTestStore regs.one =
        candidate - 1 := by
    simp [reduceTestStore, remainderStore, divisorPredStore,
      divisorStore, resultStore, oneStore, Basic.exec, hcandidate]
  have hactiveStore : Within allowed valueBits activeStore := by
    apply within_sub
      (hfootprint (index_mem_footprint regs 7))
      hreduceTestStore
    rwa [hactiveValue]
  apply invariantRuns_basics
  change
    Within allowed valueBits store ∧
      Within allowed valueBits oneStore ∧
      Within allowed valueBits resultStore ∧
      Within allowed valueBits divisorStore ∧
      Within allowed valueBits divisorPredStore ∧
      Within allowed valueBits remainderStore ∧
      Within allowed valueBits reduceTestStore ∧
      Within allowed valueBits activeStore
  exact ⟨hstore, honeStore, hresultStore, hdivisorStore,
    hdivisorPredStore, hremainderStore, hreduceTestStore,
    hactiveStore⟩

private theorem trialSetup_invariantRuns
    (regs : PrimeSearch.Registers)
    (allowed : Finset ℕ) (valueBits bound candidate : ℕ)
    (hfootprint : footprint regs ⊆ allowed)
    (hbound : bitlen bound ≤ valueBits)
    (hcandidatePos : 2 ≤ candidate)
    (hcandidateBound : candidate ≤ bound)
    (store : Store)
    (hcandidate : store regs.candidate = candidate)
    (hone : store regs.one = 1)
    (hstore : Within allowed valueBits store) :
    ∃ steps,
      InvariantRuns (Within allowed valueBits)
        (Cmd.basics (PrimeSearch.trialSetupOps regs))
        store (trialSetupStore regs store) steps := by
  have honeBits : bitlen 1 ≤ valueBits :=
    bitlen_le_of_le (show 1 ≤ bound by omega) hbound
  have hdivisorBits : bitlen (candidate - 1) ≤ valueBits :=
    bitlen_le_of_le
      ((Nat.sub_le candidate 1).trans hcandidateBound) hbound
  have hpredBits : bitlen (candidate - 1 - 1) ≤ valueBits :=
    bitlen_le_of_le
      ((Nat.sub_le (candidate - 1) 1).trans
        ((Nat.sub_le candidate 1).trans hcandidateBound)) hbound
  let resultStore := (Basic.imm regs.result 1).exec store
  let divisorStore :=
    (Basic.sub regs.divisor regs.candidate regs.one).exec
      resultStore
  let divisorPredStore :=
    (Basic.sub regs.divisorPred regs.divisor regs.one).exec
      divisorStore
  let activeStore :=
    (Basic.mul regs.active regs.result regs.divisorPred).exec
      divisorPredStore
  have hresultStore : Within allowed valueBits resultStore :=
    within_imm
      (hfootprint (index_mem_footprint regs 1))
      hstore honeBits
  have hdivisorValue :
      resultStore regs.candidate - resultStore regs.one =
        candidate - 1 := by
    simp [resultStore, Basic.exec, hcandidate, hone]
  have hdivisorStore : Within allowed valueBits divisorStore := by
    apply within_sub
      (hfootprint (index_mem_footprint regs 2))
      hresultStore
    rwa [hdivisorValue]
  have hdivisorPredValue :
      divisorStore regs.divisor - divisorStore regs.one =
        candidate - 1 - 1 := by
    simp [divisorStore, resultStore, Basic.exec, hcandidate, hone]
  have hdivisorPredStore :
      Within allowed valueBits divisorPredStore := by
    apply within_sub
      (hfootprint (index_mem_footprint regs 3))
      hdivisorStore
    rwa [hdivisorPredValue]
  have hactiveValue :
      divisorPredStore regs.result *
          divisorPredStore regs.divisorPred =
        candidate - 1 - 1 := by
    simp [divisorPredStore, divisorStore, resultStore,
      Basic.exec, hcandidate, hone]
  have hactiveStore : Within allowed valueBits activeStore := by
    apply within_mul
      (hfootprint (index_mem_footprint regs 7))
      hdivisorPredStore
    rwa [hactiveValue]
  apply invariantRuns_basics
  change
    Within allowed valueBits store ∧
      Within allowed valueBits resultStore ∧
      Within allowed valueBits divisorStore ∧
      Within allowed valueBits divisorPredStore ∧
      Within allowed valueBits activeStore
  exact ⟨hstore, hresultStore, hdivisorStore,
    hdivisorPredStore, hactiveStore⟩

private theorem trialLoop_invariantRuns
    (regs : PrimeSearch.Registers)
    (allowed : Finset ℕ) (valueBits bound candidate divisor : ℕ)
    (hfootprint : footprint regs ⊆ allowed)
    (hbound : bitlen bound ≤ valueBits)
    (hcandidateBound : candidate ≤ bound)
    (store : Store)
    (hinv : TrialShape regs candidate divisor store)
    (hstore : Within allowed valueBits store) :
    ∃ final steps,
      InvariantRuns (Within allowed valueBits)
        (PrimeSearch.trialLoop regs) store final steps := by
  induction divisor using Nat.strong_induction_on generalizing store with
  | h divisor ih =>
      by_cases hsmall : divisor ≤ 1
      · have hactiveZero : store regs.active = 0 := by
          rw [hinv.active_eq]
          omega
        exact ⟨store, 1, by
          simpa [PrimeSearch.trialLoop] using
            InvariantRuns.whileZero hactiveZero hstore⟩
      · have hdivisorPos : 0 < divisor := by omega
        have hactiveNonzero : store regs.active ≠ 0 := by
          rw [hinv.active_eq]
          omega
        let copied :=
          (Basic.mul regs.remainder regs.candidate
            regs.result).exec store
        have hcopyInvariant :
            Within allowed valueBits copied := by
          apply within_mul
            (hfootprint (index_mem_footprint regs 4)) hstore
          rw [hinv.candidate_eq, hinv.result_eq, Nat.mul_one]
          exact bitlen_le_of_le hcandidateBound hbound
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
        let reduced :=
          RuntimeArithmetic.reduceResultStore regs.reduceRegisters
            (candidate % divisor) copied
        obtain ⟨reduceSteps, hreduce⟩ :=
          reduce_invariantRuns regs.reduceRegisters allowed valueBits
            bound
            (by
              simpa [PrimeSearch.Registers.reduceRegisters] using
                hfootprint (index_mem_footprint regs 4))
            (by
              simpa [PrimeSearch.Registers.reduceRegisters] using
                hfootprint (index_mem_footprint regs 5))
            hbound copied divisor candidate hdivisorPos
            (by
              simpa [PrimeSearch.Registers.reduceRegisters] using
                hcopiedValue)
            (by
              simpa [PrimeSearch.Registers.reduceRegisters] using
                hcopiedDivisor)
            (by
              simpa [PrimeSearch.Registers.reduceRegisters] using
                hcopiedDivisorPred)
            hcandidateBound hcopyInvariant
        have hreducedInvariant :
            Within allowed valueBits reduced := by
          exact InvariantRuns.final hreduce
        have hreducedCandidate :
            reduced regs.candidate = candidate := by
          simp [reduced, RuntimeArithmetic.reduceResultStore,
            PrimeSearch.Registers.reduceRegisters,
            hcopiedCandidate]
        have hreducedDivisor :
            reduced regs.divisor = divisor := by
          simp [reduced, RuntimeArithmetic.reduceResultStore,
            PrimeSearch.Registers.reduceRegisters,
            hcopiedDivisor]
        have hreducedDivisorPred :
            reduced regs.divisorPred = divisor - 1 := by
          simp [reduced, RuntimeArithmetic.reduceResultStore,
            PrimeSearch.Registers.reduceRegisters,
            hcopiedDivisorPred]
        have hreducedRemainder :
            reduced regs.remainder = candidate % divisor := by
          simp [reduced, RuntimeArithmetic.reduceResultStore,
            PrimeSearch.Registers.reduceRegisters]
        have hreducedResult :
            reduced regs.result = 1 := by
          simp [reduced, RuntimeArithmetic.reduceResultStore,
            PrimeSearch.Registers.reduceRegisters, copied, Basic.exec,
            hinv.result_eq]
        have hreducedOne :
            reduced regs.one = 1 := by
          simp [reduced, RuntimeArithmetic.reduceResultStore,
            PrimeSearch.Registers.reduceRegisters, copied, Basic.exec,
            hinv.one_eq]
        have hcopyRun :
            InvariantRuns (Within allowed valueBits)
              (.basic
                (.mul regs.remainder regs.candidate regs.result))
              store copied 1 :=
          InvariantRuns.basic _ _ hstore hcopyInvariant
        by_cases hmod : candidate % divisor = 0
        · let marked := (Basic.imm regs.result 0).exec reduced
          have hmarkedInvariant :
              Within allowed valueBits marked := by
            apply within_imm
              (hfootprint (index_mem_footprint regs 1))
              hreducedInvariant
            exact bitlen_le_of_le (Nat.zero_le bound) hbound
          let next :=
            (Basic.mul regs.active regs.result
              regs.divisorPred).exec marked
          have hnextInvariant :
              Within allowed valueBits next := by
            apply within_mul
              (hfootprint (index_mem_footprint regs 7))
              hmarkedInvariant
            simp [marked, Basic.exec]
            exact bitlen_le_of_le (Nat.zero_le bound) hbound
          have hremainderZero : reduced regs.remainder = 0 := by
            rw [hreducedRemainder, hmod]
          have hbranch :
              InvariantRuns (Within allowed valueBits)
                (.ifZero regs.remainder
                  (.basic (.imm regs.result 0))
                  (PrimeSearch.decrementDivisor regs))
                reduced marked 2 :=
            InvariantRuns.ifZero hremainderZero
              (InvariantRuns.basic _ _ hreducedInvariant
                hmarkedInvariant)
          have hnextRun :
              InvariantRuns (Within allowed valueBits)
                (.basic
                  (.mul regs.active regs.result
                    regs.divisorPred))
                marked next 1 :=
            InvariantRuns.basic _ _ hmarkedInvariant hnextInvariant
          have hbody :
              InvariantRuns (Within allowed valueBits)
                (PrimeSearch.trialBody regs) store next
                (1 + (reduceSteps + (2 + 1))) := by
            simpa [PrimeSearch.trialBody, copied, reduced, marked,
              next] using
                InvariantRuns.seq hcopyRun
                  (InvariantRuns.seq hreduce
                    (InvariantRuns.seq hbranch hnextRun))
          have hnextActive : next regs.active = 0 := by
            simp [next, marked, Basic.exec]
          have hnextLoop :
              InvariantRuns (Within allowed valueBits)
                (PrimeSearch.trialLoop regs) next next 1 := by
            simpa [PrimeSearch.trialLoop] using
              InvariantRuns.whileZero hnextActive hnextInvariant
          exact ⟨next, 1 + (reduceSteps + (2 + 1)) + 1 + 2,
            by
              simpa [PrimeSearch.trialLoop] using
                InvariantRuns.whileNonzero hactiveNonzero hbody
                  hnextLoop⟩
        · let decremented :=
            (Basic.sub regs.divisor regs.divisor regs.one).exec
              reduced
          have hdecrementedInvariant :
              Within allowed valueBits decremented := by
            apply within_sub
              (hfootprint (index_mem_footprint regs 2))
              hreducedInvariant
            rw [hreducedDivisor, hreducedOne]
            exact bitlen_le_of_le
              ((Nat.sub_le divisor 1).trans
                hinv.divisor_lt.le |>.trans hcandidateBound)
              hbound
          let predecessor :=
            (Basic.sub regs.divisorPred regs.divisorPred
              regs.one).exec decremented
          have hpredecessorInvariant :
              Within allowed valueBits predecessor := by
            apply within_sub
              (hfootprint (index_mem_footprint regs 3))
              hdecrementedInvariant
            simp [decremented, Basic.exec, hreducedDivisorPred,
              hreducedOne]
            exact bitlen_le_of_le
              ((Nat.sub_le (divisor - 1) 1).trans
                ((Nat.sub_le divisor 1).trans
                  hinv.divisor_lt.le) |>.trans hcandidateBound)
              hbound
          let next :=
            (Basic.mul regs.active regs.result
              regs.divisorPred).exec predecessor
          have hnextInvariant :
              Within allowed valueBits next := by
            apply within_mul
              (hfootprint (index_mem_footprint regs 7))
              hpredecessorInvariant
            simp [predecessor, decremented, Basic.exec,
              hreducedDivisorPred, hreducedResult, hreducedOne]
            exact bitlen_le_of_le
              ((Nat.sub_le (divisor - 1) 1).trans
                ((Nat.sub_le divisor 1).trans
                  hinv.divisor_lt.le) |>.trans hcandidateBound)
              hbound
          have hremainderNonzero :
              reduced regs.remainder ≠ 0 := by
            rwa [hreducedRemainder]
          have hdecrement :
              InvariantRuns (Within allowed valueBits)
                (PrimeSearch.decrementDivisor regs)
                reduced predecessor 2 := by
            simpa [PrimeSearch.decrementDivisor, decremented,
              predecessor] using
                InvariantRuns.seq
                  (InvariantRuns.basic
                    (Basic.sub regs.divisor regs.divisor regs.one)
                    reduced hreducedInvariant
                    hdecrementedInvariant)
                  (InvariantRuns.basic
                    (Basic.sub regs.divisorPred
                      regs.divisorPred regs.one)
                    decremented hdecrementedInvariant
                    hpredecessorInvariant)
          have hbranch :
              InvariantRuns (Within allowed valueBits)
                (.ifZero regs.remainder
                  (.basic (.imm regs.result 0))
                  (PrimeSearch.decrementDivisor regs))
                reduced predecessor 4 :=
            InvariantRuns.ifNonzero hremainderNonzero hdecrement
          have hnextRun :
              InvariantRuns (Within allowed valueBits)
                (.basic
                  (.mul regs.active regs.result
                    regs.divisorPred))
                predecessor next 1 :=
            InvariantRuns.basic _ _ hpredecessorInvariant
              hnextInvariant
          have hbody :
              InvariantRuns (Within allowed valueBits)
                (PrimeSearch.trialBody regs) store next
                (1 + (reduceSteps + (4 + 1))) := by
            simpa [PrimeSearch.trialBody, copied, reduced, next] using
              InvariantRuns.seq hcopyRun
                (InvariantRuns.seq hreduce
                  (InvariantRuns.seq hbranch hnextRun))
          have hnextShape :
              TrialShape regs candidate (divisor - 1) next := by
            constructor
            · exact hinv.candidate_pos
            · exact (Nat.sub_le divisor 1).trans_lt
                hinv.divisor_lt
            · simp [next, predecessor, decremented, Basic.exec,
                hreducedCandidate]
            · simp [next, predecessor, decremented, Basic.exec,
                hreducedResult]
            · simp [next, predecessor, decremented, Basic.exec,
                hreducedDivisor, hreducedOne]
            · simp [next, predecessor, decremented, Basic.exec,
                hreducedDivisorPred, hreducedOne]
            · simp [next, predecessor, decremented, Basic.exec,
                hreducedOne]
            · simp [next, predecessor, decremented, Basic.exec,
                hreducedDivisorPred, hreducedResult, hreducedOne]
          have hnextLess : divisor - 1 < divisor := by omega
          obtain ⟨final, loopSteps, hloop⟩ :=
            ih (divisor - 1) hnextLess next hnextShape
              hnextInvariant
          exact ⟨final,
            1 + (reduceSteps + (4 + 1)) + loopSteps + 2,
            by
              simpa [PrimeSearch.trialLoop] using
                InvariantRuns.whileNonzero hactiveNonzero hbody
                  hloop⟩

private theorem primality_invariantRuns_raw
    (regs : PrimeSearch.Registers)
    (allowed : Finset ℕ) (valueBits bound candidate : ℕ)
    (hfootprint : footprint regs ⊆ allowed)
    (hbound : bitlen bound ≤ valueBits)
    (hboundPos : 0 < bound)
    (hcandidateBound : candidate ≤ bound)
    (store : Store)
    (hcandidate : store regs.candidate = candidate)
    (hstore : Within allowed valueBits store) :
    ∃ final steps,
      InvariantRuns (Within allowed valueBits)
        (PrimeSearch.primality regs) store final steps := by
  let setupStore := primalitySetupStore regs store
  obtain ⟨setupSteps, hsetup⟩ :=
    primalitySetup_invariantRuns regs allowed valueBits bound
      candidate hfootprint hbound hboundPos hcandidateBound
      store hcandidate hstore
  have hsetupInvariant :
      Within allowed valueBits setupStore :=
    InvariantRuns.final hsetup
  have hsetupCandidate :
      setupStore regs.candidate = candidate := by
    simp [setupStore, primalitySetupStore,
      PrimeSearch.primalitySetupOps, Basic.execList, Basic.exec,
      hcandidate]
  have hsetupResult :
      setupStore regs.result = 0 := by
    simp [setupStore, primalitySetupStore,
      PrimeSearch.primalitySetupOps, Basic.execList, Basic.exec]
  have hsetupDivisor :
      setupStore regs.divisor = 0 := by
    simp [setupStore, primalitySetupStore,
      PrimeSearch.primalitySetupOps, Basic.execList, Basic.exec]
  have hsetupDivisorPred :
      setupStore regs.divisorPred = 0 := by
    simp [setupStore, primalitySetupStore,
      PrimeSearch.primalitySetupOps, Basic.execList, Basic.exec]
  have hsetupRemainder :
      setupStore regs.remainder = 0 := by
    simp [setupStore, primalitySetupStore,
      PrimeSearch.primalitySetupOps, Basic.execList, Basic.exec]
  have hsetupReduceTest :
      setupStore regs.reduceTest = 0 := by
    simp [setupStore, primalitySetupStore,
      PrimeSearch.primalitySetupOps, Basic.execList, Basic.exec]
  have hsetupOne :
      setupStore regs.one = 1 := by
    simp [setupStore, primalitySetupStore,
      PrimeSearch.primalitySetupOps, Basic.execList, Basic.exec]
  have hsetupActive :
      setupStore regs.active = candidate - 1 := by
    simp [setupStore, primalitySetupStore,
      PrimeSearch.primalitySetupOps, Basic.execList, Basic.exec,
      hcandidate]
  by_cases hsmall : candidate ≤ 1
  · have hactiveZero : setupStore regs.active = 0 := by
      rw [hsetupActive]
      omega
    have hbranch :
        InvariantRuns (Within allowed valueBits)
          (.ifZero regs.active .skip
            (Cmd.seq
              (Cmd.basics (PrimeSearch.trialSetupOps regs))
              (PrimeSearch.trialLoop regs)))
          setupStore setupStore 1 :=
      InvariantRuns.ifZero hactiveZero
        (InvariantRuns.skip setupStore hsetupInvariant)
    exact ⟨setupStore, setupSteps + 1, by
      simpa [PrimeSearch.primality] using
        InvariantRuns.seq hsetup hbranch⟩
  · have hcandidateTwo : 2 ≤ candidate := by omega
    have hactiveNonzero : setupStore regs.active ≠ 0 := by
      rw [hsetupActive]
      omega
    let trialStore := trialSetupStore regs setupStore
    obtain ⟨trialSetupSteps, htrialSetup⟩ :=
      trialSetup_invariantRuns regs allowed valueBits bound
        candidate hfootprint hbound hcandidateTwo hcandidateBound
        setupStore hsetupCandidate hsetupOne hsetupInvariant
    have htrialInvariant :
        Within allowed valueBits trialStore :=
      InvariantRuns.final htrialSetup
    have htrialShape :
        TrialShape regs candidate (candidate - 1) trialStore := by
      constructor
      · exact hcandidateTwo
      · omega
      · simp [trialStore, trialSetupStore,
          PrimeSearch.trialSetupOps, Basic.execList, Basic.exec,
          hsetupCandidate]
      · simp [trialStore, trialSetupStore,
          PrimeSearch.trialSetupOps, Basic.execList, Basic.exec]
      · simp [trialStore, trialSetupStore,
          PrimeSearch.trialSetupOps, Basic.execList, Basic.exec,
          hsetupCandidate, hsetupOne]
      · simp [trialStore, trialSetupStore,
          PrimeSearch.trialSetupOps, Basic.execList, Basic.exec,
          hsetupCandidate, hsetupOne]
      · simp [trialStore, trialSetupStore,
          PrimeSearch.trialSetupOps, Basic.execList, Basic.exec,
          hsetupOne]
      · simp [trialStore, trialSetupStore,
          PrimeSearch.trialSetupOps, Basic.execList, Basic.exec,
          hsetupCandidate, hsetupOne]
    obtain ⟨final, loopSteps, hloop⟩ :=
      trialLoop_invariantRuns regs allowed valueBits bound
        candidate (candidate - 1) hfootprint hbound
        hcandidateBound trialStore htrialShape htrialInvariant
    have hnonzeroBranch :
        InvariantRuns (Within allowed valueBits)
          (Cmd.seq
            (Cmd.basics (PrimeSearch.trialSetupOps regs))
            (PrimeSearch.trialLoop regs))
          setupStore final (trialSetupSteps + loopSteps) :=
      InvariantRuns.seq htrialSetup hloop
    have hbranch :
        InvariantRuns (Within allowed valueBits)
          (.ifZero regs.active .skip
            (Cmd.seq
              (Cmd.basics (PrimeSearch.trialSetupOps regs))
              (PrimeSearch.trialLoop regs)))
          setupStore final
          (trialSetupSteps + loopSteps + 2) :=
      InvariantRuns.ifNonzero hactiveNonzero hnonzeroBranch
    exact ⟨final,
      setupSteps + (trialSetupSteps + loopSteps + 2), by
        simpa [PrimeSearch.primality] using
          InvariantRuns.seq hsetup hbranch⟩

theorem primalityInvariantRuns_internal
    (regs : PrimeSearch.Registers)
    (allowed : Finset ℕ) (valueBits bound candidate : ℕ)
    (hfootprint : footprint regs ⊆ allowed)
    (hbound : bitlen bound ≤ valueBits)
    (hboundPos : 0 < bound)
    (hcandidateBound : candidate ≤ bound)
    (store : Store)
    (hcandidate : store regs.candidate = candidate)
    (hstore :
      SearchProgram.MutableValuesWithin allowed valueBits store) :
    ∃ final steps,
      InvariantRuns
        (SearchProgram.MutableValuesWithin allowed valueBits)
        (PrimeSearch.primality regs) store final steps ∧
      PrimeSearch.PrimalityPost regs candidate final := by
  obtain ⟨final, steps, hrun⟩ :=
    primality_invariantRuns_raw regs allowed valueBits bound
      candidate hfootprint hbound hboundPos hcandidateBound
      store hcandidate hstore
  obtain ⟨semanticFinal, hsemantic, hpost⟩ :=
    PrimeSearch.primality_runs regs store candidate hcandidate
  have hfinal :
      final = semanticFinal :=
    runs_final_unique (InvariantRuns.toRuns hrun) hsemantic
  exact ⟨final, steps, hrun, hfinal ▸ hpost⟩

private structure SearchShape
    (regs : PrimeSearch.Registers) (candidate : ℕ)
    (store : Store) : Prop where
  candidate_eq : store regs.candidate = candidate
  result_eq :
    store regs.result = PrimeSearch.primalityValue candidate
  one_eq : store regs.one = 1
  active_eq :
    store regs.active =
      1 - PrimeSearch.primalityValue candidate

private theorem refresh_invariantRuns
    (regs : PrimeSearch.Registers)
    (allowed : Finset ℕ) (valueBits bound candidate : ℕ)
    (hfootprint : footprint regs ⊆ allowed)
    (hbound : bitlen bound ≤ valueBits)
    (hboundPositive : 0 < bound)
    (store : Store)
    (hpost : PrimeSearch.PrimalityPost regs candidate store)
    (hstore : Within allowed valueBits store) :
    ∃ refreshed,
      InvariantRuns (Within allowed valueBits)
        (PrimeSearch.refreshSearchTest regs)
        store refreshed 1 ∧
      SearchShape regs candidate refreshed := by
  let refreshed :=
    (Basic.sub regs.active regs.one regs.result).exec store
  have hrefreshValue :
      store regs.one - store regs.result =
        1 - PrimeSearch.primalityValue candidate := by
    rw [hpost.one_eq, hpost.result_eq]
  have hrefreshInvariant :
      Within allowed valueBits refreshed := by
    apply within_sub
      (hfootprint (index_mem_footprint regs 7)) hstore
    rw [hrefreshValue]
    apply bitlen_le_of_le _ hbound
    exact (Nat.sub_le 1 _).trans (by omega)
  refine ⟨refreshed, ?_, ?_⟩
  · simpa [PrimeSearch.refreshSearchTest, refreshed] using
      InvariantRuns.basic
        (Basic.sub regs.active regs.one regs.result)
        store hstore hrefreshInvariant
  · constructor
    · simp [refreshed, Basic.exec, hpost.candidate_eq]
    · simp [refreshed, Basic.exec, hpost.result_eq]
    · simp [refreshed, Basic.exec, hpost.one_eq]
    · simp [refreshed, Basic.exec, hpost.one_eq,
        hpost.result_eq]

private theorem searchLoop_invariantRuns
    (regs : PrimeSearch.Registers)
    (allowed : Finset ℕ) (valueBits selectedPrime candidate : ℕ)
    (hfootprint : footprint regs ⊆ allowed)
    (hbound : bitlen selectedPrime ≤ valueBits)
    (hselectedPrime : selectedPrime.Prime)
    (hcandidateUpper : candidate ≤ selectedPrime)
    (store : Store)
    (hinv : SearchShape regs candidate store)
    (hstore : Within allowed valueBits store) :
    ∃ final steps,
      InvariantRuns (Within allowed valueBits)
        (.whileNonzero regs.active (PrimeSearch.searchBody regs))
        store final steps := by
  generalize hgapEq : selectedPrime - candidate = gap
  induction gap using Nat.strong_induction_on
      generalizing candidate store with
  | h gap ih =>
      by_cases hprime : candidate.Prime
      · have hactiveZero : store regs.active = 0 := by
          rw [hinv.active_eq]
          simp [PrimeSearch.primalityValue, hprime]
        exact ⟨store, 1,
          InvariantRuns.whileZero hactiveZero hstore⟩
      · have hcandidateNe : candidate ≠ selectedPrime := by
          intro heq
          exact hprime (heq ▸ hselectedPrime)
        have hcandidateLt : candidate < selectedPrime :=
          lt_of_le_of_ne hcandidateUpper hcandidateNe
        have hactiveNonzero : store regs.active ≠ 0 := by
          rw [hinv.active_eq]
          simp [PrimeSearch.primalityValue, hprime]
        let incremented :=
          (Basic.add regs.candidate regs.candidate
            regs.one).exec store
        have hincrementedInvariant :
            Within allowed valueBits incremented := by
          apply within_add
            (hfootprint (index_mem_footprint regs 0)) hstore
          rw [hinv.candidate_eq, hinv.one_eq]
          apply bitlen_le_of_le _ hbound
          omega
        have hincrementedCandidate :
            incremented regs.candidate = candidate + 1 := by
          simp [incremented, Basic.exec, hinv.candidate_eq,
            hinv.one_eq]
        have hincrement :
            InvariantRuns (Within allowed valueBits)
              (.basic
                (.add regs.candidate regs.candidate regs.one))
              store incremented 1 :=
          InvariantRuns.basic _ _ hstore hincrementedInvariant
        obtain ⟨tested, testSteps, htest, hpost⟩ :=
          primalityInvariantRuns_internal regs allowed valueBits
            selectedPrime (candidate + 1) hfootprint hbound
            (by omega) (by omega) incremented
            hincrementedCandidate hincrementedInvariant
        have htestedInvariant :
            Within allowed valueBits tested :=
          InvariantRuns.final htest
        obtain ⟨refreshed, hrefresh, hnextShape⟩ :=
          refresh_invariantRuns regs allowed valueBits selectedPrime
            (candidate + 1) hfootprint hbound
            hselectedPrime.pos tested hpost htestedInvariant
        have hbody :
            InvariantRuns (Within allowed valueBits)
              (PrimeSearch.searchBody regs) store refreshed
              (1 + (testSteps + 1)) := by
          simpa [PrimeSearch.searchBody, incremented] using
            InvariantRuns.seq hincrement
              (InvariantRuns.seq htest hrefresh)
        have hnextUpper :
            candidate + 1 ≤ selectedPrime := by omega
        have hnextGap :
            selectedPrime - (candidate + 1) < gap := by
          omega
        obtain ⟨final, loopSteps, hloop⟩ :=
          ih (selectedPrime - (candidate + 1)) hnextGap
            (candidate := candidate + 1) (store := refreshed)
            hnextUpper hnextShape (InvariantRuns.final hrefresh) rfl
        exact ⟨final, 1 + (testSteps + 1) + loopSteps + 2,
          InvariantRuns.whileNonzero hactiveNonzero hbody hloop⟩

private theorem searchInvariantRunsWithPrime_internal
    (regs : PrimeSearch.Registers)
    (allowed : Finset ℕ)
    (valueBits lower selectedPrime : ℕ)
    (hfootprint : footprint regs ⊆ allowed)
    (hselectedPrime : selectedPrime.Prime)
    (hlowerPrime : lower ≤ selectedPrime)
    (hselectedWidth : bitlen selectedPrime ≤ valueBits)
    (store : Store)
    (hlower : store regs.candidate = lower)
    (hstore :
      SearchProgram.MutableValuesWithin allowed valueBits store) :
    ∃ final steps,
      InvariantRuns
        (SearchProgram.MutableValuesWithin allowed valueBits)
        (PrimeSearch.search regs) store final steps ∧
      PrimeSearch.SearchPost regs lower final := by
  obtain ⟨tested, testSteps, htest, hprimalityPost⟩ :=
    primalityInvariantRuns_internal regs allowed valueBits
      selectedPrime lower hfootprint hselectedWidth
      hselectedPrime.pos hlowerPrime store hlower hstore
  have htestedInvariant :
      Within allowed valueBits tested :=
    InvariantRuns.final htest
  obtain ⟨refreshed, hrefresh, hshape⟩ :=
    refresh_invariantRuns regs allowed valueBits selectedPrime
      lower hfootprint hselectedWidth hselectedPrime.pos tested
      hprimalityPost htestedInvariant
  obtain ⟨final, loopSteps, hloop⟩ :=
    searchLoop_invariantRuns regs allowed valueBits selectedPrime
      lower hfootprint hselectedWidth hselectedPrime hlowerPrime
      refreshed hshape (InvariantRuns.final hrefresh)
  have hrun :
      InvariantRuns
        (SearchProgram.MutableValuesWithin allowed valueBits)
        (PrimeSearch.search regs) store final
        (testSteps + (1 + loopSteps)) := by
    simpa [PrimeSearch.search] using
      InvariantRuns.seq htest
        (InvariantRuns.seq hrefresh hloop)
  obtain ⟨semanticFinal, hsemantic, hpost⟩ :=
    PrimeSearch.search_runs regs store lower hlower
  have hfinal : final = semanticFinal :=
    runs_final_unique (InvariantRuns.toRuns hrun) hsemantic
  exact ⟨final, testSteps + (1 + loopSteps), hrun,
    hfinal ▸ hpost⟩

theorem searchInvariantRuns_internal
    (regs : PrimeSearch.Registers)
    (allowed : Finset ℕ) (valueBits lower : ℕ)
    (hfootprint : footprint regs ⊆ allowed)
    (hwidth : bitlen lower + 2 ≤ valueBits)
    (store : Store)
    (hlower : store regs.candidate = lower)
    (hstore :
      SearchProgram.MutableValuesWithin allowed valueBits store) :
    ∃ final steps,
      InvariantRuns
        (SearchProgram.MutableValuesWithin allowed valueBits)
        (PrimeSearch.search regs) store final steps ∧
      PrimeSearch.SearchPost regs lower final := by
  by_cases hzero : lower = 0
  · have hselectedWidth : bitlen 2 ≤ valueBits := by
      norm_num [hzero, bitlen] at hwidth ⊢
      exact hwidth
    have hrun :=
      searchInvariantRunsWithPrime_internal regs allowed
        valueBits 0 2 hfootprint Nat.prime_two (by omega)
        hselectedWidth store (by simpa [hzero] using hlower)
        hstore
    simpa [hzero] using hrun
  · have hlowerPos : 0 < lower := Nat.pos_of_ne_zero hzero
    obtain ⟨selectedPrime, hselectedPrime, hlowerPrime,
        hprimeUpper⟩ :=
      Nat.bertrand lower hzero
    have hdouble :
        bitlen (2 * lower) = bitlen lower + 1 := by
      simpa [bitlen, Nat.shiftLeft_eq_mul_pow, Nat.mul_comm] using
        Nat.size_shiftLeft hzero 1
    have hselectedWidth :
        bitlen selectedPrime ≤ valueBits := by
      apply le_trans _ (show bitlen lower + 1 ≤ valueBits by
        omega)
      rw [← hdouble]
      simpa [bitlen] using Nat.size_le_size hprimeUpper
    exact searchInvariantRunsWithPrime_internal regs allowed
      valueBits lower selectedPrime hfootprint hselectedPrime
      hlowerPrime.le hselectedWidth store hlower hstore

end Internal

end PrimeSearchInvariant

end Runtime

end TimeSpaceSimulation

end Complexity
