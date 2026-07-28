/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.RandomAccessMachine.Structured.Run
import Complexitylib.Models.RandomAccessMachine.Structured.Invariant
import Complexitylib.Models.RandomAccessMachine.Structured.Footprint
import
  Complexitylib.Models.RandomAccessMachine.Structured.RuntimeArithmetic
import
  Complexitylib.TimeSpaceSimulation.NeighborhoodGraph.WorkspaceAccounting
import
  Complexitylib.TimeSpaceSimulation.ComputationGraph.CompactEncoding
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodProgram.Defs

/-!
# Proof internals for the fixed-register neighborhood runtime
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace Runtime

namespace NeighborhoodProgram

open RAM Structured
open NeighborhoodGraph

namespace Internal

theorem valuesWithin_bitlen_internal
    {allowed : Finset ℕ} {bound valueBits : ℕ} {store : Store}
    (hstore : ValuesWithin allowed bound store)
    (hbound : RAM.bitlen bound ≤ valueBits) :
    ∀ address, address ∈ allowed →
      RAM.bitlen (store address) ≤ valueBits := by
  intro address haddress
  have hsize :
      RAM.bitlen (store address) ≤ RAM.bitlen bound := by
    simpa [RAM.bitlen] using
      Nat.size_le_size (hstore address haddress)
  exact hsize.trans hbound

theorem transientValueBound_bounds_internal
    (packedCapacity base modulus operand counter : ℕ) :
    counter ≤ transientValueBound packedCapacity base modulus operand counter ∧
    base ≤ transientValueBound packedCapacity base modulus operand counter ∧
    modulus ≤ transientValueBound packedCapacity base modulus operand counter ∧
    operand ≤ transientValueBound packedCapacity base modulus operand counter ∧
    packedCapacity ≤
      transientValueBound packedCapacity base modulus operand counter ∧
    base * packedCapacity ≤
      transientValueBound packedCapacity base modulus operand counter ∧
    operand + base * packedCapacity ≤
      transientValueBound packedCapacity base modulus operand counter ∧
    packedCapacity + operand ≤
      transientValueBound packedCapacity base modulus operand counter ∧
    packedCapacity * operand ≤
      transientValueBound packedCapacity base modulus operand counter := by
  simp [transientValueBound]

private theorem valuesWithin_update
    {allowed : Finset ℕ} {bound index value : ℕ} {store : Store}
    (hstore : ValuesWithin allowed bound store)
    (hvalue : value ≤ bound) :
    ValuesWithin allowed bound (Function.update store index value) := by
  intro address haddress
  by_cases heq : address = index
  · subst address
    simpa using hvalue
  · simpa [Function.update_of_ne heq] using
      hstore address haddress

private theorem valuesWithin_imm
    {allowed : Finset ℕ} {bound destination value : ℕ}
    {store : Store}
    (hstore : ValuesWithin allowed bound store)
    (hvalue : value ≤ bound) :
    ValuesWithin allowed bound
      ((Basic.imm destination value).exec store) := by
  simpa [Basic.exec] using
    valuesWithin_update hstore hvalue

private theorem valuesWithin_add
    {allowed : Finset ℕ} {bound destination left right : ℕ}
    {store : Store}
    (hstore : ValuesWithin allowed bound store)
    (hvalue : store left + store right ≤ bound) :
    ValuesWithin allowed bound
      ((Basic.add destination left right).exec store) := by
  simpa [Basic.exec] using
    valuesWithin_update hstore hvalue

private theorem valuesWithin_sub
    {allowed : Finset ℕ} {bound destination left right : ℕ}
    {store : Store}
    (hstore : ValuesWithin allowed bound store)
    (hvalue : store left - store right ≤ bound) :
    ValuesWithin allowed bound
      ((Basic.sub destination left right).exec store) := by
  simpa [Basic.exec] using
    valuesWithin_update hstore hvalue

private theorem valuesWithin_mul
    {allowed : Finset ℕ} {bound destination left right : ℕ}
    {store : Store}
    (hstore : ValuesWithin allowed bound store)
    (hvalue : store left * store right ≤ bound) :
    ValuesWithin allowed bound
      ((Basic.mul destination left right).exec store) := by
  simpa [Basic.exec] using
    valuesWithin_update hstore hvalue

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
    (allowed : Finset ℕ) (bound : ℕ)
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
    (hstore : ValuesWithin allowed bound store) :
    ∃ steps,
      InvariantRuns (ValuesWithin allowed bound)
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
          ValuesWithin allowed bound valueStore := by
        apply valuesWithin_sub hstore
        rw [hvalue, hmodulusValue]
        exact (Nat.sub_le _ _).trans htotal
      have hvalueStoreModulusPred :
          valueStore regs.modulusPred = modulus - 1 := by
        simp [valueStore, Basic.exec,
          regs.value_ne_modulusPred.symm, hmodulusPred]
      have hnextInvariant :
          ValuesWithin allowed bound nextStore := by
        apply valuesWithin_sub hvalueStoreInvariant
        rw [hvalueStoreValue, hvalueStoreModulusPred]
        exact (Nat.sub_le _ _).trans hvalueStoreBound
      have hbody :
          InvariantRuns (ValuesWithin allowed bound)
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

theorem reduce_invariantRuns_internal
    (regs : RuntimeArithmetic.ReduceRegisters)
    (allowed : Finset ℕ) (bound : ℕ)
    (store : Store) (modulus value : ℕ)
    (hmodulus : 0 < modulus)
    (hvalue : store regs.value = value)
    (hmodulusValue : store regs.modulus = modulus)
    (hmodulusPred :
      store regs.modulusPred = modulus - 1)
    (hvalueBound : value ≤ bound)
    (hstore : ValuesWithin allowed bound store) :
    ∃ steps,
      InvariantRuns (ValuesWithin allowed bound)
        (RuntimeArithmetic.reduce regs) store
        (RuntimeArithmetic.reduceResultStore regs
          (value % modulus) store)
        steps := by
  let testedStore :=
    (RuntimeArithmetic.reduceTestOp regs).exec store
  have htestedInvariant :
      ValuesWithin allowed bound testedStore := by
    apply valuesWithin_sub hstore
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
  obtain ⟨loopSteps, hloop⟩ :=
    reduceLoop_invariantRuns regs allowed bound testedStore modulus
      (value % modulus) (value / modulus)
      hmodulus (Nat.mod_lt value hmodulus) htestedQuotient
      htestedModulus htestedModulusPred htestedTest
      (by simpa [hdecompose] using hvalueBound) htestedInvariant
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

theorem addMod_invariantRuns_internal
    (regs : RuntimeArithmetic.ReduceRegisters)
    (allowed : Finset ℕ) (bound left right : ℕ)
    (store : Store) (modulus : ℕ)
    (hmodulus : 0 < modulus)
    (hmodulusValue : store regs.modulus = modulus)
    (hmodulusPred :
      store regs.modulusPred = modulus - 1)
    (hrawBound : store left + store right ≤ bound)
    (hstore : ValuesWithin allowed bound store) :
    ∃ steps,
      InvariantRuns (ValuesWithin allowed bound)
        (RuntimeArithmetic.addMod regs left right) store
        (RuntimeArithmetic.reduceResultStore regs
          ((store left + store right) % modulus) store)
        steps := by
  let rawStore :=
    (Basic.add regs.value left right).exec store
  have hrawInvariant :
      ValuesWithin allowed bound rawStore :=
    valuesWithin_add hstore hrawBound
  have hrawValue :
      rawStore regs.value = store left + store right := by
    simp [rawStore, Basic.exec]
  have hrawModulus :
      rawStore regs.modulus = modulus := by
    simp [rawStore, Basic.exec, regs.value_ne_modulus.symm,
      hmodulusValue]
  have hrawModulusPred :
      rawStore regs.modulusPred = modulus - 1 := by
    simp [rawStore, Basic.exec, regs.value_ne_modulusPred.symm,
      hmodulusPred]
  obtain ⟨reduceSteps, hreduce⟩ :=
    reduce_invariantRuns_internal regs allowed bound rawStore
      modulus (store left + store right) hmodulus hrawValue
      hrawModulus hrawModulusPred hrawBound hrawInvariant
  have hresult :
      RuntimeArithmetic.reduceResultStore regs
          ((store left + store right) % modulus) rawStore =
        RuntimeArithmetic.reduceResultStore regs
          ((store left + store right) % modulus) store := by
    funext index
    by_cases hvalueIndex : index = regs.value
    · subst index
      simp [RuntimeArithmetic.reduceResultStore,
        regs.value_ne_test]
    · by_cases htestIndex : index = regs.test
      · subst index
        simp [RuntimeArithmetic.reduceResultStore]
      · simp [RuntimeArithmetic.reduceResultStore, rawStore,
          Basic.exec, Function.update_of_ne, hvalueIndex,
          htestIndex]
  rw [hresult] at hreduce
  exact ⟨1 + reduceSteps, by
    simpa [RuntimeArithmetic.addMod, rawStore] using
      InvariantRuns.seq
        (InvariantRuns.basic
          (Basic.add regs.value left right) store
          hstore hrawInvariant)
        hreduce⟩

theorem mulMod_invariantRuns_internal
    (regs : RuntimeArithmetic.ReduceRegisters)
    (allowed : Finset ℕ) (bound left right : ℕ)
    (store : Store) (modulus : ℕ)
    (hmodulus : 0 < modulus)
    (hmodulusValue : store regs.modulus = modulus)
    (hmodulusPred :
      store regs.modulusPred = modulus - 1)
    (hrawBound : store left * store right ≤ bound)
    (hstore : ValuesWithin allowed bound store) :
    ∃ steps,
      InvariantRuns (ValuesWithin allowed bound)
        (RuntimeArithmetic.mulMod regs left right) store
        (RuntimeArithmetic.reduceResultStore regs
          ((store left * store right) % modulus) store)
        steps := by
  let rawStore :=
    (Basic.mul regs.value left right).exec store
  have hrawInvariant :
      ValuesWithin allowed bound rawStore :=
    valuesWithin_mul hstore hrawBound
  have hrawValue :
      rawStore regs.value = store left * store right := by
    simp [rawStore, Basic.exec]
  have hrawModulus :
      rawStore regs.modulus = modulus := by
    simp [rawStore, Basic.exec, regs.value_ne_modulus.symm,
      hmodulusValue]
  have hrawModulusPred :
      rawStore regs.modulusPred = modulus - 1 := by
    simp [rawStore, Basic.exec, regs.value_ne_modulusPred.symm,
      hmodulusPred]
  obtain ⟨reduceSteps, hreduce⟩ :=
    reduce_invariantRuns_internal regs allowed bound rawStore
      modulus (store left * store right) hmodulus hrawValue
      hrawModulus hrawModulusPred hrawBound hrawInvariant
  have hresult :
      RuntimeArithmetic.reduceResultStore regs
          ((store left * store right) % modulus) rawStore =
        RuntimeArithmetic.reduceResultStore regs
          ((store left * store right) % modulus) store := by
    funext index
    by_cases hvalueIndex : index = regs.value
    · subst index
      simp [RuntimeArithmetic.reduceResultStore,
        regs.value_ne_test]
    · by_cases htestIndex : index = regs.test
      · subst index
        simp [RuntimeArithmetic.reduceResultStore]
      · simp [RuntimeArithmetic.reduceResultStore, rawStore,
          Basic.exec, Function.update_of_ne, hvalueIndex,
          htestIndex]
  rw [hresult] at hreduce
  exact ⟨1 + reduceSteps, by
    simpa [RuntimeArithmetic.mulMod, rawStore] using
      InvariantRuns.seq
        (InvariantRuns.basic
          (Basic.mul regs.value left right) store
          hstore hrawInvariant)
        hreduce⟩

theorem peek_invariantRuns_internal
    (regs : StackRegisters) (allowed : Finset ℕ) (bound : ℕ)
    (store : Store) (base word : ℕ)
    (hbase : 0 < base)
    (hword : store regs.word = word)
    (hbaseValue : store regs.base = base)
    (hbasePred : store regs.basePred = base - 1)
    (hwordBound : word ≤ bound)
    (hstore : ValuesWithin allowed bound store) :
    ∃ steps,
      InvariantRuns (ValuesWithin allowed bound)
        (peek regs) store
        (peekResultStore regs (PackedDigits.digit base word 0)
          store)
        steps := by
  let cleared :=
    (Basic.imm regs.value 0).exec store
  let copied :=
    (Basic.add regs.value regs.word regs.value).exec cleared
  have hclearedInvariant :
      ValuesWithin allowed bound cleared := by
    exact valuesWithin_imm hstore (Nat.zero_le bound)
  have hclearedWord : cleared regs.word = word := by
    simp [cleared, Basic.exec,
      regs.index_ne (first := 0) (second := 6) (by decide),
      hword]
  have hclearedValue : cleared regs.value = 0 := by
    simp [cleared, Basic.exec]
  have hcopiedInvariant :
      ValuesWithin allowed bound copied := by
    apply valuesWithin_add hclearedInvariant
    rw [hclearedWord, hclearedValue, Nat.add_zero]
    exact hwordBound
  have hcopiedValue : copied regs.value = word := by
    simp [copied, Basic.exec, hclearedWord, hclearedValue]
  have hcopiedBase : copied regs.base = base := by
    simp [copied, cleared, Basic.exec, regs.injective.eq_iff,
      hbaseValue]
  have hcopiedBasePred : copied regs.basePred = base - 1 := by
    simp [copied, cleared, Basic.exec, regs.injective.eq_iff,
      hbasePred]
  obtain ⟨reduceSteps, hreduce⟩ :=
    reduce_invariantRuns_internal regs.reduceRegisters allowed bound
      copied base word hbase hcopiedValue hcopiedBase
      hcopiedBasePred hwordBound hcopiedInvariant
  have hresult :
      RuntimeArithmetic.reduceResultStore regs.reduceRegisters
          (word % base) copied =
        peekResultStore regs (PackedDigits.digit base word 0)
          store := by
    funext address
    by_cases hvalueIndex : address = regs.value
    · subst address
      simp [RuntimeArithmetic.reduceResultStore, peekResultStore,
        StackRegisters.reduceRegisters, PackedDigits.digit,
        regs.index_ne (first := 6) (second := 4) (by decide)]
    · by_cases htestIndex : address = regs.test
      · subst address
        simp [RuntimeArithmetic.reduceResultStore, peekResultStore,
          StackRegisters.reduceRegisters]
      · simp [RuntimeArithmetic.reduceResultStore, peekResultStore,
          StackRegisters.reduceRegisters, copied, cleared, Basic.exec,
          Function.update_of_ne, hvalueIndex, htestIndex]
  rw [hresult] at hreduce
  exact ⟨1 + (1 + reduceSteps), by
    simpa [peek, Cmd.seqList] using
      InvariantRuns.seq
        (InvariantRuns.basic (Basic.imm regs.value 0) store
          hstore hclearedInvariant)
        (InvariantRuns.seq
          (InvariantRuns.basic
            (Basic.add regs.value regs.word regs.value) cleared
            hclearedInvariant hcopiedInvariant)
          hreduce)⟩

theorem push_invariantRuns_internal
    (regs : StackRegisters) (allowed : Finset ℕ) (bound : ℕ)
    (store : Store) (base word value : ℕ)
    (hword : store regs.word = word)
    (hbaseValue : store regs.base = base)
    (hvalue : store regs.value = value)
    (hproductBound : base * word ≤ bound)
    (hpushBound : value + base * word ≤ bound)
    (hstore : ValuesWithin allowed bound store) :
    InvariantRuns (ValuesWithin allowed bound)
      (push regs) store
      (pushResultStore regs (PackedDigits.push base value word)
        store)
      3 := by
  let afterMul :=
    (Basic.mul regs.quotient regs.base regs.word).exec store
  let afterAdd :=
    (Basic.add regs.word regs.value regs.quotient).exec afterMul
  let final :=
    (Basic.imm regs.quotient 0).exec afterAdd
  have hafterMulProduct :
      afterMul regs.quotient = base * word := by
    simp [afterMul, Basic.exec, hbaseValue, hword]
  have hafterMulValue : afterMul regs.value = value := by
    simp [afterMul, Basic.exec,
      regs.index_ne (first := 6) (second := 3) (by decide),
      hvalue]
  have hafterMulInvariant :
      ValuesWithin allowed bound afterMul := by
    apply valuesWithin_mul hstore
    rw [hbaseValue, hword]
    exact hproductBound
  have hafterAddWord :
      afterAdd regs.word = value + base * word := by
    simp only [afterAdd, Basic.exec, Function.update_self]
    rw [hafterMulValue, hafterMulProduct]
  have hafterAddInvariant :
      ValuesWithin allowed bound afterAdd := by
    apply valuesWithin_add hafterMulInvariant
    rw [hafterMulValue, hafterMulProduct]
    exact hpushBound
  have hfinalInvariant :
      ValuesWithin allowed bound final := by
    exact valuesWithin_imm hafterAddInvariant (Nat.zero_le bound)
  have hresult :
      final =
        pushResultStore regs (PackedDigits.push base value word)
          store := by
    funext address
    by_cases hwordIndex : address = regs.word
    · subst address
      simp only [final, Basic.exec]
      rw [Function.update_of_ne
        (regs.index_ne (first := 0) (second := 3) (by decide))]
      rw [hafterAddWord]
      simp [pushResultStore, PackedDigits.push,
        regs.index_ne (first := 0) (second := 3) (by decide)]
    · by_cases hquotientIndex : address = regs.quotient
      · subst address
        simp [final, pushResultStore, Basic.exec]
      · simp [final, afterAdd, afterMul, pushResultStore, Basic.exec,
          Function.update_of_ne, hwordIndex, hquotientIndex]
  rw [← hresult]
  simpa [push, Cmd.seqList] using
    InvariantRuns.seq
      (InvariantRuns.basic
        (Basic.mul regs.quotient regs.base regs.word) store
        hstore hafterMulInvariant)
      (InvariantRuns.seq
        (InvariantRuns.basic
          (Basic.add regs.word regs.value regs.quotient) afterMul
          hafterMulInvariant hafterAddInvariant)
        (InvariantRuns.basic (Basic.imm regs.quotient 0) afterAdd
          hafterAddInvariant hfinalInvariant))

private theorem popLoop_invariantRuns
    (regs : StackRegisters) (allowed : Finset ℕ) (bound : ℕ)
    (store : Store)
    (base remainder remaining completed : ℕ)
    (hbase : 0 < base) (hremainder : remainder < base)
    (hword :
      store regs.word = remaining * base + remainder)
    (hquotient : store regs.quotient = completed)
    (htest :
      store regs.test =
        remaining * base + remainder - (base - 1))
    (hbaseValue : store regs.base = base)
    (hbasePred : store regs.basePred = base - 1)
    (hone : store regs.one = 1)
    (hwordBound : remaining * base + remainder ≤ bound)
    (hquotientBound : completed + remaining ≤ bound)
    (hstore : ValuesWithin allowed bound store) :
    ∃ final steps,
      InvariantRuns (ValuesWithin allowed bound)
        (.whileNonzero regs.test (popBody regs))
        store final steps ∧
      final regs.word = remainder ∧
      final regs.quotient = completed + remaining ∧
      final regs.test = 0 ∧
      final regs.base = base ∧
      final regs.basePred = base - 1 ∧
      final regs.one = 1 := by
  induction remaining generalizing store completed with
  | zero =>
      have htestZero : store regs.test = 0 := by
        rw [htest]
        omega
      exact ⟨store, 1,
        InvariantRuns.whileZero htestZero hstore,
        by simpa using hword, by simpa using hquotient, htestZero,
        hbaseValue, hbasePred, hone⟩
  | succ remaining ih =>
      have htestNonzero : store regs.test ≠ 0 := by
        rw [htest]
        simp only [Nat.succ_mul]
        omega
      let afterSub :=
        (Basic.sub regs.word regs.word regs.base).exec store
      let afterIncrement :=
        (Basic.add regs.quotient regs.quotient regs.one).exec
          afterSub
      let afterTest := (popTestOp regs).exec afterIncrement
      have hafterSubInvariant :
          ValuesWithin allowed bound afterSub := by
        apply valuesWithin_sub hstore
        rw [hword, hbaseValue]
        exact (Nat.sub_le _ _).trans hwordBound
      have hafterSubQuotient :
          afterSub regs.quotient = completed := by
        simp [afterSub, Basic.exec,
          regs.index_ne (first := 3) (second := 0) (by decide),
          hquotient]
      have hafterSubOne : afterSub regs.one = 1 := by
        simp [afterSub, Basic.exec,
          regs.index_ne (first := 5) (second := 0) (by decide),
          hone]
      have hcompletedSuccBound : completed + 1 ≤ bound := by
        omega
      have hafterIncrementInvariant :
          ValuesWithin allowed bound afterIncrement := by
        apply valuesWithin_add hafterSubInvariant
        rw [hafterSubQuotient, hafterSubOne]
        exact hcompletedSuccBound
      have hnextWord :
          afterTest regs.word = remaining * base + remainder := by
        simp only [afterTest, popTestOp, Basic.exec]
        rw [Function.update_of_ne
          (regs.index_ne (first := 0) (second := 4) (by decide))]
        simp only [afterIncrement, Basic.exec]
        rw [Function.update_of_ne
          (regs.index_ne (first := 0) (second := 3) (by decide))]
        simp only [afterSub, Basic.exec, Function.update_self]
        rw [hword, hbaseValue]
        simp only [Nat.succ_mul]
        omega
      have hnextQuotient :
          afterTest regs.quotient = completed + 1 := by
        simp only [afterTest, popTestOp, Basic.exec]
        rw [Function.update_of_ne
          (regs.index_ne (first := 3) (second := 4) (by decide))]
        simp only [afterIncrement, Basic.exec, Function.update_self]
        rw [hafterSubQuotient, hafterSubOne]
      have hnextBase : afterTest regs.base = base := by
        simp [afterTest, popTestOp, afterIncrement, afterSub,
          Basic.exec, regs.injective.eq_iff, hbaseValue]
      have hnextBasePred :
          afterTest regs.basePred = base - 1 := by
        simp [afterTest, popTestOp, afterIncrement, afterSub,
          Basic.exec, regs.injective.eq_iff, hbasePred]
      have hnextOne : afterTest regs.one = 1 := by
        simp [afterTest, popTestOp, afterIncrement, afterSub,
          Basic.exec, regs.injective.eq_iff, hone]
      have hafterIncrementWord :
          afterIncrement regs.word =
            remaining * base + remainder := by
        rw [← hnextWord]
        simp [afterTest, popTestOp, Basic.exec,
          regs.index_ne (first := 0) (second := 4) (by decide)]
      have hafterIncrementBasePred :
          afterIncrement regs.basePred = base - 1 := by
        rw [← hnextBasePred]
        simp [afterTest, popTestOp, Basic.exec,
          regs.index_ne (first := 2) (second := 4) (by decide)]
      have hnextTest :
          afterTest regs.test =
            remaining * base + remainder - (base - 1) := by
        simp only [afterTest, popTestOp, Basic.exec,
          Function.update_self]
        rw [hafterIncrementWord, hafterIncrementBasePred]
      have hnextWordBound :
          remaining * base + remainder ≤ bound := by
        simp only [Nat.succ_mul] at hwordBound
        omega
      have hafterTestInvariant :
          ValuesWithin allowed bound afterTest := by
        apply valuesWithin_sub hafterIncrementInvariant
        rw [hafterIncrementWord, hafterIncrementBasePred]
        exact (Nat.sub_le _ _).trans hnextWordBound
      have hbody :
          InvariantRuns (ValuesWithin allowed bound)
            (popBody regs) store afterTest (1 + (1 + 1)) := by
        simpa [popBody, Cmd.seqList] using
          InvariantRuns.seq
            (InvariantRuns.basic
              (Basic.sub regs.word regs.word regs.base) store
              hstore hafterSubInvariant)
            (InvariantRuns.seq
              (InvariantRuns.basic
                (Basic.add regs.quotient regs.quotient regs.one)
                afterSub hafterSubInvariant
                hafterIncrementInvariant)
              (InvariantRuns.basic (popTestOp regs) afterIncrement
                hafterIncrementInvariant hafterTestInvariant))
      have hnextQuotientBound :
          (completed + 1) + remaining ≤ bound := by
        omega
      obtain ⟨final, loopSteps, hloop, hfinalWord,
          hfinalQuotient, hfinalTest, hfinalBase,
          hfinalBasePred, hfinalOne⟩ :=
        ih afterTest (completed + 1) hnextWord hnextQuotient
          hnextTest hnextBase hnextBasePred hnextOne
          hnextWordBound hnextQuotientBound hafterTestInvariant
      refine ⟨final, (1 + (1 + 1)) + loopSteps + 2,
        InvariantRuns.whileNonzero htestNonzero hbody hloop,
        hfinalWord, ?_, hfinalTest, hfinalBase, hfinalBasePred,
        hfinalOne⟩
      rw [hfinalQuotient]
      omega

theorem pop_invariantRuns_internal
    (regs : StackRegisters) (allowed : Finset ℕ) (bound : ℕ)
    (store : Store) (base word : ℕ)
    (hbase : 0 < base)
    (hword : store regs.word = word)
    (hbaseValue : store regs.base = base)
    (hbasePred : store regs.basePred = base - 1)
    (hone : store regs.one = 1)
    (hwordBound : word ≤ bound)
    (hstore : ValuesWithin allowed bound store) :
    ∃ final steps,
      InvariantRuns (ValuesWithin allowed bound)
        (pop regs) store final steps ∧
      final regs.word = PackedDigits.pop base word ∧
      final regs.quotient = 0 ∧
      final regs.test = 0 ∧
      final regs.base = base ∧
      final regs.basePred = base - 1 ∧
      final regs.one = 1 := by
  let quotientZero :=
    (Basic.imm regs.quotient 0).exec store
  let tested := (popTestOp regs).exec quotientZero
  have hquotientZeroInvariant :
      ValuesWithin allowed bound quotientZero :=
    valuesWithin_imm hstore (Nat.zero_le bound)
  have htestedWord : tested regs.word = word := by
    simp [tested, popTestOp, quotientZero, Basic.exec,
      regs.injective.eq_iff, hword]
  have htestedQuotient : tested regs.quotient = 0 := by
    simp [tested, popTestOp, quotientZero, Basic.exec,
      regs.injective.eq_iff]
  have htestedBase : tested regs.base = base := by
    simp [tested, popTestOp, quotientZero, Basic.exec,
      regs.injective.eq_iff, hbaseValue]
  have htestedBasePred : tested regs.basePred = base - 1 := by
    simp [tested, popTestOp, quotientZero, Basic.exec,
      regs.injective.eq_iff, hbasePred]
  have htestedOne : tested regs.one = 1 := by
    simp [tested, popTestOp, quotientZero, Basic.exec,
      regs.injective.eq_iff, hone]
  have htestedInvariant :
      ValuesWithin allowed bound tested := by
    apply valuesWithin_sub hquotientZeroInvariant
    have hquotientZeroWord : quotientZero regs.word = word := by
      simp [quotientZero, Basic.exec,
        regs.index_ne (first := 0) (second := 3) (by decide),
        hword]
    have hquotientZeroBasePred :
        quotientZero regs.basePred = base - 1 := by
      simp [quotientZero, Basic.exec,
        regs.index_ne (first := 2) (second := 3) (by decide),
        hbasePred]
    rw [hquotientZeroWord, hquotientZeroBasePred]
    exact (Nat.sub_le _ _).trans hwordBound
  have hdecompose :
      word / base * base + word % base = word := by
    simpa [Nat.mul_comm, Nat.add_comm] using
      (Nat.mod_add_div word base)
  have htestedDecompose :
      tested regs.word =
        word / base * base + word % base := by
    rw [htestedWord, hdecompose]
  have htestedTest :
      tested regs.test =
        word / base * base + word % base - (base - 1) := by
    simp only [tested, popTestOp, Basic.exec,
      Function.update_self]
    have hquotientZeroWord :
        quotientZero regs.word = word := by
      simp [quotientZero, Basic.exec,
        regs.index_ne (first := 0) (second := 3) (by decide),
        hword]
    have hquotientZeroBasePred :
        quotientZero regs.basePred = base - 1 := by
      simp [quotientZero, Basic.exec,
        regs.index_ne (first := 2) (second := 3) (by decide),
        hbasePred]
    rw [hquotientZeroWord, hquotientZeroBasePred, hdecompose]
  have hquotientBound : word / base ≤ bound := by
    exact (Nat.div_le_self word base).trans hwordBound
  obtain ⟨loopFinal, loopSteps, hloop, hloopWord,
      hloopQuotient, hloopTest, hloopBase, hloopBasePred,
      hloopOne⟩ :=
    popLoop_invariantRuns regs allowed bound tested base
      (word % base) (word / base) 0 hbase
      (Nat.mod_lt word hbase) htestedDecompose htestedQuotient
      htestedTest htestedBase htestedBasePred htestedOne
      (by simpa [hdecompose] using hwordBound)
      (by simpa using hquotientBound) htestedInvariant
  let clearedWord :=
    (Basic.imm regs.word 0).exec loopFinal
  let installed :=
    (Basic.add regs.word regs.word regs.quotient).exec clearedWord
  let final :=
    (Basic.imm regs.quotient 0).exec installed
  have hloopInvariant :
      ValuesWithin allowed bound loopFinal :=
    InvariantRuns.final hloop
  have hclearedInvariant :
      ValuesWithin allowed bound clearedWord :=
    valuesWithin_imm hloopInvariant (Nat.zero_le bound)
  have hclearedWord : clearedWord regs.word = 0 := by
    simp [clearedWord, Basic.exec]
  have hclearedQuotient :
      clearedWord regs.quotient = word / base := by
    simp [clearedWord, Basic.exec,
      regs.index_ne (first := 3) (second := 0) (by decide),
      hloopQuotient]
  have hinstalledInvariant :
      ValuesWithin allowed bound installed := by
    apply valuesWithin_add hclearedInvariant
    rw [hclearedWord, hclearedQuotient, Nat.zero_add]
    exact hquotientBound
  have hfinalInvariant :
      ValuesWithin allowed bound final :=
    valuesWithin_imm hinstalledInvariant (Nat.zero_le bound)
  have hrun :
      InvariantRuns (ValuesWithin allowed bound)
        (pop regs) store final
        (1 + (1 + (loopSteps + (1 + (1 + 1))))) := by
    simpa [pop, Cmd.seqList] using
      InvariantRuns.seq
        (InvariantRuns.basic (Basic.imm regs.quotient 0) store
          hstore hquotientZeroInvariant)
        (InvariantRuns.seq
          (InvariantRuns.basic (popTestOp regs) quotientZero
            hquotientZeroInvariant htestedInvariant)
          (InvariantRuns.seq hloop
            (InvariantRuns.seq
              (InvariantRuns.basic (Basic.imm regs.word 0) loopFinal
                hloopInvariant hclearedInvariant)
              (InvariantRuns.seq
                (InvariantRuns.basic
                  (Basic.add regs.word regs.word regs.quotient)
                  clearedWord hclearedInvariant hinstalledInvariant)
                (InvariantRuns.basic (Basic.imm regs.quotient 0)
                  installed hinstalledInvariant hfinalInvariant)))))
  refine ⟨final, 1 + (1 + (loopSteps + (1 + (1 + 1)))),
    hrun, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [final, installed, clearedWord, Basic.exec,
      regs.injective.eq_iff, hloopQuotient, PackedDigits.pop]
  · simp [final, Basic.exec]
  · simp [final, installed, clearedWord, Basic.exec,
      regs.injective.eq_iff, hloopTest]
  · simp [final, installed, clearedWord, Basic.exec,
      regs.injective.eq_iff, hloopBase]
  · simp [final, installed, clearedWord, Basic.exec,
      regs.injective.eq_iff, hloopBasePred]
  · simp [final, installed, clearedWord, Basic.exec,
      regs.injective.eq_iff, hloopOne]

private theorem cmdWritesWithin_mono
    {small large : Finset ℕ} {cmd : Cmd}
    (hsubset : small ⊆ large)
    (hwrites :
      RAM.Structured.Footprint.CmdWritesWithin small cmd) :
    RAM.Structured.Footprint.CmdWritesWithin large cmd := by
  induction cmd with
  | skip => trivial
  | basic op =>
      cases op <;>
        simp_all [RAM.Structured.Footprint.CmdWritesWithin,
          RAM.Structured.Footprint.BasicWritesWithin]
      all_goals exact hsubset hwrites
  | seq first second firstIH secondIH =>
      exact ⟨firstIH hwrites.1, secondIH hwrites.2⟩
  | ifZero test onZero onNonzero zeroIH nonzeroIH =>
      exact ⟨zeroIH hwrites.1, nonzeroIH hwrites.2⟩
  | whileNonzero test body bodyIH =>
      exact bodyIH hwrites

private theorem scaleBankFootprint_subset
    (regs : ResidueScaleRegisters) :
    regs.bank.footprint ⊆ regs.footprint := by
  intro address haddress
  obtain ⟨slot, _, rfl⟩ := Finset.mem_image.mp haddress
  exact regs.index_mem_footprint
    (ResidueScaleRegisters.bankSlot slot)

private theorem exec_eq_of_not_mem
    {cmd : Cmd} {initial final : Store}
    {steps cost space address : ℕ} {allowed : Finset ℕ}
    (hexec : Exec cmd initial final steps cost space)
    (hwrites :
      RAM.Structured.Footprint.CmdWritesWithin allowed cmd)
    (haddress : address ∉ allowed) :
    final address = initial address := by
  induction hexec with
  | skip => rfl
  | basic op store =>
      cases op <;>
        simp_all [RAM.Structured.Footprint.CmdWritesWithin,
          RAM.Structured.Footprint.BasicWritesWithin, Basic.exec]
      all_goals
        rw [Function.update_of_ne]
        intro heq
        apply haddress
        simpa [heq] using hwrites
  | seq hfirst hsecond firstIH secondIH =>
      rw [secondIH hwrites.2, firstIH hwrites.1]
  | ifZero htest hbranch branchIH =>
      exact branchIH hwrites.1
  | ifNonzero htest hbranch branchIH =>
      exact branchIH hwrites.2
  | whileZero => rfl
  | whileNonzero htest hbody hloop bodyIH loopIH =>
      rw [loopIH hwrites, bodyIH hwrites]

private theorem runs_eq_of_not_mem
    {cmd : Cmd} {initial final : Store}
    {address : ℕ} {allowed : Finset ℕ}
    (hruns : Runs cmd initial final)
    (hwrites :
      RAM.Structured.Footprint.CmdWritesWithin allowed cmd)
    (haddress : address ∉ allowed) :
    final address = initial address := by
  obtain ⟨steps, cost, space, hexec⟩ := hruns
  exact exec_eq_of_not_mem hexec hwrites haddress

private theorem residueExtra_not_mem_bankFootprint
    (regs : ResidueBankRegisters) (slot : Fin 16)
    (hslot : 12 ≤ slot.val) :
    regs.index slot ∉ regs.bank.footprint := by
  simp only [BankRegisters.footprint, Finset.mem_image,
    Finset.mem_univ, true_and]
  rintro ⟨bankSlot, heq⟩
  have hlogical := regs.injective heq
  have hval := congrArg Fin.val hlogical
  simp [ResidueBankRegisters.bankSlot] at hval
  omega

private theorem scaleRemaining_not_mem_bankFootprint
    (regs : ResidueScaleRegisters) :
    regs.remaining ∉ regs.bank.footprint := by
  simp only [ResidueBankRegisters.footprint, Finset.mem_image,
    Finset.mem_univ, true_and]
  rintro ⟨slot, heq⟩
  have hlogical := regs.injective heq
  have hval := congrArg Fin.val hlogical
  simp only [ResidueScaleRegisters.bankSlot] at hval
  omega

private theorem residueBankOp_runs
    (op : ResidueBankOp) (regs : ResidueBankRegisters)
    (store : Store) (modulus : ℕ) (hmodulus : 0 < modulus)
    (hmodulusValue : store regs.modulus = modulus)
    (hmodulusPred :
      store regs.modulusPred = modulus - 1) :
    Runs (op.command regs) store
      (RuntimeArithmetic.reduceResultStore regs.reduceRegisters
        (op.apply modulus (store regs.bank.result)
          (store regs.operand)) store) := by
  cases op with
  | add =>
      exact RuntimeArithmetic.addMod_runs regs.reduceRegisters
        regs.bank.result regs.operand store modulus hmodulus
        hmodulusValue hmodulusPred
  | mul =>
      exact RuntimeArithmetic.mulMod_runs regs.reduceRegisters
        regs.bank.result regs.operand store modulus hmodulus
        hmodulusValue hmodulusPred

private theorem residueBankOp_invariantRuns
    (op : ResidueBankOp) (regs : ResidueBankRegisters)
    (allowed : Finset ℕ) (bound : ℕ)
    (store : Store) (modulus current operand : ℕ)
    (hmodulus : 0 < modulus)
    (hcurrent :
      store regs.bank.result = current)
    (hoperand : store regs.operand = operand)
    (hmodulusValue : store regs.modulus = modulus)
    (hmodulusPred :
      store regs.modulusPred = modulus - 1)
    (hrawBound :
      op.rawApply current operand ≤ bound)
    (hstore : ValuesWithin allowed bound store) :
    ∃ steps,
      InvariantRuns (ValuesWithin allowed bound)
        (op.command regs) store
        (RuntimeArithmetic.reduceResultStore regs.reduceRegisters
          (op.apply modulus current operand) store)
        steps := by
  change store (regs.index 10) = current at hcurrent
  change store (regs.index 14) = operand at hoperand
  cases op with
  | add =>
      simpa [ResidueBankOp.command, ResidueBankOp.rawApply,
        ResidueBankOp.apply, hcurrent, hoperand] using
        addMod_invariantRuns_internal regs.reduceRegisters allowed
          bound regs.bank.result regs.operand store modulus
          hmodulus hmodulusValue hmodulusPred
          (by simpa [hcurrent, hoperand] using hrawBound) hstore
  | mul =>
      simpa [ResidueBankOp.command, ResidueBankOp.rawApply,
        ResidueBankOp.apply, hcurrent, hoperand] using
        mulMod_invariantRuns_internal regs.reduceRegisters allowed
          bound regs.bank.result regs.operand store modulus
          hmodulus hmodulusValue hmodulusPred
          (by simpa [hcurrent, hoperand] using hrawBound) hstore

private theorem popLoop_runs
    (regs : StackRegisters) (store : Store)
    (base remainder remaining completed : ℕ)
    (hbase : 0 < base) (hremainder : remainder < base)
    (hword :
      store regs.word = remaining * base + remainder)
    (hquotient : store regs.quotient = completed)
    (htest :
      store regs.test =
        remaining * base + remainder - (base - 1))
    (hbaseValue : store regs.base = base)
    (hbasePred : store regs.basePred = base - 1)
    (hone : store regs.one = 1) :
    ∃ final,
      Runs (.whileNonzero regs.test (popBody regs)) store final ∧
      final regs.word = remainder ∧
      final regs.quotient = completed + remaining ∧
      final regs.test = 0 ∧
      final regs.base = base ∧
      final regs.basePred = base - 1 ∧
      final regs.one = 1 := by
  induction remaining generalizing store completed with
  | zero =>
      have htestZero : store regs.test = 0 := by
        rw [htest]
        omega
      exact ⟨store, Runs.whileZero htestZero, by simpa using hword,
        by simpa using hquotient, htestZero, hbaseValue, hbasePred,
        hone⟩
  | succ remaining ih =>
      have htestNonzero : store regs.test ≠ 0 := by
        rw [htest]
        simp only [Nat.succ_mul]
        omega
      let afterSub :=
        (Basic.sub regs.word regs.word regs.base).exec store
      let afterIncrement :=
        (Basic.add regs.quotient regs.quotient regs.one).exec afterSub
      let afterTest := (popTestOp regs).exec afterIncrement
      have hbody : Runs (popBody regs) store afterTest := by
        exact Runs.seq (Runs.basic _ _)
          (Runs.seq (Runs.basic _ _) (Runs.basic _ _))
      have hnextWord :
          afterTest regs.word = remaining * base + remainder := by
        simp only [afterTest, popTestOp, Basic.exec]
        rw [Function.update_of_ne
          (regs.index_ne (first := 0) (second := 4) (by decide))]
        simp only [afterIncrement, Basic.exec]
        rw [Function.update_of_ne
          (regs.index_ne (first := 0) (second := 3) (by decide))]
        simp only [afterSub, Basic.exec, Function.update_self]
        rw [hword, hbaseValue]
        simp only [Nat.succ_mul]
        omega
      have hnextQuotient :
          afterTest regs.quotient = completed + 1 := by
        simp only [afterTest, popTestOp, Basic.exec]
        rw [Function.update_of_ne
          (regs.index_ne (first := 3) (second := 4) (by decide))]
        simp only [afterIncrement, Basic.exec, Function.update_self]
        have hafterSubQuotient :
            afterSub regs.quotient = completed := by
          simp [afterSub, Basic.exec,
            regs.index_ne (first := 3) (second := 0) (by decide),
            hquotient]
        have hafterSubOne : afterSub regs.one = 1 := by
          simp [afterSub, Basic.exec,
            regs.index_ne (first := 5) (second := 0) (by decide),
            hone]
        rw [hafterSubQuotient, hafterSubOne]
      have hnextBase : afterTest regs.base = base := by
        simp [afterTest, popTestOp, afterIncrement, afterSub, Basic.exec,
          regs.injective.eq_iff, hbaseValue]
      have hnextBasePred :
          afterTest regs.basePred = base - 1 := by
        simp [afterTest, popTestOp, afterIncrement, afterSub, Basic.exec,
          regs.injective.eq_iff, hbasePred]
      have hnextOne : afterTest regs.one = 1 := by
        simp [afterTest, popTestOp, afterIncrement, afterSub, Basic.exec,
          regs.injective.eq_iff, hone]
      have hafterIncrementWord :
          afterIncrement regs.word =
            remaining * base + remainder := by
        rw [← hnextWord]
        simp [afterTest, popTestOp, Basic.exec,
          regs.index_ne (first := 0) (second := 4) (by decide)]
      have hafterIncrementBasePred :
          afterIncrement regs.basePred = base - 1 := by
        rw [← hnextBasePred]
        simp [afterTest, popTestOp, Basic.exec,
          regs.index_ne (first := 2) (second := 4) (by decide)]
      have hnextTest :
          afterTest regs.test =
            remaining * base + remainder - (base - 1) := by
        simp only [afterTest, popTestOp, Basic.exec,
          Function.update_self]
        rw [hafterIncrementWord, hafterIncrementBasePred]
      obtain ⟨final, hloop, hfinalWord, hfinalQuotient,
          hfinalTest, hfinalBase, hfinalBasePred, hfinalOne⟩ :=
        ih afterTest (completed + 1) hnextWord hnextQuotient
          hnextTest hnextBase hnextBasePred hnextOne
      refine ⟨final, Runs.whileNonzero htestNonzero hbody hloop,
        hfinalWord, ?_, hfinalTest, hfinalBase, hfinalBasePred,
        hfinalOne⟩
      rw [hfinalQuotient]
      omega

theorem pop_runs_internal
    (regs : StackRegisters) (store : Store)
    (base word : ℕ) (hbase : 0 < base)
    (hword : store regs.word = word)
    (hbaseValue : store regs.base = base)
    (hbasePred : store regs.basePred = base - 1)
    (hone : store regs.one = 1) :
    ∃ final,
      Runs (pop regs) store final ∧
      final regs.word = PackedDigits.pop base word ∧
      final regs.quotient = 0 ∧
      final regs.test = 0 ∧
      final regs.base = base ∧
      final regs.basePred = base - 1 ∧
      final regs.one = 1 := by
  let quotientZero :=
    (Basic.imm regs.quotient 0).exec store
  let tested := (popTestOp regs).exec quotientZero
  have htestedWord : tested regs.word = word := by
    simp [tested, popTestOp, quotientZero, Basic.exec,
      regs.injective.eq_iff, hword]
  have htestedQuotient : tested regs.quotient = 0 := by
    simp [tested, popTestOp, quotientZero, Basic.exec,
      regs.injective.eq_iff]
  have htestedBase : tested regs.base = base := by
    simp [tested, popTestOp, quotientZero, Basic.exec,
      regs.injective.eq_iff, hbaseValue]
  have htestedBasePred : tested regs.basePred = base - 1 := by
    simp [tested, popTestOp, quotientZero, Basic.exec,
      regs.injective.eq_iff, hbasePred]
  have htestedOne : tested regs.one = 1 := by
    simp [tested, popTestOp, quotientZero, Basic.exec,
      regs.injective.eq_iff, hone]
  have hdecompose :
      word / base * base + word % base = word := by
    simpa [Nat.mul_comm, Nat.add_comm] using
      (Nat.mod_add_div word base)
  have htestedDecompose :
      tested regs.word =
        word / base * base + word % base := by
    rw [htestedWord, hdecompose]
  have htestedTest :
      tested regs.test =
        word / base * base + word % base - (base - 1) := by
    simp only [tested, popTestOp, Basic.exec,
      Function.update_self]
    have hquotientZeroWord :
        quotientZero regs.word = word := by
      simp [quotientZero, Basic.exec,
        regs.index_ne (first := 0) (second := 3) (by decide),
        hword]
    have hquotientZeroBasePred :
        quotientZero regs.basePred = base - 1 := by
      simp [quotientZero, Basic.exec,
        regs.index_ne (first := 2) (second := 3) (by decide),
        hbasePred]
    rw [hquotientZeroWord, hquotientZeroBasePred, hdecompose]
  obtain ⟨loopFinal, hloop, hloopWord, hloopQuotient,
      hloopTest, hloopBase, hloopBasePred, hloopOne⟩ :=
    popLoop_runs regs tested base (word % base) (word / base) 0
      hbase (Nat.mod_lt word hbase) htestedDecompose
      htestedQuotient htestedTest htestedBase htestedBasePred
      htestedOne
  let clearedWord :=
    (Basic.imm regs.word 0).exec loopFinal
  let installed :=
    (Basic.add regs.word regs.word regs.quotient).exec clearedWord
  let final :=
    (Basic.imm regs.quotient 0).exec installed
  have hrun : Runs (pop regs) store final := by
    simpa [pop, Cmd.seqList] using
      Runs.seq (Runs.basic (Basic.imm regs.quotient 0) store)
        (Runs.seq (Runs.basic (popTestOp regs) quotientZero)
          (Runs.seq hloop
            (Runs.seq (Runs.basic (Basic.imm regs.word 0) loopFinal)
              (Runs.seq
                (Runs.basic
                  (Basic.add regs.word regs.word regs.quotient)
                  clearedWord)
                (Runs.basic (Basic.imm regs.quotient 0)
                  installed)))))
  refine ⟨final, hrun, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [final, installed, clearedWord, Basic.exec,
      regs.injective.eq_iff, hloopQuotient, PackedDigits.pop]
  · simp [final, Basic.exec]
  · simp [final, installed, clearedWord, Basic.exec,
      regs.injective.eq_iff, hloopTest]
  · simp [final, installed, clearedWord, Basic.exec,
      regs.injective.eq_iff, hloopBase]
  · simp [final, installed, clearedWord, Basic.exec,
      regs.injective.eq_iff, hloopBasePred]
  · simp [final, installed, clearedWord, Basic.exec,
      regs.injective.eq_iff, hloopOne]

theorem peek_runs_internal
    (regs : StackRegisters) (store : Store)
    (base word : ℕ) (hbase : 0 < base)
    (hword : store regs.word = word)
    (hbaseValue : store regs.base = base)
    (hbasePred : store regs.basePred = base - 1) :
    ∃ final,
      Runs (peek regs) store final ∧
      final regs.word = word ∧
      final regs.value = PackedDigits.digit base word 0 ∧
      final regs.test = 0 ∧
      final regs.base = base ∧
      final regs.basePred = base - 1 := by
  let cleared :=
    (Basic.imm regs.value 0).exec store
  let copied :=
    (Basic.add regs.value regs.word regs.value).exec cleared
  have hcopiedValue : copied regs.value = word := by
    have hclearedWord : cleared regs.word = word := by
      simp [cleared, Basic.exec,
        regs.index_ne (first := 0) (second := 6) (by decide),
        hword]
    have hclearedValue : cleared regs.value = 0 := by
      simp [cleared, Basic.exec]
    simp [copied, Basic.exec, hclearedWord, hclearedValue]
  have hcopiedBase : copied regs.base = base := by
    simp [copied, cleared, Basic.exec, regs.injective.eq_iff,
      hbaseValue]
  have hcopiedBasePred : copied regs.basePred = base - 1 := by
    simp [copied, cleared, Basic.exec, regs.injective.eq_iff,
      hbasePred]
  let final :=
    RuntimeArithmetic.reduceResultStore regs.reduceRegisters
      (word % base) copied
  have hreduce : Runs
      (RuntimeArithmetic.reduce regs.reduceRegisters)
      copied final := by
    exact RuntimeArithmetic.reduce_runs regs.reduceRegisters copied
      base word hbase hcopiedValue hcopiedBase hcopiedBasePred
  have hrun : Runs (peek regs) store final := by
    simpa [peek, Cmd.seqList] using
      Runs.seq (Runs.basic (Basic.imm regs.value 0) store)
        (Runs.seq
          (Runs.basic
            (Basic.add regs.value regs.word regs.value) cleared)
          hreduce)
  refine ⟨final, hrun, ?_, ?_, ?_, ?_, ?_⟩
  · simp [final, RuntimeArithmetic.reduceResultStore,
      StackRegisters.reduceRegisters, copied, cleared, Basic.exec,
      regs.injective.eq_iff, hword]
  · simp [final, RuntimeArithmetic.reduceResultStore,
      StackRegisters.reduceRegisters, PackedDigits.digit,
      regs.index_ne (first := 6) (second := 4) (by decide)]
  · simp [final, RuntimeArithmetic.reduceResultStore,
      StackRegisters.reduceRegisters]
  · simp [final, RuntimeArithmetic.reduceResultStore,
      StackRegisters.reduceRegisters, copied, cleared, Basic.exec,
      regs.injective.eq_iff, hbaseValue]
  · simp [final, RuntimeArithmetic.reduceResultStore,
      StackRegisters.reduceRegisters, copied, cleared, Basic.exec,
      regs.injective.eq_iff, hbasePred]

theorem push_runs_internal
    (regs : StackRegisters) (store : Store)
    (base word value : ℕ)
    (hword : store regs.word = word)
    (hbaseValue : store regs.base = base)
    (hvalue : store regs.value = value) :
    ∃ final,
      Runs (push regs) store final ∧
      final regs.word = PackedDigits.push base value word ∧
      final regs.quotient = 0 ∧
      final regs.base = base ∧
      final regs.value = value := by
  let afterMul :=
    (Basic.mul regs.quotient regs.base regs.word).exec store
  let afterAdd :=
    (Basic.add regs.word regs.value regs.quotient).exec afterMul
  let final :=
    (Basic.imm regs.quotient 0).exec afterAdd
  have hafterMulProduct :
      afterMul regs.quotient = base * word := by
    simp [afterMul, Basic.exec, hbaseValue, hword]
  have hafterMulValue : afterMul regs.value = value := by
    simp [afterMul, Basic.exec,
      regs.index_ne (first := 6) (second := 3) (by decide),
      hvalue]
  have hafterAddWord :
      afterAdd regs.word = value + base * word := by
    simp only [afterAdd, Basic.exec, Function.update_self]
    rw [hafterMulValue, hafterMulProduct]
  have hrun : Runs (push regs) store final := by
    simpa [push, Cmd.seqList] using
      Runs.seq
        (Runs.basic
          (Basic.mul regs.quotient regs.base regs.word) store)
        (Runs.seq
          (Runs.basic
            (Basic.add regs.word regs.value regs.quotient) afterMul)
          (Runs.basic (Basic.imm regs.quotient 0) afterAdd))
  refine ⟨final, hrun, ?_, ?_, ?_, ?_⟩
  · simp [final, Basic.exec,
      regs.index_ne (first := 0) (second := 3) (by decide),
      hafterAddWord, PackedDigits.push]
  · simp [final, Basic.exec]
  · simp [final, afterAdd, afterMul, Basic.exec,
      regs.injective.eq_iff, hbaseValue]
  · simp [final, afterAdd, afterMul, Basic.exec,
      regs.injective.eq_iff, hvalue]

theorem pop_noStore_internal (regs : StackRegisters) :
    cmdNoStore (pop regs) := by
  simp [pop, popBody, popTestOp, Cmd.seqList, cmdNoStore,
    basicNoStore]

theorem peek_noStore_internal (regs : StackRegisters) :
    cmdNoStore (peek regs) := by
  simp [peek, RuntimeArithmetic.reduce, RuntimeArithmetic.reduceBody,
    RuntimeArithmetic.reduceTestOp, Cmd.seqList, cmdNoStore,
    basicNoStore]

theorem push_noStore_internal (regs : StackRegisters) :
    cmdNoStore (push regs) := by
  simp [push, Cmd.seqList, cmdNoStore, basicNoStore]

theorem pop_writesWithin_internal (regs : StackRegisters) :
    RegisterStore.DenseOverlay.FixedRegisters.Footprint.ProgramWritesWithin
      (Cmd.compile (pop regs)) regs.footprint := by
  apply RAM.Structured.Footprint.programWritesWithin_compile
  simp [pop, popBody, popTestOp, Cmd.seqList,
    RAM.Structured.Footprint.CmdWritesWithin,
    RAM.Structured.Footprint.BasicWritesWithin]

theorem peek_writesWithin_internal (regs : StackRegisters) :
    RegisterStore.DenseOverlay.FixedRegisters.Footprint.ProgramWritesWithin
      (Cmd.compile (peek regs)) regs.footprint := by
  apply RAM.Structured.Footprint.programWritesWithin_compile
  simp [peek, RuntimeArithmetic.reduce,
    RuntimeArithmetic.reduceBody, RuntimeArithmetic.reduceTestOp,
    StackRegisters.reduceRegisters, Cmd.seqList,
    RAM.Structured.Footprint.CmdWritesWithin,
    RAM.Structured.Footprint.BasicWritesWithin]

theorem push_writesWithin_internal (regs : StackRegisters) :
    RegisterStore.DenseOverlay.FixedRegisters.Footprint.ProgramWritesWithin
      (Cmd.compile (push regs)) regs.footprint := by
  apply RAM.Structured.Footprint.programWritesWithin_compile
  simp [push, Cmd.seqList,
    RAM.Structured.Footprint.CmdWritesWithin,
    RAM.Structured.Footprint.BasicWritesWithin]

private theorem peek_smallFootprint (regs : StackRegisters) :
    RAM.Structured.Footprint.CmdWritesWithin
      {regs.value, regs.test} (peek regs) := by
  simp [peek, RuntimeArithmetic.reduce,
    RuntimeArithmetic.reduceBody, RuntimeArithmetic.reduceTestOp,
    StackRegisters.reduceRegisters, Cmd.seqList,
    RAM.Structured.Footprint.CmdWritesWithin,
    RAM.Structured.Footprint.BasicWritesWithin]

private theorem pop_smallFootprint (regs : StackRegisters) :
    RAM.Structured.Footprint.CmdWritesWithin
      {regs.word, regs.quotient, regs.test} (pop regs) := by
  simp [pop, popBody, popTestOp, Cmd.seqList,
    RAM.Structured.Footprint.CmdWritesWithin,
    RAM.Structured.Footprint.BasicWritesWithin]

private theorem push_smallFootprint (regs : StackRegisters) :
    RAM.Structured.Footprint.CmdWritesWithin
      {regs.word, regs.quotient} (push regs) := by
  simp [push, Cmd.seqList,
    RAM.Structured.Footprint.CmdWritesWithin,
    RAM.Structured.Footprint.BasicWritesWithin]

private theorem bankForward_smallFootprint (regs : BankRegisters) :
    RAM.Structured.Footprint.CmdWritesWithin
      {regs.word, regs.buffer, regs.quotient, regs.test, regs.value,
        regs.indexCount, regs.completed}
      (bankForward regs) := by
  simp [bankForward, bankForwardBody, peek, pop, popBody, popTestOp,
    push, RuntimeArithmetic.reduce, RuntimeArithmetic.reduceBody,
    RuntimeArithmetic.reduceTestOp, StackRegisters.reduceRegisters,
    Cmd.seqList, regs.injective.eq_iff,
    RAM.Structured.Footprint.CmdWritesWithin,
    RAM.Structured.Footprint.BasicWritesWithin]

private theorem bankRestore_smallFootprint (regs : BankRegisters) :
    RAM.Structured.Footprint.CmdWritesWithin
      {regs.word, regs.buffer, regs.quotient, regs.test, regs.value,
        regs.completed}
      (bankRestore regs) := by
  simp [bankRestore, bankRestoreBody, peek, pop, popBody, popTestOp,
    push, RuntimeArithmetic.reduce, RuntimeArithmetic.reduceBody,
    RuntimeArithmetic.reduceTestOp, StackRegisters.reduceRegisters,
    Cmd.seqList, regs.injective.eq_iff,
    RAM.Structured.Footprint.CmdWritesWithin,
    RAM.Structured.Footprint.BasicWritesWithin]

private structure BankState (regs : BankRegisters)
    (base word buffer index completed : ℕ) (store : Store) : Prop where
  word_eq : store regs.word = word
  buffer_eq : store regs.buffer = buffer
  base_eq : store regs.base = base
  basePred_eq : store regs.basePred = base - 1
  one_eq : store regs.one = 1
  index_eq : store regs.indexCount = index
  completed_eq : store regs.completed = completed

private theorem bankForwardBody_invariantRuns
    (regs : BankRegisters) (allowed : Finset ℕ) (bound : ℕ)
    (store : Store)
    (base word buffer index completed : ℕ)
    (hbase : 0 < base)
    (hinv :
      BankState regs base word buffer (index + 1) completed store)
    (hwordBound : word ≤ bound)
    (hbufferProductBound : base * buffer ≤ bound)
    (hbufferPushBound :
      PackedDigits.digit base word 0 + base * buffer ≤ bound)
    (hindexBound : index ≤ bound)
    (hcompletedSuccBound : completed + 1 ≤ bound)
    (hstore : ValuesWithin allowed bound store) :
    ∃ final steps,
      InvariantRuns (ValuesWithin allowed bound)
        (bankForwardBody regs) store final steps ∧
      BankState regs base
        (PackedDigits.pop base word)
        (PackedDigits.push base (PackedDigits.digit base word 0) buffer)
        index (completed + 1) final := by
  let afterPeek :=
    peekResultStore regs.mainStack
      (PackedDigits.digit base word 0) store
  obtain ⟨peekSteps, hpeek⟩ :=
    peek_invariantRuns_internal regs.mainStack allowed bound store
      base word hbase hinv.word_eq hinv.base_eq hinv.basePred_eq
      hwordBound hstore
  have hpeekRuns : Runs (peek regs.mainStack) store afterPeek :=
    InvariantRuns.toRuns hpeek
  have hpeekInvariant :
      ValuesWithin allowed bound afterPeek :=
    InvariantRuns.final hpeek
  obtain ⟨semanticPeek, hsemanticPeek, hsemanticWord,
      hsemanticValue, _, hsemanticBase, hsemanticBasePred⟩ :=
    peek_runs_internal regs.mainStack store base word hbase
      hinv.word_eq hinv.base_eq hinv.basePred_eq
  have hpeekEq : afterPeek = semanticPeek :=
    runs_final_unique hpeekRuns hsemanticPeek
  rw [← hpeekEq] at hsemanticWord hsemanticValue hsemanticBase hsemanticBasePred
  have hpeekWord : afterPeek regs.word = word := by
    simpa using hsemanticWord
  have hpeekValue :
      afterPeek regs.value = PackedDigits.digit base word 0 := by
    simpa using hsemanticValue
  have hpeekBase : afterPeek regs.base = base := by
    simpa using hsemanticBase
  have hpeekBasePred : afterPeek regs.basePred = base - 1 := by
    simpa using hsemanticBasePred
  have hpeekOne : afterPeek regs.one = 1 := by
    rw [runs_eq_of_not_mem hpeekRuns
      (peek_smallFootprint regs.mainStack)]
    · exact hinv.one_eq
    · simp [BankRegisters.mainStack, BankRegisters.mainMap,
        regs.injective.eq_iff]
  obtain ⟨afterPop, popSteps, hpop, hpopWord, _, _, hpopBase,
      hpopBasePred, hpopOne⟩ :=
    pop_invariantRuns_internal regs.mainStack allowed bound afterPeek
      base word hbase hpeekWord hpeekBase hpeekBasePred hpeekOne
      hwordBound hpeekInvariant
  have hpopRuns : Runs (pop regs.mainStack) afterPeek afterPop :=
    InvariantRuns.toRuns hpop
  have hpopInvariant :
      ValuesWithin allowed bound afterPop :=
    InvariantRuns.final hpop
  have hpopValue :
      afterPop regs.value = PackedDigits.digit base word 0 := by
    rw [runs_eq_of_not_mem hpopRuns
      (pop_smallFootprint regs.mainStack)]
    · exact hpeekValue
    · simp [BankRegisters.mainStack, BankRegisters.mainMap,
        regs.injective.eq_iff]
  have hpopBuffer : afterPop regs.buffer = buffer := by
    rw [runs_eq_of_not_mem hpopRuns
      (pop_smallFootprint regs.mainStack)]
    · simp [afterPeek, peekResultStore,
        BankRegisters.mainStack, BankRegisters.mainMap,
        regs.injective.eq_iff, hinv.buffer_eq]
    · simp [BankRegisters.mainStack, BankRegisters.mainMap,
        regs.injective.eq_iff]
  have hpopIndex :
      afterPop regs.indexCount = index + 1 := by
    rw [runs_eq_of_not_mem hpopRuns
      (pop_smallFootprint regs.mainStack)]
    · simp [afterPeek, peekResultStore,
        BankRegisters.mainStack, BankRegisters.mainMap,
        regs.injective.eq_iff, hinv.index_eq]
    · simp [BankRegisters.mainStack, BankRegisters.mainMap,
        regs.injective.eq_iff]
  have hpopCompleted :
      afterPop regs.completed = completed := by
    rw [runs_eq_of_not_mem hpopRuns
      (pop_smallFootprint regs.mainStack)]
    · simp [afterPeek, peekResultStore,
        BankRegisters.mainStack, BankRegisters.mainMap,
        regs.injective.eq_iff, hinv.completed_eq]
    · simp [BankRegisters.mainStack, BankRegisters.mainMap,
        regs.injective.eq_iff]
  let afterPush :=
    pushResultStore regs.bufferStack
      (PackedDigits.push base (PackedDigits.digit base word 0)
        buffer)
      afterPop
  have hpush :
      InvariantRuns (ValuesWithin allowed bound)
        (push regs.bufferStack) afterPop afterPush 3 := by
    exact push_invariantRuns_internal regs.bufferStack allowed bound
      afterPop base buffer (PackedDigits.digit base word 0)
      hpopBuffer hpopBase hpopValue hbufferProductBound
      hbufferPushBound hpopInvariant
  have hpushInvariant :
      ValuesWithin allowed bound afterPush :=
    InvariantRuns.final hpush
  have hpushRuns :
      Runs (push regs.bufferStack) afterPop afterPush :=
    InvariantRuns.toRuns hpush
  obtain ⟨semanticPush, hsemanticPush, hsemanticBuffer, _,
      hsemanticPushBase, _⟩ :=
    push_runs_internal regs.bufferStack afterPop base buffer
      (PackedDigits.digit base word 0)
      hpopBuffer hpopBase hpopValue
  have hpushEq : afterPush = semanticPush :=
    runs_final_unique hpushRuns hsemanticPush
  rw [← hpushEq] at hsemanticBuffer hsemanticPushBase
  have hpushBuffer :
      afterPush regs.buffer =
        PackedDigits.push base (PackedDigits.digit base word 0)
          buffer := by
    simpa using hsemanticBuffer
  have hpushWord :
      afterPush regs.word = PackedDigits.pop base word := by
    rw [runs_eq_of_not_mem hpushRuns
      (push_smallFootprint regs.bufferStack)]
    · simpa using hpopWord
    · simp [BankRegisters.bufferStack, BankRegisters.bufferMap,
        regs.injective.eq_iff]
  have hpushBase : afterPush regs.base = base := by
    simpa using hsemanticPushBase
  have hpushBasePred :
      afterPush regs.basePred = base - 1 := by
    rw [runs_eq_of_not_mem hpushRuns
      (push_smallFootprint regs.bufferStack)]
    · simpa using hpopBasePred
    · simp [BankRegisters.bufferStack, BankRegisters.bufferMap,
        regs.injective.eq_iff]
  have hpushOne : afterPush regs.one = 1 := by
    rw [runs_eq_of_not_mem hpushRuns
      (push_smallFootprint regs.bufferStack)]
    · simpa using hpopOne
    · simp [BankRegisters.bufferStack, BankRegisters.bufferMap,
        regs.injective.eq_iff]
  have hpushIndex :
      afterPush regs.indexCount = index + 1 := by
    rw [runs_eq_of_not_mem hpushRuns
      (push_smallFootprint regs.bufferStack)]
    · exact hpopIndex
    · simp [BankRegisters.bufferStack, BankRegisters.bufferMap,
        regs.injective.eq_iff]
  have hpushCompleted :
      afterPush regs.completed = completed := by
    rw [runs_eq_of_not_mem hpushRuns
      (push_smallFootprint regs.bufferStack)]
    · exact hpopCompleted
    · simp [BankRegisters.bufferStack, BankRegisters.bufferMap,
        regs.injective.eq_iff]
  let afterIndex :=
    (Basic.sub regs.indexCount regs.indexCount regs.one).exec afterPush
  let final :=
    (Basic.add regs.completed regs.completed regs.one).exec afterIndex
  have hafterIndexInvariant :
      ValuesWithin allowed bound afterIndex := by
    apply valuesWithin_sub hpushInvariant
    rw [hpushIndex, hpushOne]
    simpa using hindexBound
  have hafterIndexCompleted :
      afterIndex regs.completed = completed := by
    simp [afterIndex, Basic.exec, regs.injective.eq_iff,
      hpushCompleted]
  have hafterIndexOne : afterIndex regs.one = 1 := by
    simp [afterIndex, Basic.exec, regs.injective.eq_iff, hpushOne]
  have hfinalInvariant :
      ValuesWithin allowed bound final := by
    apply valuesWithin_add hafterIndexInvariant
    rw [hafterIndexCompleted, hafterIndexOne]
    exact hcompletedSuccBound
  have hrun :
      InvariantRuns (ValuesWithin allowed bound)
        (bankForwardBody regs) store final
        (peekSteps + (popSteps + (3 + (1 + 1)))) := by
    simpa [bankForwardBody, Cmd.seqList] using
      InvariantRuns.seq hpeek
        (InvariantRuns.seq hpop
          (InvariantRuns.seq hpush
            (InvariantRuns.seq
              (InvariantRuns.basic
                (Basic.sub regs.indexCount regs.indexCount regs.one)
                afterPush hpushInvariant hafterIndexInvariant)
              (InvariantRuns.basic
                (Basic.add regs.completed regs.completed regs.one)
                afterIndex hafterIndexInvariant hfinalInvariant))))
  refine ⟨final, peekSteps + (popSteps + (3 + (1 + 1))),
    hrun, ?_⟩
  constructor
  · simp [final, afterIndex, Basic.exec, regs.injective.eq_iff,
      hpushWord]
  · simp [final, afterIndex, Basic.exec, regs.injective.eq_iff,
      hpushBuffer]
  · simp [final, afterIndex, Basic.exec, regs.injective.eq_iff,
      hpushBase]
  · simp [final, afterIndex, Basic.exec, regs.injective.eq_iff,
      hpushBasePred]
  · simp [final, afterIndex, Basic.exec, regs.injective.eq_iff,
      hpushOne]
  · simp [final, afterIndex, Basic.exec, regs.injective.eq_iff,
      hpushIndex, hpushOne]
  · simp [final, afterIndex, Basic.exec, regs.injective.eq_iff,
      hpushCompleted, hpushOne]

private theorem bankForwardBody_runs
    (regs : BankRegisters) (store : Store)
    (base word buffer index completed : ℕ)
    (hbase : 0 < base)
    (hinv :
      BankState regs base word buffer (index + 1) completed store) :
    ∃ final,
      Runs (bankForwardBody regs) store final ∧
      BankState regs base
        (PackedDigits.pop base word)
        (PackedDigits.push base (PackedDigits.digit base word 0) buffer)
        index (completed + 1) final := by
  obtain ⟨afterPeek, hpeek, hpeekWord, hpeekValue, _,
      hpeekBase, hpeekBasePred⟩ :=
    peek_runs_internal regs.mainStack store base word hbase
      hinv.word_eq hinv.base_eq hinv.basePred_eq
  have hpeekBuffer : afterPeek regs.buffer = buffer := by
    rw [runs_eq_of_not_mem hpeek
      (peek_smallFootprint regs.mainStack)]
    · exact hinv.buffer_eq
    · simp [BankRegisters.mainStack, BankRegisters.mainMap,
        regs.injective.eq_iff]
  have hpeekIndex :
      afterPeek regs.indexCount = index + 1 := by
    rw [runs_eq_of_not_mem hpeek
      (peek_smallFootprint regs.mainStack)]
    · exact hinv.index_eq
    · simp [BankRegisters.mainStack, BankRegisters.mainMap,
        regs.injective.eq_iff]
  have hpeekCompleted :
      afterPeek regs.completed = completed := by
    rw [runs_eq_of_not_mem hpeek
      (peek_smallFootprint regs.mainStack)]
    · exact hinv.completed_eq
    · simp [BankRegisters.mainStack, BankRegisters.mainMap,
        regs.injective.eq_iff]
  have hpeekOne : afterPeek regs.one = 1 := by
    rw [runs_eq_of_not_mem hpeek
      (peek_smallFootprint regs.mainStack)]
    · exact hinv.one_eq
    · simp [BankRegisters.mainStack, BankRegisters.mainMap,
        regs.injective.eq_iff]
  obtain ⟨afterPop, hpop, hpopWord, _, _, hpopBase,
      hpopBasePred, hpopOne⟩ :=
    pop_runs_internal regs.mainStack afterPeek base word hbase
      hpeekWord hpeekBase hpeekBasePred hpeekOne
  have hpopValue :
      afterPop regs.value = PackedDigits.digit base word 0 := by
    rw [runs_eq_of_not_mem hpop
      (pop_smallFootprint regs.mainStack)]
    · exact hpeekValue
    · simp [BankRegisters.mainStack, BankRegisters.mainMap,
        regs.injective.eq_iff]
  have hpopBuffer : afterPop regs.buffer = buffer := by
    rw [runs_eq_of_not_mem hpop
      (pop_smallFootprint regs.mainStack)]
    · exact hpeekBuffer
    · simp [BankRegisters.mainStack, BankRegisters.mainMap,
        regs.injective.eq_iff]
  have hpopIndex :
      afterPop regs.indexCount = index + 1 := by
    rw [runs_eq_of_not_mem hpop
      (pop_smallFootprint regs.mainStack)]
    · exact hpeekIndex
    · simp [BankRegisters.mainStack, BankRegisters.mainMap,
        regs.injective.eq_iff]
  have hpopCompleted :
      afterPop regs.completed = completed := by
    rw [runs_eq_of_not_mem hpop
      (pop_smallFootprint regs.mainStack)]
    · exact hpeekCompleted
    · simp [BankRegisters.mainStack, BankRegisters.mainMap,
        regs.injective.eq_iff]
  obtain ⟨afterPush, hpush, hpushBuffer, _, hpushBase,
      hpushValue⟩ :=
    push_runs_internal regs.bufferStack afterPop base buffer
      (PackedDigits.digit base word 0)
      hpopBuffer hpopBase hpopValue
  have hpushBuffer' :
      afterPush regs.buffer =
        PackedDigits.push base (PackedDigits.digit base word 0) buffer := by
    simpa using hpushBuffer
  have hpushBase' : afterPush regs.base = base := by
    simpa using hpushBase
  have hpushWord :
      afterPush regs.word = PackedDigits.pop base word := by
    rw [runs_eq_of_not_mem hpush
      (push_smallFootprint regs.bufferStack)]
    · exact hpopWord
    · simp [BankRegisters.bufferStack, BankRegisters.bufferMap,
        regs.injective.eq_iff]
  have hpushBasePred :
      afterPush regs.basePred = base - 1 := by
    rw [runs_eq_of_not_mem hpush
      (push_smallFootprint regs.bufferStack)]
    · exact hpopBasePred
    · simp [BankRegisters.bufferStack, BankRegisters.bufferMap,
        regs.injective.eq_iff]
  have hpushOne : afterPush regs.one = 1 := by
    rw [runs_eq_of_not_mem hpush
      (push_smallFootprint regs.bufferStack)]
    · exact hpopOne
    · simp [BankRegisters.bufferStack, BankRegisters.bufferMap,
        regs.injective.eq_iff]
  have hpushIndex :
      afterPush regs.indexCount = index + 1 := by
    rw [runs_eq_of_not_mem hpush
      (push_smallFootprint regs.bufferStack)]
    · exact hpopIndex
    · simp [BankRegisters.bufferStack, BankRegisters.bufferMap,
        regs.injective.eq_iff]
  have hpushCompleted :
      afterPush regs.completed = completed := by
    rw [runs_eq_of_not_mem hpush
      (push_smallFootprint regs.bufferStack)]
    · exact hpopCompleted
    · simp [BankRegisters.bufferStack, BankRegisters.bufferMap,
        regs.injective.eq_iff]
  let afterIndex :=
    (Basic.sub regs.indexCount regs.indexCount regs.one).exec afterPush
  let final :=
    (Basic.add regs.completed regs.completed regs.one).exec afterIndex
  have hrun : Runs (bankForwardBody regs) store final := by
    simpa [bankForwardBody, Cmd.seqList] using
      Runs.seq hpeek
        (Runs.seq hpop
          (Runs.seq hpush
            (Runs.seq
              (Runs.basic
                (Basic.sub regs.indexCount regs.indexCount regs.one)
                afterPush)
              (Runs.basic
                (Basic.add regs.completed regs.completed regs.one)
                afterIndex))))
  refine ⟨final, hrun, ?_⟩
  constructor
  · simp [final, afterIndex, Basic.exec, regs.injective.eq_iff,
      hpushWord]
  · simp [final, afterIndex, Basic.exec, regs.injective.eq_iff,
      hpushBuffer']
  · simp [final, afterIndex, Basic.exec, regs.injective.eq_iff,
      hpushBase']
  · simp [final, afterIndex, Basic.exec, regs.injective.eq_iff,
      hpushBasePred]
  · simp [final, afterIndex, Basic.exec, regs.injective.eq_iff,
      hpushOne]
  · simp [final, afterIndex, Basic.exec, regs.injective.eq_iff,
      hpushIndex, hpushOne]
  · simp [final, afterIndex, Basic.exec, regs.injective.eq_iff,
      hpushCompleted, hpushOne]

theorem popN_eq_div_pow_internal (base count word : ℕ) :
    popN base count word = word / base ^ count := by
  induction count with
  | zero => simp [popN]
  | succ count ih =>
      rw [popN, ih, PackedDigits.pop,
        Nat.div_div_eq_div_mul, pow_succ]

theorem popN_lt_pow_internal
    {base word count index : ℕ}
    (hbase : 0 < base)
    (hword : word < base ^ count)
    (hindex : index ≤ count) :
    popN base index word < base ^ (count - index) := by
  rw [popN_eq_div_pow_internal,
    Nat.div_lt_iff_lt_mul (pow_pos hbase index)]
  calc
    word < base ^ count := hword
    _ = base ^ (count - index) * base ^ index := by
      rw [← pow_add, Nat.sub_add_cancel hindex]

theorem digit_popN_internal (base count word : ℕ) :
    PackedDigits.digit base (popN base count word) 0 =
      PackedDigits.digit base word count := by
  simp [PackedDigits.digit, popN_eq_div_pow_internal]

theorem digit_popN_at_internal
    (base count word digitIndex : ℕ) :
    PackedDigits.digit base (popN base count word) digitIndex =
      PackedDigits.digit base word (count + digitIndex) := by
  simp only [PackedDigits.digit, popN_eq_div_pow_internal]
  rw [Nat.div_div_eq_div_mul, ← pow_add]

theorem reversedPrefix_digit_internal
    {base word count : ℕ} (hbase : 0 < base) :
    PackedDigits.digit base
        (reversedPrefix base word (count + 1)) 0 =
      PackedDigits.digit base word count := by
  apply PackedDigits.digit_push_zero
  exact PackedDigits.digit_lt hbase

theorem reversedPrefix_pop_internal
    {base word count : ℕ} (hbase : 0 < base) :
    PackedDigits.pop base
        (reversedPrefix base word (count + 1)) =
      reversedPrefix base word count := by
  apply PackedDigits.pop_push hbase
  exact PackedDigits.digit_lt hbase

theorem reversedPrefix_succ_internal
    (base word count : ℕ) :
    reversedPrefix base word (count + 1) =
      reversedPrefix base (PackedDigits.pop base word) count +
        base ^ count * PackedDigits.digit base word 0 := by
  induction count with
  | zero => simp [reversedPrefix, PackedDigits.push]
  | succ count ih =>
      simp only [reversedPrefix]
      rw [PackedDigits.digit_pop]
      have ih' :
          PackedDigits.push base
              (PackedDigits.digit base word count)
              (reversedPrefix base word count) =
            reversedPrefix base (PackedDigits.pop base word) count +
              base ^ count * PackedDigits.digit base word 0 := by
        simpa only [reversedPrefix] using ih
      rw [ih', pow_succ]
      simp only [PackedDigits.push]
      ring

theorem popN_pop_internal (base word count : ℕ) :
    popN base count (PackedDigits.pop base word) =
      popN base (count + 1) word := by
  simp [popN_eq_div_pow_internal, PackedDigits.pop,
    Nat.div_div_eq_div_mul, pow_succ]
  rw [Nat.mul_comm]

theorem reversedPrefix_lt_pow_internal
    {base word : ℕ} (hbase : 0 < base) :
    ∀ count,
      reversedPrefix base word count < base ^ count := by
  intro count
  induction count with
  | zero => simp [reversedPrefix]
  | succ count ih =>
      apply PackedDigits.push_lt_pow ih
        (PackedDigits.digit_lt hbase)

theorem popN_reversedPrefix_internal
    {base word count : ℕ} (hbase : 0 < base) :
    popN base count (reversedPrefix base word count) = 0 := by
  rw [popN_eq_div_pow_internal]
  exact Nat.div_eq_of_lt (reversedPrefix_lt_pow_internal hbase count)

theorem restoreN_lt_pow_internal
    {base word buffer prefixCount suffixCount : ℕ}
    (hbase : 0 < base)
    (hword : word < base ^ suffixCount)
    (hbuffer : buffer < base ^ prefixCount) :
    restoreN base prefixCount word buffer <
      base ^ (suffixCount + prefixCount) := by
  induction prefixCount generalizing word buffer suffixCount with
  | zero =>
      simpa [restoreN] using hword
  | succ prefixCount ih =>
      simp only [restoreN]
      have hpush :
          PackedDigits.push base
              (PackedDigits.digit base buffer 0) word <
            base ^ (suffixCount + 1) :=
        PackedDigits.push_lt_pow hword
          (PackedDigits.digit_lt hbase)
      have hpop :
          PackedDigits.pop base buffer < base ^ prefixCount :=
        PackedDigits.pop_lt_pow hbase hbuffer
      have hrestored :=
        ih hpush hpop
      have hexponent :
          (suffixCount + 1) + prefixCount =
            suffixCount + (prefixCount + 1) := by
        omega
      rw [hexponent] at hrestored
      exact hrestored

theorem restoreN_digit_tail_internal
    {base : ℕ} (hbase : 0 < base) :
    ∀ (count word buffer tailIndex : ℕ),
      PackedDigits.digit base
          (restoreN base count word buffer)
          (count + tailIndex) =
        PackedDigits.digit base word tailIndex := by
  intro count
  induction count with
  | zero =>
      simp [restoreN]
  | succ count ih =>
      intro word buffer tailIndex
      simp only [restoreN]
      have htail :=
        ih
          (PackedDigits.push base
            (PackedDigits.digit base buffer 0) word)
          (PackedDigits.pop base buffer) (tailIndex + 1)
      have hshift :
          PackedDigits.digit base
              (PackedDigits.push base
                (PackedDigits.digit base buffer 0) word)
              (tailIndex + 1) =
            PackedDigits.digit base word tailIndex :=
        PackedDigits.digit_push_succ hbase
          (PackedDigits.digit_lt hbase) tailIndex
      rw [hshift] at htail
      have hindex :
          count + 1 + tailIndex =
            count + (tailIndex + 1) := by
        omega
      rw [hindex]
      exact htail

theorem restoreN_digit_prefix_internal
    {base : ℕ} (hbase : 0 < base) :
    ∀ (count word₁ word₂ buffer digitIndex : ℕ),
      digitIndex < count →
      PackedDigits.digit base
          (restoreN base count word₁ buffer) digitIndex =
        PackedDigits.digit base
          (restoreN base count word₂ buffer) digitIndex := by
  intro count
  induction count with
  | zero =>
      intro word₁ word₂ buffer digitIndex hindex
      omega
  | succ count ih =>
      intro word₁ word₂ buffer digitIndex hindex
      simp only [restoreN]
      by_cases hlt : digitIndex < count
      · exact ih _ _ _ _ hlt
      · have heq : digitIndex = count := by omega
        subst digitIndex
        have hfirst :=
          restoreN_digit_tail_internal hbase count
            (PackedDigits.push base
              (PackedDigits.digit base buffer 0) word₁)
            (PackedDigits.pop base buffer) 0
        have hsecond :=
          restoreN_digit_tail_internal hbase count
            (PackedDigits.push base
              (PackedDigits.digit base buffer 0) word₂)
            (PackedDigits.pop base buffer) 0
        rw [PackedDigits.digit_push_zero
          (PackedDigits.digit_lt hbase)] at hfirst hsecond
        simpa only [Nat.add_zero] using hfirst.trans hsecond.symm

theorem restoreN_popN_reversedPrefix_internal
    {base word : ℕ} (hbase : 0 < base) :
    ∀ count,
      restoreN base count
        (popN base count word)
        (reversedPrefix base word count) =
      word := by
  intro count
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [restoreN, popN]
      rw [reversedPrefix_digit_internal hbase,
        reversedPrefix_pop_internal hbase,
        ← digit_popN_internal base count word,
        PackedDigits.push_digit_pop]
      exact ih

theorem replaceAt_digit_eq_internal
    {base word index value : ℕ}
    (hbase : 0 < base) (hvalue : value < base) :
    PackedDigits.digit base
        (replaceAt base word index value) index =
      value := by
  rw [replaceAt]
  have htail :=
    restoreN_digit_tail_internal hbase index
      (PackedDigits.push base value
        (popN base (index + 1) word))
      (reversedPrefix base word index) 0
  simpa [PackedDigits.digit_push_zero hvalue] using htail

theorem replaceAt_digit_ne_internal
    {base word index value digitIndex : ℕ}
    (hbase : 0 < base) (hvalue : value < base)
    (hne : digitIndex ≠ index) :
    PackedDigits.digit base
        (replaceAt base word index value) digitIndex =
      PackedDigits.digit base word digitIndex := by
  by_cases hlt : digitIndex < index
  · rw [replaceAt]
    calc
      PackedDigits.digit base
          (restoreN base index
            (PackedDigits.push base value
              (popN base (index + 1) word))
            (reversedPrefix base word index)) digitIndex =
        PackedDigits.digit base
          (restoreN base index (popN base index word)
            (reversedPrefix base word index)) digitIndex :=
              restoreN_digit_prefix_internal
                hbase _ _ _ _ _ hlt
      _ = PackedDigits.digit base word digitIndex := by
        rw [restoreN_popN_reversedPrefix_internal hbase]
  · have hgt : index < digitIndex := by omega
    obtain ⟨tailIndex, htailIndex⟩ :
        ∃ tailIndex, digitIndex = index + (tailIndex + 1) := by
      refine ⟨digitIndex - index - 1, ?_⟩
      omega
    rw [htailIndex, replaceAt]
    rw [restoreN_digit_tail_internal hbase]
    rw [PackedDigits.digit_push_succ hbase hvalue]
    rw [digit_popN_at_internal]
    congr 1
    omega

theorem replaceAt_lt_pow_internal
    {base word count index value : ℕ}
    (hbase : 0 < base)
    (hword : word < base ^ count)
    (hindex : index < count)
    (hvalue : value < base) :
    replaceAt base word index value < base ^ count := by
  have hindexSucc : index + 1 ≤ count := by omega
  have htail :
      popN base (index + 1) word <
        base ^ (count - (index + 1)) :=
    popN_lt_pow_internal hbase hword hindexSucc
  have hpushed :
      PackedDigits.push base value
          (popN base (index + 1) word) <
        base ^ ((count - (index + 1)) + 1) :=
    PackedDigits.push_lt_pow htail hvalue
  have hexponent :
      (count - (index + 1)) + 1 = count - index := by
    omega
  have hpushed' :
      PackedDigits.push base value
          (popN base (index + 1) word) <
        base ^ (count - index) := by
    rw [hexponent] at hpushed
    exact hpushed
  have hprefix :
      reversedPrefix base word index < base ^ index :=
    reversedPrefix_lt_pow_internal hbase index
  have hrestored :=
    restoreN_lt_pow_internal hbase hpushed' hprefix
  simpa [replaceAt, Nat.sub_add_cancel (Nat.le_of_lt hindex)]
    using hrestored

private theorem bankForwardPrefixLoop_invariantRuns
    (regs : BankRegisters) (allowed : Finset ℕ) (bound : ℕ)
    (store : Store)
    (base original processed remaining tailCount : ℕ)
    (hbase : 0 < base)
    (hinv :
      BankState regs base
        (popN base processed original)
        (reversedPrefix base original processed)
        remaining processed store)
    (horiginal :
      original < base ^ (processed + remaining + tailCount))
    (hcapacity :
      base ^ (processed + remaining + tailCount) ≤ bound)
    (hcountBound : processed + remaining ≤ bound)
    (hstore : ValuesWithin allowed bound store) :
    ∃ final steps,
      InvariantRuns (ValuesWithin allowed bound)
        (bankForward regs) store final steps ∧
      BankState regs base
        (popN base (processed + remaining) original)
        (reversedPrefix base original (processed + remaining))
        0 (processed + remaining) final := by
  induction remaining generalizing store processed with
  | zero =>
      have hzero : store regs.indexCount = 0 := hinv.index_eq
      refine ⟨store, 1, InvariantRuns.whileZero hzero hstore, ?_⟩
      simpa using hinv
  | succ remaining ih =>
      have hactive : store regs.indexCount ≠ 0 := by
        rw [hinv.index_eq]
        omega
      have honeBase : 1 ≤ base := by omega
      have horiginalBound : original ≤ bound :=
        (Nat.le_of_lt horiginal).trans hcapacity
      have hwordBound :
          popN base processed original ≤ bound := by
        rw [popN_eq_div_pow_internal]
        exact (Nat.div_le_self original (base ^ processed)).trans
          horiginalBound
      have hnextPrefixLt :
          reversedPrefix base original (processed + 1) <
            base ^ (processed + 1) :=
        reversedPrefix_lt_pow_internal hbase (processed + 1)
      have hnextPrefixCapacity :
          base ^ (processed + 1) ≤
            base ^ (processed + (remaining + 1) + tailCount) :=
        Nat.pow_le_pow_right honeBase (by omega)
      have hpushEq :
          PackedDigits.digit base
                (popN base processed original) 0 +
              base * reversedPrefix base original processed =
            reversedPrefix base original (processed + 1) := by
        rw [digit_popN_internal]
        rfl
      have hpushBound :
          PackedDigits.digit base
                (popN base processed original) 0 +
              base * reversedPrefix base original processed ≤ bound := by
        rw [hpushEq]
        exact (Nat.le_of_lt hnextPrefixLt).trans
          (hnextPrefixCapacity.trans hcapacity)
      have hproductBound :
          base * reversedPrefix base original processed ≤ bound := by
        exact (Nat.le_add_left _ _).trans hpushBound
      have hindexBound : remaining ≤ bound := by
        omega
      have hcompletedSuccBound : processed + 1 ≤ bound := by
        omega
      obtain ⟨middle, bodySteps, hbody, hmiddle⟩ :=
        bankForwardBody_invariantRuns regs allowed bound store base
          (popN base processed original)
          (reversedPrefix base original processed)
          remaining processed hbase (by simpa using hinv)
          hwordBound hproductBound hpushBound hindexBound
          hcompletedSuccBound hstore
      have hmiddleInvariant :
          ValuesWithin allowed bound middle :=
        InvariantRuns.final hbody
      have hbufferEq :
          PackedDigits.push base
              (PackedDigits.digit base
                (popN base processed original) 0)
              (reversedPrefix base original processed) =
            reversedPrefix base original (processed + 1) := by
        simpa [PackedDigits.push] using hpushEq
      have hmiddle' :
          BankState regs base
            (popN base (processed + 1) original)
            (reversedPrefix base original (processed + 1))
            remaining (processed + 1) middle := by
        simpa [popN, hbufferEq] using hmiddle
      have hnextOriginal :
          original <
            base ^ ((processed + 1) + remaining + tailCount) := by
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          using horiginal
      have hnextCapacity :
          base ^ ((processed + 1) + remaining + tailCount) ≤
            bound := by
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          using hcapacity
      have hnextCountBound :
          (processed + 1) + remaining ≤ bound := by
        omega
      obtain ⟨final, loopSteps, hloop, hfinal⟩ :=
        ih middle (processed + 1) hmiddle' hnextOriginal
          hnextCapacity hnextCountBound hmiddleInvariant
      refine ⟨final, bodySteps + loopSteps + 2,
        InvariantRuns.whileNonzero hactive hbody hloop, ?_⟩
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using hfinal

private theorem bankForwardLoop_runs
    (regs : BankRegisters) (store : Store)
    (base word buffer remaining completed : ℕ)
    (hbase : 0 < base)
    (hinv :
      BankState regs base word buffer remaining completed store) :
    ∃ final,
      Runs (bankForward regs) store final ∧
      BankState regs base
        (popN base remaining word)
        (reversedPrefix base word remaining +
          base ^ remaining * buffer)
        0 (completed + remaining) final := by
  induction remaining generalizing store word buffer completed with
  | zero =>
      have hzero : store regs.indexCount = 0 := hinv.index_eq
      refine ⟨store, Runs.whileZero hzero, ?_⟩
      simpa [popN, reversedPrefix] using hinv
  | succ remaining ih =>
      have hactive : store regs.indexCount ≠ 0 := by
        rw [hinv.index_eq]
        omega
      obtain ⟨middle, hbody, hmiddle⟩ :=
        bankForwardBody_runs regs store base word buffer remaining
          completed hbase hinv
      obtain ⟨final, hloop, hfinal⟩ :=
        ih middle (PackedDigits.pop base word)
          (PackedDigits.push base
            (PackedDigits.digit base word 0) buffer)
          (completed + 1) hmiddle
      refine ⟨final,
        Runs.whileNonzero hactive hbody hloop, ?_⟩
      constructor
      · rw [hfinal.word_eq, popN_pop_internal]
      · rw [hfinal.buffer_eq,
          reversedPrefix_succ_internal]
        simp only [PackedDigits.push, pow_succ]
        ring
      · exact hfinal.base_eq
      · exact hfinal.basePred_eq
      · exact hfinal.one_eq
      · exact hfinal.index_eq
      · rw [hfinal.completed_eq]
        omega

private theorem bankRestoreBody_runs
    (regs : BankRegisters) (store : Store)
    (base word buffer index remaining : ℕ)
    (hbase : 0 < base)
    (hinv :
      BankState regs base word buffer index (remaining + 1) store) :
    ∃ final,
      Runs (bankRestoreBody regs) store final ∧
      BankState regs base
        (PackedDigits.push base
          (PackedDigits.digit base buffer 0) word)
        (PackedDigits.pop base buffer)
        index remaining final := by
  obtain ⟨afterPeek, hpeek, hpeekBuffer, hpeekValue, _,
      hpeekBase, hpeekBasePred⟩ :=
    peek_runs_internal regs.bufferStack store base buffer hbase
      hinv.buffer_eq hinv.base_eq hinv.basePred_eq
  have hpeekWord : afterPeek regs.word = word := by
    rw [runs_eq_of_not_mem hpeek
      (peek_smallFootprint regs.bufferStack)]
    · exact hinv.word_eq
    · simp [BankRegisters.bufferStack, BankRegisters.bufferMap,
        regs.injective.eq_iff]
  have hpeekIndex : afterPeek regs.indexCount = index := by
    rw [runs_eq_of_not_mem hpeek
      (peek_smallFootprint regs.bufferStack)]
    · exact hinv.index_eq
    · simp [BankRegisters.bufferStack, BankRegisters.bufferMap,
        regs.injective.eq_iff]
  have hpeekCompleted :
      afterPeek regs.completed = remaining + 1 := by
    rw [runs_eq_of_not_mem hpeek
      (peek_smallFootprint regs.bufferStack)]
    · exact hinv.completed_eq
    · simp [BankRegisters.bufferStack, BankRegisters.bufferMap,
        regs.injective.eq_iff]
  have hpeekOne : afterPeek regs.one = 1 := by
    rw [runs_eq_of_not_mem hpeek
      (peek_smallFootprint regs.bufferStack)]
    · exact hinv.one_eq
    · simp [BankRegisters.bufferStack, BankRegisters.bufferMap,
        regs.injective.eq_iff]
  obtain ⟨afterPop, hpop, hpopBuffer, _, _, hpopBase,
      hpopBasePred, hpopOne⟩ :=
    pop_runs_internal regs.bufferStack afterPeek base buffer hbase
      hpeekBuffer hpeekBase hpeekBasePred hpeekOne
  have hpopValue :
      afterPop regs.value = PackedDigits.digit base buffer 0 := by
    rw [runs_eq_of_not_mem hpop
      (pop_smallFootprint regs.bufferStack)]
    · exact hpeekValue
    · simp [BankRegisters.bufferStack, BankRegisters.bufferMap,
        regs.injective.eq_iff]
  have hpopWord : afterPop regs.word = word := by
    rw [runs_eq_of_not_mem hpop
      (pop_smallFootprint regs.bufferStack)]
    · exact hpeekWord
    · simp [BankRegisters.bufferStack, BankRegisters.bufferMap,
        regs.injective.eq_iff]
  have hpopIndex : afterPop regs.indexCount = index := by
    rw [runs_eq_of_not_mem hpop
      (pop_smallFootprint regs.bufferStack)]
    · exact hpeekIndex
    · simp [BankRegisters.bufferStack, BankRegisters.bufferMap,
        regs.injective.eq_iff]
  have hpopCompleted :
      afterPop regs.completed = remaining + 1 := by
    rw [runs_eq_of_not_mem hpop
      (pop_smallFootprint regs.bufferStack)]
    · exact hpeekCompleted
    · simp [BankRegisters.bufferStack, BankRegisters.bufferMap,
        regs.injective.eq_iff]
  obtain ⟨afterPush, hpush, hpushWord, _, hpushBase,
      hpushValue⟩ :=
    push_runs_internal regs.mainStack afterPop base word
      (PackedDigits.digit base buffer 0)
      hpopWord hpopBase hpopValue
  have hpushWord' :
      afterPush regs.word =
        PackedDigits.push base
          (PackedDigits.digit base buffer 0) word := by
    simpa using hpushWord
  have hpushBase' : afterPush regs.base = base := by
    simpa using hpushBase
  have hpushBuffer :
      afterPush regs.buffer = PackedDigits.pop base buffer := by
    rw [runs_eq_of_not_mem hpush
      (push_smallFootprint regs.mainStack)]
    · exact hpopBuffer
    · simp [BankRegisters.mainStack, BankRegisters.mainMap,
        regs.injective.eq_iff]
  have hpushBasePred :
      afterPush regs.basePred = base - 1 := by
    rw [runs_eq_of_not_mem hpush
      (push_smallFootprint regs.mainStack)]
    · exact hpopBasePred
    · simp [BankRegisters.mainStack, BankRegisters.mainMap,
        regs.injective.eq_iff]
  have hpushOne : afterPush regs.one = 1 := by
    rw [runs_eq_of_not_mem hpush
      (push_smallFootprint regs.mainStack)]
    · exact hpopOne
    · simp [BankRegisters.mainStack, BankRegisters.mainMap,
        regs.injective.eq_iff]
  have hpushIndex : afterPush regs.indexCount = index := by
    rw [runs_eq_of_not_mem hpush
      (push_smallFootprint regs.mainStack)]
    · exact hpopIndex
    · simp [BankRegisters.mainStack, BankRegisters.mainMap,
        regs.injective.eq_iff]
  have hpushCompleted :
      afterPush regs.completed = remaining + 1 := by
    rw [runs_eq_of_not_mem hpush
      (push_smallFootprint regs.mainStack)]
    · exact hpopCompleted
    · simp [BankRegisters.mainStack, BankRegisters.mainMap,
        regs.injective.eq_iff]
  let final :=
    (Basic.sub regs.completed regs.completed regs.one).exec afterPush
  have hrun : Runs (bankRestoreBody regs) store final := by
    simpa [bankRestoreBody, Cmd.seqList] using
      Runs.seq hpeek
        (Runs.seq hpop
          (Runs.seq hpush
            (Runs.basic
              (Basic.sub regs.completed regs.completed regs.one)
              afterPush)))
  refine ⟨final, hrun, ?_⟩
  constructor
  · simp [final, Basic.exec, regs.injective.eq_iff, hpushWord']
  · simp [final, Basic.exec, regs.injective.eq_iff, hpushBuffer]
  · simp [final, Basic.exec, regs.injective.eq_iff, hpushBase']
  · simp [final, Basic.exec, regs.injective.eq_iff, hpushBasePred]
  · simp [final, Basic.exec, regs.injective.eq_iff, hpushOne]
  · simp [final, Basic.exec, regs.injective.eq_iff, hpushIndex]
  · simp [final, Basic.exec, hpushCompleted, hpushOne]

private theorem bankRestoreBody_invariantRuns
    (regs : BankRegisters) (allowed : Finset ℕ) (bound : ℕ)
    (store : Store)
    (base word buffer index remaining : ℕ)
    (hbase : 0 < base)
    (hinv :
      BankState regs base word buffer index (remaining + 1) store)
    (hbufferBound : buffer ≤ bound)
    (hwordProductBound : base * word ≤ bound)
    (hwordPushBound :
      PackedDigits.digit base buffer 0 + base * word ≤ bound)
    (hremainingBound : remaining ≤ bound)
    (hstore : ValuesWithin allowed bound store) :
    ∃ final steps,
      InvariantRuns (ValuesWithin allowed bound)
        (bankRestoreBody regs) store final steps ∧
      BankState regs base
        (PackedDigits.push base
          (PackedDigits.digit base buffer 0) word)
        (PackedDigits.pop base buffer)
        index remaining final := by
  let afterPeek :=
    peekResultStore regs.bufferStack
      (PackedDigits.digit base buffer 0) store
  obtain ⟨peekSteps, hpeek⟩ :=
    peek_invariantRuns_internal regs.bufferStack allowed bound store
      base buffer hbase hinv.buffer_eq hinv.base_eq
      hinv.basePred_eq hbufferBound hstore
  have hpeekRuns :
      Runs (peek regs.bufferStack) store afterPeek :=
    InvariantRuns.toRuns hpeek
  have hpeekInvariant :
      ValuesWithin allowed bound afterPeek :=
    InvariantRuns.final hpeek
  obtain ⟨semanticPeek, hsemanticPeek, hsemanticBuffer,
      hsemanticValue, _, hsemanticBase, hsemanticBasePred⟩ :=
    peek_runs_internal regs.bufferStack store base buffer hbase
      hinv.buffer_eq hinv.base_eq hinv.basePred_eq
  have hpeekEq : afterPeek = semanticPeek :=
    runs_final_unique hpeekRuns hsemanticPeek
  rw [← hpeekEq] at hsemanticBuffer hsemanticValue hsemanticBase hsemanticBasePred
  have hpeekBuffer : afterPeek regs.buffer = buffer := by
    simpa using hsemanticBuffer
  have hpeekValue :
      afterPeek regs.value = PackedDigits.digit base buffer 0 := by
    simpa using hsemanticValue
  have hpeekBase : afterPeek regs.base = base := by
    simpa using hsemanticBase
  have hpeekBasePred : afterPeek regs.basePred = base - 1 := by
    simpa using hsemanticBasePred
  have hpeekWord : afterPeek regs.word = word := by
    rw [runs_eq_of_not_mem hpeekRuns
      (peek_smallFootprint regs.bufferStack)]
    · exact hinv.word_eq
    · simp [BankRegisters.bufferStack, BankRegisters.bufferMap,
        regs.injective.eq_iff]
  have hpeekIndex : afterPeek regs.indexCount = index := by
    rw [runs_eq_of_not_mem hpeekRuns
      (peek_smallFootprint regs.bufferStack)]
    · exact hinv.index_eq
    · simp [BankRegisters.bufferStack, BankRegisters.bufferMap,
        regs.injective.eq_iff]
  have hpeekCompleted :
      afterPeek regs.completed = remaining + 1 := by
    rw [runs_eq_of_not_mem hpeekRuns
      (peek_smallFootprint regs.bufferStack)]
    · exact hinv.completed_eq
    · simp [BankRegisters.bufferStack, BankRegisters.bufferMap,
        regs.injective.eq_iff]
  have hpeekOne : afterPeek regs.one = 1 := by
    rw [runs_eq_of_not_mem hpeekRuns
      (peek_smallFootprint regs.bufferStack)]
    · exact hinv.one_eq
    · simp [BankRegisters.bufferStack, BankRegisters.bufferMap,
        regs.injective.eq_iff]
  obtain ⟨afterPop, popSteps, hpop, hpopBuffer, _, _,
      hpopBase, hpopBasePred, hpopOne⟩ :=
    pop_invariantRuns_internal regs.bufferStack allowed bound
      afterPeek base buffer hbase hpeekBuffer hpeekBase
      hpeekBasePred hpeekOne hbufferBound hpeekInvariant
  have hpopRuns :
      Runs (pop regs.bufferStack) afterPeek afterPop :=
    InvariantRuns.toRuns hpop
  have hpopInvariant :
      ValuesWithin allowed bound afterPop :=
    InvariantRuns.final hpop
  have hpopValue :
      afterPop regs.value = PackedDigits.digit base buffer 0 := by
    rw [runs_eq_of_not_mem hpopRuns
      (pop_smallFootprint regs.bufferStack)]
    · exact hpeekValue
    · simp [BankRegisters.bufferStack, BankRegisters.bufferMap,
        regs.injective.eq_iff]
  have hpopWord : afterPop regs.word = word := by
    rw [runs_eq_of_not_mem hpopRuns
      (pop_smallFootprint regs.bufferStack)]
    · exact hpeekWord
    · simp [BankRegisters.bufferStack, BankRegisters.bufferMap,
        regs.injective.eq_iff]
  have hpopIndex : afterPop regs.indexCount = index := by
    rw [runs_eq_of_not_mem hpopRuns
      (pop_smallFootprint regs.bufferStack)]
    · exact hpeekIndex
    · simp [BankRegisters.bufferStack, BankRegisters.bufferMap,
        regs.injective.eq_iff]
  have hpopCompleted :
      afterPop regs.completed = remaining + 1 := by
    rw [runs_eq_of_not_mem hpopRuns
      (pop_smallFootprint regs.bufferStack)]
    · exact hpeekCompleted
    · simp [BankRegisters.bufferStack, BankRegisters.bufferMap,
        regs.injective.eq_iff]
  let afterPush :=
    pushResultStore regs.mainStack
      (PackedDigits.push base
        (PackedDigits.digit base buffer 0) word)
      afterPop
  have hpush :
      InvariantRuns (ValuesWithin allowed bound)
        (push regs.mainStack) afterPop afterPush 3 := by
    exact push_invariantRuns_internal regs.mainStack allowed bound
      afterPop base word (PackedDigits.digit base buffer 0)
      hpopWord hpopBase hpopValue hwordProductBound
      hwordPushBound hpopInvariant
  have hpushRuns :
      Runs (push regs.mainStack) afterPop afterPush :=
    InvariantRuns.toRuns hpush
  have hpushInvariant :
      ValuesWithin allowed bound afterPush :=
    InvariantRuns.final hpush
  obtain ⟨semanticPush, hsemanticPush, hsemanticWord, _,
      hsemanticPushBase, _⟩ :=
    push_runs_internal regs.mainStack afterPop base word
      (PackedDigits.digit base buffer 0)
      hpopWord hpopBase hpopValue
  have hpushEq : afterPush = semanticPush :=
    runs_final_unique hpushRuns hsemanticPush
  rw [← hpushEq] at hsemanticWord hsemanticPushBase
  have hpushWord :
      afterPush regs.word =
        PackedDigits.push base
          (PackedDigits.digit base buffer 0) word := by
    simpa using hsemanticWord
  have hpushBase : afterPush regs.base = base := by
    simpa using hsemanticPushBase
  have hpushBuffer :
      afterPush regs.buffer = PackedDigits.pop base buffer := by
    rw [runs_eq_of_not_mem hpushRuns
      (push_smallFootprint regs.mainStack)]
    · simpa using hpopBuffer
    · simp [BankRegisters.mainStack, BankRegisters.mainMap,
        regs.injective.eq_iff]
  have hpushBasePred :
      afterPush regs.basePred = base - 1 := by
    rw [runs_eq_of_not_mem hpushRuns
      (push_smallFootprint regs.mainStack)]
    · simpa using hpopBasePred
    · simp [BankRegisters.mainStack, BankRegisters.mainMap,
        regs.injective.eq_iff]
  have hpushOne : afterPush regs.one = 1 := by
    rw [runs_eq_of_not_mem hpushRuns
      (push_smallFootprint regs.mainStack)]
    · simpa using hpopOne
    · simp [BankRegisters.mainStack, BankRegisters.mainMap,
        regs.injective.eq_iff]
  have hpushIndex : afterPush regs.indexCount = index := by
    rw [runs_eq_of_not_mem hpushRuns
      (push_smallFootprint regs.mainStack)]
    · exact hpopIndex
    · simp [BankRegisters.mainStack, BankRegisters.mainMap,
        regs.injective.eq_iff]
  have hpushCompleted :
      afterPush regs.completed = remaining + 1 := by
    rw [runs_eq_of_not_mem hpushRuns
      (push_smallFootprint regs.mainStack)]
    · exact hpopCompleted
    · simp [BankRegisters.mainStack, BankRegisters.mainMap,
        regs.injective.eq_iff]
  let final :=
    (Basic.sub regs.completed regs.completed regs.one).exec afterPush
  have hfinalInvariant :
      ValuesWithin allowed bound final := by
    apply valuesWithin_sub hpushInvariant
    rw [hpushCompleted, hpushOne]
    simpa using hremainingBound
  have hrun :
      InvariantRuns (ValuesWithin allowed bound)
        (bankRestoreBody regs) store final
        (peekSteps + (popSteps + (3 + 1))) := by
    simpa [bankRestoreBody, Cmd.seqList] using
      InvariantRuns.seq hpeek
        (InvariantRuns.seq hpop
          (InvariantRuns.seq hpush
            (InvariantRuns.basic
              (Basic.sub regs.completed regs.completed regs.one)
              afterPush hpushInvariant hfinalInvariant)))
  refine ⟨final, peekSteps + (popSteps + (3 + 1)), hrun, ?_⟩
  constructor
  · simp [final, Basic.exec, regs.injective.eq_iff, hpushWord]
  · simp [final, Basic.exec, regs.injective.eq_iff, hpushBuffer]
  · simp [final, Basic.exec, regs.injective.eq_iff, hpushBase]
  · simp [final, Basic.exec, regs.injective.eq_iff, hpushBasePred]
  · simp [final, Basic.exec, regs.injective.eq_iff, hpushOne]
  · simp [final, Basic.exec, regs.injective.eq_iff, hpushIndex]
  · simp [final, Basic.exec, hpushCompleted, hpushOne]

private theorem bankRestoreLoop_invariantRuns
    (regs : BankRegisters) (allowed : Finset ℕ) (bound : ℕ)
    (store : Store)
    (base word buffer index remaining suffixCount : ℕ)
    (hbase : 0 < base)
    (hinv :
      BankState regs base word buffer index remaining store)
    (hword : word < base ^ suffixCount)
    (hbuffer : buffer < base ^ remaining)
    (hcapacity :
      base ^ (suffixCount + remaining) ≤ bound)
    (hremainingBound : remaining ≤ bound)
    (hstore : ValuesWithin allowed bound store) :
    ∃ final steps,
      InvariantRuns (ValuesWithin allowed bound)
        (bankRestore regs) store final steps ∧
      BankState regs base
        (restoreN base remaining word buffer)
        (popN base remaining buffer)
        index 0 final := by
  induction remaining generalizing store word buffer suffixCount with
  | zero =>
      have hzero : store regs.completed = 0 := hinv.completed_eq
      refine ⟨store, 1, InvariantRuns.whileZero hzero hstore, ?_⟩
      simpa [restoreN, popN] using hinv
  | succ remaining ih =>
      have hactive : store regs.completed ≠ 0 := by
        rw [hinv.completed_eq]
        omega
      have honeBase : 1 ≤ base := by omega
      have hbufferBound : buffer ≤ bound := by
        exact (Nat.le_of_lt hbuffer).trans
          ((Nat.pow_le_pow_right honeBase (by omega)).trans hcapacity)
      have hproductLt :
          base * word < base ^ (suffixCount + 1) := by
        calc
          base * word < base * base ^ suffixCount := by
            nlinarith
          _ = base ^ (suffixCount + 1) := by
            simp [pow_succ, Nat.mul_comm]
      have hnextCapacityLe :
          base ^ (suffixCount + 1) ≤
            base ^ (suffixCount + (remaining + 1)) :=
        Nat.pow_le_pow_right honeBase (by omega)
      have hproductBound : base * word ≤ bound :=
        (Nat.le_of_lt hproductLt).trans
          (hnextCapacityLe.trans hcapacity)
      have hpushLt :
          PackedDigits.push base
              (PackedDigits.digit base buffer 0) word <
            base ^ (suffixCount + 1) :=
        PackedDigits.push_lt_pow hword
          (PackedDigits.digit_lt hbase)
      have hpushBound :
          PackedDigits.digit base buffer 0 + base * word ≤ bound := by
        change
          PackedDigits.push base
              (PackedDigits.digit base buffer 0) word ≤ bound
        exact (Nat.le_of_lt hpushLt).trans
          (hnextCapacityLe.trans hcapacity)
      have hnextRemainingBound : remaining ≤ bound := by
        omega
      obtain ⟨middle, bodySteps, hbody, hmiddle⟩ :=
        bankRestoreBody_invariantRuns regs allowed bound store
          base word buffer index remaining hbase hinv
          hbufferBound hproductBound hpushBound
          hnextRemainingBound hstore
      have hmiddleInvariant :
          ValuesWithin allowed bound middle :=
        InvariantRuns.final hbody
      have hnextBuffer :
          PackedDigits.pop base buffer < base ^ remaining :=
        PackedDigits.pop_lt_pow hbase hbuffer
      have hnextCapacity :
          base ^ ((suffixCount + 1) + remaining) ≤ bound := by
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          using hcapacity
      obtain ⟨final, loopSteps, hloop, hfinal⟩ :=
        ih middle
          (PackedDigits.push base
            (PackedDigits.digit base buffer 0) word)
          (PackedDigits.pop base buffer) (suffixCount + 1)
          hmiddle hpushLt hnextBuffer hnextCapacity
          hnextRemainingBound hmiddleInvariant
      refine ⟨final, bodySteps + loopSteps + 2,
        InvariantRuns.whileNonzero hactive hbody hloop, ?_⟩
      simpa only [restoreN, popN_pop_internal] using hfinal

private theorem bankRestoreLoop_runs
    (regs : BankRegisters) (store : Store)
    (base word buffer index remaining : ℕ)
    (hbase : 0 < base)
    (hinv :
      BankState regs base word buffer index remaining store) :
    ∃ final,
      Runs (bankRestore regs) store final ∧
      BankState regs base
        (restoreN base remaining word buffer)
        (popN base remaining buffer)
        index 0 final := by
  induction remaining generalizing store word buffer with
  | zero =>
      have hzero : store regs.completed = 0 := hinv.completed_eq
      refine ⟨store, Runs.whileZero hzero, ?_⟩
      simpa [restoreN, popN] using hinv
  | succ remaining ih =>
      have hactive : store regs.completed ≠ 0 := by
        rw [hinv.completed_eq]
        omega
      obtain ⟨middle, hbody, hmiddle⟩ :=
        bankRestoreBody_runs regs store base word buffer index
          remaining hbase hinv
      obtain ⟨final, hloop, hfinal⟩ :=
        ih middle
          (PackedDigits.push base
            (PackedDigits.digit base buffer 0) word)
          (PackedDigits.pop base buffer) hmiddle
      refine ⟨final,
        Runs.whileNonzero hactive hbody hloop, ?_⟩
      simpa only [restoreN, popN_pop_internal] using hfinal

private theorem bankSeek_runs
    (regs : BankRegisters) (store : Store)
    (base word index : ℕ) (hbase : 0 < base)
    (hword : store regs.word = word)
    (hbaseValue : store regs.base = base)
    (hbasePred : store regs.basePred = base - 1)
    (hone : store regs.one = 1)
    (hindex : store regs.indexCount = index) :
    ∃ final,
      Runs (bankSeek regs) store final ∧
      BankState regs base
        (popN base index word)
        (reversedPrefix base word index)
        0 index final ∧
      final regs.result = PackedDigits.digit base word index ∧
      final regs.replacement = store regs.replacement := by
  let bufferZero := (Basic.imm regs.buffer 0).exec store
  let countersZero :=
    (Basic.imm regs.completed 0).exec bufferZero
  have hinitial :
      BankState regs base word 0 index 0 countersZero := by
    constructor <;>
      simp [countersZero, bufferZero, Basic.exec,
        regs.injective.eq_iff, hword, hbaseValue, hbasePred,
        hone, hindex]
  obtain ⟨afterForward, hforward, hforwardInv⟩ :=
    bankForwardLoop_runs regs countersZero base word 0 index 0
      hbase hinitial
  have hforwardInv' :
      BankState regs base
        (popN base index word)
        (reversedPrefix base word index)
        0 index afterForward := by
    simpa using hforwardInv
  have hforwardReplacement :
      afterForward regs.replacement =
        store regs.replacement := by
    rw [runs_eq_of_not_mem hforward
      (bankForward_smallFootprint regs)]
    · simp [countersZero, bufferZero, Basic.exec,
        regs.injective.eq_iff]
    · simp [regs.injective.eq_iff]
  obtain ⟨afterPeek, hpeek, hpeekWord, hpeekValue, _,
      hpeekBase, hpeekBasePred⟩ :=
    peek_runs_internal regs.mainStack afterForward base
      (popN base index word) hbase
      hforwardInv'.word_eq hforwardInv'.base_eq
      hforwardInv'.basePred_eq
  have hpeekWord' :
      afterPeek regs.word = popN base index word := by
    simpa using hpeekWord
  have hpeekValueRaw :
      afterPeek regs.value =
        PackedDigits.digit base (popN base index word) 0 := by
    simpa using hpeekValue
  have hpeekBase' : afterPeek regs.base = base := by
    simpa using hpeekBase
  have hpeekBasePred' :
      afterPeek regs.basePred = base - 1 := by
    simpa using hpeekBasePred
  have hpeekValue' :
      afterPeek regs.value =
        PackedDigits.digit base word index := by
    rw [hpeekValueRaw, digit_popN_internal]
  have hpeekBuffer :
      afterPeek regs.buffer =
        reversedPrefix base word index := by
    rw [runs_eq_of_not_mem hpeek
      (peek_smallFootprint regs.mainStack)]
    · exact hforwardInv'.buffer_eq
    · simp [regs.injective.eq_iff]
  have hpeekIndex : afterPeek regs.indexCount = 0 := by
    rw [runs_eq_of_not_mem hpeek
      (peek_smallFootprint regs.mainStack)]
    · exact hforwardInv'.index_eq
    · simp [regs.injective.eq_iff]
  have hpeekCompleted :
      afterPeek regs.completed = index := by
    rw [runs_eq_of_not_mem hpeek
      (peek_smallFootprint regs.mainStack)]
    · exact hforwardInv'.completed_eq
    · simp [regs.injective.eq_iff]
  have hpeekOne : afterPeek regs.one = 1 := by
    rw [runs_eq_of_not_mem hpeek
      (peek_smallFootprint regs.mainStack)]
    · exact hforwardInv'.one_eq
    · simp [regs.injective.eq_iff]
  have hpeekReplacement :
      afterPeek regs.replacement =
        store regs.replacement := by
    rw [runs_eq_of_not_mem hpeek
      (peek_smallFootprint regs.mainStack)]
    · exact hforwardReplacement
    · simp [regs.injective.eq_iff]
  let resultZero :=
    (Basic.imm regs.result 0).exec afterPeek
  let afterResult :=
    (Basic.add regs.result regs.value regs.result).exec resultZero
  have hafterResultValue :
      afterResult regs.result =
        PackedDigits.digit base word index := by
    simp [afterResult, resultZero, Basic.exec,
      regs.injective.eq_iff, hpeekValue']
  have hafterResultInv :
      BankState regs base
        (popN base index word)
        (reversedPrefix base word index)
        0 index afterResult := by
    constructor <;>
      simp [afterResult, resultZero, Basic.exec,
        regs.injective.eq_iff, hpeekWord', hpeekBuffer,
        hpeekBase', hpeekBasePred', hpeekOne, hpeekIndex,
        hpeekCompleted]
  have hafterResultReplacement :
      afterResult regs.replacement =
        store regs.replacement := by
    simp [afterResult, resultZero, Basic.exec,
      regs.injective.eq_iff, hpeekReplacement]
  have hrun : Runs (bankSeek regs) store afterResult := by
    simpa [bankSeek, Cmd.seqList] using
      Runs.seq (Runs.basic (Basic.imm regs.buffer 0) store)
        (Runs.seq
          (Runs.basic (Basic.imm regs.completed 0) bufferZero)
          (Runs.seq hforward
            (Runs.seq hpeek
              (Runs.seq
                (Runs.basic (Basic.imm regs.result 0) afterPeek)
                (Runs.basic
                  (Basic.add regs.result regs.value regs.result)
                  resultZero)))))
  exact ⟨afterResult, hrun, hafterResultInv,
    hafterResultValue, hafterResultReplacement⟩

theorem bankSeek_invariantRuns_internal
    (regs : BankRegisters) (allowed : Finset ℕ) (bound : ℕ)
    (store : Store)
    (base word index digitCount : ℕ)
    (hbase : 0 < base)
    (hword : store regs.word = word)
    (hbaseValue : store regs.base = base)
    (hbasePred : store regs.basePred = base - 1)
    (hone : store regs.one = 1)
    (hindex : store regs.indexCount = index)
    (hwordCapacity : word < base ^ digitCount)
    (hindexCapacity : index ≤ digitCount)
    (hpackedBound : base ^ digitCount ≤ bound)
    (hbaseBound : base ≤ bound)
    (hindexBound : index ≤ bound)
    (hstore : ValuesWithin allowed bound store) :
    ∃ final steps,
      InvariantRuns (ValuesWithin allowed bound)
        (bankSeek regs) store final steps ∧
      BankState regs base
        (popN base index word)
        (reversedPrefix base word index)
        0 index final ∧
      final regs.result = PackedDigits.digit base word index ∧
      final regs.replacement = store regs.replacement := by
  let bufferZero := (Basic.imm regs.buffer 0).exec store
  let countersZero :=
    (Basic.imm regs.completed 0).exec bufferZero
  have hbufferInvariant :
      ValuesWithin allowed bound bufferZero :=
    valuesWithin_imm hstore (Nat.zero_le bound)
  have hcountersInvariant :
      ValuesWithin allowed bound countersZero :=
    valuesWithin_imm hbufferInvariant (Nat.zero_le bound)
  have hinitial :
      BankState regs base word 0 index 0 countersZero := by
    constructor <;>
      simp [countersZero, bufferZero, Basic.exec,
        regs.injective.eq_iff, hword, hbaseValue, hbasePred,
        hone, hindex]
  have hinitial' :
      BankState regs base
        (popN base 0 word) (reversedPrefix base word 0)
        index 0 countersZero := by
    simpa [popN, reversedPrefix] using hinitial
  have hforwardWordCapacity :
      word < base ^ (0 + index + (digitCount - index)) := by
    simpa [Nat.add_sub_of_le hindexCapacity] using hwordCapacity
  have hforwardPackedBound :
      base ^ (0 + index + (digitCount - index)) ≤ bound := by
    simpa [Nat.add_sub_of_le hindexCapacity] using hpackedBound
  obtain ⟨afterForward, forwardSteps, hforward,
      hforwardInv⟩ :=
    bankForwardPrefixLoop_invariantRuns regs allowed bound
      countersZero base word 0 index (digitCount - index) hbase
      hinitial' hforwardWordCapacity hforwardPackedBound
      (by simpa using hindexBound) hcountersInvariant
  have hforwardInvariant :
      ValuesWithin allowed bound afterForward :=
    InvariantRuns.final hforward
  have hforwardInv' :
      BankState regs base
        (popN base index word)
        (reversedPrefix base word index)
        0 index afterForward := by
    simpa using hforwardInv
  have hwordBound : word ≤ bound :=
    (Nat.le_of_lt hwordCapacity).trans hpackedBound
  have hcurrentWordBound :
      popN base index word ≤ bound := by
    rw [popN_eq_div_pow_internal]
    exact (Nat.div_le_self word (base ^ index)).trans hwordBound
  let afterPeek :=
    peekResultStore regs.mainStack
      (PackedDigits.digit base (popN base index word) 0)
      afterForward
  obtain ⟨peekSteps, hpeek⟩ :=
    peek_invariantRuns_internal regs.mainStack allowed bound
      afterForward base (popN base index word) hbase
      hforwardInv'.word_eq hforwardInv'.base_eq
      hforwardInv'.basePred_eq hcurrentWordBound
      hforwardInvariant
  have hpeekRuns :
      Runs (peek regs.mainStack) afterForward afterPeek :=
    InvariantRuns.toRuns hpeek
  have hpeekInvariant :
      ValuesWithin allowed bound afterPeek :=
    InvariantRuns.final hpeek
  obtain ⟨semanticPeek, hsemanticPeek, _, hsemanticValue,
      _, _, _⟩ :=
    peek_runs_internal regs.mainStack afterForward base
      (popN base index word) hbase hforwardInv'.word_eq
      hforwardInv'.base_eq hforwardInv'.basePred_eq
  have hpeekEq : afterPeek = semanticPeek :=
    runs_final_unique hpeekRuns hsemanticPeek
  rw [← hpeekEq] at hsemanticValue
  have hpeekValue :
      afterPeek regs.value =
        PackedDigits.digit base word index := by
    simpa [digit_popN_internal] using hsemanticValue
  let resultZero :=
    (Basic.imm regs.result 0).exec afterPeek
  let afterResult :=
    (Basic.add regs.result regs.value regs.result).exec resultZero
  have hresultZeroInvariant :
      ValuesWithin allowed bound resultZero :=
    valuesWithin_imm hpeekInvariant (Nat.zero_le bound)
  have hresultZeroValue :
      resultZero regs.value =
        PackedDigits.digit base word index := by
    simp [resultZero, Basic.exec, regs.injective.eq_iff,
      hpeekValue]
  have hresultZeroResult : resultZero regs.result = 0 := by
    simp [resultZero, Basic.exec]
  have hdigitBound :
      PackedDigits.digit base word index ≤ bound :=
    (Nat.le_of_lt (PackedDigits.digit_lt hbase)).trans hbaseBound
  have hafterResultInvariant :
      ValuesWithin allowed bound afterResult := by
    apply valuesWithin_add hresultZeroInvariant
    rw [hresultZeroValue, hresultZeroResult, Nat.add_zero]
    exact hdigitBound
  have hrun :
      InvariantRuns (ValuesWithin allowed bound)
        (bankSeek regs) store afterResult
        (1 + (1 + (forwardSteps + (peekSteps + (1 + 1))))) := by
    simpa [bankSeek, Cmd.seqList] using
      InvariantRuns.seq
        (InvariantRuns.basic (Basic.imm regs.buffer 0) store
          hstore hbufferInvariant)
        (InvariantRuns.seq
          (InvariantRuns.basic (Basic.imm regs.completed 0)
            bufferZero hbufferInvariant hcountersInvariant)
          (InvariantRuns.seq hforward
            (InvariantRuns.seq hpeek
              (InvariantRuns.seq
                (InvariantRuns.basic (Basic.imm regs.result 0)
                  afterPeek hpeekInvariant hresultZeroInvariant)
                (InvariantRuns.basic
                  (Basic.add regs.result regs.value regs.result)
                  resultZero hresultZeroInvariant
                  hafterResultInvariant)))))
  obtain ⟨semanticFinal, hsemanticRun, hsemanticInv,
      hsemanticResult, hsemanticReplacement⟩ :=
    bankSeek_runs regs store base word index hbase hword
      hbaseValue hbasePred hone hindex
  have hfinalEq : afterResult = semanticFinal :=
    runs_final_unique (InvariantRuns.toRuns hrun) hsemanticRun
  rw [← hfinalEq] at hsemanticInv hsemanticResult hsemanticReplacement
  exact ⟨afterResult,
    1 + (1 + (forwardSteps + (peekSteps + (1 + 1)))),
    hrun, hsemanticInv, hsemanticResult, hsemanticReplacement⟩

theorem bankRead_runs_internal
    (regs : BankRegisters) (store : Store)
    (base word index : ℕ) (hbase : 0 < base)
    (hword : store regs.word = word)
    (hbaseValue : store regs.base = base)
    (hbasePred : store regs.basePred = base - 1)
    (hone : store regs.one = 1)
    (hindex : store regs.indexCount = index) :
    ∃ final,
      Runs (bankRead regs) store final ∧
      final regs.word = word ∧
      final regs.buffer = 0 ∧
      final regs.indexCount = 0 ∧
      final regs.completed = 0 ∧
      final regs.result = PackedDigits.digit base word index ∧
      final regs.base = base ∧
      final regs.basePred = base - 1 ∧
      final regs.one = 1 ∧
      final regs.replacement = store regs.replacement := by
  obtain ⟨afterSeek, hseek, hseekInv, hseekResult,
      hseekReplacement⟩ :=
    bankSeek_runs regs store base word index hbase hword
      hbaseValue hbasePred hone hindex
  obtain ⟨final, hrestore, hfinalInv⟩ :=
    bankRestoreLoop_runs regs afterSeek base
      (popN base index word)
      (reversedPrefix base word index) 0 index hbase
      hseekInv
  have hfinalResult :
      final regs.result =
        PackedDigits.digit base word index := by
    rw [runs_eq_of_not_mem hrestore
      (bankRestore_smallFootprint regs)]
    · exact hseekResult
    · simp [regs.injective.eq_iff]
  have hfinalReplacement :
      final regs.replacement =
        store regs.replacement := by
    rw [runs_eq_of_not_mem hrestore
      (bankRestore_smallFootprint regs)]
    · exact hseekReplacement
    · simp [regs.injective.eq_iff]
  have hrun : Runs (bankRead regs) store final := by
    exact Runs.seq hseek hrestore
  refine ⟨final, hrun, ?_, ?_, hfinalInv.index_eq,
    hfinalInv.completed_eq, hfinalResult, hfinalInv.base_eq,
    hfinalInv.basePred_eq, hfinalInv.one_eq,
    hfinalReplacement⟩
  · rw [hfinalInv.word_eq,
      restoreN_popN_reversedPrefix_internal hbase]
  · rw [hfinalInv.buffer_eq,
      popN_reversedPrefix_internal hbase]

theorem bankRead_invariantRuns_internal
    (regs : BankRegisters) (allowed : Finset ℕ) (bound : ℕ)
    (store : Store)
    (base word index digitCount : ℕ)
    (hbase : 0 < base)
    (hword : store regs.word = word)
    (hbaseValue : store regs.base = base)
    (hbasePred : store regs.basePred = base - 1)
    (hone : store regs.one = 1)
    (hindex : store regs.indexCount = index)
    (hwordCapacity : word < base ^ digitCount)
    (hindexCapacity : index ≤ digitCount)
    (hpackedBound : base ^ digitCount ≤ bound)
    (hbaseBound : base ≤ bound)
    (hindexBound : index ≤ bound)
    (hstore : ValuesWithin allowed bound store) :
    ∃ final steps,
      InvariantRuns (ValuesWithin allowed bound)
        (bankRead regs) store final steps ∧
      final regs.word = word ∧
      final regs.buffer = 0 ∧
      final regs.indexCount = 0 ∧
      final regs.completed = 0 ∧
      final regs.result = PackedDigits.digit base word index ∧
      final regs.base = base ∧
      final regs.basePred = base - 1 ∧
      final regs.one = 1 ∧
      final regs.replacement = store regs.replacement := by
  obtain ⟨afterSeek, seekSteps, hseek, hseekInv, _, _⟩ :=
    bankSeek_invariantRuns_internal regs allowed bound store base
      word index digitCount hbase hword hbaseValue hbasePred hone
      hindex hwordCapacity hindexCapacity hpackedBound hbaseBound
      hindexBound hstore
  have hseekInvariant :
      ValuesWithin allowed bound afterSeek :=
    InvariantRuns.final hseek
  have htail :
      popN base index word < base ^ (digitCount - index) :=
    popN_lt_pow_internal hbase hwordCapacity hindexCapacity
  have hprefix :
      reversedPrefix base word index < base ^ index :=
    reversedPrefix_lt_pow_internal hbase index
  have hrestoreCapacity :
      base ^ ((digitCount - index) + index) ≤ bound := by
    simpa [Nat.sub_add_cancel hindexCapacity] using hpackedBound
  obtain ⟨final, restoreSteps, hrestore, _⟩ :=
    bankRestoreLoop_invariantRuns regs allowed bound afterSeek base
      (popN base index word) (reversedPrefix base word index)
      0 index (digitCount - index) hbase hseekInv htail hprefix
      hrestoreCapacity hindexBound hseekInvariant
  have hrun :
      InvariantRuns (ValuesWithin allowed bound)
        (bankRead regs) store final (seekSteps + restoreSteps) :=
    InvariantRuns.seq hseek hrestore
  obtain ⟨semanticFinal, hsemanticRun, hfinalWord,
      hfinalBuffer, hfinalIndex, hfinalCompleted, hfinalResult,
      hfinalBase, hfinalBasePred, hfinalOne,
      hfinalReplacement⟩ :=
    bankRead_runs_internal regs store base word index hbase hword
      hbaseValue hbasePred hone hindex
  have hfinalEq : final = semanticFinal :=
    runs_final_unique (InvariantRuns.toRuns hrun) hsemanticRun
  subst semanticFinal
  exact ⟨final, seekSteps + restoreSteps, hrun, hfinalWord,
    hfinalBuffer, hfinalIndex, hfinalCompleted, hfinalResult,
    hfinalBase, hfinalBasePred, hfinalOne, hfinalReplacement⟩

theorem bankReplace_runs_internal
    (regs : BankRegisters) (store : Store)
    (base word index replacement : ℕ) (hbase : 0 < base)
    (hword : store regs.word = word)
    (hbaseValue : store regs.base = base)
    (hbasePred : store regs.basePred = base - 1)
    (hone : store regs.one = 1)
    (hindex : store regs.indexCount = index)
    (hreplacement : store regs.replacement = replacement) :
    ∃ final,
      Runs (bankReplace regs) store final ∧
      final regs.word = replaceAt base word index replacement ∧
      final regs.buffer = 0 ∧
      final regs.indexCount = 0 ∧
      final regs.completed = 0 ∧
      final regs.result = PackedDigits.digit base word index ∧
      final regs.base = base ∧
      final regs.basePred = base - 1 ∧
      final regs.one = 1 ∧
      final regs.replacement = replacement := by
  obtain ⟨afterSeek, hseek, hseekInv, hseekResult,
      hseekReplacement⟩ :=
    bankSeek_runs regs store base word index hbase hword
      hbaseValue hbasePred hone hindex
  have hseekReplacement' :
      afterSeek regs.replacement = replacement := by
    rw [hseekReplacement, hreplacement]
  obtain ⟨afterPop, hpop, hpopWord, _, _, hpopBase,
      hpopBasePred, hpopOne⟩ :=
    pop_runs_internal regs.mainStack afterSeek base
      (popN base index word) hbase hseekInv.word_eq
      hseekInv.base_eq hseekInv.basePred_eq hseekInv.one_eq
  have hpopWord' :
      afterPop regs.word = popN base (index + 1) word := by
    simpa only [popN] using hpopWord
  have hpopBase' : afterPop regs.base = base := by
    simpa using hpopBase
  have hpopBasePred' :
      afterPop regs.basePred = base - 1 := by
    simpa using hpopBasePred
  have hpopOne' : afterPop regs.one = 1 := by
    simpa using hpopOne
  have hpopBuffer :
      afterPop regs.buffer =
        reversedPrefix base word index := by
    rw [runs_eq_of_not_mem hpop
      (pop_smallFootprint regs.mainStack)]
    · exact hseekInv.buffer_eq
    · simp [regs.injective.eq_iff]
  have hpopIndex : afterPop regs.indexCount = 0 := by
    rw [runs_eq_of_not_mem hpop
      (pop_smallFootprint regs.mainStack)]
    · exact hseekInv.index_eq
    · simp [regs.injective.eq_iff]
  have hpopCompleted : afterPop regs.completed = index := by
    rw [runs_eq_of_not_mem hpop
      (pop_smallFootprint regs.mainStack)]
    · exact hseekInv.completed_eq
    · simp [regs.injective.eq_iff]
  have hpopResult :
      afterPop regs.result =
        PackedDigits.digit base word index := by
    rw [runs_eq_of_not_mem hpop
      (pop_smallFootprint regs.mainStack)]
    · exact hseekResult
    · simp [regs.injective.eq_iff]
  have hpopReplacement :
      afterPop regs.replacement = replacement := by
    rw [runs_eq_of_not_mem hpop
      (pop_smallFootprint regs.mainStack)]
    · exact hseekReplacement'
    · simp [regs.injective.eq_iff]
  let valueZero :=
    (Basic.imm regs.value 0).exec afterPop
  let afterValue :=
    (Basic.add regs.value regs.replacement regs.value).exec valueZero
  have hafterValueValue :
      afterValue regs.value = replacement := by
    simp [afterValue, valueZero, Basic.exec,
      regs.injective.eq_iff, hpopReplacement]
  have hafterValueWord :
      afterValue regs.word = popN base (index + 1) word := by
    simp [afterValue, valueZero, Basic.exec,
      regs.injective.eq_iff, hpopWord']
  have hafterValueBuffer :
      afterValue regs.buffer =
        reversedPrefix base word index := by
    simp [afterValue, valueZero, Basic.exec,
      regs.injective.eq_iff, hpopBuffer]
  have hafterValueBase : afterValue regs.base = base := by
    simp [afterValue, valueZero, Basic.exec,
      regs.injective.eq_iff, hpopBase']
  have hafterValueBasePred :
      afterValue regs.basePred = base - 1 := by
    simp [afterValue, valueZero, Basic.exec,
      regs.injective.eq_iff, hpopBasePred']
  have hafterValueOne : afterValue regs.one = 1 := by
    simp [afterValue, valueZero, Basic.exec,
      regs.injective.eq_iff, hpopOne']
  have hafterValueIndex :
      afterValue regs.indexCount = 0 := by
    simp [afterValue, valueZero, Basic.exec,
      regs.injective.eq_iff, hpopIndex]
  have hafterValueCompleted :
      afterValue regs.completed = index := by
    simp [afterValue, valueZero, Basic.exec,
      regs.injective.eq_iff, hpopCompleted]
  have hafterValueResult :
      afterValue regs.result =
        PackedDigits.digit base word index := by
    simp [afterValue, valueZero, Basic.exec,
      regs.injective.eq_iff, hpopResult]
  have hafterValueReplacement :
      afterValue regs.replacement = replacement := by
    simp [afterValue, valueZero, Basic.exec,
      regs.injective.eq_iff, hpopReplacement]
  obtain ⟨afterPush, hpush, hpushWord, _, hpushBase,
      hpushValue⟩ :=
    push_runs_internal regs.mainStack afterValue base
      (popN base (index + 1) word) replacement
      hafterValueWord hafterValueBase hafterValueValue
  have hpushWord' :
      afterPush regs.word =
        PackedDigits.push base replacement
          (popN base (index + 1) word) := by
    simpa using hpushWord
  have hpushBase' : afterPush regs.base = base := by
    simpa using hpushBase
  have hpushBuffer :
      afterPush regs.buffer =
        reversedPrefix base word index := by
    rw [runs_eq_of_not_mem hpush
      (push_smallFootprint regs.mainStack)]
    · exact hafterValueBuffer
    · simp [regs.injective.eq_iff]
  have hpushBasePred :
      afterPush regs.basePred = base - 1 := by
    rw [runs_eq_of_not_mem hpush
      (push_smallFootprint regs.mainStack)]
    · exact hafterValueBasePred
    · simp [regs.injective.eq_iff]
  have hpushOne : afterPush regs.one = 1 := by
    rw [runs_eq_of_not_mem hpush
      (push_smallFootprint regs.mainStack)]
    · exact hafterValueOne
    · simp [regs.injective.eq_iff]
  have hpushIndex : afterPush regs.indexCount = 0 := by
    rw [runs_eq_of_not_mem hpush
      (push_smallFootprint regs.mainStack)]
    · exact hafterValueIndex
    · simp [regs.injective.eq_iff]
  have hpushCompleted :
      afterPush regs.completed = index := by
    rw [runs_eq_of_not_mem hpush
      (push_smallFootprint regs.mainStack)]
    · exact hafterValueCompleted
    · simp [regs.injective.eq_iff]
  have hpushResult :
      afterPush regs.result =
        PackedDigits.digit base word index := by
    rw [runs_eq_of_not_mem hpush
      (push_smallFootprint regs.mainStack)]
    · exact hafterValueResult
    · simp [regs.injective.eq_iff]
  have hpushReplacement :
      afterPush regs.replacement = replacement := by
    rw [runs_eq_of_not_mem hpush
      (push_smallFootprint regs.mainStack)]
    · exact hafterValueReplacement
    · simp [regs.injective.eq_iff]
  have hpushInv :
      BankState regs base
        (PackedDigits.push base replacement
          (popN base (index + 1) word))
        (reversedPrefix base word index)
        0 index afterPush :=
    ⟨hpushWord', hpushBuffer, hpushBase', hpushBasePred,
      hpushOne, hpushIndex, hpushCompleted⟩
  obtain ⟨final, hrestore, hfinalInv⟩ :=
    bankRestoreLoop_runs regs afterPush base
      (PackedDigits.push base replacement
        (popN base (index + 1) word))
      (reversedPrefix base word index) 0 index hbase hpushInv
  have hfinalResult :
      final regs.result =
        PackedDigits.digit base word index := by
    rw [runs_eq_of_not_mem hrestore
      (bankRestore_smallFootprint regs)]
    · exact hpushResult
    · simp [regs.injective.eq_iff]
  have hfinalReplacement :
      final regs.replacement = replacement := by
    rw [runs_eq_of_not_mem hrestore
      (bankRestore_smallFootprint regs)]
    · exact hpushReplacement
    · simp [regs.injective.eq_iff]
  have hrun : Runs (bankReplace regs) store final := by
    simpa [bankReplace, Cmd.seqList] using
      Runs.seq hseek
        (Runs.seq hpop
          (Runs.seq
            (Runs.basic (Basic.imm regs.value 0) afterPop)
            (Runs.seq
              (Runs.basic
                (Basic.add regs.value regs.replacement regs.value)
                valueZero)
              (Runs.seq hpush hrestore))))
  refine ⟨final, hrun, ?_, ?_, hfinalInv.index_eq,
    hfinalInv.completed_eq, hfinalResult, hfinalInv.base_eq,
    hfinalInv.basePred_eq, hfinalInv.one_eq,
    hfinalReplacement⟩
  · exact hfinalInv.word_eq
  · rw [hfinalInv.buffer_eq,
      popN_reversedPrefix_internal hbase]

theorem bankReplace_invariantRuns_internal
    (regs : BankRegisters) (allowed : Finset ℕ) (bound : ℕ)
    (store : Store)
    (base word index replacement digitCount : ℕ)
    (hbase : 0 < base)
    (hword : store regs.word = word)
    (hbaseValue : store regs.base = base)
    (hbasePred : store regs.basePred = base - 1)
    (hone : store regs.one = 1)
    (hindex : store regs.indexCount = index)
    (hreplacement : store regs.replacement = replacement)
    (hwordCapacity : word < base ^ digitCount)
    (hindexCapacity : index < digitCount)
    (hreplacementDigit : replacement < base)
    (hpackedBound : base ^ digitCount ≤ bound)
    (hbaseBound : base ≤ bound)
    (hindexBound : index ≤ bound)
    (hreplacementBound : replacement ≤ bound)
    (hstore : ValuesWithin allowed bound store) :
    ∃ final steps,
      InvariantRuns (ValuesWithin allowed bound)
        (bankReplace regs) store final steps ∧
      final regs.word = replaceAt base word index replacement ∧
      final regs.buffer = 0 ∧
      final regs.indexCount = 0 ∧
      final regs.completed = 0 ∧
      final regs.result = PackedDigits.digit base word index ∧
      final regs.base = base ∧
      final regs.basePred = base - 1 ∧
      final regs.one = 1 ∧
      final regs.replacement = replacement := by
  have hindexCapacityLe : index ≤ digitCount :=
    Nat.le_of_lt hindexCapacity
  obtain ⟨afterSeek, seekSteps, hseek, hseekInv, _,
      hseekReplacement⟩ :=
    bankSeek_invariantRuns_internal regs allowed bound store base
      word index digitCount hbase hword hbaseValue hbasePred hone
      hindex hwordCapacity hindexCapacityLe hpackedBound hbaseBound
      hindexBound hstore
  have hseekInvariant :
      ValuesWithin allowed bound afterSeek :=
    InvariantRuns.final hseek
  have hseekReplacement' :
      afterSeek regs.replacement = replacement := by
    rw [hseekReplacement, hreplacement]
  have hwordBound : word ≤ bound :=
    (Nat.le_of_lt hwordCapacity).trans hpackedBound
  have hcurrentWordBound :
      popN base index word ≤ bound := by
    rw [popN_eq_div_pow_internal]
    exact (Nat.div_le_self word (base ^ index)).trans hwordBound
  obtain ⟨afterPop, popSteps, hpop, hpopWord, _,
      _, hpopBase, hpopBasePred, hpopOne⟩ :=
    pop_invariantRuns_internal regs.mainStack allowed bound
      afterSeek base (popN base index word) hbase
      hseekInv.word_eq hseekInv.base_eq hseekInv.basePred_eq
      hseekInv.one_eq hcurrentWordBound hseekInvariant
  have hpopRuns :
      Runs (pop regs.mainStack) afterSeek afterPop :=
    InvariantRuns.toRuns hpop
  have hpopInvariant :
      ValuesWithin allowed bound afterPop :=
    InvariantRuns.final hpop
  have hpopWord' :
      afterPop regs.word = popN base (index + 1) word := by
    simpa only [popN] using hpopWord
  have hpopBase' : afterPop regs.base = base := by
    simpa using hpopBase
  have hpopBasePred' :
      afterPop regs.basePred = base - 1 := by
    simpa using hpopBasePred
  have hpopOne' : afterPop regs.one = 1 := by
    simpa using hpopOne
  have hpopBuffer :
      afterPop regs.buffer = reversedPrefix base word index := by
    rw [runs_eq_of_not_mem hpopRuns
      (pop_smallFootprint regs.mainStack)]
    · exact hseekInv.buffer_eq
    · simp [regs.injective.eq_iff]
  have hpopIndex : afterPop regs.indexCount = 0 := by
    rw [runs_eq_of_not_mem hpopRuns
      (pop_smallFootprint regs.mainStack)]
    · exact hseekInv.index_eq
    · simp [regs.injective.eq_iff]
  have hpopCompleted : afterPop regs.completed = index := by
    rw [runs_eq_of_not_mem hpopRuns
      (pop_smallFootprint regs.mainStack)]
    · exact hseekInv.completed_eq
    · simp [regs.injective.eq_iff]
  have hpopReplacement :
      afterPop regs.replacement = replacement := by
    rw [runs_eq_of_not_mem hpopRuns
      (pop_smallFootprint regs.mainStack)]
    · exact hseekReplacement'
    · simp [regs.injective.eq_iff]
  let valueZero :=
    (Basic.imm regs.value 0).exec afterPop
  let afterValue :=
    (Basic.add regs.value regs.replacement regs.value).exec
      valueZero
  have hvalueZeroInvariant :
      ValuesWithin allowed bound valueZero :=
    valuesWithin_imm hpopInvariant (Nat.zero_le bound)
  have hvalueZeroReplacement :
      valueZero regs.replacement = replacement := by
    simp [valueZero, Basic.exec, regs.injective.eq_iff,
      hpopReplacement]
  have hvalueZeroValue : valueZero regs.value = 0 := by
    simp [valueZero, Basic.exec]
  have hafterValueInvariant :
      ValuesWithin allowed bound afterValue := by
    apply valuesWithin_add hvalueZeroInvariant
    rw [hvalueZeroReplacement, hvalueZeroValue, Nat.add_zero]
    exact hreplacementBound
  have hafterValueValue :
      afterValue regs.value = replacement := by
    simp [afterValue, Basic.exec, hvalueZeroReplacement,
      hvalueZeroValue]
  have hafterValueWord :
      afterValue regs.word = popN base (index + 1) word := by
    simp [afterValue, valueZero, Basic.exec,
      regs.injective.eq_iff, hpopWord']
  have hafterValueBase : afterValue regs.base = base := by
    simp [afterValue, valueZero, Basic.exec,
      regs.injective.eq_iff, hpopBase']
  have htail :
      popN base (index + 1) word <
        base ^ (digitCount - (index + 1)) :=
    popN_lt_pow_internal hbase hwordCapacity (by omega)
  have hpushedRaw :
      PackedDigits.push base replacement
          (popN base (index + 1) word) <
        base ^ ((digitCount - (index + 1)) + 1) :=
    PackedDigits.push_lt_pow htail hreplacementDigit
  have hexponent :
      (digitCount - (index + 1)) + 1 = digitCount - index := by
    omega
  have hpushed :
      PackedDigits.push base replacement
          (popN base (index + 1) word) <
        base ^ (digitCount - index) := by
    rw [hexponent] at hpushedRaw
    exact hpushedRaw
  have honeBase : 1 ≤ base := by omega
  have hsuffixCapacity :
      base ^ (digitCount - index) ≤ bound :=
    (Nat.pow_le_pow_right honeBase (Nat.sub_le _ _)).trans
      hpackedBound
  have hpushBound :
      replacement + base * popN base (index + 1) word ≤ bound :=
    (Nat.le_of_lt hpushed).trans hsuffixCapacity
  have hproductBound :
      base * popN base (index + 1) word ≤ bound :=
    (Nat.le_add_left _ _).trans hpushBound
  let afterPush :=
    pushResultStore regs.mainStack
      (PackedDigits.push base replacement
        (popN base (index + 1) word))
      afterValue
  have hpush :
      InvariantRuns (ValuesWithin allowed bound)
        (push regs.mainStack) afterValue afterPush 3 :=
    push_invariantRuns_internal regs.mainStack allowed bound
      afterValue base (popN base (index + 1) word) replacement
      hafterValueWord hafterValueBase hafterValueValue
      hproductBound hpushBound hafterValueInvariant
  have hpushRuns :
      Runs (push regs.mainStack) afterValue afterPush :=
    InvariantRuns.toRuns hpush
  have hpushInvariant :
      ValuesWithin allowed bound afterPush :=
    InvariantRuns.final hpush
  obtain ⟨semanticPush, hsemanticPush, hsemanticWord, _,
      hsemanticBase, _⟩ :=
    push_runs_internal regs.mainStack afterValue base
      (popN base (index + 1) word) replacement
      hafterValueWord hafterValueBase hafterValueValue
  have hpushEq : afterPush = semanticPush :=
    runs_final_unique hpushRuns hsemanticPush
  rw [← hpushEq] at hsemanticWord hsemanticBase
  have hpushWord :
      afterPush regs.word =
        PackedDigits.push base replacement
          (popN base (index + 1) word) := by
    simpa using hsemanticWord
  have hpushBase : afterPush regs.base = base := by
    simpa using hsemanticBase
  have hpushBuffer :
      afterPush regs.buffer = reversedPrefix base word index := by
    rw [runs_eq_of_not_mem hpushRuns
      (push_smallFootprint regs.mainStack)]
    · simp [afterValue, valueZero, Basic.exec,
        regs.injective.eq_iff, hpopBuffer]
    · simp [regs.injective.eq_iff]
  have hpushBasePred :
      afterPush regs.basePred = base - 1 := by
    rw [runs_eq_of_not_mem hpushRuns
      (push_smallFootprint regs.mainStack)]
    · simp [afterValue, valueZero, Basic.exec,
        regs.injective.eq_iff, hpopBasePred']
    · simp [regs.injective.eq_iff]
  have hpushOne : afterPush regs.one = 1 := by
    rw [runs_eq_of_not_mem hpushRuns
      (push_smallFootprint regs.mainStack)]
    · simp [afterValue, valueZero, Basic.exec,
        regs.injective.eq_iff, hpopOne']
    · simp [regs.injective.eq_iff]
  have hpushIndex : afterPush regs.indexCount = 0 := by
    rw [runs_eq_of_not_mem hpushRuns
      (push_smallFootprint regs.mainStack)]
    · simp [afterValue, valueZero, Basic.exec,
        regs.injective.eq_iff, hpopIndex]
    · simp [regs.injective.eq_iff]
  have hpushCompleted :
      afterPush regs.completed = index := by
    rw [runs_eq_of_not_mem hpushRuns
      (push_smallFootprint regs.mainStack)]
    · simp [afterValue, valueZero, Basic.exec,
        regs.injective.eq_iff, hpopCompleted]
    · simp [regs.injective.eq_iff]
  have hpushInv :
      BankState regs base
        (PackedDigits.push base replacement
          (popN base (index + 1) word))
        (reversedPrefix base word index)
        0 index afterPush :=
    ⟨hpushWord, hpushBuffer, hpushBase, hpushBasePred,
      hpushOne, hpushIndex, hpushCompleted⟩
  have hprefix :
      reversedPrefix base word index < base ^ index :=
    reversedPrefix_lt_pow_internal hbase index
  have hrestoreCapacity :
      base ^ ((digitCount - index) + index) ≤ bound := by
    simpa [Nat.sub_add_cancel hindexCapacityLe] using hpackedBound
  obtain ⟨final, restoreSteps, hrestore, _⟩ :=
    bankRestoreLoop_invariantRuns regs allowed bound afterPush base
      (PackedDigits.push base replacement
        (popN base (index + 1) word))
      (reversedPrefix base word index) 0 index
      (digitCount - index) hbase hpushInv hpushed hprefix
      hrestoreCapacity hindexBound hpushInvariant
  have hrun :
      InvariantRuns (ValuesWithin allowed bound)
        (bankReplace regs) store final
        (seekSteps +
          (popSteps + (1 + (1 + (3 + restoreSteps))))) := by
    simpa [bankReplace, Cmd.seqList] using
      InvariantRuns.seq hseek
        (InvariantRuns.seq hpop
          (InvariantRuns.seq
            (InvariantRuns.basic (Basic.imm regs.value 0) afterPop
              hpopInvariant hvalueZeroInvariant)
            (InvariantRuns.seq
              (InvariantRuns.basic
                (Basic.add regs.value regs.replacement regs.value)
                valueZero hvalueZeroInvariant
                hafterValueInvariant)
              (InvariantRuns.seq hpush hrestore))))
  obtain ⟨semanticFinal, hsemanticRun, hfinalWord,
      hfinalBuffer, hfinalIndex, hfinalCompleted, hfinalResult,
      hfinalBase, hfinalBasePred, hfinalOne,
      hfinalReplacement⟩ :=
    bankReplace_runs_internal regs store base word index replacement
      hbase hword hbaseValue hbasePred hone hindex hreplacement
  have hfinalEq : final = semanticFinal :=
    runs_final_unique (InvariantRuns.toRuns hrun) hsemanticRun
  subst semanticFinal
  exact ⟨final,
    seekSteps + (popSteps + (1 + (1 + (3 + restoreSteps)))),
    hrun, hfinalWord, hfinalBuffer, hfinalIndex, hfinalCompleted,
    hfinalResult, hfinalBase, hfinalBasePred, hfinalOne,
    hfinalReplacement⟩

private theorem bankRead_residueFootprint
    (regs : BankRegisters) :
    RAM.Structured.Footprint.CmdWritesWithin
      regs.footprint (bankRead regs) := by
  simp [bankRead, bankSeek, bankForward, bankForwardBody,
    bankRestore, bankRestoreBody, peek, pop, popBody, popTestOp,
    push, RuntimeArithmetic.reduce, RuntimeArithmetic.reduceBody,
    RuntimeArithmetic.reduceTestOp, StackRegisters.reduceRegisters,
    Cmd.seqList, RAM.Structured.Footprint.CmdWritesWithin,
    RAM.Structured.Footprint.BasicWritesWithin]

private theorem bankReplace_residueFootprint
    (regs : BankRegisters) :
    RAM.Structured.Footprint.CmdWritesWithin
      regs.footprint (bankReplace regs) := by
  simp [bankReplace, bankSeek, bankForward, bankForwardBody,
    bankRestore, bankRestoreBody, peek, pop, popBody, popTestOp,
    push, RuntimeArithmetic.reduce, RuntimeArithmetic.reduceBody,
    RuntimeArithmetic.reduceTestOp, StackRegisters.reduceRegisters,
    Cmd.seqList, RAM.Structured.Footprint.CmdWritesWithin,
    RAM.Structured.Footprint.BasicWritesWithin]

private theorem saveBankIndex_smallFootprint
    (regs : ResidueBankRegisters) :
    RAM.Structured.Footprint.CmdWritesWithin
      {regs.savedIndex} (saveBankIndex regs) := by
  simp [saveBankIndex,
    RAM.Structured.Footprint.CmdWritesWithin,
    RAM.Structured.Footprint.BasicWritesWithin]

private theorem restoreBankIndex_smallFootprint
    (regs : ResidueBankRegisters) :
    RAM.Structured.Footprint.CmdWritesWithin
      {regs.bank.indexCount} (restoreBankIndex regs) := by
  simp [restoreBankIndex,
    RAM.Structured.Footprint.CmdWritesWithin,
    RAM.Structured.Footprint.BasicWritesWithin]

private theorem residueBankOp_smallFootprint
    (regs : ResidueBankRegisters) (op : ResidueBankOp) :
    RAM.Structured.Footprint.CmdWritesWithin
      {regs.bank.replacement, regs.bank.test}
      (op.command regs) := by
  cases op <;>
    simp [ResidueBankOp.command, RuntimeArithmetic.addMod,
      RuntimeArithmetic.mulMod, RuntimeArithmetic.reduce,
      RuntimeArithmetic.reduceBody, RuntimeArithmetic.reduceTestOp,
      ResidueBankRegisters.reduceRegisters,
      RAM.Structured.Footprint.CmdWritesWithin,
      RAM.Structured.Footprint.BasicWritesWithin]

private theorem bankAddress_ne_extra
    (regs : ResidueBankRegisters) (bankSlot : Fin 12)
    (extra : Fin 16) (hextra : 12 ≤ extra.val) :
    regs.bank.index bankSlot ≠ regs.index extra := by
  intro heq
  apply residueExtra_not_mem_bankFootprint regs extra hextra
  rw [← heq]
  exact regs.bank.index_mem_footprint bankSlot

private theorem bankSlot_not_mem_residueScratch
    (regs : ResidueBankRegisters) (slot : Fin 12)
    (hreplacement : slot ≠ 11) (htest : slot ≠ 5) :
    regs.bank.index slot ∉
      ({regs.bank.replacement, regs.bank.test} : Finset ℕ) := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  exact ⟨regs.bank.index_ne hreplacement,
    regs.bank.index_ne htest⟩

private theorem extra_not_mem_residueScratch
    (regs : ResidueBankRegisters) (slot : Fin 16)
    (hslot : 12 ≤ slot.val) :
    regs.index slot ∉
      ({regs.bank.replacement, regs.bank.test} : Finset ℕ) := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  exact
    ⟨(bankAddress_ne_extra regs 11 slot hslot).symm,
      (bankAddress_ne_extra regs 5 slot hslot).symm⟩

theorem bankUpdateAt_runs_internal
    (regs : ResidueBankRegisters) (op : ResidueBankOp)
    (store : Store)
    (base word index modulus operand : ℕ)
    (hbase : 0 < base)
    (hmodulus : 0 < modulus)
    (hword : store regs.bank.word = word)
    (hbaseValue : store regs.bank.base = base)
    (hbasePred : store regs.bank.basePred = base - 1)
    (hone : store regs.bank.one = 1)
    (hindex : store regs.bank.indexCount = index)
    (hmodulusValue : store regs.modulus = modulus)
    (hmodulusPred : store regs.modulusPred = modulus - 1)
    (hoperand : store regs.operand = operand) :
    ∃ final,
      Runs (bankUpdateAt regs op) store final ∧
      final regs.bank.word =
        replaceAt base word index
          (op.apply modulus
            (PackedDigits.digit base word index) operand) ∧
      final regs.bank.buffer = 0 ∧
      final regs.bank.indexCount = 0 ∧
      final regs.bank.completed = 0 ∧
      final regs.bank.result =
        PackedDigits.digit base word index ∧
      final regs.bank.base = base ∧
      final regs.bank.basePred = base - 1 ∧
      final regs.bank.one = 1 ∧
      final regs.bank.replacement =
        op.apply modulus
          (PackedDigits.digit base word index) operand ∧
      final regs.modulus = modulus ∧
      final regs.modulusPred = modulus - 1 ∧
      final regs.operand = operand ∧
      final regs.savedIndex = index := by
  let savedZero :=
    (Basic.imm regs.savedIndex 0).exec store
  let afterSave :=
    (Basic.add regs.savedIndex regs.bank.indexCount
      regs.savedIndex).exec savedZero
  have hsaveRun : Runs (saveBankIndex regs) store afterSave := by
    exact Runs.seq (Runs.basic _ _) (Runs.basic _ _)
  have hsaveWord : afterSave regs.bank.word = word := by
    rw [runs_eq_of_not_mem hsaveRun
      (saveBankIndex_smallFootprint regs)]
    · exact hword
    · simpa only [Finset.mem_singleton] using
        bankAddress_ne_extra regs 0 15 (by omega)
  have hsaveBase : afterSave regs.bank.base = base := by
    rw [runs_eq_of_not_mem hsaveRun
      (saveBankIndex_smallFootprint regs)]
    · exact hbaseValue
    · simpa only [Finset.mem_singleton] using
        bankAddress_ne_extra regs 2 15 (by omega)
  have hsaveBasePred :
      afterSave regs.bank.basePred = base - 1 := by
    rw [runs_eq_of_not_mem hsaveRun
      (saveBankIndex_smallFootprint regs)]
    · exact hbasePred
    · simpa only [Finset.mem_singleton] using
        bankAddress_ne_extra regs 3 15 (by omega)
  have hsaveOne : afterSave regs.bank.one = 1 := by
    rw [runs_eq_of_not_mem hsaveRun
      (saveBankIndex_smallFootprint regs)]
    · exact hone
    · simpa only [Finset.mem_singleton] using
        bankAddress_ne_extra regs 6 15 (by omega)
  have hsaveIndex :
      afterSave regs.bank.indexCount = index := by
    rw [runs_eq_of_not_mem hsaveRun
      (saveBankIndex_smallFootprint regs)]
    · exact hindex
    · simpa only [Finset.mem_singleton] using
        bankAddress_ne_extra regs 8 15 (by omega)
  have hsaveModulus :
      afterSave regs.modulus = modulus := by
    rw [runs_eq_of_not_mem hsaveRun
      (saveBankIndex_smallFootprint regs)]
    · exact hmodulusValue
    · simpa only [Finset.mem_singleton] using
        regs.index_ne (first := 12) (second := 15) (by decide)
  have hsaveModulusPred :
      afterSave regs.modulusPred = modulus - 1 := by
    rw [runs_eq_of_not_mem hsaveRun
      (saveBankIndex_smallFootprint regs)]
    · exact hmodulusPred
    · simpa only [Finset.mem_singleton] using
        regs.index_ne (first := 13) (second := 15) (by decide)
  have hsaveOperand :
      afterSave regs.operand = operand := by
    rw [runs_eq_of_not_mem hsaveRun
      (saveBankIndex_smallFootprint regs)]
    · exact hoperand
    · simpa only [Finset.mem_singleton] using
        regs.index_ne (first := 14) (second := 15) (by decide)
  have hsaveSaved :
      afterSave regs.savedIndex = index := by
    have hne :=
      bankAddress_ne_extra regs 8 15 (by omega)
    change regs.index 8 ≠ regs.index 15 at hne
    change store (regs.index 8) = index at hindex
    simp [afterSave, savedZero, Basic.exec, hne, hindex]
  obtain ⟨afterRead, hread, hreadWord, _hreadBuffer,
      _hreadIndex, _hreadCompleted, hreadResult, hreadBase,
      hreadBasePred, hreadOne, _hreadReplacement⟩ :=
    bankRead_runs_internal regs.bank afterSave base word index hbase
      hsaveWord hsaveBase hsaveBasePred hsaveOne hsaveIndex
  have hreadModulus :
      afterRead regs.modulus = modulus := by
    rw [runs_eq_of_not_mem hread
      (bankRead_residueFootprint regs.bank)
      (residueExtra_not_mem_bankFootprint regs 12 (by omega))]
    exact hsaveModulus
  have hreadModulusPred :
      afterRead regs.modulusPred = modulus - 1 := by
    rw [runs_eq_of_not_mem hread
      (bankRead_residueFootprint regs.bank)
      (residueExtra_not_mem_bankFootprint regs 13 (by omega))]
    exact hsaveModulusPred
  have hreadOperand :
      afterRead regs.operand = operand := by
    rw [runs_eq_of_not_mem hread
      (bankRead_residueFootprint regs.bank)
      (residueExtra_not_mem_bankFootprint regs 14 (by omega))]
    exact hsaveOperand
  have hreadSaved :
      afterRead regs.savedIndex = index := by
    rw [runs_eq_of_not_mem hread
      (bankRead_residueFootprint regs.bank)
      (residueExtra_not_mem_bankFootprint regs 15 (by omega))]
    exact hsaveSaved
  let updated :=
    op.apply modulus (PackedDigits.digit base word index) operand
  let afterOp :=
    RuntimeArithmetic.reduceResultStore regs.reduceRegisters
      updated afterRead
  have hopRun : Runs (op.command regs) afterRead afterOp := by
    have hrun :=
      residueBankOp_runs op regs afterRead modulus hmodulus
        hreadModulus hreadModulusPred
    change afterRead (regs.index 10) =
      PackedDigits.digit base word index at hreadResult
    change afterRead (regs.index 14) = operand at hreadOperand
    simpa [afterOp, updated, hreadResult, hreadOperand] using hrun
  have hopWord : afterOp regs.bank.word = word := by
    rw [runs_eq_of_not_mem hopRun
      (residueBankOp_smallFootprint regs op)
      (bankSlot_not_mem_residueScratch regs 0 (by decide)
        (by decide))]
    exact hreadWord
  have hopBase : afterOp regs.bank.base = base := by
    rw [runs_eq_of_not_mem hopRun
      (residueBankOp_smallFootprint regs op)
      (bankSlot_not_mem_residueScratch regs 2 (by decide)
        (by decide))]
    exact hreadBase
  have hopBasePred :
      afterOp regs.bank.basePred = base - 1 := by
    rw [runs_eq_of_not_mem hopRun
      (residueBankOp_smallFootprint regs op)
      (bankSlot_not_mem_residueScratch regs 3 (by decide)
        (by decide))]
    exact hreadBasePred
  have hopOne : afterOp regs.bank.one = 1 := by
    rw [runs_eq_of_not_mem hopRun
      (residueBankOp_smallFootprint regs op)
      (bankSlot_not_mem_residueScratch regs 6 (by decide)
        (by decide))]
    exact hreadOne
  have hopUpdated :
      afterOp regs.bank.replacement = updated := by
    change afterOp (regs.index 11) = updated
    simp [afterOp, RuntimeArithmetic.reduceResultStore,
      ResidueBankRegisters.reduceRegisters,
      regs.index_ne (first := 11) (second := 5) (by decide)]
  have hopModulus :
      afterOp regs.modulus = modulus := by
    rw [runs_eq_of_not_mem hopRun
      (residueBankOp_smallFootprint regs op)
      (extra_not_mem_residueScratch regs 12 (by omega))]
    exact hreadModulus
  have hopModulusPred :
      afterOp regs.modulusPred = modulus - 1 := by
    rw [runs_eq_of_not_mem hopRun
      (residueBankOp_smallFootprint regs op)
      (extra_not_mem_residueScratch regs 13 (by omega))]
    exact hreadModulusPred
  have hopOperand :
      afterOp regs.operand = operand := by
    rw [runs_eq_of_not_mem hopRun
      (residueBankOp_smallFootprint regs op)
      (extra_not_mem_residueScratch regs 14 (by omega))]
    exact hreadOperand
  have hopSaved :
      afterOp regs.savedIndex = index := by
    rw [runs_eq_of_not_mem hopRun
      (residueBankOp_smallFootprint regs op)
      (extra_not_mem_residueScratch regs 15 (by omega))]
    exact hreadSaved
  let indexZero :=
    (Basic.imm regs.bank.indexCount 0).exec afterOp
  let afterIndex :=
    (Basic.add regs.bank.indexCount regs.savedIndex
      regs.bank.indexCount).exec indexZero
  have hrestoreIndexRun :
      Runs (restoreBankIndex regs) afterOp afterIndex := by
    exact Runs.seq (Runs.basic _ _) (Runs.basic _ _)
  have hindexWord :
      afterIndex regs.bank.word = word := by
    rw [runs_eq_of_not_mem hrestoreIndexRun
      (restoreBankIndex_smallFootprint regs)]
    · exact hopWord
    · simpa only [Finset.mem_singleton] using
        regs.bank.index_ne (first := 0) (second := 8) (by decide)
  have hindexBase :
      afterIndex regs.bank.base = base := by
    rw [runs_eq_of_not_mem hrestoreIndexRun
      (restoreBankIndex_smallFootprint regs)]
    · exact hopBase
    · simpa only [Finset.mem_singleton] using
        regs.bank.index_ne (first := 2) (second := 8) (by decide)
  have hindexBasePred :
      afterIndex regs.bank.basePred = base - 1 := by
    rw [runs_eq_of_not_mem hrestoreIndexRun
      (restoreBankIndex_smallFootprint regs)]
    · exact hopBasePred
    · simpa only [Finset.mem_singleton] using
        regs.bank.index_ne (first := 3) (second := 8) (by decide)
  have hindexOne :
      afterIndex regs.bank.one = 1 := by
    rw [runs_eq_of_not_mem hrestoreIndexRun
      (restoreBankIndex_smallFootprint regs)]
    · exact hopOne
    · simpa only [Finset.mem_singleton] using
        regs.bank.index_ne (first := 6) (second := 8) (by decide)
  have hindexIndex :
      afterIndex regs.bank.indexCount = index := by
    have hne :=
      bankAddress_ne_extra regs 8 15 (by omega)
    change regs.index 8 ≠ regs.index 15 at hne
    change afterOp (regs.index 15) = index at hopSaved
    simp [afterIndex, indexZero, Basic.exec, hne.symm,
      hopSaved]
  have hindexUpdated :
      afterIndex regs.bank.replacement = updated := by
    rw [runs_eq_of_not_mem hrestoreIndexRun
      (restoreBankIndex_smallFootprint regs)]
    · exact hopUpdated
    · simpa only [Finset.mem_singleton] using
        regs.bank.index_ne (first := 11) (second := 8) (by decide)
  have hindexModulus :
      afterIndex regs.modulus = modulus := by
    rw [runs_eq_of_not_mem hrestoreIndexRun
      (restoreBankIndex_smallFootprint regs)]
    · exact hopModulus
    · simpa only [Finset.mem_singleton] using
        (bankAddress_ne_extra regs 8 12 (by omega)).symm
  have hindexModulusPred :
      afterIndex regs.modulusPred = modulus - 1 := by
    rw [runs_eq_of_not_mem hrestoreIndexRun
      (restoreBankIndex_smallFootprint regs)]
    · exact hopModulusPred
    · simpa only [Finset.mem_singleton] using
        (bankAddress_ne_extra regs 8 13 (by omega)).symm
  have hindexOperand :
      afterIndex regs.operand = operand := by
    rw [runs_eq_of_not_mem hrestoreIndexRun
      (restoreBankIndex_smallFootprint regs)]
    · exact hopOperand
    · simpa only [Finset.mem_singleton] using
        (bankAddress_ne_extra regs 8 14 (by omega)).symm
  have hindexSaved :
      afterIndex regs.savedIndex = index := by
    rw [runs_eq_of_not_mem hrestoreIndexRun
      (restoreBankIndex_smallFootprint regs)]
    · exact hopSaved
    · simpa only [Finset.mem_singleton] using
        (bankAddress_ne_extra regs 8 15 (by omega)).symm
  obtain ⟨final, hreplace, hfinalWord, hfinalBuffer,
      hfinalIndex, hfinalCompleted, hfinalResult, hfinalBase,
      hfinalBasePred, hfinalOne, hfinalReplacement⟩ :=
    bankReplace_runs_internal regs.bank afterIndex base word index
      updated hbase hindexWord hindexBase hindexBasePred hindexOne
      hindexIndex hindexUpdated
  have hfinalModulus :
      final regs.modulus = modulus := by
    rw [runs_eq_of_not_mem hreplace
      (bankReplace_residueFootprint regs.bank)
      (residueExtra_not_mem_bankFootprint regs 12 (by omega))]
    exact hindexModulus
  have hfinalModulusPred :
      final regs.modulusPred = modulus - 1 := by
    rw [runs_eq_of_not_mem hreplace
      (bankReplace_residueFootprint regs.bank)
      (residueExtra_not_mem_bankFootprint regs 13 (by omega))]
    exact hindexModulusPred
  have hfinalOperand :
      final regs.operand = operand := by
    rw [runs_eq_of_not_mem hreplace
      (bankReplace_residueFootprint regs.bank)
      (residueExtra_not_mem_bankFootprint regs 14 (by omega))]
    exact hindexOperand
  have hfinalSaved :
      final regs.savedIndex = index := by
    rw [runs_eq_of_not_mem hreplace
      (bankReplace_residueFootprint regs.bank)
      (residueExtra_not_mem_bankFootprint regs 15 (by omega))]
    exact hindexSaved
  have hrun : Runs (bankUpdateAt regs op) store final := by
    simpa [bankUpdateAt, Cmd.seqList] using
      Runs.seq hsaveRun
        (Runs.seq hread
          (Runs.seq hopRun
            (Runs.seq hrestoreIndexRun hreplace)))
  exact ⟨final, hrun, hfinalWord, hfinalBuffer,
    hfinalIndex, hfinalCompleted, hfinalResult, hfinalBase,
    hfinalBasePred, hfinalOne, hfinalReplacement,
    hfinalModulus, hfinalModulusPred, hfinalOperand,
    hfinalSaved⟩

theorem bankUpdateAt_invariantRuns_internal
    (regs : ResidueBankRegisters) (op : ResidueBankOp)
    (allowed : Finset ℕ) (bound : ℕ)
    (store : Store)
    (base word index modulus operand digitCount : ℕ)
    (hbase : 0 < base)
    (hmodulus : 0 < modulus)
    (hmodulusBase : modulus ≤ base)
    (hword : store regs.bank.word = word)
    (hbaseValue : store regs.bank.base = base)
    (hbasePred : store regs.bank.basePred = base - 1)
    (hone : store regs.bank.one = 1)
    (hindex : store regs.bank.indexCount = index)
    (hmodulusValue : store regs.modulus = modulus)
    (hmodulusPred : store regs.modulusPred = modulus - 1)
    (hoperand : store regs.operand = operand)
    (hwordCapacity : word < base ^ digitCount)
    (hindexCapacity : index < digitCount)
    (hpackedBound : base ^ digitCount ≤ bound)
    (hbaseBound : base ≤ bound)
    (hindexBound : index ≤ bound)
    (hrawBound :
      op.rawApply (PackedDigits.digit base word index) operand ≤
        bound)
    (hstore : ValuesWithin allowed bound store) :
    ∃ final steps,
      InvariantRuns (ValuesWithin allowed bound)
        (bankUpdateAt regs op) store final steps ∧
      final regs.bank.word =
        replaceAt base word index
          (op.apply modulus
            (PackedDigits.digit base word index) operand) ∧
      final regs.bank.buffer = 0 ∧
      final regs.bank.indexCount = 0 ∧
      final regs.bank.completed = 0 ∧
      final regs.bank.result =
        PackedDigits.digit base word index ∧
      final regs.bank.base = base ∧
      final regs.bank.basePred = base - 1 ∧
      final regs.bank.one = 1 ∧
      final regs.bank.replacement =
        op.apply modulus
          (PackedDigits.digit base word index) operand ∧
      final regs.modulus = modulus ∧
      final regs.modulusPred = modulus - 1 ∧
      final regs.operand = operand ∧
      final regs.savedIndex = index := by
  let savedZero :=
    (Basic.imm regs.savedIndex 0).exec store
  let afterSave :=
    (Basic.add regs.savedIndex regs.bank.indexCount
      regs.savedIndex).exec savedZero
  have hsavedZeroInvariant :
      ValuesWithin allowed bound savedZero :=
    valuesWithin_imm hstore (Nat.zero_le bound)
  have hsavedZeroIndex :
      savedZero regs.bank.indexCount = index := by
    simp only [savedZero, Basic.exec]
    rw [Function.update_of_ne
      (bankAddress_ne_extra regs 8 15 (by omega))]
    exact hindex
  have hsavedZeroSaved : savedZero regs.savedIndex = 0 := by
    simp [savedZero, Basic.exec]
  have hsaveInvariant :
      ValuesWithin allowed bound afterSave := by
    apply valuesWithin_add hsavedZeroInvariant
    rw [hsavedZeroIndex, hsavedZeroSaved, Nat.add_zero]
    exact hindexBound
  have hsaveRun :
      InvariantRuns (ValuesWithin allowed bound)
        (saveBankIndex regs) store afterSave (1 + 1) := by
    exact InvariantRuns.seq
      (InvariantRuns.basic (Basic.imm regs.savedIndex 0) store
        hstore hsavedZeroInvariant)
      (InvariantRuns.basic
        (Basic.add regs.savedIndex regs.bank.indexCount
          regs.savedIndex)
        savedZero hsavedZeroInvariant hsaveInvariant)
  have hsaveRuns : Runs (saveBankIndex regs) store afterSave :=
    InvariantRuns.toRuns hsaveRun
  have hsaveWord : afterSave regs.bank.word = word := by
    rw [runs_eq_of_not_mem hsaveRuns
      (saveBankIndex_smallFootprint regs)]
    · exact hword
    · simpa only [Finset.mem_singleton] using
        bankAddress_ne_extra regs 0 15 (by omega)
  have hsaveBase : afterSave regs.bank.base = base := by
    rw [runs_eq_of_not_mem hsaveRuns
      (saveBankIndex_smallFootprint regs)]
    · exact hbaseValue
    · simpa only [Finset.mem_singleton] using
        bankAddress_ne_extra regs 2 15 (by omega)
  have hsaveBasePred :
      afterSave regs.bank.basePred = base - 1 := by
    rw [runs_eq_of_not_mem hsaveRuns
      (saveBankIndex_smallFootprint regs)]
    · exact hbasePred
    · simpa only [Finset.mem_singleton] using
        bankAddress_ne_extra regs 3 15 (by omega)
  have hsaveOne : afterSave regs.bank.one = 1 := by
    rw [runs_eq_of_not_mem hsaveRuns
      (saveBankIndex_smallFootprint regs)]
    · exact hone
    · simpa only [Finset.mem_singleton] using
        bankAddress_ne_extra regs 6 15 (by omega)
  have hsaveIndex :
      afterSave regs.bank.indexCount = index := by
    rw [runs_eq_of_not_mem hsaveRuns
      (saveBankIndex_smallFootprint regs)]
    · exact hindex
    · simpa only [Finset.mem_singleton] using
        bankAddress_ne_extra regs 8 15 (by omega)
  have hsaveModulus :
      afterSave regs.modulus = modulus := by
    rw [runs_eq_of_not_mem hsaveRuns
      (saveBankIndex_smallFootprint regs)]
    · exact hmodulusValue
    · simpa only [Finset.mem_singleton] using
        regs.index_ne (first := 12) (second := 15) (by decide)
  have hsaveModulusPred :
      afterSave regs.modulusPred = modulus - 1 := by
    rw [runs_eq_of_not_mem hsaveRuns
      (saveBankIndex_smallFootprint regs)]
    · exact hmodulusPred
    · simpa only [Finset.mem_singleton] using
        regs.index_ne (first := 13) (second := 15) (by decide)
  have hsaveOperand :
      afterSave regs.operand = operand := by
    rw [runs_eq_of_not_mem hsaveRuns
      (saveBankIndex_smallFootprint regs)]
    · exact hoperand
    · simpa only [Finset.mem_singleton] using
        regs.index_ne (first := 14) (second := 15) (by decide)
  have hsaveSaved :
      afterSave regs.savedIndex = index := by
    simp only [afterSave, Basic.exec, Function.update_self]
    rw [hsavedZeroIndex, hsavedZeroSaved, Nat.add_zero]
  have hindexCapacityLe : index ≤ digitCount :=
    Nat.le_of_lt hindexCapacity
  obtain ⟨afterRead, readSteps, hread, hreadWord, _,
      _, _, hreadResult, hreadBase, hreadBasePred, hreadOne,
      _⟩ :=
    bankRead_invariantRuns_internal regs.bank allowed bound
      afterSave base word index digitCount hbase hsaveWord hsaveBase
      hsaveBasePred hsaveOne hsaveIndex hwordCapacity
      hindexCapacityLe hpackedBound hbaseBound hindexBound
      hsaveInvariant
  have hreadRuns :
      Runs (bankRead regs.bank) afterSave afterRead :=
    InvariantRuns.toRuns hread
  have hreadInvariant :
      ValuesWithin allowed bound afterRead :=
    InvariantRuns.final hread
  have hreadModulus :
      afterRead regs.modulus = modulus := by
    rw [runs_eq_of_not_mem hreadRuns
      (bankRead_residueFootprint regs.bank)
      (residueExtra_not_mem_bankFootprint regs 12 (by omega))]
    exact hsaveModulus
  have hreadModulusPred :
      afterRead regs.modulusPred = modulus - 1 := by
    rw [runs_eq_of_not_mem hreadRuns
      (bankRead_residueFootprint regs.bank)
      (residueExtra_not_mem_bankFootprint regs 13 (by omega))]
    exact hsaveModulusPred
  have hreadOperand :
      afterRead regs.operand = operand := by
    rw [runs_eq_of_not_mem hreadRuns
      (bankRead_residueFootprint regs.bank)
      (residueExtra_not_mem_bankFootprint regs 14 (by omega))]
    exact hsaveOperand
  have hreadSaved :
      afterRead regs.savedIndex = index := by
    rw [runs_eq_of_not_mem hreadRuns
      (bankRead_residueFootprint regs.bank)
      (residueExtra_not_mem_bankFootprint regs 15 (by omega))]
    exact hsaveSaved
  let updated :=
    op.apply modulus (PackedDigits.digit base word index) operand
  let afterOp :=
    RuntimeArithmetic.reduceResultStore regs.reduceRegisters
      updated afterRead
  obtain ⟨opSteps, hop⟩ :=
    residueBankOp_invariantRuns op regs allowed bound afterRead
      modulus (PackedDigits.digit base word index) operand hmodulus
      hreadResult hreadOperand hreadModulus hreadModulusPred
      hrawBound hreadInvariant
  have hopRuns : Runs (op.command regs) afterRead afterOp :=
    InvariantRuns.toRuns hop
  have hopInvariant :
      ValuesWithin allowed bound afterOp :=
    InvariantRuns.final hop
  have hopWord : afterOp regs.bank.word = word := by
    rw [runs_eq_of_not_mem hopRuns
      (residueBankOp_smallFootprint regs op)
      (bankSlot_not_mem_residueScratch regs 0 (by decide)
        (by decide))]
    exact hreadWord
  have hopBase : afterOp regs.bank.base = base := by
    rw [runs_eq_of_not_mem hopRuns
      (residueBankOp_smallFootprint regs op)
      (bankSlot_not_mem_residueScratch regs 2 (by decide)
        (by decide))]
    exact hreadBase
  have hopBasePred :
      afterOp regs.bank.basePred = base - 1 := by
    rw [runs_eq_of_not_mem hopRuns
      (residueBankOp_smallFootprint regs op)
      (bankSlot_not_mem_residueScratch regs 3 (by decide)
        (by decide))]
    exact hreadBasePred
  have hopOne : afterOp regs.bank.one = 1 := by
    rw [runs_eq_of_not_mem hopRuns
      (residueBankOp_smallFootprint regs op)
      (bankSlot_not_mem_residueScratch regs 6 (by decide)
        (by decide))]
    exact hreadOne
  have hopUpdated :
      afterOp regs.bank.replacement = updated := by
    change afterOp (regs.index 11) = updated
    simp [afterOp, RuntimeArithmetic.reduceResultStore,
      ResidueBankRegisters.reduceRegisters,
      regs.index_ne (first := 11) (second := 5) (by decide)]
  have hopModulus :
      afterOp regs.modulus = modulus := by
    rw [runs_eq_of_not_mem hopRuns
      (residueBankOp_smallFootprint regs op)
      (extra_not_mem_residueScratch regs 12 (by omega))]
    exact hreadModulus
  have hopModulusPred :
      afterOp regs.modulusPred = modulus - 1 := by
    rw [runs_eq_of_not_mem hopRuns
      (residueBankOp_smallFootprint regs op)
      (extra_not_mem_residueScratch regs 13 (by omega))]
    exact hreadModulusPred
  have hopOperand :
      afterOp regs.operand = operand := by
    rw [runs_eq_of_not_mem hopRuns
      (residueBankOp_smallFootprint regs op)
      (extra_not_mem_residueScratch regs 14 (by omega))]
    exact hreadOperand
  have hopSaved :
      afterOp regs.savedIndex = index := by
    rw [runs_eq_of_not_mem hopRuns
      (residueBankOp_smallFootprint regs op)
      (extra_not_mem_residueScratch regs 15 (by omega))]
    exact hreadSaved
  let indexZero :=
    (Basic.imm regs.bank.indexCount 0).exec afterOp
  let afterIndex :=
    (Basic.add regs.bank.indexCount regs.savedIndex
      regs.bank.indexCount).exec indexZero
  have hindexZeroInvariant :
      ValuesWithin allowed bound indexZero :=
    valuesWithin_imm hopInvariant (Nat.zero_le bound)
  have hindexZeroSaved :
      indexZero regs.savedIndex = index := by
    simp only [indexZero, Basic.exec]
    rw [Function.update_of_ne
      (bankAddress_ne_extra regs 8 15 (by omega)).symm]
    exact hopSaved
  have hindexZeroIndex :
      indexZero regs.bank.indexCount = 0 := by
    simp [indexZero, Basic.exec]
  have hindexInvariant :
      ValuesWithin allowed bound afterIndex := by
    apply valuesWithin_add hindexZeroInvariant
    rw [hindexZeroSaved, hindexZeroIndex, Nat.add_zero]
    exact hindexBound
  have hrestoreIndexRun :
      InvariantRuns (ValuesWithin allowed bound)
        (restoreBankIndex regs) afterOp afterIndex (1 + 1) :=
    InvariantRuns.seq
      (InvariantRuns.basic
        (Basic.imm regs.bank.indexCount 0) afterOp
        hopInvariant hindexZeroInvariant)
      (InvariantRuns.basic
        (Basic.add regs.bank.indexCount regs.savedIndex
          regs.bank.indexCount)
        indexZero hindexZeroInvariant hindexInvariant)
  have hrestoreIndexRuns :
      Runs (restoreBankIndex regs) afterOp afterIndex :=
    InvariantRuns.toRuns hrestoreIndexRun
  have hindexWord :
      afterIndex regs.bank.word = word := by
    rw [runs_eq_of_not_mem hrestoreIndexRuns
      (restoreBankIndex_smallFootprint regs)]
    · exact hopWord
    · simpa only [Finset.mem_singleton] using
        regs.bank.index_ne (first := 0) (second := 8) (by decide)
  have hindexBase :
      afterIndex regs.bank.base = base := by
    rw [runs_eq_of_not_mem hrestoreIndexRuns
      (restoreBankIndex_smallFootprint regs)]
    · exact hopBase
    · simpa only [Finset.mem_singleton] using
        regs.bank.index_ne (first := 2) (second := 8) (by decide)
  have hindexBasePred :
      afterIndex regs.bank.basePred = base - 1 := by
    rw [runs_eq_of_not_mem hrestoreIndexRuns
      (restoreBankIndex_smallFootprint regs)]
    · exact hopBasePred
    · simpa only [Finset.mem_singleton] using
        regs.bank.index_ne (first := 3) (second := 8) (by decide)
  have hindexOne :
      afterIndex regs.bank.one = 1 := by
    rw [runs_eq_of_not_mem hrestoreIndexRuns
      (restoreBankIndex_smallFootprint regs)]
    · exact hopOne
    · simpa only [Finset.mem_singleton] using
        regs.bank.index_ne (first := 6) (second := 8) (by decide)
  have hindexIndex :
      afterIndex regs.bank.indexCount = index := by
    simp only [afterIndex, Basic.exec, Function.update_self]
    rw [hindexZeroSaved, hindexZeroIndex, Nat.add_zero]
  have hindexUpdated :
      afterIndex regs.bank.replacement = updated := by
    rw [runs_eq_of_not_mem hrestoreIndexRuns
      (restoreBankIndex_smallFootprint regs)]
    · exact hopUpdated
    · simpa only [Finset.mem_singleton] using
        regs.bank.index_ne (first := 11) (second := 8) (by decide)
  have hupdatedModulus : updated < modulus := by
    cases op <;>
      exact Nat.mod_lt _ hmodulus
  have hupdatedDigit : updated < base :=
    hupdatedModulus.trans_le hmodulusBase
  have hupdatedBound : updated ≤ bound :=
    (Nat.le_of_lt hupdatedDigit).trans hbaseBound
  obtain ⟨final, replaceSteps, hreplace, _, _, _, _, _, _,
      _, _, _⟩ :=
    bankReplace_invariantRuns_internal regs.bank allowed bound
      afterIndex base word index updated digitCount hbase hindexWord
      hindexBase hindexBasePred hindexOne hindexIndex hindexUpdated
      hwordCapacity hindexCapacity hupdatedDigit hpackedBound
      hbaseBound hindexBound hupdatedBound hindexInvariant
  have hrun :
      InvariantRuns (ValuesWithin allowed bound)
        (bankUpdateAt regs op) store final
        ((1 + 1) +
          (readSteps + (opSteps + ((1 + 1) + replaceSteps)))) := by
    simpa [bankUpdateAt, Cmd.seqList] using
      InvariantRuns.seq hsaveRun
        (InvariantRuns.seq hread
          (InvariantRuns.seq hop
            (InvariantRuns.seq hrestoreIndexRun hreplace)))
  obtain ⟨semanticFinal, hsemanticRun, hfinalWord,
      hfinalBuffer, hfinalIndex, hfinalCompleted, hfinalResult,
      hfinalBase, hfinalBasePred, hfinalOne,
      hfinalReplacement, hfinalModulus, hfinalModulusPred,
      hfinalOperand, hfinalSaved⟩ :=
    bankUpdateAt_runs_internal regs op store base word index
      modulus operand hbase hmodulus hword hbaseValue hbasePred hone
      hindex hmodulusValue hmodulusPred hoperand
  have hfinalEq : final = semanticFinal :=
    runs_final_unique (InvariantRuns.toRuns hrun) hsemanticRun
  subst semanticFinal
  exact ⟨final,
    (1 + 1) +
      (readSteps + (opSteps + ((1 + 1) + replaceSteps))),
    hrun, hfinalWord, hfinalBuffer, hfinalIndex, hfinalCompleted,
    hfinalResult, hfinalBase, hfinalBasePred, hfinalOne,
    hfinalReplacement, hfinalModulus, hfinalModulusPred,
    hfinalOperand, hfinalSaved⟩

theorem bankRead_sourceWritesWithin_internal (regs : BankRegisters) :
    RAM.Structured.Footprint.CmdWritesWithin
      regs.footprint (bankRead regs) := by
  simp [bankRead, bankSeek, bankForward, bankForwardBody,
    bankRestore, bankRestoreBody, peek, pop, popBody, popTestOp,
    push, RuntimeArithmetic.reduce, RuntimeArithmetic.reduceBody,
    RuntimeArithmetic.reduceTestOp, StackRegisters.reduceRegisters,
    Cmd.seqList, RAM.Structured.Footprint.CmdWritesWithin,
    RAM.Structured.Footprint.BasicWritesWithin]

theorem bankReplace_sourceWritesWithin_internal (regs : BankRegisters) :
    RAM.Structured.Footprint.CmdWritesWithin
      regs.footprint (bankReplace regs) := by
  simp [bankReplace, bankSeek, bankForward, bankForwardBody,
    bankRestore, bankRestoreBody, peek, pop, popBody, popTestOp,
    push, RuntimeArithmetic.reduce, RuntimeArithmetic.reduceBody,
    RuntimeArithmetic.reduceTestOp, StackRegisters.reduceRegisters,
    Cmd.seqList, RAM.Structured.Footprint.CmdWritesWithin,
    RAM.Structured.Footprint.BasicWritesWithin]

theorem bankUpdateAt_sourceWritesWithin_internal
    (regs : ResidueBankRegisters) (op : ResidueBankOp) :
    RAM.Structured.Footprint.CmdWritesWithin
      regs.footprint (bankUpdateAt regs op) := by
  cases op <;>
    simp [bankUpdateAt, saveBankIndex, restoreBankIndex,
      ResidueBankOp.command, bankRead, bankSeek, bankForward,
      bankForwardBody, bankRestore, bankRestoreBody, bankReplace,
      peek, pop, popBody, popTestOp, push,
      RuntimeArithmetic.addMod, RuntimeArithmetic.mulMod,
      RuntimeArithmetic.reduce, RuntimeArithmetic.reduceBody,
      RuntimeArithmetic.reduceTestOp,
      StackRegisters.reduceRegisters,
      ResidueBankRegisters.reduceRegisters,
      Cmd.seqList, RAM.Structured.Footprint.CmdWritesWithin,
      RAM.Structured.Footprint.BasicWritesWithin,
      ResidueBankRegisters.footprint]

theorem bankRead_writesWithin_internal (regs : BankRegisters) :
    RegisterStore.DenseOverlay.FixedRegisters.Footprint.ProgramWritesWithin
      (bankRead regs).compile regs.footprint :=
  RAM.Structured.Footprint.programWritesWithin_compile
    (bankRead_sourceWritesWithin_internal regs)

theorem bankReplace_writesWithin_internal (regs : BankRegisters) :
    RegisterStore.DenseOverlay.FixedRegisters.Footprint.ProgramWritesWithin
      (bankReplace regs).compile regs.footprint :=
  RAM.Structured.Footprint.programWritesWithin_compile
    (bankReplace_sourceWritesWithin_internal regs)

theorem bankUpdateAt_writesWithin_internal
    (regs : ResidueBankRegisters) (op : ResidueBankOp) :
    RegisterStore.DenseOverlay.FixedRegisters.Footprint.ProgramWritesWithin
      (bankUpdateAt regs op).compile regs.footprint :=
  RAM.Structured.Footprint.programWritesWithin_compile
    (bankUpdateAt_sourceWritesWithin_internal regs op)

theorem bankUpdateAt_noStore_internal
    (regs : ResidueBankRegisters) (op : ResidueBankOp) :
    cmdNoStore (bankUpdateAt regs op) := by
  cases op <;>
    simp [bankUpdateAt, saveBankIndex, restoreBankIndex,
      ResidueBankOp.command, bankRead, bankSeek, bankForward,
      bankForwardBody, bankRestore, bankRestoreBody, bankReplace,
      peek, pop, popBody, popTestOp, push,
      RuntimeArithmetic.addMod, RuntimeArithmetic.mulMod,
      RuntimeArithmetic.reduce, RuntimeArithmetic.reduceBody,
      RuntimeArithmetic.reduceTestOp, Cmd.seqList, cmdNoStore,
      basicNoStore]

theorem bankScaleRegister_sourceWritesWithin_internal
    (regs : ResidueScaleRegisters) :
    RAM.Structured.Footprint.CmdWritesWithin
      regs.footprint (bankScaleRegister regs) := by
  simp only [bankScaleRegister, bankScaleRegisterBody,
    advanceScaleChunk,
    RAM.Structured.Footprint.CmdWritesWithin,
    RAM.Structured.Footprint.BasicWritesWithin]
  constructor
  · apply cmdWritesWithin_mono
      (scaleBankFootprint_subset regs)
    simpa [bankScaleAt] using
      bankUpdateAt_sourceWritesWithin_internal regs.bank .mul
  · constructor
    · exact regs.index_mem_footprint 16
    · exact regs.index_mem_footprint 8

theorem bankScaleRegister_writesWithin_internal
    (regs : ResidueScaleRegisters) :
    RegisterStore.DenseOverlay.FixedRegisters.Footprint.ProgramWritesWithin
      (bankScaleRegister regs).compile regs.footprint :=
  RAM.Structured.Footprint.programWritesWithin_compile
    (bankScaleRegister_sourceWritesWithin_internal regs)

theorem bankScaleRegister_noStore_internal
    (regs : ResidueScaleRegisters) :
    cmdNoStore (bankScaleRegister regs) := by
  simp only [bankScaleRegister, bankScaleRegisterBody,
    advanceScaleChunk, cmdNoStore, basicNoStore, and_true]
  simpa [bankScaleAt] using
    bankUpdateAt_noStore_internal regs.bank .mul

theorem residueBankOp_lt_internal
    {op : ResidueBankOp} {modulus current operand base : ℕ}
    (hmodulus : 0 < modulus)
    (hmodulusBase : modulus ≤ base) :
    op.apply modulus current operand < base := by
  apply lt_of_lt_of_le _ hmodulusBase
  cases op <;>
    exact Nat.mod_lt _ hmodulus

theorem bankUpdateAt_otherDigit_runs_internal
    (regs : ResidueBankRegisters) (op : ResidueBankOp)
    (store : Store)
    (base word index otherIndex modulus operand : ℕ)
    (hbase : 0 < base)
    (hmodulus : 0 < modulus)
    (hmodulusBase : modulus ≤ base)
    (hword : store regs.bank.word = word)
    (hbaseValue : store regs.bank.base = base)
    (hbasePred : store regs.bank.basePred = base - 1)
    (hone : store regs.bank.one = 1)
    (hindex : store regs.bank.indexCount = index)
    (hmodulusValue : store regs.modulus = modulus)
    (hmodulusPred : store regs.modulusPred = modulus - 1)
    (hoperand : store regs.operand = operand)
    (hother : otherIndex ≠ index) :
    ∃ final,
      Runs (bankUpdateAt regs op) store final ∧
      PackedDigits.digit base (final regs.bank.word) otherIndex =
        PackedDigits.digit base word otherIndex := by
  obtain ⟨final, hrun, hfinalWord, _⟩ :=
    bankUpdateAt_runs_internal regs op store base word index modulus
      operand hbase hmodulus hword hbaseValue hbasePred hone hindex
      hmodulusValue hmodulusPred hoperand
  refine ⟨final, hrun, ?_⟩
  rw [hfinalWord]
  exact replaceAt_digit_ne_internal hbase
    (residueBankOp_lt_internal hmodulus hmodulusBase) hother

theorem bankUpdateAt_word_lt_pow_internal
    {op : ResidueBankOp}
    {base word count index modulus operand : ℕ}
    (hbase : 0 < base)
    (hword : word < base ^ count)
    (hindex : index < count)
    (hmodulus : 0 < modulus)
    (hmodulusBase : modulus ≤ base) :
    replaceAt base word index
        (op.apply modulus
          (PackedDigits.digit base word index) operand) <
      base ^ count :=
  replaceAt_lt_pow_internal hbase hword hindex
    (residueBankOp_lt_internal hmodulus hmodulusBase)

theorem bankUpdateAt_word_size_le_internal
    {op : ResidueBankOp}
    {base word count index modulus operand width : ℕ}
    (hbase : 0 < base)
    (hword : word < base ^ count)
    (hindex : index < count)
    (hmodulus : 0 < modulus)
    (hmodulusBase : modulus ≤ base)
    (hbaseWidth : base ≤ 2 ^ width) :
    (replaceAt base word index
      (op.apply modulus
        (PackedDigits.digit base word index) operand)).size ≤
      count * width :=
  PackedDigits.size_le_count_mul_width
    (bankUpdateAt_word_lt_pow_internal hbase hword hindex
      hmodulus hmodulusBase)
    hbaseWidth

theorem residueBankIndex_lt_internal
    {workTapeCount : ℕ}
    (tm : TM workTapeCount) (blockLength : ℕ)
    (register :
      Fin (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount + 1))
    (chunk :
      Fin
        (TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
          (NeighborhoodExecutableEvaluation.payloadWidth tm blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount))) :
    residueBankIndex tm blockLength register chunk <
      (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount + 1) *
        TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
          (NeighborhoodExecutableEvaluation.payloadWidth tm blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn
            workTapeCount) := by
  let count :=
    TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
      (NeighborhoodExecutableEvaluation.payloadWidth tm blockLength)
      (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount)
  calc
    residueBankIndex tm blockLength register chunk <
        register.val * count + count := by
      unfold residueBankIndex
      exact Nat.add_lt_add_left chunk.isLt _
    _ = (register.val + 1) * count := by ring
    _ ≤
        (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount + 1) *
          count :=
      Nat.mul_le_mul_right count (Nat.succ_le_of_lt register.isLt)

theorem residueBankIndex_eq_iff_internal
    {workTapeCount : ℕ}
    (tm : TM workTapeCount) (blockLength : ℕ)
    (firstRegister secondRegister :
      Fin
        (NeighborhoodExecutableEvaluation.graphFanIn
          workTapeCount + 1))
    (firstChunk secondChunk :
      Fin
        (TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
          (NeighborhoodExecutableEvaluation.payloadWidth tm blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn
            workTapeCount))) :
    residueBankIndex tm blockLength firstRegister firstChunk =
        residueBankIndex tm blockLength secondRegister secondChunk ↔
      firstRegister = secondRegister ∧ firstChunk = secondChunk := by
  constructor
  · intro heq
    let count :=
      TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
        (NeighborhoodExecutableEvaluation.payloadWidth tm blockLength)
        (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount)
    change firstRegister.val * count + firstChunk.val =
      secondRegister.val * count + secondChunk.val at heq
    have hcount : 0 < count :=
      lt_of_le_of_lt (Nat.zero_le firstChunk.val) firstChunk.isLt
    have hfirstMod :
        (firstRegister.val * count + firstChunk.val) % count =
          firstChunk.val := by
      rw [Nat.mul_comm firstRegister.val count,
        Nat.mul_add_mod_self_left,
        Nat.mod_eq_of_lt firstChunk.isLt]
    have hsecondMod :
        (secondRegister.val * count + secondChunk.val) % count =
          secondChunk.val := by
      rw [Nat.mul_comm secondRegister.val count,
        Nat.mul_add_mod_self_left,
        Nat.mod_eq_of_lt secondChunk.isLt]
    have hchunkVal : firstChunk.val = secondChunk.val := by
      rw [← hfirstMod, heq, hsecondMod]
    have hfirstDiv :
        (firstRegister.val * count + firstChunk.val) / count =
          firstRegister.val := by
      rw [Nat.mul_comm firstRegister.val count,
        Nat.mul_add_div hcount,
        Nat.div_eq_of_lt firstChunk.isLt, Nat.add_zero]
    have hsecondDiv :
        (secondRegister.val * count + secondChunk.val) / count =
          secondRegister.val := by
      rw [Nat.mul_comm secondRegister.val count,
        Nat.mul_add_div hcount,
        Nat.div_eq_of_lt secondChunk.isLt, Nat.add_zero]
    have hregisterVal :
        firstRegister.val = secondRegister.val := by
      rw [← hfirstDiv, heq, hsecondDiv]
    exact ⟨Fin.ext hregisterVal, Fin.ext hchunkVal⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem representsResidueBank_replaceAt_internal
    {workTapeCount : ℕ}
    (tm : TM workTapeCount) (blockLength base word : ℕ)
    (regs :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm blockLength)
    (register :
      Fin
        (NeighborhoodExecutableEvaluation.graphFanIn
          workTapeCount + 1))
    (chunk :
      Fin
        (TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
          (NeighborhoodExecutableEvaluation.payloadWidth tm blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn
            workTapeCount)))
    (value : ℕ)
    (hrep :
      RepresentsResidueBank tm blockLength base word regs)
    (hbase : 0 < base) (hvalue : value < base) :
    RepresentsResidueBank tm blockLength base
      (replaceAt base word
        (residueBankIndex tm blockLength register chunk) value)
      (updateResidueCoordinate
        tm blockLength regs register chunk value) := by
  intro currentRegister currentChunk
  by_cases hsame :
      currentRegister = register ∧ currentChunk = chunk
  · rcases hsame with ⟨rfl, rfl⟩
    rw [replaceAt_digit_eq_internal hbase hvalue]
    simp [updateResidueCoordinate]
  · have hcoordinate :
        residueBankIndex tm blockLength currentRegister currentChunk ≠
          residueBankIndex tm blockLength register chunk := by
      intro heq
      exact hsame
        ((residueBankIndex_eq_iff_internal tm blockLength
          currentRegister register currentChunk chunk).mp heq)
    rw [replaceAt_digit_ne_internal hbase hvalue hcoordinate]
    rw [hrep currentRegister currentChunk]
    by_cases hregister : currentRegister = register
    · subst currentRegister
      have hchunk : currentChunk ≠ chunk := by
        intro heq
        exact hsame ⟨rfl, heq⟩
      simp [updateResidueCoordinate, hchunk]
    · simp [updateResidueCoordinate, hregister]

theorem bankUpdateAt_represents_runs_internal
    {workTapeCount : ℕ}
    (tm : TM workTapeCount) (blockLength : ℕ)
    (bankRegs : ResidueBankRegisters) (op : ResidueBankOp)
    (store : Store) (base word modulus operand : ℕ)
    (residueRegs :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm blockLength)
    (register :
      Fin
        (NeighborhoodExecutableEvaluation.graphFanIn
          workTapeCount + 1))
    (chunk :
      Fin
        (TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
          (NeighborhoodExecutableEvaluation.payloadWidth tm blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn
            workTapeCount)))
    (hbase : 0 < base)
    (hmodulus : 0 < modulus)
    (hmodulusBase : modulus ≤ base)
    (hword : store bankRegs.bank.word = word)
    (hbaseValue : store bankRegs.bank.base = base)
    (hbasePred : store bankRegs.bank.basePred = base - 1)
    (hone : store bankRegs.bank.one = 1)
    (hindex :
      store bankRegs.bank.indexCount =
        residueBankIndex tm blockLength register chunk)
    (hmodulusValue : store bankRegs.modulus = modulus)
    (hmodulusPred :
      store bankRegs.modulusPred = modulus - 1)
    (hoperand : store bankRegs.operand = operand)
    (hrep :
      RepresentsResidueBank
        tm blockLength base word residueRegs) :
    ∃ final,
      Runs (bankUpdateAt bankRegs op) store final ∧
      RepresentsResidueBank tm blockLength base
        (final bankRegs.bank.word)
        (updateResidueCoordinate tm blockLength residueRegs register
          chunk
          (op.apply modulus
            (residueRegs register chunk) operand)) := by
  obtain ⟨final, hrun, hfinalWord, _⟩ :=
    bankUpdateAt_runs_internal bankRegs op store base word
      (residueBankIndex tm blockLength register chunk) modulus operand
      hbase hmodulus hword hbaseValue hbasePred hone hindex
      hmodulusValue hmodulusPred hoperand
  rw [hrep register chunk] at hfinalWord
  refine ⟨final, hrun, ?_⟩
  rw [hfinalWord]
  exact representsResidueBank_replaceAt_internal
    tm blockLength base word residueRegs register chunk
      (op.apply modulus (residueRegs register chunk) operand)
      hrep hbase
      (residueBankOp_lt_internal hmodulus hmodulusBase)

theorem residueBankIndex_lt_instance_internal
    {workTapeCount : ℕ}
    (tm : TM workTapeCount) (inst : ResidueInstance tm)
    (register :
      Fin (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount + 1))
    (chunk :
      Fin
        (TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
          (NeighborhoodExecutableEvaluation.payloadWidth
            tm inst.blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount))) :
    residueBankIndex tm inst.blockLength register chunk <
      bankDigitCount tm.Q workTapeCount inst.candidateTime := by
  calc
    residueBankIndex tm inst.blockLength register chunk <
        (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount + 1) *
          TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
            (NeighborhoodExecutableEvaluation.payloadWidth
              tm inst.blockLength)
            (NeighborhoodExecutableEvaluation.graphFanIn
              workTapeCount) :=
      residueBankIndex_lt_internal tm inst.blockLength register chunk
    _ = bankDigitCount tm.Q workTapeCount inst.candidateTime := by
      rw [inst.blockLength_eq]
      simp [bankDigitCount, WorkspaceAccounting.fanIn,
        WorkspaceAccounting.chunkCount,
        WorkspaceAccounting.booleanWidth,
        NeighborhoodExecutableEvaluation.graphFanIn,
        NeighborhoodExecutableEvaluation.payloadWidth,
        NeighborhoodEvaluator.candidateBlockLength,
        NeighborhoodEvaluator.fanIn,
        WorkspaceAccounting.blockLength,
        ComputationGraph.CompactEncoding.width_eq]

theorem residueBankAdd_eq_addAt_internal
    {workTapeCount : ℕ}
    (tm : TM workTapeCount) (blockLength : ℕ)
    (regs :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm blockLength)
    (register :
      Fin
        (NeighborhoodExecutableEvaluation.graphFanIn
          workTapeCount + 1))
    (value :
      NeighborhoodExecutableEvaluation.ResidueValue tm blockLength)
    (chunk :
      Fin
        (TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
          (NeighborhoodExecutableEvaluation.payloadWidth tm blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn
            workTapeCount))) :
    ResidueBankOp.add.apply
        (NeighborhoodExecutableEvaluation.modulus tm blockLength)
        (regs register chunk) (value chunk) =
      (NeighborhoodExecutableEvaluation.Residue.addAt
        tm blockLength regs register value) register chunk := by
  simp [ResidueBankOp.apply,
    NeighborhoodExecutableEvaluation.Residue.addAt,
    NeighborhoodExecutableEvaluation.Residue.addValue,
    TreeEval.CookMertz.PrimeField.Runtime.add,
    TreeEval.CookMertz.PrimeField.Runtime.addInput,
    TreeEval.CookMertz.PrimeField.Runtime.normalize,
    Nat.add_mod]

theorem residueBankScale_eq_scaleAt_internal
    {workTapeCount : ℕ}
    (tm : TM workTapeCount) (blockLength scalar : ℕ)
    (regs :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm blockLength)
    (register :
      Fin
        (NeighborhoodExecutableEvaluation.graphFanIn
          workTapeCount + 1))
    (chunk :
      Fin
        (TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
          (NeighborhoodExecutableEvaluation.payloadWidth tm blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn
            workTapeCount))) :
    ResidueBankOp.mul.apply
        (NeighborhoodExecutableEvaluation.modulus tm blockLength)
        (regs register chunk) scalar =
      (NeighborhoodExecutableEvaluation.Residue.scaleAt
        tm blockLength scalar regs register) register chunk := by
  simp [ResidueBankOp.apply,
    NeighborhoodExecutableEvaluation.Residue.scaleAt,
    NeighborhoodExecutableEvaluation.Residue.scaleValue,
    TreeEval.CookMertz.PrimeField.Runtime.mul,
    TreeEval.CookMertz.PrimeField.Runtime.mulInput,
    TreeEval.CookMertz.PrimeField.Runtime.normalize,
    Nat.mul_mod, Nat.mul_comm]

theorem scaleResiduePrefix_zero_internal
    {workTapeCount : ℕ}
    (tm : TM workTapeCount) (blockLength scalar : ℕ)
    (regs :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm blockLength)
    (register :
      Fin
        (NeighborhoodExecutableEvaluation.graphFanIn
          workTapeCount + 1)) :
    scaleResiduePrefix tm blockLength scalar regs register 0 =
      regs := by
  funext currentRegister chunk
  simp [scaleResiduePrefix]

theorem updateResidueCoordinate_scalePrefix_internal
    {workTapeCount : ℕ}
    (tm : TM workTapeCount) (blockLength scalar : ℕ)
    (regs :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm blockLength)
    (register :
      Fin
        (NeighborhoodExecutableEvaluation.graphFanIn
          workTapeCount + 1))
    (processed : ℕ)
    (hprocessed :
      processed <
        TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
          (NeighborhoodExecutableEvaluation.payloadWidth tm blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn
            workTapeCount)) :
    let chunk :
      Fin
        (TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
          (NeighborhoodExecutableEvaluation.payloadWidth tm blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn
            workTapeCount)) :=
      ⟨processed, hprocessed⟩
    updateResidueCoordinate tm blockLength
        (scaleResiduePrefix
          tm blockLength scalar regs register processed)
        register chunk
        (ResidueBankOp.mul.apply
          (NeighborhoodExecutableEvaluation.modulus tm blockLength)
          ((scaleResiduePrefix
            tm blockLength scalar regs register processed)
              register chunk)
          scalar) =
      scaleResiduePrefix tm blockLength scalar regs register
        (processed + 1) := by
  dsimp only
  funext currentRegister currentChunk
  by_cases hregister : currentRegister = register
  · subst currentRegister
    by_cases hchunk :
        currentChunk = ⟨processed, hprocessed⟩
    · subst currentChunk
      simp [updateResidueCoordinate, scaleResiduePrefix]
    · have hlt_iff :
          currentChunk.val < processed + 1 ↔
            currentChunk.val < processed := by
        constructor
        · intro hlt
          by_contra hnot
          have heq : currentChunk.val = processed := by omega
          exact hchunk (Fin.ext heq)
        · omega
      simp [updateResidueCoordinate, scaleResiduePrefix,
        hchunk, hlt_iff]
  · simp [updateResidueCoordinate, scaleResiduePrefix, hregister]

theorem scaleResiduePrefix_all_internal
    {workTapeCount : ℕ}
    (tm : TM workTapeCount) (blockLength scalar : ℕ)
    (regs :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm blockLength)
    (register :
      Fin
        (NeighborhoodExecutableEvaluation.graphFanIn
          workTapeCount + 1)) :
    scaleResiduePrefix tm blockLength scalar regs register
        (TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
          (NeighborhoodExecutableEvaluation.payloadWidth tm blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount)) =
      NeighborhoodExecutableEvaluation.Residue.scaleAt
        tm blockLength scalar regs register := by
  funext currentRegister chunk
  by_cases hregister : currentRegister = register
  · subst currentRegister
    rw [show
      scaleResiduePrefix tm blockLength scalar regs register
          (TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
            (NeighborhoodExecutableEvaluation.payloadWidth
              tm blockLength)
            (NeighborhoodExecutableEvaluation.graphFanIn
              workTapeCount))
          register chunk =
        ResidueBankOp.mul.apply
          (NeighborhoodExecutableEvaluation.modulus tm blockLength)
          (regs register chunk) scalar by
        simp only [scaleResiduePrefix]
        rw [if_pos ⟨trivial, chunk.isLt⟩]]
    exact residueBankScale_eq_scaleAt_internal
      tm blockLength scalar regs register chunk
  · simp [scaleResiduePrefix,
      NeighborhoodExecutableEvaluation.Residue.scaleAt, hregister]

theorem advanceScaleChunk_runs_internal
    (regs : ResidueScaleRegisters) (store : Store)
    (remaining index base word modulus operand : ℕ)
    (hremaining : store regs.remaining = remaining + 1)
    (hsaved : store regs.bank.savedIndex = index)
    (hone : store regs.bank.bank.one = 1)
    (hword : store regs.bank.bank.word = word)
    (hbase : store regs.bank.bank.base = base)
    (hbasePred : store regs.bank.bank.basePred = base - 1)
    (hmodulus : store regs.bank.modulus = modulus)
    (hmodulusPred :
      store regs.bank.modulusPred = modulus - 1)
    (hoperand : store regs.bank.operand = operand) :
    ∃ final,
      Runs (advanceScaleChunk regs) store final ∧
      final regs.remaining = remaining ∧
      final regs.bank.bank.indexCount = index + 1 ∧
      final regs.bank.bank.word = word ∧
      final regs.bank.bank.base = base ∧
      final regs.bank.bank.basePred = base - 1 ∧
      final regs.bank.bank.one = 1 ∧
      final regs.bank.modulus = modulus ∧
      final regs.bank.modulusPred = modulus - 1 ∧
      final regs.bank.operand = operand := by
  let afterRemaining :=
    (Basic.sub regs.remaining regs.remaining
      regs.bank.bank.one).exec store
  let final :=
    (Basic.add regs.bank.bank.indexCount regs.bank.savedIndex
      regs.bank.bank.one).exec afterRemaining
  have hrun : Runs (advanceScaleChunk regs) store final := by
    simpa [advanceScaleChunk] using
      Runs.seq
        (Runs.basic
          (.sub regs.remaining regs.remaining
            regs.bank.bank.one) store)
        (Runs.basic
          (.add regs.bank.bank.indexCount regs.bank.savedIndex
            regs.bank.bank.one) afterRemaining)
  refine ⟨final, hrun, ?_⟩
  change store (regs.index 16) = remaining + 1 at hremaining
  change store (regs.index 15) = index at hsaved
  change store (regs.index 6) = 1 at hone
  change store (regs.index 0) = word at hword
  change store (regs.index 2) = base at hbase
  change store (regs.index 3) = base - 1 at hbasePred
  change store (regs.index 12) = modulus at hmodulus
  change store (regs.index 13) = modulus - 1 at hmodulusPred
  change store (regs.index 14) = operand at hoperand
  simp [final, afterRemaining, Basic.exec,
    ResidueScaleRegisters.bank,
    ResidueScaleRegisters.bankSlot,
    ResidueScaleRegisters.remaining,
    ResidueBankRegisters.bank,
    ResidueBankRegisters.bankSlot,
    ResidueBankRegisters.savedIndex,
    ResidueBankRegisters.modulus,
    ResidueBankRegisters.modulusPred,
    ResidueBankRegisters.operand,
    BankRegisters.word, BankRegisters.base,
    BankRegisters.basePred, BankRegisters.one,
    BankRegisters.indexCount,
    regs.injective.eq_iff,
    hremaining, hsaved, hone, hword, hbase, hbasePred,
    hmodulus, hmodulusPred, hoperand]

theorem advanceScaleChunk_invariantRuns_internal
    (regs : ResidueScaleRegisters)
    (allowed : Finset ℕ) (bound : ℕ) (store : Store)
    (remaining index base word modulus operand : ℕ)
    (hremaining : store regs.remaining = remaining + 1)
    (hsaved : store regs.bank.savedIndex = index)
    (hone : store regs.bank.bank.one = 1)
    (hword : store regs.bank.bank.word = word)
    (hbase : store regs.bank.bank.base = base)
    (hbasePred : store regs.bank.bank.basePred = base - 1)
    (hmodulus : store regs.bank.modulus = modulus)
    (hmodulusPred :
      store regs.bank.modulusPred = modulus - 1)
    (hoperand : store regs.bank.operand = operand)
    (hremainingBound : remaining ≤ bound)
    (hindexSuccBound : index + 1 ≤ bound)
    (hstore : ValuesWithin allowed bound store) :
    ∃ final,
      InvariantRuns (ValuesWithin allowed bound)
        (advanceScaleChunk regs) store final (1 + 1) ∧
      final regs.remaining = remaining ∧
      final regs.bank.bank.indexCount = index + 1 ∧
      final regs.bank.bank.word = word ∧
      final regs.bank.bank.base = base ∧
      final regs.bank.bank.basePred = base - 1 ∧
      final regs.bank.bank.one = 1 ∧
      final regs.bank.modulus = modulus ∧
      final regs.bank.modulusPred = modulus - 1 ∧
      final regs.bank.operand = operand := by
  let afterRemaining :=
    (Basic.sub regs.remaining regs.remaining
      regs.bank.bank.one).exec store
  let final :=
    (Basic.add regs.bank.bank.indexCount regs.bank.savedIndex
      regs.bank.bank.one).exec afterRemaining
  have hafterRemainingInvariant :
      ValuesWithin allowed bound afterRemaining := by
    apply valuesWithin_sub hstore
    rw [hremaining, hone]
    simpa using hremainingBound
  have hafterRemainingSaved :
      afterRemaining regs.bank.savedIndex = index := by
    change afterRemaining (regs.index 15) = index
    change store (regs.index 15) = index at hsaved
    simp [afterRemaining, Basic.exec,
      ResidueScaleRegisters.remaining,
      ResidueScaleRegisters.bank,
      ResidueScaleRegisters.bankSlot,
      regs.injective.eq_iff, hsaved]
  have hafterRemainingOne :
      afterRemaining regs.bank.bank.one = 1 := by
    change afterRemaining (regs.index 6) = 1
    change store (regs.index 6) = 1 at hone
    simp [afterRemaining, Basic.exec,
      ResidueScaleRegisters.remaining,
      ResidueScaleRegisters.bank,
      ResidueScaleRegisters.bankSlot,
      ResidueBankRegisters.bank,
      ResidueBankRegisters.bankSlot,
      BankRegisters.one, regs.injective.eq_iff, hone]
  have hfinalInvariant :
      ValuesWithin allowed bound final := by
    apply valuesWithin_add hafterRemainingInvariant
    rw [hafterRemainingSaved, hafterRemainingOne]
    exact hindexSuccBound
  have hrun :
      InvariantRuns (ValuesWithin allowed bound)
        (advanceScaleChunk regs) store final (1 + 1) := by
    simpa [advanceScaleChunk] using
      InvariantRuns.seq
        (InvariantRuns.basic
          (.sub regs.remaining regs.remaining regs.bank.bank.one)
          store hstore hafterRemainingInvariant)
        (InvariantRuns.basic
          (.add regs.bank.bank.indexCount regs.bank.savedIndex
            regs.bank.bank.one)
          afterRemaining hafterRemainingInvariant hfinalInvariant)
  obtain ⟨semanticFinal, hsemanticRun, hfinalRemaining,
      hfinalIndex, hfinalWord, hfinalBase, hfinalBasePred,
      hfinalOne, hfinalModulus, hfinalModulusPred,
      hfinalOperand⟩ :=
    advanceScaleChunk_runs_internal regs store remaining index base
      word modulus operand hremaining hsaved hone hword hbase
      hbasePred hmodulus hmodulusPred hoperand
  have hfinalEq : final = semanticFinal :=
    runs_final_unique (InvariantRuns.toRuns hrun) hsemanticRun
  subst semanticFinal
  exact ⟨final, hrun, hfinalRemaining, hfinalIndex, hfinalWord,
    hfinalBase, hfinalBasePred, hfinalOne, hfinalModulus,
    hfinalModulusPred, hfinalOperand⟩

private structure ScaleRegisterState
    {workTapeCount : ℕ}
    (tm : TM workTapeCount) (blockLength scalar base count : ℕ)
    (original :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm blockLength)
    (register :
      Fin
        (NeighborhoodExecutableEvaluation.graphFanIn
          workTapeCount + 1))
    (regs : ResidueScaleRegisters)
    (processed remaining word : ℕ) (store : Store) : Prop where
  balance : processed + remaining = count
  word_eq : store regs.bank.bank.word = word
  represents :
    RepresentsResidueBank tm blockLength base word
      (scaleResiduePrefix
        tm blockLength scalar original register processed)
  word_lt :
    word <
      base ^
        ((NeighborhoodExecutableEvaluation.graphFanIn
            workTapeCount + 1) * count)
  base_eq : store regs.bank.bank.base = base
  basePred_eq : store regs.bank.bank.basePred = base - 1
  one_eq : store regs.bank.bank.one = 1
  index_eq :
    store regs.bank.bank.indexCount =
      register.val * count + processed
  modulus_eq :
    store regs.bank.modulus =
      NeighborhoodExecutableEvaluation.modulus tm blockLength
  modulusPred_eq :
    store regs.bank.modulusPred =
      NeighborhoodExecutableEvaluation.modulus tm blockLength - 1
  operand_eq : store regs.bank.operand = scalar
  remaining_eq : store regs.remaining = remaining

private theorem bankScaleRegisterBody_runs_internal
    {workTapeCount : ℕ}
    (tm : TM workTapeCount) (blockLength scalar base count : ℕ)
    (original :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm blockLength)
    (register :
      Fin
        (NeighborhoodExecutableEvaluation.graphFanIn
          workTapeCount + 1))
    (regs : ResidueScaleRegisters)
    (processed remaining word : ℕ) (store : Store)
    (hcount :
      count =
        TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
          (NeighborhoodExecutableEvaluation.payloadWidth tm blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn
            workTapeCount))
    (hbase : 0 < base)
    (hmodulus :
      0 < NeighborhoodExecutableEvaluation.modulus tm blockLength)
    (hmodulusBase :
      NeighborhoodExecutableEvaluation.modulus tm blockLength ≤ base)
    (hinv :
      ScaleRegisterState tm blockLength scalar base count
        original register regs processed (remaining + 1) word store) :
    ∃ final nextWord,
      Runs (bankScaleRegisterBody regs) store final ∧
      ScaleRegisterState tm blockLength scalar base count
        original register regs (processed + 1) remaining
        nextWord final := by
  have hbalance := hinv.balance
  have hprocessed : processed < count := by
    omega
  have hchunkLt :
      processed <
        TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
          (NeighborhoodExecutableEvaluation.payloadWidth tm blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn
            workTapeCount) := by
    rw [← hcount]
    exact hprocessed
  let chunk :
      Fin
        (TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
          (NeighborhoodExecutableEvaluation.payloadWidth tm blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn
            workTapeCount)) :=
    ⟨processed, hchunkLt⟩
  have hcoordinate :
      residueBankIndex tm blockLength register chunk =
        register.val * count + processed := by
    unfold residueBankIndex
    change
      register.val *
          TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
            (NeighborhoodExecutableEvaluation.payloadWidth
              tm blockLength)
            (NeighborhoodExecutableEvaluation.graphFanIn
              workTapeCount) +
          processed =
        register.val * count + processed
    rw [← hcount]
  have hcoordinateLt :
      residueBankIndex tm blockLength register chunk <
        (NeighborhoodExecutableEvaluation.graphFanIn
            workTapeCount + 1) * count := by
    rw [hcount]
    exact residueBankIndex_lt_internal
      tm blockLength register chunk
  have hindex :
      store regs.bank.bank.indexCount =
        residueBankIndex tm blockLength register chunk :=
    hinv.index_eq.trans hcoordinate.symm
  obtain ⟨updated, hupdate, hupdatedWord, _,
      _, _, _, hupdatedBase, hupdatedBasePred, hupdatedOne,
      _, hupdatedModulus, hupdatedModulusPred, hupdatedOperand,
      hupdatedSaved⟩ :=
    bankUpdateAt_runs_internal regs.bank .mul store base word
      (residueBankIndex tm blockLength register chunk)
      (NeighborhoodExecutableEvaluation.modulus tm blockLength)
      scalar hbase hmodulus hinv.word_eq hinv.base_eq
      hinv.basePred_eq hinv.one_eq hindex hinv.modulus_eq
      hinv.modulusPred_eq hinv.operand_eq
  have hupdatedWordRaw := hupdatedWord
  have hupdatedWordLt :
      updated regs.bank.bank.word <
        base ^
          ((NeighborhoodExecutableEvaluation.graphFanIn
              workTapeCount + 1) * count) := by
    rw [hupdatedWordRaw]
    exact bankUpdateAt_word_lt_pow_internal
      hbase hinv.word_lt hcoordinateLt hmodulus hmodulusBase
  have hupdatedRemaining :
      updated regs.remaining = remaining + 1 := by
    rw [runs_eq_of_not_mem hupdate
      (bankUpdateAt_sourceWritesWithin_internal regs.bank .mul)
      (scaleRemaining_not_mem_bankFootprint regs)]
    exact hinv.remaining_eq
  have hselected := hinv.represents register chunk
  rw [hselected] at hupdatedWord
  have hupdatedRep :
      RepresentsResidueBank tm blockLength base
        (updated regs.bank.bank.word)
        (updateResidueCoordinate tm blockLength
          (scaleResiduePrefix
            tm blockLength scalar original register processed)
          register chunk
          (ResidueBankOp.mul.apply
            (NeighborhoodExecutableEvaluation.modulus tm blockLength)
            ((scaleResiduePrefix
              tm blockLength scalar original register processed)
                register chunk)
            scalar)) := by
    rw [hupdatedWord]
    exact representsResidueBank_replaceAt_internal
      tm blockLength base word
      (scaleResiduePrefix
        tm blockLength scalar original register processed)
      register chunk
      (ResidueBankOp.mul.apply
        (NeighborhoodExecutableEvaluation.modulus tm blockLength)
        ((scaleResiduePrefix
          tm blockLength scalar original register processed)
            register chunk)
        scalar)
      hinv.represents hbase
      (residueBankOp_lt_internal hmodulus hmodulusBase)
  have hprefixStep :=
    updateResidueCoordinate_scalePrefix_internal
      tm blockLength scalar original register processed hchunkLt
  rw [hprefixStep] at hupdatedRep
  obtain ⟨final, hadvance, hfinalRemaining, hfinalIndex,
      hfinalWord, hfinalBase, hfinalBasePred, hfinalOne,
      hfinalModulus, hfinalModulusPred, hfinalOperand⟩ :=
    advanceScaleChunk_runs_internal regs updated remaining
      (residueBankIndex tm blockLength register chunk)
      base (updated regs.bank.bank.word)
      (NeighborhoodExecutableEvaluation.modulus tm blockLength)
      scalar hupdatedRemaining hupdatedSaved hupdatedOne rfl
      hupdatedBase hupdatedBasePred hupdatedModulus
      hupdatedModulusPred hupdatedOperand
  have hbody :
      Runs (bankScaleRegisterBody regs) store final := by
    simpa [bankScaleRegisterBody, bankScaleAt] using
      Runs.seq hupdate hadvance
  refine ⟨final, updated regs.bank.bank.word, hbody, ?_⟩
  constructor
  · omega
  · exact hfinalWord
  · exact hupdatedRep
  · exact hupdatedWordLt
  · exact hfinalBase
  · exact hfinalBasePred
  · exact hfinalOne
  · rw [hfinalIndex, hcoordinate]
    omega
  · exact hfinalModulus
  · exact hfinalModulusPred
  · exact hfinalOperand
  · exact hfinalRemaining

private theorem bankScaleRegisterBody_invariantRuns_internal
    {workTapeCount : ℕ}
    (tm : TM workTapeCount) (blockLength scalar base count : ℕ)
    (original :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm blockLength)
    (register :
      Fin
        (NeighborhoodExecutableEvaluation.graphFanIn
          workTapeCount + 1))
    (regs : ResidueScaleRegisters)
    (allowed : Finset ℕ) (bound : ℕ)
    (processed remaining word : ℕ) (store : Store)
    (hcount :
      count =
        TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
          (NeighborhoodExecutableEvaluation.payloadWidth tm blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn
            workTapeCount))
    (hbase : 0 < base)
    (hmodulus :
      0 < NeighborhoodExecutableEvaluation.modulus tm blockLength)
    (hmodulusBase :
      NeighborhoodExecutableEvaluation.modulus tm blockLength ≤ base)
    (hpackedBound :
      base ^
          ((NeighborhoodExecutableEvaluation.graphFanIn
              workTapeCount + 1) * count) ≤
        bound)
    (hbaseBound : base ≤ bound)
    (hdigitCountBound :
      (NeighborhoodExecutableEvaluation.graphFanIn
          workTapeCount + 1) * count ≤ bound)
    (hscalarProductBound : base * scalar ≤ bound)
    (hinv :
      ScaleRegisterState tm blockLength scalar base count
        original register regs processed (remaining + 1) word store)
    (hstore : ValuesWithin allowed bound store) :
    ∃ final nextWord steps,
      InvariantRuns (ValuesWithin allowed bound)
        (bankScaleRegisterBody regs) store final steps ∧
      ScaleRegisterState tm blockLength scalar base count
        original register regs (processed + 1) remaining
        nextWord final := by
  have hbalance := hinv.balance
  have hprocessed : processed < count := by omega
  have hchunkLt :
      processed <
        TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
          (NeighborhoodExecutableEvaluation.payloadWidth tm blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn
            workTapeCount) := by
    rw [← hcount]
    exact hprocessed
  let chunk :
      Fin
        (TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
          (NeighborhoodExecutableEvaluation.payloadWidth tm blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn
            workTapeCount)) :=
    ⟨processed, hchunkLt⟩
  have hcoordinate :
      residueBankIndex tm blockLength register chunk =
        register.val * count + processed := by
    unfold residueBankIndex
    change
      register.val *
          TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
            (NeighborhoodExecutableEvaluation.payloadWidth
              tm blockLength)
            (NeighborhoodExecutableEvaluation.graphFanIn
              workTapeCount) +
          processed =
        register.val * count + processed
    rw [← hcount]
  have hcoordinateLt :
      residueBankIndex tm blockLength register chunk <
        (NeighborhoodExecutableEvaluation.graphFanIn
            workTapeCount + 1) * count := by
    rw [hcount]
    exact residueBankIndex_lt_internal
      tm blockLength register chunk
  have hcoordinateBound :
      residueBankIndex tm blockLength register chunk ≤ bound :=
    (Nat.le_of_lt hcoordinateLt).trans hdigitCountBound
  have hcoordinateSuccBound :
      residueBankIndex tm blockLength register chunk + 1 ≤ bound :=
    (Nat.succ_le_of_lt hcoordinateLt).trans hdigitCountBound
  have hindex :
      store regs.bank.bank.indexCount =
        residueBankIndex tm blockLength register chunk :=
    hinv.index_eq.trans hcoordinate.symm
  have hrawBound :
      ResidueBankOp.mul.rawApply
          (PackedDigits.digit base word
            (residueBankIndex tm blockLength register chunk))
          scalar ≤
        bound := by
    simp only [ResidueBankOp.rawApply]
    exact
      (Nat.mul_le_mul_right scalar
        (Nat.le_of_lt (PackedDigits.digit_lt hbase))).trans
        hscalarProductBound
  obtain ⟨updated, updateSteps, hupdate, _, _, _, _, _,
      hupdatedBase, hupdatedBasePred, hupdatedOne, _,
      hupdatedModulus, hupdatedModulusPred, hupdatedOperand,
      hupdatedSaved⟩ :=
    bankUpdateAt_invariantRuns_internal regs.bank .mul allowed bound
      store base word
      (residueBankIndex tm blockLength register chunk)
      (NeighborhoodExecutableEvaluation.modulus tm blockLength)
      scalar
      ((NeighborhoodExecutableEvaluation.graphFanIn
          workTapeCount + 1) * count)
      hbase hmodulus hmodulusBase hinv.word_eq hinv.base_eq
      hinv.basePred_eq hinv.one_eq hindex hinv.modulus_eq
      hinv.modulusPred_eq hinv.operand_eq hinv.word_lt
      hcoordinateLt hpackedBound hbaseBound hcoordinateBound
      hrawBound hstore
  have hupdateRuns :
      Runs (bankScaleAt regs.bank) store updated := by
    simpa [bankScaleAt] using InvariantRuns.toRuns hupdate
  have hupdatedInvariant :
      ValuesWithin allowed bound updated :=
    InvariantRuns.final hupdate
  have hupdatedRemaining :
      updated regs.remaining = remaining + 1 := by
    rw [runs_eq_of_not_mem hupdateRuns
      (bankUpdateAt_sourceWritesWithin_internal regs.bank .mul)
      (scaleRemaining_not_mem_bankFootprint regs)]
    exact hinv.remaining_eq
  have hcountLeDigits :
      count ≤
        (NeighborhoodExecutableEvaluation.graphFanIn
            workTapeCount + 1) * count :=
    Nat.le_mul_of_pos_left count (by omega)
  have hremainingBound : remaining ≤ bound := by
    have hremainingCount : remaining ≤ count := by omega
    exact hremainingCount.trans
      (hcountLeDigits.trans hdigitCountBound)
  obtain ⟨final, hadvance, _, _, _, _, _, _, _, _, _⟩ :=
    advanceScaleChunk_invariantRuns_internal regs allowed bound
      updated remaining
      (residueBankIndex tm blockLength register chunk)
      base (updated regs.bank.bank.word)
      (NeighborhoodExecutableEvaluation.modulus tm blockLength)
      scalar hupdatedRemaining hupdatedSaved hupdatedOne rfl
      hupdatedBase hupdatedBasePred hupdatedModulus
      hupdatedModulusPred hupdatedOperand hremainingBound
      hcoordinateSuccBound hupdatedInvariant
  have hbody :
      InvariantRuns (ValuesWithin allowed bound)
        (bankScaleRegisterBody regs) store final
        (updateSteps + (1 + 1)) := by
    simpa [bankScaleRegisterBody, bankScaleAt] using
      InvariantRuns.seq hupdate hadvance
  obtain ⟨semanticFinal, nextWord, hsemanticRun,
      hsemanticState⟩ :=
    bankScaleRegisterBody_runs_internal tm blockLength scalar base
      count original register regs processed remaining word store
      hcount hbase hmodulus hmodulusBase hinv
  have hfinalEq : final = semanticFinal :=
    runs_final_unique (InvariantRuns.toRuns hbody) hsemanticRun
  subst semanticFinal
  exact ⟨final, nextWord, updateSteps + (1 + 1), hbody,
    hsemanticState⟩

private theorem bankScaleRegisterLoop_runs_internal
    {workTapeCount : ℕ}
    (tm : TM workTapeCount) (blockLength scalar base count : ℕ)
    (original :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm blockLength)
    (register :
      Fin
        (NeighborhoodExecutableEvaluation.graphFanIn
          workTapeCount + 1))
    (regs : ResidueScaleRegisters)
    (hcount :
      count =
        TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
          (NeighborhoodExecutableEvaluation.payloadWidth tm blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn
            workTapeCount))
    (hbase : 0 < base)
    (hmodulus :
      0 < NeighborhoodExecutableEvaluation.modulus tm blockLength)
    (hmodulusBase :
      NeighborhoodExecutableEvaluation.modulus tm blockLength ≤ base) :
    ∀ (remaining processed word : ℕ) (store : Store),
      ScaleRegisterState tm blockLength scalar base count
        original register regs processed remaining word store →
      ∃ final finalWord,
        Runs (bankScaleRegister regs) store final ∧
        ScaleRegisterState tm blockLength scalar base count
          original register regs count 0 finalWord final := by
  intro remaining
  induction remaining with
  | zero =>
      intro processed word store hinv
      have hprocessed : processed = count := by
        have hbalance := hinv.balance
        omega
      subst processed
      have hzero : store regs.remaining = 0 :=
        hinv.remaining_eq
      exact ⟨store, word, by
        simpa [bankScaleRegister] using Runs.whileZero hzero,
        hinv⟩
  | succ remaining ih =>
      intro processed word store hinv
      have hactive : store regs.remaining ≠ 0 := by
        rw [hinv.remaining_eq]
        omega
      obtain ⟨middle, nextWord, hbody, hmiddle⟩ :=
        bankScaleRegisterBody_runs_internal tm blockLength scalar
          base count original register regs processed remaining word
          store hcount hbase hmodulus hmodulusBase hinv
      obtain ⟨final, finalWord, hloop, hfinal⟩ :=
        ih (processed + 1) nextWord middle hmiddle
      exact ⟨final, finalWord, by
        simpa [bankScaleRegister] using
          Runs.whileNonzero hactive hbody hloop,
        hfinal⟩

private theorem bankScaleRegisterLoop_invariantRuns_internal
    {workTapeCount : ℕ}
    (tm : TM workTapeCount) (blockLength scalar base count : ℕ)
    (original :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm blockLength)
    (register :
      Fin
        (NeighborhoodExecutableEvaluation.graphFanIn
          workTapeCount + 1))
    (regs : ResidueScaleRegisters)
    (allowed : Finset ℕ) (bound : ℕ)
    (hcount :
      count =
        TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
          (NeighborhoodExecutableEvaluation.payloadWidth tm blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn
            workTapeCount))
    (hbase : 0 < base)
    (hmodulus :
      0 < NeighborhoodExecutableEvaluation.modulus tm blockLength)
    (hmodulusBase :
      NeighborhoodExecutableEvaluation.modulus tm blockLength ≤ base)
    (hpackedBound :
      base ^
          ((NeighborhoodExecutableEvaluation.graphFanIn
              workTapeCount + 1) * count) ≤
        bound)
    (hbaseBound : base ≤ bound)
    (hdigitCountBound :
      (NeighborhoodExecutableEvaluation.graphFanIn
          workTapeCount + 1) * count ≤ bound)
    (hscalarProductBound : base * scalar ≤ bound) :
    ∀ (remaining processed word : ℕ) (store : Store),
      ScaleRegisterState tm blockLength scalar base count
        original register regs processed remaining word store →
      ValuesWithin allowed bound store →
      ∃ final finalWord steps,
        InvariantRuns (ValuesWithin allowed bound)
          (bankScaleRegister regs) store final steps ∧
        ScaleRegisterState tm blockLength scalar base count
          original register regs count 0 finalWord final := by
  intro remaining
  induction remaining with
  | zero =>
      intro processed word store hinv hstore
      have hprocessed : processed = count := by
        have hbalance := hinv.balance
        omega
      subst processed
      have hzero : store regs.remaining = 0 :=
        hinv.remaining_eq
      exact ⟨store, word, 1, by
        simpa [bankScaleRegister] using
          InvariantRuns.whileZero hzero hstore,
        hinv⟩
  | succ remaining ih =>
      intro processed word store hinv hstore
      have hactive : store regs.remaining ≠ 0 := by
        rw [hinv.remaining_eq]
        omega
      obtain ⟨middle, nextWord, bodySteps, hbody, hmiddle⟩ :=
        bankScaleRegisterBody_invariantRuns_internal tm blockLength
          scalar base count original register regs allowed bound
          processed remaining word store hcount hbase hmodulus
          hmodulusBase hpackedBound hbaseBound hdigitCountBound
          hscalarProductBound hinv hstore
      have hmiddleInvariant :
          ValuesWithin allowed bound middle :=
        InvariantRuns.final hbody
      obtain ⟨final, finalWord, loopSteps, hloop, hfinal⟩ :=
        ih (processed + 1) nextWord middle hmiddle
          hmiddleInvariant
      exact ⟨final, finalWord, bodySteps + loopSteps + 2, by
        simpa [bankScaleRegister] using
          InvariantRuns.whileNonzero hactive hbody hloop,
        hfinal⟩

theorem bankScaleRegister_runs_internal
    {workTapeCount : ℕ}
    (tm : TM workTapeCount) (blockLength scalar base word : ℕ)
    (original :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm blockLength)
    (register :
      Fin
        (NeighborhoodExecutableEvaluation.graphFanIn
          workTapeCount + 1))
    (regs : ResidueScaleRegisters) (store : Store)
    (hbase : 0 < base)
    (hmodulus :
      0 < NeighborhoodExecutableEvaluation.modulus tm blockLength)
    (hmodulusBase :
      NeighborhoodExecutableEvaluation.modulus tm blockLength ≤ base)
    (hword : store regs.bank.bank.word = word)
    (hrep :
      RepresentsResidueBank
        tm blockLength base word original)
    (hwordLt :
      word <
        base ^
          ((NeighborhoodExecutableEvaluation.graphFanIn
              workTapeCount + 1) *
            TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
              (NeighborhoodExecutableEvaluation.payloadWidth
                tm blockLength)
              (NeighborhoodExecutableEvaluation.graphFanIn
                workTapeCount)))
    (hbaseValue : store regs.bank.bank.base = base)
    (hbasePred : store regs.bank.bank.basePred = base - 1)
    (hone : store regs.bank.bank.one = 1)
    (hindex :
      store regs.bank.bank.indexCount =
        register.val *
          TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
            (NeighborhoodExecutableEvaluation.payloadWidth
              tm blockLength)
            (NeighborhoodExecutableEvaluation.graphFanIn
              workTapeCount))
    (hmodulusValue :
      store regs.bank.modulus =
        NeighborhoodExecutableEvaluation.modulus tm blockLength)
    (hmodulusPred :
      store regs.bank.modulusPred =
        NeighborhoodExecutableEvaluation.modulus tm blockLength - 1)
    (hoperand : store regs.bank.operand = scalar)
    (hremaining :
      store regs.remaining =
        TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
          (NeighborhoodExecutableEvaluation.payloadWidth tm blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn
            workTapeCount)) :
    ∃ final finalWord,
      Runs (bankScaleRegister regs) store final ∧
      final regs.bank.bank.word = finalWord ∧
      RepresentsResidueBank tm blockLength base finalWord
        (NeighborhoodExecutableEvaluation.Residue.scaleAt
          tm blockLength scalar original register) ∧
      finalWord <
        base ^
          ((NeighborhoodExecutableEvaluation.graphFanIn
              workTapeCount + 1) *
            TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
              (NeighborhoodExecutableEvaluation.payloadWidth
                tm blockLength)
              (NeighborhoodExecutableEvaluation.graphFanIn
                workTapeCount)) ∧
      (∀ chunk,
        PackedDigits.digit base finalWord
            (residueBankIndex tm blockLength register chunk) =
          (NeighborhoodExecutableEvaluation.Residue.scaleAt
            tm blockLength scalar original register) register chunk) ∧
      (∀ currentRegister, currentRegister ≠ register →
        ∀ chunk,
          PackedDigits.digit base finalWord
              (residueBankIndex
                tm blockLength currentRegister chunk) =
            original currentRegister chunk) ∧
      final regs.remaining = 0 ∧
      final regs.bank.bank.indexCount =
        register.val *
            TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
              (NeighborhoodExecutableEvaluation.payloadWidth
                tm blockLength)
              (NeighborhoodExecutableEvaluation.graphFanIn
                workTapeCount) +
          TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
            (NeighborhoodExecutableEvaluation.payloadWidth
              tm blockLength)
            (NeighborhoodExecutableEvaluation.graphFanIn
              workTapeCount) ∧
      final regs.bank.bank.base = base ∧
      final regs.bank.bank.basePred = base - 1 ∧
      final regs.bank.bank.one = 1 ∧
      final regs.bank.modulus =
        NeighborhoodExecutableEvaluation.modulus tm blockLength ∧
      final regs.bank.modulusPred =
        NeighborhoodExecutableEvaluation.modulus tm blockLength - 1 ∧
      final regs.bank.operand = scalar := by
  let count :=
    TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
      (NeighborhoodExecutableEvaluation.payloadWidth tm blockLength)
      (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount)
  have hinitial :
      ScaleRegisterState tm blockLength scalar base count
        original register regs 0 count word store := by
    constructor
    · omega
    · exact hword
    · rw [scaleResiduePrefix_zero_internal]
      exact hrep
    · exact hwordLt
    · exact hbaseValue
    · exact hbasePred
    · exact hone
    · simpa [count] using hindex
    · exact hmodulusValue
    · exact hmodulusPred
    · exact hoperand
    · exact hremaining
  obtain ⟨final, finalWord, hrun, hfinal⟩ :=
    bankScaleRegisterLoop_runs_internal tm blockLength scalar base
      count original register regs rfl hbase hmodulus
      hmodulusBase count 0 word store hinitial
  have hfinalRep := hfinal.represents
  rw [scaleResiduePrefix_all_internal] at hfinalRep
  refine ⟨final, finalWord, hrun, hfinal.word_eq, hfinalRep,
    hfinal.word_lt,
    ?_, ?_, hfinal.remaining_eq, ?_, hfinal.base_eq,
    hfinal.basePred_eq, hfinal.one_eq, hfinal.modulus_eq,
    hfinal.modulusPred_eq, hfinal.operand_eq⟩
  · intro chunk
    exact hfinalRep register chunk
  · intro currentRegister hne chunk
    rw [hfinalRep currentRegister chunk]
    simp [NeighborhoodExecutableEvaluation.Residue.scaleAt, hne]
  · simpa [count] using hfinal.index_eq

theorem bankScaleRegister_invariantRuns_internal
    {workTapeCount : ℕ}
    (tm : TM workTapeCount) (blockLength scalar base word : ℕ)
    (original :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm blockLength)
    (register :
      Fin
        (NeighborhoodExecutableEvaluation.graphFanIn
          workTapeCount + 1))
    (regs : ResidueScaleRegisters)
    (allowed : Finset ℕ) (bound : ℕ) (store : Store)
    (hbase : 0 < base)
    (hmodulus :
      0 < NeighborhoodExecutableEvaluation.modulus tm blockLength)
    (hmodulusBase :
      NeighborhoodExecutableEvaluation.modulus tm blockLength ≤ base)
    (hword : store regs.bank.bank.word = word)
    (hrep :
      RepresentsResidueBank
        tm blockLength base word original)
    (hwordLt :
      word <
        base ^
          ((NeighborhoodExecutableEvaluation.graphFanIn
              workTapeCount + 1) *
            TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
              (NeighborhoodExecutableEvaluation.payloadWidth
                tm blockLength)
              (NeighborhoodExecutableEvaluation.graphFanIn
                workTapeCount)))
    (hbaseValue : store regs.bank.bank.base = base)
    (hbasePred : store regs.bank.bank.basePred = base - 1)
    (hone : store regs.bank.bank.one = 1)
    (hindex :
      store regs.bank.bank.indexCount =
        register.val *
          TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
            (NeighborhoodExecutableEvaluation.payloadWidth
              tm blockLength)
            (NeighborhoodExecutableEvaluation.graphFanIn
              workTapeCount))
    (hmodulusValue :
      store regs.bank.modulus =
        NeighborhoodExecutableEvaluation.modulus tm blockLength)
    (hmodulusPred :
      store regs.bank.modulusPred =
        NeighborhoodExecutableEvaluation.modulus tm blockLength - 1)
    (hoperand : store regs.bank.operand = scalar)
    (hremaining :
      store regs.remaining =
        TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
          (NeighborhoodExecutableEvaluation.payloadWidth tm blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn
            workTapeCount))
    (hpackedBound :
      base ^
          ((NeighborhoodExecutableEvaluation.graphFanIn
              workTapeCount + 1) *
            TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
              (NeighborhoodExecutableEvaluation.payloadWidth
                tm blockLength)
              (NeighborhoodExecutableEvaluation.graphFanIn
                workTapeCount)) ≤
        bound)
    (hbaseBound : base ≤ bound)
    (hdigitCountBound :
      (NeighborhoodExecutableEvaluation.graphFanIn
          workTapeCount + 1) *
          TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
            (NeighborhoodExecutableEvaluation.payloadWidth
              tm blockLength)
            (NeighborhoodExecutableEvaluation.graphFanIn
              workTapeCount) ≤
        bound)
    (hscalarProductBound : base * scalar ≤ bound)
    (hstore : ValuesWithin allowed bound store) :
    ∃ final finalWord steps,
      InvariantRuns (ValuesWithin allowed bound)
        (bankScaleRegister regs) store final steps ∧
      final regs.bank.bank.word = finalWord ∧
      RepresentsResidueBank tm blockLength base finalWord
        (NeighborhoodExecutableEvaluation.Residue.scaleAt
          tm blockLength scalar original register) ∧
      finalWord <
        base ^
          ((NeighborhoodExecutableEvaluation.graphFanIn
              workTapeCount + 1) *
            TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
              (NeighborhoodExecutableEvaluation.payloadWidth
                tm blockLength)
              (NeighborhoodExecutableEvaluation.graphFanIn
                workTapeCount)) ∧
      (∀ chunk,
        PackedDigits.digit base finalWord
            (residueBankIndex tm blockLength register chunk) =
          (NeighborhoodExecutableEvaluation.Residue.scaleAt
            tm blockLength scalar original register) register chunk) ∧
      (∀ currentRegister, currentRegister ≠ register →
        ∀ chunk,
          PackedDigits.digit base finalWord
              (residueBankIndex
                tm blockLength currentRegister chunk) =
            original currentRegister chunk) ∧
      final regs.remaining = 0 ∧
      final regs.bank.bank.indexCount =
        register.val *
            TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
              (NeighborhoodExecutableEvaluation.payloadWidth
                tm blockLength)
              (NeighborhoodExecutableEvaluation.graphFanIn
                workTapeCount) +
          TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
            (NeighborhoodExecutableEvaluation.payloadWidth
              tm blockLength)
            (NeighborhoodExecutableEvaluation.graphFanIn
              workTapeCount) ∧
      final regs.bank.bank.base = base ∧
      final regs.bank.bank.basePred = base - 1 ∧
      final regs.bank.bank.one = 1 ∧
      final regs.bank.modulus =
        NeighborhoodExecutableEvaluation.modulus tm blockLength ∧
      final regs.bank.modulusPred =
        NeighborhoodExecutableEvaluation.modulus tm blockLength - 1 ∧
      final regs.bank.operand = scalar := by
  let count :=
    TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
      (NeighborhoodExecutableEvaluation.payloadWidth tm blockLength)
      (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount)
  have hinitial :
      ScaleRegisterState tm blockLength scalar base count
        original register regs 0 count word store := by
    constructor
    · omega
    · exact hword
    · rw [scaleResiduePrefix_zero_internal]
      exact hrep
    · exact hwordLt
    · exact hbaseValue
    · exact hbasePred
    · exact hone
    · simpa [count] using hindex
    · exact hmodulusValue
    · exact hmodulusPred
    · exact hoperand
    · exact hremaining
  obtain ⟨invariantFinal, _, steps, hrun, _⟩ :=
    bankScaleRegisterLoop_invariantRuns_internal tm blockLength
      scalar base count original register regs allowed bound rfl
      hbase hmodulus hmodulusBase hpackedBound hbaseBound
      hdigitCountBound hscalarProductBound count 0 word store
      hinitial hstore
  obtain ⟨semanticFinal, finalWord, hsemanticRun, hfinalWord,
      hfinalRep, hfinalLt, hselected, hothers, hfinalRemaining,
      hfinalIndex, hfinalBase, hfinalBasePred, hfinalOne,
      hfinalModulus, hfinalModulusPred, hfinalOperand⟩ :=
    bankScaleRegister_runs_internal tm blockLength scalar base word
      original register regs store hbase hmodulus hmodulusBase hword
      hrep hwordLt hbaseValue hbasePred hone hindex hmodulusValue
      hmodulusPred hoperand hremaining
  have hfinalEq : invariantFinal = semanticFinal :=
    runs_final_unique (InvariantRuns.toRuns hrun) hsemanticRun
  subst semanticFinal
  exact ⟨invariantFinal, finalWord, steps, hrun, hfinalWord,
    hfinalRep, hfinalLt, hselected, hothers, hfinalRemaining,
    hfinalIndex, hfinalBase, hfinalBasePred, hfinalOne,
    hfinalModulus, hfinalModulusPred, hfinalOperand⟩

theorem bankAddAt_selectedDigit_runs_internal
    {workTapeCount : ℕ}
    (tm : TM workTapeCount) (blockLength : ℕ)
    (bankRegs : ResidueBankRegisters) (store : Store)
    (base word : ℕ)
    (residueRegs :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm blockLength)
    (register :
      Fin
        (NeighborhoodExecutableEvaluation.graphFanIn
          workTapeCount + 1))
    (value :
      NeighborhoodExecutableEvaluation.ResidueValue tm blockLength)
    (chunk :
      Fin
        (TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
          (NeighborhoodExecutableEvaluation.payloadWidth tm blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn
            workTapeCount)))
    (hbase : 0 < base)
    (hmodulus :
      0 < NeighborhoodExecutableEvaluation.modulus tm blockLength)
    (hmodulusBase :
      NeighborhoodExecutableEvaluation.modulus tm blockLength ≤ base)
    (hword : store bankRegs.bank.word = word)
    (hbaseValue : store bankRegs.bank.base = base)
    (hbasePred : store bankRegs.bank.basePred = base - 1)
    (hone : store bankRegs.bank.one = 1)
    (hindex :
      store bankRegs.bank.indexCount =
        residueBankIndex tm blockLength register chunk)
    (hmodulusValue :
      store bankRegs.modulus =
        NeighborhoodExecutableEvaluation.modulus tm blockLength)
    (hmodulusPred :
      store bankRegs.modulusPred =
        NeighborhoodExecutableEvaluation.modulus tm blockLength - 1)
    (hoperand : store bankRegs.operand = value chunk)
    (hpacked :
      PackedDigits.digit base word
          (residueBankIndex tm blockLength register chunk) =
        residueRegs register chunk) :
    ∃ final,
      Runs (bankAddAt bankRegs) store final ∧
      PackedDigits.digit base (final bankRegs.bank.word)
          (residueBankIndex tm blockLength register chunk) =
        (NeighborhoodExecutableEvaluation.Residue.addAt
          tm blockLength residueRegs register value) register chunk := by
  obtain ⟨final, hrun, hfinalWord, _⟩ :=
    bankUpdateAt_runs_internal bankRegs .add store base word
      (residueBankIndex tm blockLength register chunk)
      (NeighborhoodExecutableEvaluation.modulus tm blockLength)
      (value chunk) hbase hmodulus hword hbaseValue hbasePred hone
      hindex hmodulusValue hmodulusPred hoperand
  refine ⟨final, ?_, ?_⟩
  · simpa [bankAddAt] using hrun
  · rw [hfinalWord]
    rw [replaceAt_digit_eq_internal hbase
      (residueBankOp_lt_internal hmodulus hmodulusBase)]
    rw [hpacked]
    exact residueBankAdd_eq_addAt_internal
      tm blockLength residueRegs register value chunk

theorem bankScaleAt_selectedDigit_runs_internal
    {workTapeCount : ℕ}
    (tm : TM workTapeCount) (blockLength scalar : ℕ)
    (bankRegs : ResidueBankRegisters) (store : Store)
    (base word : ℕ)
    (residueRegs :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm blockLength)
    (register :
      Fin
        (NeighborhoodExecutableEvaluation.graphFanIn
          workTapeCount + 1))
    (chunk :
      Fin
        (TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
          (NeighborhoodExecutableEvaluation.payloadWidth tm blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn
            workTapeCount)))
    (hbase : 0 < base)
    (hmodulus :
      0 < NeighborhoodExecutableEvaluation.modulus tm blockLength)
    (hmodulusBase :
      NeighborhoodExecutableEvaluation.modulus tm blockLength ≤ base)
    (hword : store bankRegs.bank.word = word)
    (hbaseValue : store bankRegs.bank.base = base)
    (hbasePred : store bankRegs.bank.basePred = base - 1)
    (hone : store bankRegs.bank.one = 1)
    (hindex :
      store bankRegs.bank.indexCount =
        residueBankIndex tm blockLength register chunk)
    (hmodulusValue :
      store bankRegs.modulus =
        NeighborhoodExecutableEvaluation.modulus tm blockLength)
    (hmodulusPred :
      store bankRegs.modulusPred =
        NeighborhoodExecutableEvaluation.modulus tm blockLength - 1)
    (hoperand : store bankRegs.operand = scalar)
    (hpacked :
      PackedDigits.digit base word
          (residueBankIndex tm blockLength register chunk) =
        residueRegs register chunk) :
    ∃ final,
      Runs (bankScaleAt bankRegs) store final ∧
      PackedDigits.digit base (final bankRegs.bank.word)
          (residueBankIndex tm blockLength register chunk) =
        (NeighborhoodExecutableEvaluation.Residue.scaleAt
          tm blockLength scalar residueRegs register) register chunk := by
  obtain ⟨final, hrun, hfinalWord, _⟩ :=
    bankUpdateAt_runs_internal bankRegs .mul store base word
      (residueBankIndex tm blockLength register chunk)
      (NeighborhoodExecutableEvaluation.modulus tm blockLength)
      scalar hbase hmodulus hword hbaseValue hbasePred hone hindex
      hmodulusValue hmodulusPred hoperand
  refine ⟨final, ?_, ?_⟩
  · simpa [bankScaleAt] using hrun
  · rw [hfinalWord]
    rw [replaceAt_digit_eq_internal hbase
      (residueBankOp_lt_internal hmodulus hmodulusBase)]
    rw [hpacked]
    exact residueBankScale_eq_scaleAt_internal
      tm blockLength scalar residueRegs register chunk

theorem pushedWord_size_le_internal
    {base value word count width : ℕ}
    (hword : word < base ^ count)
    (hvalue : value < base)
    (hbaseWidth : base ≤ 2 ^ width) :
    (PackedDigits.push base value word).size ≤
      (count + 1) * width :=
  PackedDigits.push_size_le hword hvalue hbaseWidth

theorem poppedWord_size_le_internal
    {base word count width : ℕ}
    (hbase : 0 < base)
    (hword : word < base ^ (count + 1))
    (hbaseWidth : base ≤ 2 ^ width) :
    (PackedDigits.pop base word).size ≤ count * width :=
  PackedDigits.size_le_count_mul_width
    (PackedDigits.pop_lt_pow hbase hword) hbaseWidth

theorem peekedDigit_size_le_internal
    {base word width : ℕ}
    (hbase : 0 < base)
    (hbaseWidth : base ≤ 2 ^ width) :
    (PackedDigits.digit base word 0).size ≤ width := by
  exact Nat.size_le.mpr
    (lt_of_lt_of_le (PackedDigits.digit_lt hbase) hbaseWidth)

theorem stackWord_size_le_internal
    {Q : Type*} [Fintype Q] {workTapeCount candidate stackWord : ℕ}
    (hstack :
      stackWord <
        frameRadix Q workTapeCount candidate ^
          WorkspaceAccounting.horizon candidate) :
    stackWord.size ≤
      WorkspaceAccounting.stackBits Q workTapeCount candidate := by
  have hbound := PackedDigits.size_le_count_mul_width hstack
    (show frameRadix Q workTapeCount candidate ≤
        2 ^ WorkspaceAccounting.frameBits Q workTapeCount candidate by
      rfl)
  simpa [WorkspaceAccounting.stackBits] using hbound

theorem bankWord_size_le_internal
    {Q : Type*} [Fintype Q]
    {workTapeCount candidate bankWord : ℕ}
    (hbank :
      bankWord <
        bankRadix Q workTapeCount candidate ^
          bankDigitCount Q workTapeCount candidate) :
    bankWord.size ≤
      WorkspaceAccounting.catalyticBankBits
        Q workTapeCount candidate := by
  have hbound := PackedDigits.size_le_count_mul_width hbank
    (show bankRadix Q workTapeCount candidate ≤
        2 ^ WorkspaceAccounting.fieldBits
          Q workTapeCount candidate by
      rfl)
  simpa [bankDigitCount, WorkspaceAccounting.catalyticBankBits,
    TreeEval.CookMertz.Workspace.registerBitBudget,
    TreeEval.CookMertz.Workspace.registerFieldCells] using hbound

private theorem fixedValues_size_le
    {Q : Type*} [Fintype Q]
    {workTapeCount candidate : ℕ}
    {fixedValues : Fin fixedRegisterCount → ℕ}
    (hfixed : ∀ index,
      fixedValues index <
        2 ^ WorkspaceAccounting.scratchBits
          Q workTapeCount candidate) :
    (∑ index, (fixedValues index).size) ≤
      fixedRegisterCount *
        WorkspaceAccounting.scratchBits
          Q workTapeCount candidate := by
  calc
    (∑ index, (fixedValues index).size) ≤
        ∑ _ : Fin fixedRegisterCount,
          WorkspaceAccounting.scratchBits
            Q workTapeCount candidate := by
      apply Finset.sum_le_sum
      intro index _
      exact Nat.size_le.mpr (hfixed index)
    _ = fixedRegisterCount *
        WorkspaceAccounting.scratchBits
          Q workTapeCount candidate := by
      simp

theorem packedWorkspaceBits_le_trialEnvelope_internal
    {Q : Type*} [Fintype Q] (workTapeCount : ℕ)
    {candidate trialHorizon stackWord bankWord : ℕ}
    {fixedValues : Fin fixedRegisterCount → ℕ}
    (hcandidate : candidate ≤ trialHorizon)
    (hbounded :
      BoundedWorkspace Q workTapeCount candidate
        stackWord bankWord fixedValues) :
    packedWorkspaceBits stackWord bankWord fixedValues ≤
      fixedRegisterCount *
        WorkspaceAccounting.trialEnvelopeBits
          Q workTapeCount trialHorizon := by
  have hstack := stackWord_size_le_internal hbounded.stack_lt
  have hbank := bankWord_size_le_internal hbounded.bank_lt
  have hfixed := fixedValues_size_le hbounded.fixed_lt
  have htotal :=
    WorkspaceAccounting.totalBits_le_trialEnvelope
      Q workTapeCount hcandidate
  unfold packedWorkspaceBits
  unfold WorkspaceAccounting.totalBits at htotal
  simp only [fixedRegisterCount] at hfixed ⊢
  omega

theorem packedWorkspaceBits_isBigO_trialEnvelope_internal
    {Q : Type*} [Fintype Q] (workTapeCount : ℕ)
    (stackWord bankWord : ℕ → ℕ)
    (fixedValues : ℕ → Fin fixedRegisterCount → ℕ)
    (hbounded : ∀ candidate,
      BoundedWorkspace Q workTapeCount candidate
        (stackWord candidate) (bankWord candidate)
        (fixedValues candidate)) :
    (fun candidate =>
      packedWorkspaceBits (stackWord candidate) (bankWord candidate)
        (fixedValues candidate)) =O
      (fun candidate =>
        WorkspaceAccounting.trialEnvelopeBits
          Q workTapeCount candidate) := by
  rw [BigO]
  apply Asymptotics.IsBigO.of_bound fixedRegisterCount
  filter_upwards with candidate
  simp only [Real.norm_natCast]
  exact_mod_cast packedWorkspaceBits_le_trialEnvelope_internal
    workTapeCount (le_refl candidate) (hbounded candidate)

theorem microcode_loop_runs_internal
    {workTapeCount : ℕ} {tm : TM workTapeCount}
    (microcode : ResidueMicrocode tm)
    {inst : ResidueInstance tm} (state : microcode.State inst) :
    ∃ final : microcode.State inst,
      microcode.terminal final ∧
      Runs (.whileNonzero microcode.active microcode.body)
        (microcode.store state)
        (microcode.store final) := by
  induction hrank : microcode.rank state using
      Nat.strong_induction_on generalizing state with
  | h rank ih =>
      by_cases hterminal : microcode.terminal state
      · refine ⟨state, hterminal, ?_⟩
        apply Runs.whileZero
        exact (microcode.active_zero_iff state).mpr hterminal
      · have hactive :
          microcode.store state microcode.active ≠ 0 := by
          intro hzero
          exact hterminal
            ((microcode.active_zero_iff state).mp hzero)
        have hdecrease :
            microcode.rank (microcode.next state) < rank := by
          simpa [← hrank] using
            microcode.rank_next_lt state hterminal
        obtain ⟨final, hfinal, hloop⟩ :=
          ih (microcode.rank (microcode.next state))
            hdecrease (microcode.next state) rfl
        exact ⟨final, hfinal,
          Runs.whileNonzero hactive
            (microcode.body_runs state hterminal) hloop⟩

theorem microcode_program_result_internal
    {workTapeCount : ℕ} {tm : TM workTapeCount}
    (microcode : ResidueMicrocode tm)
    (inst : ResidueInstance tm) :
    ∃ final,
      Runs microcode.program
        (RAM.initRegs (microcode.ramInput inst)) final ∧
      microcode.decode inst final =
        (NeighborhoodExecutableEvaluation.Residue.profileDecision
          tm inst.x inst.blockLength inst.encoding inst.positive
            inst.horizon inst.guess).result := by
  obtain ⟨state, hterminal, hruns⟩ :=
    microcode_loop_runs_internal microcode (microcode.initial inst)
  exact ⟨microcode.store state,
    Runs.seq (microcode.setup_runs inst) hruns,
    microcode.terminal_correct state hterminal⟩

theorem microcode_program_sourceWritesWithin_internal
    {workTapeCount : ℕ} {tm : TM workTapeCount}
    (microcode : ResidueMicrocode tm) :
    RAM.Structured.Footprint.CmdWritesWithin
      microcode.layout.footprint microcode.program := by
  simpa [ResidueMicrocode.program,
    RAM.Structured.Footprint.CmdWritesWithin] using
    And.intro microcode.setupWritesWithin
      microcode.bodyWritesWithin

theorem microcode_program_writesWithin_internal
    {workTapeCount : ℕ} {tm : TM workTapeCount}
    (microcode : ResidueMicrocode tm) :
    RegisterStore.DenseOverlay.FixedRegisters.Footprint.ProgramWritesWithin
      microcode.program.compile microcode.layout.footprint :=
  RAM.Structured.Footprint.programWritesWithin_compile
    (microcode_program_sourceWritesWithin_internal microcode)

private theorem cmdNoStore_of_writesWithin
    {allowed : Finset ℕ} {cmd : Cmd}
    (hwrites :
      RAM.Structured.Footprint.CmdWritesWithin allowed cmd) :
    cmdNoStore cmd := by
  induction cmd with
  | skip => trivial
  | basic op =>
      cases op <;>
        simp_all [RAM.Structured.Footprint.CmdWritesWithin,
          RAM.Structured.Footprint.BasicWritesWithin,
          cmdNoStore, basicNoStore]
  | seq first second firstIH secondIH =>
      simpa [RAM.Structured.Footprint.CmdWritesWithin, cmdNoStore] using
        And.intro (firstIH hwrites.1) (secondIH hwrites.2)
  | ifZero test onZero onNonzero zeroIH nonzeroIH =>
      simpa [RAM.Structured.Footprint.CmdWritesWithin, cmdNoStore] using
        And.intro (zeroIH hwrites.1) (nonzeroIH hwrites.2)
  | whileNonzero test body bodyIH =>
      simpa [RAM.Structured.Footprint.CmdWritesWithin, cmdNoStore] using
        bodyIH hwrites

theorem microcode_program_noStore_internal
    {workTapeCount : ℕ} {tm : TM workTapeCount}
    (microcode : ResidueMicrocode tm) :
    cmdNoStore microcode.program :=
  cmdNoStore_of_writesWithin
    (microcode_program_sourceWritesWithin_internal microcode)

theorem microcode_mutableValue_size_le_internal
    {workTapeCount : ℕ} {tm : TM workTapeCount}
    (microcode : ResidueMicrocode tm)
    {inst : ResidueInstance tm} {trialHorizon : ℕ}
    (hcandidate : inst.candidateTime ≤ trialHorizon)
    (state : microcode.State inst) {address : ℕ}
    (haddress : address ∈ microcode.layout.footprint) :
    (microcode.store state address).size ≤
      fixedRegisterCount *
        WorkspaceAccounting.trialEnvelopeBits
          tm.Q workTapeCount trialHorizon := by
  have htotal :=
    packedWorkspaceBits_le_trialEnvelope_internal
      workTapeCount hcandidate (microcode.bounded state)
  rw [Layout.footprint, Finset.mem_union] at haddress
  rcases haddress with hpacked | hfixed
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hpacked
    rcases hpacked with rfl | rfl
    · unfold packedWorkspaceBits at htotal
      omega
    · unfold packedWorkspaceBits at htotal
      omega
  · obtain ⟨index, _, rfl⟩ := Finset.mem_image.mp hfixed
    have hcomponent :
        (microcode.store state
          (microcode.layout.fixed index)).size ≤
          ∑ current : Fin fixedRegisterCount,
            (microcode.store state
              (microcode.layout.fixed current)).size := by
      exact Finset.single_le_sum
        (fun current _ => Nat.zero_le
          (microcode.store state
            (microcode.layout.fixed current)).size)
        (Finset.mem_univ index)
    unfold packedWorkspaceBits at htotal
    simp only at htotal
    omega

theorem microcode_compiledPrefix_mutableValue_size_le_internal
    {workTapeCount : ℕ} {tm : TM workTapeCount}
    (microcode : ResidueMicrocode tm)
    (inst : ResidueInstance tm) (trialHorizon : ℕ)
    (hcandidate : inst.candidateTime ≤ trialHorizon)
    (k : ℕ) (hk : k ≤ microcode.runFuel inst)
    (address : ℕ)
    (haddress : address ∈ microcode.layout.footprint) :
    bitlen
        ((RAM.run microcode.program.compile k
          (RAM.initCfg (microcode.ramInput inst))).regs address) ≤
      fixedRegisterCount *
        WorkspaceAccounting.trialEnvelopeBits
          tm.Q workTapeCount trialHorizon := by
  obtain ⟨final, _hterminal, hrun⟩ :=
    microcode.prefixInvariant_run inst
  apply microcode.prefixInvariant_values
    inst trialHorizon hcandidate
  · simpa [ResidueMicrocode.program] using
      RAM.Structured.InvariantRuns.compile_prefix hrun hk
  · exact haddress

theorem microcode_traceBound_internal
    {workTapeCount : ℕ} {tm : TM workTapeCount}
    (microcode : ResidueMicrocode tm)
    (inst : ResidueInstance tm) (trialHorizon : ℕ)
    (hcandidate : inst.candidateTime ≤ trialHorizon) :
    RegisterStore.DenseOverlay.FixedRegisters.TraceBound
      microcode.program.compile (microcode.ramInput inst)
      (microcode.runFuel inst) microcode.layout.footprint.card
      (fixedRegisterCount *
          WorkspaceAccounting.trialEnvelopeBits
            tm.Q workTapeCount trialHorizon +
        1) := by
  apply RAM.Structured.Footprint.traceBound_compile
  · exact microcode_program_sourceWritesWithin_internal microcode
  · exact microcode.zero_mem
  · exact microcode.code_size_le inst trialHorizon hcandidate
  · exact microcode.footprint_count_le inst trialHorizon hcandidate
  · exact microcode.address_size_le inst trialHorizon hcandidate
  · exact microcode_compiledPrefix_mutableValue_size_le_internal
      microcode inst trialHorizon hcandidate

end Internal

end NeighborhoodProgram

end Runtime

end TimeSpaceSimulation

end Complexity
