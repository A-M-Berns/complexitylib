/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.RandomAccessMachine.Structured.Run
import
  Complexitylib.Models.RandomAccessMachine.Structured.RuntimeArithmetic.Defs

/-!
# Proof internals for structured runtime arithmetic
-/

namespace Complexity

namespace RAM

namespace Structured

namespace RuntimeArithmetic

namespace Internal

private theorem reduceLoop_runs
    (regs : ReduceRegisters) (store : Store)
    (modulus remainder quotient : ℕ)
    (hmodulus : 0 < modulus) (hremainder : remainder < modulus)
    (hvalue :
      store regs.value = quotient * modulus + remainder)
    (hmodulusValue : store regs.modulus = modulus)
    (hmodulusPred :
      store regs.modulusPred = modulus - 1)
    (htest :
      store regs.test =
        quotient * modulus + remainder - (modulus - 1)) :
    Runs (.whileNonzero regs.test (reduceBody regs))
      store (reduceResultStore regs remainder store) := by
  induction quotient generalizing store with
  | zero =>
      have htestZero : store regs.test = 0 := by
        rw [htest]
        omega
      have hresult :
          reduceResultStore regs remainder store = store := by
        funext index
        by_cases hvalueIndex : index = regs.value
        · subst index
          simp [reduceResultStore, regs.value_ne_test, hvalue]
        · by_cases htestIndex : index = regs.test
          · subst index
            simp [reduceResultStore, htestZero]
          · simp [reduceResultStore, Function.update_of_ne,
              hvalueIndex, htestIndex]
      rw [hresult]
      exact Runs.whileZero htestZero
  | succ quotient ih =>
      have htestNonzero : store regs.test ≠ 0 := by
        rw [htest]
        simp only [Nat.succ_mul]
        omega
      let valueStore :=
        (Basic.sub regs.value regs.value regs.modulus).exec store
      let nextStore := (reduceTestOp regs).exec valueStore
      have hbody :
          Runs (reduceBody regs) store nextStore := by
        apply Runs.seq (Runs.basic _ _)
        exact Runs.basic _ _
      have hnextValue :
          nextStore regs.value =
            quotient * modulus + remainder := by
        simp only [nextStore, reduceTestOp, Basic.exec]
        rw [Function.update_of_ne regs.value_ne_test]
        simp only [valueStore, Basic.exec, Function.update_self]
        rw [hvalue, hmodulusValue]
        simp only [Nat.succ_mul]
        omega
      have hnextModulus :
          nextStore regs.modulus = modulus := by
        simp [nextStore, reduceTestOp, valueStore, Basic.exec,
          regs.modulus_ne_test,
          regs.value_ne_modulus.symm, hmodulusValue]
      have hnextModulusPred :
          nextStore regs.modulusPred = modulus - 1 := by
        simp [nextStore, reduceTestOp, valueStore, Basic.exec,
          regs.modulusPred_ne_test,
          regs.value_ne_modulusPred.symm, hmodulusPred]
      have hvalueStoreValue :
          valueStore regs.value =
            quotient * modulus + remainder := by
        simp only [valueStore, Basic.exec, Function.update_self]
        rw [hvalue, hmodulusValue]
        simp only [Nat.succ_mul]
        omega
      have hvalueStoreModulusPred :
          valueStore regs.modulusPred = modulus - 1 := by
        simp [valueStore, Basic.exec,
          regs.value_ne_modulusPred.symm, hmodulusPred]
      have hnextTest :
          nextStore regs.test =
            quotient * modulus + remainder - (modulus - 1) := by
        simp only [nextStore, reduceTestOp, Basic.exec,
          Function.update_self]
        rw [hvalueStoreValue, hvalueStoreModulusPred]
      have hloop :=
        ih nextStore hnextValue hnextModulus
          hnextModulusPred hnextTest
      have hresult :
          reduceResultStore regs remainder nextStore =
            reduceResultStore regs remainder store := by
        funext index
        by_cases hvalueIndex : index = regs.value
        · subst index
          simp [reduceResultStore, regs.value_ne_test]
        · by_cases htestIndex : index = regs.test
          · subst index
            simp [reduceResultStore]
          · simp [reduceResultStore, nextStore, reduceTestOp,
              valueStore, Basic.exec, Function.update_of_ne,
              hvalueIndex, htestIndex]
      rw [hresult] at hloop
      exact Runs.whileNonzero htestNonzero hbody hloop

theorem reduce_runs_internal
    (regs : ReduceRegisters) (store : Store)
    (modulus value : ℕ) (hmodulus : 0 < modulus)
    (hvalue : store regs.value = value)
    (hmodulusValue : store regs.modulus = modulus)
    (hmodulusPred :
      store regs.modulusPred = modulus - 1) :
    Runs (reduce regs) store
      (reduceResultStore regs (value % modulus) store) := by
  let testedStore := (reduceTestOp regs).exec store
  have htestedValue : testedStore regs.value = value := by
    simp [testedStore, reduceTestOp, Basic.exec,
      regs.value_ne_test, hvalue]
  have htestedModulus :
      testedStore regs.modulus = modulus := by
    simp [testedStore, reduceTestOp, Basic.exec,
      regs.modulus_ne_test, hmodulusValue]
  have htestedModulusPred :
      testedStore regs.modulusPred = modulus - 1 := by
    simp [testedStore, reduceTestOp, Basic.exec,
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
    simp only [testedStore, reduceTestOp, Basic.exec,
      Function.update_self]
    rw [hvalue, hmodulusPred, hdecompose]
  have hloop := reduceLoop_runs regs testedStore modulus
    (value % modulus) (value / modulus) hmodulus
    (Nat.mod_lt value hmodulus) htestedQuotient
    htestedModulus htestedModulusPred htestedTest
  have hresult :
      reduceResultStore regs (value % modulus) testedStore =
        reduceResultStore regs (value % modulus) store := by
    funext index
    by_cases hvalueIndex : index = regs.value
    · subst index
      simp [reduceResultStore, regs.value_ne_test]
    · by_cases htestIndex : index = regs.test
      · subst index
        simp [reduceResultStore]
      · simp [reduceResultStore, testedStore, reduceTestOp,
          Basic.exec, Function.update_of_ne,
          hvalueIndex, htestIndex]
  rw [hresult] at hloop
  simpa [reduce, testedStore] using
    Runs.seq (Runs.basic (reduceTestOp regs) store) hloop

theorem addMod_runs_internal
    (regs : ReduceRegisters) (left right : ℕ)
    (store : Store) (modulus : ℕ) (hmodulus : 0 < modulus)
    (hmodulusValue : store regs.modulus = modulus)
    (hmodulusPred :
      store regs.modulusPred = modulus - 1) :
    Runs (addMod regs left right) store
      (reduceResultStore regs
        ((store left + store right) % modulus) store) := by
  let rawStore :=
    (Basic.add regs.value left right).exec store
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
  have hreduce := reduce_runs_internal regs rawStore modulus
    (store left + store right) hmodulus hrawValue
    hrawModulus hrawModulusPred
  have hresult :
      reduceResultStore regs
          ((store left + store right) % modulus) rawStore =
        reduceResultStore regs
          ((store left + store right) % modulus) store := by
    funext index
    by_cases hvalueIndex : index = regs.value
    · subst index
      simp [reduceResultStore, regs.value_ne_test]
    · by_cases htestIndex : index = regs.test
      · subst index
        simp [reduceResultStore]
      · simp [reduceResultStore, rawStore, Basic.exec,
          Function.update_of_ne, hvalueIndex, htestIndex]
  rw [hresult] at hreduce
  simpa [addMod, rawStore] using
    Runs.seq (Runs.basic (Basic.add regs.value left right) store)
      hreduce

theorem mulMod_runs_internal
    (regs : ReduceRegisters) (left right : ℕ)
    (store : Store) (modulus : ℕ) (hmodulus : 0 < modulus)
    (hmodulusValue : store regs.modulus = modulus)
    (hmodulusPred :
      store regs.modulusPred = modulus - 1) :
    Runs (mulMod regs left right) store
      (reduceResultStore regs
        ((store left * store right) % modulus) store) := by
  let rawStore :=
    (Basic.mul regs.value left right).exec store
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
  have hreduce := reduce_runs_internal regs rawStore modulus
    (store left * store right) hmodulus hrawValue
    hrawModulus hrawModulusPred
  have hresult :
      reduceResultStore regs
          ((store left * store right) % modulus) rawStore =
        reduceResultStore regs
          ((store left * store right) % modulus) store := by
    funext index
    by_cases hvalueIndex : index = regs.value
    · subst index
      simp [reduceResultStore, regs.value_ne_test]
    · by_cases htestIndex : index = regs.test
      · subst index
        simp [reduceResultStore]
      · simp [reduceResultStore, rawStore, Basic.exec,
          Function.update_of_ne, hvalueIndex, htestIndex]
  rw [hresult] at hreduce
  simpa [mulMod, rawStore] using
    Runs.seq (Runs.basic (Basic.mul regs.value left right) store)
      hreduce

theorem subMod_runs_internal
    (regs : ReduceRegisters) (left right : ℕ)
    (store : Store) (modulus : ℕ) (hmodulus : 0 < modulus)
    (hright : right ≠ regs.value)
    (hmodulusValue : store regs.modulus = modulus)
    (hmodulusPred :
      store regs.modulusPred = modulus - 1) :
    Runs (subMod regs left right) store
      (reduceResultStore regs
        ((store left + modulus - store right) % modulus) store) := by
  let addedStore :=
    (Basic.add regs.value left regs.modulus).exec store
  let rawStore :=
    (Basic.sub regs.value regs.value right).exec addedStore
  have haddedValue :
      addedStore regs.value = store left + modulus := by
    simp [addedStore, Basic.exec, hmodulusValue]
  have haddedRight :
      addedStore right = store right := by
    simp [addedStore, Basic.exec, hright]
  have hrawValue :
      rawStore regs.value =
        store left + modulus - store right := by
    simp only [rawStore, Basic.exec, Function.update_self]
    rw [haddedValue, haddedRight]
  have haddedModulus :
      addedStore regs.modulus = modulus := by
    simp [addedStore, Basic.exec,
      regs.value_ne_modulus.symm, hmodulusValue]
  have hrawModulus :
      rawStore regs.modulus = modulus := by
    simp [rawStore, Basic.exec, regs.value_ne_modulus.symm,
      haddedModulus]
  have haddedModulusPred :
      addedStore regs.modulusPred = modulus - 1 := by
    simp [addedStore, Basic.exec,
      regs.value_ne_modulusPred.symm, hmodulusPred]
  have hrawModulusPred :
      rawStore regs.modulusPred = modulus - 1 := by
    simp [rawStore, Basic.exec,
      regs.value_ne_modulusPred.symm, haddedModulusPred]
  have hreduce := reduce_runs_internal regs rawStore modulus
    (store left + modulus - store right) hmodulus hrawValue
    hrawModulus hrawModulusPred
  have hresult :
      reduceResultStore regs
          ((store left + modulus - store right) % modulus) rawStore =
        reduceResultStore regs
          ((store left + modulus - store right) % modulus) store := by
    funext index
    by_cases hvalueIndex : index = regs.value
    · subst index
      simp [reduceResultStore, regs.value_ne_test]
    · by_cases htestIndex : index = regs.test
      · subst index
        simp [reduceResultStore]
      · simp [reduceResultStore, rawStore, addedStore, Basic.exec,
          Function.update_of_ne, hvalueIndex, htestIndex]
  rw [hresult] at hreduce
  have hfirst :
      Runs (.basic (.add regs.value left regs.modulus))
        store addedStore :=
    Runs.basic _ _
  have hsecond :
      Runs (.basic (.sub regs.value regs.value right))
        addedStore rawStore :=
    Runs.basic _ _
  simpa [subMod, addedStore, rawStore] using
    Runs.seq hfirst (Runs.seq hsecond hreduce)

private theorem powModLoop_runs
    (regs : PowRegisters) (store : Store)
    (modulus base exponent accumulator : ℕ)
    (hmodulus : 0 < modulus)
    (haccumulator :
      store regs.accumulator = accumulator)
    (hmodulusValue : store regs.modulus = modulus)
    (hmodulusPred :
      store regs.modulusPred = modulus - 1)
    (htest : store regs.test = 0)
    (hbase : store regs.base = base)
    (hexponent : store regs.exponent = exponent)
    (hone : store regs.one = 1) :
    Runs (.whileNonzero regs.exponent (powModBody regs))
      store
      (powModResultStore regs
        (powModLoop modulus base exponent accumulator) store) := by
  induction exponent generalizing store accumulator with
  | zero =>
      have haccTest : regs.accumulator ≠ regs.test :=
        regs.index_ne (first := 0) (second := 3) (by decide)
      have haccExponent : regs.accumulator ≠ regs.exponent :=
        regs.index_ne (first := 0) (second := 5) (by decide)
      have htestExponent : regs.test ≠ regs.exponent :=
        regs.index_ne (first := 3) (second := 5) (by decide)
      have hresult :
          powModResultStore regs accumulator store = store := by
        funext index
        by_cases hacc : index = regs.accumulator
        · subst index
          simp [powModResultStore, haccTest, haccExponent,
            haccumulator]
        · by_cases htestIndex : index = regs.test
          · subst index
            simp [powModResultStore, htestExponent, htest]
          · by_cases hexponentIndex : index = regs.exponent
            · subst index
              simp [powModResultStore, hexponent]
            · simp [powModResultStore, Function.update_of_ne, hacc,
                htestIndex, hexponentIndex]
      rw [show powModLoop modulus base 0 accumulator = accumulator
        from rfl, hresult]
      exact Runs.whileZero hexponent
  | succ exponent ih =>
      let nextAccumulator := (accumulator * base) % modulus
      let afterMul :=
        reduceResultStore regs.reduceRegisters nextAccumulator store
      have hmul :
          Runs
            (mulMod regs.reduceRegisters regs.accumulator regs.base)
            store afterMul := by
        simpa [afterMul, nextAccumulator, haccumulator, hbase] using
          mulMod_runs_internal regs.reduceRegisters regs.accumulator
            regs.base store modulus hmodulus hmodulusValue
              hmodulusPred
      let afterBody :=
        (Basic.sub regs.exponent regs.exponent regs.one).exec afterMul
      have hdecrement :
          Runs
            (.basic
              (.sub regs.exponent regs.exponent regs.one))
            afterMul afterBody :=
        Runs.basic _ _
      have hbody :
          Runs (powModBody regs) store afterBody := by
        simpa [powModBody] using Runs.seq hmul hdecrement
      have hafterAccumulator :
          afterBody regs.accumulator = nextAccumulator := by
        simp [afterBody, afterMul, reduceResultStore,
          PowRegisters.reduceRegisters, Basic.exec,
          regs.injective.eq_iff]
      have hafterModulus :
          afterBody regs.modulus = modulus := by
        simp [afterBody, afterMul, reduceResultStore,
          PowRegisters.reduceRegisters, Basic.exec,
          regs.injective.eq_iff, hmodulusValue]
      have hafterModulusPred :
          afterBody regs.modulusPred = modulus - 1 := by
        simp [afterBody, afterMul, reduceResultStore,
          PowRegisters.reduceRegisters, Basic.exec,
          regs.injective.eq_iff, hmodulusPred]
      have hafterTest :
          afterBody regs.test = 0 := by
        simp [afterBody, afterMul, reduceResultStore,
          PowRegisters.reduceRegisters, Basic.exec,
          regs.injective.eq_iff]
      have hafterBase :
          afterBody regs.base = base := by
        simp [afterBody, afterMul, reduceResultStore,
          PowRegisters.reduceRegisters, Basic.exec,
          regs.injective.eq_iff, hbase]
      have hafterExponent :
          afterBody regs.exponent = exponent := by
        simp [afterBody, afterMul, reduceResultStore,
          PowRegisters.reduceRegisters, Basic.exec,
          regs.injective.eq_iff, hexponent, hone]
      have hafterOne :
          afterBody regs.one = 1 := by
        simp [afterBody, afterMul, reduceResultStore,
          PowRegisters.reduceRegisters, Basic.exec,
          regs.injective.eq_iff, hone]
      have hloop :=
        ih afterBody nextAccumulator hafterAccumulator
          hafterModulus hafterModulusPred hafterTest hafterBase
            hafterExponent hafterOne
      let result :=
        powModLoop modulus base exponent nextAccumulator
      have hfinal :
          powModResultStore regs result afterBody =
            powModResultStore regs result store := by
        funext index
        by_cases hacc : index = regs.accumulator
        · subst index
          simp [powModResultStore, regs.injective.eq_iff]
        · by_cases htestIndex : index = regs.test
          · subst index
            simp [powModResultStore, regs.injective.eq_iff]
          · by_cases hexponentIndex : index = regs.exponent
            · subst index
              simp [powModResultStore]
            · simp [powModResultStore, afterBody, afterMul,
                reduceResultStore, PowRegisters.reduceRegisters,
                Basic.exec, Function.update_of_ne, hacc,
                htestIndex, hexponentIndex]
      have hnonzero :
          store regs.exponent ≠ 0 := by
        omega
      have hrun :=
        Runs.whileNonzero hnonzero hbody hloop
      change
        powModResultStore regs
            (powModLoop modulus base exponent nextAccumulator)
            afterBody =
          powModResultStore regs
            (powModLoop modulus base exponent nextAccumulator)
            store at hfinal
      rw [hfinal] at hrun
      simpa [powModLoop, nextAccumulator] using hrun

theorem powMod_runs_internal
    (regs : PowRegisters) (store : Store)
    (modulus base exponent accumulator : ℕ)
    (hmodulus : 0 < modulus)
    (haccumulator :
      store regs.accumulator = accumulator)
    (hmodulusValue : store regs.modulus = modulus)
    (hmodulusPred :
      store regs.modulusPred = modulus - 1)
    (hbase : store regs.base = base)
    (hexponent : store regs.exponent = exponent)
    (hone : store regs.one = 1) :
    Runs (powMod regs) store
      (powModResultStore regs
        (powModLoop modulus base exponent accumulator) store) := by
  let cleared :=
    (Basic.imm regs.test 0).exec store
  have hclear :
      Runs (.basic (.imm regs.test 0)) store cleared :=
    Runs.basic _ _
  have hclearedAccumulator :
      cleared regs.accumulator = accumulator := by
    simp [cleared, Basic.exec, regs.injective.eq_iff, haccumulator]
  have hclearedModulus :
      cleared regs.modulus = modulus := by
    simp [cleared, Basic.exec, regs.injective.eq_iff, hmodulusValue]
  have hclearedModulusPred :
      cleared regs.modulusPred = modulus - 1 := by
    simp [cleared, Basic.exec, regs.injective.eq_iff, hmodulusPred]
  have hclearedTest :
      cleared regs.test = 0 := by
    simp [cleared, Basic.exec]
  have hclearedBase :
      cleared regs.base = base := by
    simp [cleared, Basic.exec, regs.injective.eq_iff, hbase]
  have hclearedExponent :
      cleared regs.exponent = exponent := by
    simp [cleared, Basic.exec, regs.injective.eq_iff, hexponent]
  have hclearedOne :
      cleared regs.one = 1 := by
    simp [cleared, Basic.exec, regs.injective.eq_iff, hone]
  have hloop :=
    powModLoop_runs regs cleared modulus base exponent accumulator
      hmodulus hclearedAccumulator hclearedModulus
        hclearedModulusPred hclearedTest hclearedBase
          hclearedExponent hclearedOne
  let result :=
    powModLoop modulus base exponent accumulator
  have hfinal :
      powModResultStore regs result cleared =
        powModResultStore regs result store := by
    funext index
    by_cases hacc : index = regs.accumulator
    · subst index
      simp [powModResultStore, regs.injective.eq_iff]
    · by_cases htestIndex : index = regs.test
      · subst index
        simp [powModResultStore, regs.injective.eq_iff]
      · by_cases hexponentIndex : index = regs.exponent
        · subst index
          simp [powModResultStore]
        · simp [powModResultStore, cleared, Basic.exec,
            Function.update_of_ne, hacc, htestIndex,
            hexponentIndex]
  change
    powModResultStore regs
        (powModLoop modulus base exponent accumulator) cleared =
      powModResultStore regs
        (powModLoop modulus base exponent accumulator) store at hfinal
  rw [hfinal] at hloop
  simpa [powMod, cleared] using Runs.seq hclear hloop

end Internal

end RuntimeArithmetic

end Structured

end RAM

end Complexity
