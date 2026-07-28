/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.Runtime.Arithmetic.Defs
import
  Complexitylib.Models.RandomAccessMachine.Structured.RuntimeArithmetic
import Complexitylib.TreeEvaluation.CookMertz.PrimeField.Runtime

/-!
# Proof internals for first-order simulator arithmetic
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace Runtime

open RAM Structured
open TreeEval CookMertz PrimeField

namespace Internal

theorem powModLoop_eq_runtime_internal
    {modulus base exponent accumulator : ℕ}
    (hmodulus : 0 < modulus)
    (haccumulator : accumulator < modulus) :
    RuntimeArithmetic.powModLoop modulus base exponent accumulator =
      PrimeField.Runtime.powLoop modulus base exponent accumulator := by
  induction exponent generalizing accumulator with
  | zero =>
      rfl
  | succ exponent ih =>
      rw [RuntimeArithmetic.powModLoop, PrimeField.Runtime.powLoop]
      have hnext :
          accumulator * base % modulus =
            PrimeField.Runtime.mul modulus accumulator base := by
        simp [PrimeField.Runtime.mul, PrimeField.Runtime.mulInput,
          PrimeField.Runtime.normalize, Nat.mul_mod,
          Nat.mod_eq_of_lt haccumulator]
      rw [← hnext]
      exact ih (Nat.mod_lt _ hmodulus)

theorem powModLoop_one_eq_runtime_internal
    {modulus base exponent : ℕ} (hmodulus : 1 < modulus) :
    RuntimeArithmetic.powModLoop modulus base exponent 1 =
      PrimeField.Runtime.pow modulus base exponent := by
  unfold PrimeField.Runtime.pow
  rw [show PrimeField.Runtime.normalize modulus 1 = 1 by
    simp [PrimeField.Runtime.normalize, Nat.mod_eq_of_lt hmodulus]]
  exact powModLoop_eq_runtime_internal (by omega) hmodulus

theorem inverseMod_runs_internal
    (regs : RuntimeArithmetic.PowRegisters)
    (store : Store) (modulus base : ℕ)
    (hprime : modulus.Prime)
    (hmodulusValue : store regs.modulus = modulus)
    (hmodulusPred :
      store regs.modulusPred = modulus - 1)
    (hbase : store regs.base = base)
    (hone : store regs.one = 1)
    (hbaseLt : base < modulus) :
    Runs (inverseMod regs) store
      (RuntimeArithmetic.powModResultStore regs
        (PrimeField.Runtime.inverse modulus base) store) := by
  let setAccumulator :=
    (Basic.imm regs.accumulator 1).exec store
  let setExponentPred :=
    (Basic.sub regs.exponent regs.modulus regs.one).exec
      setAccumulator
  let prepared :=
    (Basic.sub regs.exponent regs.exponent regs.one).exec
      setExponentPred
  have hsetAccumulator :
      Runs (.basic (.imm regs.accumulator 1))
        store setAccumulator :=
    Runs.basic _ _
  have hsetExponentPred :
      Runs
        (.basic
          (.sub regs.exponent regs.modulus regs.one))
        setAccumulator setExponentPred :=
    Runs.basic _ _
  have hprepareExponent :
      Runs
        (.basic
          (.sub regs.exponent regs.exponent regs.one))
        setExponentPred prepared :=
    Runs.basic _ _
  have hpreparedAccumulator :
      prepared regs.accumulator = 1 := by
    simp [prepared, setExponentPred, setAccumulator, Basic.exec,
      regs.injective.eq_iff]
  have hpreparedModulus :
      prepared regs.modulus = modulus := by
    simp [prepared, setExponentPred, setAccumulator, Basic.exec,
      regs.injective.eq_iff, hmodulusValue]
  have hpreparedModulusPred :
      prepared regs.modulusPred = modulus - 1 := by
    simp [prepared, setExponentPred, setAccumulator, Basic.exec,
      regs.injective.eq_iff, hmodulusPred]
  have hpreparedBase :
      prepared regs.base = base := by
    simp [prepared, setExponentPred, setAccumulator, Basic.exec,
      regs.injective.eq_iff, hbase]
  have hpreparedExponent :
      prepared regs.exponent = modulus - 2 := by
    simp [prepared, setExponentPred, setAccumulator, Basic.exec,
      regs.injective.eq_iff, hmodulusValue, hone]
    omega
  have hpreparedOne :
      prepared regs.one = 1 := by
    simp [prepared, setExponentPred, setAccumulator, Basic.exec,
      regs.injective.eq_iff, hone]
  have hfinal (result : ℕ) :
      RuntimeArithmetic.powModResultStore regs result prepared =
        RuntimeArithmetic.powModResultStore regs result store := by
    funext index
    by_cases hacc : index = regs.accumulator
    · subst index
      simp [RuntimeArithmetic.powModResultStore,
        regs.injective.eq_iff]
    · by_cases htestIndex : index = regs.test
      · subst index
        simp [RuntimeArithmetic.powModResultStore,
          regs.injective.eq_iff]
      · by_cases hexponentIndex : index = regs.exponent
        · subst index
          simp [RuntimeArithmetic.powModResultStore]
        · simp [RuntimeArithmetic.powModResultStore, prepared,
            setExponentPred, setAccumulator, Basic.exec,
            Function.update_of_ne, hacc, htestIndex,
            hexponentIndex]
  by_cases hzero : base = 0
  · let zeroAccumulator :=
      (Basic.imm regs.accumulator 0).exec prepared
    let zeroTest :=
      (Basic.imm regs.test 0).exec zeroAccumulator
    let zeroFinal :=
      (Basic.imm regs.exponent 0).exec zeroTest
    have hzeroAccumulator :
        Runs (.basic (.imm regs.accumulator 0))
          prepared zeroAccumulator :=
      Runs.basic _ _
    have hzeroTest :
        Runs (.basic (.imm regs.test 0))
          zeroAccumulator zeroTest :=
      Runs.basic _ _
    have hzeroExponent :
        Runs (.basic (.imm regs.exponent 0))
          zeroTest zeroFinal :=
      Runs.basic _ _
    have hzeroFinal :
        zeroFinal =
          RuntimeArithmetic.powModResultStore regs
            (PrimeField.Runtime.inverse modulus base) prepared := by
      simp [zeroFinal, zeroTest, zeroAccumulator, Basic.exec,
        RuntimeArithmetic.powModResultStore,
        PrimeField.Runtime.inverse, PrimeField.Runtime.normalize,
        hzero]
    have hzeroRun :=
      Runs.seq hzeroAccumulator
        (Runs.seq hzeroTest hzeroExponent)
    rw [hzeroFinal, hfinal] at hzeroRun
    have hbranch :
        Runs
          (.ifZero regs.base
            (.seq (.basic (.imm regs.accumulator 0))
              (.seq (.basic (.imm regs.test 0))
                (.basic (.imm regs.exponent 0))))
            (RuntimeArithmetic.powMod regs))
          prepared
          (RuntimeArithmetic.powModResultStore regs
            (PrimeField.Runtime.inverse modulus base) store) :=
      Runs.ifZero (hpreparedBase.trans hzero) hzeroRun
    simpa [inverseMod] using
      Runs.seq hsetAccumulator
        (Runs.seq hsetExponentPred
          (Runs.seq hprepareExponent hbranch))
  · have hpow :=
      RuntimeArithmetic.powMod_runs regs prepared modulus base
        (modulus - 2) 1 hprime.pos hpreparedAccumulator
          hpreparedModulus hpreparedModulusPred hpreparedBase
            hpreparedExponent hpreparedOne
    have hpowResult :
        RuntimeArithmetic.powModLoop modulus base (modulus - 2) 1 =
          PrimeField.Runtime.inverse modulus base := by
      rw [powModLoop_one_eq_runtime_internal hprime.one_lt]
      simp [PrimeField.Runtime.inverse, PrimeField.Runtime.normalize,
        Nat.mod_eq_of_lt hbaseLt, hzero]
    rw [hpowResult, hfinal] at hpow
    have hbranch :
        Runs
          (.ifZero regs.base
            (.seq (.basic (.imm regs.accumulator 0))
              (.seq (.basic (.imm regs.test 0))
                (.basic (.imm regs.exponent 0))))
            (RuntimeArithmetic.powMod regs))
          prepared
          (RuntimeArithmetic.powModResultStore regs
            (PrimeField.Runtime.inverse modulus base) store) :=
      Runs.ifNonzero (by simpa [hpreparedBase] using hzero) hpow
    simpa [inverseMod] using
      Runs.seq hsetAccumulator
        (Runs.seq hsetExponentPred
          (Runs.seq hprepareExponent hbranch))

end Internal

end Runtime

end TimeSpaceSimulation

end Complexity
