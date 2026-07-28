/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.Models.RandomAccessMachine.Structured.Footprint
import
  Complexitylib.Models.RandomAccessMachine.Structured.Run
import
  Complexitylib.Models.RandomAccessMachine.Structured.RuntimeArithmetic
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.CombineValue.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.Layout
import
  Complexitylib.TreeEvaluation.CookMertz.PrimeField.Runtime

/-!
# Fixed-register range folds for local residue combination -- proofs
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace CombineValue
namespace Internal

open RAM Structured
open TreeEval CookMertz

variable {controller : SearchProgram.Registers}

private theorem foldCommand_runs
    (op : FoldOp) (regs : RangeRegisters)
    (store : Store) (modulus : ℕ)
    (hmodulus : 0 < modulus)
    (hmodulusValue : store regs.modulus = modulus)
    (hmodulusPred : store regs.modulusPred = modulus - 1) :
    Runs (foldCommand op regs) store
      (RuntimeArithmetic.reduceResultStore regs.reduceRegisters
        (op.apply modulus (store regs.term)
          (store regs.accumulator))
        store) := by
  cases op with
  | add =>
      simpa [foldCommand, FoldOp.apply,
        PrimeField.Runtime.add, PrimeField.Runtime.addInput,
        PrimeField.Runtime.normalize, Nat.add_mod] using
        RuntimeArithmetic.addMod_runs regs.reduceRegisters
          regs.term regs.accumulator store modulus hmodulus
          hmodulusValue hmodulusPred
  | mul =>
      simpa [foldCommand, FoldOp.apply,
        PrimeField.Runtime.mul, PrimeField.Runtime.mulInput,
        PrimeField.Runtime.normalize, Nat.mul_mod] using
        RuntimeArithmetic.mulMod_runs regs.reduceRegisters
          regs.term regs.accumulator store modulus hmodulus
          hmodulusValue hmodulusPred

private theorem rangeFoldFromLoop_runs
    (op : FoldOp) (regs : RangeRegisters)
    (termKernel : Cmd) (term : ℕ → ℕ)
    (modulus count accumulator : ℕ)
    (hspec : TermKernelSpecAt regs termKernel modulus term)
    (store : Store)
    (hmodulus : 0 < modulus)
    (hremaining : store regs.remaining = count)
    (haccumulator : store regs.accumulator = accumulator)
    (hmodulusValue : store regs.modulus = modulus)
    (hmodulusPred : store regs.modulusPred = modulus - 1)
    (hone : store regs.one = 1) :
    ∃ final,
      Runs (rangeFoldFrom op regs termKernel) store final ∧
      RangeFromPost op regs modulus count accumulator term store final := by
  induction count generalizing store accumulator with
  | zero =>
      have hzero : store regs.remaining = 0 := by
        simpa using hremaining
      refine ⟨store, ?_, ?_⟩
      · simpa [rangeFoldFrom] using Runs.whileZero hzero
      · exact
          { accumulator_eq := by
              simpa [FoldOp.fold] using haccumulator
            remaining_eq := hzero
            modulus_eq := hmodulusValue
            modulusPred_eq := hmodulusPred
            one_eq := hone
            count_eq := rfl }
  | succ count ih =>
      have hnonzero : store regs.remaining ≠ 0 := by
        rw [hremaining]
        omega
      let afterDecrement :=
        (Basic.sub regs.remaining regs.remaining regs.one).exec store
      have hdecrementRun :
          Runs (.basic
            (.sub regs.remaining regs.remaining regs.one))
            store afterDecrement :=
        Runs.basic _ _
      have hdecrementRemaining :
          afterDecrement regs.remaining = count := by
        simp [afterDecrement, Basic.exec, hremaining, hone]
      have hdecrementAccumulator :
          afterDecrement regs.accumulator = accumulator := by
        simp [afterDecrement, Basic.exec, regs.injective.eq_iff,
          haccumulator]
      have hdecrementModulus :
          afterDecrement regs.modulus = modulus := by
        simp [afterDecrement, Basic.exec, regs.injective.eq_iff,
          hmodulusValue]
      have hdecrementModulusPred :
          afterDecrement regs.modulusPred = modulus - 1 := by
        simp [afterDecrement, Basic.exec, regs.injective.eq_iff,
          hmodulusPred]
      have hdecrementOne :
          afterDecrement regs.one = 1 := by
        simp [afterDecrement, Basic.exec, regs.injective.eq_iff, hone]
      have hdecrementCount :
          afterDecrement regs.count = store regs.count := by
        simp [afterDecrement, Basic.exec, regs.injective.eq_iff]
      obtain ⟨afterTerm, htermRun, htermPost⟩ :=
        hspec afterDecrement count hdecrementRemaining
          hdecrementModulus hdecrementModulusPred hdecrementOne
      have htermAccumulator :
          afterTerm regs.accumulator = accumulator :=
        htermPost.accumulator_eq.trans hdecrementAccumulator
      have htermModulus :
          afterTerm regs.modulus = modulus :=
        htermPost.modulus_eq.trans hdecrementModulus
      have htermModulusPred :
          afterTerm regs.modulusPred = modulus - 1 :=
        htermPost.modulusPred_eq.trans hdecrementModulusPred
      have htermOne :
          afterTerm regs.one = 1 :=
        htermPost.one_eq.trans hdecrementOne
      let nextAccumulator :=
        op.apply modulus (term count) accumulator
      let afterFold :=
        RuntimeArithmetic.reduceResultStore regs.reduceRegisters
          nextAccumulator afterTerm
      have hfoldRun :
          Runs (foldCommand op regs) afterTerm afterFold := by
        simpa [afterFold, nextAccumulator, htermPost.term_eq,
          htermAccumulator] using
          foldCommand_runs op regs afterTerm modulus hmodulus
            htermModulus htermModulusPred
      have hfoldAccumulator :
          afterFold regs.accumulator = nextAccumulator := by
        simp [afterFold, RuntimeArithmetic.reduceResultStore,
          RangeRegisters.reduceRegisters, regs.injective.eq_iff]
      have hfoldRemaining :
          afterFold regs.remaining = count := by
        simp [afterFold, RuntimeArithmetic.reduceResultStore,
          RangeRegisters.reduceRegisters, regs.injective.eq_iff,
          htermPost.remaining_eq]
      have hfoldModulus :
          afterFold regs.modulus = modulus := by
        simp [afterFold, RuntimeArithmetic.reduceResultStore,
          RangeRegisters.reduceRegisters, regs.injective.eq_iff,
          htermModulus]
      have hfoldModulusPred :
          afterFold regs.modulusPred = modulus - 1 := by
        simp [afterFold, RuntimeArithmetic.reduceResultStore,
          RangeRegisters.reduceRegisters, regs.injective.eq_iff,
          htermModulusPred]
      have hfoldOne :
          afterFold regs.one = 1 := by
        simp [afterFold, RuntimeArithmetic.reduceResultStore,
          RangeRegisters.reduceRegisters, regs.injective.eq_iff,
          htermOne]
      have hfoldCount :
          afterFold regs.count = afterTerm regs.count := by
        simp [afterFold, RuntimeArithmetic.reduceResultStore,
          RangeRegisters.reduceRegisters, regs.injective.eq_iff]
      obtain ⟨final, hrest, hrestPost⟩ :=
        ih nextAccumulator afterFold hfoldRemaining hfoldAccumulator
          hfoldModulus hfoldModulusPred hfoldOne
      have hbody :
          Runs (foldBody op regs termKernel) store afterFold := by
        simpa [foldBody] using
          Runs.seq hdecrementRun (Runs.seq htermRun hfoldRun)
      refine ⟨final, ?_, ?_⟩
      · simpa [rangeFoldFrom] using
          Runs.whileNonzero hnonzero hbody hrest
      · exact
          { accumulator_eq := by
              simpa [FoldOp.fold, nextAccumulator] using
                hrestPost.accumulator_eq
            remaining_eq := hrestPost.remaining_eq
            modulus_eq := hrestPost.modulus_eq
            modulusPred_eq := hrestPost.modulusPred_eq
            one_eq := hrestPost.one_eq
            count_eq := by
              exact hrestPost.count_eq.trans
                (hfoldCount.trans
                  (htermPost.count_eq.trans hdecrementCount)) }

private theorem decrement_writesWithin_driver
    (regs : RangeRegisters) :
    RAM.Structured.Footprint.CmdWritesWithin
      regs.driverWriteFootprint
      (.basic (.sub regs.remaining regs.remaining regs.one)) := by
  simp [RangeRegisters.driverWriteFootprint,
    RAM.Structured.Footprint.CmdWritesWithin,
    RAM.Structured.Footprint.BasicWritesWithin]

private theorem foldCommand_writesWithin_driver
    (op : FoldOp) (regs : RangeRegisters) :
    RAM.Structured.Footprint.CmdWritesWithin
      regs.driverWriteFootprint (foldCommand op regs) := by
  cases op <;>
    simp [foldCommand, RuntimeArithmetic.addMod,
      RuntimeArithmetic.mulMod, RuntimeArithmetic.reduce,
      RuntimeArithmetic.reduceBody, RuntimeArithmetic.reduceTestOp,
      RangeRegisters.reduceRegisters,
      RangeRegisters.driverWriteFootprint,
      RAM.Structured.Footprint.CmdWritesWithin,
      RAM.Structured.Footprint.BasicWritesWithin]

private theorem rangeFoldFromLoop_runsContext
    (op : FoldOp) (regs : RangeRegisters)
    (termKernel : Cmd) (term : ℕ → ℕ)
    (modulus count accumulator : ℕ)
    (context : Store → Prop)
    (hstable : StableUnderDriverWrites regs context)
    (hspec :
      TermKernelSpecAtContext regs termKernel modulus term context)
    (store : Store)
    (hmodulus : 0 < modulus)
    (hremaining : store regs.remaining = count)
    (haccumulator : store regs.accumulator = accumulator)
    (hmodulusValue : store regs.modulus = modulus)
    (hmodulusPred : store regs.modulusPred = modulus - 1)
    (hone : store regs.one = 1)
    (hcontext : context store) :
    ∃ final,
      Runs (rangeFoldFrom op regs termKernel) store final ∧
      RangeFromPost op regs modulus count accumulator term store final ∧
      context final := by
  induction count generalizing store accumulator with
  | zero =>
      have hzero : store regs.remaining = 0 := by
        simpa using hremaining
      refine ⟨store, ?_, ?_, hcontext⟩
      · simpa [rangeFoldFrom] using Runs.whileZero hzero
      · exact
          { accumulator_eq := by
              simpa [FoldOp.fold] using haccumulator
            remaining_eq := hzero
            modulus_eq := hmodulusValue
            modulusPred_eq := hmodulusPred
            one_eq := hone
            count_eq := rfl }
  | succ count ih =>
      have hnonzero : store regs.remaining ≠ 0 := by
        rw [hremaining]
        omega
      let afterDecrement :=
        (Basic.sub regs.remaining regs.remaining regs.one).exec store
      have hdecrementRun :
          Runs (.basic
            (.sub regs.remaining regs.remaining regs.one))
            store afterDecrement :=
        Runs.basic _ _
      have hdecrementContext : context afterDecrement := by
        apply hstable hcontext
        intro address haddress
        exact RAM.Structured.Footprint.runs_eq_outside
          (decrement_writesWithin_driver regs)
          hdecrementRun haddress
      have hdecrementRemaining :
          afterDecrement regs.remaining = count := by
        simp [afterDecrement, Basic.exec, hremaining, hone]
      have hdecrementAccumulator :
          afterDecrement regs.accumulator = accumulator := by
        simp [afterDecrement, Basic.exec, regs.injective.eq_iff,
          haccumulator]
      have hdecrementModulus :
          afterDecrement regs.modulus = modulus := by
        simp [afterDecrement, Basic.exec, regs.injective.eq_iff,
          hmodulusValue]
      have hdecrementModulusPred :
          afterDecrement regs.modulusPred = modulus - 1 := by
        simp [afterDecrement, Basic.exec, regs.injective.eq_iff,
          hmodulusPred]
      have hdecrementOne :
          afterDecrement regs.one = 1 := by
        simp [afterDecrement, Basic.exec, regs.injective.eq_iff, hone]
      have hdecrementCount :
          afterDecrement regs.count = store regs.count := by
        simp [afterDecrement, Basic.exec, regs.injective.eq_iff]
      obtain ⟨afterTerm, htermRun, htermPost, htermContext⟩ :=
        hspec afterDecrement count hdecrementContext
          hdecrementRemaining hdecrementModulus
          hdecrementModulusPred hdecrementOne
      have htermAccumulator :
          afterTerm regs.accumulator = accumulator :=
        htermPost.accumulator_eq.trans hdecrementAccumulator
      have htermModulus :
          afterTerm regs.modulus = modulus :=
        htermPost.modulus_eq.trans hdecrementModulus
      have htermModulusPred :
          afterTerm regs.modulusPred = modulus - 1 :=
        htermPost.modulusPred_eq.trans hdecrementModulusPred
      have htermOne :
          afterTerm regs.one = 1 :=
        htermPost.one_eq.trans hdecrementOne
      let nextAccumulator :=
        op.apply modulus (term count) accumulator
      let afterFold :=
        RuntimeArithmetic.reduceResultStore regs.reduceRegisters
          nextAccumulator afterTerm
      have hfoldRun :
          Runs (foldCommand op regs) afterTerm afterFold := by
        simpa [afterFold, nextAccumulator, htermPost.term_eq,
          htermAccumulator] using
          foldCommand_runs op regs afterTerm modulus hmodulus
            htermModulus htermModulusPred
      have hfoldContext : context afterFold := by
        apply hstable htermContext
        intro address haddress
        exact RAM.Structured.Footprint.runs_eq_outside
          (foldCommand_writesWithin_driver op regs)
          hfoldRun haddress
      have hfoldAccumulator :
          afterFold regs.accumulator = nextAccumulator := by
        simp [afterFold, RuntimeArithmetic.reduceResultStore,
          RangeRegisters.reduceRegisters, regs.injective.eq_iff]
      have hfoldRemaining :
          afterFold regs.remaining = count := by
        simp [afterFold, RuntimeArithmetic.reduceResultStore,
          RangeRegisters.reduceRegisters, regs.injective.eq_iff,
          htermPost.remaining_eq]
      have hfoldModulus :
          afterFold regs.modulus = modulus := by
        simp [afterFold, RuntimeArithmetic.reduceResultStore,
          RangeRegisters.reduceRegisters, regs.injective.eq_iff,
          htermModulus]
      have hfoldModulusPred :
          afterFold regs.modulusPred = modulus - 1 := by
        simp [afterFold, RuntimeArithmetic.reduceResultStore,
          RangeRegisters.reduceRegisters, regs.injective.eq_iff,
          htermModulusPred]
      have hfoldOne :
          afterFold regs.one = 1 := by
        simp [afterFold, RuntimeArithmetic.reduceResultStore,
          RangeRegisters.reduceRegisters, regs.injective.eq_iff,
          htermOne]
      have hfoldCount :
          afterFold regs.count = afterTerm regs.count := by
        simp [afterFold, RuntimeArithmetic.reduceResultStore,
          RangeRegisters.reduceRegisters, regs.injective.eq_iff]
      obtain ⟨final, hrest, hrestPost, hrestContext⟩ :=
        ih nextAccumulator afterFold hfoldRemaining hfoldAccumulator
          hfoldModulus hfoldModulusPred hfoldOne hfoldContext
      have hbody :
          Runs (foldBody op regs termKernel) store afterFold := by
        simpa [foldBody] using
          Runs.seq hdecrementRun (Runs.seq htermRun hfoldRun)
      refine ⟨final, ?_, ?_, hrestContext⟩
      · simpa [rangeFoldFrom] using
          Runs.whileNonzero hnonzero hbody hrest
      · exact
          { accumulator_eq := by
              simpa [FoldOp.fold, nextAccumulator] using
                hrestPost.accumulator_eq
            remaining_eq := hrestPost.remaining_eq
            modulus_eq := hrestPost.modulus_eq
            modulusPred_eq := hrestPost.modulusPred_eq
            one_eq := hrestPost.one_eq
            count_eq := by
              exact hrestPost.count_eq.trans
                (hfoldCount.trans
                  (htermPost.count_eq.trans hdecrementCount)) }

theorem rangeFoldFrom_runs_internal
    (op : FoldOp) (regs : RangeRegisters)
    (termKernel : Cmd) (term : ℕ → ℕ)
    (hspec : TermKernelSpec regs termKernel term)
    (store : Store)
    (modulus count accumulator : ℕ)
    (hmodulus : 0 < modulus)
    (hremaining : store regs.remaining = count)
    (haccumulator : store regs.accumulator = accumulator)
    (hmodulusValue : store regs.modulus = modulus)
    (hmodulusPred : store regs.modulusPred = modulus - 1)
    (hone : store regs.one = 1) :
    ∃ final,
      Runs (rangeFoldFrom op regs termKernel) store final ∧
      RangeFromPost op regs modulus count accumulator term store final :=
  rangeFoldFromLoop_runs op regs termKernel term
    modulus count accumulator
    (fun current index hindex _ _ _ =>
      hspec current index hindex)
    store
    hmodulus hremaining haccumulator
    hmodulusValue hmodulusPred hone

theorem rangeFoldFrom_runsAt_internal
    (op : FoldOp) (regs : RangeRegisters)
    (termKernel : Cmd) (term : ℕ → ℕ)
    (modulus count accumulator : ℕ)
    (hspec : TermKernelSpecAt regs termKernel modulus term)
    (store : Store)
    (hmodulus : 0 < modulus)
    (hremaining : store regs.remaining = count)
    (haccumulator : store regs.accumulator = accumulator)
    (hmodulusValue : store regs.modulus = modulus)
    (hmodulusPred : store regs.modulusPred = modulus - 1)
    (hone : store regs.one = 1) :
    ∃ final,
      Runs (rangeFoldFrom op regs termKernel) store final ∧
      RangeFromPost op regs modulus count accumulator term store final :=
  rangeFoldFromLoop_runs op regs termKernel term
    modulus count accumulator hspec store
    hmodulus hremaining haccumulator
    hmodulusValue hmodulusPred hone

theorem rangeFoldFrom_runsAtContext_internal
    (op : FoldOp) (regs : RangeRegisters)
    (termKernel : Cmd) (term : ℕ → ℕ)
    (modulus count accumulator : ℕ)
    (context : Store → Prop)
    (hstable : StableUnderDriverWrites regs context)
    (hspec :
      TermKernelSpecAtContext regs termKernel modulus term context)
    (store : Store)
    (hmodulus : 0 < modulus)
    (hremaining : store regs.remaining = count)
    (haccumulator : store regs.accumulator = accumulator)
    (hmodulusValue : store regs.modulus = modulus)
    (hmodulusPred : store regs.modulusPred = modulus - 1)
    (hone : store regs.one = 1)
    (hcontext : context store) :
    ∃ final,
      Runs (rangeFoldFrom op regs termKernel) store final ∧
      RangeFromPost op regs modulus count accumulator term store final ∧
      context final :=
  rangeFoldFromLoop_runsContext op regs termKernel term
    modulus count accumulator context hstable hspec store
    hmodulus hremaining haccumulator hmodulusValue
    hmodulusPred hone hcontext

private theorem initializeFold_runs
    (op : FoldOp) (regs : RangeRegisters)
    (store : Store) (modulus count : ℕ)
    (hmodulus : 0 < modulus)
    (hmodulusValue : store regs.modulus = modulus)
    (hmodulusPred : store regs.modulusPred = modulus - 1)
    (hcount : store regs.count = count) :
    ∃ final,
      Runs (initializeFold op regs) store final ∧
      final regs.accumulator = op.identity modulus ∧
      final regs.remaining = count ∧
      final regs.modulus = modulus ∧
      final regs.modulusPred = modulus - 1 ∧
      final regs.one = 1 ∧
      final regs.count = count := by
  let rawIdentity :=
    match op with
    | .add => 0
    | .mul => 1
  let afterOne := (Basic.imm regs.one 1).exec store
  let afterClear :=
    (Basic.imm regs.remaining 0).exec afterOne
  let afterCopy :=
    (Basic.add regs.remaining regs.count regs.remaining).exec
      afterClear
  let afterIdentity :=
    (Basic.imm regs.accumulator rawIdentity).exec afterCopy
  let final :=
    RuntimeArithmetic.reduceResultStore regs.reduceRegisters
      (rawIdentity % modulus) afterIdentity
  have hcopy :
      Runs (copy regs.remaining regs.count) afterOne afterCopy := by
    simpa [copy, afterClear, afterCopy] using
      Runs.seq
        (Runs.basic (Basic.imm regs.remaining 0) afterOne)
        (Runs.basic
          (Basic.add regs.remaining regs.count regs.remaining)
          afterClear)
  have hafterIdentityValue :
      afterIdentity regs.accumulator = rawIdentity := by
    simp [afterIdentity, Basic.exec]
  have hafterIdentityModulus :
      afterIdentity regs.modulus = modulus := by
    simp [afterIdentity, afterCopy, afterClear, afterOne,
      Basic.exec, regs.injective.eq_iff, hmodulusValue]
  have hafterIdentityModulusPred :
      afterIdentity regs.modulusPred = modulus - 1 := by
    simp [afterIdentity, afterCopy, afterClear, afterOne,
      Basic.exec, regs.injective.eq_iff, hmodulusPred]
  have hreduce :
      Runs (RuntimeArithmetic.reduce regs.reduceRegisters)
        afterIdentity final := by
    simpa [final] using
      RuntimeArithmetic.reduce_runs regs.reduceRegisters
        afterIdentity modulus rawIdentity hmodulus
        hafterIdentityValue hafterIdentityModulus
        hafterIdentityModulusPred
  have hinitialize :
      Runs (initializeFold op regs) store final := by
    simpa [initializeFold, rawIdentity, Cmd.seqList] using
      Runs.seq (Runs.basic (Basic.imm regs.one 1) store)
        (Runs.seq hcopy
          (Runs.seq
            (Runs.basic
              (Basic.imm regs.accumulator rawIdentity) afterCopy)
            hreduce))
  refine ⟨final, hinitialize, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · cases op <;>
      simp [final, rawIdentity,
        RuntimeArithmetic.reduceResultStore,
        RangeRegisters.reduceRegisters, FoldOp.identity,
        PrimeField.Runtime.normalize, regs.injective.eq_iff]
  · simp [final, afterIdentity, afterCopy, afterClear, afterOne,
      RuntimeArithmetic.reduceResultStore,
      RangeRegisters.reduceRegisters, Basic.exec,
      regs.injective.eq_iff, hcount]
  · simp [final, afterIdentity, afterCopy, afterClear, afterOne,
      RuntimeArithmetic.reduceResultStore,
      RangeRegisters.reduceRegisters, Basic.exec,
      regs.injective.eq_iff, hmodulusValue]
  · simp [final, afterIdentity, afterCopy, afterClear, afterOne,
      RuntimeArithmetic.reduceResultStore,
      RangeRegisters.reduceRegisters, Basic.exec,
      regs.injective.eq_iff, hmodulusPred]
  · simp [final, afterIdentity, afterCopy, afterClear, afterOne,
      RuntimeArithmetic.reduceResultStore,
      RangeRegisters.reduceRegisters, Basic.exec,
      regs.injective.eq_iff]
  · simp [final, afterIdentity, afterCopy, afterClear, afterOne,
      RuntimeArithmetic.reduceResultStore,
      RangeRegisters.reduceRegisters, Basic.exec,
      regs.injective.eq_iff, hcount]

private theorem initializeFold_writesWithin_driver
    (op : FoldOp) (regs : RangeRegisters) :
    RAM.Structured.Footprint.CmdWritesWithin
      regs.driverWriteFootprint (initializeFold op regs) := by
  cases op <;>
    simp [initializeFold, copy, RuntimeArithmetic.reduce,
      RuntimeArithmetic.reduceBody, RuntimeArithmetic.reduceTestOp,
      RangeRegisters.reduceRegisters,
      RangeRegisters.driverWriteFootprint, Cmd.seqList,
      RAM.Structured.Footprint.CmdWritesWithin,
      RAM.Structured.Footprint.BasicWritesWithin]

theorem rangeFold_runsAt_internal
    (op : FoldOp) (regs : RangeRegisters)
    (termKernel : Cmd) (term : ℕ → ℕ)
    (store : Store) (modulus count : ℕ)
    (hspec : TermKernelSpecAt regs termKernel modulus term)
    (hmodulus : 0 < modulus)
    (hmodulusValue : store regs.modulus = modulus)
    (hmodulusPred : store regs.modulusPred = modulus - 1)
    (hcount : store regs.count = count) :
    ∃ final,
      Runs (rangeFold op regs termKernel) store final ∧
      RangePost op regs modulus count term store final := by
  obtain
    ⟨initialized, hinitialize, haccumulator, hremaining,
      hinitializedModulus, hinitializedModulusPred, hone,
      hinitializedCount⟩ :=
    initializeFold_runs op regs store modulus count hmodulus
      hmodulusValue hmodulusPred hcount
  obtain ⟨final, hfold, hpost⟩ :=
    rangeFoldFrom_runsAt_internal op regs termKernel term
      modulus count (op.identity modulus) hspec initialized hmodulus
      hremaining haccumulator hinitializedModulus
      hinitializedModulusPred hone
  refine ⟨final, ?_, ?_⟩
  · simpa [rangeFold] using Runs.seq hinitialize hfold
  · exact
      { accumulator_eq := by
          simpa [FoldOp.range] using hpost.accumulator_eq
        remaining_eq := hpost.remaining_eq
        modulus_eq := hpost.modulus_eq
        modulusPred_eq := hpost.modulusPred_eq
        one_eq := hpost.one_eq
        count_eq := hpost.count_eq.trans hinitializedCount }

theorem rangeFold_runsAtContext_internal
    (op : FoldOp) (regs : RangeRegisters)
    (termKernel : Cmd) (term : ℕ → ℕ)
    (store : Store) (modulus count : ℕ)
    (context : Store → Prop)
    (hstable : StableUnderDriverWrites regs context)
    (hspec :
      TermKernelSpecAtContext regs termKernel modulus term context)
    (hmodulus : 0 < modulus)
    (hmodulusValue : store regs.modulus = modulus)
    (hmodulusPred : store regs.modulusPred = modulus - 1)
    (hcount : store regs.count = count)
    (hcontext : context store) :
    ∃ final,
      Runs (rangeFold op regs termKernel) store final ∧
      RangePost op regs modulus count term store final ∧
      context final := by
  obtain
    ⟨initialized, hinitialize, haccumulator, hremaining,
      hinitializedModulus, hinitializedModulusPred, hone,
      hinitializedCount⟩ :=
    initializeFold_runs op regs store modulus count hmodulus
      hmodulusValue hmodulusPred hcount
  have hinitializedContext : context initialized := by
    apply hstable hcontext
    intro address haddress
    exact RAM.Structured.Footprint.runs_eq_outside
      (initializeFold_writesWithin_driver op regs)
      hinitialize haddress
  obtain ⟨final, hfold, hpost, hfinalContext⟩ :=
    rangeFoldFrom_runsAtContext_internal op regs termKernel term
      modulus count (op.identity modulus) context hstable hspec
      initialized hmodulus hremaining haccumulator
      hinitializedModulus hinitializedModulusPred hone
      hinitializedContext
  refine ⟨final, ?_, ?_, hfinalContext⟩
  · simpa [rangeFold] using Runs.seq hinitialize hfold
  · exact
      { accumulator_eq := by
          simpa [FoldOp.range] using hpost.accumulator_eq
        remaining_eq := hpost.remaining_eq
        modulus_eq := hpost.modulus_eq
        modulusPred_eq := hpost.modulusPred_eq
        one_eq := hpost.one_eq
        count_eq := hpost.count_eq.trans hinitializedCount }

theorem rangeFold_runs_internal
    (op : FoldOp) (regs : RangeRegisters)
    (termKernel : Cmd) (term : ℕ → ℕ)
    (hspec : TermKernelSpec regs termKernel term)
    (store : Store) (modulus count : ℕ)
    (hmodulus : 0 < modulus)
    (hmodulusValue : store regs.modulus = modulus)
    (hmodulusPred : store regs.modulusPred = modulus - 1)
    (hcount : store regs.count = count) :
    ∃ final,
      Runs (rangeFold op regs termKernel) store final ∧
      RangePost op regs modulus count term store final :=
  rangeFold_runsAt_internal op regs termKernel term store
    modulus count
    (fun current index hindex _ _ _ =>
      hspec current index hindex)
    hmodulus hmodulusValue hmodulusPred hcount

private theorem combineScratch_mem
    (regs : NeighborhoodTrial.Registers controller)
    (slot : Fin 19) :
    regs.index (combineScratchMap slot) ∈
      combineScratchFootprint regs := by
  exact Finset.mem_image.mpr ⟨slot, Finset.mem_univ _, rfl⟩

theorem combineScratchFootprint_subset_layout_internal
    (regs : NeighborhoodTrial.Registers controller) :
    combineScratchFootprint regs ⊆ regs.layout.footprint := by
  intro address haddress
  obtain ⟨slot, _, rfl⟩ := Finset.mem_image.mp haddress
  exact Layout.index_mem_layout_footprint regs (combineScratchMap slot)

theorem rangeFold_writesWithin_internal
    (op : FoldOp)
    (regs : NeighborhoodTrial.Registers controller)
    (termKernel : Cmd)
    (hkernel :
      RAM.Structured.Footprint.CmdWritesWithin
        (combineScratchFootprint regs) termKernel) :
    RAM.Structured.Footprint.CmdWritesWithin
      (combineScratchFootprint regs)
      (rangeFold op (rangeRegisters regs) termKernel) := by
  have hAccumulator := combineScratch_mem regs (10 : Fin 19)
  have hTest := combineScratch_mem regs (3 : Fin 19)
  have hRemaining := combineScratch_mem regs (13 : Fin 19)
  have hOne := combineScratch_mem regs (9 : Fin 19)
  change (rangeRegisters regs).accumulator ∈
    combineScratchFootprint regs at hAccumulator
  change (rangeRegisters regs).test ∈
    combineScratchFootprint regs at hTest
  change (rangeRegisters regs).remaining ∈
    combineScratchFootprint regs at hRemaining
  change (rangeRegisters regs).one ∈
    combineScratchFootprint regs at hOne
  cases op <;>
    simp_all [rangeFold, initializeFold, rangeFoldFrom, foldBody,
      foldCommand, copy, RuntimeArithmetic.addMod,
      RuntimeArithmetic.mulMod, RuntimeArithmetic.reduce,
      RuntimeArithmetic.reduceBody, RuntimeArithmetic.reduceTestOp,
      RangeRegisters.reduceRegisters,
      Cmd.seqList, RAM.Structured.Footprint.CmdWritesWithin,
      RAM.Structured.Footprint.BasicWritesWithin]

private theorem cmdWritesWithin_mono
    {smaller larger : Finset ℕ}
    (hsubset : smaller ⊆ larger) :
    ∀ command,
      RAM.Structured.Footprint.CmdWritesWithin smaller command →
      RAM.Structured.Footprint.CmdWritesWithin larger command := by
  intro command hwrites
  induction command with
  | skip => trivial
  | basic op =>
      cases op <;>
        simp_all [RAM.Structured.Footprint.CmdWritesWithin,
          RAM.Structured.Footprint.BasicWritesWithin] <;>
        exact hsubset hwrites
  | seq first second firstIH secondIH =>
      exact ⟨firstIH hwrites.1, secondIH hwrites.2⟩
  | ifZero test onZero onNonzero zeroIH nonzeroIH =>
      exact ⟨zeroIH hwrites.1, nonzeroIH hwrites.2⟩
  | whileNonzero test body bodyIH =>
      exact bodyIH hwrites

theorem rangeFold_layout_writesWithin_internal
    (op : FoldOp)
    (regs : NeighborhoodTrial.Registers controller)
    (termKernel : Cmd)
    (hkernel :
      RAM.Structured.Footprint.CmdWritesWithin
        (combineScratchFootprint regs) termKernel) :
    RAM.Structured.Footprint.CmdWritesWithin
      regs.layout.footprint
      (rangeFold op (rangeRegisters regs) termKernel) := by
  exact cmdWritesWithin_mono
    (combineScratchFootprint_subset_layout_internal regs) _
    (rangeFold_writesWithin_internal op regs termKernel hkernel)

private theorem abi_outside_combineScratch
    (regs : NeighborhoodTrial.Registers controller) :
    Layout.fuel regs ∉ combineScratchFootprint regs ∧
    Layout.nodeCode regs ∉ combineScratchFootprint regs ∧
    Layout.scalar regs ∉ combineScratchFootprint regs ∧
    Layout.out regs ∉ combineScratchFootprint regs ∧
    Layout.phaseCode regs ∉ combineScratchFootprint regs ∧
    Layout.active regs ∉ combineScratchFootprint regs ∧
    Layout.blockLength regs ∉ combineScratchFootprint regs ∧
    Layout.horizon regs ∉ combineScratchFootprint regs ∧
    Layout.chunkCount regs ∉ combineScratchFootprint regs ∧
    Layout.chunkRadix regs ∉ combineScratchFootprint regs ∧
    Layout.frameRadix regs ∉ combineScratchFootprint regs ∧
    Layout.bankRadix regs ∉ combineScratchFootprint regs ∧
    Layout.bankDigitCount regs ∉ combineScratchFootprint regs ∧
    Layout.modulusPred regs ∉ combineScratchFootprint regs ∧
    Layout.modulus regs ∉ combineScratchFootprint regs := by
  refine
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [combineScratchFootprint, Finset.mem_image,
      Finset.mem_univ, true_and, not_exists] <;>
    intro slot heq <;>
    have hslot := regs.injective heq <;>
    change combineScratchMap slot = _ at hslot <;>
    fin_cases slot <;>
    contradiction

theorem preservesABI_of_combineScratch_internal
    (regs : NeighborhoodTrial.Registers controller)
    {command : Cmd}
    (hkernel :
      RAM.Structured.Footprint.CmdWritesWithin
        (combineScratchFootprint regs) command)
    {initial final : Store}
    (hrun : Runs command initial final) :
    ControlDecode.PreservesABI regs initial final := by
  rcases abi_outside_combineScratch regs with
    ⟨hfuel, hnode, hscalar, hout, hphase, hactive,
      hblock, hhorizon, hcount, hradix, hframeRadix,
      hbankRadix, hbankCount, hmodulusPred, hmodulus⟩
  exact
    { fuel_eq :=
        RAM.Structured.Footprint.runs_eq_outside
          hkernel hrun hfuel
      nodeCode_eq :=
        RAM.Structured.Footprint.runs_eq_outside
          hkernel hrun hnode
      scalar_eq :=
        RAM.Structured.Footprint.runs_eq_outside
          hkernel hrun hscalar
      out_eq :=
        RAM.Structured.Footprint.runs_eq_outside
          hkernel hrun hout
      phaseCode_eq :=
        RAM.Structured.Footprint.runs_eq_outside
          hkernel hrun hphase
      active_eq :=
        RAM.Structured.Footprint.runs_eq_outside
          hkernel hrun hactive
      blockLength_eq :=
        RAM.Structured.Footprint.runs_eq_outside
          hkernel hrun hblock
      horizon_eq :=
        RAM.Structured.Footprint.runs_eq_outside
          hkernel hrun hhorizon
      chunkCount_eq :=
        RAM.Structured.Footprint.runs_eq_outside
          hkernel hrun hcount
      chunkRadix_eq :=
        RAM.Structured.Footprint.runs_eq_outside
          hkernel hrun hradix
      frameRadix_eq :=
        RAM.Structured.Footprint.runs_eq_outside
          hkernel hrun hframeRadix
      bankRadix_eq :=
        RAM.Structured.Footprint.runs_eq_outside
          hkernel hrun hbankRadix
      bankDigitCount_eq :=
        RAM.Structured.Footprint.runs_eq_outside
          hkernel hrun hbankCount
      modulusPred_eq :=
        RAM.Structured.Footprint.runs_eq_outside
          hkernel hrun hmodulusPred
      modulus_eq :=
        RAM.Structured.Footprint.runs_eq_outside
          hkernel hrun hmodulus }

theorem rangeFold_preservesABI_internal
    (op : FoldOp)
    (regs : NeighborhoodTrial.Registers controller)
    (termKernel : Cmd)
    (hkernel :
      RAM.Structured.Footprint.CmdWritesWithin
        (combineScratchFootprint regs) termKernel)
    {initial final : Store}
    (hrun :
      Runs (rangeFold op (rangeRegisters regs) termKernel)
        initial final) :
    ControlDecode.PreservesABI regs initial final :=
  preservesABI_of_combineScratch_internal regs
    (rangeFold_writesWithin_internal op regs termKernel hkernel) hrun

private theorem fold_add_eq_foldSum
    (modulus : ℕ) (term : ℕ → ℕ)
    (count accumulator : ℕ) :
    FoldOp.fold .add modulus term count accumulator =
      NeighborhoodExecutableEvaluation.Residue.foldSum
        modulus term count accumulator := by
  induction count generalizing accumulator with
  | zero =>
      rfl
  | succ count ih =>
      simp only [FoldOp.fold, FoldOp.apply,
        NeighborhoodExecutableEvaluation.Residue.foldSum]
      exact ih _

theorem fold_add_eq_sumRange_internal
    (modulus : ℕ) (term : ℕ → ℕ) (count : ℕ) :
    FoldOp.range .add modulus term count =
      NeighborhoodExecutableEvaluation.Residue.sumRange
        modulus term count := by
  simpa [FoldOp.range, FoldOp.identity,
    NeighborhoodExecutableEvaluation.Residue.sumRange] using
    fold_add_eq_foldSum modulus term count
      (PrimeField.Runtime.normalize modulus 0)

private theorem fold_mul_eq_foldProduct
    (modulus : ℕ) (term : ℕ → ℕ)
    (count accumulator : ℕ) :
    FoldOp.fold .mul modulus term count accumulator =
      NeighborhoodExecutableEvaluation.Residue.foldProduct
        modulus term count accumulator := by
  induction count generalizing accumulator with
  | zero =>
      rfl
  | succ count ih =>
      simp only [FoldOp.fold, FoldOp.apply,
        NeighborhoodExecutableEvaluation.Residue.foldProduct]
      exact ih _

theorem fold_mul_eq_productRange_internal
    (modulus : ℕ) (term : ℕ → ℕ) (count : ℕ) :
    FoldOp.range .mul modulus term count =
      NeighborhoodExecutableEvaluation.Residue.productRange
        modulus term count := by
  simpa [FoldOp.range, FoldOp.identity,
    NeighborhoodExecutableEvaluation.Residue.productRange] using
    fold_mul_eq_foldProduct modulus term count
      (PrimeField.Runtime.normalize modulus 1)

theorem evaluateNode_eq_assignmentRange_internal
    (payloadWidth fanIn : ℕ)
    (combine :
      (Fin fanIn → Fin payloadWidth → Bool) →
        Fin payloadWidth → Bool)
    (args :
      Fin fanIn →
        Fin
          (PrimeGrouped.Logarithmic.chunkCount payloadWidth fanIn) →
          ℕ)
    (outputChunk :
      Fin
        (PrimeGrouped.Logarithmic.chunkCount payloadWidth fanIn)) :
    NeighborhoodExecutableEvaluation.Residue.evaluateNode
        payloadWidth fanIn combine args outputChunk =
      FoldOp.range .add
        (NeighborhoodExecutableEvaluation.Residue.fieldModulus
          payloadWidth fanIn)
        (assignmentTerm payloadWidth fanIn combine args outputChunk)
        (assignmentCount payloadWidth fanIn) := by
  rw [fold_add_eq_sumRange_internal]
  rfl

theorem evaluateNode_rangeFold_runs_internal
    (regs : NeighborhoodTrial.Registers controller)
    (termKernel : Cmd)
    (payloadWidth fanIn : ℕ)
    (combine :
      (Fin fanIn → Fin payloadWidth → Bool) →
        Fin payloadWidth → Bool)
    (args :
      Fin fanIn →
        Fin
          (PrimeGrouped.Logarithmic.chunkCount payloadWidth fanIn) →
          ℕ)
    (outputChunk :
      Fin
        (PrimeGrouped.Logarithmic.chunkCount payloadWidth fanIn))
    (hspec :
      CombineTermKernelSpecAt (rangeRegisters regs) termKernel
        payloadWidth fanIn combine args outputChunk)
    (hkernel :
      RAM.Structured.Footprint.CmdWritesWithin
        (combineScratchFootprint regs) termKernel)
    (store : Store)
    (hmodulus :
      0 <
        NeighborhoodExecutableEvaluation.Residue.fieldModulus
          payloadWidth fanIn)
    (hmodulusValue :
      store (rangeRegisters regs).modulus =
        NeighborhoodExecutableEvaluation.Residue.fieldModulus
          payloadWidth fanIn)
    (hmodulusPred :
      store (rangeRegisters regs).modulusPred =
        NeighborhoodExecutableEvaluation.Residue.fieldModulus
            payloadWidth fanIn -
          1)
    (hcount :
      store (rangeRegisters regs).count =
        assignmentCount payloadWidth fanIn) :
    ∃ final,
      Runs
          (rangeFold .add (rangeRegisters regs) termKernel)
          store final ∧
        final (rangeRegisters regs).accumulator =
          NeighborhoodExecutableEvaluation.Residue.evaluateNode
            payloadWidth fanIn combine args outputChunk ∧
        RangePost .add (rangeRegisters regs)
          (NeighborhoodExecutableEvaluation.Residue.fieldModulus
            payloadWidth fanIn)
          (assignmentCount payloadWidth fanIn)
          (assignmentTerm payloadWidth fanIn combine args outputChunk)
          store final ∧
        ControlDecode.PreservesABI regs store final := by
  obtain ⟨final, hrun, hpost⟩ :=
    rangeFold_runsAt_internal .add (rangeRegisters regs) termKernel
      (assignmentTerm payloadWidth fanIn combine args outputChunk)
      store
      (NeighborhoodExecutableEvaluation.Residue.fieldModulus
        payloadWidth fanIn)
      (assignmentCount payloadWidth fanIn) hspec hmodulus hmodulusValue
      hmodulusPred hcount
  refine ⟨final, hrun, ?_, hpost, ?_⟩
  · rw [hpost.accumulator_eq]
    exact
      (evaluateNode_eq_assignmentRange_internal
        payloadWidth fanIn combine args outputChunk).symm
  · exact rangeFold_preservesABI_internal
      .add regs termKernel hkernel hrun

end Internal
end CombineValue
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
