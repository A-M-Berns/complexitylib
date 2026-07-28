/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.RandomAccessMachine.Internal
import Complexitylib.Models.RandomAccessMachine.Structured.ControlFlow.Defs
import Complexitylib.Models.RandomAccessMachine.Structured.Internal

/-!
# Proof internals for structured RAM control-flow bounds
-/

namespace Complexity

namespace RAM

namespace Structured

namespace ControlFlow

namespace Internal

theorem step_pc_le_internal
    {program : Program} {bound : ℕ} {cfg : Cfg}
    (htargets : ProgramTargetsWithin program bound)
    (hboundary : BoundaryHalts program bound)
    (hpc : cfg.pc ≤ bound) :
    (RAM.step program cfg).pc ≤ bound := by
  rcases lt_or_eq_of_le hpc with hlt | heq
  · unfold RAM.step
    have htarget := htargets cfg.pc
    change InstrTargetsWithin bound (RAM.curInstr program cfg) at htarget
    generalize hinstr : RAM.curInstr program cfg = instruction at htarget ⊢
    cases instruction with
    | imm => simp [RAM.stepInstr]; omega
    | add => simp [RAM.stepInstr]; omega
    | sub => simp [RAM.stepInstr]; omega
    | mul => simp [RAM.stepInstr]; omega
    | load => simp [RAM.stepInstr]; omega
    | store => simp [RAM.stepInstr]; omega
    | jz source target =>
        simp only [InstrTargetsWithin] at htarget
        simp only [RAM.stepInstr]
        split
        · simpa using htarget
        · change cfg.pc + 1 ≤ bound
          omega
    | jmp target => simpa [RAM.stepInstr] using htarget
    | halt => simpa [RAM.stepInstr] using hpc
  · have hhalted : RAM.Halted program cfg := by
      unfold RAM.Halted RAM.curInstr
      rw [heq]
      exact hboundary
    rw [RAM.step_halted program hhalted]
    exact hpc

theorem run_pc_le_internal
    {program : Program} {bound fuel : ℕ} {cfg : Cfg}
    (htargets : ProgramTargetsWithin program bound)
    (hboundary : BoundaryHalts program bound)
    (hpc : cfg.pc ≤ bound) :
    (RAM.run program fuel cfg).pc ≤ bound := by
  induction fuel generalizing cfg with
  | zero => exact hpc
  | succ fuel ih =>
      rw [RAM.run_succ]
      by_cases hhalted : RAM.Halted program cfg
      · rw [if_pos hhalted]
        exact hpc
      · rw [if_neg hhalted]
        exact ih (step_pc_le_internal htargets hboundary hpc)

private theorem instrTargetsWithin_mono
    {instruction : Instr} {bound larger : ℕ}
    (htarget : InstrTargetsWithin bound instruction)
    (hle : bound ≤ larger) :
    InstrTargetsWithin larger instruction := by
  cases instruction <;>
    simp_all [InstrTargetsWithin] <;>
    omega

private theorem compileAt_targets_of_le
    (cmd : Cmd) {start bound : ℕ}
    (hle : start + cmd.codeSize ≤ bound) :
    (cmd.compileAt start).Forall (InstrTargetsWithin bound) := by
  induction cmd generalizing start with
  | skip => simp [Cmd.compileAt]
  | basic op =>
      cases op <;>
        simp [Cmd.compileAt, Basic.instr, InstrTargetsWithin]
  | seq first second ihFirst ihSecond =>
      simp only [Cmd.compileAt, List.forall_append]
      constructor
      · apply ihFirst
        simp only [Cmd.codeSize] at hle ⊢
        omega
      · apply ihSecond
        simp only [Cmd.codeSize] at hle ⊢
        omega
  | ifZero test onZero onNonzero ihZero ihNonzero =>
      change start + (2 + onZero.codeSize + onNonzero.codeSize) ≤
        bound at hle
      have hnonzero := ihNonzero (start := start + 1) (by omega)
      have hzero := ihZero
        (start := start + 1 + onNonzero.codeSize + 1) (by omega)
      simpa [Cmd.compileAt, Cmd.codeSize, InstrTargetsWithin] using
        And.intro
          (show start + 1 + onNonzero.codeSize + 1 ≤ bound by omega)
          (And.intro hnonzero (And.intro hle hzero))
  | whileNonzero test body ih =>
      change start + (body.codeSize + 2) ≤ bound at hle
      have hbody := ih (start := start + 1) (by omega)
      simpa [Cmd.compileAt, Cmd.codeSize, InstrTargetsWithin] using
        And.intro hle
          (And.intro hbody (show start ≤ bound by omega))

theorem Cmd.compile_targetsWithin_internal (cmd : Cmd) :
    ProgramTargetsWithin cmd.compile cmd.codeSize := by
  have hbody : (cmd.compileAt 0).Forall
      (InstrTargetsWithin cmd.codeSize) :=
    compileAt_targets_of_le cmd (by simp)
  have hall : cmd.compile.Forall
      (InstrTargetsWithin cmd.codeSize) := by
    simp [Cmd.compile, hbody, InstrTargetsWithin]
  intro pc
  cases hget : cmd.compile[pc]? with
  | none =>
      simp [InstrTargetsWithin]
  | some instruction =>
      have hmem : instruction ∈ cmd.compile :=
        List.mem_of_getElem? hget
      have hinstruction :
          InstrTargetsWithin cmd.codeSize instruction :=
        List.forall_iff_forall_mem.mp hall instruction hmem
      simpa only [Option.getD_some] using hinstruction

theorem Cmd.compile_boundaryHalts_internal (cmd : Cmd) :
    BoundaryHalts cmd.compile cmd.codeSize := by
  simp [BoundaryHalts, Cmd.compile, Cmd.length_compileAt]

theorem Cmd.run_compile_pc_le_internal
    (cmd : Cmd) (initial : Store) (fuel : ℕ) :
    (RAM.run cmd.compile fuel { pc := 0, regs := initial }).pc ≤
      cmd.codeSize := by
  exact run_pc_le_internal
    (Cmd.compile_targetsWithin_internal cmd)
    (Cmd.compile_boundaryHalts_internal cmd) (by simp)

end Internal

end ControlFlow

end Structured

end RAM

end Complexity
