/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.DenseOverlay.Footprint
import Complexitylib.Models.RandomAccessMachine.Structured.ControlFlow
import Complexitylib.Models.RandomAccessMachine.Structured.Footprint.Defs
import Complexitylib.Models.RandomAccessMachine.Structured.Run.Defs

/-!
# Proof internals for structured RAM write footprints
-/

namespace Complexity

namespace RAM

namespace Structured

namespace Footprint

open RegisterStore DenseOverlay FixedRegisters
open FixedRegisters.Footprint

namespace Internal

theorem exec_eq_outside_internal
    {allowed : Finset ℕ} {cmd : Cmd} {initial final : Store}
    {steps cost space : ℕ}
    (hwrites : CmdWritesWithin allowed cmd)
    (hexec : Exec cmd initial final steps cost space)
    {address : ℕ} (haddress : address ∉ allowed) :
    final address = initial address := by
  induction hexec with
  | skip =>
      rfl
  | basic op store =>
      cases op <;>
        simp only [CmdWritesWithin, BasicWritesWithin] at hwrites
      all_goals
        simp only [Basic.exec]
        rw [Function.update_of_ne]
        exact fun heq => haddress (heq ▸ hwrites)
  | seq hfirst hsecond ihFirst ihSecond =>
      exact (ihSecond hwrites.2).trans (ihFirst hwrites.1)
  | ifZero htest hbranch ih =>
      exact ih hwrites.1
  | ifNonzero htest hbranch ih =>
      exact ih hwrites.2
  | whileZero htest =>
      rfl
  | whileNonzero htest hbody hloop ihBody ihLoop =>
      exact (ihLoop hwrites).trans (ihBody hwrites)

theorem runs_eq_outside_internal
    {allowed : Finset ℕ} {cmd : Cmd} {initial final : Store}
    (hwrites : CmdWritesWithin allowed cmd)
    (hrun : Runs cmd initial final)
    {address : ℕ} (haddress : address ∉ allowed) :
    final address = initial address := by
  obtain ⟨steps, cost, space, hexec⟩ := hrun
  exact exec_eq_outside_internal hwrites hexec haddress

private theorem compileAt_instructions
    {allowed : Finset ℕ} {cmd : Cmd}
    (hwrites : CmdWritesWithin allowed cmd) (start : ℕ) :
    (cmd.compileAt start).Forall
      (InstrWritesWithin allowed) := by
  induction cmd generalizing start with
  | skip =>
      simp [Cmd.compileAt]
  | basic op =>
      cases op <;>
        simp_all [Cmd.compileAt, CmdWritesWithin,
          BasicWritesWithin, Basic.instr, InstrWritesWithin]
  | seq first second ihFirst ihSecond =>
      simp only [CmdWritesWithin] at hwrites
      simp [Cmd.compileAt, ihFirst hwrites.1,
        ihSecond hwrites.2]
  | ifZero test onZero onNonzero ihZero ihNonzero =>
      simp only [CmdWritesWithin] at hwrites
      simp [Cmd.compileAt, ihZero hwrites.1,
        ihNonzero hwrites.2, InstrWritesWithin]
  | whileNonzero test body ih =>
      simp only [CmdWritesWithin] at hwrites
      simp [Cmd.compileAt, ih hwrites, InstrWritesWithin]

theorem programWritesWithin_compile_internal
    {allowed : Finset ℕ} {cmd : Cmd}
    (hwrites : CmdWritesWithin allowed cmd) :
    ProgramWritesWithin cmd.compile allowed := by
  have hall :
      cmd.compile.Forall
        (InstrWritesWithin allowed) := by
    simp [Cmd.compile, compileAt_instructions hwrites,
      InstrWritesWithin]
  intro pc
  cases hget : cmd.compile[pc]? with
  | none =>
      simp [InstrWritesWithin]
  | some instruction =>
      have hmem :
          instruction ∈ cmd.compile :=
        List.mem_of_getElem? hget
      have hinstruction :
          InstrWritesWithin allowed instruction :=
        List.forall_iff_forall_mem.mp hall instruction hmem
      simpa only [Option.getD_some] using hinstruction

theorem traceBound_compile_internal
    {allowed : Finset ℕ} {cmd : Cmd} {input : List Bool}
    {fuel valueBits : ℕ}
    (hwrites : CmdWritesWithin allowed cmd)
    (hzero : 0 ∈ allowed)
    (hcode : bitlen cmd.codeSize ≤ valueBits + 1)
    (hcount : bitlen allowed.card ≤ valueBits + 1)
    (haddresses : ∀ address ∈ allowed,
      bitlen address ≤ valueBits + 1)
    (hvalues : ∀ k, k ≤ fuel → ∀ address ∈ allowed,
      bitlen ((RAM.run cmd.compile k (RAM.initCfg input)).regs address) ≤
        valueBits) :
    FixedRegisters.TraceBound cmd.compile input fuel allowed.card
      (valueBits + 1) := by
  apply FixedRegisters.Footprint.TraceBound.of_footprint
  · exact programWritesWithin_compile_internal hwrites
  · exact hzero
  · intro k _hk
    have hpc :=
      ControlFlow.Cmd.run_compile_pc_le cmd (RAM.initRegs input) k
    exact (Nat.size_le_size hpc).trans hcode
  · exact hcount
  · exact haddresses
  · exact hvalues

end Internal

end Footprint

end Structured

end RAM

end Complexity
