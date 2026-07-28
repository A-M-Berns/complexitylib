/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.Models.RandomAccessMachine.Structured.Footprint
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.CombineBranch.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.CursorFinish
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.Dispatcher
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.Representation
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.ResidueBankOps
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodScheduler.FrameBounds

/-!
# Uniform combine-branch composition -- proofs
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace CombineBranch
namespace Internal

open RAM Structured
open TreeEval CookMertz

variable {controller : SearchProgram.Registers}

private theorem copy_writesWithin
    (regs : NeighborhoodTrial.Registers controller)
    (destination : Fin 34) (source : ℕ) :
    Footprint.CmdWritesWithin regs.layout.footprint
      (copy (regs.index destination) source) := by
  simp [copy, Footprint.CmdWritesWithin,
    Footprint.BasicWritesWithin,
    Layout.index_mem_layout_footprint]

private theorem installNegativeScalar_writesWithin
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin regs.layout.footprint
      (installNegativeScalar regs) := by
  simp [installNegativeScalar, copy, Cmd.seqList,
    Footprint.CmdWritesWithin, Footprint.BasicWritesWithin,
    Layout.index_mem_layout_footprint]

private theorem restoreScalar_writesWithin
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin regs.layout.footprint
      (restoreScalar regs) :=
  copy_writesWithin regs 25 (Layout.frameCode regs)

private theorem addNegativeScaledChunk_writesWithin
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin regs.layout.footprint
      (addNegativeScaledChunk regs) := by
  simp only [addNegativeScaledChunk, Cmd.seqList,
    Footprint.CmdWritesWithin]
  exact
    ⟨installNegativeScalar_writesWithin regs,
      ResidueBankOps.addScaledActiveChunk_writesWithin regs,
      restoreScalar_writesWithin regs⟩

theorem step_writesWithin_internal
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (chunkKernel : Cmd)
    (hkernel :
      Footprint.CmdWritesWithin regs.layout.footprint chunkKernel) :
    Footprint.CmdWritesWithin regs.layout.footprint
      (step controller regs chunkKernel) := by
  have hbody :
      Footprint.CmdWritesWithin regs.layout.footprint
        (streamBody controller regs chunkKernel) := by
    simp only [streamBody, Cmd.seqList, Footprint.CmdWritesWithin]
    exact
      ⟨by
          simp [Footprint.BasicWritesWithin,
            Layout.index_mem_layout_footprint],
        hkernel, addNegativeScaledChunk_writesWithin regs⟩
  have hstream :
      Footprint.CmdWritesWithin regs.layout.footprint
        (streamChunks controller regs chunkKernel) := by
    simp only [streamChunks, Cmd.seqList, Footprint.CmdWritesWithin]
    exact
      ⟨copy_writesWithin regs 28 (Layout.chunkCount regs),
        hbody,
        by
          simp [Footprint.BasicWritesWithin,
            Layout.index_mem_layout_footprint]⟩
  simp only [step, installCleanupCall, Footprint.CmdWritesWithin]
  exact
    ⟨hstream, ControlDecode.decodePhase_layout_writesWithin regs,
      Dispatcher.encodeCleanupCallPhase_writesWithin regs⟩

private theorem copy_runs
    (destination source : ℕ) (store : Store)
    (hne : destination ≠ source) :
    ∃ final,
      Runs (copy destination source) store final ∧
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

private theorem index_not_mem_mapped
    (regs : NeighborhoodTrial.Registers controller)
    (map : Fin count → Fin 34) (target : Fin 34)
    (hne : ∀ slot, map slot ≠ target) :
    regs.index target ∉
      Finset.univ.image (fun slot => regs.index (map slot)) := by
  simp only [Finset.mem_image, Finset.mem_univ, true_and,
    not_exists]
  intro slot heq
  exact hne slot (regs.injective heq)

private theorem scale_index_not_mem
    (regs : NeighborhoodTrial.Registers controller)
    (target : Fin 34)
    (hne : ∀ slot, Layout.residueScaleMap slot ≠ target) :
    regs.index target ∉
      (Layout.residueScaleRegisters regs).footprint :=
  index_not_mem_mapped regs Layout.residueScaleMap target hne

private theorem controller_eq_of_layout_run
    (regs : NeighborhoodTrial.Registers controller)
    (slot : Fin 17) {command : Cmd} {initial final : Store}
    (hwrites :
      Footprint.CmdWritesWithin regs.layout.footprint command)
    (hrun : Runs command initial final) :
    final (controller.index slot) = initial (controller.index slot) := by
  apply Footprint.runs_eq_outside hwrites hrun
  exact fun hmem =>
    Finset.disjoint_left.mp
      (NeighborhoodTrial.Registers.layout_disjoint_controller regs)
      hmem (controller.index_mem_footprint slot)

private theorem addScaled_preservesABI
    (regs : NeighborhoodTrial.Registers controller)
    {initial final : Store} {base modulus : ℕ}
    (hrun :
      Runs (ResidueBankOps.addScaledActiveChunk regs)
        initial final)
    (hbaseInitial :
      initial
          (Layout.residueScaleRegisters regs).bank.bank.base =
        base)
    (hmodulusInitial :
      initial (Layout.residueScaleRegisters regs).bank.modulus =
        modulus)
    (hmodulusPredInitial :
      initial
          (Layout.residueScaleRegisters regs).bank.modulusPred =
        modulus - 1)
    (hbaseFinal :
      final
          (Layout.residueScaleRegisters regs).bank.bank.base =
        base)
    (hmodulusFinal :
      final (Layout.residueScaleRegisters regs).bank.modulus =
        modulus)
    (hmodulusPredFinal :
      final
          (Layout.residueScaleRegisters regs).bank.modulusPred =
        modulus - 1) :
    ControlDecode.PreservesABI regs initial final := by
  let outside (target : Fin 34)
      (hne : ∀ slot, Layout.residueScaleMap slot ≠ target) :
      final (regs.index target) = initial (regs.index target) :=
    Footprint.runs_eq_outside
      (ResidueBankOps.addScaledActiveChunk_scaleWritesWithin regs)
      hrun (scale_index_not_mem regs target hne)
  exact
    { fuel_eq := outside 22 (by intro slot; fin_cases slot <;> decide)
      nodeCode_eq :=
        outside 23 (by intro slot; fin_cases slot <;> decide)
      scalar_eq :=
        outside 25 (by intro slot; fin_cases slot <;> decide)
      out_eq := outside 26 (by intro slot; fin_cases slot <;> decide)
      phaseCode_eq :=
        outside 27 (by intro slot; fin_cases slot <;> decide)
      active_eq :=
        outside 28 (by intro slot; fin_cases slot <;> decide)
      blockLength_eq :=
        outside 2 (by intro slot; fin_cases slot <;> decide)
      horizon_eq :=
        outside 3 (by intro slot; fin_cases slot <;> decide)
      chunkCount_eq :=
        outside 7 (by intro slot; fin_cases slot <;> decide)
      chunkRadix_eq :=
        outside 8 (by intro slot; fin_cases slot <;> decide)
      frameRadix_eq :=
        outside 13 (by intro slot; fin_cases slot <;> decide)
      bankRadix_eq := hbaseFinal.trans hbaseInitial.symm
      bankDigitCount_eq :=
        outside 15 (by intro slot; fin_cases slot <;> decide)
      modulusPred_eq :=
        hmodulusPredFinal.trans hmodulusPredInitial.symm
      modulus_eq :=
        hmodulusFinal.trans hmodulusInitial.symm }

private def negativeScalar
    {tm : TM workTapeCount}
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (frame : NeighborhoodScheduler.Frame tm instanceData) : ℕ :=
  PrimeField.Runtime.sub
    (NeighborhoodScheduler.fieldModulus instanceData)
    0 frame.scalar

private theorem mul_negativeRepresentative_mod
    (p scalar value : ℕ) (hscalar : scalar < p) :
    (value * (p - scalar)) % p =
      (value * PrimeField.Runtime.sub p 0 scalar) % p := by
  simp [PrimeField.Runtime.sub, PrimeField.Runtime.subInput,
    PrimeField.Runtime.normalize, Nat.mod_eq_of_lt hscalar]

private def combinedValue
    {tm : TM workTapeCount}
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (tape : TapeIndex workTapeCount)
    (slot : NeighborhoodGraph.Slot)
    (interval : ℕ)
    (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength) :
    NeighborhoodExecutableEvaluation.ResidueValue
      tm instanceData.blockLength :=
  fun chunk =>
    NeighborhoodExecutableEvaluation.combineResidues
      tm instanceData.x instanceData.blockLength
      instanceData.encoding instanceData.positive tape slot
      interval (computationArguments frame logicalBank) chunk

private def updateChunk
    {tm : TM workTapeCount}
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (value :
      NeighborhoodExecutableEvaluation.ResidueValue
        tm instanceData.blockLength)
    (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (chunk :
      Fin
        (PrimeGrouped.Logarithmic.chunkCount
          (NeighborhoodExecutableEvaluation.payloadWidth
            tm instanceData.blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount))) :
    NeighborhoodExecutableEvaluation.Residue.Registers
      tm instanceData.blockLength :=
  NeighborhoodProgram.updateResidueCoordinate
    tm instanceData.blockLength logicalBank frame.out chunk
    (NeighborhoodProgram.ResidueBankOp.add.apply
      (NeighborhoodScheduler.fieldModulus instanceData)
      (logicalBank frame.out chunk)
      ((value chunk * negativeScalar instanceData frame) %
        NeighborhoodScheduler.fieldModulus instanceData))

private def streamRegisters
    {tm : TM workTapeCount}
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (value :
      NeighborhoodExecutableEvaluation.ResidueValue
        tm instanceData.blockLength) :
    ℕ →
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength →
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength
  | 0, logicalBank => logicalBank
  | remaining + 1, logicalBank =>
      if hchunk :
          remaining <
            PrimeGrouped.Logarithmic.chunkCount
              (NeighborhoodExecutableEvaluation.payloadWidth
                tm instanceData.blockLength)
              (NeighborhoodExecutableEvaluation.graphFanIn
                workTapeCount) then
        streamRegisters instanceData frame value remaining
          (updateChunk instanceData frame value logicalBank
            ⟨remaining, hchunk⟩)
      else
        streamRegisters instanceData frame value remaining logicalBank

private theorem computationArguments_updateChunk
    {tm : TM workTapeCount}
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (value :
      NeighborhoodExecutableEvaluation.ResidueValue
        tm instanceData.blockLength)
    (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (chunk :
      Fin
        (PrimeGrouped.Logarithmic.chunkCount
          (NeighborhoodExecutableEvaluation.payloadWidth
            tm instanceData.blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount))) :
    computationArguments frame
        (updateChunk instanceData frame value logicalBank chunk) =
      computationArguments frame logicalBank := by
  funext child outputChunk
  simp [computationArguments, updateChunk,
    NeighborhoodProgram.updateResidueCoordinate,
    NeighborhoodScheduler.Frame.childTarget, Fin.succAbove_ne]

private theorem computationArguments_streamRegisters
    {tm : TM workTapeCount}
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (value :
      NeighborhoodExecutableEvaluation.ResidueValue
        tm instanceData.blockLength)
    (remaining : ℕ)
    (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength) :
    computationArguments frame
        (streamRegisters instanceData frame value remaining logicalBank) =
      computationArguments frame logicalBank := by
  induction remaining generalizing logicalBank with
  | zero =>
      rfl
  | succ remaining ih =>
      simp only [streamRegisters]
      split
      · exact
          (ih
            (updateChunk instanceData frame value logicalBank
              ⟨remaining, by assumption⟩)).trans
            (computationArguments_updateChunk
              instanceData frame value logicalBank
              ⟨remaining, by assumption⟩)
      · exact ih logicalBank

private theorem streamRegisters_apply
    {tm : TM workTapeCount}
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (value :
      NeighborhoodExecutableEvaluation.ResidueValue
        tm instanceData.blockLength)
    (remaining : ℕ)
    (hremaining :
      remaining ≤
        PrimeGrouped.Logarithmic.chunkCount
          (NeighborhoodExecutableEvaluation.payloadWidth
            tm instanceData.blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount))
    (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (register :
      Fin
        (NeighborhoodExecutableEvaluation.graphFanIn
          workTapeCount + 1))
    (chunk :
      Fin
        (PrimeGrouped.Logarithmic.chunkCount
          (NeighborhoodExecutableEvaluation.payloadWidth
            tm instanceData.blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount))) :
    streamRegisters instanceData frame value remaining logicalBank
          register chunk =
      if register = frame.out ∧ chunk.val < remaining then
        NeighborhoodProgram.ResidueBankOp.add.apply
          (NeighborhoodScheduler.fieldModulus instanceData)
          (logicalBank register chunk)
          ((value chunk * negativeScalar instanceData frame) %
            NeighborhoodScheduler.fieldModulus instanceData)
      else
        logicalBank register chunk := by
  induction remaining generalizing logicalBank with
  | zero =>
      simp [streamRegisters]
  | succ remaining ih =>
      have hchunk :
          remaining <
            PrimeGrouped.Logarithmic.chunkCount
              (NeighborhoodExecutableEvaluation.payloadWidth
                tm instanceData.blockLength)
              (NeighborhoodExecutableEvaluation.graphFanIn
                workTapeCount) := by
        omega
      rw [streamRegisters, dif_pos hchunk]
      rw [ih (by omega)]
      by_cases hreg : register = frame.out
      · subst register
        by_cases hlt : chunk.val < remaining
        · have hne : chunk ≠ ⟨remaining, hchunk⟩ := by
            intro heq
            have hval : chunk.val = remaining := by
              simpa using congrArg Fin.val heq
            omega
          rw [if_pos ⟨rfl, hlt⟩, if_pos ⟨rfl, by omega⟩]
          simp [updateChunk,
            NeighborhoodProgram.updateResidueCoordinate, hne]
        · by_cases heqval : chunk.val = remaining
          · have heq : chunk = ⟨remaining, hchunk⟩ :=
              Fin.ext heqval
            rw [if_neg (by simp [hlt]),
              if_pos ⟨rfl, by omega⟩]
            subst chunk
            simp [updateChunk,
              NeighborhoodProgram.updateResidueCoordinate]
          · have hgt : remaining < chunk.val := by omega
            have hne : chunk ≠ ⟨remaining, hchunk⟩ := by
              intro heq
              have hval : chunk.val = remaining := by
                simpa using congrArg Fin.val heq
              omega
            rw [if_neg (by simp [hlt]),
              if_neg (by simp; omega)]
            simp [updateChunk,
              NeighborhoodProgram.updateResidueCoordinate, hne]
      · rw [if_neg (by simp [hreg]), if_neg (by simp [hreg])]
        simp [updateChunk,
          NeighborhoodProgram.updateResidueCoordinate, hreg]

private theorem streamRegisters_eq_addScaledAt
    {tm : TM workTapeCount}
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (value :
      NeighborhoodExecutableEvaluation.ResidueValue
        tm instanceData.blockLength)
    (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength) :
    streamRegisters instanceData frame value
        (PrimeGrouped.Logarithmic.chunkCount
          (NeighborhoodExecutableEvaluation.payloadWidth
            tm instanceData.blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount))
        logicalBank =
      NeighborhoodScheduler.addScaledAt
        instanceData logicalBank frame.out
        (negativeScalar instanceData frame) value := by
  funext register chunk
  rw [streamRegisters_apply instanceData frame value _
    (le_refl _) logicalBank register chunk]
  by_cases hreg : register = frame.out
  · subst register
    rw [if_pos ⟨rfl, chunk.isLt⟩]
    simp [NeighborhoodScheduler.addScaledAt,
      NeighborhoodScheduler.fieldModulus,
      NeighborhoodExecutableEvaluation.Residue.addAt,
      NeighborhoodExecutableEvaluation.Residue.addValue,
      NeighborhoodExecutableEvaluation.Residue.scaleValue,
      NeighborhoodProgram.ResidueBankOp.apply,
      PrimeField.Runtime.add, PrimeField.Runtime.addInput,
      PrimeField.Runtime.mul, PrimeField.Runtime.mulInput,
      PrimeField.Runtime.normalize, Nat.mul_mod, Nat.add_mod,
      Nat.mul_comm]
  · rw [if_neg (by simp [hreg])]
    simp [NeighborhoodScheduler.addScaledAt,
      NeighborhoodExecutableEvaluation.Residue.addAt, hreg]

/-- Representation invariant while `Layout.active` is the chunk countdown. -/
private structure StreamState
    {tm : TM workTapeCount}
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (rest : List (NeighborhoodScheduler.Frame tm instanceData))
    (sourceBank currentBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (remaining : ℕ)
    (store : Store) : Prop where
  parameters : Representation.Parameters regs instanceData store
  fuel_eq : store (Layout.fuel regs) = frame.fuel
  node_eq :
    store (Layout.nodeCode regs) =
      FrameCodec.encodeNode (Representation.digitBase instanceData)
        frame.node
  scalar_eq : store (Layout.scalar regs) = frame.scalar
  out_eq : store (Layout.out regs) = frame.out.val
  phase_eq :
    store (Layout.phaseCode regs) =
      FrameCodec.encodePhase (Representation.digitBase instanceData)
        frame.phase
  active_eq : store (Layout.active regs) = remaining
  tail :
    FrameTransfer.RepresentsStack regs
      (Representation.digitBase instanceData)
      (Representation.frameBase instanceData) rest store
  bank :
    NeighborhoodProgram.RepresentsResidueBank
      tm instanceData.blockLength
      (Representation.fieldBase instanceData)
      (store regs.layout.bank) currentBank
  bank_lt :
    store regs.layout.bank <
      Representation.fieldBase instanceData ^
        ((NeighborhoodExecutableEvaluation.graphFanIn
            workTapeCount + 1) *
          PrimeGrouped.Logarithmic.chunkCount
            (NeighborhoodExecutableEvaluation.payloadWidth
              tm instanceData.blockLength)
            (NeighborhoodExecutableEvaluation.graphFanIn
              workTapeCount))
  bounds :
    NeighborhoodScheduler.FrameBounds.StateBound
      { stack := frame :: rest
        registers := currentBank }
  arguments_eq :
    computationArguments frame currentBank =
      computationArguments frame sourceBank
  one_eq : store controller.one = 1

private theorem addNegativeScaledChunk_runs
    {tm : TM workTapeCount}
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (rest : List (NeighborhoodScheduler.Frame tm instanceData))
    (sourceBank currentBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (value :
      NeighborhoodExecutableEvaluation.ResidueValue
        tm instanceData.blockLength)
    (chunk :
      Fin
        (PrimeGrouped.Logarithmic.chunkCount
          (NeighborhoodExecutableEvaluation.payloadWidth
            tm instanceData.blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount)))
    (store : Store)
    (hstate :
      StreamState regs instanceData frame rest sourceBank currentBank
        chunk.val store)
    (hvalue : store (chunkValue regs) = value chunk) :
    ∃ final,
      Runs (addNegativeScaledChunk regs) store final ∧
      StreamState regs instanceData frame rest sourceBank
        (updateChunk instanceData frame value currentBank chunk)
        chunk.val final := by
  let savedZero :=
    (Basic.imm (Layout.frameCode regs) 0).exec store
  let saved :=
    (Basic.add (Layout.frameCode regs) (Layout.scalar regs)
      (Layout.frameCode regs)).exec savedZero
  let cursorZero :=
    (Basic.imm (Layout.codecScratch regs) 0).exec saved
  let cursor :=
    (Basic.add (Layout.codecScratch regs) (Layout.active regs)
      (Layout.codecScratch regs)).exec cursorZero
  let installed :=
    (Basic.sub (Layout.scalar regs) (Layout.modulus regs)
      (Layout.frameCode regs)).exec cursor
  have hsave :
      Runs (copy (Layout.frameCode regs) (Layout.scalar regs))
        store saved := by
    simpa [copy, savedZero, saved] using
      Runs.seq
        (Runs.basic
          (Basic.imm (Layout.frameCode regs) 0) store)
        (Runs.basic
          (Basic.add (Layout.frameCode regs) (Layout.scalar regs)
            (Layout.frameCode regs)) savedZero)
  have hcursor :
      Runs (copy (Layout.codecScratch regs) (Layout.active regs))
        saved cursor := by
    simpa [copy, cursorZero, cursor] using
      Runs.seq
        (Runs.basic
          (Basic.imm (Layout.codecScratch regs) 0) saved)
        (Runs.basic
          (Basic.add (Layout.codecScratch regs) (Layout.active regs)
            (Layout.codecScratch regs)) cursorZero)
  have hnegative :
      Runs
        (.basic
          (.sub (Layout.scalar regs) (Layout.modulus regs)
            (Layout.frameCode regs)))
        cursor installed :=
    Runs.basic _ _
  have hinstall :
      Runs (installNegativeScalar regs) store installed := by
    simpa [installNegativeScalar, Cmd.seqList] using
      Runs.seq hsave (Runs.seq hcursor hnegative)
  have hphysical
      (slot : Fin 34) (hscalar : slot ≠ 25)
      (hframeCode : slot ≠ 29) (hcodec : slot ≠ 31) :
      installed (regs.index slot) = store (regs.index slot) := by
    simp [installed, cursor, cursorZero, saved, savedZero,
      Basic.exec, regs.injective.eq_iff, hscalar, hframeCode,
      hcodec]
  have hinstalledScalar :
      installed (Layout.scalar regs) =
        NeighborhoodScheduler.fieldModulus instanceData -
          frame.scalar := by
    simp [installed, cursor, cursorZero, saved, savedZero,
      Basic.exec, regs.injective.eq_iff,
      hstate.parameters.modulus_eq, hstate.scalar_eq]
  have hinstalledCursor :
      installed (Layout.codecScratch regs) = chunk.val := by
    simp [installed, cursor, cursorZero, saved, savedZero,
      Basic.exec, regs.injective.eq_iff, hstate.active_eq]
  have hframeBound :
      NeighborhoodScheduler.FrameBounds.FrameBound frame :=
    hstate.bounds frame (by simp)
  have hscalarLt :
      frame.scalar <
        NeighborhoodScheduler.fieldModulus instanceData :=
    hframeBound.2.2.1
  have hdigitBase :
      0 < Representation.digitBase instanceData := by
    unfold Representation.digitBase CandidateParameters.domainSize
    exact PrimeGrouped.Logarithmic.domainSize_pos _ _
  have hfieldBase :
      0 < Representation.fieldBase instanceData :=
    pow_pos hdigitBase _
  have hmodulus :
      0 <
        NeighborhoodExecutableEvaluation.modulus
          tm instanceData.blockLength := by
    change 0 < NeighborhoodScheduler.fieldModulus instanceData
    have hone :=
      NeighborhoodScheduler.FrameBounds.fieldModulus_one_lt
        instanceData
    omega
  have hmodulusBase :
      NeighborhoodExecutableEvaluation.modulus
          tm instanceData.blockLength ≤
        Representation.fieldBase instanceData := by
    have hlt :=
      CandidateParameters.RadixBounds.canonicalModulus_lt_bankRadix
        tm.Q workTapeCount instanceData.candidateTime
    rw [← NeighborhoodTrial.fieldModulus_eq_canonicalModulus
      instanceData] at hlt
    rw [CandidateParameters.RadixBounds.bankRadix_eq_domainSize_sq]
      at hlt
    simpa [NeighborhoodScheduler.fieldModulus,
      Representation.fieldBase, Representation.digitBase] using
      Nat.le_of_lt hlt
  have hrep :
      NeighborhoodProgram.RepresentsResidueBank
        tm instanceData.blockLength
        (Representation.fieldBase instanceData)
        (installed regs.layout.bank) currentBank := by
    change
      NeighborhoodProgram.RepresentsResidueBank
        tm instanceData.blockLength
        (Representation.fieldBase instanceData)
        (installed (regs.index 33)) currentBank
    rw [hphysical 33 (by decide) (by decide) (by decide)]
    exact hstate.bank
  have hbaseValue :
      installed
          (Layout.residueScaleRegisters regs).bank.bank.base =
        Representation.fieldBase instanceData := by
    change
      installed (regs.index 14) =
        Representation.fieldBase instanceData
    rw [hphysical 14 (by decide) (by decide) (by decide)]
    exact hstate.parameters.bankBase_eq
  have hmodulusValue :
      installed (Layout.residueScaleRegisters regs).bank.modulus =
        NeighborhoodExecutableEvaluation.modulus
          tm instanceData.blockLength := by
    change
      installed (regs.index 24) =
        NeighborhoodExecutableEvaluation.modulus
          tm instanceData.blockLength
    rw [hphysical 24 (by decide) (by decide) (by decide)]
    exact hstate.parameters.modulus_eq
  have hmodulusPred :
      installed
          (Layout.residueScaleRegisters regs).bank.modulusPred =
        NeighborhoodExecutableEvaluation.modulus
            tm instanceData.blockLength - 1 := by
    change
      installed (regs.index 16) =
        NeighborhoodExecutableEvaluation.modulus
            tm instanceData.blockLength - 1
    rw [hphysical 16 (by decide) (by decide) (by decide)]
    exact hstate.parameters.modulusPred_eq
  have hoperand :
      installed
          (Layout.residueScaleRegisters regs).bank.operand =
        value chunk := by
    change installed (regs.index 19) = value chunk
    rw [hphysical 19 (by decide) (by decide) (by decide)]
    exact hvalue
  have hout :
      installed (Layout.out regs) = frame.out.val := by
    rw [hphysical 26 (by decide) (by decide) (by decide)]
    exact hstate.out_eq
  have hchunkCount :
      installed (Layout.chunkCount regs) =
        PrimeGrouped.Logarithmic.chunkCount
          (NeighborhoodExecutableEvaluation.payloadWidth
            tm instanceData.blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount) := by
    rw [hphysical 7 (by decide) (by decide) (by decide)]
    exact hstate.parameters.chunkCount_eq
  obtain ⟨updated, hupdate, hupdatedBank, hupdatedWord,
      hupdatedBase, hupdatedModulus, hupdatedModulusPred⟩ :=
    ResidueBankOps.addScaledActiveChunk_runs tm
      instanceData.blockLength
      (NeighborhoodScheduler.fieldModulus instanceData - frame.scalar)
      (Representation.fieldBase instanceData)
      (installed regs.layout.bank) (value chunk) currentBank
      frame.out chunk regs installed hfieldBase hmodulus
      hmodulusBase rfl hrep hbaseValue hmodulusValue
      hmodulusPred hoperand hinstalledScalar hout hchunkCount
      hinstalledCursor
  have hscale :
      (value chunk *
          (NeighborhoodScheduler.fieldModulus instanceData -
            frame.scalar)) %
          NeighborhoodScheduler.fieldModulus instanceData =
        (value chunk * negativeScalar instanceData frame) %
          NeighborhoodScheduler.fieldModulus instanceData := by
    exact mul_negativeRepresentative_mod _ _ _ hscalarLt
  have hscaleExecutable :
      (value chunk *
          (NeighborhoodExecutableEvaluation.modulus
              tm instanceData.blockLength -
            frame.scalar)) %
          NeighborhoodExecutableEvaluation.modulus
            tm instanceData.blockLength =
        (value chunk * negativeScalar instanceData frame) %
          NeighborhoodExecutableEvaluation.modulus
            tm instanceData.blockLength := by
    change
      (value chunk *
          (NeighborhoodScheduler.fieldModulus instanceData -
            frame.scalar)) %
          NeighborhoodScheduler.fieldModulus instanceData =
        (value chunk * negativeScalar instanceData frame) %
          NeighborhoodScheduler.fieldModulus instanceData
    exact hscale
  have hupdatedBank' :
      NeighborhoodProgram.RepresentsResidueBank
        tm instanceData.blockLength
        (Representation.fieldBase instanceData)
        (updated regs.layout.bank)
        (updateChunk instanceData frame value currentBank chunk) := by
    change
      NeighborhoodProgram.RepresentsResidueBank
        tm instanceData.blockLength
        (Representation.fieldBase instanceData)
        (updated (regs.index 33))
        (updateChunk instanceData frame value currentBank chunk)
    change
      NeighborhoodProgram.RepresentsResidueBank
        tm instanceData.blockLength
        (Representation.fieldBase instanceData)
        (updated (regs.index 33))
        _ at hupdatedBank
    simpa [updateChunk, NeighborhoodScheduler.fieldModulus,
      hscaleExecutable] using hupdatedBank
  have hupdateABI :
      ControlDecode.PreservesABI regs installed updated :=
    addScaled_preservesABI regs hupdate hbaseValue hmodulusValue
      hmodulusPred hupdatedBase hupdatedModulus
      hupdatedModulusPred
  let restoreZero :=
    (Basic.imm (Layout.scalar regs) 0).exec updated
  let final :=
    (Basic.add (Layout.scalar regs) (Layout.frameCode regs)
      (Layout.scalar regs)).exec restoreZero
  have hrestore :
      Runs (restoreScalar regs) updated final := by
    simpa [restoreScalar, copy, restoreZero, final] using
      Runs.seq
        (Runs.basic (Basic.imm (Layout.scalar regs) 0) updated)
        (Runs.basic
          (Basic.add (Layout.scalar regs) (Layout.frameCode regs)
            (Layout.scalar regs)) restoreZero)
  have hrun :
      Runs (addNegativeScaledChunk regs) store final := by
    simpa [addNegativeScaledChunk, Cmd.seqList] using
      Runs.seq hinstall (Runs.seq hupdate hrestore)
  have hfinalPhysical
      (slot : Fin 34) (hne : slot ≠ 25) :
      final (regs.index slot) = updated (regs.index slot) := by
    simp [final, restoreZero, Basic.exec, regs.injective.eq_iff,
      hne]
  have hupdatedFrameCode :
      updated (Layout.frameCode regs) =
        installed (Layout.frameCode regs) :=
    Footprint.runs_eq_outside
      (ResidueBankOps.addScaledActiveChunk_scaleWritesWithin regs)
      hupdate
      (scale_index_not_mem regs 29
        (by intro slot; fin_cases slot <;> decide))
  have hfinalScalar :
      final (Layout.scalar regs) = store (Layout.scalar regs) := by
    simp [final, restoreZero, Basic.exec,
      regs.injective.eq_iff, hupdatedFrameCode, installed,
      cursor, cursorZero, saved, savedZero]
  have habi :
      ControlDecode.PreservesABI regs store final := by
    exact
      { fuel_eq := (hfinalPhysical 22 (by decide)).trans
          (hupdateABI.fuel_eq.trans
            (hphysical 22 (by decide) (by decide) (by decide)))
        nodeCode_eq := (hfinalPhysical 23 (by decide)).trans
          (hupdateABI.nodeCode_eq.trans
            (hphysical 23 (by decide) (by decide) (by decide)))
        scalar_eq := hfinalScalar
        out_eq := (hfinalPhysical 26 (by decide)).trans
          (hupdateABI.out_eq.trans
            (hphysical 26 (by decide) (by decide) (by decide)))
        phaseCode_eq := (hfinalPhysical 27 (by decide)).trans
          (hupdateABI.phaseCode_eq.trans
            (hphysical 27 (by decide) (by decide) (by decide)))
        active_eq := (hfinalPhysical 28 (by decide)).trans
          (hupdateABI.active_eq.trans
            (hphysical 28 (by decide) (by decide) (by decide)))
        blockLength_eq := (hfinalPhysical 2 (by decide)).trans
          (hupdateABI.blockLength_eq.trans
            (hphysical 2 (by decide) (by decide) (by decide)))
        horizon_eq := (hfinalPhysical 3 (by decide)).trans
          (hupdateABI.horizon_eq.trans
            (hphysical 3 (by decide) (by decide) (by decide)))
        chunkCount_eq := (hfinalPhysical 7 (by decide)).trans
          (hupdateABI.chunkCount_eq.trans
            (hphysical 7 (by decide) (by decide) (by decide)))
        chunkRadix_eq := (hfinalPhysical 8 (by decide)).trans
          (hupdateABI.chunkRadix_eq.trans
            (hphysical 8 (by decide) (by decide) (by decide)))
        frameRadix_eq := (hfinalPhysical 13 (by decide)).trans
          (hupdateABI.frameRadix_eq.trans
            (hphysical 13 (by decide) (by decide) (by decide)))
        bankRadix_eq := (hfinalPhysical 14 (by decide)).trans
          (hupdateABI.bankRadix_eq.trans
            (hphysical 14 (by decide) (by decide) (by decide)))
        bankDigitCount_eq := (hfinalPhysical 15 (by decide)).trans
          (hupdateABI.bankDigitCount_eq.trans
            (hphysical 15 (by decide) (by decide) (by decide)))
        modulusPred_eq := (hfinalPhysical 16 (by decide)).trans
          (hupdateABI.modulusPred_eq.trans
            (hphysical 16 (by decide) (by decide) (by decide)))
        modulus_eq := (hfinalPhysical 24 (by decide)).trans
          (hupdateABI.modulus_eq.trans
            (hphysical 24 (by decide) (by decide) (by decide))) }
  have hparameters :
      Representation.Parameters regs instanceData final :=
    Representation.Parameters.of_preservesABI regs store final
      hstate.parameters habi
  have htail :
      FrameTransfer.RepresentsStack regs
        (Representation.digitBase instanceData)
        (Representation.frameBase instanceData) rest final := by
    calc
      final regs.layout.stack = updated regs.layout.stack :=
        hfinalPhysical 32 (by decide)
      _ = installed regs.layout.stack := by
        exact Footprint.runs_eq_outside
          (ResidueBankOps.addScaledActiveChunk_scaleWritesWithin regs)
          hupdate
          (scale_index_not_mem regs 32
            (by intro slot; fin_cases slot <;> decide))
      _ = store regs.layout.stack :=
        hphysical 32 (by decide) (by decide) (by decide)
      _ = FrameTransfer.encodeStack
          (Representation.digitBase instanceData)
          (Representation.frameBase instanceData) rest :=
        hstate.tail
  have hbank :
      NeighborhoodProgram.RepresentsResidueBank
        tm instanceData.blockLength
        (Representation.fieldBase instanceData)
        (final regs.layout.bank)
        (updateChunk instanceData frame value currentBank chunk) := by
    change
      NeighborhoodProgram.RepresentsResidueBank
        tm instanceData.blockLength
        (Representation.fieldBase instanceData)
        (final (regs.index 33))
        (updateChunk instanceData frame value currentBank chunk)
    change
      NeighborhoodProgram.RepresentsResidueBank
        tm instanceData.blockLength
        (Representation.fieldBase instanceData)
        (updated (regs.index 33))
        (updateChunk instanceData frame value currentBank chunk)
      at hupdatedBank'
    rw [hfinalPhysical 33 (by decide)]
    exact hupdatedBank'
  have hbankLt :
      final regs.layout.bank <
        Representation.fieldBase instanceData ^
          ((NeighborhoodExecutableEvaluation.graphFanIn
              workTapeCount + 1) *
            PrimeGrouped.Logarithmic.chunkCount
              (NeighborhoodExecutableEvaluation.payloadWidth
                tm instanceData.blockLength)
              (NeighborhoodExecutableEvaluation.graphFanIn
                workTapeCount)) := by
    change
      final (regs.index 33) <
        Representation.fieldBase instanceData ^
          ((NeighborhoodExecutableEvaluation.graphFanIn
              workTapeCount + 1) *
            PrimeGrouped.Logarithmic.chunkCount
              (NeighborhoodExecutableEvaluation.payloadWidth
                tm instanceData.blockLength)
              (NeighborhoodExecutableEvaluation.graphFanIn
                workTapeCount))
    change updated (regs.index 33) = _ at hupdatedWord
    rw [hfinalPhysical 33 (by decide), hupdatedWord]
    have hbound :=
      NeighborhoodProgram.bankUpdateAt_word_lt_pow
        (op := NeighborhoodProgram.ResidueBankOp.add)
        (operand :=
          (value chunk *
            (NeighborhoodScheduler.fieldModulus instanceData -
              frame.scalar)) %
            NeighborhoodScheduler.fieldModulus instanceData)
        hfieldBase hstate.bank_lt
        (NeighborhoodProgram.residueBankIndex_lt
          tm instanceData.blockLength frame.out chunk)
        hmodulus hmodulusBase
    rw [hstate.bank frame.out chunk] at hbound
    have hinstalledBank :
        installed regs.layout.bank = store regs.layout.bank := by
      change installed (regs.index 33) = store (regs.index 33)
      exact hphysical 33 (by decide) (by decide) (by decide)
    rw [hinstalledBank]
    simpa [NeighborhoodScheduler.fieldModulus] using hbound
  have hone :
      final controller.one = 1 := by
    calc
      final controller.one = store controller.one :=
        controller_eq_of_layout_run regs
          (SearchProgram.Registers.primeSlot (6 : Fin 8))
          (addNegativeScaledChunk_writesWithin regs) hrun
      _ = 1 := hstate.one_eq
  refine ⟨final, hrun, ?_⟩
  exact
    { parameters := hparameters
      fuel_eq := habi.fuel_eq.trans hstate.fuel_eq
      node_eq := habi.nodeCode_eq.trans hstate.node_eq
      scalar_eq := habi.scalar_eq.trans hstate.scalar_eq
      out_eq := habi.out_eq.trans hstate.out_eq
      phase_eq := habi.phaseCode_eq.trans hstate.phase_eq
      active_eq := habi.active_eq.trans hstate.active_eq
      tail := htail
      bank := hbank
      bank_lt := hbankLt
      bounds := hstate.bounds
      arguments_eq :=
        (computationArguments_updateChunk
          instanceData frame value currentBank chunk).trans
          hstate.arguments_eq
      one_eq := hone }

private theorem streamLoop_runs
    {tm : TM workTapeCount}
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (rest : List (NeighborhoodScheduler.Frame tm instanceData))
    (sourceBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (tape : TapeIndex workTapeCount)
    (slot : NeighborhoodGraph.Slot)
    (interval : ℕ)
    (hnode :
      frame.node =
        (show
          NeighborhoodEvaluator.QueryNode
            workTapeCount instanceData.horizon
          from .graph (.computation tape slot interval)))
    (chunkKernel : Cmd)
    (hkernel :
      ComputationChunkKernelSpecAt regs instanceData frame tape slot
        interval chunkKernel)
    (remaining : ℕ)
    (hremaining :
      remaining ≤
        PrimeGrouped.Logarithmic.chunkCount
          (NeighborhoodExecutableEvaluation.payloadWidth
            tm instanceData.blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount))
    (currentBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (store : Store)
    (hstate :
      StreamState regs instanceData frame rest sourceBank currentBank
        remaining store) :
    ∃ final,
      Runs
        (.whileNonzero (Layout.active regs)
          (streamBody controller regs chunkKernel))
        store final ∧
      StreamState regs instanceData frame rest sourceBank
        (streamRegisters instanceData frame
          (combinedValue instanceData frame tape slot interval
            sourceBank)
          remaining currentBank)
        0 final := by
  induction remaining generalizing currentBank store with
  | zero =>
      refine ⟨store, Runs.whileZero hstate.active_eq, ?_⟩
      simpa [streamRegisters] using hstate
  | succ remaining ih =>
      have hchunk :
          remaining <
            PrimeGrouped.Logarithmic.chunkCount
              (NeighborhoodExecutableEvaluation.payloadWidth
                tm instanceData.blockLength)
              (NeighborhoodExecutableEvaluation.graphFanIn
                workTapeCount) := by
        omega
      let chunk :
          Fin
            (PrimeGrouped.Logarithmic.chunkCount
              (NeighborhoodExecutableEvaluation.payloadWidth
                tm instanceData.blockLength)
              (NeighborhoodExecutableEvaluation.graphFanIn
                workTapeCount)) :=
        ⟨remaining, hchunk⟩
      let decremented :=
        (Basic.sub (Layout.active regs) (Layout.active regs)
          controller.one).exec store
      have hdecrement :
          Runs
            (.basic
              (.sub (Layout.active regs) (Layout.active regs)
                controller.one))
            store decremented :=
        Runs.basic _ _
      have hphysical
          (address : ℕ) (hne : address ≠ Layout.active regs) :
          decremented address = store address := by
        simp [decremented, Basic.exec, hne]
      have hactive :
          decremented (Layout.active regs) = remaining := by
        simp [decremented, Basic.exec, hstate.active_eq,
          hstate.one_eq]
      have hone :
          decremented controller.one = 1 := by
        have hne :
            controller.one ≠ Layout.active regs :=
          (regs.index_ne_controller 28
            (SearchProgram.Registers.primeSlot (6 : Fin 8))).symm
        rw [hphysical controller.one hne]
        exact hstate.one_eq
      have hparameters :
          Representation.Parameters regs instanceData decremented := by
        exact
          { blockLength_eq := by
              rw [hphysical (Layout.blockLength regs)
                (regs.injective.ne (by decide))]
              exact hstate.parameters.blockLength_eq
            horizon_eq := by
              rw [hphysical (Layout.horizon regs)
                (regs.injective.ne (by decide))]
              exact hstate.parameters.horizon_eq
            digitBase_eq := by
              rw [hphysical (Layout.chunkRadix regs)
                (regs.injective.ne (by decide))]
              exact hstate.parameters.digitBase_eq
            bankBase_eq := by
              rw [hphysical (Layout.bankRadix regs)
                (regs.injective.ne (by decide))]
              exact hstate.parameters.bankBase_eq
            frameBase_eq := by
              rw [hphysical (Layout.frameRadix regs)
                (regs.injective.ne (by decide))]
              exact hstate.parameters.frameBase_eq
            chunkCount_eq := by
              rw [hphysical (Layout.chunkCount regs)
                (regs.injective.ne (by decide))]
              exact hstate.parameters.chunkCount_eq
            bankDigitCount_eq := by
              rw [hphysical (Layout.bankDigitCount regs)
                (regs.injective.ne (by decide))]
              exact hstate.parameters.bankDigitCount_eq
            modulus_eq := by
              rw [hphysical (Layout.modulus regs)
                (regs.injective.ne (by decide))]
              exact hstate.parameters.modulus_eq
            modulusPred_eq := by
              rw [hphysical (Layout.modulusPred regs)
                (regs.injective.ne (by decide))]
              exact hstate.parameters.modulusPred_eq }
      have hdecremented :
          StreamState regs instanceData frame rest sourceBank currentBank
            chunk.val decremented := by
        exact
          { parameters := hparameters
            fuel_eq := by
              rw [hphysical (Layout.fuel regs)
                (regs.injective.ne (by decide))]
              exact hstate.fuel_eq
            node_eq := by
              rw [hphysical (Layout.nodeCode regs)
                (regs.injective.ne (by decide))]
              exact hstate.node_eq
            scalar_eq := by
              rw [hphysical (Layout.scalar regs)
                (regs.injective.ne (by decide))]
              exact hstate.scalar_eq
            out_eq := by
              rw [hphysical (Layout.out regs)
                (regs.injective.ne (by decide))]
              exact hstate.out_eq
            phase_eq := by
              rw [hphysical (Layout.phaseCode regs)
                (regs.injective.ne (by decide))]
              exact hstate.phase_eq
            active_eq := by
              simpa [chunk] using hactive
            tail := by
              unfold FrameTransfer.RepresentsStack
              rw [hphysical
                (Layout.frameStackRegisters regs).word (by
                change regs.index 32 ≠ regs.index 28
                exact regs.injective.ne (by decide))]
              exact hstate.tail
            bank := by
              rw [hphysical regs.layout.bank (by
                change regs.index 33 ≠ regs.index 28
                exact regs.injective.ne (by decide))]
              exact hstate.bank
            bank_lt := by
              rw [hphysical regs.layout.bank (by
                change regs.index 33 ≠ regs.index 28
                exact regs.injective.ne (by decide))]
              exact hstate.bank_lt
            bounds := hstate.bounds
            arguments_eq := hstate.arguments_eq
            one_eq := hone }
      have hcontext :
          ComputationContext regs instanceData frame tape slot interval
            currentBank decremented := by
        exact
          { parameters := hdecremented.parameters
            nodeCode_eq := by
              simpa [hnode] using hdecremented.node_eq
            out_eq := hdecremented.out_eq
            bank := hdecremented.bank }
      obtain ⟨provided, hprovide, hpost⟩ :=
        hkernel currentBank decremented chunk hcontext
          hdecremented.active_eq
      have hprovidedParameters :
          Representation.Parameters regs instanceData provided :=
        Representation.Parameters.of_preservesABI regs decremented
          provided hdecremented.parameters hpost.abi
      have hprovided :
          StreamState regs instanceData frame rest sourceBank currentBank
            chunk.val provided := by
        exact
          { parameters := hprovidedParameters
            fuel_eq := hpost.abi.fuel_eq.trans
              hdecremented.fuel_eq
            node_eq := hpost.abi.nodeCode_eq.trans
              hdecremented.node_eq
            scalar_eq := hpost.abi.scalar_eq.trans
              hdecremented.scalar_eq
            out_eq := hpost.abi.out_eq.trans
              hdecremented.out_eq
            phase_eq := hpost.abi.phaseCode_eq.trans
              hdecremented.phase_eq
            active_eq := hpost.cursor_eq
            tail := by
              calc
                provided regs.layout.stack =
                    decremented regs.layout.stack := hpost.stack_eq
                _ = FrameTransfer.encodeStack
                    (Representation.digitBase instanceData)
                    (Representation.frameBase instanceData) rest :=
                  hdecremented.tail
            bank := by
              rw [hpost.bank_eq]
              exact hdecremented.bank
            bank_lt := by
              rw [hpost.bank_eq]
              exact hdecremented.bank_lt
            bounds := hdecremented.bounds
            arguments_eq := hdecremented.arguments_eq
            one_eq := hpost.one_eq.trans hdecremented.one_eq }
      have hprovidedValue :
          provided (chunkValue regs) =
            combinedValue instanceData frame tape slot interval
              sourceBank chunk := by
        rw [hpost.value_eq]
        simp only [combinedValue]
        rw [hdecremented.arguments_eq]
      obtain ⟨updated, hupdate, hupdated⟩ :=
        addNegativeScaledChunk_runs regs instanceData frame rest
          sourceBank currentBank
          (combinedValue instanceData frame tape slot interval sourceBank)
          chunk provided hprovided hprovidedValue
      obtain ⟨final, hloop, hfinal⟩ :=
        ih (by omega)
          (updateChunk instanceData frame
            (combinedValue instanceData frame tape slot interval
              sourceBank)
            currentBank chunk)
          updated hupdated
      refine ⟨final, ?_, ?_⟩
      · exact
          Runs.whileNonzero
            (by
              rw [hstate.active_eq]
              omega)
            (by
              simpa [streamBody, Cmd.seqList] using
                Runs.seq hdecrement (Runs.seq hprovide hupdate))
            hloop
      · rw [streamRegisters, dif_pos hchunk]
        simpa [chunk] using hfinal

private theorem streamChunks_runs
    {tm : TM workTapeCount}
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (rest : List (NeighborhoodScheduler.Frame tm instanceData))
    (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (tape : TapeIndex workTapeCount)
    (slot : NeighborhoodGraph.Slot)
    (interval : ℕ)
    (hnode :
      frame.node =
        (show
          NeighborhoodEvaluator.QueryNode
            workTapeCount instanceData.horizon
          from .graph (.computation tape slot interval)))
    (chunkKernel : Cmd)
    (store : Store)
    (hquery :
      Representation.QueryState regs instanceData
        { stack := frame :: rest
          registers := logicalBank }
        store)
    (hone : store controller.one = 1)
    (hkernel :
      ComputationChunkKernelSpecAt regs instanceData frame tape slot
        interval chunkKernel) :
    ∃ final,
      Runs (streamChunks controller regs chunkKernel) store final ∧
      Representation.QueryState regs instanceData
        { stack := frame :: rest
          registers :=
            NeighborhoodScheduler.addScaledAt instanceData logicalBank
              frame.out (negativeScalar instanceData frame)
              (combinedValue instanceData frame tape slot interval
                logicalBank) }
        final := by
  obtain ⟨initialized, hinitialize, hactive, houtside⟩ :=
    copy_runs (Layout.active regs) (Layout.chunkCount regs) store
      (regs.injective.ne (by decide))
  have hslot
      (physical : Fin 34) (hne : physical ≠ 28) :
      initialized (regs.index physical) = store (regs.index physical) :=
    houtside (regs.index physical)
      (regs.injective.ne hne)
  have hparameters :
      Representation.Parameters regs instanceData initialized := by
    exact
      { blockLength_eq :=
          (hslot 2 (by decide)).trans
            hquery.parameters.blockLength_eq
        horizon_eq :=
          (hslot 3 (by decide)).trans
            hquery.parameters.horizon_eq
        digitBase_eq :=
          (hslot 8 (by decide)).trans
            hquery.parameters.digitBase_eq
        bankBase_eq :=
          (hslot 14 (by decide)).trans
            hquery.parameters.bankBase_eq
        frameBase_eq :=
          (hslot 13 (by decide)).trans
            hquery.parameters.frameBase_eq
        chunkCount_eq :=
          (hslot 7 (by decide)).trans
            hquery.parameters.chunkCount_eq
        bankDigitCount_eq :=
          (hslot 15 (by decide)).trans
            hquery.parameters.bankDigitCount_eq
        modulus_eq :=
          (hslot 24 (by decide)).trans
            hquery.parameters.modulus_eq
        modulusPred_eq :=
          (hslot 16 (by decide)).trans
            hquery.parameters.modulusPred_eq }
  have hinitialized :
      StreamState regs instanceData frame rest logicalBank logicalBank
        (PrimeGrouped.Logarithmic.chunkCount
          (NeighborhoodExecutableEvaluation.payloadWidth
            tm instanceData.blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount))
        initialized := by
    exact
      { parameters := hparameters
        fuel_eq := (hslot 22 (by decide)).trans
          hquery.stack.1.fuel_eq
        node_eq := (hslot 23 (by decide)).trans
          hquery.stack.1.node_eq
        scalar_eq := (hslot 25 (by decide)).trans
          hquery.stack.1.scalar_eq
        out_eq := (hslot 26 (by decide)).trans
          hquery.stack.1.out_eq
        phase_eq := (hslot 27 (by decide)).trans
          hquery.stack.1.phase_eq
        active_eq := hactive.trans
          hquery.parameters.chunkCount_eq
        tail := by
          unfold FrameTransfer.RepresentsStack
          calc
            initialized (Layout.frameStackRegisters regs).word =
                store (Layout.frameStackRegisters regs).word :=
              hslot 32 (by decide)
            _ = FrameTransfer.encodeStack
                (Representation.digitBase instanceData)
                (Representation.frameBase instanceData) rest :=
              hquery.stack.2
        bank := by
          have hbankStore := hquery.bank
          change
            NeighborhoodProgram.RepresentsResidueBank
              tm instanceData.blockLength
              (Representation.fieldBase instanceData)
              (initialized (regs.index 33)) logicalBank
          change
            NeighborhoodProgram.RepresentsResidueBank
              tm instanceData.blockLength
              (Representation.fieldBase instanceData)
              (store (regs.index 33)) logicalBank
            at hbankStore
          rw [hslot 33 (by decide)]
          exact hbankStore
        bank_lt := by
          have hbankLtStore := hquery.bank_lt
          change
            initialized (regs.index 33) <
              Representation.fieldBase instanceData ^
                ((NeighborhoodExecutableEvaluation.graphFanIn
                    workTapeCount + 1) *
                  PrimeGrouped.Logarithmic.chunkCount
                    (NeighborhoodExecutableEvaluation.payloadWidth
                      tm instanceData.blockLength)
                    (NeighborhoodExecutableEvaluation.graphFanIn
                      workTapeCount))
          change
            store (regs.index 33) <
              Representation.fieldBase instanceData ^
                ((NeighborhoodExecutableEvaluation.graphFanIn
                    workTapeCount + 1) *
                  PrimeGrouped.Logarithmic.chunkCount
                    (NeighborhoodExecutableEvaluation.payloadWidth
                      tm instanceData.blockLength)
                    (NeighborhoodExecutableEvaluation.graphFanIn
                      workTapeCount))
            at hbankLtStore
          rw [hslot 33 (by decide)]
          exact hbankLtStore
        bounds := hquery.bounds
        arguments_eq := rfl
        one_eq := by
          rw [houtside controller.one (by
            exact
              (regs.index_ne_controller 28
                (SearchProgram.Registers.primeSlot
                  (6 : Fin 8))).symm)]
          exact hone }
  obtain ⟨looped, hloop, hlooped⟩ :=
    streamLoop_runs controller regs instanceData frame rest logicalBank
      tape slot interval hnode chunkKernel hkernel _ (le_refl _)
      logicalBank initialized hinitialized
  let final :=
    (Basic.imm (Layout.active regs) 1).exec looped
  have hfinish :
      Runs (.basic (.imm (Layout.active regs) 1)) looped final :=
    Runs.basic _ _
  have hfinalPhysical
      (address : ℕ) (hne : address ≠ Layout.active regs) :
      final address = looped address := by
    simp [final, Basic.exec, hne]
  have hfinalParameters :
      Representation.Parameters regs instanceData final := by
    exact
      { blockLength_eq := by
          rw [hfinalPhysical (Layout.blockLength regs)
            (regs.injective.ne (by decide))]
          exact hlooped.parameters.blockLength_eq
        horizon_eq := by
          rw [hfinalPhysical (Layout.horizon regs)
            (regs.injective.ne (by decide))]
          exact hlooped.parameters.horizon_eq
        digitBase_eq := by
          rw [hfinalPhysical (Layout.chunkRadix regs)
            (regs.injective.ne (by decide))]
          exact hlooped.parameters.digitBase_eq
        bankBase_eq := by
          rw [hfinalPhysical (Layout.bankRadix regs)
            (regs.injective.ne (by decide))]
          exact hlooped.parameters.bankBase_eq
        frameBase_eq := by
          rw [hfinalPhysical (Layout.frameRadix regs)
            (regs.injective.ne (by decide))]
          exact hlooped.parameters.frameBase_eq
        chunkCount_eq := by
          rw [hfinalPhysical (Layout.chunkCount regs)
            (regs.injective.ne (by decide))]
          exact hlooped.parameters.chunkCount_eq
        bankDigitCount_eq := by
          rw [hfinalPhysical (Layout.bankDigitCount regs)
            (regs.injective.ne (by decide))]
          exact hlooped.parameters.bankDigitCount_eq
        modulus_eq := by
          rw [hfinalPhysical (Layout.modulus regs)
            (regs.injective.ne (by decide))]
          exact hlooped.parameters.modulus_eq
        modulusPred_eq := by
          rw [hfinalPhysical (Layout.modulusPred regs)
            (regs.injective.ne (by decide))]
          exact hlooped.parameters.modulusPred_eq }
  have hactiveFinal :
      Representation.ActiveFrame regs frame final := by
    exact
      { fuel_eq := by
          rw [hfinalPhysical (Layout.fuel regs)
            (regs.injective.ne (by decide))]
          exact hlooped.fuel_eq
        node_eq := by
          rw [hfinalPhysical (Layout.nodeCode regs)
            (regs.injective.ne (by decide))]
          exact hlooped.node_eq
        scalar_eq := by
          rw [hfinalPhysical (Layout.scalar regs)
            (regs.injective.ne (by decide))]
          exact hlooped.scalar_eq
        out_eq := by
          rw [hfinalPhysical (Layout.out regs)
            (regs.injective.ne (by decide))]
          exact hlooped.out_eq
        phase_eq := by
          rw [hfinalPhysical (Layout.phaseCode regs)
            (regs.injective.ne (by decide))]
          exact hlooped.phase_eq
        active_eq := by
          simp [final, Basic.exec] }
  have htailFinal :
      FrameTransfer.RepresentsStack regs
        (Representation.digitBase instanceData)
        (Representation.frameBase instanceData) rest final := by
    unfold FrameTransfer.RepresentsStack
    rw [hfinalPhysical
      (Layout.frameStackRegisters regs).word (by
        change regs.index 32 ≠ regs.index 28
        exact regs.injective.ne (by decide))]
    exact hlooped.tail
  have hqueryFinal :
      Representation.QueryState regs instanceData
        { stack := frame :: rest
          registers :=
            streamRegisters instanceData frame
              (combinedValue instanceData frame tape slot interval
                logicalBank)
              (PrimeGrouped.Logarithmic.chunkCount
                (NeighborhoodExecutableEvaluation.payloadWidth
                  tm instanceData.blockLength)
                (NeighborhoodExecutableEvaluation.graphFanIn
                  workTapeCount))
              logicalBank }
        final := by
    exact
      { parameters := hfinalParameters
        stack := ⟨hactiveFinal, htailFinal⟩
        bank := by
          change
            NeighborhoodProgram.RepresentsResidueBank
              tm instanceData.blockLength
              (Representation.fieldBase instanceData)
              (final (regs.index 33)) _
          rw [hfinalPhysical (regs.index 33) (by
            change regs.index 33 ≠ regs.index 28
            exact regs.injective.ne (by decide))]
          exact hlooped.bank
        bank_lt := by
          change
            final (regs.index 33) <
              Representation.fieldBase instanceData ^
                ((NeighborhoodExecutableEvaluation.graphFanIn
                    workTapeCount + 1) *
                  PrimeGrouped.Logarithmic.chunkCount
                    (NeighborhoodExecutableEvaluation.payloadWidth
                      tm instanceData.blockLength)
                    (NeighborhoodExecutableEvaluation.graphFanIn
                      workTapeCount))
          rw [hfinalPhysical (regs.index 33) (by
            change regs.index 33 ≠ regs.index 28
            exact regs.injective.ne (by decide))]
          exact hlooped.bank_lt
        bounds := hlooped.bounds }
  refine ⟨final, ?_, ?_⟩
  · simpa [streamChunks, Cmd.seqList] using
      Runs.seq hinitialize (Runs.seq hloop hfinish)
  · rw [streamRegisters_eq_addScaledAt] at hqueryFinal
    exact hqueryFinal

theorem step_runs_internal
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (rest : List (NeighborhoodScheduler.Frame tm instanceData))
    (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (chunkKernel : Cmd)
    (store : Store)
    (tape : TapeIndex workTapeCount)
    (slot : NeighborhoodGraph.Slot)
    (interval residue residuesLeft : ℕ)
    (hquery :
      Representation.QueryState regs instanceData
        { stack := frame :: rest
          registers := logicalBank }
        store)
    (hphase : frame.phase = .combine residue residuesLeft)
    (hnode :
      frame.node =
        (show
          NeighborhoodEvaluator.QueryNode
            workTapeCount instanceData.horizon
          from .graph (.computation tape slot interval)))
    (hone : store controller.one = 1)
    (hkernel :
      ComputationChunkKernelSpecAt regs instanceData frame tape slot
        interval chunkKernel) :
    ∃ final,
      Runs (step controller regs chunkKernel) store final ∧
      Representation.QueryState regs instanceData
        (NeighborhoodScheduler.State.next
          { stack := frame :: rest
            registers := logicalBank })
        final := by
  let value :=
    combinedValue instanceData frame tape slot interval logicalBank
  let updatedBank :=
    NeighborhoodScheduler.addScaledAt instanceData logicalBank
      frame.out (negativeScalar instanceData frame) value
  obtain ⟨streamed, hstream, hstreamed⟩ :=
    streamChunks_runs controller regs instanceData frame rest
      logicalBank tape slot interval hnode chunkKernel store hquery
      hone hkernel
  have hstreamed' :
      Representation.QueryState regs instanceData
        { stack := frame :: rest
          registers := updatedBank }
        streamed := by
    simpa [updatedBank, value] using hstreamed
  obtain ⟨decoded, hdecode, hdecoded, hqueryDecoded⟩ :=
    Representation.QueryState.decodePhase_runs
      regs frame rest updatedBank streamed hstreamed'
  have hdecodedResidue :
      decoded (Dispatcher.decodedResidue regs) = residue := by
    simpa [hphase, ControlDecode.expectedPhaseValues] using
      hdecoded.residue_eq
  have hdecodedLeft :
      decoded (Dispatcher.decodedResiduesLeft regs) =
        residuesLeft := by
    simpa [hphase, ControlDecode.expectedPhaseValues] using
      hdecoded.residuesLeft_eq
  have hdecodedNext :
      decoded (Dispatcher.decodedNextChild regs) = 0 := by
    simpa [hphase, ControlDecode.expectedPhaseValues] using
      hdecoded.next_eq
  obtain ⟨final, hencode, hencoded⟩ :=
    Dispatcher.encodeCleanupCallPhase_runs regs decoded
  let updatedFrame :
      NeighborhoodScheduler.Frame tm instanceData :=
    { frame with phase := .cleanupCall residue residuesLeft 0 }
  have hframeBound :
      NeighborhoodScheduler.FrameBounds.FrameBound frame :=
    hquery.bounds frame (by simp)
  have hbase :
      0 < Representation.digitBase instanceData := by
    unfold Representation.digitBase CandidateParameters.domainSize
    exact PrimeGrouped.Logarithmic.domainSize_pos _ _
  have hresidue :
      residue <
        Representation.digitBase instanceData ^
          FrameCodec.scalarDigitCount := by
    simpa [hphase, ControlDecode.expectedPhaseValues] using
      FrameBounds.frameBound_phaseResidue_lt frame hframeBound
  have hleft :
      residuesLeft <
        Representation.digitBase instanceData ^
          FrameCodec.scalarDigitCount := by
    simpa [hphase, ControlDecode.expectedPhaseValues] using
      FrameBounds.frameBound_phaseResiduesLeft_lt frame hframeBound
  have hphasePost :
      CursorFinish.PhaseUpdatePost regs updatedFrame.phase
        decoded final := by
    exact
      { phaseCode_eq := by
          rw [hencoded.phaseCode_eq,
            hqueryDecoded.parameters.digitBase_eq,
            hqueryDecoded.parameters.bankBase_eq,
            hdecodedResidue, hdecodedLeft, hdecodedNext]
          simpa [updatedFrame, Representation.fieldBase] using
            (Dispatcher.phaseValue_cleanupCall
              (workTapeCount := workTapeCount) (child := 0)
              hbase hresidue hleft)
        eq_outside := by
          intro address haddress
          apply hencoded.eq_of_ne
          · intro heq
            apply haddress
            simp [CursorFinish.phaseWriteFootprint, heq]
          · intro heq
            apply haddress
            simp [CursorFinish.phaseWriteFootprint, heq] }
  have hbounds :
      NeighborhoodScheduler.FrameBounds.StateBound
        { stack := updatedFrame :: rest
          registers := updatedBank } := by
    have hnext :=
      NeighborhoodScheduler.FrameBounds.StateBound.next
        { stack := frame :: rest
          registers := logicalBank }
        hquery.bounds
    simpa [NeighborhoodScheduler.State.next, hphase, hnode,
      updatedFrame, updatedBank, value, combinedValue,
      negativeScalar, computationArguments] using hnext
  have hqueryFinal :
      Representation.QueryState regs instanceData
        { stack := updatedFrame :: rest
          registers := updatedBank }
        final :=
    CursorFinish.PhaseUpdatePost.queryState
      regs frame updatedFrame rest updatedBank decoded final
      hqueryDecoded (by simp [updatedFrame]) hphasePost hbounds
  refine ⟨final, ?_, ?_⟩
  · simpa [step, installCleanupCall] using
      Runs.seq hstream (Runs.seq hdecode hencode)
  · have hnextEq :
        NeighborhoodScheduler.State.next
            { stack := frame :: rest
              registers := logicalBank } =
          { stack := updatedFrame :: rest
            registers := updatedBank } := by
      simp [NeighborhoodScheduler.State.next, hphase, hnode,
        updatedFrame, updatedBank, value, negativeScalar]
      rfl
    rw [hnextEq]
    exact hqueryFinal

end Internal
end CombineBranch
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
