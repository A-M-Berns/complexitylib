/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.PrepareScale.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.Dispatcher.Internal

/-!
# Prepare-fold catalytic-bank scaling -- proofs
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace PrepareScale
namespace Internal

open RAM Structured

variable {controller : SearchProgram.Registers}

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

private theorem scaleActiveRegister_sourceWritesWithin
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin
      (Layout.residueScaleRegisters regs).footprint
      (ResidueBankOps.scaleActiveRegister regs) := by
  constructor
  · simp [ResidueBankOps.prepareScaleActive,
      ResidueBankOps.prepareScaleActiveOps, Cmd.basics,
      Cmd.seqList, Footprint.CmdWritesWithin,
      Footprint.BasicWritesWithin,
      NeighborhoodProgram.ResidueScaleRegisters.bank,
      NeighborhoodProgram.ResidueScaleRegisters.bankSlot,
      NeighborhoodProgram.ResidueBankRegisters.operand,
      NeighborhoodProgram.ResidueScaleRegisters.index_mem_footprint]
  · exact
      NeighborhoodProgram.bankScaleRegister_sourceWritesWithin
        (Layout.residueScaleRegisters regs)

private theorem scaleFootprint_subset_write
    (regs : NeighborhoodTrial.Registers controller) :
    (Layout.residueScaleRegisters regs).footprint ⊆
      writeFootprint regs :=
  Finset.subset_union_left

private theorem scratch_mem_write
    (regs : NeighborhoodTrial.Registers controller) :
    Layout.codecScratch regs ∈ writeFootprint regs := by
  apply Finset.mem_union_right
  simp

private theorem frameCode_mem_write
    (regs : NeighborhoodTrial.Registers controller) :
    Layout.frameCode regs ∈ writeFootprint regs := by
  apply Finset.mem_union_right
  simp

private theorem scalar_mem_write
    (regs : NeighborhoodTrial.Registers controller) :
    Layout.scalar regs ∈ writeFootprint regs := by
  apply Finset.mem_union_right
  simp

private theorem out_mem_write
    (regs : NeighborhoodTrial.Registers controller) :
    Layout.out regs ∈ writeFootprint regs := by
  apply Finset.mem_union_right
  simp

private theorem targetTest_mem_write
    (regs : NeighborhoodTrial.Registers controller) :
    (Dispatcher.cleanupInverseRegisters regs).test ∈
      writeFootprint regs := by
  apply scaleFootprint_subset_write regs
  change
    (Layout.residueScaleRegisters regs).index 5 ∈
      (Layout.residueScaleRegisters regs).footprint
  exact
    (Layout.residueScaleRegisters regs).index_mem_footprint 5

theorem scaleChildTarget_writesWithin_internal
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (writeFootprint regs)
      (scaleChildTarget regs) := by
  have hsave :
      Footprint.CmdWritesWithin (writeFootprint regs)
        (Dispatcher.saveActiveFields regs) := by
    simp [Dispatcher.saveActiveFields, Dispatcher.copy,
      Footprint.CmdWritesWithin, Footprint.BasicWritesWithin,
      scratch_mem_write regs, frameCode_mem_write regs]
  have hinstall :
      Footprint.CmdWritesWithin (writeFootprint regs)
        (Dispatcher.copy
          (Layout.scalar regs)
          (Dispatcher.decodedResidue regs)) := by
    simp [Dispatcher.copy, Footprint.CmdWritesWithin,
      Footprint.BasicWritesWithin, scalar_mem_write regs]
  have htarget :
      Footprint.CmdWritesWithin (writeFootprint regs)
        (Dispatcher.selectChildTarget regs) := by
    have hcopyOut :
        Footprint.CmdWritesWithin (writeFootprint regs)
          (Dispatcher.copy
            (Layout.out regs) (Dispatcher.decodedChild regs)) := by
      simp [Dispatcher.copy, Footprint.CmdWritesWithin,
        Footprint.BasicWritesWithin, out_mem_write regs]
    simp only [Dispatcher.selectChildTarget,
      Footprint.CmdWritesWithin]
    exact
      ⟨targetTest_mem_write regs,
        ⟨hcopyOut, out_mem_write regs⟩, hcopyOut⟩
  have hscale :
      Footprint.CmdWritesWithin (writeFootprint regs)
        (ResidueBankOps.scaleActiveRegister regs) :=
    cmdWritesWithin_mono
      (scaleActiveRegister_sourceWritesWithin regs)
      (scaleFootprint_subset_write regs)
  have hrestore :
      Footprint.CmdWritesWithin (writeFootprint regs)
        (Dispatcher.restoreActiveFields regs) := by
    simp [Dispatcher.restoreActiveFields, Dispatcher.copy,
      Footprint.CmdWritesWithin, Footprint.BasicWritesWithin,
      scalar_mem_write regs, out_mem_write regs]
  simpa only [scaleChildTarget, Cmd.seqList,
    Footprint.CmdWritesWithin] using
      And.intro hsave
        (And.intro hinstall
          (And.intro htarget
            (And.intro hscale hrestore)))

theorem writeFootprint_subset_layout_internal
    (regs : NeighborhoodTrial.Registers controller) :
    writeFootprint regs ⊆ regs.layout.footprint := by
  intro address haddress
  rw [writeFootprint, Finset.mem_union] at haddress
  rcases haddress with hscale | hactive
  · exact Layout.residueScale_footprint_subset regs hscale
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hactive
    rcases hactive with rfl | rfl | rfl | rfl
    · exact Layout.index_mem_layout_footprint regs 31
    · exact Layout.index_mem_layout_footprint regs 29
    · exact Layout.index_mem_layout_footprint regs 25
    · exact Layout.index_mem_layout_footprint regs 26

private theorem copy_update_runs
    {destination source : ℕ} (store : Store)
    (hne : destination ≠ source) :
    Runs (Dispatcher.copy destination source) store
      (Function.update store destination (store source)) := by
  apply Runs.seq (Runs.basic (.imm destination 0) store)
  simpa [Basic.exec, Function.update_of_ne, hne, Ne.symm hne] using
    Runs.basic
      (.add destination source destination)
      (Basic.exec (.imm destination 0) store)

private theorem physical_not_mem_scale_footprint
    (regs : NeighborhoodTrial.Registers controller)
    (slot : Fin 34)
    (hslot : ∀ index, Layout.residueScaleMap index ≠ slot) :
    regs.index slot ∉
      (Layout.residueScaleRegisters regs).footprint := by
  simp only [NeighborhoodProgram.ResidueScaleRegisters.footprint,
    Layout.residueScaleRegisters, Finset.mem_image,
    Finset.mem_univ, true_and, not_exists]
  intro index
  rw [regs.injective.eq_iff]
  exact hslot index

private theorem scale_run_preserves_physical
    (regs : NeighborhoodTrial.Registers controller)
    (slot : Fin 34)
    (hslot : ∀ index, Layout.residueScaleMap index ≠ slot)
    {initial final : Store}
    (hrun :
      Runs (ResidueBankOps.scaleActiveRegister regs)
        initial final) :
    final (regs.index slot) = initial (regs.index slot) :=
  Footprint.runs_eq_outside
    (scaleActiveRegister_sourceWritesWithin regs) hrun
    (physical_not_mem_scale_footprint regs slot hslot)

theorem scaleChildTarget_runs_internal
    {workTapeCount : ℕ} (tm : TM workTapeCount)
    (blockLength parentScalar residue base word : ℕ)
    (original :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm blockLength)
    (out :
      Fin
        (NeighborhoodExecutableEvaluation.graphFanIn
          workTapeCount + 1))
    (child :
      Fin
        (NeighborhoodExecutableEvaluation.graphFanIn
          workTapeCount))
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store)
    (hbase : 0 < base)
    (hmodulus :
      0 < NeighborhoodExecutableEvaluation.modulus tm blockLength)
    (hmodulusBase :
      NeighborhoodExecutableEvaluation.modulus tm blockLength ≤ base)
    (hword :
      store
          (Layout.residueScaleRegisters regs).bank.bank.word =
        word)
    (hrep :
      NeighborhoodProgram.RepresentsResidueBank
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
    (hbaseValue :
      store
          (Layout.residueScaleRegisters regs).bank.bank.base =
        base)
    (hmodulusValue :
      store (Layout.residueScaleRegisters regs).bank.modulus =
        NeighborhoodExecutableEvaluation.modulus tm blockLength)
    (hmodulusPred :
      store (Layout.residueScaleRegisters regs).bank.modulusPred =
        NeighborhoodExecutableEvaluation.modulus tm blockLength - 1)
    (hone :
      store (Dispatcher.cleanupInverseRegisters regs).one = 1)
    (hscalar : store (Layout.scalar regs) = parentScalar)
    (hout : store (Layout.out regs) = out.val)
    (hchunkCount :
      store (Layout.chunkCount regs) =
        TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
          (NeighborhoodExecutableEvaluation.payloadWidth tm blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn
            workTapeCount))
    (hdecodedResidue :
      store (Dispatcher.decodedResidue regs) = residue)
    (hdecodedChild :
      store (Dispatcher.decodedChild regs) = child.val) :
    ∃ final finalWord,
      Runs (scaleChildTarget regs) store final ∧
      ScalePost tm blockLength parentScalar residue base finalWord
        original out child regs store final := by
  obtain ⟨saved, hsaveRun, hsavePost⟩ :=
    Dispatcher.Internal.saveActiveFields_runs_internal regs store
  have hsavedPhysical
      (slot : Fin 34)
      (hscratch : slot ≠ 31)
      (hframe : slot ≠ 29) :
      saved (regs.index slot) = store (regs.index slot) :=
    hsavePost.eq_of_ne _
      (regs.injective.ne hscratch)
      (regs.injective.ne hframe)
  let installed :=
    Function.update saved (Layout.scalar regs)
      (saved (Dispatcher.decodedResidue regs))
  have hinstallRun :
      Runs
        (Dispatcher.copy
          (Layout.scalar regs)
          (Dispatcher.decodedResidue regs))
        saved installed :=
    copy_update_runs saved (regs.injective.ne (by decide))
  have hinstalledPhysical
      (slot : Fin 34) (hscalarSlot : slot ≠ 25) :
      installed (regs.index slot) = saved (regs.index slot) := by
    simp [installed, Function.update_of_ne,
      regs.injective.ne hscalarSlot]
  have hsavedResidue :
      saved (Dispatcher.decodedResidue regs) = residue := by
    simpa [Dispatcher.decodedResidue] using
      (hsavedPhysical (9 : Fin 34) (by decide)
        (by decide)).trans hdecodedResidue
  have hinstalledScalar :
      installed (Layout.scalar regs) = residue := by
    simp [installed, hsavedResidue]
  have hinstalledOne :
      installed (Dispatcher.cleanupInverseRegisters regs).one = 1 := by
    calc
      installed (Dispatcher.cleanupInverseRegisters regs).one =
          saved (Dispatcher.cleanupInverseRegisters regs).one := by
        simpa [Dispatcher.cleanupInverseRegisters,
          Dispatcher.cleanupInverseMap] using
          hinstalledPhysical (17 : Fin 34) (by decide)
      _ = store (Dispatcher.cleanupInverseRegisters regs).one := by
        simpa [Dispatcher.cleanupInverseRegisters,
          Dispatcher.cleanupInverseMap] using
          hsavedPhysical (17 : Fin 34) (by decide) (by decide)
      _ = 1 := hone
  have hinstalledChild :
      installed (Dispatcher.decodedChild regs) = child.val := by
    calc
      installed (Dispatcher.decodedChild regs) =
          saved (Dispatcher.decodedChild regs) := by
        simpa [Dispatcher.decodedChild] using
          hinstalledPhysical (11 : Fin 34) (by decide)
      _ = store (Dispatcher.decodedChild regs) := by
        simpa [Dispatcher.decodedChild] using
          hsavedPhysical (11 : Fin 34) (by decide) (by decide)
      _ = child.val := hdecodedChild
  have hinstalledOut :
      installed (Layout.out regs) = out.val := by
    calc
      installed (Layout.out regs) = saved (Layout.out regs) := by
        exact hinstalledPhysical (26 : Fin 34) (by decide)
      _ = store (Layout.out regs) :=
        hsavedPhysical (26 : Fin 34) (by decide) (by decide)
      _ = out.val := hout
  have hinstalledScratch :
      installed (Layout.codecScratch regs) = parentScalar := by
    calc
      installed (Layout.codecScratch regs) =
          saved (Layout.codecScratch regs) :=
        hinstalledPhysical (31 : Fin 34) (by decide)
      _ = store (Layout.scalar regs) :=
        hsavePost.savedScalar_eq
      _ = parentScalar := hscalar
  have hinstalledFrame :
      installed (Layout.frameCode regs) = out.val := by
    calc
      installed (Layout.frameCode regs) =
          saved (Layout.frameCode regs) :=
        hinstalledPhysical (29 : Fin 34) (by decide)
      _ = store (Layout.out regs) := hsavePost.savedOut_eq
      _ = out.val := hout
  obtain ⟨targeted, htargetRun, htargetPost⟩ :=
    Dispatcher.Internal.selectChildTarget_runs_internal
      regs installed hinstalledOne
  have htargetedPhysical
      (slot : Fin 34)
      (hscratch : slot ≠ 31)
      (hframe : slot ≠ 29)
      (hscalarSlot : slot ≠ 25)
      (houtSlot : slot ≠ 26)
      (htest :
        regs.index slot ≠
          (Dispatcher.cleanupInverseRegisters regs).test) :
      targeted (regs.index slot) = store (regs.index slot) := by
    calc
      targeted (regs.index slot) =
          installed (regs.index slot) :=
        htargetPost.eq_of_ne _
          (regs.injective.ne houtSlot) htest
      _ = saved (regs.index slot) :=
        hinstalledPhysical slot hscalarSlot
      _ = store (regs.index slot) :=
        hsavedPhysical slot hscratch hframe
  have htargetedScalar :
      targeted (Layout.scalar regs) = residue := by
    calc
      targeted (Layout.scalar regs) =
          installed (Layout.scalar regs) :=
        htargetPost.eq_of_ne _
          (regs.injective.ne (by decide))
          (by
            simp [Dispatcher.cleanupInverseRegisters,
              Dispatcher.cleanupInverseMap, regs.injective.eq_iff])
      _ = residue := hinstalledScalar
  have htargetedOut :
      targeted (Layout.out regs) = (out.succAbove child).val := by
    calc
      targeted (Layout.out regs) =
          if installed (Dispatcher.decodedChild regs) <
              installed (Layout.out regs) then
            installed (Dispatcher.decodedChild regs)
          else
            installed (Dispatcher.decodedChild regs) + 1 :=
        htargetPost.out_eq
      _ = if child.val < out.val then
            child.val
          else
            child.val + 1 := by
        rw [hinstalledChild, hinstalledOut]
      _ = (out.succAbove child).val :=
        Dispatcher.Internal.childTargetValue_eq_succAbove_internal
          out child
  have htargetedScratch :
      targeted (Layout.codecScratch regs) = parentScalar := by
    calc
      targeted (Layout.codecScratch regs) =
          installed (Layout.codecScratch regs) :=
        htargetPost.eq_of_ne _
          (regs.injective.ne (by decide))
          (by
            simp [Dispatcher.cleanupInverseRegisters,
              Dispatcher.cleanupInverseMap, regs.injective.eq_iff])
      _ = parentScalar := hinstalledScratch
  have htargetedFrame :
      targeted (Layout.frameCode regs) = out.val := by
    calc
      targeted (Layout.frameCode regs) =
          installed (Layout.frameCode regs) :=
        htargetPost.eq_of_ne _
          (regs.injective.ne (by decide))
          (by
            simp [Dispatcher.cleanupInverseRegisters,
              Dispatcher.cleanupInverseMap, regs.injective.eq_iff])
      _ = out.val := hinstalledFrame
  have htargetedWord :
      targeted
          (Layout.residueScaleRegisters regs).bank.bank.word =
        word := by
    simpa [Layout.residueScaleRegisters, Layout.residueScaleMap,
      NeighborhoodProgram.ResidueScaleRegisters.bank,
      NeighborhoodProgram.ResidueScaleRegisters.bankSlot,
      NeighborhoodProgram.ResidueBankRegisters.bank,
      NeighborhoodProgram.ResidueBankRegisters.bankSlot,
      NeighborhoodProgram.BankRegisters.mainStack,
      NeighborhoodProgram.BankRegisters.mainMap] using
      (htargetedPhysical (33 : Fin 34)
        (by decide) (by decide) (by decide) (by decide)
        (by
          simp [Dispatcher.cleanupInverseRegisters,
            Dispatcher.cleanupInverseMap,
            regs.injective.eq_iff])).trans hword
  have htargetedBase :
      targeted
          (Layout.residueScaleRegisters regs).bank.bank.base =
        base := by
    simpa [Layout.residueScaleRegisters, Layout.residueScaleMap,
      NeighborhoodProgram.ResidueScaleRegisters.bank,
      NeighborhoodProgram.ResidueScaleRegisters.bankSlot,
      NeighborhoodProgram.ResidueBankRegisters.bank,
      NeighborhoodProgram.ResidueBankRegisters.bankSlot,
      NeighborhoodProgram.BankRegisters.mainStack,
      NeighborhoodProgram.BankRegisters.mainMap] using
      (htargetedPhysical (14 : Fin 34)
        (by decide) (by decide) (by decide) (by decide)
        (by
          simp [Dispatcher.cleanupInverseRegisters,
            Dispatcher.cleanupInverseMap,
            regs.injective.eq_iff])).trans hbaseValue
  have htargetedModulus :
      targeted (Layout.residueScaleRegisters regs).bank.modulus =
        NeighborhoodExecutableEvaluation.modulus tm blockLength := by
    simpa [Layout.residueScaleRegisters, Layout.residueScaleMap,
      NeighborhoodProgram.ResidueScaleRegisters.bank,
      NeighborhoodProgram.ResidueScaleRegisters.bankSlot,
      NeighborhoodProgram.ResidueBankRegisters.modulus] using
      (htargetedPhysical (24 : Fin 34)
        (by decide) (by decide) (by decide) (by decide)
        (by
          simp [Dispatcher.cleanupInverseRegisters,
            Dispatcher.cleanupInverseMap,
            regs.injective.eq_iff])).trans hmodulusValue
  have htargetedModulusPred :
      targeted (Layout.residueScaleRegisters regs).bank.modulusPred =
        NeighborhoodExecutableEvaluation.modulus tm blockLength - 1 := by
    simpa [Layout.residueScaleRegisters, Layout.residueScaleMap,
      NeighborhoodProgram.ResidueScaleRegisters.bank,
      NeighborhoodProgram.ResidueScaleRegisters.bankSlot,
      NeighborhoodProgram.ResidueBankRegisters.modulusPred] using
      (htargetedPhysical (16 : Fin 34)
        (by decide) (by decide) (by decide) (by decide)
        (by
          simp [Dispatcher.cleanupInverseRegisters,
            Dispatcher.cleanupInverseMap,
            regs.injective.eq_iff])).trans hmodulusPred
  have htargetedChunkCount :
      targeted (Layout.chunkCount regs) =
        TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
          (NeighborhoodExecutableEvaluation.payloadWidth tm blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn
            workTapeCount) := by
    exact
      (htargetedPhysical (7 : Fin 34)
        (by decide) (by decide) (by decide) (by decide)
        (by
          simp [Dispatcher.cleanupInverseRegisters,
            Dispatcher.cleanupInverseMap,
            regs.injective.eq_iff])).trans hchunkCount
  obtain ⟨scaled, finalWord, hscaleRun, hscaledWord,
      hscaledRep, hscaledWordLt, hscaledBase, hscaledBasePred, hscaledOne,
      hscaledModulus, hscaledModulusPred, _hscaledOperand⟩ :=
    ResidueBankOps.Internal.scaleActiveRegister_runs_internal
      tm blockLength residue base word original
      (out.succAbove child) regs targeted hbase hmodulus
      hmodulusBase htargetedWord hrep hwordLt htargetedBase
      htargetedModulus htargetedModulusPred htargetedScalar
      htargetedOut htargetedChunkCount
  have hscaledScratch :
      scaled (Layout.codecScratch regs) =
        targeted (Layout.codecScratch regs) :=
    scale_run_preserves_physical regs 31 (by
      intro index
      fin_cases index <;> simp [Layout.residueScaleMap]) hscaleRun
  have hscaledFrame :
      scaled (Layout.frameCode regs) =
        targeted (Layout.frameCode regs) :=
    scale_run_preserves_physical regs 29 (by
      intro index
      fin_cases index <;> simp [Layout.residueScaleMap]) hscaleRun
  obtain ⟨final, hrestoreRun, hrestorePost⟩ :=
    Dispatcher.Internal.restoreActiveFields_runs_internal regs scaled
  have hrun :
      Runs (scaleChildTarget regs) store final := by
    simpa [scaleChildTarget, Cmd.seqList] using
      Runs.seq hsaveRun
        (Runs.seq hinstallRun
          (Runs.seq htargetRun
            (Runs.seq hscaleRun hrestoreRun)))
  refine ⟨final, finalWord, hrun, ?_⟩
  refine
    { scalar_eq := ?_
      out_eq := ?_
      word_eq := ?_
      represents := hscaledRep
      word_lt := hscaledWordLt
      base_eq := ?_
      basePred_eq := ?_
      one_eq := ?_
      modulus_eq := ?_
      modulusPred_eq := ?_
      eq_outside := ?_ }
  · calc
      final (Layout.scalar regs) =
          scaled (Layout.codecScratch regs) :=
        hrestorePost.scalar_eq
      _ = targeted (Layout.codecScratch regs) := hscaledScratch
      _ = parentScalar := htargetedScratch
  · calc
      final (Layout.out regs) =
          scaled (Layout.frameCode regs) :=
        hrestorePost.out_eq
      _ = targeted (Layout.frameCode regs) := hscaledFrame
      _ = out.val := htargetedFrame
  · exact (hrestorePost.eq_of_ne _
      (by
        simp [Layout.residueScaleRegisters, Layout.residueScaleMap,
          NeighborhoodProgram.ResidueScaleRegisters.bank,
          NeighborhoodProgram.ResidueScaleRegisters.bankSlot,
          NeighborhoodProgram.ResidueBankRegisters.bank,
          NeighborhoodProgram.ResidueBankRegisters.bankSlot,
          regs.injective.eq_iff])
      (by
        simp [Layout.residueScaleRegisters, Layout.residueScaleMap,
          NeighborhoodProgram.ResidueScaleRegisters.bank,
          NeighborhoodProgram.ResidueScaleRegisters.bankSlot,
          NeighborhoodProgram.ResidueBankRegisters.bank,
          NeighborhoodProgram.ResidueBankRegisters.bankSlot,
          regs.injective.eq_iff])).trans hscaledWord
  · exact (hrestorePost.eq_of_ne _
      (by
        simp [Layout.residueScaleRegisters, Layout.residueScaleMap,
          NeighborhoodProgram.ResidueScaleRegisters.bank,
          NeighborhoodProgram.ResidueScaleRegisters.bankSlot,
          NeighborhoodProgram.ResidueBankRegisters.bank,
          NeighborhoodProgram.ResidueBankRegisters.bankSlot,
          regs.injective.eq_iff])
      (by
        simp [Layout.residueScaleRegisters, Layout.residueScaleMap,
          NeighborhoodProgram.ResidueScaleRegisters.bank,
          NeighborhoodProgram.ResidueScaleRegisters.bankSlot,
          NeighborhoodProgram.ResidueBankRegisters.bank,
          NeighborhoodProgram.ResidueBankRegisters.bankSlot,
          regs.injective.eq_iff])).trans hscaledBase
  · exact (hrestorePost.eq_of_ne _
      (by
        simp [Layout.residueScaleRegisters, Layout.residueScaleMap,
          NeighborhoodProgram.ResidueScaleRegisters.bank,
          NeighborhoodProgram.ResidueScaleRegisters.bankSlot,
          NeighborhoodProgram.ResidueBankRegisters.bank,
          NeighborhoodProgram.ResidueBankRegisters.bankSlot,
          regs.injective.eq_iff])
      (by
        simp [Layout.residueScaleRegisters, Layout.residueScaleMap,
          NeighborhoodProgram.ResidueScaleRegisters.bank,
          NeighborhoodProgram.ResidueScaleRegisters.bankSlot,
          NeighborhoodProgram.ResidueBankRegisters.bank,
          NeighborhoodProgram.ResidueBankRegisters.bankSlot,
          regs.injective.eq_iff])).trans hscaledBasePred
  · exact (hrestorePost.eq_of_ne _
      (by
        simp [Layout.residueScaleRegisters, Layout.residueScaleMap,
          NeighborhoodProgram.ResidueScaleRegisters.bank,
          NeighborhoodProgram.ResidueScaleRegisters.bankSlot,
          NeighborhoodProgram.ResidueBankRegisters.bank,
          NeighborhoodProgram.ResidueBankRegisters.bankSlot,
          regs.injective.eq_iff])
      (by
        simp [Layout.residueScaleRegisters, Layout.residueScaleMap,
          NeighborhoodProgram.ResidueScaleRegisters.bank,
          NeighborhoodProgram.ResidueScaleRegisters.bankSlot,
          NeighborhoodProgram.ResidueBankRegisters.bank,
          NeighborhoodProgram.ResidueBankRegisters.bankSlot,
          regs.injective.eq_iff])).trans hscaledOne
  · exact (hrestorePost.eq_of_ne _
      (by
        simp [Layout.residueScaleRegisters, Layout.residueScaleMap,
          NeighborhoodProgram.ResidueScaleRegisters.bank,
          NeighborhoodProgram.ResidueScaleRegisters.bankSlot,
          NeighborhoodProgram.ResidueBankRegisters.modulus,
          regs.injective.eq_iff])
      (by
        simp [Layout.residueScaleRegisters, Layout.residueScaleMap,
          NeighborhoodProgram.ResidueScaleRegisters.bank,
          NeighborhoodProgram.ResidueScaleRegisters.bankSlot,
          NeighborhoodProgram.ResidueBankRegisters.modulus,
          regs.injective.eq_iff])).trans hscaledModulus
  · exact (hrestorePost.eq_of_ne _
      (by
        simp [Layout.residueScaleRegisters, Layout.residueScaleMap,
          NeighborhoodProgram.ResidueScaleRegisters.bank,
          NeighborhoodProgram.ResidueScaleRegisters.bankSlot,
          NeighborhoodProgram.ResidueBankRegisters.modulusPred,
          regs.injective.eq_iff])
      (by
        simp [Layout.residueScaleRegisters, Layout.residueScaleMap,
          NeighborhoodProgram.ResidueScaleRegisters.bank,
          NeighborhoodProgram.ResidueScaleRegisters.bankSlot,
          NeighborhoodProgram.ResidueBankRegisters.modulusPred,
          regs.injective.eq_iff])).trans hscaledModulusPred
  · intro address haddress
    exact Footprint.runs_eq_outside
      (scaleChildTarget_writesWithin_internal regs)
      hrun haddress

end Internal
end PrepareScale
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
