/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.FrameInstall.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.Layout
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodScheduler.FrameBounds

/-!
# Active child-frame installation -- proofs
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace FrameInstall
namespace Internal

open RAM Structured
open TreeEval CookMertz

variable {controller : SearchProgram.Registers}

private theorem basics_runs
    (ops : List Basic) (store : Store) :
    Runs (Cmd.basics ops) store (Basic.execList ops store) := by
  obtain ⟨cost, space, hexec⟩ :=
    RAM.Structured.Internal.exec_basics_exists ops store
  exact ⟨ops.length, cost, space, hexec⟩

theorem installPrepareChild_writesWithin_internal
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin
      (writeFootprint regs) (installPrepareChild regs) := by
  simp [installPrepareChild, writeFootprint, Cmd.basics, Cmd.seqList,
    Footprint.CmdWritesWithin, Footprint.BasicWritesWithin]

theorem installCleanupChild_writesWithin_internal
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin
      (writeFootprint regs) (installCleanupChild regs) := by
  simp [installCleanupChild, writeFootprint, Cmd.basics, Cmd.seqList,
    Footprint.CmdWritesWithin, Footprint.BasicWritesWithin]

theorem writeFootprint_subset_layout_internal
    (regs : NeighborhoodTrial.Registers controller) :
    writeFootprint regs ⊆ regs.layout.footprint := by
  intro address haddress
  simp only [writeFootprint, Finset.mem_insert, Finset.mem_singleton]
    at haddress
  rcases haddress with h | h | h | h
  · subst address
    exact Layout.index_mem_layout_footprint regs 22
  · subst address
    exact Layout.index_mem_layout_footprint regs 25
  · subst address
    exact Layout.index_mem_layout_footprint regs 27
  · subst address
    exact Layout.index_mem_layout_footprint regs 28

theorem installPrepareChild_runs_internal
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store) :
    ∃ final,
      Runs (installPrepareChild regs) store final ∧
      InstallPost regs 1 store final := by
  let final :=
    Basic.execList
      [.imm (Layout.scalar regs) 1,
        .sub (Layout.fuel regs) (Layout.fuel regs) (Layout.scalar regs),
        .imm (Layout.phaseCode regs) 0,
        .imm (Layout.active regs) 1]
      store
  refine ⟨final, ?_, ?_⟩
  · simpa [installPrepareChild, final] using
      (basics_runs
        [.imm (Layout.scalar regs) 1,
          .sub (Layout.fuel regs)
            (Layout.fuel regs) (Layout.scalar regs),
          .imm (Layout.phaseCode regs) 0,
          .imm (Layout.active regs) 1]
        store)
  · constructor
    · simp [final, Basic.execList, Basic.exec, regs.injective.eq_iff]
    · simp [final, Basic.execList, Basic.exec, regs.injective.eq_iff]
    · simp [final, Basic.execList, Basic.exec, regs.injective.eq_iff]
    · simp [final, Basic.execList, Basic.exec, regs.injective.eq_iff]
    · simp [final, Basic.execList, Basic.exec, regs.injective.eq_iff]
    · simp [final, Basic.execList, Basic.exec, regs.injective.eq_iff]
    · intro address haddress
      simp only [writeFootprint, Finset.mem_insert,
        Finset.mem_singleton] at haddress
      have hfuel : address ≠ Layout.fuel regs :=
        fun h => haddress (Or.inl h)
      have hscalar : address ≠ Layout.scalar regs :=
        fun h => haddress (Or.inr (Or.inl h))
      have hphase : address ≠ Layout.phaseCode regs :=
        fun h => haddress (Or.inr (Or.inr (Or.inl h)))
      have hactive : address ≠ Layout.active regs :=
        fun h => haddress (Or.inr (Or.inr (Or.inr h)))
      simp [final, Basic.execList, Basic.exec, hfuel, hscalar,
        hphase, hactive]

theorem installCleanupChild_runs_internal
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store) :
    ∃ final,
      Runs (installCleanupChild regs) store final ∧
      InstallPost regs (store (Layout.modulusPred regs)) store final := by
  let final :=
    Basic.execList
      [.imm (Layout.scalar regs) 1,
        .sub (Layout.fuel regs) (Layout.fuel regs) (Layout.scalar regs),
        .imm (Layout.scalar regs) 0,
        .add (Layout.scalar regs)
          (Layout.modulusPred regs) (Layout.scalar regs),
        .imm (Layout.phaseCode regs) 0,
        .imm (Layout.active regs) 1]
      store
  refine ⟨final, ?_, ?_⟩
  · simpa [installCleanupChild, final] using
      (basics_runs
        [.imm (Layout.scalar regs) 1,
          .sub (Layout.fuel regs)
            (Layout.fuel regs) (Layout.scalar regs),
          .imm (Layout.scalar regs) 0,
          .add (Layout.scalar regs)
            (Layout.modulusPred regs) (Layout.scalar regs),
          .imm (Layout.phaseCode regs) 0,
          .imm (Layout.active regs) 1]
        store)
  · constructor
    · simp [final, Basic.execList, Basic.exec, regs.injective.eq_iff]
    · simp [final, Basic.execList, Basic.exec, regs.injective.eq_iff]
    · simp [final, Basic.execList, Basic.exec, regs.injective.eq_iff]
    · simp [final, Basic.execList, Basic.exec, regs.injective.eq_iff]
    · simp [final, Basic.execList, Basic.exec, regs.injective.eq_iff]
    · simp [final, Basic.execList, Basic.exec, regs.injective.eq_iff]
    · intro address haddress
      simp only [writeFootprint, Finset.mem_insert,
        Finset.mem_singleton] at haddress
      have hfuel : address ≠ Layout.fuel regs :=
        fun h => haddress (Or.inl h)
      have hscalar : address ≠ Layout.scalar regs :=
        fun h => haddress (Or.inr (Or.inl h))
      have hphase : address ≠ Layout.phaseCode regs :=
        fun h => haddress (Or.inr (Or.inr (Or.inl h)))
      have hactive : address ≠ Layout.active regs :=
        fun h => haddress (Or.inr (Or.inr (Or.inr h)))
      simp [final, Basic.execList, Basic.exec, hfuel, hscalar,
        hphase, hactive]

private theorem parameters_of_install_internal
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (regs : NeighborhoodTrial.Registers controller)
    (initial final : Store)
    (hparameters : Representation.Parameters regs instanceData initial)
    (hrun : Runs command initial final)
    (hwrites :
      Footprint.CmdWritesWithin (writeFootprint regs) command) :
    Representation.Parameters regs instanceData final := by
  have preserved (address : ℕ)
      (houtside : address ∉ writeFootprint regs) :
      final address = initial address :=
    Footprint.runs_eq_outside hwrites hrun houtside
  constructor
  · rw [preserved (Layout.blockLength regs) (by
      simp [writeFootprint, Layout.blockLength,
        regs.injective.eq_iff])]
    exact hparameters.blockLength_eq
  · rw [preserved (Layout.horizon regs) (by
      simp [writeFootprint, Layout.horizon,
        regs.injective.eq_iff])]
    exact hparameters.horizon_eq
  · rw [preserved (Layout.chunkRadix regs) (by
      simp [writeFootprint, Layout.chunkRadix,
        regs.injective.eq_iff])]
    exact hparameters.digitBase_eq
  · rw [preserved (Layout.bankRadix regs) (by
      simp [writeFootprint, Layout.bankRadix,
        regs.injective.eq_iff])]
    exact hparameters.bankBase_eq
  · rw [preserved (Layout.frameRadix regs) (by
      simp [writeFootprint, Layout.frameRadix,
        regs.injective.eq_iff])]
    exact hparameters.frameBase_eq
  · rw [preserved (Layout.chunkCount regs) (by
      simp [writeFootprint, Layout.chunkCount,
        regs.injective.eq_iff])]
    exact hparameters.chunkCount_eq
  · rw [preserved (Layout.bankDigitCount regs) (by
      simp [writeFootprint, Layout.bankDigitCount,
        regs.injective.eq_iff])]
    exact hparameters.bankDigitCount_eq
  · rw [preserved (Layout.modulus regs) (by
      simp [writeFootprint, Layout.modulus,
        regs.injective.eq_iff])]
    exact hparameters.modulus_eq
  · rw [preserved (Layout.modulusPred regs) (by
      simp [writeFootprint, Layout.modulusPred,
        regs.injective.eq_iff])]
    exact hparameters.modulusPred_eq

theorem parameters_of_installPrepareChild_internal
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (regs : NeighborhoodTrial.Registers controller)
    (initial final : Store)
    (hparameters : Representation.Parameters regs instanceData initial)
    (hrun : Runs (installPrepareChild regs) initial final) :
    Representation.Parameters regs instanceData final :=
  parameters_of_install_internal regs initial final hparameters hrun
    (installPrepareChild_writesWithin_internal regs)

theorem parameters_of_installCleanupChild_internal
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (regs : NeighborhoodTrial.Registers controller)
    (initial final : Store)
    (hparameters : Representation.Parameters regs instanceData initial)
    (hrun : Runs (installCleanupChild regs) initial final) :
    Representation.Parameters regs instanceData final :=
  parameters_of_install_internal regs initial final hparameters hrun
    (installCleanupChild_writesWithin_internal regs)

private theorem representsStack_of_installPost_internal
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (regs : NeighborhoodTrial.Registers controller)
    (digitBase frameBase : ℕ)
    (frames : List (NeighborhoodScheduler.Frame tm instanceData))
    (initial final : Store)
    (hpost : InstallPost regs scalar initial final)
    (hstack :
      FrameTransfer.RepresentsStack regs digitBase frameBase
        frames initial) :
    FrameTransfer.RepresentsStack regs digitBase frameBase frames final := by
  unfold FrameTransfer.RepresentsStack at hstack ⊢
  rw [hpost.eq_outside
    (Layout.frameStackRegisters regs).word (by
      simp [writeFootprint, Layout.frameStackRegisters,
        Layout.frameStackMap, regs.injective.eq_iff])]
  exact hstack

theorem installPost_bank_eq_internal
    (regs : NeighborhoodTrial.Registers controller)
    {initial final : Store}
    (hpost : InstallPost regs scalar initial final) :
    final regs.layout.bank = initial regs.layout.bank :=
  hpost.eq_outside regs.layout.bank (by
    simp [writeFootprint, NeighborhoodTrial.Registers.layout,
      regs.injective.eq_iff])

theorem prepareChild_activeFrame_internal
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (regs : NeighborhoodTrial.Registers controller)
    (parent : NeighborhoodScheduler.Frame tm instanceData)
    (child :
      Fin (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount))
    (initial final : Store)
    (hpost : InstallPost regs 1 initial final)
    (hfuel : initial (Layout.fuel regs) = parent.fuel)
    (hnode :
      initial (Layout.nodeCode regs) =
        FrameCodec.encodeNode
          (Representation.digitBase instanceData)
          (parent.childNode child))
    (hout :
      initial (Layout.out regs) = (parent.childTarget child).val) :
    Representation.ActiveFrame regs (parent.prepareChild child) final := by
  constructor
  · simpa [NeighborhoodScheduler.Frame.prepareChild] using
      hpost.fuel_eq.trans (congrArg (fun value => value - 1) hfuel)
  · simpa [NeighborhoodScheduler.Frame.prepareChild] using
      hpost.nodeCode_eq.trans hnode
  · rw [hpost.scalar_eq]
    simp [NeighborhoodScheduler.Frame.prepareChild,
      PrimeField.Runtime.normalize,
      Nat.mod_eq_of_lt
        (NeighborhoodScheduler.FrameBounds.fieldModulus_one_lt
          instanceData)]
  · simpa [NeighborhoodScheduler.Frame.prepareChild] using
      hpost.out_eq.trans hout
  · rw [hpost.phaseCode_eq]
    rfl
  · exact hpost.active_eq

theorem prepareChild_stack_internal
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (regs : NeighborhoodTrial.Registers controller)
    (parent : NeighborhoodScheduler.Frame tm instanceData)
    (rest : List (NeighborhoodScheduler.Frame tm instanceData))
    (child :
      Fin (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount))
    (initial final : Store)
    (hpost : InstallPost regs 1 initial final)
    (hfuel : initial (Layout.fuel regs) = parent.fuel)
    (hnode :
      initial (Layout.nodeCode regs) =
        FrameCodec.encodeNode
          (Representation.digitBase instanceData)
          (parent.childNode child))
    (hout :
      initial (Layout.out regs) = (parent.childTarget child).val)
    (hstack :
      FrameTransfer.RepresentsStack regs
        (Representation.digitBase instanceData)
        (Representation.frameBase instanceData)
        (parent :: rest) initial) :
    Representation.Stack regs
      (parent.prepareChild child :: parent :: rest) final :=
  ⟨prepareChild_activeFrame_internal
      regs parent child initial final hpost hfuel hnode hout,
    representsStack_of_installPost_internal
      regs (Representation.digitBase instanceData)
      (Representation.frameBase instanceData)
      (parent :: rest) initial final hpost hstack⟩

theorem cleanupChild_activeFrame_internal
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (regs : NeighborhoodTrial.Registers controller)
    (parent : NeighborhoodScheduler.Frame tm instanceData)
    (child :
      Fin (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount))
    (initial final : Store)
    (hpost :
      InstallPost regs (initial (Layout.modulusPred regs)) initial final)
    (hparameters :
      Representation.Parameters regs instanceData initial)
    (hfuel : initial (Layout.fuel regs) = parent.fuel)
    (hnode :
      initial (Layout.nodeCode regs) =
        FrameCodec.encodeNode
          (Representation.digitBase instanceData)
          (parent.childNode child))
    (hout :
      initial (Layout.out regs) = (parent.childTarget child).val) :
    Representation.ActiveFrame regs (parent.cleanupChild child) final := by
  constructor
  · simpa [NeighborhoodScheduler.Frame.cleanupChild] using
      hpost.fuel_eq.trans (congrArg (fun value => value - 1) hfuel)
  · simpa [NeighborhoodScheduler.Frame.cleanupChild] using
      hpost.nodeCode_eq.trans hnode
  · rw [hpost.scalar_eq, hparameters.modulusPred_eq]
    simp [NeighborhoodScheduler.Frame.cleanupChild,
      PrimeField.Runtime.sub, PrimeField.Runtime.subInput,
      PrimeField.Runtime.normalize,
      Nat.mod_eq_of_lt
        (NeighborhoodScheduler.FrameBounds.fieldModulus_one_lt
          instanceData)]
  · simpa [NeighborhoodScheduler.Frame.cleanupChild] using
      hpost.out_eq.trans hout
  · rw [hpost.phaseCode_eq]
    rfl
  · exact hpost.active_eq

theorem cleanupChild_stack_internal
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (regs : NeighborhoodTrial.Registers controller)
    (parent : NeighborhoodScheduler.Frame tm instanceData)
    (rest : List (NeighborhoodScheduler.Frame tm instanceData))
    (child :
      Fin (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount))
    (initial final : Store)
    (hpost :
      InstallPost regs (initial (Layout.modulusPred regs)) initial final)
    (hparameters :
      Representation.Parameters regs instanceData initial)
    (hfuel : initial (Layout.fuel regs) = parent.fuel)
    (hnode :
      initial (Layout.nodeCode regs) =
        FrameCodec.encodeNode
          (Representation.digitBase instanceData)
          (parent.childNode child))
    (hout :
      initial (Layout.out regs) = (parent.childTarget child).val)
    (hstack :
      FrameTransfer.RepresentsStack regs
        (Representation.digitBase instanceData)
        (Representation.frameBase instanceData)
        (parent :: rest) initial) :
    Representation.Stack regs
      (parent.cleanupChild child :: parent :: rest) final :=
  ⟨cleanupChild_activeFrame_internal
      regs parent child initial final hpost hparameters hfuel hnode hout,
    representsStack_of_installPost_internal
      regs (Representation.digitBase instanceData)
      (Representation.frameBase instanceData)
      (parent :: rest) initial final hpost hstack⟩

end Internal
end FrameInstall
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
