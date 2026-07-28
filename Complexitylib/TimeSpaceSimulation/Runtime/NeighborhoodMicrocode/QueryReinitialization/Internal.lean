/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.QueryReinitialization.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.Representation
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodScheduler.FrameBounds

/-!
# Reinitializing a query while retaining the catalytic bank -- proofs
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace QueryReinitialization
namespace Internal

open RAM Structured
open NeighborhoodExecutableEvaluation

variable {controller : SearchProgram.Registers}

private theorem basics_runs
    (operations : List Basic) (store : Store) :
    Runs (Cmd.basics operations) store
      (Basic.execList operations store) := by
  obtain ⟨cost, space, hexec⟩ :=
    RAM.Structured.Internal.exec_basics_exists operations store
  exact ⟨operations.length, cost, space, hexec⟩

private theorem cmdWritesWithin_mono
    {small large : Finset ℕ} {command : Cmd}
    (hwrites : Footprint.CmdWritesWithin small command)
    (hsubset : small ⊆ large) :
    Footprint.CmdWritesWithin large command := by
  induction command with
  | skip =>
      trivial
  | basic operation =>
      cases operation <;>
        simp only [Footprint.CmdWritesWithin,
          Footprint.BasicWritesWithin] at hwrites ⊢
      all_goals exact hsubset hwrites
  | seq first second ihFirst ihSecond =>
      exact ⟨ihFirst hwrites.1, ihSecond hwrites.2⟩
  | ifZero test onZero onNonzero ihZero ihNonzero =>
      exact ⟨ihZero hwrites.1, ihNonzero hwrites.2⟩
  | whileNonzero test body ih =>
      exact ih hwrites

theorem reinitialize_writesWithin_internal
    (workTapeCount : ℕ)
    (regs : NeighborhoodTrial.Registers controller)
    (out : Fin (graphFanIn workTapeCount + 1)) :
    Footprint.CmdWritesWithin regs.layout.footprint
      (reinitializeQuery workTapeCount regs out) := by
  simp only [reinitializeQuery, activeOps, Cmd.basics]
  exact
    ⟨Layout.index_mem_layout_footprint regs 32,
      Layout.index_mem_layout_footprint regs 22,
      Layout.index_mem_layout_footprint regs 22,
      Layout.index_mem_layout_footprint regs 25,
      Layout.index_mem_layout_footprint regs 26,
      Layout.index_mem_layout_footprint regs 27,
      Layout.index_mem_layout_footprint regs 28⟩

theorem reinitialize_from_bank_runs_internal
    {tm : TM workTapeCount}
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (registers :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (node :
      NeighborhoodEvaluator.QueryNode
        workTapeCount instanceData.horizon)
    (out : Fin (graphFanIn workTapeCount + 1))
    (store : Store)
    (hparameters :
      Representation.Parameters regs instanceData store)
    (hbank :
      NeighborhoodProgram.RepresentsResidueBank
        tm instanceData.blockLength
        (Representation.fieldBase instanceData)
        (store regs.layout.bank) registers)
    (hbankLt :
      store regs.layout.bank <
        Representation.fieldBase instanceData ^
          ((graphFanIn workTapeCount + 1) *
            TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
              (payloadWidth tm instanceData.blockLength)
              (graphFanIn workTapeCount)))
    (hnodeCode :
      store (Layout.nodeCode regs) =
        FrameCodec.encodeNode
          (Representation.digitBase instanceData) node)
    (hnodeBound :
      NeighborhoodScheduler.FrameBounds.QueryBound
        instanceData.horizon node) :
    ∃ final,
      Runs (reinitializeQuery workTapeCount regs out) store final ∧
      Representation.QueryState regs instanceData
        (NeighborhoodScheduler.State.initial
          instanceData.horizon node 1 out registers)
        final := by
  let final :=
    Basic.execList (activeOps workTapeCount regs out) store
  have hrun :
      Runs (reinitializeQuery workTapeCount regs out) store final := by
    simpa [reinitializeQuery] using
      basics_runs (activeOps workTapeCount regs out) store
  have hfinalPhysical (slot : Fin 34)
      (hne32 : slot ≠ 32) (hne22 : slot ≠ 22)
      (hne25 : slot ≠ 25) (hne26 : slot ≠ 26)
      (hne27 : slot ≠ 27) (hne28 : slot ≠ 28) :
      final (regs.index slot) = store (regs.index slot) := by
    simp [final, activeOps, Basic.execList, Basic.exec,
      Layout.frameStackRegisters, Layout.frameStackMap,
      Layout.fuel, Layout.horizon, Layout.scalar, Layout.out,
      Layout.phaseCode, Layout.active, regs.injective.eq_iff,
      hne32, hne22, hne25, hne26, hne27, hne28]
  have hfinalParameters :
      Representation.Parameters regs instanceData final := by
    refine
      { blockLength_eq := ?_
        horizon_eq := ?_
        digitBase_eq := ?_
        bankBase_eq := ?_
        frameBase_eq := ?_
        chunkCount_eq := ?_
        bankDigitCount_eq := ?_
        modulus_eq := ?_
        modulusPred_eq := ?_ }
    all_goals
      first
      | exact
          (hfinalPhysical _ (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide)).trans
            hparameters.blockLength_eq
      | exact
          (hfinalPhysical _ (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide)).trans
            hparameters.horizon_eq
      | exact
          (hfinalPhysical _ (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide)).trans
            hparameters.digitBase_eq
      | exact
          (hfinalPhysical _ (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide)).trans
            hparameters.bankBase_eq
      | exact
          (hfinalPhysical _ (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide)).trans
            hparameters.frameBase_eq
      | exact
          (hfinalPhysical _ (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide)).trans
            hparameters.chunkCount_eq
      | exact
          (hfinalPhysical _ (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide)).trans
            hparameters.bankDigitCount_eq
      | exact
          (hfinalPhysical _ (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide)).trans
            hparameters.modulus_eq
      | exact
          (hfinalPhysical _ (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide)).trans
            hparameters.modulusPred_eq
  refine ⟨final, hrun, ?_⟩
  refine
    { parameters := hfinalParameters
      stack := ?_
      bank := ?_
      bank_lt := ?_
      bounds := ?_ }
  · change
      Representation.ActiveFrame regs
          { fuel := instanceData.horizon
            node := node
            scalar := 1
            out := out
            phase := .enter }
          final ∧
        FrameTransfer.RepresentsStack regs
          (Representation.digitBase instanceData)
          (Representation.frameBase instanceData) [] final
    constructor
    · refine
        { fuel_eq := ?_
          node_eq := ?_
          scalar_eq := ?_
          out_eq := ?_
          phase_eq := ?_
          active_eq := ?_ }
      · simp [final, activeOps, Basic.execList, Basic.exec,
          Layout.frameStackRegisters, Layout.frameStackMap,
          Layout.fuel, Layout.horizon, Layout.scalar, Layout.out,
          Layout.phaseCode, Layout.active, regs.injective.eq_iff]
        exact hparameters.horizon_eq
      · exact
          (hfinalPhysical (23 : Fin 34) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide)).trans
            hnodeCode
      · simp [final, activeOps, Basic.execList, Basic.exec,
          Layout.frameStackRegisters, Layout.frameStackMap,
          Layout.fuel, Layout.horizon, Layout.scalar, Layout.out,
          Layout.phaseCode, Layout.active, regs.injective.eq_iff]
      · simp [final, activeOps, Basic.execList, Basic.exec,
          Layout.frameStackRegisters, Layout.frameStackMap,
          Layout.fuel, Layout.horizon, Layout.scalar, Layout.out,
          Layout.phaseCode, Layout.active, regs.injective.eq_iff]
      · simp [final, activeOps, Basic.execList, Basic.exec,
          Layout.frameStackRegisters, Layout.frameStackMap,
          Layout.fuel, Layout.horizon, Layout.scalar, Layout.out,
          Layout.phaseCode, Layout.active, regs.injective.eq_iff,
          FrameCodec.encodePhase, FrameCodec.phaseDigits,
          FrameCodec.encodeList, PackedDigits.push]
      · simp [final, activeOps, Basic.execList, Basic.exec,
          Layout.frameStackRegisters, Layout.frameStackMap,
          Layout.fuel, Layout.horizon, Layout.scalar, Layout.out,
          Layout.phaseCode, Layout.active, regs.injective.eq_iff]
    · simp [FrameTransfer.RepresentsStack,
        FrameTransfer.encodeStack, final, activeOps,
        Basic.execList, Basic.exec, Layout.frameStackRegisters,
        Layout.frameStackMap, Layout.fuel, Layout.horizon,
        Layout.scalar, Layout.out, Layout.phaseCode, Layout.active,
        regs.injective.eq_iff]
  · change
      NeighborhoodProgram.RepresentsResidueBank
        tm instanceData.blockLength
        (Representation.fieldBase instanceData)
        (final (regs.index 33)) registers
    rw [hfinalPhysical (33 : Fin 34) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)]
    exact hbank
  · change
      final (regs.index 33) <
        Representation.fieldBase instanceData ^
          ((graphFanIn workTapeCount + 1) *
            TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
              (payloadWidth tm instanceData.blockLength)
              (graphFanIn workTapeCount))
    rw [hfinalPhysical (33 : Fin 34) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)]
    exact hbankLt
  · apply NeighborhoodScheduler.FrameBounds.stateBound_initial
    · exact Nat.le_refl _
    · exact hnodeBound
    · exact
        NeighborhoodScheduler.FrameBounds.fieldModulus_one_lt
          instanceData

theorem reinitialize_runs_internal
    {tm : TM workTapeCount}
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (state : NeighborhoodScheduler.State tm instanceData)
    (node :
      NeighborhoodEvaluator.QueryNode
        workTapeCount instanceData.horizon)
    (out : Fin (graphFanIn workTapeCount + 1))
    (store : Store)
    (hquery :
      Representation.QueryState regs instanceData state store)
    (hnodeCode :
      store (Layout.nodeCode regs) =
        FrameCodec.encodeNode
          (Representation.digitBase instanceData) node)
    (hnodeBound :
      NeighborhoodScheduler.FrameBounds.QueryBound
        instanceData.horizon node) :
    ∃ final,
      Runs (reinitializeQuery workTapeCount regs out) store final ∧
      Representation.QueryState regs instanceData
        (NeighborhoodScheduler.State.initial
          instanceData.horizon node 1 out state.registers)
        final :=
  reinitialize_from_bank_runs_internal
    regs instanceData state.registers node out store
    hquery.parameters hquery.bank hquery.bank_lt hnodeCode hnodeBound

theorem reinitialize_from_bank_runs_preserving_abi_internal
    {tm : TM workTapeCount}
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (registers :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (node :
      NeighborhoodEvaluator.QueryNode
        workTapeCount instanceData.horizon)
    (out : Fin (graphFanIn workTapeCount + 1))
    (word : ℕ)
    (store : Store)
    (hparameters :
      Representation.Parameters regs instanceData store)
    (hbank :
      NeighborhoodProgram.RepresentsResidueBank
        tm instanceData.blockLength
        (Representation.fieldBase instanceData)
        (store regs.layout.bank) registers)
    (hbankLt :
      store regs.layout.bank <
        Representation.fieldBase instanceData ^
          ((graphFanIn workTapeCount + 1) *
            TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
              (payloadWidth tm instanceData.blockLength)
              (graphFanIn workTapeCount)))
    (hnodeCode :
      store (Layout.nodeCode regs) =
        FrameCodec.encodeNode
          (Representation.digitBase instanceData) node)
    (hnodeBound :
      NeighborhoodScheduler.FrameBounds.QueryBound
        instanceData.horizon node)
    (hframe :
      SearchProgram.InputFrame
        controller regs.footprint instanceData.x store)
    (hinputLength :
      store controller.inputLength = instanceData.x.length)
    (hone : store controller.one = 1)
    (hguess : store controller.guess = word) :
    ∃ final,
      Runs (reinitializeQuery workTapeCount regs out) store final ∧
      Representation.QueryState regs instanceData
        (NeighborhoodScheduler.State.initial
          instanceData.horizon node 1 out registers)
        final ∧
      SearchProgram.InputFrame
        controller regs.footprint instanceData.x final ∧
      final controller.inputLength = instanceData.x.length ∧
      final controller.one = 1 ∧
      final controller.guess = word := by
  obtain ⟨final, hrun, hqueryFinal⟩ :=
    reinitialize_from_bank_runs_internal
      regs instanceData registers node out store
      hparameters hbank hbankLt hnodeCode hnodeBound
  have hwrites :
      Footprint.CmdWritesWithin regs.footprint
        (reinitializeQuery workTapeCount regs out) :=
    cmdWritesWithin_mono
      (reinitialize_writesWithin_internal workTapeCount regs out)
      (fun address haddress =>
        Finset.mem_union_left _ haddress)
  have hinputLengthFinal :
      final controller.inputLength =
        store controller.inputLength :=
    NeighborhoodTrial.Registers.runs_preserves_controller_index
      regs hwrites hrun (0 : Fin 17)
      (by decide) (by decide) (by decide)
  have honeFinal :
      final controller.one = store controller.one := by
    simpa [SearchProgram.Registers.one,
      SearchProgram.Registers.primeRegisters,
      SearchProgram.Registers.primeSlot] using
        NeighborhoodTrial.Registers.runs_preserves_controller_index
          regs hwrites hrun (14 : Fin 17)
          (by decide) (by decide) (by decide)
  have hguessFinal :
      final controller.guess = store controller.guess :=
    NeighborhoodTrial.Registers.runs_preserves_controller_index
      regs hwrites hrun (2 : Fin 17)
      (by decide) (by decide) (by decide)
  exact
    ⟨final, hrun, hqueryFinal,
      NeighborhoodTrial.Registers.runs_preserves_inputFrame
        regs hwrites hrun hframe,
      hinputLengthFinal.trans hinputLength,
      honeFinal.trans hone,
      hguessFinal.trans hguess⟩

theorem reinitialize_runs_preserving_abi_internal
    {tm : TM workTapeCount}
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (state : NeighborhoodScheduler.State tm instanceData)
    (node :
      NeighborhoodEvaluator.QueryNode
        workTapeCount instanceData.horizon)
    (out : Fin (graphFanIn workTapeCount + 1))
    (word : ℕ)
    (store : Store)
    (hquery :
      Representation.QueryState regs instanceData state store)
    (hnodeCode :
      store (Layout.nodeCode regs) =
        FrameCodec.encodeNode
          (Representation.digitBase instanceData) node)
    (hnodeBound :
      NeighborhoodScheduler.FrameBounds.QueryBound
        instanceData.horizon node)
    (hframe :
      SearchProgram.InputFrame
        controller regs.footprint instanceData.x store)
    (hinputLength :
      store controller.inputLength = instanceData.x.length)
    (hone : store controller.one = 1)
    (hguess : store controller.guess = word) :
    ∃ final,
      Runs (reinitializeQuery workTapeCount regs out) store final ∧
      Representation.QueryState regs instanceData
        (NeighborhoodScheduler.State.initial
          instanceData.horizon node 1 out state.registers)
        final ∧
      SearchProgram.InputFrame
        controller regs.footprint instanceData.x final ∧
      final controller.inputLength = instanceData.x.length ∧
      final controller.one = 1 ∧
      final controller.guess = word :=
  reinitialize_from_bank_runs_preserving_abi_internal
    controller regs instanceData state.registers node out word store
    hquery.parameters hquery.bank hquery.bank_lt hnodeCode hnodeBound
    hframe hinputLength hone hguess

end Internal
end QueryReinitialization
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
