/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.ChildNode
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.QueryInitialization
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.StateRootInitialization.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodScheduler.FrameBounds

/-!
# Uniform initialization of the state-consistency root -- proofs
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace StateRootInitialization
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
  | basic op =>
      cases op <;>
        simp only [Footprint.CmdWritesWithin,
          Footprint.BasicWritesWithin] at hwrites ⊢
      all_goals exact hsubset hwrites
  | seq first second ihFirst ihSecond =>
      exact ⟨ihFirst hwrites.1, ihSecond hwrites.2⟩
  | ifZero test onZero onNonzero ihZero ihNonzero =>
      exact ⟨ihZero hwrites.1, ihNonzero hwrites.2⟩
  | whileNonzero test body ih =>
      exact ih hwrites

theorem buildStateRoot_writesWithin_internal
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (rootFootprint regs)
      (buildStateRoot controller regs) := by
  simp [buildStateRoot, sourceFields, computationFields,
    ChildNode.encodeNodeFields, ChildNode.encodeNodeFieldsOps,
    rootFootprint, Cmd.basics, Cmd.seqList,
    Footprint.CmdWritesWithin, Footprint.BasicWritesWithin]

theorem rootFootprint_subset_layout_internal
    (regs : NeighborhoodTrial.Registers controller) :
    rootFootprint regs ⊆ regs.layout.footprint := by
  intro address haddress
  simp only [rootFootprint, Finset.mem_insert,
    Finset.mem_singleton] at haddress
  rcases haddress with rfl | rfl | rfl | rfl | rfl
  all_goals exact Layout.index_mem_layout_footprint regs _

theorem initializeStateQuery_writesWithin_internal
    (workTapeCount : ℕ)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin regs.layout.footprint
      (initializeStateQuery workTapeCount controller regs) := by
  exact
    ⟨cmdWritesWithin_mono
        (buildStateRoot_writesWithin_internal controller regs)
        (rootFootprint_subset_layout_internal regs),
      QueryInitialization.initialize_writesWithin workTapeCount regs⟩

private theorem parameters_of_buildStateRoot_run
    {tm : TM workTapeCount}
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (initial final : Store)
    (hparameters :
      Representation.Parameters regs instanceData initial)
    (hrun : Runs (buildStateRoot controller regs) initial final) :
    Representation.Parameters regs instanceData final := by
  have hphysical (slot : Fin 34)
      (hne9 : slot ≠ 9) (hne10 : slot ≠ 10)
      (hne11 : slot ≠ 11) (hne23 : slot ≠ 23)
      (hne30 : slot ≠ 30) :
      final (regs.index slot) = initial (regs.index slot) := by
    apply Footprint.runs_eq_outside
      (buildStateRoot_writesWithin_internal controller regs) hrun
    simp [rootFootprint, ControlDecode.nodeTape,
      ControlDecode.nodePayload0, ControlDecode.nodePayload1,
      ControlDecode.first, ControlDecode.second, ControlDecode.third,
      Layout.nodeCode, Layout.codecDigit, regs.injective.eq_iff,
      hne9, hne10, hne11, hne23, hne30]
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
        (hphysical _ (by decide) (by decide) (by decide)
          (by decide) (by decide)).trans hparameters.blockLength_eq
    | exact
        (hphysical _ (by decide) (by decide) (by decide)
          (by decide) (by decide)).trans hparameters.horizon_eq
    | exact
        (hphysical _ (by decide) (by decide) (by decide)
          (by decide) (by decide)).trans hparameters.digitBase_eq
    | exact
        (hphysical _ (by decide) (by decide) (by decide)
          (by decide) (by decide)).trans hparameters.bankBase_eq
    | exact
        (hphysical _ (by decide) (by decide) (by decide)
          (by decide) (by decide)).trans hparameters.frameBase_eq
    | exact
        (hphysical _ (by decide) (by decide) (by decide)
          (by decide) (by decide)).trans hparameters.chunkCount_eq
    | exact
        (hphysical _ (by decide) (by decide) (by decide)
          (by decide) (by decide)).trans hparameters.bankDigitCount_eq
    | exact
        (hphysical _ (by decide) (by decide) (by decide)
          (by decide) (by decide)).trans hparameters.modulus_eq
    | exact
        (hphysical _ (by decide) (by decide) (by decide)
          (by decide) (by decide)).trans hparameters.modulusPred_eq

private theorem one_of_buildStateRoot_run
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (initial final : Store)
    (hrun : Runs (buildStateRoot controller regs) initial final) :
    final controller.one = initial controller.one := by
  have hwrites :
      Footprint.CmdWritesWithin regs.footprint
        (buildStateRoot controller regs) :=
    cmdWritesWithin_mono
      (buildStateRoot_writesWithin_internal controller regs)
      (fun address haddress =>
        Finset.mem_union_left _
          (rootFootprint_subset_layout_internal regs haddress))
  simpa [SearchProgram.Registers.one,
    SearchProgram.Registers.primeRegisters,
    SearchProgram.Registers.primeSlot] using
      NeighborhoodTrial.Registers.runs_preserves_controller_index
        regs hwrites hrun (14 : Fin 17)
        (by decide) (by decide) (by decide)

private theorem stateRoot_eq_source_of_horizon_eq_zero
    {horizon : ℕ}
    (guess :
      NeighborhoodGraph.Guess.CenterGuess workTapeCount horizon)
    (hhorizon : horizon = 0)
    (hinitial :
      guess.initialCenter (TapeIndex.input workTapeCount) = 0) :
    NeighborhoodEvaluator.stateRoot guess =
      .graph
        (.source (TapeIndex.input workTapeCount) 0) := by
  subst horizon
  simpa [NeighborhoodEvaluator.stateRoot] using hinitial

private theorem stateRoot_eq_computation_of_horizon_eq_succ
    {horizon : ℕ}
    (guess :
      NeighborhoodGraph.Guess.CenterGuess workTapeCount horizon)
    (previous : ℕ)
    (hhorizon : horizon = previous + 1) :
    NeighborhoodEvaluator.stateRoot guess =
      .graph
        (.computation
          (TapeIndex.input workTapeCount)
          .center previous) := by
  subst horizon
  rfl

theorem buildStateRoot_runs_internal
    {tm : TM workTapeCount}
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (store : Store)
    (hparameters :
      Representation.Parameters regs instanceData store)
    (hone : store controller.one = 1) :
    ∃ final,
      Runs (buildStateRoot controller regs) store final ∧
      Representation.Parameters regs instanceData final ∧
      final (Layout.nodeCode regs) =
        FrameCodec.encodeNode
          (Representation.digitBase instanceData)
          (NeighborhoodEvaluator.stateRoot instanceData.guess) ∧
      final controller.one = 1 := by
  by_cases hhorizon : instanceData.horizon = 0
  ·
      let operations : List Basic :=
        [.imm (ControlDecode.nodeTape regs) 0,
          .imm (ControlDecode.nodePayload0 regs) 0,
          .imm (ControlDecode.nodePayload1 regs) 0]
      let prepared := Basic.execList operations store
      have hfields :
          Runs (sourceFields regs) store prepared := by
        simpa [sourceFields, operations] using
          basics_runs operations store
      obtain ⟨final, hencode, hpost⟩ :=
        ChildNode.encodeNodeFields_runs regs 1 prepared
      have htest : store (Layout.horizon regs) = 0 := by
        rw [hparameters.horizon_eq, hhorizon]
      have hrun :
          Runs (buildStateRoot controller regs) store final := by
        simpa [buildStateRoot] using
          Runs.ifZero htest (Runs.seq hfields hencode)
      refine
        ⟨final, hrun,
          parameters_of_buildStateRoot_run
            controller regs instanceData store final
            hparameters hrun, ?_,
          (one_of_buildStateRoot_run
            controller regs store final hrun).trans hone⟩
      rw [hpost.nodeCode_eq]
      have hinitial :=
        NeighborhoodProgram.InstanceBounds.guess_initialCenter_eq_zero
          instanceData (TapeIndex.input workTapeCount)
      rw [stateRoot_eq_source_of_horizon_eq_zero
        instanceData.guess hhorizon hinitial]
      simp [prepared, operations, Basic.execList, Basic.exec,
        ChildNode.nodeFieldValue,
        FrameCodec.encodeNode, FrameCodec.nodeDigits,
        FrameCodec.encodeList, PackedDigits.push,
        Layout.chunkRadix, TapeIndex.input, ControlDecode.nodeTape,
        ControlDecode.nodePayload0, ControlDecode.nodePayload1,
        ControlDecode.first, ControlDecode.second, ControlDecode.third,
        regs.injective.eq_iff, hparameters.digitBase_eq]
  ·
      obtain ⟨previous, hprevious⟩ :=
        Nat.exists_eq_succ_of_ne_zero hhorizon
      let operations : List Basic :=
        [.imm (ControlDecode.nodeTape regs) 0,
          .imm (ControlDecode.nodePayload0 regs)
            NeighborhoodGraph.Slot.center.toFin.val,
          .sub (ControlDecode.nodePayload1 regs)
            (Layout.horizon regs) controller.one]
      let prepared := Basic.execList operations store
      have hfields :
          Runs (computationFields controller regs) store prepared := by
        simpa [computationFields, operations] using
          basics_runs operations store
      obtain ⟨final, hencode, hpost⟩ :=
        ChildNode.encodeNodeFields_runs regs 2 prepared
      have htest : store (Layout.horizon regs) ≠ 0 := by
        rw [hparameters.horizon_eq]
        omega
      have hrun :
          Runs (buildStateRoot controller regs) store final := by
        simpa [buildStateRoot] using
          Runs.ifNonzero htest (Runs.seq hfields hencode)
      refine
        ⟨final, hrun,
          parameters_of_buildStateRoot_run
            controller regs instanceData store final
            hparameters hrun, ?_,
          (one_of_buildStateRoot_run
            controller regs store final hrun).trans hone⟩
      rw [hpost.nodeCode_eq]
      rw [stateRoot_eq_computation_of_horizon_eq_succ
        instanceData.guess previous hprevious]
      have hone' : store (controller.index 14) = 1 := by
        simpa [SearchProgram.Registers.one,
          SearchProgram.Registers.primeRegisters,
          SearchProgram.Registers.primeSlot,
          PrimeSearch.Registers.one] using hone
      have h9one :
          regs.index 9 ≠ controller.index 14 :=
        regs.index_ne_controller 9 14
      have h10one :
          regs.index 10 ≠ controller.index 14 :=
        regs.index_ne_controller 10 14
      simp [prepared, operations, Basic.execList, Basic.exec,
        ChildNode.nodeFieldValue,
        FrameCodec.encodeNode, FrameCodec.nodeDigits,
        FrameCodec.encodeList, PackedDigits.push,
        Layout.chunkRadix, Layout.horizon, TapeIndex.input,
        ControlDecode.nodeTape, ControlDecode.nodePayload0,
        ControlDecode.nodePayload1, ControlDecode.first,
        ControlDecode.second, ControlDecode.third,
        SearchProgram.Registers.one,
        SearchProgram.Registers.primeRegisters,
        SearchProgram.Registers.primeSlot,
        PrimeSearch.Registers.one,
        regs.injective.eq_iff, h9one.symm, h10one.symm,
        hparameters.digitBase_eq, hparameters.horizon_eq,
        hprevious, hone']

theorem initializeStateQuery_runs_internal
    {tm : TM workTapeCount}
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (store : Store)
    (hparameters :
      Representation.Parameters regs instanceData store)
    (hone : store controller.one = 1) :
    ∃ final,
      Runs
        (initializeStateQuery workTapeCount controller regs)
        store final ∧
      Representation.QueryState regs instanceData
        (NeighborhoodScheduler.Decision.queryInitial
          (NeighborhoodEvaluator.stateRoot instanceData.guess))
        final ∧
      final controller.one = 1 := by
  obtain
      ⟨rooted, hrootRun, hrootParameters, hrootCode, _hrootOne⟩ :=
    buildStateRoot_runs_internal
      controller regs instanceData store hparameters hone
  obtain ⟨final, hinitializeRun, hquery⟩ :=
    QueryInitialization.initialize_runs
      regs instanceData
      (NeighborhoodEvaluator.stateRoot instanceData.guess)
      rooted hrootParameters hrootCode
      (NeighborhoodScheduler.FrameBounds.queryBound_stateRoot
        instanceData)
  have hrun :
      Runs
        (initializeStateQuery workTapeCount controller regs)
        store final := by
    simpa [initializeStateQuery] using
      Runs.seq hrootRun hinitializeRun
  have hmodulus :
      1 < NeighborhoodScheduler.fieldModulus instanceData :=
    NeighborhoodScheduler.FrameBounds.fieldModulus_one_lt
      instanceData
  have hnormalize :
      TreeEval.CookMertz.PrimeField.Runtime.normalize
        (NeighborhoodScheduler.fieldModulus instanceData) 1 = 1 := by
    simp [TreeEval.CookMertz.PrimeField.Runtime.normalize,
      Nat.mod_eq_of_lt hmodulus]
  have hzero :
      NeighborhoodScheduler.Decision.zeroRegisters =
        ResidueBankOps.zeroRegisters tm instanceData.blockLength := by
    funext register chunk
    simp [NeighborhoodScheduler.Decision.zeroRegisters,
      ResidueBankOps.zeroRegisters,
      NeighborhoodExecutableEvaluation.Residue.zeroValue,
      TreeEval.CookMertz.PrimeField.Runtime.normalize]
  have hwrites :
      Footprint.CmdWritesWithin regs.footprint
        (initializeStateQuery workTapeCount controller regs) :=
    cmdWritesWithin_mono
      (initializeStateQuery_writesWithin_internal
        workTapeCount controller regs)
      (fun address haddress =>
        Finset.mem_union_left _ haddress)
  have honeFinal : final controller.one = store controller.one := by
    simpa [SearchProgram.Registers.one,
      SearchProgram.Registers.primeRegisters,
      SearchProgram.Registers.primeSlot,
      PrimeSearch.Registers.one] using
        NeighborhoodTrial.Registers.runs_preserves_controller_index
          regs hwrites hrun (14 : Fin 17)
          (by decide) (by decide) (by decide)
  refine ⟨final, hrun, ?_, honeFinal.trans hone⟩
  simpa [NeighborhoodScheduler.Decision.queryInitial,
    hnormalize, hzero] using hquery

theorem initializeStateQuery_runs_preserving_abi_internal
    {tm : TM workTapeCount}
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (word : ℕ)
    (store : Store)
    (hparameters :
      Representation.Parameters regs instanceData store)
    (hone : store controller.one = 1)
    (hframe :
      SearchProgram.InputFrame
        controller regs.footprint instanceData.x store)
    (hinputLength :
      store controller.inputLength = instanceData.x.length)
    (hguess : store controller.guess = word) :
    ∃ final,
      Runs
        (initializeStateQuery workTapeCount controller regs)
        store final ∧
      Representation.QueryState regs instanceData
        (NeighborhoodScheduler.Decision.queryInitial
          (NeighborhoodEvaluator.stateRoot instanceData.guess))
        final ∧
      SearchProgram.InputFrame
        controller regs.footprint instanceData.x final ∧
      final controller.inputLength = instanceData.x.length ∧
      final controller.one = 1 ∧
      final controller.guess = word := by
  obtain ⟨final, hrun, hquery, honeFinal⟩ :=
    initializeStateQuery_runs_internal
      controller regs instanceData store hparameters hone
  have hwrites :
      Footprint.CmdWritesWithin regs.footprint
        (initializeStateQuery workTapeCount controller regs) :=
    cmdWritesWithin_mono
      (initializeStateQuery_writesWithin_internal
        workTapeCount controller regs)
      (fun address haddress =>
        Finset.mem_union_left _ haddress)
  have hframeFinal :
      SearchProgram.InputFrame
        controller regs.footprint instanceData.x final :=
    NeighborhoodTrial.Registers.runs_preserves_inputFrame
      regs hwrites hrun hframe
  have hinputLengthFinal :
      final controller.inputLength =
        store controller.inputLength := by
    exact
      NeighborhoodTrial.Registers.runs_preserves_controller_index
        regs hwrites hrun (0 : Fin 17)
        (by decide) (by decide) (by decide)
  have hguessFinal :
      final controller.guess = store controller.guess := by
    exact
      NeighborhoodTrial.Registers.runs_preserves_controller_index
        regs hwrites hrun (2 : Fin 17)
        (by decide) (by decide) (by decide)
  exact
    ⟨final, hrun, hquery, hframeFinal,
      hinputLengthFinal.trans hinputLength,
      honeFinal, hguessFinal.trans hguess⟩

end Internal
end StateRootInitialization
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
