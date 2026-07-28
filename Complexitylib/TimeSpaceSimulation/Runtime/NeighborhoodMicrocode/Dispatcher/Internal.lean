/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.Dispatcher.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.ControlDecode
import Complexitylib.Models.RandomAccessMachine.Structured.Footprint
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.Representation
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodTrial

/-!
# Concrete control fragments for neighborhood-scheduler dispatch -- proofs
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace Dispatcher
namespace Internal

open RAM Structured

variable {controller : SearchProgram.Registers}

private theorem switch_writesWithin
    {allowed : Finset ℕ} {count test one : ℕ}
    (branch : Fin count → Cmd)
    (htest : test ∈ allowed)
    (hbranch : ∀ index,
      Footprint.CmdWritesWithin allowed (branch index)) :
    Footprint.CmdWritesWithin allowed
      (RAM.Structured.Switch.select count test one branch) := by
  induction count with
  | zero =>
      trivial
  | succ count ih =>
      simp only [RAM.Structured.Switch.select,
        Footprint.CmdWritesWithin]
      refine ⟨hbranch ⟨0, by omega⟩, ?_, ih
        (fun index => branch index.succ)
        (fun index => hbranch index.succ)⟩
      simpa [Footprint.BasicWritesWithin] using htest

theorem dispatchPhase_writesWithin_internal
    (regs : NeighborhoodTrial.Registers controller)
    (enter prepare combine cleanupCall cleanupScale : Cmd)
    (henter : Footprint.CmdWritesWithin regs.layout.footprint enter)
    (hprepare : Footprint.CmdWritesWithin regs.layout.footprint prepare)
    (hcombine : Footprint.CmdWritesWithin regs.layout.footprint combine)
    (hcleanupCall :
      Footprint.CmdWritesWithin regs.layout.footprint cleanupCall)
    (hcleanupScale :
      Footprint.CmdWritesWithin regs.layout.footprint cleanupScale) :
    Footprint.CmdWritesWithin regs.layout.footprint
      (dispatchPhase regs enter prepare combine cleanupCall cleanupScale) := by
  apply switch_writesWithin
  · exact Layout.index_mem_layout_footprint regs 6
  · intro index
    fin_cases index <;>
      simp [phaseBranches, *]

theorem dispatchPhase_runs_internal
    (regs : NeighborhoodTrial.Registers controller)
    (enter prepare combine cleanupCall cleanupScale : Cmd)
    (store final : Store) (phase : NeighborhoodScheduler.Phase workTapeCount)
    (hdecoded : ControlDecode.EncodedPhasePost regs phase store)
    (hone : store controller.one = 1)
    (hbranch :
      Runs
        (phaseBranches enter prepare combine cleanupCall cleanupScale
          ⟨(ControlDecode.expectedPhaseValues phase).tag, by
            cases phase <;>
              simp [ControlDecode.expectedPhaseValues]⟩)
        (RAM.Structured.Switch.cleared store (ControlDecode.tag regs))
        final) :
    Runs
      (dispatchPhase regs enter prepare combine cleanupCall cleanupScale)
      store final := by
  obtain ⟨branchSteps, branchCost, branchSpace, hbranchExec⟩ := hbranch
  obtain ⟨cost, space, hexec⟩ :=
    RAM.Structured.Switch.select_exec
      (phaseBranches enter prepare combine cleanupCall cleanupScale)
      store final
      (by cases phase <;>
        simp [ControlDecode.expectedPhaseValues])
      hdecoded.tag_eq hone
      (by
        change regs.index 6 ≠ controller.index 14
        exact regs.index_ne_controller 6 14)
      ⟨branchCost, branchSpace, hbranchExec⟩
  exact ⟨_, cost, space, hexec⟩

theorem decodeAndDispatch_writesWithin_internal
    (regs : NeighborhoodTrial.Registers controller)
    (enter prepare combine cleanupCall cleanupScale : Cmd)
    (henter : Footprint.CmdWritesWithin regs.layout.footprint enter)
    (hprepare : Footprint.CmdWritesWithin regs.layout.footprint prepare)
    (hcombine : Footprint.CmdWritesWithin regs.layout.footprint combine)
    (hcleanupCall :
      Footprint.CmdWritesWithin regs.layout.footprint cleanupCall)
    (hcleanupScale :
      Footprint.CmdWritesWithin regs.layout.footprint cleanupScale) :
    Footprint.CmdWritesWithin regs.layout.footprint
      (decodeAndDispatch regs
        enter prepare combine cleanupCall cleanupScale) :=
  ⟨ControlDecode.decodePhase_layout_writesWithin regs,
    dispatchPhase_writesWithin_internal regs
      enter prepare combine cleanupCall cleanupScale
      henter hprepare hcombine hcleanupCall hcleanupScale⟩

theorem decodeAndDispatch_runs_internal
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (regs : NeighborhoodTrial.Registers controller)
    (enter prepare combine cleanupCall cleanupScale : Cmd)
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (store : Store)
    (post : Store → Prop)
    (hactive : Representation.ActiveFrame regs frame store)
    (hparameters : Representation.Parameters regs instanceData store)
    (hbound :
      NeighborhoodScheduler.FrameBounds.FrameBound frame)
    (hone : store controller.one = 1)
    (hbranch : ∀ middle,
      ControlDecode.EncodedPhasePost regs frame.phase middle →
      Representation.ActiveFrame regs frame middle →
      Representation.Parameters regs instanceData middle →
      ∃ final,
        Runs
          (phaseBranches enter prepare combine cleanupCall cleanupScale
            ⟨(ControlDecode.expectedPhaseValues frame.phase).tag, by
              cases frame.phase <;>
                simp [ControlDecode.expectedPhaseValues]⟩)
          (RAM.Structured.Switch.cleared middle
            (ControlDecode.tag regs))
          final ∧
        post final) :
    ∃ final,
      Runs
        (decodeAndDispatch regs
          enter prepare combine cleanupCall cleanupScale)
        store final ∧
      post final := by
  obtain ⟨middle, hdecode, hdecoded, hactiveMiddle,
      hparametersMiddle⟩ :=
    Representation.ActiveFrame.decodePhase_runs
      regs frame store hactive hparameters hbound
  obtain ⟨final, hbranchRun, hpost⟩ :=
    hbranch middle hdecoded hactiveMiddle hparametersMiddle
  have honeMiddle : middle controller.one = 1 := by
    rw [Footprint.runs_eq_outside
      (ControlDecode.decodePhase_layout_writesWithin regs)
      hdecode]
    · exact hone
    · intro honeMem
      exact NeighborhoodTrial.Registers.one_not_mem_footprint regs
        (Finset.mem_union_left _ honeMem)
  have hdispatch :=
    dispatchPhase_runs_internal regs
      enter prepare combine cleanupCall cleanupScale
      middle final frame.phase hdecoded honeMiddle hbranchRun
  exact ⟨final, Runs.seq hdecode hdispatch, hpost⟩

theorem decodeAndDispatchQuery_runs_internal
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (regs : NeighborhoodTrial.Registers controller)
    (enter prepare combine cleanupCall cleanupScale : Cmd)
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (rest : List (NeighborhoodScheduler.Frame tm instanceData))
    (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (store : Store)
    (post : Store → Prop)
    (hquery :
      Representation.QueryState regs instanceData
        { stack := frame :: rest
          registers := logicalBank }
        store)
    (hone : store controller.one = 1)
    (hbranch : ∀ middle,
      ControlDecode.EncodedPhasePost regs frame.phase middle →
      Representation.QueryState regs instanceData
        { stack := frame :: rest
          registers := logicalBank }
        middle →
      ∃ final,
        Runs
          (phaseBranches enter prepare combine cleanupCall cleanupScale
            ⟨(ControlDecode.expectedPhaseValues frame.phase).tag, by
              cases frame.phase <;>
                simp [ControlDecode.expectedPhaseValues]⟩)
          (RAM.Structured.Switch.cleared middle
            (ControlDecode.tag regs))
          final ∧
        post final) :
    ∃ final,
      Runs
        (decodeAndDispatch regs
          enter prepare combine cleanupCall cleanupScale)
        store final ∧
      post final := by
  obtain ⟨middle, hdecode, hdecoded, hqueryMiddle⟩ :=
    Representation.QueryState.decodePhase_runs
      regs frame rest logicalBank store hquery
  obtain ⟨final, hbranchRun, hpost⟩ :=
    hbranch middle hdecoded hqueryMiddle
  have honeMiddle : middle controller.one = 1 := by
    rw [Footprint.runs_eq_outside
      (ControlDecode.decodePhase_layout_writesWithin regs)
      hdecode]
    · exact hone
    · intro honeMem
      exact NeighborhoodTrial.Registers.one_not_mem_footprint regs
        (Finset.mem_union_left _ honeMem)
  have hdispatch :=
    dispatchPhase_runs_internal regs
      enter prepare combine cleanupCall cleanupScale
      middle final frame.phase hdecoded honeMiddle hbranchRun
  exact ⟨final, Runs.seq hdecode hdispatch, hpost⟩

theorem dispatchNode_writesWithin_internal
    (regs : NeighborhoodTrial.Registers controller)
    (failure source computation : Cmd)
    (hfailure :
      Footprint.CmdWritesWithin regs.layout.footprint failure)
    (hsource :
      Footprint.CmdWritesWithin regs.layout.footprint source)
    (hcomputation :
      Footprint.CmdWritesWithin regs.layout.footprint computation) :
    Footprint.CmdWritesWithin regs.layout.footprint
      (dispatchNode regs failure source computation) := by
  apply switch_writesWithin
  · exact Layout.index_mem_layout_footprint regs 6
  · intro index
    fin_cases index <;>
      simp [nodeBranches, *]

theorem dispatchNode_runs_internal
    (regs : NeighborhoodTrial.Registers controller)
    (failure source computation : Cmd)
    (store final : Store)
    (node :
      NeighborhoodEvaluator.QueryNode workTapeCount horizon)
    (hdecoded : ControlDecode.EncodedNodePost regs node store)
    (hone : store controller.one = 1)
    (hbranch :
      Runs
        (nodeBranches failure source computation
          ⟨(ControlDecode.expectedNodeValues node).tag, by
            cases node with
            | failure =>
                simp [ControlDecode.expectedNodeValues]
            | graph graphNode =>
                cases graphNode <;>
                  simp [ControlDecode.expectedNodeValues]⟩)
        (RAM.Structured.Switch.cleared store (ControlDecode.tag regs))
        final) :
    Runs
      (dispatchNode regs failure source computation)
      store final := by
  obtain ⟨branchSteps, branchCost, branchSpace, hbranchExec⟩ := hbranch
  obtain ⟨cost, space, hexec⟩ :=
    RAM.Structured.Switch.select_exec
      (nodeBranches failure source computation)
      store final
      (by
        cases node with
        | failure =>
            simp [ControlDecode.expectedNodeValues]
        | graph graphNode =>
            cases graphNode <;>
              simp [ControlDecode.expectedNodeValues])
      hdecoded.tag_eq hone
      (by
        change regs.index 6 ≠ controller.index 14
        exact regs.index_ne_controller 6 14)
      ⟨branchCost, branchSpace, hbranchExec⟩
  exact ⟨_, cost, space, hexec⟩

theorem decodeAndDispatchNode_writesWithin_internal
    (regs : NeighborhoodTrial.Registers controller)
    (failure source computation : Cmd)
    (hfailure :
      Footprint.CmdWritesWithin regs.layout.footprint failure)
    (hsource :
      Footprint.CmdWritesWithin regs.layout.footprint source)
    (hcomputation :
      Footprint.CmdWritesWithin regs.layout.footprint computation) :
    Footprint.CmdWritesWithin regs.layout.footprint
      (decodeAndDispatchNode regs failure source computation) :=
  ⟨ControlDecode.decodeNode_layout_writesWithin regs,
    dispatchNode_writesWithin_internal regs
      failure source computation hfailure hsource hcomputation⟩

theorem decodeAndDispatchNode_runs_internal
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (regs : NeighborhoodTrial.Registers controller)
    (failure source computation : Cmd)
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (store : Store)
    (post : Store → Prop)
    (hactive : Representation.ActiveFrame regs frame store)
    (hparameters : Representation.Parameters regs instanceData store)
    (hbound :
      NeighborhoodScheduler.FrameBounds.FrameBound frame)
    (hone : store controller.one = 1)
    (hbranch : ∀ middle,
      ControlDecode.EncodedNodePost regs frame.node middle →
      Representation.ActiveFrame regs frame middle →
      Representation.Parameters regs instanceData middle →
      ∃ final,
        Runs
          (nodeBranches failure source computation
            ⟨(ControlDecode.expectedNodeValues frame.node).tag, by
              cases frame.node with
              | failure =>
                  simp [ControlDecode.expectedNodeValues]
              | graph graphNode =>
                  cases graphNode <;>
                    simp [ControlDecode.expectedNodeValues]⟩)
          (RAM.Structured.Switch.cleared middle
            (ControlDecode.tag regs))
          final ∧
        post final) :
    ∃ final,
      Runs
        (decodeAndDispatchNode regs failure source computation)
        store final ∧
      post final := by
  obtain ⟨middle, hdecode, hdecoded, hactiveMiddle,
      hparametersMiddle⟩ :=
    Representation.ActiveFrame.decodeNode_runs
      regs frame store hactive hparameters hbound
  obtain ⟨final, hbranchRun, hpost⟩ :=
    hbranch middle hdecoded hactiveMiddle hparametersMiddle
  have honeMiddle : middle controller.one = 1 := by
    rw [Footprint.runs_eq_outside
      (ControlDecode.decodeNode_layout_writesWithin regs)
      hdecode]
    · exact hone
    · intro honeMem
      exact NeighborhoodTrial.Registers.one_not_mem_footprint regs
        (Finset.mem_union_left _ honeMem)
  have hdispatch :=
    dispatchNode_runs_internal regs failure source computation
      middle final frame.node hdecoded honeMiddle hbranchRun
  exact ⟨final, Runs.seq hdecode hdispatch, hpost⟩

theorem decodeAndDispatchNodeQuery_runs_internal
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (regs : NeighborhoodTrial.Registers controller)
    (failure source computation : Cmd)
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (rest : List (NeighborhoodScheduler.Frame tm instanceData))
    (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (store : Store)
    (post : Store → Prop)
    (hquery :
      Representation.QueryState regs instanceData
        { stack := frame :: rest
          registers := logicalBank }
        store)
    (hone : store controller.one = 1)
    (hbranch : ∀ middle,
      ControlDecode.EncodedNodePost regs frame.node middle →
      Representation.QueryState regs instanceData
        { stack := frame :: rest
          registers := logicalBank }
        middle →
      ∃ final,
        Runs
          (nodeBranches failure source computation
            ⟨(ControlDecode.expectedNodeValues frame.node).tag, by
              cases frame.node with
              | failure =>
                  simp [ControlDecode.expectedNodeValues]
              | graph graphNode =>
                  cases graphNode <;>
                    simp [ControlDecode.expectedNodeValues]⟩)
          (RAM.Structured.Switch.cleared middle
            (ControlDecode.tag regs))
          final ∧
        post final) :
    ∃ final,
      Runs
        (decodeAndDispatchNode regs failure source computation)
        store final ∧
      post final := by
  obtain ⟨middle, hdecode, hdecoded, hqueryMiddle⟩ :=
    Representation.QueryState.decodeNode_runs
      regs frame rest logicalBank store hquery
  obtain ⟨final, hbranchRun, hpost⟩ :=
    hbranch middle hdecoded hqueryMiddle
  have honeMiddle : middle controller.one = 1 := by
    rw [Footprint.runs_eq_outside
      (ControlDecode.decodeNode_layout_writesWithin regs)
      hdecode]
    · exact hone
    · intro honeMem
      exact NeighborhoodTrial.Registers.one_not_mem_footprint regs
        (Finset.mem_union_left _ honeMem)
  have hdispatch :=
    dispatchNode_runs_internal regs failure source computation
      middle final frame.node hdecoded honeMiddle hbranchRun
  exact ⟨final, Runs.seq hdecode hdispatch, hpost⟩

private theorem basics_runs
    (ops : List Basic) (store : Store) :
    Runs (Cmd.basics ops) store (Basic.execList ops store) := by
  obtain ⟨cost, space, hexec⟩ :=
    RAM.Structured.Internal.exec_basics_exists ops store
  exact ⟨ops.length, cost, space, hexec⟩

private theorem copy_runs
    {destination source : ℕ} (store : Store)
    (hne : destination ≠ source) :
    Runs (copy destination source) store
      (Function.update store destination (store source)) := by
  apply Runs.seq (Runs.basic (.imm destination 0) store)
  simpa [Basic.exec, Function.update_of_ne, hne, Ne.symm hne] using
    Runs.basic
      (.add destination source destination)
      (Basic.exec (.imm destination 0) store)

theorem encodePhase_runs_internal
    (regs : NeighborhoodTrial.Registers controller)
    (tag residue residuesLeft child nextChild : ℕ)
    (store : Store) :
    Runs
      (encodePhase regs tag residue residuesLeft child nextChild)
      store
      (Basic.execList
        (encodePhaseOps regs tag residue residuesLeft child nextChild)
        store) := by
  exact basics_runs _ _

theorem encodeDecodedPhase_value_internal
    (regs : NeighborhoodTrial.Registers controller)
    (tag : ℕ) (store : Store) :
    (Basic.execList
      (encodePhaseOps regs tag
        (decodedResidue regs) (decodedResiduesLeft regs)
        (decodedChild regs) (decodedNextChild regs)) store)
        (Layout.phaseCode regs) =
      phaseValue
        (store (Layout.chunkRadix regs))
        (store (Layout.bankRadix regs)) tag
        (store (decodedResidue regs))
        (store (decodedResiduesLeft regs))
        (store (decodedChild regs))
        (store (decodedNextChild regs)) := by
  simp [encodePhaseOps, Basic.execList, Basic.exec, phaseValue,
    regs.injective.eq_iff]

theorem encodeDecodedPhase_runs_internal
    (regs : NeighborhoodTrial.Registers controller)
    (tag : ℕ) (store : Store) :
    ∃ final,
      Runs
        (encodePhase regs tag
          (decodedResidue regs) (decodedResiduesLeft regs)
          (decodedChild regs) (decodedNextChild regs))
        store final ∧
      EncodePhasePost regs tag store final := by
  let final :=
    Basic.execList
      (encodePhaseOps regs tag
        (decodedResidue regs) (decodedResiduesLeft regs)
        (decodedChild regs) (decodedNextChild regs))
      store
  refine ⟨final, encodePhase_runs_internal
    regs tag (decodedResidue regs) (decodedResiduesLeft regs)
      (decodedChild regs) (decodedNextChild regs) store, ?_⟩
  constructor
  · exact encodeDecodedPhase_value_internal regs tag store
  · intro address hphase hquotient hdigit
    simp [final, encodePhaseOps, Basic.execList, Basic.exec,
      Function.update_of_ne, hphase, hdigit]

theorem phaseValue_cleanupCall_internal
    {workTapeCount base residue residuesLeft child : ℕ}
    (hbase : 0 < base)
    (hresidue :
      residue < base ^ FrameCodec.scalarDigitCount)
    (hleft :
      residuesLeft < base ^ FrameCodec.scalarDigitCount) :
    phaseValue base (base ^ FrameCodec.scalarDigitCount)
        3 residue residuesLeft child 0 =
      FrameCodec.encodePhase base
        (.cleanupCall residue residuesLeft child :
          NeighborhoodScheduler.Phase workTapeCount) := by
  rw [FrameCodec.encodePhase]
  simp only [FrameCodec.phaseDigits]
  change phaseValue base (base ^ FrameCodec.scalarDigitCount)
      3 residue residuesLeft child 0 =
    FrameCodec.encodeList base
      ([3] ++ (FrameCodec.scalarDigits base residue ++
        (FrameCodec.scalarDigits base residuesLeft ++ [child, 0])))
  rw [FrameCodec.encodeList_append]
  rw [FrameCodec.encodeList_append]
  rw [FrameCodec.encodeList_append]
  rw [FrameCodec.encodeList_scalarDigits hbase hresidue]
  rw [FrameCodec.encodeList_scalarDigits hbase hleft]
  simp [FrameCodec.encodeList, FrameCodec.scalarDigits,
    FrameCodec.scalarDigitCount, phaseValue, PackedDigits.push]

theorem phaseValue_enter_internal
    {workTapeCount base : ℕ} :
    phaseValue base (base ^ FrameCodec.scalarDigitCount)
        0 0 0 0 0 =
      FrameCodec.encodePhase base
        (.enter : NeighborhoodScheduler.Phase workTapeCount) := by
  simp [phaseValue, FrameCodec.encodePhase, FrameCodec.phaseDigits,
    FrameCodec.encodeList, PackedDigits.push]

theorem phaseValue_prepare_internal
    {workTapeCount base residue residuesLeft child : ℕ}
    (hbase : 0 < base)
    (hresidue :
      residue < base ^ FrameCodec.scalarDigitCount)
    (hleft :
      residuesLeft < base ^ FrameCodec.scalarDigitCount) :
    phaseValue base (base ^ FrameCodec.scalarDigitCount)
        1 residue residuesLeft child 0 =
      FrameCodec.encodePhase base
        (.prepare residue residuesLeft child :
          NeighborhoodScheduler.Phase workTapeCount) := by
  rw [FrameCodec.encodePhase]
  simp only [FrameCodec.phaseDigits]
  change phaseValue base (base ^ FrameCodec.scalarDigitCount)
      1 residue residuesLeft child 0 =
    FrameCodec.encodeList base
      ([1] ++ (FrameCodec.scalarDigits base residue ++
        (FrameCodec.scalarDigits base residuesLeft ++ [child, 0])))
  rw [FrameCodec.encodeList_append]
  rw [FrameCodec.encodeList_append]
  rw [FrameCodec.encodeList_append]
  rw [FrameCodec.encodeList_scalarDigits hbase hresidue]
  rw [FrameCodec.encodeList_scalarDigits hbase hleft]
  simp [FrameCodec.encodeList, FrameCodec.scalarDigits,
    FrameCodec.scalarDigitCount, phaseValue, PackedDigits.push]

theorem phaseValue_combine_internal
    {workTapeCount base residue residuesLeft : ℕ}
    (hbase : 0 < base)
    (hresidue :
      residue < base ^ FrameCodec.scalarDigitCount)
    (hleft :
      residuesLeft < base ^ FrameCodec.scalarDigitCount) :
    phaseValue base (base ^ FrameCodec.scalarDigitCount)
        2 residue residuesLeft 0 0 =
      FrameCodec.encodePhase base
        (.combine residue residuesLeft :
          NeighborhoodScheduler.Phase workTapeCount) := by
  rw [FrameCodec.encodePhase]
  simp only [FrameCodec.phaseDigits]
  change phaseValue base (base ^ FrameCodec.scalarDigitCount)
      2 residue residuesLeft 0 0 =
    FrameCodec.encodeList base
      ([2] ++ (FrameCodec.scalarDigits base residue ++
        (FrameCodec.scalarDigits base residuesLeft ++ [0, 0])))
  rw [FrameCodec.encodeList_append]
  rw [FrameCodec.encodeList_append]
  rw [FrameCodec.encodeList_append]
  rw [FrameCodec.encodeList_scalarDigits hbase hresidue]
  rw [FrameCodec.encodeList_scalarDigits hbase hleft]
  simp [FrameCodec.encodeList, FrameCodec.scalarDigits,
    FrameCodec.scalarDigitCount, phaseValue, PackedDigits.push]

theorem phaseValue_cleanupScale_internal
    {workTapeCount base residue residuesLeft nextChild : ℕ}
    (child : Fin (NeighborhoodExecutableEvaluation.graphFanIn
      workTapeCount))
    (hbase : 0 < base)
    (hresidue :
      residue < base ^ FrameCodec.scalarDigitCount)
    (hleft :
      residuesLeft < base ^ FrameCodec.scalarDigitCount) :
    phaseValue base (base ^ FrameCodec.scalarDigitCount)
        4 residue residuesLeft child.val nextChild =
      FrameCodec.encodePhase base
        (.cleanupScale residue residuesLeft child nextChild :
          NeighborhoodScheduler.Phase workTapeCount) := by
  rw [FrameCodec.encodePhase]
  simp only [FrameCodec.phaseDigits]
  change phaseValue base (base ^ FrameCodec.scalarDigitCount)
      4 residue residuesLeft child.val nextChild =
    FrameCodec.encodeList base
      ([4] ++ (FrameCodec.scalarDigits base residue ++
        (FrameCodec.scalarDigits base residuesLeft ++
          [child.val, nextChild])))
  rw [FrameCodec.encodeList_append]
  rw [FrameCodec.encodeList_append]
  rw [FrameCodec.encodeList_append]
  rw [FrameCodec.encodeList_scalarDigits hbase hresidue]
  rw [FrameCodec.encodeList_scalarDigits hbase hleft]
  simp [FrameCodec.encodeList, FrameCodec.scalarDigits,
    FrameCodec.scalarDigitCount, phaseValue, PackedDigits.push]

theorem encodeDecodedPhase_roundtrip_runs_internal
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store) (base : ℕ)
    (phase : NeighborhoodScheduler.Phase workTapeCount)
    (hbase : 0 < base)
    (hdecoded : ControlDecode.EncodedPhasePost regs phase store)
    (hresidue :
      (ControlDecode.expectedPhaseValues phase).residue <
        base ^ FrameCodec.scalarDigitCount)
    (hleft :
      (ControlDecode.expectedPhaseValues phase).residuesLeft <
        base ^ FrameCodec.scalarDigitCount)
    (hbaseValue : store (Layout.chunkRadix regs) = base)
    (hbankValue :
      store (Layout.bankRadix regs) =
        base ^ FrameCodec.scalarDigitCount) :
    ∃ final,
      Runs
        (encodePhase regs
          (ControlDecode.expectedPhaseValues phase).tag
          (decodedResidue regs) (decodedResiduesLeft regs)
          (decodedChild regs) (decodedNextChild regs))
        store final ∧
      final (Layout.phaseCode regs) =
        FrameCodec.encodePhase base phase ∧
      EncodePhasePost regs
        (ControlDecode.expectedPhaseValues phase).tag store final := by
  obtain ⟨final, hrun, hpost⟩ :=
    encodeDecodedPhase_runs_internal regs
      (ControlDecode.expectedPhaseValues phase).tag store
  refine ⟨final, hrun, ?_, hpost⟩
  rw [hpost.phaseCode_eq, hbaseValue, hbankValue,
    hdecoded.residue_eq, hdecoded.residuesLeft_eq,
    hdecoded.child_eq, hdecoded.next_eq]
  cases phase with
  | enter =>
      exact phaseValue_enter_internal
  | prepare residue residuesLeft child =>
      exact phaseValue_prepare_internal hbase hresidue hleft
  | combine residue residuesLeft =>
      exact phaseValue_combine_internal hbase hresidue hleft
  | cleanupCall residue residuesLeft child =>
      exact phaseValue_cleanupCall_internal hbase hresidue hleft
  | cleanupScale residue residuesLeft child next =>
      exact
        phaseValue_cleanupScale_internal
          child hbase hresidue hleft

theorem encodeCleanupCallPhase_runs_internal
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store) :
    ∃ final,
      Runs (encodeCleanupCallPhase regs) store final ∧
      EncodeCleanupPost regs store final := by
  let middle :=
    Basic.exec (.imm (Layout.codecDigit regs) 0) store
  let final :=
    Basic.execList
      (encodePhaseOps regs 3
        (decodedResidue regs) (decodedResiduesLeft regs)
        (decodedNextChild regs) (Layout.codecDigit regs)) middle
  refine ⟨final, ?_, ?_⟩
  · apply Runs.seq (Runs.basic _ store)
    exact encodePhase_runs_internal regs 3
      (decodedResidue regs) (decodedResiduesLeft regs)
      (decodedNextChild regs) (Layout.codecDigit regs) middle
  · constructor
    · simp [final, middle, encodePhaseOps, Basic.execList, Basic.exec,
        phaseValue, regs.injective.eq_iff]
    · intro address hphase hcodec
      simp [final, middle, encodePhaseOps, Basic.execList, Basic.exec,
        Function.update_of_ne, hphase, hcodec]

theorem encodePhase_writesWithin_internal
    (regs : NeighborhoodTrial.Registers controller)
    (tag residue residuesLeft child nextChild : ℕ) :
    Footprint.CmdWritesWithin regs.layout.footprint
      (encodePhase regs tag residue residuesLeft child nextChild) := by
  simp [encodePhase, encodePhaseOps, Cmd.basics, Cmd.seqList,
    Footprint.CmdWritesWithin, Footprint.BasicWritesWithin,
    Layout.index_mem_layout_footprint]

theorem encodeCleanupCallPhase_writesWithin_internal
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin regs.layout.footprint
      (encodeCleanupCallPhase regs) := by
  exact ⟨by
      simp [Footprint.CmdWritesWithin, Footprint.BasicWritesWithin,
        Layout.index_mem_layout_footprint],
    encodePhase_writesWithin_internal regs 3
      (decodedResidue regs) (decodedResiduesLeft regs)
      (decodedNextChild regs) (Layout.codecDigit regs)⟩

private theorem copy_writesWithin
    (regs : NeighborhoodTrial.Registers controller)
    (destination : Fin 34) (source : ℕ) :
    Footprint.CmdWritesWithin regs.layout.footprint
      (copy (regs.index destination) source) := by
  simp [copy, Footprint.CmdWritesWithin,
    Footprint.BasicWritesWithin,
    Layout.index_mem_layout_footprint]

@[simp] private theorem cleanupInverse_index_mem
    (regs : NeighborhoodTrial.Registers controller)
    (slot : Fin 7) :
    (cleanupInverseRegisters regs).index slot ∈
      regs.layout.footprint := by
  exact
    Layout.index_mem_layout_footprint regs
      (cleanupInverseMap slot)

theorem saveActiveFields_writesWithin_internal
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin regs.layout.footprint
      (saveActiveFields regs) :=
  ⟨copy_writesWithin regs 31 (Layout.scalar regs),
    copy_writesWithin regs 29 (Layout.out regs)⟩

theorem saveActiveFields_runs_internal
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store) :
    ∃ final,
      Runs (saveActiveFields regs) store final ∧
      SaveActivePost regs store final := by
  let middle :=
    Function.update store (Layout.codecScratch regs)
      (store (Layout.scalar regs))
  let final :=
    Function.update middle (Layout.frameCode regs)
      (middle (Layout.out regs))
  have hfirst :
      Runs
        (copy (Layout.codecScratch regs) (Layout.scalar regs))
        store middle := by
    exact copy_runs store (regs.injective.ne (by decide))
  have hsecond :
      Runs
        (copy (Layout.frameCode regs) (Layout.out regs))
        middle final := by
    exact copy_runs middle (regs.injective.ne (by decide))
  refine ⟨final, Runs.seq hfirst hsecond, ?_⟩
  constructor
  · simp [final, middle, regs.injective.eq_iff]
  · simp [final, middle, regs.injective.eq_iff]
  · intro address hscratch hframe
    simp [final, middle, Function.update_of_ne,
      hscratch, hframe]

theorem restoreActiveFields_writesWithin_internal
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin regs.layout.footprint
      (restoreActiveFields regs) :=
  ⟨copy_writesWithin regs 25 (Layout.codecScratch regs),
    copy_writesWithin regs 26 (Layout.frameCode regs)⟩

theorem restoreActiveFields_runs_internal
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store) :
    ∃ final,
      Runs (restoreActiveFields regs) store final ∧
      RestoreActivePost regs store final := by
  let middle :=
    Function.update store (Layout.scalar regs)
      (store (Layout.codecScratch regs))
  let final :=
    Function.update middle (Layout.out regs)
      (middle (Layout.frameCode regs))
  have hfirst :
      Runs
        (copy (Layout.scalar regs) (Layout.codecScratch regs))
        store middle := by
    exact copy_runs store (regs.injective.ne (by decide))
  have hsecond :
      Runs
        (copy (Layout.out regs) (Layout.frameCode regs))
        middle final := by
    exact copy_runs middle (regs.injective.ne (by decide))
  refine ⟨final, Runs.seq hfirst hsecond, ?_⟩
  constructor
  · simp [final, middle, regs.injective.eq_iff]
  · simp [final, middle, regs.injective.eq_iff]
  · intro address hscalar hout
    simp [final, middle, Function.update_of_ne, hscalar, hout]

private theorem cleanupInverse_writesWithin
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin regs.layout.footprint
      (Runtime.inverseMod (cleanupInverseRegisters regs)) := by
  simp [Runtime.inverseMod, RAM.Structured.RuntimeArithmetic.powMod,
    RAM.Structured.RuntimeArithmetic.powModBody,
    RAM.Structured.RuntimeArithmetic.mulMod,
    RAM.Structured.RuntimeArithmetic.reduce,
    RAM.Structured.RuntimeArithmetic.reduceBody,
    RAM.Structured.RuntimeArithmetic.reduceTestOp,
    RAM.Structured.RuntimeArithmetic.PowRegisters.reduceRegisters,
    Footprint.CmdWritesWithin,
    Footprint.BasicWritesWithin]

theorem selectChildTarget_writesWithin_internal
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin regs.layout.footprint
      (selectChildTarget regs) := by
  simp only [selectChildTarget, Footprint.CmdWritesWithin]
  refine ⟨?_, ?_, ?_⟩
  · simp [Footprint.BasicWritesWithin]
  · exact ⟨copy_writesWithin regs 26 (decodedChild regs),
      by
        simp [Footprint.BasicWritesWithin,
          Layout.index_mem_layout_footprint]⟩
  · exact copy_writesWithin regs 26 (decodedChild regs)

theorem selectChildTarget_runs_internal
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store)
    (hone : store (cleanupInverseRegisters regs).one = 1) :
    ∃ final,
      Runs (selectChildTarget regs) store final ∧
      ChildTargetPost regs store final := by
  let inverse := cleanupInverseRegisters regs
  change store inverse.one = 1 at hone
  have htestOne : inverse.test ≠ inverse.one :=
    inverse.index_ne (by decide)
  have houtOne : Layout.out regs ≠ inverse.one := by
    simp [inverse, cleanupInverseRegisters, cleanupInverseMap,
      regs.injective.eq_iff]
  let tested :=
    Basic.exec
      (.sub inverse.test (Layout.out regs) (decodedChild regs))
      store
  have htestRun :
      Runs
        (.basic
          (.sub inverse.test
            (Layout.out regs) (decodedChild regs)))
        store tested :=
    Runs.basic _ _
  by_cases hchild :
      store (decodedChild regs) < store (Layout.out regs)
  · let final :=
      Function.update tested (Layout.out regs)
        (tested (decodedChild regs))
    have hcopy :
        Runs
          (copy (Layout.out regs) (decodedChild regs))
          tested final := by
      exact copy_runs tested (regs.injective.ne (by decide))
    have htest : tested inverse.test ≠ 0 := by
      simp [tested, Basic.exec, inverse, cleanupInverseRegisters,
        cleanupInverseMap]
      exact Nat.ne_of_gt (Nat.sub_pos_of_lt hchild)
    refine
      ⟨final,
        Runs.seq htestRun (Runs.ifNonzero htest hcopy), ?_⟩
    constructor
    · simp [final, tested, hchild, Basic.exec,
        inverse, cleanupInverseRegisters, cleanupInverseMap,
        regs.injective.eq_iff]
    · intro address hout htestAddress
      change address ≠ inverse.test at htestAddress
      simp [final, tested, Basic.exec, Function.update_of_ne,
        hout, htestAddress]
  · have hle :
        store (Layout.out regs) ≤
          store (decodedChild regs) :=
      Nat.le_of_not_gt hchild
    let copied :=
      Function.update tested (Layout.out regs)
        (tested (decodedChild regs))
    let final :=
      Basic.exec
        (.add (Layout.out regs) (Layout.out regs) inverse.one)
        copied
    have hcopy :
        Runs
          (copy (Layout.out regs) (decodedChild regs))
          tested copied := by
      exact copy_runs tested (regs.injective.ne (by decide))
    have hadd :
        Runs
          (.basic
            (.add (Layout.out regs)
              (Layout.out regs) inverse.one))
          copied final :=
      Runs.basic _ _
    have htest : tested inverse.test = 0 := by
      simp [tested, Basic.exec, inverse, cleanupInverseRegisters,
        cleanupInverseMap, Nat.sub_eq_zero_of_le hle]
    have honeTested : tested inverse.one = 1 := by
      simpa [tested, Basic.exec, Function.update_of_ne,
        htestOne, Ne.symm htestOne] using hone
    have honeCopied : copied inverse.one = 1 := by
      simpa [copied, Function.update_of_ne,
        houtOne, Ne.symm houtOne] using honeTested
    have hchildTested :
        tested (decodedChild regs) =
          store (decodedChild regs) := by
      simp [tested, Basic.exec, inverse, cleanupInverseRegisters,
        cleanupInverseMap, regs.injective.eq_iff]
    have houtCopied :
        copied (Layout.out regs) =
          store (decodedChild regs) := by
      simp [copied, hchildTested]
    refine
      ⟨final,
        Runs.seq htestRun
          (Runs.ifZero htest (Runs.seq hcopy hadd)), ?_⟩
    constructor
    · simp only [final, Basic.exec]
      rw [Function.update_self]
      rw [houtCopied, honeCopied]
      simp [hchild]
    · intro address hout htestAddress
      change address ≠ inverse.test at htestAddress
      simp [final, copied, tested, Basic.exec,
        Function.update_of_ne, hout, htestAddress]

theorem childTargetValue_eq_succAbove_internal
    {n : ℕ} (out : Fin (n + 1)) (child : Fin n) :
    (if child.val < out.val then child.val else child.val + 1) =
      (out.succAbove child).val := by
  by_cases hchild : child.val < out.val
  · have hcast : child.castSucc < out := hchild
    rw [Fin.succAbove_of_castSucc_lt out child hcast]
    simp [hchild]
  · have hcast : out ≤ child.castSucc := by
      simpa using Nat.le_of_not_gt hchild
    rw [Fin.succAbove_of_le_castSucc out child hcast]
    simp [hchild]

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

theorem cleanupScale_writesWithin_internal
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin regs.layout.footprint
      (cleanupScale regs) := by
  simp only [cleanupScale, Cmd.seqList,
    Footprint.CmdWritesWithin]
  exact ⟨encodeCleanupCallPhase_writesWithin_internal regs,
    saveActiveFields_writesWithin_internal regs,
    cleanupInverse_writesWithin regs,
    copy_writesWithin regs 25
      (cleanupInverseRegisters regs).accumulator,
    selectChildTarget_writesWithin_internal regs,
    ResidueBankOps.scaleActiveRegister_writesWithin regs,
    restoreActiveFields_writesWithin_internal regs⟩

theorem cleanupScale_runs_internal
    {workTapeCount : ℕ} (tm : TM workTapeCount)
    (blockLength scalar residue residuesLeft nextChild
      digitBase bankBase word : ℕ)
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
    (hprime :
      (NeighborhoodExecutableEvaluation.modulus
        tm blockLength).Prime)
    (hdigitBase : 0 < digitBase)
    (hbankBase : 0 < bankBase)
    (hmodulusBase :
      NeighborhoodExecutableEvaluation.modulus tm blockLength ≤
        bankBase)
    (hresidueLt :
      residue <
        NeighborhoodExecutableEvaluation.modulus tm blockLength)
    (hresidueDigits :
      residue < digitBase ^ FrameCodec.scalarDigitCount)
    (hleftDigits :
      residuesLeft < digitBase ^ FrameCodec.scalarDigitCount)
    (hword :
      store
          (Layout.residueScaleRegisters regs).bank.bank.word =
        word)
    (hrep :
      NeighborhoodProgram.RepresentsResidueBank
        tm blockLength bankBase word original)
    (hwordLt :
      word <
        bankBase ^
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
        bankBase)
    (hmodulusValue :
      store (Layout.residueScaleRegisters regs).bank.modulus =
        NeighborhoodExecutableEvaluation.modulus tm blockLength)
    (hmodulusPred :
      store (Layout.residueScaleRegisters regs).bank.modulusPred =
        NeighborhoodExecutableEvaluation.modulus tm blockLength - 1)
    (hone :
      store (cleanupInverseRegisters regs).one = 1)
    (hscalar : store (Layout.scalar regs) = scalar)
    (hout : store (Layout.out regs) = out.val)
    (hchunkCount :
      store (Layout.chunkCount regs) =
        TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
          (NeighborhoodExecutableEvaluation.payloadWidth tm blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn
            workTapeCount))
    (hchunkRadix :
      store (Layout.chunkRadix regs) = digitBase)
    (hbankRadix :
      store (Layout.bankRadix regs) =
        digitBase ^ FrameCodec.scalarDigitCount)
    (hdecodedResidue :
      store (decodedResidue regs) = residue)
    (hdecodedResiduesLeft :
      store (decodedResiduesLeft regs) = residuesLeft)
    (hdecodedChild :
      store (decodedChild regs) = child.val)
    (hdecodedNextChild :
      store (decodedNextChild regs) = nextChild) :
    ∃ final finalWord,
      Runs (cleanupScale regs) store final ∧
      CleanupScalePost tm blockLength scalar residue residuesLeft
        nextChild digitBase bankBase finalWord original out child
        regs store final := by
  let modulus :=
    NeighborhoodExecutableEvaluation.modulus tm blockLength
  let inverse := cleanupInverseRegisters regs
  let inverseValue :=
    TreeEval.CookMertz.PrimeField.Runtime.inverse modulus residue
  obtain ⟨encoded, hencodeRun, hencodePost⟩ :=
    encodeCleanupCallPhase_runs_internal regs store
  obtain ⟨saved, hsaveRun, hsavePost⟩ :=
    saveActiveFields_runs_internal regs encoded
  have hsavedPhysical
      (slot : Fin 34)
      (hphase : slot ≠ 27)
      (hcodec : slot ≠ 30)
      (hscratch : slot ≠ 31)
      (hframe : slot ≠ 29) :
      saved (regs.index slot) = store (regs.index slot) := by
    calc
      saved (regs.index slot) = encoded (regs.index slot) :=
        hsavePost.eq_of_ne _ (regs.injective.ne hscratch)
          (regs.injective.ne hframe)
      _ = store (regs.index slot) :=
        hencodePost.eq_of_ne _ (regs.injective.ne hphase)
          (regs.injective.ne hcodec)
  have hsavedModulus : saved inverse.modulus = modulus := by
    simpa [inverse, cleanupInverseRegisters, cleanupInverseMap,
      modulus] using
      (hsavedPhysical (24 : Fin 34) (by decide) (by decide)
        (by decide) (by decide)).trans hmodulusValue
  have hsavedModulusPred :
      saved inverse.modulusPred = modulus - 1 := by
    simpa [inverse, cleanupInverseRegisters, cleanupInverseMap,
      modulus] using
      (hsavedPhysical (16 : Fin 34) (by decide) (by decide)
        (by decide) (by decide)).trans hmodulusPred
  have hsavedBase : saved inverse.base = residue := by
    simpa [inverse, cleanupInverseRegisters, cleanupInverseMap] using
      (hsavedPhysical (9 : Fin 34) (by decide) (by decide)
        (by decide) (by decide)).trans hdecodedResidue
  have hsavedOne : saved inverse.one = 1 := by
    simpa [inverse, cleanupInverseRegisters, cleanupInverseMap] using
      (hsavedPhysical (17 : Fin 34) (by decide) (by decide)
        (by decide) (by decide)).trans hone
  let inverted :=
    RAM.Structured.RuntimeArithmetic.powModResultStore
      inverse inverseValue saved
  have hinverseRun :
      Runs (Runtime.inverseMod inverse) saved inverted := by
    simpa [inverted, inverseValue] using
      Runtime.inverseMod_runs inverse saved modulus residue hprime
        hsavedModulus hsavedModulusPred hsavedBase hsavedOne
        hresidueLt
  have hinvertedEq
      (address : ℕ)
      (haccumulator : address ≠ inverse.accumulator)
      (htest : address ≠ inverse.test)
      (hexponent : address ≠ inverse.exponent) :
      inverted address = saved address := by
    simp [inverted,
      RAM.Structured.RuntimeArithmetic.powModResultStore,
      Function.update_of_ne, haccumulator, htest, hexponent]
  let scalarInstalled :=
    Function.update inverted (Layout.scalar regs)
      (inverted inverse.accumulator)
  have hinstallRun :
      Runs (copy (Layout.scalar regs) inverse.accumulator)
        inverted scalarInstalled := by
    exact copy_runs inverted (by
      simp [inverse, cleanupInverseRegisters, cleanupInverseMap,
        regs.injective.eq_iff])
  have hscalarInstalledEq
      (address : ℕ) (hscalarAddress : address ≠ Layout.scalar regs) :
      scalarInstalled address = inverted address := by
    simp [scalarInstalled, Function.update_of_ne, hscalarAddress]
  have hinstalledOne : scalarInstalled inverse.one = 1 := by
    calc
      scalarInstalled inverse.one = inverted inverse.one :=
        hscalarInstalledEq _ (by
          simp [inverse, cleanupInverseRegisters, cleanupInverseMap,
            regs.injective.eq_iff])
      _ = saved inverse.one :=
        hinvertedEq _ (inverse.index_ne (by decide)).symm
          (inverse.index_ne (by decide)).symm
          (inverse.index_ne (by decide)).symm
      _ = 1 := hsavedOne
  obtain ⟨targeted, htargetRun, htargetPost⟩ :=
    selectChildTarget_runs_internal regs scalarInstalled hinstalledOne
  have htargetedEq
      (address : ℕ)
      (houtAddress : address ≠ Layout.out regs)
      (htestAddress : address ≠ inverse.test) :
      targeted address = scalarInstalled address := by
    exact htargetPost.eq_of_ne address houtAddress (by
      simpa [inverse] using htestAddress)
  have htargetedPhysical
      (slot : Fin 34)
      (hphase : slot ≠ 27)
      (hcodec : slot ≠ 30)
      (hscratch : slot ≠ 31)
      (hframe : slot ≠ 29)
      (haccumulator : regs.index slot ≠ inverse.accumulator)
      (htest : regs.index slot ≠ inverse.test)
      (hexponent : regs.index slot ≠ inverse.exponent)
      (hscalarAddress : slot ≠ 25)
      (houtAddress : slot ≠ 26) :
      targeted (regs.index slot) = store (regs.index slot) := by
    calc
      targeted (regs.index slot) =
          scalarInstalled (regs.index slot) :=
        htargetedEq _ (regs.injective.ne houtAddress) htest
      _ = inverted (regs.index slot) :=
        hscalarInstalledEq _ (regs.injective.ne hscalarAddress)
      _ = saved (regs.index slot) :=
        hinvertedEq _ haccumulator htest hexponent
      _ = store (regs.index slot) :=
        hsavedPhysical slot hphase hcodec hscratch hframe
  have hinvertedAccumulator :
      inverted inverse.accumulator = inverseValue := by
    simp [inverted,
      RAM.Structured.RuntimeArithmetic.powModResultStore,
      inverse.injective.eq_iff]
  have htargetedScalar :
      targeted (Layout.scalar regs) = inverseValue := by
    calc
      targeted (Layout.scalar regs) =
          scalarInstalled (Layout.scalar regs) :=
        htargetedEq _ (regs.injective.ne (by decide)) (by
          simp [inverse, cleanupInverseRegisters, cleanupInverseMap,
            regs.injective.eq_iff])
      _ = inverted inverse.accumulator := by
        simp [scalarInstalled]
      _ = inverseValue := hinvertedAccumulator
  have hinstalledChild :
      scalarInstalled (decodedChild regs) = child.val := by
    calc
      scalarInstalled (decodedChild regs) =
          inverted (decodedChild regs) :=
        hscalarInstalledEq _ (regs.injective.ne (by decide))
      _ = saved (decodedChild regs) :=
        hinvertedEq _
          (by
            simp [inverse, cleanupInverseRegisters,
              cleanupInverseMap, regs.injective.eq_iff])
          (by
            simp [inverse, cleanupInverseRegisters,
              cleanupInverseMap, regs.injective.eq_iff])
          (by
            simp [inverse, cleanupInverseRegisters,
              cleanupInverseMap, regs.injective.eq_iff])
      _ = store (decodedChild regs) :=
        hsavedPhysical (11 : Fin 34) (by decide) (by decide)
          (by decide) (by decide)
      _ = child.val := hdecodedChild
  have hinstalledOut :
      scalarInstalled (Layout.out regs) = out.val := by
    calc
      scalarInstalled (Layout.out regs) =
          inverted (Layout.out regs) :=
        hscalarInstalledEq _ (regs.injective.ne (by decide))
      _ = saved (Layout.out regs) :=
        hinvertedEq _
          (by
            simp [inverse, cleanupInverseRegisters,
              cleanupInverseMap, regs.injective.eq_iff])
          (by
            simp [inverse, cleanupInverseRegisters,
              cleanupInverseMap, regs.injective.eq_iff])
          (by
            simp [inverse, cleanupInverseRegisters,
              cleanupInverseMap, regs.injective.eq_iff])
      _ = store (Layout.out regs) :=
        hsavedPhysical (26 : Fin 34) (by decide) (by decide)
          (by decide) (by decide)
      _ = out.val := hout
  have htargetedOut :
      targeted (Layout.out regs) = (out.succAbove child).val := by
    calc
      targeted (Layout.out regs) =
          if scalarInstalled (decodedChild regs) <
              scalarInstalled (Layout.out regs) then
            scalarInstalled (decodedChild regs)
          else
            scalarInstalled (decodedChild regs) + 1 :=
        htargetPost.out_eq
      _ = if child.val < out.val then child.val else child.val + 1 := by
        rw [hinstalledChild, hinstalledOut]
      _ = (out.succAbove child).val :=
        childTargetValue_eq_succAbove_internal out child
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
          simp [inverse, cleanupInverseRegisters,
            cleanupInverseMap, regs.injective.eq_iff])
        (by
          simp [inverse, cleanupInverseRegisters,
            cleanupInverseMap, regs.injective.eq_iff])
        (by
          simp [inverse, cleanupInverseRegisters,
            cleanupInverseMap, regs.injective.eq_iff])
        (by decide) (by decide)).trans hword
  have htargetedBase :
      targeted
          (Layout.residueScaleRegisters regs).bank.bank.base =
        bankBase := by
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
          simp [inverse, cleanupInverseRegisters,
            cleanupInverseMap, regs.injective.eq_iff])
        (by
          simp [inverse, cleanupInverseRegisters,
            cleanupInverseMap, regs.injective.eq_iff])
        (by
          simp [inverse, cleanupInverseRegisters,
            cleanupInverseMap, regs.injective.eq_iff])
        (by decide) (by decide)).trans hbaseValue
  have htargetedModulus :
      targeted (Layout.residueScaleRegisters regs).bank.modulus =
        modulus := by
    simpa [Layout.residueScaleRegisters, Layout.residueScaleMap,
      NeighborhoodProgram.ResidueScaleRegisters.bank,
      NeighborhoodProgram.ResidueScaleRegisters.bankSlot,
      NeighborhoodProgram.ResidueBankRegisters.modulus, modulus] using
      (htargetedPhysical (24 : Fin 34)
        (by decide) (by decide) (by decide) (by decide)
        (by
          simp [inverse, cleanupInverseRegisters,
            cleanupInverseMap, regs.injective.eq_iff])
        (by
          simp [inverse, cleanupInverseRegisters,
            cleanupInverseMap, regs.injective.eq_iff])
        (by
          simp [inverse, cleanupInverseRegisters,
            cleanupInverseMap, regs.injective.eq_iff])
        (by decide) (by decide)).trans hmodulusValue
  have htargetedModulusPred :
      targeted (Layout.residueScaleRegisters regs).bank.modulusPred =
        modulus - 1 := by
    simpa [Layout.residueScaleRegisters, Layout.residueScaleMap,
      NeighborhoodProgram.ResidueScaleRegisters.bank,
      NeighborhoodProgram.ResidueScaleRegisters.bankSlot,
      NeighborhoodProgram.ResidueBankRegisters.modulusPred,
      modulus] using
      (htargetedPhysical (16 : Fin 34)
        (by decide) (by decide) (by decide) (by decide)
        (by
          simp [inverse, cleanupInverseRegisters,
            cleanupInverseMap, regs.injective.eq_iff])
        (by
          simp [inverse, cleanupInverseRegisters,
            cleanupInverseMap, regs.injective.eq_iff])
        (by
          simp [inverse, cleanupInverseRegisters,
            cleanupInverseMap, regs.injective.eq_iff])
        (by decide) (by decide)).trans hmodulusPred
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
          simp [inverse, cleanupInverseRegisters,
            cleanupInverseMap, regs.injective.eq_iff])
        (by
          simp [inverse, cleanupInverseRegisters,
            cleanupInverseMap, regs.injective.eq_iff])
        (by
          simp [inverse, cleanupInverseRegisters,
            cleanupInverseMap, regs.injective.eq_iff])
        (by decide) (by decide)).trans hchunkCount
  obtain ⟨scaled, finalWord, hscaleRun, hscaledWord,
      hscaledRep, hscaledWordLt, hscaledBase, hscaledBasePred, hscaledOne,
      hscaledModulus, hscaledModulusPred, _hscaledOperand⟩ :=
    ResidueBankOps.scaleActiveRegister_runs tm blockLength
      inverseValue bankBase word original (out.succAbove child)
      regs targeted hbankBase hprime.pos hmodulusBase htargetedWord
      hrep hwordLt htargetedBase htargetedModulus
      htargetedModulusPred htargetedScalar htargetedOut
      htargetedChunkCount
  have hscaledScratch :
      scaled (Layout.codecScratch regs) =
        targeted (Layout.codecScratch regs) :=
    scale_run_preserves_physical regs 31 (by
      intro index
      fin_cases index <;> decide) hscaleRun
  have hscaledFrame :
      scaled (Layout.frameCode regs) =
        targeted (Layout.frameCode regs) :=
    scale_run_preserves_physical regs 29 (by
      intro index
      fin_cases index <;> decide) hscaleRun
  have hscaledPhase :
      scaled (Layout.phaseCode regs) =
        targeted (Layout.phaseCode regs) :=
    scale_run_preserves_physical regs 27 (by
      intro index
      fin_cases index <;> decide) hscaleRun
  have htargetedScratch :
      targeted (Layout.codecScratch regs) = scalar := by
    calc
      targeted (Layout.codecScratch regs) =
          scalarInstalled (Layout.codecScratch regs) :=
        htargetedEq _ (regs.injective.ne (by decide)) (by
          simp [inverse, cleanupInverseRegisters, cleanupInverseMap,
            regs.injective.eq_iff])
      _ = inverted (Layout.codecScratch regs) :=
        hscalarInstalledEq _ (regs.injective.ne (by decide))
      _ = saved (Layout.codecScratch regs) :=
        hinvertedEq _
          (by
            simp [inverse, cleanupInverseRegisters,
              cleanupInverseMap, regs.injective.eq_iff])
          (by
            simp [inverse, cleanupInverseRegisters,
              cleanupInverseMap, regs.injective.eq_iff])
          (by
            simp [inverse, cleanupInverseRegisters,
              cleanupInverseMap, regs.injective.eq_iff])
      _ = encoded (Layout.scalar regs) :=
        hsavePost.savedScalar_eq
      _ = store (Layout.scalar regs) :=
        hencodePost.eq_of_ne _
          (regs.injective.ne (by decide))
          (regs.injective.ne (by decide))
      _ = scalar := hscalar
  have htargetedFrame :
      targeted (Layout.frameCode regs) = out.val := by
    calc
      targeted (Layout.frameCode regs) =
          scalarInstalled (Layout.frameCode regs) :=
        htargetedEq _ (regs.injective.ne (by decide)) (by
          simp [inverse, cleanupInverseRegisters, cleanupInverseMap,
            regs.injective.eq_iff])
      _ = inverted (Layout.frameCode regs) :=
        hscalarInstalledEq _ (regs.injective.ne (by decide))
      _ = saved (Layout.frameCode regs) :=
        hinvertedEq _
          (by
            simp [inverse, cleanupInverseRegisters,
              cleanupInverseMap, regs.injective.eq_iff])
          (by
            simp [inverse, cleanupInverseRegisters,
              cleanupInverseMap, regs.injective.eq_iff])
          (by
            simp [inverse, cleanupInverseRegisters,
              cleanupInverseMap, regs.injective.eq_iff])
      _ = encoded (Layout.out regs) :=
        hsavePost.savedOut_eq
      _ = store (Layout.out regs) :=
        hencodePost.eq_of_ne _
          (regs.injective.ne (by decide))
          (regs.injective.ne (by decide))
      _ = out.val := hout
  have htargetedPhase :
      targeted (Layout.phaseCode regs) =
        FrameCodec.encodePhase digitBase
          (.cleanupCall residue residuesLeft nextChild :
            NeighborhoodScheduler.Phase workTapeCount) := by
    calc
      targeted (Layout.phaseCode regs) =
          scalarInstalled (Layout.phaseCode regs) :=
        htargetedEq _ (regs.injective.ne (by decide)) (by
          simp [inverse, cleanupInverseRegisters, cleanupInverseMap,
            regs.injective.eq_iff])
      _ = inverted (Layout.phaseCode regs) :=
        hscalarInstalledEq _ (regs.injective.ne (by decide))
      _ = saved (Layout.phaseCode regs) :=
        hinvertedEq _
          (by
            simp [inverse, cleanupInverseRegisters,
              cleanupInverseMap, regs.injective.eq_iff])
          (by
            simp [inverse, cleanupInverseRegisters,
              cleanupInverseMap, regs.injective.eq_iff])
          (by
            simp [inverse, cleanupInverseRegisters,
              cleanupInverseMap, regs.injective.eq_iff])
      _ = encoded (Layout.phaseCode regs) :=
        hsavePost.eq_of_ne _
          (regs.injective.ne (by decide))
          (regs.injective.ne (by decide))
      _ = phaseValue
          (store (Layout.chunkRadix regs))
          (store (Layout.bankRadix regs)) 3
          (store (decodedResidue regs))
          (store (decodedResiduesLeft regs))
          (store (decodedNextChild regs)) 0 :=
        hencodePost.phaseCode_eq
      _ = phaseValue digitBase
          (digitBase ^ FrameCodec.scalarDigitCount)
          3 residue residuesLeft nextChild 0 := by
        rw [hchunkRadix, hbankRadix, hdecodedResidue,
          hdecodedResiduesLeft, hdecodedNextChild]
      _ = FrameCodec.encodePhase digitBase
          (.cleanupCall residue residuesLeft nextChild :
            NeighborhoodScheduler.Phase workTapeCount) :=
        phaseValue_cleanupCall_internal
          hdigitBase hresidueDigits hleftDigits
  obtain ⟨final, hrestoreRun, hrestorePost⟩ :=
    restoreActiveFields_runs_internal regs scaled
  have hfinalPhase :
      final (Layout.phaseCode regs) =
        FrameCodec.encodePhase digitBase
          (.cleanupCall residue residuesLeft nextChild :
            NeighborhoodScheduler.Phase workTapeCount) := by
    calc
      final (Layout.phaseCode regs) =
          scaled (Layout.phaseCode regs) :=
        hrestorePost.eq_of_ne _
          (regs.injective.ne (by decide))
          (regs.injective.ne (by decide))
      _ = targeted (Layout.phaseCode regs) := hscaledPhase
      _ = _ := htargetedPhase
  have hfinalScalar : final (Layout.scalar regs) = scalar := by
    calc
      final (Layout.scalar regs) =
          scaled (Layout.codecScratch regs) :=
        hrestorePost.scalar_eq
      _ = targeted (Layout.codecScratch regs) := hscaledScratch
      _ = scalar := htargetedScratch
  have hfinalOut : final (Layout.out regs) = out.val := by
    calc
      final (Layout.out regs) =
          scaled (Layout.frameCode regs) :=
        hrestorePost.out_eq
      _ = targeted (Layout.frameCode regs) := hscaledFrame
      _ = out.val := htargetedFrame
  have hfinalWord :
      final
          (Layout.residueScaleRegisters regs).bank.bank.word =
        finalWord := by
    calc
      final
          (Layout.residueScaleRegisters regs).bank.bank.word =
          scaled
            (Layout.residueScaleRegisters regs).bank.bank.word :=
        hrestorePost.eq_of_ne _
          (by
            simp [Layout.residueScaleRegisters,
              Layout.residueScaleMap,
              NeighborhoodProgram.ResidueScaleRegisters.bank,
              NeighborhoodProgram.ResidueScaleRegisters.bankSlot,
              NeighborhoodProgram.ResidueBankRegisters.bank,
              NeighborhoodProgram.ResidueBankRegisters.bankSlot,
              regs.injective.eq_iff])
          (by
            simp [Layout.residueScaleRegisters,
              Layout.residueScaleMap,
              NeighborhoodProgram.ResidueScaleRegisters.bank,
              NeighborhoodProgram.ResidueScaleRegisters.bankSlot,
              NeighborhoodProgram.ResidueBankRegisters.bank,
              NeighborhoodProgram.ResidueBankRegisters.bankSlot,
              regs.injective.eq_iff])
      _ = finalWord := hscaledWord
  have hfinalBase :
      final
          (Layout.residueScaleRegisters regs).bank.bank.base =
        bankBase := by
    exact (hrestorePost.eq_of_ne _
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
  have hfinalBasePred :
      final
          (Layout.residueScaleRegisters regs).bank.bank.basePred =
        bankBase - 1 := by
    exact (hrestorePost.eq_of_ne _
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
  have hfinalOne :
      final
          (Layout.residueScaleRegisters regs).bank.bank.one =
        1 := by
    exact (hrestorePost.eq_of_ne _
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
  have hfinalModulus :
      final (Layout.residueScaleRegisters regs).bank.modulus =
        NeighborhoodExecutableEvaluation.modulus tm blockLength := by
    exact (hrestorePost.eq_of_ne _
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
  have hfinalModulusPred :
      final (Layout.residueScaleRegisters regs).bank.modulusPred =
        NeighborhoodExecutableEvaluation.modulus tm blockLength - 1 := by
    exact (hrestorePost.eq_of_ne _
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
  have hfinalPhysical
      (slot : Fin 34)
      (hphase : slot ≠ 27)
      (hcodec : slot ≠ 30)
      (hscratch : slot ≠ 31)
      (hframe : slot ≠ 29)
      (haccumulator : regs.index slot ≠ inverse.accumulator)
      (htest : regs.index slot ≠ inverse.test)
      (hexponent : regs.index slot ≠ inverse.exponent)
      (hscalarAddress : slot ≠ 25)
      (houtAddress : slot ≠ 26)
      (hscale :
        ∀ index, Layout.residueScaleMap index ≠ slot) :
      final (regs.index slot) = store (regs.index slot) := by
    calc
      final (regs.index slot) = scaled (regs.index slot) :=
        hrestorePost.eq_of_ne _
          (regs.injective.ne hscalarAddress)
          (regs.injective.ne houtAddress)
      _ = targeted (regs.index slot) :=
        scale_run_preserves_physical regs slot hscale hscaleRun
      _ = store (regs.index slot) :=
        htargetedPhysical slot hphase hcodec hscratch hframe
          haccumulator htest hexponent hscalarAddress houtAddress
  have hfinalRetained :
      ∀ slot,
        final (regs.index (cleanupRetainedMap slot)) =
          store (regs.index (cleanupRetainedMap slot)) := by
    intro slot
    fin_cases slot <;>
      apply hfinalPhysical <;>
      first
      | decide
      | simp [cleanupRetainedMap, inverse,
          cleanupInverseRegisters, cleanupInverseMap,
          regs.injective.eq_iff]
  have hallRuns :
      Runs (cleanupScale regs) store final := by
    simpa [cleanupScale, Cmd.seqList, inverse] using
      Runs.seq hencodeRun
        (Runs.seq hsaveRun
          (Runs.seq hinverseRun
            (Runs.seq hinstallRun
              (Runs.seq htargetRun
                (Runs.seq hscaleRun hrestoreRun)))))
  exact
    ⟨final, finalWord, hallRuns,
      { phaseCode_eq := hfinalPhase
        scalar_eq := hfinalScalar
        out_eq := hfinalOut
        word_eq := hfinalWord
        word_lt := hscaledWordLt
        represents := hscaledRep
        base_eq := hfinalBase
        basePred_eq := hfinalBasePred
        one_eq := hfinalOne
        modulus_eq := hfinalModulus
        modulusPred_eq := hfinalModulusPred
        retained_eq := hfinalRetained }⟩

end Internal
end Dispatcher
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
