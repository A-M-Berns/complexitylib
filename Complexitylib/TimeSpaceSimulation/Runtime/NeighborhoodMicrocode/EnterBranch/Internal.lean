/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.Dispatcher
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.EnterBranch.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.EnterComputation
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.EnterLeaf

/-!
# Concrete enter-phase branch -- proofs
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace EnterBranch
namespace Internal

open RAM Structured
open NeighborhoodExecutableEvaluation

variable {controller : SearchProgram.Registers}

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

private theorem layoutWritesWithin_trial
    (regs : NeighborhoodTrial.Registers controller)
    {command : Cmd}
    (hwrites :
      Footprint.CmdWritesWithin regs.layout.footprint command) :
    Footprint.CmdWritesWithin regs.footprint command :=
  cmdWritesWithin_mono hwrites (by
    intro address haddress
    exact Finset.mem_union_left _ haddress)

private theorem inputFrame_of_layout_run
    (regs : NeighborhoodTrial.Registers controller)
    (input : List Bool)
    {command : Cmd} {initial final : Store}
    (hwrites :
      Footprint.CmdWritesWithin regs.layout.footprint command)
    (hrun : Runs command initial final)
    (hframe :
      SearchProgram.InputFrame
        controller regs.footprint input initial) :
    SearchProgram.InputFrame
      controller regs.footprint input final :=
  NeighborhoodTrial.Registers.runs_preserves_inputFrame
    regs (layoutWritesWithin_trial regs hwrites) hrun hframe

private theorem inputLength_of_layout_run
    (regs : NeighborhoodTrial.Registers controller)
    {command : Cmd} {initial final : Store}
    (hwrites :
      Footprint.CmdWritesWithin regs.layout.footprint command)
    (hrun : Runs command initial final) :
    final controller.inputLength =
      initial controller.inputLength :=
  NeighborhoodTrial.Registers.runs_preserves_controller_index
    regs (layoutWritesWithin_trial regs hwrites) hrun
    (0 : Fin 17) (by decide) (by decide) (by decide)

private theorem one_of_layout_run
    (regs : NeighborhoodTrial.Registers controller)
    {command : Cmd} {initial final : Store}
    (hwrites :
      Footprint.CmdWritesWithin regs.layout.footprint command)
    (hrun : Runs command initial final) :
    final controller.one = initial controller.one := by
  simpa [SearchProgram.Registers.one,
    SearchProgram.Registers.primeRegisters,
    SearchProgram.Registers.primeSlot] using
      NeighborhoodTrial.Registers.runs_preserves_controller_index
        regs (layoutWritesWithin_trial regs hwrites) hrun
        (14 : Fin 17) (by decide) (by decide) (by decide)

theorem step_writesWithin_internal
    (tm : TM workTapeCount)
    (order : FiniteEncoding.StateOrder tm)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin regs.layout.footprint
      (step tm order regs) := by
  exact
    Dispatcher.decodeAndDispatchNode_writesWithin regs
      (EnterLeaf.failure regs)
      (EnterLeaf.source tm order regs)
      (EnterComputation.step regs)
      (EnterLeaf.failure_writesWithin regs)
      (EnterLeaf.source_writesWithin tm order regs)
      (EnterComputation.step_writesWithin regs)

theorem step_runs_internal
    {tm : TM workTapeCount}
    (order : FiniteEncoding.StateOrder tm)
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (rest : List (NeighborhoodScheduler.Frame tm instanceData))
    (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (store : Store)
    (hphase : frame.phase = .enter)
    (hencoding :
      instanceData.encoding =
        FiniteEncoding.ofStateOrder order instanceData.blockLength)
    (hquery :
      Representation.QueryState regs instanceData
        { stack := frame :: rest
          registers := logicalBank }
        store)
    (hframe :
      SearchProgram.InputFrame
        controller regs.footprint instanceData.x store)
    (hinputLength :
      store controller.inputLength = instanceData.x.length)
    (hone : store controller.one = 1) :
    ∃ final,
      Runs (step tm order regs) store final ∧
      Representation.QueryState regs instanceData
        (NeighborhoodScheduler.State.next
          { stack := frame :: rest
            registers := logicalBank })
        final ∧
      SearchProgram.InputFrame
        controller regs.footprint instanceData.x final ∧
      final controller.inputLength = instanceData.x.length ∧
      final controller.one = 1 := by
  obtain ⟨middle, hdecode, hdecoded, hqueryMiddle⟩ :=
    Representation.QueryState.decodeNode_runs
      regs frame rest logicalBank store hquery
  have hframeMiddle :
      SearchProgram.InputFrame
        controller regs.footprint instanceData.x middle :=
    inputFrame_of_layout_run regs instanceData.x
      (ControlDecode.decodeNode_layout_writesWithin regs)
      hdecode hframe
  have hinputLengthMiddle :
      middle controller.inputLength = instanceData.x.length :=
    (inputLength_of_layout_run regs
      (ControlDecode.decodeNode_layout_writesWithin regs)
      hdecode).trans hinputLength
  have honeMiddle :
      middle controller.one = 1 :=
    (one_of_layout_run regs
      (ControlDecode.decodeNode_layout_writesWithin regs)
      hdecode).trans hone
  let cleared :=
    RAM.Structured.Switch.cleared middle
      (ControlDecode.tag regs)
  have hclearRun :
      Runs
        (.basic (.imm (ControlDecode.tag regs) 0))
        middle cleared := by
    simpa [cleared, RAM.Structured.Switch.cleared,
      Basic.exec] using
        Runs.basic
          (.imm (ControlDecode.tag regs) 0) middle
  have hclearWrites :
      Footprint.CmdWritesWithin regs.layout.footprint
        (.basic (.imm (ControlDecode.tag regs) 0)) := by
    simpa [Footprint.CmdWritesWithin,
      Footprint.BasicWritesWithin, ControlDecode.tag] using
        Layout.index_mem_layout_footprint regs 6
  have hqueryCleared :
      Representation.QueryState regs instanceData
        { stack := frame :: rest
          registers := logicalBank }
        cleared := by
    simpa [cleared] using
      Representation.QueryState.clearedTag
        regs frame rest logicalBank middle hqueryMiddle
  have hframeCleared :
      SearchProgram.InputFrame
        controller regs.footprint instanceData.x cleared :=
    inputFrame_of_layout_run regs instanceData.x
      hclearWrites hclearRun hframeMiddle
  have hinputLengthCleared :
      cleared controller.inputLength = instanceData.x.length :=
    (inputLength_of_layout_run regs
      hclearWrites hclearRun).trans hinputLengthMiddle
  have honeCleared :
      cleared controller.one = 1 :=
    (one_of_layout_run regs
      hclearWrites hclearRun).trans honeMiddle
  cases hnode : frame.node with
  | failure =>
      obtain ⟨final, hbranch, hfinal, hfinalFrame,
          hfinalLength, hfinalOne⟩ :=
        EnterLeaf.failure_runs
          regs instanceData frame rest logicalBank cleared
          hnode hphase hqueryCleared hframeCleared
          hinputLengthCleared honeCleared
      have hselected :
          Runs
            (Dispatcher.nodeBranches
              (EnterLeaf.failure regs)
              (EnterLeaf.source tm order regs)
              (EnterComputation.step regs)
              ⟨(ControlDecode.expectedNodeValues frame.node).tag, by
                simp [hnode, ControlDecode.expectedNodeValues]⟩)
            cleared final := by
        simpa [Dispatcher.nodeBranches, hnode,
          ControlDecode.expectedNodeValues] using hbranch
      have hdispatch :=
        Dispatcher.dispatchNode_runs
          regs
          (EnterLeaf.failure regs)
          (EnterLeaf.source tm order regs)
          (EnterComputation.step regs)
          middle final frame.node hdecoded honeMiddle
          (by simpa [cleared] using hselected)
      exact
        ⟨final,
          by
            simpa [step, Dispatcher.decodeAndDispatchNode] using
              Runs.seq hdecode hdispatch,
          hfinal, hfinalFrame, hfinalLength, hfinalOne⟩
  | graph graphNode =>
      cases graphNode with
      | source tape block =>
          obtain ⟨final, hbranch, hfinal, hfinalFrame,
              hfinalLength, hfinalOne⟩ :=
            EnterLeaf.source_runs
              order regs instanceData frame rest logicalBank
              tape block cleared hnode hphase hencoding
              hqueryCleared hframeCleared hinputLengthCleared
              honeCleared
          have hselected :
              Runs
                (Dispatcher.nodeBranches
                  (EnterLeaf.failure regs)
                  (EnterLeaf.source tm order regs)
                  (EnterComputation.step regs)
                  ⟨(ControlDecode.expectedNodeValues frame.node).tag, by
                    simp [hnode, ControlDecode.expectedNodeValues]⟩)
                cleared final := by
            simpa [Dispatcher.nodeBranches, hnode,
              ControlDecode.expectedNodeValues] using hbranch
          have hdispatch :=
            Dispatcher.dispatchNode_runs
              regs
              (EnterLeaf.failure regs)
              (EnterLeaf.source tm order regs)
              (EnterComputation.step regs)
              middle final frame.node hdecoded honeMiddle
              (by simpa [cleared] using hselected)
          exact
            ⟨final,
              by
                simpa [step, Dispatcher.decodeAndDispatchNode] using
                  Runs.seq hdecode hdispatch,
              hfinal, hfinalFrame, hfinalLength, hfinalOne⟩
      | computation tape slot interval =>
          have hdecodedInterval :
              cleared (ControlDecode.nodePayload1 regs) =
                interval := by
            calc
              cleared (ControlDecode.nodePayload1 regs) =
                  middle (ControlDecode.nodePayload1 regs) := by
                simp [cleared, RAM.Structured.Switch.cleared,
                  ControlDecode.nodePayload1, ControlDecode.tag,
                  regs.injective.eq_iff]
              _ = interval := by
                simpa [hnode,
                  ControlDecode.expectedNodeValues] using
                    hdecoded.payload1_eq
          obtain ⟨final, hbranch, hfinal, hfinalFrame,
              hfinalLength, hfinalOne⟩ :=
            EnterComputation.step_runs
              regs instanceData frame rest logicalBank cleared
              tape slot interval hnode hphase hdecodedInterval
              hqueryCleared hframeCleared hinputLengthCleared
              honeCleared
          have hselected :
              Runs
                (Dispatcher.nodeBranches
                  (EnterLeaf.failure regs)
                  (EnterLeaf.source tm order regs)
                  (EnterComputation.step regs)
                  ⟨(ControlDecode.expectedNodeValues frame.node).tag, by
                    simp [hnode, ControlDecode.expectedNodeValues]⟩)
                cleared final := by
            simpa [Dispatcher.nodeBranches, hnode,
              ControlDecode.expectedNodeValues] using hbranch
          have hdispatch :=
            Dispatcher.dispatchNode_runs
              regs
              (EnterLeaf.failure regs)
              (EnterLeaf.source tm order regs)
              (EnterComputation.step regs)
              middle final frame.node hdecoded honeMiddle
              (by simpa [cleared] using hselected)
          exact
            ⟨final,
              by
                simpa [step, Dispatcher.decodeAndDispatchNode] using
                  Runs.seq hdecode hdispatch,
              hfinal, hfinalFrame, hfinalLength, hfinalOne⟩

end Internal
end EnterBranch
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
