/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.Representation.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.Representation.Internal

/-!
# Logical representation of neighborhood-scheduler query states

This surface exposes the exact correspondence between a pure scheduler query
state and its active fields, suspended-frame word, and catalytic residue bank.
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace Representation

variable {controller : SearchProgram.Registers}

/-- Decoder ABI preservation transports an exact active-frame
representation to the final store. -/
theorem ActiveFrame.of_preservesABI
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (regs : NeighborhoodTrial.Registers controller)
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (initial final : RAM.Structured.Store)
    (hframe : ActiveFrame regs frame initial)
    (hpreserves : ControlDecode.PreservesABI regs initial final) :
    ActiveFrame regs frame final :=
  Internal.activeFrame_of_preservesABI_internal
    regs frame initial final hframe hpreserves

/-- Decoder ABI preservation transports all retained runtime parameters to
the final store. -/
theorem Parameters.of_preservesABI
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (regs : NeighborhoodTrial.Registers controller)
    (initial final : RAM.Structured.Store)
    (hparameters : Parameters regs instanceData initial)
    (hpreserves : ControlDecode.PreservesABI regs initial final) :
    Parameters regs instanceData final :=
  Internal.parameters_of_preservesABI_internal
    regs initial final hparameters hpreserves

/-- Popping a continuation preserves every retained runtime parameter. -/
theorem Parameters.of_popParent
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (regs : NeighborhoodTrial.Registers controller)
    (initial final : RAM.Structured.Store)
    (hparameters : Parameters regs instanceData initial)
    (hrun : RAM.Structured.Runs
      (FrameTransfer.popParent regs) initial final) :
    Parameters regs instanceData final :=
  Internal.parameters_of_popParent_internal
    regs initial final hparameters hrun

/-- Suspending a continuation preserves every retained runtime parameter. -/
theorem Parameters.of_pushParent
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (regs : NeighborhoodTrial.Registers controller)
    (initial final : RAM.Structured.Store)
    (hparameters : Parameters regs instanceData initial)
    (hrun : RAM.Structured.Runs
      (FrameTransfer.pushParent regs) initial final) :
    Parameters regs instanceData final :=
  Internal.parameters_of_pushParent_internal
    regs initial final hparameters hrun

/-- Suspending a parent preserves every active-frame and retained-parameter
ABI cell exactly. -/
theorem pushParent_preservesABI
    (regs : NeighborhoodTrial.Registers controller)
    {initial final : RAM.Structured.Store}
    (hrun : RAM.Structured.Runs
      (FrameTransfer.pushParent regs) initial final) :
    ControlDecode.PreservesABI regs initial final :=
  Internal.pushParent_preservesABI_internal regs hrun

/-- Popping a continuation never writes the catalytic bank word. -/
theorem popParent_bank_eq
    (regs : NeighborhoodTrial.Registers controller)
    {initial final : RAM.Structured.Store}
    (hrun : RAM.Structured.Runs
      (FrameTransfer.popParent regs) initial final) :
    final regs.layout.bank = initial regs.layout.bank :=
  Internal.popParent_bank_eq_internal regs hrun

/-- Suspending a continuation never writes the catalytic bank word. -/
theorem pushParent_bank_eq
    (regs : NeighborhoodTrial.Registers controller)
    {initial final : RAM.Structured.Store}
    (hrun : RAM.Structured.Runs
      (FrameTransfer.pushParent regs) initial final) :
    final regs.layout.bank = initial regs.layout.bank :=
  Internal.pushParent_bank_eq_internal regs hrun

/-- Suspending the represented active frame packs it at the head of the
continuation word, while preserving all runtime parameters and the catalytic
bank. The caller may then install a child as the new active frame. -/
theorem Stack.pushParent_runs
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (regs : NeighborhoodTrial.Registers controller)
    (current : NeighborhoodScheduler.Frame tm instanceData)
    (rest : List (NeighborhoodScheduler.Frame tm instanceData))
    (store : RAM.Structured.Store)
    (hstack : Stack regs (current :: rest) store)
    (hparameters : Parameters regs instanceData store)
    (hbound : NeighborhoodScheduler.FrameBounds.FrameBound current) :
    ∃ final,
      RAM.Structured.Runs
        (FrameTransfer.pushParent regs) store final ∧
      FrameTransfer.RepresentsStack regs
        (digitBase instanceData) (frameBase instanceData)
        (current :: rest) final ∧
      Parameters regs instanceData final ∧
      final regs.layout.bank = store regs.layout.bank :=
  Internal.stack_pushParent_runs_internal
    regs current rest store hstack hparameters hbound

/-- Popping the represented active frame either exposes the exact suspended
parent or produces the exact empty-stack representation. Runtime parameters
and the catalytic bank word are preserved in both cases. -/
theorem Stack.popParent_runs
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (regs : NeighborhoodTrial.Registers controller)
    (current : NeighborhoodScheduler.Frame tm instanceData)
    (rest : List (NeighborhoodScheduler.Frame tm instanceData))
    (store : RAM.Structured.Store)
    (hstack : Stack regs (current :: rest) store)
    (hparameters : Parameters regs instanceData store)
    (hbounds : ∀ frame ∈ rest,
      NeighborhoodScheduler.FrameBounds.FrameBound frame) :
    ∃ final,
      RAM.Structured.Runs
        (FrameTransfer.popParent regs) store final ∧
      Stack regs rest final ∧
      Parameters regs instanceData final ∧
      final regs.layout.bank = store regs.layout.bank :=
  Internal.stack_popParent_runs_internal
    regs current rest store hstack hparameters hbounds

/-- Popping a represented query state's active frame produces the exact
logical tail while preserving its catalytic register family. -/
theorem QueryState.popParent_runs
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (regs : NeighborhoodTrial.Registers controller)
    (current : NeighborhoodScheduler.Frame tm instanceData)
    (rest : List (NeighborhoodScheduler.Frame tm instanceData))
    (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (store : RAM.Structured.Store)
    (hquery :
      QueryState regs instanceData
        { stack := current :: rest
          registers := logicalBank }
        store) :
    ∃ final,
      RAM.Structured.Runs
        (FrameTransfer.popParent regs) store final ∧
      QueryState regs instanceData
        { stack := rest
          registers := logicalBank }
        final :=
  Internal.queryState_popParent_runs_internal
    regs current rest logicalBank store hquery

/-- Decoding a represented reachable node recovers its exact semantic fields
while preserving the active frame and retained runtime parameters. -/
theorem ActiveFrame.decodeNode_runs
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (regs : NeighborhoodTrial.Registers controller)
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (store : RAM.Structured.Store)
    (hactive : ActiveFrame regs frame store)
    (hparameters : Parameters regs instanceData store)
    (hbound :
      NeighborhoodScheduler.FrameBounds.FrameBound frame) :
    ∃ final,
      RAM.Structured.Runs (ControlDecode.decodeNode regs) store final ∧
      ControlDecode.EncodedNodePost regs frame.node final ∧
      ActiveFrame regs frame final ∧
      Parameters regs instanceData final :=
  Internal.activeFrame_decodeNode_runs_internal
    regs frame store hactive hparameters hbound

/-- Decoding a represented reachable phase recovers its exact semantic fields
while preserving the active frame and retained runtime parameters. -/
theorem ActiveFrame.decodePhase_runs
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (regs : NeighborhoodTrial.Registers controller)
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (store : RAM.Structured.Store)
    (hactive : ActiveFrame regs frame store)
    (hparameters : Parameters regs instanceData store)
    (hbound :
      NeighborhoodScheduler.FrameBounds.FrameBound frame) :
    ∃ final,
      RAM.Structured.Runs (ControlDecode.decodePhase regs) store final ∧
      ControlDecode.EncodedPhasePost regs frame.phase final ∧
      ActiveFrame regs frame final ∧
      Parameters regs instanceData final :=
  Internal.activeFrame_decodePhase_runs_internal
    regs frame store hactive hparameters hbound

/-- Decoding the active node preserves the complete represented query state,
including the suspended stack and catalytic residue bank. -/
theorem QueryState.decodeNode_runs
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (regs : NeighborhoodTrial.Registers controller)
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (rest : List (NeighborhoodScheduler.Frame tm instanceData))
    (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (store : RAM.Structured.Store)
    (hquery :
      QueryState regs instanceData
        { stack := frame :: rest
          registers := logicalBank }
        store) :
    ∃ final,
      RAM.Structured.Runs
        (ControlDecode.decodeNode regs) store final ∧
      ControlDecode.EncodedNodePost regs frame.node final ∧
      QueryState regs instanceData
        { stack := frame :: rest
          registers := logicalBank }
        final :=
  Internal.queryState_decodeNode_runs_internal
    regs frame rest logicalBank store hquery

/-- Decoding the active phase preserves the complete represented query state,
including the suspended stack and catalytic residue bank. -/
theorem QueryState.decodePhase_runs
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (regs : NeighborhoodTrial.Registers controller)
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (rest : List (NeighborhoodScheduler.Frame tm instanceData))
    (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (store : RAM.Structured.Store)
    (hquery :
      QueryState regs instanceData
        { stack := frame :: rest
          registers := logicalBank }
        store) :
    ∃ final,
      RAM.Structured.Runs
        (ControlDecode.decodePhase regs) store final ∧
      ControlDecode.EncodedPhasePost regs frame.phase final ∧
      QueryState regs instanceData
        { stack := frame :: rest
          registers := logicalBank }
        final :=
  Internal.queryState_decodePhase_runs_internal
    regs frame rest logicalBank store hquery

/-- Clearing the shared decoder tag leaves the complete represented query
state unchanged. This is the state handed to a selected numeric-switch
branch. -/
theorem QueryState.clearedTag
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (regs : NeighborhoodTrial.Registers controller)
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (rest : List (NeighborhoodScheduler.Frame tm instanceData))
    (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (store : RAM.Structured.Store)
    (hquery :
      QueryState regs instanceData
        { stack := frame :: rest
          registers := logicalBank }
        store) :
    QueryState regs instanceData
      { stack := frame :: rest
        registers := logicalBank }
      (RAM.Structured.Switch.cleared store
        (ControlDecode.tag regs)) :=
  Internal.queryState_clearedTag_internal
    regs frame rest logicalBank store hquery

/-- Any fragment preserving the decoder ABI, packed continuation word, and
catalytic bank transports the complete represented nonempty query state. -/
theorem QueryState.of_preservesABI
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (regs : NeighborhoodTrial.Registers controller)
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (rest : List (NeighborhoodScheduler.Frame tm instanceData))
    (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (initial final : RAM.Structured.Store)
    (hquery :
      QueryState regs instanceData
        { stack := frame :: rest
          registers := logicalBank }
        initial)
    (hpreserves :
      ControlDecode.PreservesABI regs initial final)
    (hstack :
      final (Layout.frameStackRegisters regs).word =
        initial (Layout.frameStackRegisters regs).word)
    (hbank :
      final regs.layout.bank = initial regs.layout.bank) :
    QueryState regs instanceData
      { stack := frame :: rest
        registers := logicalBank }
      final :=
  Internal.queryState_of_preservesABI_internal
    regs frame rest logicalBank initial final hquery
    hpreserves hstack hbank

/-- The instance payload width is the candidate pass's Boolean width. -/
theorem payloadWidth_eq_booleanWidth
    {tm : TM workTapeCount}
    (instanceData : NeighborhoodProgram.ResidueInstance tm) :
    NeighborhoodExecutableEvaluation.payloadWidth
        tm instanceData.blockLength =
      CandidateParameters.booleanWidth
        tm.Q instanceData.candidateTime :=
  Internal.payloadWidth_eq_booleanWidth_internal instanceData

/-- The two-chunk field radix is exactly the runtime bank radix. -/
theorem fieldBase_eq_bankRadix
    {tm : TM workTapeCount}
    (instanceData : NeighborhoodProgram.ResidueInstance tm) :
    fieldBase instanceData =
      CandidateParameters.bankRadix
        tm.Q workTapeCount instanceData.candidateTime :=
  Internal.fieldBase_eq_bankRadix_internal instanceData

/-- The row-major logical bank dimensions equal the candidate pass's packed
bank digit count. -/
theorem bankCoordinateCount_eq
    {tm : TM workTapeCount}
    (instanceData : NeighborhoodProgram.ResidueInstance tm) :
    (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount + 1) *
        TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
          (NeighborhoodExecutableEvaluation.payloadWidth
            tm instanceData.blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount) =
      CandidateParameters.bankDigitCount
        tm.Q workTapeCount instanceData.candidateTime :=
  Internal.bankCoordinateCount_eq_internal instanceData

/-- The concrete stack codec is the generic least-significant-first frame
packing used by the scheduler depth analysis. -/
theorem encodeStack_eq_packFrames
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (digitBase frameBase : ℕ)
    (frames : List (NeighborhoodScheduler.Frame tm instanceData)) :
    FrameTransfer.encodeStack digitBase frameBase frames =
      NeighborhoodScheduler.StackDepth.packFrames frameBase
        (fun frame =>
          FrameCodec.encodeFrame digitBase frame + 1)
        frames :=
  Internal.encodeStack_eq_packFrames_internal
    digitBase frameBase frames

/-- The concrete loop flag is zero exactly for the empty logical stack. -/
theorem stack_active_zero_iff
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (regs : NeighborhoodTrial.Registers controller)
    (frames : List (NeighborhoodScheduler.Frame tm instanceData))
    (store : RAM.Structured.Store)
    (hstack : Stack regs frames store) :
    store (Layout.active regs) = 0 ↔ frames = [] :=
  Internal.stack_active_zero_iff_internal
    regs frames store hstack

/-- The concrete loop flag is exact for a represented query state. -/
theorem QueryState.active_zero_iff_terminal
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (regs : NeighborhoodTrial.Registers controller)
    (state : NeighborhoodScheduler.State tm instanceData)
    (store : RAM.Structured.Store)
    (hrep : QueryState regs instanceData state store) :
    store (Layout.active regs) = 0 ↔ state.Terminal :=
  Internal.queryState_active_zero_iff_terminal_internal
    regs state store hrep

/-- A represented nonempty stack exposes its exact active frame and tail. -/
theorem QueryState.head
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (regs : NeighborhoodTrial.Registers controller)
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (rest : List (NeighborhoodScheduler.Frame tm instanceData))
    (state : NeighborhoodScheduler.State tm instanceData)
    (store : RAM.Structured.Store)
    (hframes : state.stack = frame :: rest)
    (hrep : QueryState regs instanceData state store) :
    ActiveFrame regs frame store ∧
      FrameTransfer.RepresentsStack regs
        (digitBase instanceData) (frameBase instanceData) rest store :=
  Internal.queryState_head_internal
    regs frame rest state store hframes hrep

/-- A represented empty stack has a cleared active flag and empty word. -/
theorem QueryState.empty
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (regs : NeighborhoodTrial.Registers controller)
    (state : NeighborhoodScheduler.State tm instanceData)
    (store : RAM.Structured.Store)
    (hempty : state.stack = [])
    (hrep : QueryState regs instanceData state store) :
    store (Layout.active regs) = 0 ∧
      FrameTransfer.RepresentsStack regs
        (digitBase instanceData) (frameBase instanceData)
        ([] :
          List (NeighborhoodScheduler.Frame tm instanceData))
        store :=
  Internal.queryState_empty_internal
    regs state store hempty hrep

/-- A scheduler capacity invariant and per-frame codec bounds imply the exact
packed continuation-word bound required by workspace accounting. -/
theorem QueryState.stack_lt
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (regs : NeighborhoodTrial.Registers controller)
    (state : NeighborhoodScheduler.State tm instanceData)
    (store : RAM.Structured.Store)
    (hrep : QueryState regs instanceData state store)
    (hcapacity :
      NeighborhoodScheduler.StackDepth.StackInvariant
        instanceData.horizon state) :
    store regs.layout.stack <
      frameBase instanceData ^ instanceData.horizon :=
  Internal.queryState_stack_lt_internal
    regs state store hrep hcapacity

/-- The represented catalytic bank satisfies the exact candidate-level
packed-word bound. -/
theorem QueryState.bankWord_lt
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (regs : NeighborhoodTrial.Registers controller)
    (state : NeighborhoodScheduler.State tm instanceData)
    (store : RAM.Structured.Store)
    (hrep : QueryState regs instanceData state store) :
    store regs.layout.bank <
      CandidateParameters.bankRadix
          tm.Q workTapeCount instanceData.candidateTime ^
        CandidateParameters.bankDigitCount
          tm.Q workTapeCount instanceData.candidateTime :=
  Internal.queryState_bank_lt_internal
    regs state store hrep

/-- Once the fixed scalar cells satisfy their scratch envelope, the logical
representation supplies the complete packed-workspace invariant. -/
theorem QueryState.boundedWorkspace
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (regs : NeighborhoodTrial.Registers controller)
    (state : NeighborhoodScheduler.State tm instanceData)
    (store : RAM.Structured.Store)
    (hrep : QueryState regs instanceData state store)
    (hcapacity :
      NeighborhoodScheduler.StackDepth.StackInvariant
        instanceData.horizon state)
    (hfixed : ∀ index,
      store (regs.layout.fixed index) <
        2 ^ NeighborhoodGraph.WorkspaceAccounting.scratchBits
          tm.Q workTapeCount instanceData.candidateTime) :
    NeighborhoodProgram.BoundedWorkspace
      tm.Q workTapeCount instanceData.candidateTime
      (store regs.layout.stack) (store regs.layout.bank)
      (fun index => store (regs.layout.fixed index)) :=
  Internal.queryState_boundedWorkspace_internal
    regs state store hrep hcapacity hfixed

end Representation
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
