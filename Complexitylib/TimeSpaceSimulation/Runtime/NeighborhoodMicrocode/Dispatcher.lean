/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.Dispatcher.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.Dispatcher.Internal

/-!
# Concrete control fragments for neighborhood-scheduler dispatch
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace Dispatcher

open RAM Structured

variable {controller : SearchProgram.Registers}

/-- If each scheduler branch writes only within the shared evaluator layout,
then the uniform five-way phase dispatcher has the same fixed footprint. -/
theorem dispatchPhase_writesWithin
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
      (dispatchPhase regs enter prepare combine cleanupCall cleanupScale) :=
  Internal.dispatchPhase_writesWithin_internal
    regs enter prepare combine cleanupCall cleanupScale
    henter hprepare hcombine hcleanupCall hcleanupScale

/-- A decoded valid phase tag selects exactly its corresponding scheduler
branch.  The selected branch starts with the shared tag cell cleared. -/
theorem dispatchPhase_runs
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
      store final :=
  Internal.dispatchPhase_runs_internal
    regs enter prepare combine cleanupCall cleanupScale store final
    phase hdecoded hone hbranch

/-- Decoding followed by runtime phase selection writes only in the shared
evaluator layout whenever each selected branch does. -/
theorem decodeAndDispatch_writesWithin
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
  Internal.decodeAndDispatch_writesWithin_internal
    regs enter prepare combine cleanupCall cleanupScale
    henter hprepare hcombine hcleanupCall hcleanupScale

/-- On a represented reachable active frame, the uniform decoder and numeric
switch reach exactly the branch selected by the logical scheduler phase. -/
theorem decodeAndDispatch_runs
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
      post final :=
  Internal.decodeAndDispatch_runs_internal
    regs enter prepare combine cleanupCall cleanupScale
    frame store post hactive hparameters hbound hone hbranch

/-- The uniform phase decoder and switch preserve enough information to hand
the complete represented query state to the selected branch proof. -/
theorem decodeAndDispatchQuery_runs
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
      post final :=
  Internal.decodeAndDispatchQuery_runs_internal
    regs enter prepare combine cleanupCall cleanupScale
    frame rest logicalBank store post hquery hone hbranch

/-- If each node-entry branch writes only within the shared evaluator layout,
then the uniform three-way node dispatcher has the same fixed footprint. -/
theorem dispatchNode_writesWithin
    (regs : NeighborhoodTrial.Registers controller)
    (failure source computation : Cmd)
    (hfailure :
      Footprint.CmdWritesWithin regs.layout.footprint failure)
    (hsource :
      Footprint.CmdWritesWithin regs.layout.footprint source)
    (hcomputation :
      Footprint.CmdWritesWithin regs.layout.footprint computation) :
    Footprint.CmdWritesWithin regs.layout.footprint
      (dispatchNode regs failure source computation) :=
  Internal.dispatchNode_writesWithin_internal
    regs failure source computation hfailure hsource hcomputation

/-- A decoded valid node tag selects exactly its corresponding entry branch.
The selected branch starts with the shared tag cell cleared. -/
theorem dispatchNode_runs
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
      store final :=
  Internal.dispatchNode_runs_internal
    regs failure source computation store final node
    hdecoded hone hbranch

/-- Decoding followed by runtime node selection writes only in the shared
evaluator layout whenever each selected branch does. -/
theorem decodeAndDispatchNode_writesWithin
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
  Internal.decodeAndDispatchNode_writesWithin_internal
    regs failure source computation hfailure hsource hcomputation

/-- On a represented reachable active frame, node decoding and numeric
selection reach exactly the branch selected by the logical query node. -/
theorem decodeAndDispatchNode_runs
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
      post final :=
  Internal.decodeAndDispatchNode_runs_internal
    regs failure source computation frame store post hactive
    hparameters hbound hone hbranch

/-- The uniform node decoder and switch preserve enough information to hand
the complete represented query state to the selected branch proof. -/
theorem decodeAndDispatchNodeQuery_runs
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
      post final :=
  Internal.decodeAndDispatchNodeQuery_runs_internal
    regs failure source computation frame rest logicalBank
    store post hquery hone hbranch

/-- Rebuilding one phase code is a concrete terminating source-RAM run. -/
theorem encodePhase_runs
    (regs : NeighborhoodTrial.Registers controller)
    (tag residue residuesLeft child nextChild : ℕ)
    (store : Store) :
    Runs
      (encodePhase regs tag residue residuesLeft child nextChild)
      store
      (Basic.execList
        (encodePhaseOps regs tag residue residuesLeft child nextChild)
        store) :=
  Internal.encodePhase_runs_internal
    regs tag residue residuesLeft child nextChild store

/-- On the decoder ABI, straight-line phase rebuilding computes the exact
mixed-radix numeral from the five decoded fields. -/
theorem encodeDecodedPhase_value
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
        (store (decodedNextChild regs)) :=
  Internal.encodeDecodedPhase_value_internal regs tag store

/-- Rebuilding a phase from the decoder ABI terminates with the exact
mixed-radix value and preserves every non-scratch cell. -/
theorem encodeDecodedPhase_runs
    (regs : NeighborhoodTrial.Registers controller)
    (tag : ℕ) (store : Store) :
    ∃ final,
      Runs
        (encodePhase regs tag
          (decodedResidue regs) (decodedResiduesLeft regs)
          (decodedChild regs) (decodedNextChild regs))
        store final ∧
      EncodePhasePost regs tag store final :=
  Internal.encodeDecodedPhase_runs_internal regs tag store

/-- The mixed-radix cleanup-call numeral is exactly the proof-level phase
codec whenever its two scalar fields fit the two-digit allocation. -/
theorem phaseValue_cleanupCall
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
          NeighborhoodScheduler.Phase workTapeCount) :=
  Internal.phaseValue_cleanupCall_internal
    hbase hresidue hleft

/-- The all-zero enter numeral is exactly the proof-level phase codec. -/
theorem phaseValue_enter
    {workTapeCount base : ℕ} :
    phaseValue base (base ^ FrameCodec.scalarDigitCount)
        0 0 0 0 0 =
      FrameCodec.encodePhase base
        (.enter : NeighborhoodScheduler.Phase workTapeCount) :=
  Internal.phaseValue_enter_internal

/-- The mixed-radix prepare numeral is exactly the proof-level phase codec
whenever its two scalar fields fit the two-digit allocation. -/
theorem phaseValue_prepare
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
          NeighborhoodScheduler.Phase workTapeCount) :=
  Internal.phaseValue_prepare_internal
    hbase hresidue hleft

/-- The mixed-radix combine numeral is exactly the proof-level phase codec
whenever its two scalar fields fit the two-digit allocation. -/
theorem phaseValue_combine
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
          NeighborhoodScheduler.Phase workTapeCount) :=
  Internal.phaseValue_combine_internal
    hbase hresidue hleft

/-- The mixed-radix cleanup-scale numeral is exactly the proof-level phase
codec whenever its two scalar fields fit the two-digit allocation. -/
theorem phaseValue_cleanupScale
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
          NeighborhoodScheduler.Phase workTapeCount) :=
  Internal.phaseValue_cleanupScale_internal
    child hbase hresidue hleft

/-- Re-encoding the semantic fields produced by the phase decoder is an
exact round trip through the proof-level seven-digit phase codec. -/
theorem encodeDecodedPhase_roundtrip_runs
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
        (ControlDecode.expectedPhaseValues phase).tag store final :=
  Internal.encodeDecodedPhase_roundtrip_runs_internal
    regs store base phase hbase hdecoded hresidue hleft
      hbaseValue hbankValue

/-- The cleanup-call encoder terminates and installs the exact mixed-radix
successor phase. -/
theorem encodeCleanupCallPhase_runs
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store) :
    ∃ final,
      Runs (encodeCleanupCallPhase regs) store final ∧
      EncodeCleanupPost regs store final :=
  Internal.encodeCleanupCallPhase_runs_internal regs store

/-- Phase encoding writes only inside the shared evaluator layout. -/
theorem encodePhase_writesWithin
    (regs : NeighborhoodTrial.Registers controller)
    (tag residue residuesLeft child nextChild : ℕ) :
    Footprint.CmdWritesWithin regs.layout.footprint
      (encodePhase regs tag residue residuesLeft child nextChild) :=
  Internal.encodePhase_writesWithin_internal
    regs tag residue residuesLeft child nextChild

/-- Encoding the successor cleanup-call phase stays in the evaluator
layout. -/
theorem encodeCleanupCallPhase_writesWithin
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin regs.layout.footprint
      (encodeCleanupCallPhase regs) :=
  Internal.encodeCleanupCallPhase_writesWithin_internal regs

/-- Saving the active parent fields stays in the evaluator layout. -/
theorem saveActiveFields_writesWithin
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin regs.layout.footprint
      (saveActiveFields regs) :=
  Internal.saveActiveFields_writesWithin_internal regs

/-- Saving active parent fields terminates with the advertised exact
preservation relation. -/
theorem saveActiveFields_runs
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store) :
    ∃ final,
      Runs (saveActiveFields regs) store final ∧
      SaveActivePost regs store final :=
  Internal.saveActiveFields_runs_internal regs store

/-- Restoring the active parent fields stays in the evaluator layout. -/
theorem restoreActiveFields_writesWithin
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin regs.layout.footprint
      (restoreActiveFields regs) :=
  Internal.restoreActiveFields_writesWithin_internal regs

/-- Restoring active parent fields terminates with the advertised exact
preservation relation. -/
theorem restoreActiveFields_runs
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store) :
    ∃ final,
      Runs (restoreActiveFields regs) store final ∧
      RestoreActivePost regs store final :=
  Internal.restoreActiveFields_runs_internal regs store

/-- Dynamic child-target selection stays in the evaluator layout. -/
theorem selectChildTarget_writesWithin
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin regs.layout.footprint
      (selectChildTarget regs) :=
  Internal.selectChildTarget_writesWithin_internal regs

/-- Dynamic child-target selection terminates and computes the natural
`succAbove` representative. -/
theorem selectChildTarget_runs
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store)
    (hone : store (cleanupInverseRegisters regs).one = 1) :
    ∃ final,
      Runs (selectChildTarget regs) store final ∧
      ChildTargetPost regs store final :=
  Internal.selectChildTarget_runs_internal regs store hone

/-- The natural branch computed by `selectChildTarget` is exactly the
standard finite-coordinate embedding around the parent output. -/
theorem childTargetValue_eq_succAbove
    {n : ℕ} (out : Fin (n + 1)) (child : Fin n) :
    (if child.val < out.val then child.val else child.val + 1) =
      (out.succAbove child).val :=
  Internal.childTargetValue_eq_succAbove_internal out child

/-- The complete cleanup-scale fragment has a fixed direct-write footprint. -/
theorem cleanupScale_writesWithin
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin regs.layout.footprint
      (cleanupScale regs) :=
  Internal.cleanupScale_writesWithin_internal regs

/-- The cleanup-scale fragment computes the inverse-residue scaling at the
selected child coordinate, advances to the next cleanup call, and restores
the active parent scalars. -/
theorem cleanupScale_runs
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
        regs store final :=
  Internal.cleanupScale_runs_internal
    tm blockLength scalar residue residuesLeft nextChild
    digitBase bankBase word original out child regs store hprime
    hdigitBase hbankBase hmodulusBase hresidueLt
    hresidueDigits hleftDigits hword hrep hwordLt hbaseValue
    hmodulusValue hmodulusPred hone hscalar hout hchunkCount
    hchunkRadix hbankRadix hdecodedResidue hdecodedResiduesLeft
    hdecodedChild hdecodedNextChild

end Dispatcher
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
