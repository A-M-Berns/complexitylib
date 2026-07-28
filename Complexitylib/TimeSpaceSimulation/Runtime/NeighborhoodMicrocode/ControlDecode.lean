/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.ControlDecode.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.ControlDecode.Internal

/-!
# Concrete control-field decoding for neighborhood microcode

This surface exposes terminating source-RAM executions, exact write
footprints, noninterference with the active-frame ABI, and round trips for
fitting packed node and phase encodings.
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace ControlDecode

open RAM Structured

variable {controller : SearchProgram.Registers}

/-- One quotient/remainder command writes only its four mutable registers. -/
theorem divRem_writesWithin
    (regs : DivisionRegisters) :
    RAM.Structured.Footprint.CmdWritesWithin
      regs.writeFootprint (divRem regs) :=
  Internal.divRem_writesWithin_internal regs

/-- Repeated subtraction computes the exact quotient and remainder while
preserving every address outside its four direct destinations. -/
theorem divRem_runs
    (regs : DivisionRegisters) (store : Store)
    (base input : ℕ)
    (hbase : 0 < base)
    (hvalue : store regs.value = input)
    (hdivisor : store regs.divisor = base) :
    ∃ final,
      Runs (divRem regs) store final ∧
      DivRemPost regs base input store final :=
  Internal.divRem_runs_internal
    regs store base input hbase hvalue hdivisor

/-- Every time-multiplexed decoder cell belongs to the shared evaluator
layout. -/
theorem scratchFootprint_subset_layout
    (regs : NeighborhoodTrial.Registers controller) :
    scratchFootprint regs ⊆ regs.layout.footprint :=
  Internal.scratchFootprint_subset_layout_internal regs

/-- Node decoding writes exactly within the seven-cell decoder footprint. -/
theorem decodeNode_writesWithin
    (regs : NeighborhoodTrial.Registers controller) :
    RAM.Structured.Footprint.CmdWritesWithin
      (scratchFootprint regs) (decodeNode regs) :=
  Internal.decodeNode_writesWithin_internal regs

/-- Phase decoding writes exactly within the seven-cell decoder footprint. -/
theorem decodePhase_writesWithin
    (regs : NeighborhoodTrial.Registers controller) :
    RAM.Structured.Footprint.CmdWritesWithin
      (scratchFootprint regs) (decodePhase regs) :=
  Internal.decodePhase_writesWithin_internal regs

/-- Node decoding writes within the one shared evaluator layout. -/
theorem decodeNode_layout_writesWithin
    (regs : NeighborhoodTrial.Registers controller) :
    RAM.Structured.Footprint.CmdWritesWithin
      regs.layout.footprint (decodeNode regs) :=
  Internal.decodeNode_layout_writesWithin_internal regs

/-- Phase decoding writes within the one shared evaluator layout. -/
theorem decodePhase_layout_writesWithin
    (regs : NeighborhoodTrial.Registers controller) :
    RAM.Structured.Footprint.CmdWritesWithin
      regs.layout.footprint (decodePhase regs) :=
  Internal.decodePhase_layout_writesWithin_internal regs

/-- Every node-decoder execution preserves active fields and parameter
cells. -/
theorem decodeNode_preservesABI
    (regs : NeighborhoodTrial.Registers controller)
    {initial final : Store}
    (hrun : Runs (decodeNode regs) initial final) :
    PreservesABI regs initial final :=
  Internal.decodeNode_preservesABI_internal regs hrun

/-- Every phase-decoder execution preserves active fields and parameter
cells. -/
theorem decodePhase_preservesABI
    (regs : NeighborhoodTrial.Registers controller)
    {initial final : Store}
    (hrun : Runs (decodePhase regs) initial final) :
    PreservesABI regs initial final :=
  Internal.decodePhase_preservesABI_internal regs hrun

/-- The concrete node decoder terminates with the exact arithmetic
projection of an arbitrary packed node word. -/
theorem decodeNode_runs
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store) (base code : ℕ)
    (hbase : 0 < base)
    (hsource : store (Layout.nodeCode regs) = code)
    (hbaseValue : store (Layout.chunkRadix regs) = base) :
    ∃ final,
      Runs (decodeNode regs) store final ∧
      NodePost regs base code final ∧
      PreservesABI regs store final :=
  Internal.decodeNode_runs_internal
    regs store base code hbase hsource hbaseValue

/-- The concrete phase decoder terminates with the exact mixed-radix
projection of an arbitrary packed phase word. -/
theorem decodePhase_runs
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store) (base residueBase code : ℕ)
    (hbase : 0 < base)
    (hresidueBase : 0 < residueBase)
    (hsource : store (Layout.phaseCode regs) = code)
    (hbaseValue : store (Layout.chunkRadix regs) = base)
    (hresidueBaseValue :
      store (Layout.bankRadix regs) = residueBase) :
    ∃ final,
      Runs (decodePhase regs) store final ∧
      PhasePost regs base residueBase code final ∧
      PreservesABI regs store final :=
  Internal.decodePhase_runs_internal regs store base residueBase code
    hbase hresidueBase hsource hbaseValue hresidueBaseValue

/-- A fitting four-digit packed node decodes to its semantic tag, tape, and
payloads. -/
theorem nodeValues_encodeNode
    {base : ℕ}
    (node : NeighborhoodEvaluator.QueryNode workTapeCount horizon)
    (hbase : 0 < base)
    (hfits :
      ∀ digit ∈ FrameCodec.nodeDigits node, digit < base) :
    nodeValues base (FrameCodec.encodeNode base node) =
      expectedNodeValues node :=
  Internal.nodeValues_encodeNode_internal node hbase hfits

/-- A fitting seven-digit packed phase decodes to its semantic residue and
cursor fields. -/
theorem phaseValues_encodePhase
    {base : ℕ}
    (phase : NeighborhoodScheduler.Phase workTapeCount)
    (hbase : 0 < base)
    (hfits :
      ∀ digit ∈ FrameCodec.phaseDigits base phase, digit < base)
    (hresidue :
      (expectedPhaseValues phase).residue <
        base ^ FrameCodec.scalarDigitCount)
    (hresiduesLeft :
      (expectedPhaseValues phase).residuesLeft <
        base ^ FrameCodec.scalarDigitCount) :
    phaseValues base (base ^ FrameCodec.scalarDigitCount)
        (FrameCodec.encodePhase base phase) =
      expectedPhaseValues phase :=
  Internal.phaseValues_encodePhase_internal phase hbase hfits
    hresidue hresiduesLeft

/-- Running the concrete node decoder on a fitting packed node recovers all
semantic fields and preserves the active-frame ABI. -/
theorem decodeNode_encodeNode_runs
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store) (base : ℕ)
    (node : NeighborhoodEvaluator.QueryNode workTapeCount horizon)
    (hbase : 0 < base)
    (hfits :
      ∀ digit ∈ FrameCodec.nodeDigits node, digit < base)
    (hsource :
      store (Layout.nodeCode regs) =
        FrameCodec.encodeNode base node)
    (hbaseValue : store (Layout.chunkRadix regs) = base) :
    ∃ final,
      Runs (decodeNode regs) store final ∧
      NodePost regs base (FrameCodec.encodeNode base node) final ∧
      EncodedNodePost regs node final ∧
      PreservesABI regs store final :=
  Internal.decodeNode_encodeNode_runs_internal
    regs store base node hbase hfits hsource hbaseValue

/-- Running the concrete phase decoder on a fitting packed phase recovers
all semantic fields and preserves the active-frame ABI. -/
theorem decodePhase_encodePhase_runs
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store) (base : ℕ)
    (phase : NeighborhoodScheduler.Phase workTapeCount)
    (hbase : 0 < base)
    (hfits :
      ∀ digit ∈ FrameCodec.phaseDigits base phase, digit < base)
    (hresidue :
      (expectedPhaseValues phase).residue <
        base ^ FrameCodec.scalarDigitCount)
    (hresiduesLeft :
      (expectedPhaseValues phase).residuesLeft <
        base ^ FrameCodec.scalarDigitCount)
    (hsource :
      store (Layout.phaseCode regs) =
        FrameCodec.encodePhase base phase)
    (hbaseValue : store (Layout.chunkRadix regs) = base)
    (hresidueBaseValue :
      store (Layout.bankRadix regs) =
        base ^ FrameCodec.scalarDigitCount) :
    ∃ final,
      Runs (decodePhase regs) store final ∧
      PhasePost regs base (base ^ FrameCodec.scalarDigitCount)
        (FrameCodec.encodePhase base phase) final ∧
      EncodedPhasePost regs phase final ∧
      PreservesABI regs store final :=
  Internal.decodePhase_encodePhase_runs_internal regs store base phase
    hbase hfits hresidue hresiduesLeft hsource hbaseValue
    hresidueBaseValue

/-- Because node decoding preserves the packed phase and both radices, a
phase can be recovered immediately after any node-decoder run. -/
theorem decodePhase_after_decodeNode_runs
    (regs : NeighborhoodTrial.Registers controller)
    {initial middle : Store}
    (hnode : Runs (decodeNode regs) initial middle)
    (base residueBase code : ℕ)
    (hbase : 0 < base)
    (hresidueBase : 0 < residueBase)
    (hsource : initial (Layout.phaseCode regs) = code)
    (hbaseValue : initial (Layout.chunkRadix regs) = base)
    (hresidueBaseValue :
      initial (Layout.bankRadix regs) = residueBase) :
    ∃ final,
      Runs (decodePhase regs) middle final ∧
      PhasePost regs base residueBase code final ∧
      PreservesABI regs middle final := by
  have hpreserved := decodeNode_preservesABI regs hnode
  apply decodePhase_runs regs middle base residueBase code
    hbase hresidueBase
  · rw [hpreserved.phaseCode_eq]
    exact hsource
  · rw [hpreserved.chunkRadix_eq]
    exact hbaseValue
  · rw [hpreserved.bankRadix_eq]
    exact hresidueBaseValue

/-- Because phase decoding preserves the packed node and codec radix, a node
can be recovered immediately after any phase-decoder run. -/
theorem decodeNode_after_decodePhase_runs
    (regs : NeighborhoodTrial.Registers controller)
    {initial middle : Store}
    (hphase : Runs (decodePhase regs) initial middle)
    (base code : ℕ)
    (hbase : 0 < base)
    (hsource : initial (Layout.nodeCode regs) = code)
    (hbaseValue : initial (Layout.chunkRadix regs) = base) :
    ∃ final,
      Runs (decodeNode regs) middle final ∧
      NodePost regs base code final ∧
      PreservesABI regs middle final := by
  have hpreserved := decodePhase_preservesABI regs hphase
  apply decodeNode_runs regs middle base code hbase
  · rw [hpreserved.nodeCode_eq]
    exact hsource
  · rw [hpreserved.chunkRadix_eq]
    exact hbaseValue

end ControlDecode
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
