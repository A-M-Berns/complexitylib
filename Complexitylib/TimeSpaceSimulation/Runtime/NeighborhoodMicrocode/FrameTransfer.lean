/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.FrameTransfer.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.FrameTransfer.Internal

/-!
# First-order transfer of neighborhood-scheduler frames
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace FrameTransfer

variable {controller : SearchProgram.Registers}

/-- Every active-frame transfer destination belongs to the shared evaluator
layout. -/
theorem writeFootprint_subset_layout
    (regs : NeighborhoodTrial.Registers controller) :
    writeFootprint regs ⊆ regs.layout.footprint :=
  Internal.writeFootprint_subset_layout_internal regs

/-- Repeating codec-word division realizes the corresponding pure iteration
of packed-word pop while preserving the radix constants. -/
theorem popMany_runs
    (regs : NeighborhoodTrial.Registers controller)
    (store : RAM.Structured.Store) (base word count : ℕ)
    (hbase : 0 < base)
    (hword :
      store (Layout.frameCodecRegisters regs).word = word)
    (hbaseValue :
      store (Layout.frameCodecRegisters regs).base = base)
    (hbasePred :
      store (Layout.frameCodecRegisters regs).basePred = base - 1)
    (hone :
      store (Layout.frameCodecRegisters regs).one = 1) :
    ∃ final,
      RAM.Structured.Runs (popMany regs count) store final ∧
      final (Layout.frameCodecRegisters regs).word =
        (PackedDigits.pop base)^[count] word ∧
      final (Layout.frameCodecRegisters regs).base = base ∧
      final (Layout.frameCodecRegisters regs).basePred = base - 1 ∧
      final (Layout.frameCodecRegisters regs).one = 1 :=
  Internal.popMany_runs_internal
    regs store base word count hbase hword hbaseValue hbasePred hone

/-- Active-frame encoding writes only inside the shared evaluator layout. -/
theorem encodeActive_writesWithin
    (regs : NeighborhoodTrial.Registers controller) :
    RAM.Structured.Footprint.CmdWritesWithin
      regs.layout.footprint (encodeActive regs) :=
  Internal.encodeActive_writesWithin_internal regs

/-- Active-field encoding has a concrete terminating source-RAM run. -/
theorem encodeActive_runs
    (regs : NeighborhoodTrial.Registers controller)
    (store : RAM.Structured.Store) :
    RAM.Structured.Runs (encodeActive regs) store
      (RAM.Structured.Basic.execList
        (encodeActiveOps regs) store) :=
  Internal.encodeActive_runs_internal regs store

/-- The concrete encoder computes the advertised mixed-radix frame code. -/
theorem encodeActive_frameCode
    (regs : NeighborhoodTrial.Registers controller)
    (store : RAM.Structured.Store) :
    (RAM.Structured.Basic.execList
      (encodeActiveOps regs) store)
        (Layout.frameCode regs) =
      activeCode
        (store (Layout.chunkRadix regs))
        (store (Layout.bankRadix regs))
        (store (Layout.fuel regs))
        (store (Layout.nodeCode regs))
        (store (Layout.scalar regs))
        (store (Layout.out regs))
        (store (Layout.phaseCode regs)) :=
  Internal.encodeActive_frameCode_internal regs store

/-- Active-frame decoding has a concrete terminating run and realizes the
advertised mixed-radix field projection. -/
theorem loadActive_runs
    (regs : NeighborhoodTrial.Registers controller)
    (store : RAM.Structured.Store) (radix bankRadix code : ℕ)
    (hradix : 0 < radix)
    (hword :
      store (Layout.frameCodecRegisters regs).word = code)
    (hbase :
      store (Layout.frameCodecRegisters regs).base = radix)
    (hbank :
      store (Layout.bankRadix regs) = bankRadix) :
    ∃ final,
      RAM.Structured.Runs (loadActive regs) store final ∧
      LoadPost regs radix bankRadix code final :=
  Internal.loadActive_runs_internal
    regs store radix bankRadix code hradix hword hbase hbank

/-- Decoding the fuel coordinate of a fitting frame is exact. -/
theorem decodedFuel_encodeFrame
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    {base : ℕ}
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (hfits : FrameCodec.FrameFits base frame) :
    decodedFuel base (FrameCodec.encodeFrame base frame) =
      frame.fuel :=
  Internal.decodedFuel_encodeFrame_internal frame hfits

/-- Decoding the node subword of a fitting frame is exact. -/
theorem decodedNodeCode_encodeFrame
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    {base : ℕ}
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (hbase : 0 < base)
    (hfits : FrameCodec.FrameFits base frame) :
    decodedNodeCode base (base ^ FrameCodec.scalarDigitCount)
        (FrameCodec.encodeFrame base frame) =
      FrameCodec.encodeNode base frame.node :=
  Internal.decodedNodeCode_encodeFrame_internal frame hbase hfits

/-- A fitting two-digit scalar round-trips through frame decoding. -/
theorem decodedScalar_encodeFrame
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    {base : ℕ}
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (hbase : 0 < base)
    (hfits : FrameCodec.FrameFits base frame)
    (hscalar :
      frame.scalar < base ^ FrameCodec.scalarDigitCount) :
    decodedScalar base (base ^ FrameCodec.scalarDigitCount)
        (FrameCodec.encodeFrame base frame) =
      frame.scalar :=
  Internal.decodedScalar_encodeFrame_internal
    frame hbase hfits hscalar

/-- Decoding the catalytic output coordinate of a fitting frame is exact. -/
theorem decodedOut_encodeFrame
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    {base : ℕ}
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (hfits : FrameCodec.FrameFits base frame) :
    decodedOut base (FrameCodec.encodeFrame base frame) =
      frame.out.val :=
  Internal.decodedOut_encodeFrame_internal frame hfits

/-- Decoding the scheduler-phase subword of a fitting frame is exact. -/
theorem decodedPhase_encodeFrame
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    {base : ℕ}
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (hbase : 0 < base)
    (hfits : FrameCodec.FrameFits base frame) :
    decodedPhase base (FrameCodec.encodeFrame base frame) =
      FrameCodec.encodePhase base frame.phase :=
  Internal.decodedPhase_encodeFrame_internal frame hbase hfits

/-- The concrete decoder restores every observable field of one fitting
scheduler frame. -/
theorem loadActive_encodeFrame_runs
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (regs : NeighborhoodTrial.Registers controller)
    (store : RAM.Structured.Store) (base : ℕ)
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (hbase : 0 < base)
    (hfits : FrameCodec.FrameFits base frame)
    (hscalar :
      frame.scalar < base ^ FrameCodec.scalarDigitCount)
    (hword :
      store (Layout.frameCodecRegisters regs).word =
        FrameCodec.encodeFrame base frame)
    (hbaseValue :
      store (Layout.frameCodecRegisters regs).base = base)
    (hbank :
      store (Layout.bankRadix regs) =
        base ^ FrameCodec.scalarDigitCount) :
    ∃ final,
      RAM.Structured.Runs (loadActive regs) store final ∧
      FrameLoadPost regs base frame final :=
  Internal.loadActive_encodeFrame_runs_internal
    regs store base frame hbase hfits hscalar
      hword hbaseValue hbank

/-- Pushing the active frame adds exactly one least-significant continuation
to the represented packed scheduler stack. -/
theorem pushParent_frame_runs
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (regs : NeighborhoodTrial.Registers controller)
    (store : RAM.Structured.Store) (digitBase frameBase : ℕ)
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (rest : List (NeighborhoodScheduler.Frame tm instanceData))
    (hdigitBase : 0 < digitBase)
    (hscalar :
      frame.scalar < digitBase ^ FrameCodec.scalarDigitCount)
    (hchunkRadix :
      store (Layout.chunkRadix regs) = digitBase)
    (hbankRadix :
      store (Layout.bankRadix regs) =
        digitBase ^ FrameCodec.scalarDigitCount)
    (hfuel : store (Layout.fuel regs) = frame.fuel)
    (hnode :
      store (Layout.nodeCode regs) =
        FrameCodec.encodeNode digitBase frame.node)
    (hscalarValue : store (Layout.scalar regs) = frame.scalar)
    (hout : store (Layout.out regs) = frame.out.val)
    (hphase :
      store (Layout.phaseCode regs) =
        FrameCodec.encodePhase digitBase frame.phase)
    (hframeBase :
      store (Layout.frameStackRegisters regs).base = frameBase)
    (hstack :
      RepresentsStack regs digitBase frameBase rest store) :
    ∃ final,
      RAM.Structured.Runs (pushParent regs) store final ∧
      RepresentsStack regs digitBase frameBase (frame :: rest) final :=
  Internal.pushParent_frame_runs_internal
    regs store digitBase frameBase frame rest hdigitBase hscalar
      hchunkRadix hbankRadix hfuel hnode hscalarValue hout hphase
      hframeBase hstack

/-- Popping an empty represented continuation clears the active-frame flag
and leaves the empty packed stack unchanged. -/
theorem popParent_empty_runs
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (regs : NeighborhoodTrial.Registers controller)
    (store : RAM.Structured.Store) (digitBase frameBase : ℕ)
    (hstack :
      RepresentsStack regs digitBase frameBase
        ([] : List (NeighborhoodScheduler.Frame tm instanceData))
        store) :
    ∃ final,
      RAM.Structured.Runs (popParent regs) store final ∧
      final (Layout.active regs) = 0 ∧
      RepresentsStack regs digitBase frameBase
        ([] : List (NeighborhoodScheduler.Frame tm instanceData))
        final :=
  Internal.popParent_empty_runs_internal
    regs store digitBase frameBase hstack

/-- Popping a nonempty represented continuation restores its top frame
exactly and leaves the packed representation of its tail. -/
theorem popParent_frame_runs
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (regs : NeighborhoodTrial.Registers controller)
    (store : RAM.Structured.Store) (digitBase frameBase : ℕ)
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (rest : List (NeighborhoodScheduler.Frame tm instanceData))
    (hdigitBase : 0 < digitBase)
    (hfits : FrameCodec.FrameFits digitBase frame)
    (hscalar :
      frame.scalar < digitBase ^ FrameCodec.scalarDigitCount)
    (hshiftedFits :
      FrameCodec.encodeFrame digitBase frame + 1 < frameBase)
    (hchunkRadix : store (Layout.chunkRadix regs) = digitBase)
    (hbankRadix :
      store (Layout.bankRadix regs) =
        digitBase ^ FrameCodec.scalarDigitCount)
    (hframeBase :
      store (Layout.frameStackRegisters regs).base = frameBase)
    (hstack :
      RepresentsStack regs digitBase frameBase
        (frame :: rest) store) :
    ∃ final,
      RAM.Structured.Runs (popParent regs) store final ∧
      FrameLoadPost regs digitBase frame final ∧
      RepresentsStack regs digitBase frameBase rest final ∧
      final (Layout.frameStackRegisters regs).base = frameBase :=
  Internal.popParent_frame_runs_internal
    regs store digitBase frameBase frame rest hdigitBase hfits
      hscalar hshiftedFits hchunkRadix hbankRadix hframeBase hstack

/-- Resuming a parent writes only the exact transfer destinations; in
particular, it preserves every retained runtime parameter and the catalytic
bank word. -/
theorem popParent_writesWithin_writeFootprint
    (regs : NeighborhoodTrial.Registers controller) :
    RAM.Structured.Footprint.CmdWritesWithin
      (writeFootprint regs) (popParent regs) :=
  Internal.popParent_writesWithin_writeFootprint_internal regs

/-- Suspending the active parent writes only the exact transfer
destinations, preserving all retained parameters and the catalytic bank. -/
theorem pushParent_writesWithin_writeFootprint
    (regs : NeighborhoodTrial.Registers controller) :
    RAM.Structured.Footprint.CmdWritesWithin
      (writeFootprint regs) (pushParent regs) :=
  Internal.pushParent_writesWithin_writeFootprint_internal regs

/-- Parent suspension actually writes only the stack word and four transfer
scratch cells; all active-frame fields remain read-only. -/
theorem pushParent_writesWithin_pushWriteFootprint
    (regs : NeighborhoodTrial.Registers controller) :
    RAM.Structured.Footprint.CmdWritesWithin
      (pushWriteFootprint regs) (pushParent regs) :=
  Internal.pushParent_writesWithin_pushWriteFootprint_internal regs

/-- Active-frame decoding writes only inside the shared evaluator layout. -/
theorem loadActive_writesWithin
    (regs : NeighborhoodTrial.Registers controller) :
    RAM.Structured.Footprint.CmdWritesWithin
      regs.layout.footprint (loadActive regs) :=
  Internal.loadActive_writesWithin_internal regs

/-- Suspending the active parent writes only inside the evaluator layout. -/
theorem pushParent_writesWithin
    (regs : NeighborhoodTrial.Registers controller) :
    RAM.Structured.Footprint.CmdWritesWithin
      regs.layout.footprint (pushParent regs) :=
  Internal.pushParent_writesWithin_internal regs

/-- Resuming a parent or clearing the active flag writes only inside the
evaluator layout. -/
theorem popParent_writesWithin
    (regs : NeighborhoodTrial.Registers controller) :
    RAM.Structured.Footprint.CmdWritesWithin
      regs.layout.footprint (popParent regs) :=
  Internal.popParent_writesWithin_internal regs

end FrameTransfer
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
