/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.FrameTransfer.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodScheduler.FrameBounds.Defs

/-!
# Logical representation of neighborhood-scheduler query states

This definitions layer relates a pure scheduler state to the concrete packed
stack, active-frame fields, catalytic bank, and preserved runtime parameters.
The active frame remains in fixed registers; only its suspended tail is stored
in the packed continuation word.
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace Representation

open NeighborhoodExecutableEvaluation

variable {controller : SearchProgram.Registers}

/-- Canonical one-chunk radix for one runtime instance. -/
def digitBase
    {tm : TM workTapeCount}
    (instanceData : NeighborhoodProgram.ResidueInstance tm) : ℕ :=
  CandidateParameters.domainSize
    tm.Q workTapeCount instanceData.candidateTime

/-- Canonical suspended-frame radix for one runtime instance. -/
def frameBase
    {tm : TM workTapeCount}
    (instanceData : NeighborhoodProgram.ResidueInstance tm) : ℕ :=
  CandidateParameters.frameRadix
    tm.Q workTapeCount instanceData.candidateTime

/-- Canonical two-chunk radix for one field residue. -/
def fieldBase
    {tm : TM workTapeCount}
    (instanceData : NeighborhoodProgram.ResidueInstance tm) : ℕ :=
  digitBase instanceData ^ FrameCodec.scalarDigitCount

/-- Runtime parameter cells retained throughout concrete query execution. -/
structure Parameters
    {tm : TM workTapeCount}
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (store : RAM.Structured.Store) : Prop where
  /-- The canonical block length is retained. -/
  blockLength_eq :
    store (Layout.blockLength regs) = instanceData.blockLength
  /-- The canonical interval horizon is retained. -/
  horizon_eq :
    store (Layout.horizon regs) = instanceData.horizon
  /-- The one-chunk frame radix is retained. -/
  digitBase_eq :
    store (Layout.chunkRadix regs) = digitBase instanceData
  /-- The two-digit field radix is retained. -/
  bankBase_eq :
    store (Layout.bankRadix regs) = fieldBase instanceData
  /-- The twenty-four-digit suspended-frame radix is retained. -/
  frameBase_eq :
    store (Layout.frameRadix regs) = frameBase instanceData
  /-- The grouped-coordinate count is retained. -/
  chunkCount_eq :
    store (Layout.chunkCount regs) =
      TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
        (payloadWidth tm instanceData.blockLength)
        (graphFanIn workTapeCount)
  /-- The complete catalytic-bank coordinate count is retained. -/
  bankDigitCount_eq :
    store (Layout.bankDigitCount regs) =
      (graphFanIn workTapeCount + 1) *
        TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
          (payloadWidth tm instanceData.blockLength)
          (graphFanIn workTapeCount)
  /-- The canonical searched field modulus is retained. -/
  modulus_eq :
    store (Layout.modulus regs) =
      NeighborhoodScheduler.fieldModulus instanceData
  /-- The modulus predecessor used by reduction loops is retained. -/
  modulusPred_eq :
    store (Layout.modulusPred regs) =
      NeighborhoodScheduler.fieldModulus instanceData - 1

/-- The six active scalar cells exactly encode one logical scheduler frame. -/
structure ActiveFrame
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (regs : NeighborhoodTrial.Registers controller)
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (store : RAM.Structured.Store) : Prop where
  /-- Recursion fuel is represented literally. -/
  fuel_eq :
    store (Layout.fuel regs) = frame.fuel
  /-- The query node uses the fixed four-digit codec. -/
  node_eq :
    store (Layout.nodeCode regs) =
      FrameCodec.encodeNode (digitBase instanceData) frame.node
  /-- The field scalar is represented literally. -/
  scalar_eq :
    store (Layout.scalar regs) = frame.scalar
  /-- The catalytic output coordinate is represented literally. -/
  out_eq :
    store (Layout.out regs) = frame.out.val
  /-- The control phase uses the fixed seven-digit codec. -/
  phase_eq :
    store (Layout.phaseCode regs) =
      FrameCodec.encodePhase (digitBase instanceData) frame.phase
  /-- A represented active frame sets the evaluator loop flag. -/
  active_eq :
    store (Layout.active regs) = 1

/-- The active frame and packed suspended tail represent one logical stack. -/
def Stack
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (regs : NeighborhoodTrial.Registers controller)
    (frames : List (NeighborhoodScheduler.Frame tm instanceData))
    (store : RAM.Structured.Store) : Prop :=
  match frames with
  | [] =>
      store (Layout.active regs) = 0 ∧
        FrameTransfer.RepresentsStack regs
          (digitBase instanceData) (frameBase instanceData)
          ([] :
            List (NeighborhoodScheduler.Frame tm instanceData))
          store
  | frame :: rest =>
      ActiveFrame regs frame store ∧
        FrameTransfer.RepresentsStack regs
          (digitBase instanceData) (frameBase instanceData) rest store

/-- Complete concrete representation of one pure query-scheduler state. -/
structure QueryState
    {tm : TM workTapeCount}
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (state : NeighborhoodScheduler.State tm instanceData)
    (store : RAM.Structured.Store) : Prop where
  /-- Runtime parameters agree with the selected instance. -/
  parameters : Parameters regs instanceData store
  /-- The active frame and suspended stack agree with the logical stack. -/
  stack : Stack regs state.stack store
  /-- The packed catalytic bank agrees with the logical register family. -/
  bank :
    NeighborhoodProgram.RepresentsResidueBank
      tm instanceData.blockLength (fieldBase instanceData)
      (store regs.layout.bank) state.registers
  /-- The canonical packed bank has no nonzero digits above its advertised
  row-major coordinates. -/
  bank_lt :
    store regs.layout.bank <
      fieldBase instanceData ^
        ((graphFanIn workTapeCount + 1) *
          TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
            (payloadWidth tm instanceData.blockLength)
            (graphFanIn workTapeCount))
  /-- Every live logical frame satisfies the codec's numeric invariant. -/
  bounds : NeighborhoodScheduler.FrameBounds.StateBound state

end Representation
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
