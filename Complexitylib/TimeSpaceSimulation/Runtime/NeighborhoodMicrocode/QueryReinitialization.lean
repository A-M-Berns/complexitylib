/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.QueryReinitialization.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.QueryReinitialization.Internal

/-!
# Reinitializing a query while retaining the catalytic bank
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace QueryReinitialization

open RAM Structured
open NeighborhoodExecutableEvaluation

variable {controller : SearchProgram.Registers}

/-- Bank-preserving query reinitialization writes only in the evaluator
layout. -/
theorem reinitialize_writesWithin
    (workTapeCount : ℕ)
    (regs : NeighborhoodTrial.Registers controller)
    (out : Fin (graphFanIn workTapeCount + 1)) :
    Footprint.CmdWritesWithin regs.layout.footprint
      (reinitializeQuery workTapeCount regs out) :=
  Internal.reinitialize_writesWithin_internal
    workTapeCount regs out

/-- A prebuilt bounded root replaces the continuation stack using only the
retained runtime parameters and packed catalytic bank. No representation of
the overwritten old frame is required. -/
theorem reinitialize_from_bank_runs
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
        final :=
  Internal.reinitialize_from_bank_runs_internal
    regs instanceData registers node out store
    hparameters hbank hbankLt hnodeCode hnodeBound

/-- A prebuilt bounded root replaces the represented continuation stack while
the complete logical catalytic bank is retained. -/
theorem reinitialize_runs
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
  Internal.reinitialize_runs_internal
    regs instanceData state node out store hquery hnodeCode hnodeBound

/-- Bank-based reinitialization also preserves the public input frame and
every read-only controller value needed by the following query loop. -/
theorem reinitialize_from_bank_runs_preserving_abi
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
      final controller.guess = word :=
  Internal.reinitialize_from_bank_runs_preserving_abi_internal
    controller regs instanceData registers node out word store
    hparameters hbank hbankLt hnodeCode hnodeBound
    hframe hinputLength hone hguess

/-- Bank-preserving reinitialization also preserves the public input frame
and every read-only controller value needed by the following query loop. -/
theorem reinitialize_runs_preserving_abi
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
  Internal.reinitialize_runs_preserving_abi_internal
    controller regs instanceData state node out word store
    hquery hnodeCode hnodeBound hframe hinputLength hone hguess

end QueryReinitialization
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
