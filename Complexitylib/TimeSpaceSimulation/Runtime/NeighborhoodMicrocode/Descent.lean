/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.Descent.Internal

/-!
# Closing a recursive-descent representation

These theorems close the last straight-line installation step once the parent
has been suspended, the child node and target have been regenerated, and the
logical catalytic-bank update has been established.
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace Descent

open RAM Structured

variable {controller : SearchProgram.Registers}

/-- Installing a prepared child turns the suspended-parent representation
into the exact complete successor query state. -/
theorem finishPrepare_runs
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (regs : NeighborhoodTrial.Registers controller)
    (parent : NeighborhoodScheduler.Frame tm instanceData)
    (updatedParent : NeighborhoodScheduler.Frame tm instanceData)
    (rest : List (NeighborhoodScheduler.Frame tm instanceData))
    (child :
      Fin (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount))
    (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (store : Store)
    (hparentFields :
      updatedParent.fuel = parent.fuel ∧
      updatedParent.node = parent.node ∧
      updatedParent.scalar = parent.scalar ∧
      updatedParent.out = parent.out)
    (hsuspended :
      FrameTransfer.RepresentsStack regs
        (Representation.digitBase instanceData)
        (Representation.frameBase instanceData)
        (updatedParent :: rest) store)
    (hparameters :
      Representation.Parameters regs instanceData store)
    (hbank :
      NeighborhoodProgram.RepresentsResidueBank
        tm instanceData.blockLength
        (Representation.fieldBase instanceData)
        (store regs.layout.bank) logicalBank)
    (hbankLt :
      store regs.layout.bank <
        Representation.fieldBase instanceData ^
          ((NeighborhoodExecutableEvaluation.graphFanIn
              workTapeCount + 1) *
            TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
              (NeighborhoodExecutableEvaluation.payloadWidth
                tm instanceData.blockLength)
              (NeighborhoodExecutableEvaluation.graphFanIn
                workTapeCount)))
    (hfuel : store (Layout.fuel regs) = parent.fuel)
    (hnode :
      store (Layout.nodeCode regs) =
        FrameCodec.encodeNode
          (Representation.digitBase instanceData)
          (parent.childNode child))
    (hout :
      store (Layout.out regs) = (parent.childTarget child).val)
    (horiginalBound :
      NeighborhoodScheduler.FrameBounds.FrameBound parent)
    (hparentBound :
      NeighborhoodScheduler.FrameBounds.FrameBound updatedParent)
    (hrestBounds :
      ∀ frame ∈ rest,
        NeighborhoodScheduler.FrameBounds.FrameBound frame) :
    ∃ final,
      Runs (FrameInstall.installPrepareChild regs) store final ∧
      Representation.QueryState regs instanceData
        { stack :=
            parent.prepareChild child :: updatedParent :: rest
          registers := logicalBank }
        final :=
  Internal.finishPrepare_runs_internal
    regs parent updatedParent rest child logicalBank store
    hparentFields hsuspended hparameters hbank hbankLt
    hfuel hnode hout horiginalBound hparentBound hrestBounds

/-- Installing a cleanup child turns the suspended-parent representation
into the exact complete successor query state. -/
theorem finishCleanup_runs
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (regs : NeighborhoodTrial.Registers controller)
    (parent : NeighborhoodScheduler.Frame tm instanceData)
    (updatedParent : NeighborhoodScheduler.Frame tm instanceData)
    (rest : List (NeighborhoodScheduler.Frame tm instanceData))
    (child :
      Fin (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount))
    (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (store : Store)
    (hparentFields :
      updatedParent.fuel = parent.fuel ∧
      updatedParent.node = parent.node ∧
      updatedParent.scalar = parent.scalar ∧
      updatedParent.out = parent.out)
    (hsuspended :
      FrameTransfer.RepresentsStack regs
        (Representation.digitBase instanceData)
        (Representation.frameBase instanceData)
        (updatedParent :: rest) store)
    (hparameters :
      Representation.Parameters regs instanceData store)
    (hbank :
      NeighborhoodProgram.RepresentsResidueBank
        tm instanceData.blockLength
        (Representation.fieldBase instanceData)
        (store regs.layout.bank) logicalBank)
    (hbankLt :
      store regs.layout.bank <
        Representation.fieldBase instanceData ^
          ((NeighborhoodExecutableEvaluation.graphFanIn
              workTapeCount + 1) *
            TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
              (NeighborhoodExecutableEvaluation.payloadWidth
                tm instanceData.blockLength)
              (NeighborhoodExecutableEvaluation.graphFanIn
                workTapeCount)))
    (hfuel : store (Layout.fuel regs) = parent.fuel)
    (hnode :
      store (Layout.nodeCode regs) =
        FrameCodec.encodeNode
          (Representation.digitBase instanceData)
          (parent.childNode child))
    (hout :
      store (Layout.out regs) = (parent.childTarget child).val)
    (horiginalBound :
      NeighborhoodScheduler.FrameBounds.FrameBound parent)
    (hparentBound :
      NeighborhoodScheduler.FrameBounds.FrameBound updatedParent)
    (hrestBounds :
      ∀ frame ∈ rest,
        NeighborhoodScheduler.FrameBounds.FrameBound frame) :
    ∃ final,
      Runs (FrameInstall.installCleanupChild regs) store final ∧
      Representation.QueryState regs instanceData
        { stack :=
            parent.cleanupChild child :: updatedParent :: rest
          registers := logicalBank }
        final :=
  Internal.finishCleanup_runs_internal
    regs parent updatedParent rest child logicalBank store
    hparentFields hsuspended hparameters hbank hbankLt
    hfuel hnode hout horiginalBound hparentBound hrestBounds

end Descent
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
