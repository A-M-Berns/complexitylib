/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.FrameInstall

/-!
# Closing a recursive-descent representation -- proofs
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace Descent
namespace Internal

open RAM Structured

variable {controller : SearchProgram.Registers}

theorem finishPrepare_runs_internal
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
        final := by
  obtain ⟨final, hrun, hpost⟩ :=
    FrameInstall.installPrepareChild_runs regs store
  have hupdatedFuel :
      store (Layout.fuel regs) = updatedParent.fuel := by
    rw [hparentFields.1]
    exact hfuel
  have hupdatedNode :
      store (Layout.nodeCode regs) =
        FrameCodec.encodeNode
          (Representation.digitBase instanceData)
          (updatedParent.childNode child) := by
    simpa [NeighborhoodScheduler.Frame.childNode,
      hparentFields.2.1] using hnode
  have hupdatedOut :
      store (Layout.out regs) =
        (updatedParent.childTarget child).val := by
    simpa [NeighborhoodScheduler.Frame.childTarget,
      hparentFields.2.2.2] using hout
  have hstack :
      Representation.Stack regs
        (updatedParent.prepareChild child :: updatedParent :: rest)
        final :=
    FrameInstall.prepareChild_stack
      regs updatedParent rest child store final hpost
      hupdatedFuel hupdatedNode hupdatedOut hsuspended
  have hchildEq :
      updatedParent.prepareChild child =
        parent.prepareChild child := by
    cases parent
    cases updatedParent
    simp_all [NeighborhoodScheduler.Frame.prepareChild,
      NeighborhoodScheduler.Frame.childNode,
      NeighborhoodScheduler.Frame.childTarget]
  have hbankEq : final regs.layout.bank = store regs.layout.bank :=
    FrameInstall.InstallPost.bank_eq regs hpost
  refine ⟨final, hrun, ?_⟩
  refine
    { parameters :=
        FrameInstall.Parameters.of_installPrepareChild
          regs store final hparameters hrun
      stack := ?_
      bank := ?_
      bank_lt := ?_
      bounds := ?_ }
  · simpa [hchildEq] using hstack
  · rw [hbankEq]
    exact hbank
  · rw [hbankEq]
    exact hbankLt
  · intro frame hframe
    simp only [List.mem_cons] at hframe
    rcases hframe with rfl | rfl | hframe
    · exact
        NeighborhoodScheduler.FrameBounds.FrameBound.prepareChild
          parent child horiginalBound
    · exact hparentBound
    · exact hrestBounds frame hframe

theorem finishCleanup_runs_internal
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
        final := by
  obtain ⟨final, hrun, hpost⟩ :=
    FrameInstall.installCleanupChild_runs regs store
  have hupdatedFuel :
      store (Layout.fuel regs) = updatedParent.fuel := by
    rw [hparentFields.1]
    exact hfuel
  have hupdatedNode :
      store (Layout.nodeCode regs) =
        FrameCodec.encodeNode
          (Representation.digitBase instanceData)
          (updatedParent.childNode child) := by
    simpa [NeighborhoodScheduler.Frame.childNode,
      hparentFields.2.1] using hnode
  have hupdatedOut :
      store (Layout.out regs) =
        (updatedParent.childTarget child).val := by
    simpa [NeighborhoodScheduler.Frame.childTarget,
      hparentFields.2.2.2] using hout
  have hstack :
      Representation.Stack regs
        (updatedParent.cleanupChild child :: updatedParent :: rest)
        final :=
    FrameInstall.cleanupChild_stack
      regs updatedParent rest child store final hpost
      hparameters hupdatedFuel hupdatedNode hupdatedOut hsuspended
  have hchildEq :
      updatedParent.cleanupChild child =
        parent.cleanupChild child := by
    cases parent
    cases updatedParent
    simp_all [NeighborhoodScheduler.Frame.cleanupChild,
      NeighborhoodScheduler.Frame.childNode,
      NeighborhoodScheduler.Frame.childTarget]
  have hbankEq : final regs.layout.bank = store regs.layout.bank :=
    FrameInstall.InstallPost.bank_eq regs hpost
  refine ⟨final, hrun, ?_⟩
  refine
    { parameters :=
        FrameInstall.Parameters.of_installCleanupChild
          regs store final hparameters hrun
      stack := ?_
      bank := ?_
      bank_lt := ?_
      bounds := ?_ }
  · simpa [hchildEq] using hstack
  · rw [hbankEq]
    exact hbank
  · rw [hbankEq]
    exact hbankLt
  · intro frame hframe
    simp only [List.mem_cons] at hframe
    rcases hframe with rfl | rfl | hframe
    · exact
        NeighborhoodScheduler.FrameBounds.FrameBound.cleanupChild
          parent child horiginalBound
    · exact hparentBound
    · exact hrestBounds frame hframe

end Internal
end Descent
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
