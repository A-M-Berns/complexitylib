/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.FrameInstall.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.FrameInstall.Internal

/-!
# Active child-frame installation
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace FrameInstall

open RAM Structured

variable {controller : SearchProgram.Registers}

/-- Prepare-child installation writes only its exact four active-frame
destinations. -/
theorem installPrepareChild_writesWithin
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin
      (writeFootprint regs) (installPrepareChild regs) :=
  Internal.installPrepareChild_writesWithin_internal regs

/-- Cleanup-child installation writes only its exact four active-frame
destinations. -/
theorem installCleanupChild_writesWithin
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin
      (writeFootprint regs) (installCleanupChild regs) :=
  Internal.installCleanupChild_writesWithin_internal regs

/-- Every child-installation destination belongs to the evaluator layout. -/
theorem writeFootprint_subset_layout
    (regs : NeighborhoodTrial.Registers controller) :
    writeFootprint regs ⊆ regs.layout.footprint :=
  Internal.writeFootprint_subset_layout_internal regs

/-- The prepare installer has an exact terminating execution. -/
theorem installPrepareChild_runs
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store) :
    ∃ final,
      Runs (installPrepareChild regs) store final ∧
      InstallPost regs 1 store final :=
  Internal.installPrepareChild_runs_internal regs store

/-- The cleanup installer has an exact terminating execution. -/
theorem installCleanupChild_runs
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store) :
    ∃ final,
      Runs (installCleanupChild regs) store final ∧
      InstallPost regs (store (Layout.modulusPred regs)) store final :=
  Internal.installCleanupChild_runs_internal regs store

/-- Prepare-child installation preserves every retained runtime parameter. -/
theorem Parameters.of_installPrepareChild
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (regs : NeighborhoodTrial.Registers controller)
    (initial final : Store)
    (hparameters : Representation.Parameters regs instanceData initial)
    (hrun : Runs (installPrepareChild regs) initial final) :
    Representation.Parameters regs instanceData final :=
  Internal.parameters_of_installPrepareChild_internal
    regs initial final hparameters hrun

/-- Cleanup-child installation preserves every retained runtime parameter. -/
theorem Parameters.of_installCleanupChild
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (regs : NeighborhoodTrial.Registers controller)
    (initial final : Store)
    (hparameters : Representation.Parameters regs instanceData initial)
    (hrun : Runs (installCleanupChild regs) initial final) :
    Representation.Parameters regs instanceData final :=
  Internal.parameters_of_installCleanupChild_internal
    regs initial final hparameters hrun

/-- Either child installer leaves the catalytic bank word unchanged. -/
theorem InstallPost.bank_eq
    (regs : NeighborhoodTrial.Registers controller)
    {initial final : Store}
    (hpost : InstallPost regs scalar initial final) :
    final regs.layout.bank = initial regs.layout.bank :=
  Internal.installPost_bank_eq_internal regs hpost

/-- The prepare installer turns a regenerated child node and target into the
exact semantic prepare-child frame. -/
theorem prepareChild_activeFrame
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (regs : NeighborhoodTrial.Registers controller)
    (parent : NeighborhoodScheduler.Frame tm instanceData)
    (child :
      Fin (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount))
    (initial final : Store)
    (hpost : InstallPost regs 1 initial final)
    (hfuel : initial (Layout.fuel regs) = parent.fuel)
    (hnode :
      initial (Layout.nodeCode regs) =
        FrameCodec.encodeNode
          (Representation.digitBase instanceData)
          (parent.childNode child))
    (hout :
      initial (Layout.out regs) = (parent.childTarget child).val) :
    Representation.ActiveFrame regs (parent.prepareChild child) final :=
  Internal.prepareChild_activeFrame_internal
    regs parent child initial final hpost hfuel hnode hout

/-- Once the parent has been suspended, prepare-child installation produces
the exact semantic child-parent stack. -/
theorem prepareChild_stack
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (regs : NeighborhoodTrial.Registers controller)
    (parent : NeighborhoodScheduler.Frame tm instanceData)
    (rest : List (NeighborhoodScheduler.Frame tm instanceData))
    (child :
      Fin (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount))
    (initial final : Store)
    (hpost : InstallPost regs 1 initial final)
    (hfuel : initial (Layout.fuel regs) = parent.fuel)
    (hnode :
      initial (Layout.nodeCode regs) =
        FrameCodec.encodeNode
          (Representation.digitBase instanceData)
          (parent.childNode child))
    (hout :
      initial (Layout.out regs) = (parent.childTarget child).val)
    (hstack :
      FrameTransfer.RepresentsStack regs
        (Representation.digitBase instanceData)
        (Representation.frameBase instanceData)
        (parent :: rest) initial) :
    Representation.Stack regs
      (parent.prepareChild child :: parent :: rest) final :=
  Internal.prepareChild_stack_internal
    regs parent rest child initial final hpost hfuel hnode hout hstack

/-- The cleanup installer turns a regenerated child node and target into the
exact semantic cleanup-child frame. -/
theorem cleanupChild_activeFrame
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (regs : NeighborhoodTrial.Registers controller)
    (parent : NeighborhoodScheduler.Frame tm instanceData)
    (child :
      Fin (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount))
    (initial final : Store)
    (hpost :
      InstallPost regs (initial (Layout.modulusPred regs)) initial final)
    (hparameters :
      Representation.Parameters regs instanceData initial)
    (hfuel : initial (Layout.fuel regs) = parent.fuel)
    (hnode :
      initial (Layout.nodeCode regs) =
        FrameCodec.encodeNode
          (Representation.digitBase instanceData)
          (parent.childNode child))
    (hout :
      initial (Layout.out regs) = (parent.childTarget child).val) :
    Representation.ActiveFrame regs (parent.cleanupChild child) final :=
  Internal.cleanupChild_activeFrame_internal
    regs parent child initial final hpost hparameters hfuel hnode hout

/-- Once the parent has been suspended, cleanup-child installation produces
the exact semantic child-parent stack. -/
theorem cleanupChild_stack
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (regs : NeighborhoodTrial.Registers controller)
    (parent : NeighborhoodScheduler.Frame tm instanceData)
    (rest : List (NeighborhoodScheduler.Frame tm instanceData))
    (child :
      Fin (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount))
    (initial final : Store)
    (hpost :
      InstallPost regs (initial (Layout.modulusPred regs)) initial final)
    (hparameters :
      Representation.Parameters regs instanceData initial)
    (hfuel : initial (Layout.fuel regs) = parent.fuel)
    (hnode :
      initial (Layout.nodeCode regs) =
        FrameCodec.encodeNode
          (Representation.digitBase instanceData)
          (parent.childNode child))
    (hout :
      initial (Layout.out regs) = (parent.childTarget child).val)
    (hstack :
      FrameTransfer.RepresentsStack regs
        (Representation.digitBase instanceData)
        (Representation.frameBase instanceData)
        (parent :: rest) initial) :
    Representation.Stack regs
      (parent.cleanupChild child :: parent :: rest) final :=
  Internal.cleanupChild_stack_internal
    regs parent rest child initial final hpost hparameters
    hfuel hnode hout hstack

end FrameInstall
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
