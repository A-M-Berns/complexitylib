/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.CombineSafeCenter.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.CombineSafeCenter.Internal

/-!
# Combine-safe guessed-center reconstruction

This surface exposes a uniform runtime decoder for
`ChildNode.derivedCenterValue` whose eleven mutable cells are all ordinary
combine scratch. It preserves the outer range, active computation context,
packed continuation stack, and catalytic bank.
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace CombineSafeCenter

open RAM Structured

variable {controller : SearchProgram.Registers}

/-- Center reconstruction writes only its eleven scratch cells. -/
theorem deriveCenter_writesWithin
    (workTapeCount : ℕ)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (footprint regs)
      (deriveCenter workTapeCount controller regs) :=
  Internal.deriveCenter_writesWithin_internal
    workTapeCount controller regs

/-- Compiling center reconstruction preserves the same fixed write
footprint as its structured source command. -/
theorem deriveCenter_compiledWritesWithin
    (workTapeCount : ℕ)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) :
    RAM.RegisterStore.DenseOverlay.FixedRegisters.Footprint.ProgramWritesWithin
      (deriveCenter workTapeCount controller regs).compile
      (footprint regs) :=
  Internal.deriveCenter_compiledWritesWithin_internal
    workTapeCount controller regs

/-- Every center-decoder destination is inside the range term kernel's
advertised combine-scratch footprint. -/
theorem footprint_subset_combineScratch
    (regs : NeighborhoodTrial.Registers controller) :
    footprint regs ⊆ CombineValue.combineScratchFootprint regs :=
  Internal.footprint_subset_combineScratch_internal regs

/-- A center-decoder execution preserves every live combine range and stable
computation-context field. -/
theorem deriveCenter_preservesCombine
    (workTapeCount : ℕ)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    {initial final : Store}
    (hrun :
      Runs (deriveCenter workTapeCount controller regs)
        initial final) :
    PreservesCombine regs initial final :=
  Internal.deriveCenter_preservesCombine_internal
    workTapeCount controller regs hrun

/-- The concrete scan terminates with exactly
`ChildNode.derivedCenterValue`, while preserving every address outside its
scratch-only footprint. -/
theorem deriveCenter_runs
    (workTapeCount : ℕ)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store) (word tape interval : ℕ)
    (hguess : store controller.guess = word)
    (htape : store (ControlDecode.nodeTape regs) = tape)
    (hinterval :
      store (ControlDecode.nodePayload1 regs) = interval) :
    ∃ final,
      Runs (deriveCenter workTapeCount controller regs) store final ∧
      Post workTapeCount word tape interval
        controller regs store final :=
  Internal.deriveCenter_runs_internal
    workTapeCount controller regs store word tape interval
    hguess htape hinterval

end CombineSafeCenter
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
