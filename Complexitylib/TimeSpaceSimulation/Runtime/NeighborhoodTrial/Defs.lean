/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.CandidateParameters.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.SearchProgram.Defs

/-!
# Register allocation for a concrete neighborhood trial

This definitions layer gives the candidate-parameter program and the packed
neighborhood evaluator one shared fixed workspace. Thirty-two registers hold
the parameter outputs and reusable scalar scratch; two further registers hold
the packed continuation stack and catalytic bank. The workspace is disjoint
from all seventeen outer-controller registers.

The public kernel footprint adds precisely the three controller destinations
that one trial is allowed to write: `success`, `verdict`, and `hasNext`.
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodTrial

open RAM Structured

/-- A thirty-four-register workspace disjoint from an outer search
controller. -/
structure Registers (controller : SearchProgram.Registers) where
  /-- Physical allocation for thirty-two scalar registers and two packed
  words. -/
  index : Fin 34 → ℕ
  /-- Workspace logical fields occupy distinct physical registers. -/
  injective : Function.Injective index
  /-- No workspace register aliases an outer-controller register. -/
  index_ne_controller :
    ∀ workspaceSlot controllerSlot,
      index workspaceSlot ≠ controller.index controllerSlot

namespace Registers

/-- Canonical workspace immediately above the canonical controller prefix. -/
def canonical : Registers SearchProgram.Registers.canonical where
  index := fun slot => slot.val + 17
  injective := by
    intro first second heq
    apply Fin.ext
    exact Nat.add_right_cancel heq
  index_ne_controller := by
    intro workspaceSlot controllerSlot
    have hcontroller :=
      SearchProgram.Registers.canonical_index_lt controllerSlot
    intro heq
    change workspaceSlot.val + 17 =
      SearchProgram.Registers.canonical.index controllerSlot at heq
    omega

/-- Embed one scalar/parameter slot into the shared workspace. -/
def fixedSlot (slot : Fin NeighborhoodProgram.fixedRegisterCount) :
    Fin 34 :=
  ⟨slot.val, by
    have hslot := slot.isLt
    change slot.val < 32 at hslot
    omega⟩

/-- Candidate-parameter view of the first thirty-two workspace registers.

The candidate itself remains the outer controller's read-only candidate
register. -/
def parameters
    (regs : Registers controller) :
    CandidateParameters.Registers where
  candidate := controller.candidate
  index := fun slot => regs.index (fixedSlot slot)
  injective := by
    intro first second heq
    have hslots := regs.injective heq
    have hval :
        (fixedSlot first).val = (fixedSlot second).val :=
      congrArg (fun slot : Fin 34 => slot.val) hslots
    exact Fin.ext hval
  candidate_ne := by
    intro slot
    exact
      (regs.index_ne_controller (fixedSlot slot) (1 : Fin 17)).symm

/-- Packed evaluator layout sharing its scalar fields with the parameter
program. -/
def layout (regs : Registers controller) : NeighborhoodProgram.Layout where
  stack := regs.index 32
  bank := regs.index 33
  fixed := fun slot => regs.index (fixedSlot slot)

/-- The only outer-controller destinations written by a trial. -/
def outputFootprint (controller : SearchProgram.Registers) : Finset ℕ :=
  {controller.success, controller.verdict, controller.hasNext}

/-- One exact mutable footprint for parameter setup, packed evaluation, and
the three trial outputs. -/
def footprint (regs : Registers controller) : Finset ℕ :=
  regs.layout.footprint ∪ outputFootprint controller

/-- Runtime candidate-parameter setup performed before neighborhood
evaluation. -/
def parameterProgram
    (Q : Type*) [Fintype Q]
    (workTapeCount : ℕ)
    (regs : Registers controller) : Cmd :=
  CandidateParameters.program Q workTapeCount regs.parameters

end Registers

end NeighborhoodTrial
end Runtime
end TimeSpaceSimulation
end Complexity
