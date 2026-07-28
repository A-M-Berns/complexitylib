/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.DenseOverlay.Defs
import Mathlib.Data.Finset.Card

/-!
# Static write footprints for dense-overlay RAM runs

A fixed-register program may read immutable public input indirectly, but every
mutable write must target one of a fixed finite set of direct destinations.
This module states that syntactic invariant and the corresponding overlay
coverage predicate.
-/

namespace Complexity

namespace RAM

namespace RegisterStore

namespace DenseOverlay

namespace FixedRegisters

namespace Footprint

/-- One instruction writes only within `allowed`.

Indirect RAM stores are deliberately rejected. Loads are permitted because
their destination register remains a direct program literal. -/
def InstrWritesWithin (allowed : Finset ℕ) : Instr → Prop
  | .imm destination _ => destination ∈ allowed
  | .add destination _ _ => destination ∈ allowed
  | .sub destination _ _ => destination ∈ allowed
  | .mul destination _ _ => destination ∈ allowed
  | .load destination _ => destination ∈ allowed
  | .store _ _ => False
  | .jz _ _ => True
  | .jmp _ => True
  | .halt => True

/-- Every program-counter lookup writes only within `allowed`, including the
out-of-range default halt instruction. -/
def ProgramWritesWithin (program : Program) (allowed : Finset ℕ) : Prop :=
  ∀ (pc : ℕ), InstrWritesWithin allowed ((program[pc]?).getD .halt)

/-- Every materialized mutable overlay address lies in `allowed`. -/
def Covered (overlay : Store) (allowed : Finset ℕ) : Prop :=
  ∀ entry ∈ overlay, entry.1 ∈ allowed

end Footprint

end FixedRegisters

end DenseOverlay

end RegisterStore

end RAM

end Complexity
