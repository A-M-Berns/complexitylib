/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.DenseOverlay
import
  Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.DenseOverlay.Fixed.Defs
import Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore

/-!
# Proof internals for fixed-register dense-overlay bounds
-/

namespace Complexity

namespace RAM

namespace RegisterStore

namespace DenseOverlay

namespace FixedRegisters

namespace Internal

theorem SnapshotBound.encode_length_le_internal
    {snapshot : Snapshot} {entryBudget wordBits : ℕ}
    (hbound : SnapshotBound snapshot entryBudget wordBits) :
    snapshot.encode.length ≤ codeBudget entryBudget wordBits := by
  have hcount :
      bitlen snapshot.overlay.length ≤ wordBits :=
    (Nat.size_le_size hbound.entryCount).trans
      hbound.entryBudgetWidth
  change
    (RegisterStore.Snapshot.encode
      { pc := snapshot.pc, store := snapshot.overlay }).length ≤
        codeBudget entryBudget wordBits
  exact (RegisterStore.Snapshot.encode_length_le
    { pc := snapshot.pc, store := snapshot.overlay }
    wordBits hbound.pcWidth hcount hbound.entries).trans
      (by
        simp only [codeBudget]
        exact Nat.mul_le_mul_right (4 * wordBits + 2)
          (Nat.add_le_add_right hbound.entryCount 1))

theorem TraceBound.toTraceFits_internal
    {program : Program} {input : List Bool}
    {fuel entryBudget wordBits : ℕ}
    (hbound : TraceBound program input fuel entryBudget wordBits) :
    TraceFits program input fuel (codeBudget entryBudget wordBits) := by
  intro k hk
  exact SnapshotBound.encode_length_le_internal (hbound k hk)

theorem TraceBound.at_internal
    {program : Program} {input : List Bool}
    {fuel entryBudget wordBits k : ℕ}
    (hbound : TraceBound program input fuel entryBudget wordBits)
    (hk : k ≤ fuel) :
    SnapshotBound
      ((Snapshot.initial input).run program input k)
      entryBudget wordBits :=
  hbound k hk

theorem TraceBound.mono_fuel_internal
    {program : Program} {input : List Bool}
    {fuel fuel' entryBudget wordBits : ℕ}
    (hbound : TraceBound program input fuel entryBudget wordBits)
    (hfuel : fuel' ≤ fuel) :
    TraceBound program input fuel' entryBudget wordBits := by
  intro k hk
  exact hbound k (hk.trans hfuel)

end Internal

end FixedRegisters

end DenseOverlay

end RegisterStore

end RAM

end Complexity
