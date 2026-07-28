/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.DenseOverlay.Fixed.Defs
import
  Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.DenseOverlay.Fixed.Internal
import
  Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.DenseOverlay.Footprint

/-!
# Fixed-register dense-overlay bounds

This module turns a uniform bound on a fixed collection of mutable RAM
registers into a bound on every serialized dense-overlay prefix. It is the
representation boundary used by packed-space programs: the public input stays
on the read-only input tape, while vectors and stacks may be packed into a
constant number of natural-valued registers.
-/

namespace Complexity

namespace RAM

namespace RegisterStore

namespace DenseOverlay

namespace FixedRegisters

/-- A fixed-register snapshot occupies at most its explicit codec budget. -/
theorem SnapshotBound.encode_length_le
    {snapshot : Snapshot} {entryBudget wordBits : ℕ}
    (hbound : SnapshotBound snapshot entryBudget wordBits) :
    snapshot.encode.length ≤ codeBudget entryBudget wordBits :=
  Internal.SnapshotBound.encode_length_le_internal hbound

/-- A fixed-register bound on every run prefix yields an actual serialized
dense-overlay trace certificate. -/
theorem TraceBound.toTraceFits
    {program : Program} {input : List Bool}
    {fuel entryBudget wordBits : ℕ}
    (hbound : TraceBound program input fuel entryBudget wordBits) :
    TraceFits program input fuel (codeBudget entryBudget wordBits) :=
  Internal.TraceBound.toTraceFits_internal hbound

/-- Project the fixed-register invariant at one certified prefix. -/
theorem TraceBound.at
    {program : Program} {input : List Bool}
    {fuel entryBudget wordBits k : ℕ}
    (hbound : TraceBound program input fuel entryBudget wordBits)
    (hk : k ≤ fuel) :
    SnapshotBound
      ((Snapshot.initial input).run program input k)
      entryBudget wordBits :=
  Internal.TraceBound.at_internal hbound hk

/-- Restricting the execution horizon preserves a fixed-register trace bound. -/
theorem TraceBound.mono_fuel
    {program : Program} {input : List Bool}
    {fuel fuel' entryBudget wordBits : ℕ}
    (hbound : TraceBound program input fuel entryBudget wordBits)
    (hfuel : fuel' ≤ fuel) :
    TraceBound program input fuel' entryBudget wordBits :=
  Internal.TraceBound.mono_fuel_internal hbound hfuel

end FixedRegisters

end DenseOverlay

end RegisterStore

end RAM

end Complexity
