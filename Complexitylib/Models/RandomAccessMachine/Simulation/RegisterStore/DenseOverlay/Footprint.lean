/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.DenseOverlay.Footprint.Defs
import
  Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.DenseOverlay.Footprint.Internal

/-!
# Static write footprints for dense-overlay RAM runs

Direct-write programs materialize only their fixed destination registers. The
public input remains in the immutable dense bank, and indirect loads do not
enlarge the mutable overlay footprint.
-/

namespace Complexity

namespace RAM

namespace RegisterStore

namespace DenseOverlay

namespace FixedRegisters

namespace Footprint

/-- A covered overlay remains covered after a permitted tagged write. -/
theorem write_covered
    {overlay : Store} {allowed : Finset ℕ}
    (hcovered : Covered overlay allowed)
    {address value : ℕ} (haddress : address ∈ allowed) :
    Covered (DenseOverlay.write overlay address value) allowed :=
  Internal.write_covered_internal hcovered haddress

/-- One permitted instruction preserves the fixed address footprint. -/
theorem Snapshot.stepInstr_covered
    {input : List Bool} {instruction : Instr}
    {snapshot : Snapshot} {allowed : Finset ℕ}
    (hwrites : InstrWritesWithin allowed instruction)
    (hcovered : Covered snapshot.overlay allowed) :
    Covered (snapshot.stepInstr input instruction).overlay allowed :=
  Internal.Snapshot.stepInstr_covered_internal hwrites hcovered

/-- One program step preserves its fixed address footprint. -/
theorem Snapshot.step_covered
    {program : Program} {input : List Bool}
    {snapshot : Snapshot} {allowed : Finset ℕ}
    (hwrites : ProgramWritesWithin program allowed)
    (hcovered : Covered snapshot.overlay allowed) :
    Covered (snapshot.step program input).overlay allowed :=
  Internal.Snapshot.step_covered_internal hwrites hcovered

/-- Every prefix of a direct-write program stays inside the footprint. -/
theorem Snapshot.run_covered
    {program : Program} {input : List Bool}
    {snapshot : Snapshot} {allowed : Finset ℕ}
    (hwrites : ProgramWritesWithin program allowed)
    (hcovered : Covered snapshot.overlay allowed)
    (fuel : ℕ) :
    Covered (snapshot.run program input fuel).overlay allowed :=
  Internal.Snapshot.run_covered_internal hwrites hcovered fuel

/-- The one-entry initial overlay is covered whenever address zero is allowed. -/
theorem Snapshot.initial_covered
    {input : List Bool} {allowed : Finset ℕ}
    (hzero : 0 ∈ allowed) :
    Covered (Snapshot.initial input).overlay allowed :=
  Internal.Snapshot.initial_covered_internal hzero

/-- A canonical covered overlay has at most one entry per allowed address. -/
theorem Covered.length_le_card
    {overlay : Store} {allowed : Finset ℕ}
    (hcanonical : Canonical overlay)
    (hcovered : Covered overlay allowed) :
    overlay.length ≤ allowed.card :=
  Internal.Covered.length_le_card_internal hcanonical hcovered

/-- Every public-ABI run prefix of a direct-write program has constant entry
count bounded by its fixed address footprint. -/
theorem Snapshot.initial_run_length_le
    {program : Program} {input : List Bool}
    {allowed : Finset ℕ}
    (hwrites : ProgramWritesWithin program allowed)
    (hzero : 0 ∈ allowed) (fuel : ℕ) :
    ((Snapshot.initial input).run program input fuel).overlay.length ≤
      allowed.card :=
  Internal.Snapshot.initial_run_length_le_internal hwrites hzero fuel

/-- A fixed address footprint and decoded-value width bound induce the concrete
tagged-snapshot bound expected by the dense RAM-to-TM simulator. The extra bit
accounts for the positive overlay tag `value + 1`. -/
theorem SnapshotBound.of_footprint
    {input : List Bool} {snapshot : Snapshot}
    {allowed : Finset ℕ} {valueBits : ℕ}
    (hvalid : Valid snapshot.overlay)
    (hcovered : Covered snapshot.overlay allowed)
    (hpc : bitlen snapshot.pc ≤ valueBits + 1)
    (hcount : bitlen allowed.card ≤ valueBits + 1)
    (haddresses : ∀ address ∈ allowed,
      bitlen address ≤ valueBits + 1)
    (hvalues : ∀ address ∈ allowed,
      bitlen ((snapshot.decode input).regs address) ≤ valueBits) :
    SnapshotBound snapshot allowed.card (valueBits + 1) :=
  Internal.SnapshotBound.of_footprint_internal hvalid hcovered hpc
    hcount haddresses hvalues

/-- A direct-write program whose ordinary decoded run has uniformly bounded
program counters and mutable values has a concrete fixed-register trace bound.
The dense public input is read through the immutable input bank and therefore
does not contribute one mutable overlay entry per input bit. -/
theorem TraceBound.of_footprint
    {program : Program} {input : List Bool}
    {allowed : Finset ℕ} {fuel valueBits : ℕ}
    (hwrites : ProgramWritesWithin program allowed)
    (hzero : 0 ∈ allowed)
    (hpc : ∀ k, k ≤ fuel →
      bitlen (RAM.run program k (RAM.initCfg input)).pc ≤ valueBits + 1)
    (hcount : bitlen allowed.card ≤ valueBits + 1)
    (haddresses : ∀ address ∈ allowed,
      bitlen address ≤ valueBits + 1)
    (hvalues : ∀ k, k ≤ fuel → ∀ address ∈ allowed,
      bitlen ((RAM.run program k (RAM.initCfg input)).regs address) ≤ valueBits) :
    TraceBound program input fuel allowed.card (valueBits + 1) :=
  Internal.TraceBound.of_footprint_internal hwrites hzero hpc hcount
    haddresses hvalues

end Footprint

end FixedRegisters

end DenseOverlay

end RegisterStore

end RAM

end Complexity
