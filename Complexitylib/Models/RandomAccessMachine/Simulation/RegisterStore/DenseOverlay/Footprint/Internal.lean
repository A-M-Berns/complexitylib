/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.DenseOverlay
import
  Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.DenseOverlay.Fixed.Defs
import
  Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.DenseOverlay.Footprint.Defs

/-!
# Proof internals for static dense-overlay write footprints
-/

namespace Complexity

namespace RAM

namespace RegisterStore

namespace DenseOverlay

namespace FixedRegisters

namespace Footprint

namespace Internal

theorem write_covered_internal
    {overlay : Store} {allowed : Finset ℕ}
    (hcovered : Covered overlay allowed)
    {address value : ℕ} (haddress : address ∈ allowed) :
    Covered (DenseOverlay.write overlay address value) allowed := by
  intro entry hentry
  induction overlay with
  | nil =>
      simp [DenseOverlay.write, RegisterStore.write] at hentry
      rcases hentry with rfl
      exact haddress
  | cons head rest ih =>
      rcases head with ⟨storedAddress, storedTag⟩
      by_cases heq : address = storedAddress
      · subst storedAddress
        simp [DenseOverlay.write, RegisterStore.write] at hentry
        rcases hentry with rfl | hentry
        · exact haddress
        · exact hcovered entry (by simp [hentry])
      · simp [DenseOverlay.write, RegisterStore.write, heq] at hentry
        rcases hentry with rfl | hentry
        · exact hcovered (storedAddress, storedTag) (by simp)
        · apply ih
          · intro current hcurrent
            exact hcovered current (by simp [hcurrent])
          · exact hentry

theorem Snapshot.stepInstr_covered_internal
    {input : List Bool} {instruction : Instr}
    {snapshot : Snapshot} {allowed : Finset ℕ}
    (hwrites : InstrWritesWithin allowed instruction)
    (hcovered : Covered snapshot.overlay allowed) :
    Covered (snapshot.stepInstr input instruction).overlay allowed := by
  cases instruction with
  | imm destination value =>
      exact write_covered_internal hcovered hwrites
  | add destination source₀ source₁ =>
      exact write_covered_internal hcovered hwrites
  | sub destination source₀ source₁ =>
      exact write_covered_internal hcovered hwrites
  | mul destination source₀ source₁ =>
      exact write_covered_internal hcovered hwrites
  | load destination addressRegister =>
      exact write_covered_internal hcovered hwrites
  | store addressRegister source =>
      contradiction
  | jz source target =>
      simp only [Snapshot.stepInstr]
      split <;> exact hcovered
  | jmp target =>
      simpa [Snapshot.stepInstr] using hcovered
  | halt =>
      simpa [Snapshot.stepInstr] using hcovered

theorem Snapshot.step_covered_internal
    {program : Program} {input : List Bool}
    {snapshot : Snapshot} {allowed : Finset ℕ}
    (hwrites : ProgramWritesWithin program allowed)
    (hcovered : Covered snapshot.overlay allowed) :
    Covered (snapshot.step program input).overlay allowed :=
  Snapshot.stepInstr_covered_internal (hwrites snapshot.pc) hcovered

theorem Snapshot.run_covered_internal
    {program : Program} {input : List Bool}
    {snapshot : Snapshot} {allowed : Finset ℕ}
    (hwrites : ProgramWritesWithin program allowed)
    (hcovered : Covered snapshot.overlay allowed)
    (fuel : ℕ) :
    Covered (snapshot.run program input fuel).overlay allowed := by
  induction fuel generalizing snapshot with
  | zero =>
      simpa [Snapshot.run] using hcovered
  | succ fuel ih =>
      rw [Snapshot.run]
      split
      · exact hcovered
      · exact ih
          (Snapshot.step_covered_internal hwrites hcovered)

theorem Snapshot.initial_covered_internal
    {input : List Bool} {allowed : Finset ℕ}
    (hzero : 0 ∈ allowed) :
    Covered (Snapshot.initial input).overlay allowed := by
  intro entry hentry
  simp [Snapshot.initial, DenseOverlay.write,
    RegisterStore.write] at hentry
  rcases hentry with rfl
  exact hzero

theorem Covered.length_le_card_internal
    {overlay : Store} {allowed : Finset ℕ}
    (hcanonical : Canonical overlay)
    (hcovered : Covered overlay allowed) :
    overlay.length ≤ allowed.card := by
  have hsubset :
      (overlay.map Prod.fst).toFinset ⊆ allowed := by
    intro address haddress
    simp only [List.mem_toFinset, List.mem_map] at haddress
    obtain ⟨entry, hentry, rfl⟩ := haddress
    exact hcovered entry hentry
  calc
    overlay.length = (overlay.map Prod.fst).length := by simp
    _ = (overlay.map Prod.fst).toFinset.card := by
      symm
      exact List.toFinset_card_of_nodup hcanonical.1
    _ ≤ allowed.card := Finset.card_le_card hsubset

theorem Snapshot.initial_run_length_le_internal
    {program : Program} {input : List Bool}
    {allowed : Finset ℕ}
    (hwrites : ProgramWritesWithin program allowed)
    (hzero : 0 ∈ allowed) (fuel : ℕ) :
    ((Snapshot.initial input).run program input fuel).overlay.length ≤
      allowed.card := by
  apply Covered.length_le_card_internal
  · exact Snapshot.run_canonical program input fuel
      (Snapshot.initial input) (Snapshot.initial_canonical input)
  · exact Snapshot.run_covered_internal hwrites
      (Snapshot.initial_covered_internal hzero) fuel

private theorem read_entry_eq
    {overlay : Store} (hnodup : AddressesNodup overlay)
    {entry : Entry} (hentry : entry ∈ overlay) :
    RegisterStore.read overlay entry.1 = entry.2 := by
  rcases entry with ⟨target, targetValue⟩
  induction overlay with
  | nil =>
      simp at hentry
  | cons head rest ih =>
      rcases head with ⟨storedAddress, storedValue⟩
      simp only [AddressesNodup, List.map_cons,
        List.nodup_cons] at hnodup
      simp only [List.mem_cons] at hentry
      rcases hentry with heq | hentry
      · cases heq
        simp [RegisterStore.read]
      · have hne : target ≠ storedAddress := by
          intro heq
          subst target
          apply hnodup.1
          exact List.mem_map.mpr
            ⟨(storedAddress, targetValue), hentry, rfl⟩
        simpa [RegisterStore.read, hne] using
          ih hnodup.2 hentry

private theorem bitlen_succ_le (value : ℕ) :
    bitlen (value + 1) ≤ bitlen value + 1 := by
  rw [bitlen, bitlen, Nat.size_le]
  have hvalue := Nat.lt_size_self value
  rw [pow_succ]
  omega

theorem SnapshotBound.of_footprint_internal
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
    SnapshotBound snapshot allowed.card (valueBits + 1) := by
  refine ⟨hpc,
    Covered.length_le_card_internal hvalid.1 hcovered,
    hcount, ?_⟩
  intro entry hentry
  constructor
  · exact haddresses entry.1 (hcovered entry hentry)
  · have htag :
        entry.2 ≠ 0 :=
      hvalid.1.2 entry hentry
    have hread :
        RegisterStore.read snapshot.overlay entry.1 = entry.2 :=
      read_entry_eq hvalid.1.1 hentry
    have hdecoded :
        (snapshot.decode input).regs entry.1 = entry.2 - 1 := by
      simp only [Snapshot.decode, DenseOverlay.decode,
        DenseOverlay.read]
      rw [hread, if_neg htag]
    have hvalue :=
      hvalues entry.1 (hcovered entry hentry)
    rw [hdecoded] at hvalue
    have hone :
        1 ≤ entry.2 :=
      Nat.one_le_iff_ne_zero.mpr htag
    calc
      bitlen entry.2 = bitlen (entry.2 - 1 + 1) := by
        rw [Nat.sub_add_cancel hone]
      _ ≤ bitlen (entry.2 - 1) + 1 :=
        bitlen_succ_le _
      _ ≤ valueBits + 1 :=
        Nat.add_le_add_right hvalue 1

theorem TraceBound.of_footprint_internal
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
    TraceBound program input fuel allowed.card (valueBits + 1) := by
  intro k hk
  apply SnapshotBound.of_footprint_internal (input := input)
  · exact Snapshot.run_valid program input k (Snapshot.initial input)
      (Snapshot.initial_valid input)
  · exact Snapshot.run_covered_internal hwrites
      (Snapshot.initial_covered_internal hzero) k
  · have hdecode := Snapshot.decode_run program input k
      (Snapshot.initial input) (Snapshot.initial_canonical input)
    rw [Snapshot.initial_decode] at hdecode
    have hkpc := hpc k hk
    rw [← hdecode] at hkpc
    exact hkpc
  · exact hcount
  · exact haddresses
  · intro address haddress
    have hdecode := Snapshot.decode_run program input k
      (Snapshot.initial input) (Snapshot.initial_canonical input)
    rw [Snapshot.initial_decode] at hdecode
    have hvalue := hvalues k hk address haddress
    rw [← hdecode] at hvalue
    exact hvalue

end Internal

end Footprint

end FixedRegisters

end DenseOverlay

end RegisterStore

end RAM

end Complexity
