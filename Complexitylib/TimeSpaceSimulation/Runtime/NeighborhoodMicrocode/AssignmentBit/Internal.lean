/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.AssignmentBit.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.CombineTerm

/-!
# Uniform Boolean lookup in a streamed grouped assignment -- proofs
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace AssignmentBit
namespace Internal

open RAM Structured

variable {controller : SearchProgram.Registers}

private theorem cmdWritesWithin_mono
    {smaller larger : Finset ℕ}
    (hsubset : smaller ⊆ larger) :
    ∀ command,
      Footprint.CmdWritesWithin smaller command →
      Footprint.CmdWritesWithin larger command := by
  intro command hwrites
  induction command with
  | skip => trivial
  | basic op =>
      cases op <;>
        simp_all [Footprint.CmdWritesWithin,
          Footprint.BasicWritesWithin] <;>
        exact hsubset hwrites
  | seq first second firstIH secondIH =>
      exact ⟨firstIH hwrites.1, secondIH hwrites.2⟩
  | ifZero test onZero onNonzero zeroIH nonzeroIH =>
      exact ⟨zeroIH hwrites.1, nonzeroIH hwrites.2⟩
  | whileNonzero test body bodyIH =>
      exact bodyIH hwrites

private theorem copy_writesWithin
    {allowed : Finset ℕ} {destination source : ℕ}
    (hdestination : destination ∈ allowed) :
    Footprint.CmdWritesWithin allowed
      (CombineTerm.copy destination source) := by
  simpa [CombineTerm.copy, Footprint.CmdWritesWithin,
    Footprint.BasicWritesWithin] using
    And.intro hdestination hdestination

private theorem copy_runs
    (destination source : ℕ) (store : Store)
    (hne : destination ≠ source) :
    ∃ final,
      Runs (CombineTerm.copy destination source) store final ∧
      final destination = store source ∧
      ∀ address, address ≠ destination →
        final address = store address := by
  let middle := (Basic.imm destination 0).exec store
  let final := (Basic.add destination source destination).exec middle
  refine ⟨final, ?_, ?_, ?_⟩
  · exact Runs.seq (Runs.basic _ _) (Runs.basic _ _)
  · simp [final, middle, Basic.exec, Ne.symm hne]
  · intro address haddress
    simp [final, middle, Basic.exec, Function.update_of_ne,
      haddress]

theorem read_writesWithin_internal
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (writeFootprint regs) (read regs) := by
  let digit := digitRegisters regs
  have hvalue : digit.value ∈ writeFootprint regs := by
    simp [writeFootprint, digit, digitRegisters,
      CombineTerm.DigitRegisters.writeFootprint]
  have hcursor : digit.cursor ∈ writeFootprint regs := by
    simp [writeFootprint, digit, digitRegisters,
      CombineTerm.DigitRegisters.writeFootprint]
  have hdivisor : digit.divisor ∈ writeFootprint regs := by
    change digit.divisor ∈ digit.writeFootprint ∪ {digit.divisor}
    exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
  have hseek :
      Footprint.CmdWritesWithin (writeFootprint regs)
        (CombineTerm.seekDigit digit) :=
    cmdWritesWithin_mono
      (Finset.subset_union_left :
        digit.writeFootprint ⊆
          digit.writeFootprint ∪ {digit.divisor})
      _ (CombineTerm.seekDigit_writesWithin digit)
  simpa only [read, Cmd.seqList, Footprint.CmdWritesWithin] using
    And.intro (copy_writesWithin hvalue)
      (And.intro (copy_writesWithin hcursor)
        (And.intro hdivisor hseek))

theorem read_combineScratch_writesWithin_internal
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin
      (CombineValue.combineScratchFootprint regs) (read regs) := by
  apply cmdWritesWithin_mono (command := read regs)
  · intro address haddress
    change address ∈
      (digitRegisters regs).writeFootprint ∪
        {(digitRegisters regs).divisor} at haddress
    rw [Finset.mem_union] at haddress
    simp only [Finset.mem_singleton] at haddress
    rcases haddress with haddress | haddress
    · simp only [CombineTerm.DigitRegisters.writeFootprint,
        Finset.mem_insert, Finset.mem_singleton] at haddress
      rcases haddress with haddress | haddress | haddress |
          haddress | haddress
      · subst address
        exact Finset.mem_image.mpr
          ⟨(4 : Fin 19), Finset.mem_univ _, rfl⟩
      · subst address
        exact Finset.mem_image.mpr
          ⟨(12 : Fin 19), Finset.mem_univ _, rfl⟩
      · subst address
        exact Finset.mem_image.mpr
          ⟨(2 : Fin 19), Finset.mem_univ _, rfl⟩
      · subst address
        exact Finset.mem_image.mpr
          ⟨(5 : Fin 19), Finset.mem_univ _, rfl⟩
      · subst address
        exact Finset.mem_image.mpr
          ⟨(15 : Fin 19), Finset.mem_univ _, rfl⟩
    · subst address
      exact Finset.mem_image.mpr
        ⟨(7 : Fin 19), Finset.mem_univ _, rfl⟩
  · exact read_writesWithin_internal regs

theorem read_layout_writesWithin_internal
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin regs.layout.footprint (read regs) :=
  cmdWritesWithin_mono
    (CombineValue.combineScratchFootprint_subset_layout regs)
    _ (read_combineScratch_writesWithin_internal regs)

theorem read_runs_internal
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store) (code index : ℕ)
    (hcode :
      store (CombineValue.rangeRegisters regs).remaining = code)
    (hindex : store (digitIndex regs) = index) :
    ∃ final,
      Runs (read regs) store final ∧
      Post regs code index store final ∧
      ControlDecode.PreservesABI regs store final := by
  let digit := digitRegisters regs
  let range := CombineValue.rangeRegisters regs
  obtain ⟨afterCode, hcopyCode, hcopyCodeValue,
      hcopyCodeOutside⟩ :=
    copy_runs digit.value range.remaining store
      (regs.injective.ne (by decide))
  have hafterCodeIndex :
      afterCode (digitIndex regs) = index := by
    rw [hcopyCodeOutside (digitIndex regs)
      (regs.injective.ne (by decide))]
    exact hindex
  obtain ⟨afterIndex, hcopyIndex, hcopyIndexValue,
      hcopyIndexOutside⟩ :=
    copy_runs digit.cursor (digitIndex regs) afterCode
      (regs.injective.ne (by decide))
  let afterDivisor := (Basic.imm digit.divisor 2).exec afterIndex
  have hdivisorRun :
      Runs (.basic (.imm digit.divisor 2))
        afterIndex afterDivisor :=
    Runs.basic _ _
  have hafterDivisorValue :
      afterDivisor digit.value = code := by
    have hvalueDivisor : digit.value ≠ digit.divisor :=
      digit.injective.ne (by decide)
    rw [show afterDivisor digit.value =
        afterIndex digit.value by
      simp [afterDivisor, Basic.exec, hvalueDivisor]]
    rw [hcopyIndexOutside digit.value
      (regs.injective.ne (by decide))]
    exact hcopyCodeValue.trans hcode
  have hafterDivisorCursor :
      afterDivisor digit.cursor = index := by
    have hcursorDivisor : digit.cursor ≠ digit.divisor :=
      digit.injective.ne (by decide)
    rw [show afterDivisor digit.cursor =
        afterIndex digit.cursor by
      simp [afterDivisor, Basic.exec, hcursorDivisor]]
    exact hcopyIndexValue.trans hafterCodeIndex
  have hafterDivisorDivisor :
      afterDivisor digit.divisor = 2 := by
    simp [afterDivisor, Basic.exec]
  obtain ⟨final, hseek, hseekPost⟩ :=
    CombineTerm.seekDigit_runs digit afterDivisor 2 code index
      (by omega) hafterDivisorValue hafterDivisorCursor
      hafterDivisorDivisor
  have hrun : Runs (read regs) store final := by
    simpa [read, Cmd.seqList] using
      Runs.seq hcopyCode
        (Runs.seq hcopyIndex (Runs.seq hdivisorRun hseek))
  have houtside :
      ∀ address, address ∉ writeFootprint regs →
        final address = store address := by
    intro address haddress
    exact Footprint.runs_eq_outside
      (read_writesWithin_internal regs) hrun haddress
  have haccumulator :
      range.accumulator ∉ writeFootprint regs := by
    simp [writeFootprint, range, digitRegisters, digitMap,
      CombineValue.rangeRegisters,
      CombineTerm.DigitRegisters.writeFootprint,
      regs.injective.eq_iff]
  have hremaining :
      range.remaining ∉ writeFootprint regs := by
    simp [writeFootprint, range, digitRegisters, digitMap,
      CombineValue.rangeRegisters,
      CombineTerm.DigitRegisters.writeFootprint,
      regs.injective.eq_iff]
  have hmodulus :
      range.modulus ∉ writeFootprint regs := by
    simp [writeFootprint, range, digitRegisters, digitMap,
      CombineValue.rangeRegisters,
      CombineTerm.DigitRegisters.writeFootprint,
      regs.injective.eq_iff]
  have hmodulusPred :
      range.modulusPred ∉ writeFootprint regs := by
    simp [writeFootprint, range, digitRegisters, digitMap,
      CombineValue.rangeRegisters,
      CombineTerm.DigitRegisters.writeFootprint,
      regs.injective.eq_iff]
  have hone :
      range.one ∉ writeFootprint regs := by
    simp [writeFootprint, range, digitRegisters, digitMap,
      CombineValue.rangeRegisters,
      CombineTerm.DigitRegisters.writeFootprint,
      regs.injective.eq_iff]
  have hcount :
      range.count ∉ writeFootprint regs := by
    simp [writeFootprint, range, digitRegisters, digitMap,
      CombineValue.rangeRegisters,
      CombineTerm.DigitRegisters.writeFootprint,
      regs.injective.eq_iff]
  have hindexOutside :
      digitIndex regs ∉ writeFootprint regs := by
    simp [writeFootprint, digitRegisters, digitMap, digitIndex,
      CombineTerm.DigitRegisters.writeFootprint,
      regs.injective.eq_iff]
  refine ⟨final, hrun, ?_, ?_⟩
  · exact
      { value_eq := hseekPost.value_eq
        accumulator_eq := houtside range.accumulator haccumulator
        remaining_eq :=
          (houtside range.remaining hremaining).trans hcode
        modulus_eq := houtside range.modulus hmodulus
        modulusPred_eq := houtside range.modulusPred hmodulusPred
        one_eq := houtside range.one hone
        count_eq := houtside range.count hcount
        index_eq :=
          (houtside (digitIndex regs) hindexOutside).trans hindex
        eq_outside := houtside }
  · exact CombineValue.preservesABI_of_combineScratch regs
      (read_combineScratch_writesWithin_internal regs) hrun

end Internal
end AssignmentBit
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
