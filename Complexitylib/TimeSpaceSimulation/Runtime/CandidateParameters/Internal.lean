/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Mathlib.Tactic.FinCases
import
  Complexitylib.Models.RandomAccessMachine.Structured.Footprint
import
  Complexitylib.Models.RandomAccessMachine.Structured.Invariant
import
  Complexitylib.TimeSpaceSimulation.NeighborhoodGraph.WorkspaceAccounting
import
  Complexitylib.TimeSpaceSimulation.Runtime.CandidateParameters.Bounds
import
  Complexitylib.TimeSpaceSimulation.Runtime.CandidateParameters.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.CanonicalPrime
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodProgram
import
  Complexitylib.TimeSpaceSimulation.Runtime.PrimeSearchInvariant
import
  Complexitylib.TreeEvaluation.CookMertz.PrimeGrouped.Logarithmic

/-!
# Runtime candidate-parameter construction internals
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace Runtime

namespace CandidateParameters

open RAM Structured
open NeighborhoodGraph
open TreeEval CookMertz

namespace Internal

private abbrev outputAddress
    (regs : Registers) (slot : Fin 17) : ℕ :=
  regs.index ⟨slot.val, by omega⟩

private theorem outputAddress_ne
    (regs : Registers) {first second : Fin 17}
    (hne : first ≠ second) :
    outputAddress regs first ≠ outputAddress regs second := by
  intro haddress
  have hslots := regs.injective haddress
  apply hne
  have hval :
      (⟨first.val, by omega⟩ : Fin 32).val =
        (⟨second.val, by omega⟩ : Fin 32).val :=
    congrArg (fun slot : Fin 32 => slot.val) hslots
  exact Fin.ext hval

private def copyResultStore
    (destination source : ℕ) (store : Store) : Store :=
  Function.update store destination (store source)

private theorem copy_runs_internal
    (destination source : ℕ) (store : Store)
    (hne : destination ≠ source) :
    Runs (copy destination source) store
      (copyResultStore destination source store) := by
  let cleared := (Basic.imm destination 0).exec store
  let final := (Basic.add destination source destination).exec cleared
  have hsource : cleared source = store source := by
    simp [cleared, Basic.exec, hne.symm]
  have hfinal :
      final = copyResultStore destination source store := by
    funext address
    by_cases haddress : address = destination
    · subst address
      simp only [final, Basic.exec, Function.update_self]
      rw [hsource]
      simp [cleared, copyResultStore, Basic.exec]
    · simp [final, cleared, copyResultStore, Basic.exec, haddress]
  rw [← hfinal]
  exact Runs.seq
    (Runs.basic (Basic.imm destination 0) store)
    (Runs.basic (Basic.add destination source destination) cleared)

private theorem copy_result_internal
    (destination source : ℕ) (store : Store)
    (_hne : destination ≠ source) :
    copyResultStore destination source store destination =
      store source := by
  simp [copyResultStore]

private theorem copy_eq_outside_internal
    (destination source address : ℕ) (store : Store)
    (haddress : address ≠ destination) :
    copyResultStore destination source store address =
      store address := by
  simp [copyResultStore, haddress]

private theorem stack_index_ne_output_internal
    (regs : Registers) (scratchSlot : Fin 7)
    (outputSlot : Fin 17) :
    regs.stackRegisters.index scratchSlot ≠
      outputAddress regs outputSlot := by
  apply regs.index_ne
  intro heq
  have hval := congrArg Fin.val heq
  dsimp [Registers.stackRegisters] at hval
  omega

private theorem prime_index_ne_output_internal
    (regs : Registers) (primeSlot : Fin 8)
    (outputSlot : Fin 17) :
    regs.primeRegisters.index primeSlot ≠
      outputAddress regs outputSlot := by
  apply regs.index_ne
  intro heq
  have hval := congrArg Fin.val heq
  dsimp [Registers.primeRegisters] at hval
  omega

private theorem stack_index_ne_prime_internal
    (regs : Registers) (scratchSlot : Fin 7)
    (primeSlot : Fin 8) :
    regs.stackRegisters.index scratchSlot ≠
      regs.primeRegisters.index primeSlot := by
  apply regs.index_ne
  intro heq
  have hval := congrArg Fin.val heq
  dsimp [Registers.stackRegisters, Registers.primeRegisters] at hval
  omega

private theorem stack_footprint_subset_internal
    (regs : Registers) :
    regs.stackRegisters.footprint ⊆ regs.footprint := by
  intro address haddress
  obtain ⟨slot, _, rfl⟩ := Finset.mem_image.mp haddress
  exact regs.index_mem_footprint ⟨slot.val + 17, by omega⟩

private theorem prime_footprint_subset_internal
    (regs : Registers) :
    PrimeSearchInvariant.footprint regs.primeRegisters ⊆
      regs.footprint := by
  intro address haddress
  obtain ⟨slot, _, rfl⟩ := Finset.mem_image.mp haddress
  exact regs.index_mem_footprint ⟨slot.val + 24, by omega⟩

private theorem pop_sourceWritesWithin_internal
    (regs : Registers) :
    RAM.Structured.Footprint.CmdWritesWithin
      regs.stackRegisters.footprint
      (NeighborhoodProgram.pop regs.stackRegisters) := by
  let scratch := regs.stackRegisters
  simp [NeighborhoodProgram.pop, NeighborhoodProgram.popBody,
    NeighborhoodProgram.popTestOp, Cmd.seqList,
    RAM.Structured.Footprint.CmdWritesWithin,
    RAM.Structured.Footprint.BasicWritesWithin,
    NeighborhoodProgram.StackRegisters.footprint]

private theorem cmdNoStore_of_writesWithin_internal
    (allowed : Finset ℕ) :
    ∀ cmd : Cmd,
      RAM.Structured.Footprint.CmdWritesWithin allowed cmd →
        NeighborhoodProgram.cmdNoStore cmd := by
  intro cmd
  induction cmd with
  | skip =>
      simp [RAM.Structured.Footprint.CmdWritesWithin,
        NeighborhoodProgram.cmdNoStore]
  | basic op =>
      cases op <;>
        simp [RAM.Structured.Footprint.CmdWritesWithin,
          RAM.Structured.Footprint.BasicWritesWithin,
          NeighborhoodProgram.cmdNoStore,
          NeighborhoodProgram.basicNoStore]
  | seq first second ihFirst ihSecond =>
      intro h
      exact ⟨ihFirst h.1, ihSecond h.2⟩
  | ifZero test onZero onNonzero ihZero ihNonzero =>
      intro h
      exact ⟨ihZero h.1, ihNonzero h.2⟩
  | whileNonzero test body ih =>
      exact ih

private theorem exec_deterministic_internal
    {cmd : Cmd} {initial firstFinal secondFinal : Store}
    {firstSteps secondSteps firstCost secondCost firstSpace secondSpace : ℕ}
    (hfirst :
      Exec cmd initial firstFinal firstSteps firstCost firstSpace)
    (hsecond :
      Exec cmd initial secondFinal secondSteps secondCost secondSpace) :
    firstFinal = secondFinal ∧ firstSteps = secondSteps := by
  induction hfirst generalizing secondFinal secondSteps secondCost
      secondSpace with
  | skip store =>
      cases hsecond
      exact ⟨rfl, rfl⟩
  | basic op store =>
      cases hsecond
      exact ⟨rfl, rfl⟩
  | seq hfirstLeft hfirstRight ihLeft ihRight =>
      cases hsecond with
      | seq hsecondLeft hsecondRight =>
          obtain ⟨hmiddle, hleftSteps⟩ :=
            ihLeft hsecondLeft
          subst hmiddle
          obtain ⟨hfinal, hrightSteps⟩ :=
            ihRight hsecondRight
          constructor
          · exact hfinal
          · omega
  | ifZero htest hbranch ih =>
      cases hsecond with
      | ifZero _ hsecondBranch =>
          obtain ⟨hfinal, hsteps⟩ := ih hsecondBranch
          exact ⟨hfinal, by omega⟩
      | ifNonzero hnonzero _ =>
          exact (hnonzero htest).elim
  | ifNonzero htest hbranch ih =>
      cases hsecond with
      | ifZero hzero _ =>
          exact (htest hzero).elim
      | ifNonzero _ hsecondBranch =>
          obtain ⟨hfinal, hsteps⟩ := ih hsecondBranch
          exact ⟨hfinal, by omega⟩
  | whileZero htest =>
      cases hsecond with
      | whileZero _ =>
          exact ⟨rfl, rfl⟩
      | whileNonzero hnonzero _ _ =>
          exact (hnonzero htest).elim
  | whileNonzero htest hbody hloop ihBody ihLoop =>
      cases hsecond with
      | whileZero hzero =>
          exact (htest hzero).elim
      | whileNonzero _ hsecondBody hsecondLoop =>
          obtain ⟨hmiddle, hbodySteps⟩ :=
            ihBody hsecondBody
          subst hmiddle
          obtain ⟨hfinal, hloopSteps⟩ :=
            ihLoop hsecondLoop
          exact ⟨hfinal, by omega⟩

private theorem runs_final_eq_internal
    {cmd : Cmd} {initial firstFinal secondFinal : Store}
    (hfirst : Runs cmd initial firstFinal)
    (hsecond : Runs cmd initial secondFinal) :
    firstFinal = secondFinal := by
  obtain ⟨firstSteps, firstCost, firstSpace, hfirst⟩ := hfirst
  obtain ⟨secondSteps, secondCost, secondSpace, hsecond⟩ := hsecond
  exact (exec_deterministic_internal hfirst hsecond).1

private theorem invariantRuns_mono_internal
    {firstInvariant secondInvariant : Store → Prop}
    (hmono : ∀ store, firstInvariant store → secondInvariant store) :
    ∀ {cmd initial final steps},
      InvariantRuns firstInvariant cmd initial final steps →
      InvariantRuns secondInvariant cmd initial final steps := by
  intro cmd initial final steps hrun
  induction hrun with
  | skip store hstore =>
      exact InvariantRuns.skip store (hmono store hstore)
  | basic op store hstore hnext =>
      exact InvariantRuns.basic op store
        (hmono store hstore) (hmono _ hnext)
  | seq hfirst hsecond ihFirst ihSecond =>
      exact InvariantRuns.seq ihFirst ihSecond
  | ifZero htest hbranch ih =>
      exact InvariantRuns.ifZero htest ih
  | ifNonzero htest hbranch ih =>
      exact InvariantRuns.ifNonzero htest ih
  | whileZero htest hstore =>
      exact InvariantRuns.whileZero htest (hmono _ hstore)
  | whileNonzero htest hbody hloop ihBody ihLoop =>
      exact InvariantRuns.whileNonzero htest ihBody ihLoop

private theorem numericCap_iff_size_internal
    (value width : ℕ) :
    value ≤ 2 ^ width - 1 ↔ Nat.size value ≤ width := by
  rw [Nat.size_le]
  have hpositive : 0 < 2 ^ width := Nat.two_pow_pos width
  omega

private theorem numericWithin_cap_iff_internal
    (allowed : Finset ℕ) (width : ℕ) (store : Store) :
    NeighborhoodProgram.ValuesWithin allowed (2 ^ width - 1) store ↔
      ValuesWithin allowed width store := by
  constructor
  · intro hstore address haddress
    simpa [bitlen, numericCap_iff_size_internal] using
      hstore address haddress
  · intro hstore address haddress
    rw [numericCap_iff_size_internal]
    simpa [bitlen] using hstore address haddress

private theorem size_mul_le_internal (left right : ℕ) :
    Nat.size (left * right) ≤ Nat.size left + Nat.size right := by
  by_cases hleft : left = 0
  · simp [hleft]
  by_cases hright : right = 0
  · simp [hright]
  rw [Nat.size_le]
  calc
    left * right < 2 ^ Nat.size left * right :=
      Nat.mul_lt_mul_of_pos_right (Nat.lt_size_self left)
        (Nat.pos_of_ne_zero hright)
    _ < 2 ^ Nat.size left * 2 ^ Nat.size right :=
      Nat.mul_lt_mul_of_pos_left (Nat.lt_size_self right)
        (Nat.two_pow_pos _)
    _ = 2 ^ (Nat.size left + Nat.size right) := by
      rw [Nat.pow_add]

private theorem size_add_le_internal (left right : ℕ) :
    Nat.size (left + right) ≤
      Nat.size left + Nat.size right + 1 := by
  rw [Nat.size_le]
  let width := Nat.size left + Nat.size right
  have hleft :
      left < 2 ^ width := by
    exact (Nat.lt_size_self left).trans_le
      (Nat.pow_le_pow_right (by omega)
        (Nat.le_add_right (Nat.size left) (Nat.size right)))
  have hright :
      right < 2 ^ width := by
    exact (Nat.lt_size_self right).trans_le
      (Nat.pow_le_pow_right (by omega)
        (Nat.le_add_left (Nat.size right) (Nat.size left)))
  calc
    left + right < 2 ^ width + 2 ^ width :=
      Nat.add_lt_add hleft hright
    _ = 2 ^ (width + 1) := by
      rw [Nat.pow_succ]
      ring
    _ = 2 ^ (Nat.size left + Nat.size right + 1) := by
      rfl

private theorem size_sub_le_internal (left right : ℕ) :
    Nat.size (left - right) ≤ Nat.size left :=
  Nat.size_le_size (Nat.sub_le left right)

private theorem size_le_self_internal (value : ℕ) :
    Nat.size value ≤ value :=
  Nat.size_le.mpr Nat.lt_two_pow_self

private theorem protectedLogBody_sourceWritesWithin_internal
    (regs : Registers) (result : ℕ)
    (hresult : result ∈ regs.footprint) :
    RAM.Structured.Footprint.CmdWritesWithin regs.footprint
      (protectedLogBody regs result) := by
  have hstack (slot : Fin 7) :
      regs.stackRegisters.index slot ∈ regs.footprint :=
    stack_footprint_subset_internal regs
      (NeighborhoodProgram.StackRegisters.index_mem_footprint
        regs.stackRegisters slot)
  simp [protectedLogBody, protectedLogTest, NeighborhoodProgram.pop,
    NeighborhoodProgram.popBody, NeighborhoodProgram.popTestOp,
    Cmd.seqList, RAM.Structured.Footprint.CmdWritesWithin,
    RAM.Structured.Footprint.BasicWritesWithin, hresult, hstack]

private def tailFootprint
    (regs : Registers) (start : ℕ) : Finset ℕ :=
  regs.stackRegisters.footprint ∪
    PrimeSearchInvariant.footprint regs.primeRegisters ∪
      ((Finset.univ.filter fun slot : Fin 17 => start ≤ slot.val).image
        (outputAddress regs))

private theorem tailFootprint_subset_internal
    (regs : Registers) (start : ℕ) :
    tailFootprint regs start ⊆ regs.footprint := by
  intro address haddress
  simp only [tailFootprint, Finset.mem_union, Finset.mem_image,
    Finset.mem_filter, Finset.mem_univ, true_and] at haddress
  rcases haddress with (hstack | hprime) | ⟨slot, _, rfl⟩
  · exact stack_footprint_subset_internal regs hstack
  · exact prime_footprint_subset_internal regs hprime
  · exact regs.index_mem_footprint ⟨slot.val, by omega⟩

private theorem stack_mem_tailFootprint_internal
    (regs : Registers) (start : ℕ) (slot : Fin 7) :
    regs.stackRegisters.index slot ∈ tailFootprint regs start := by
  exact Finset.mem_union_left _
    (Finset.mem_union_left _
      (NeighborhoodProgram.StackRegisters.index_mem_footprint
        regs.stackRegisters slot))

private theorem prime_mem_tailFootprint_internal
    (regs : Registers) (start : ℕ) (slot : Fin 8) :
    regs.primeRegisters.index slot ∈ tailFootprint regs start := by
  exact Finset.mem_union_left _
    (Finset.mem_union_right _
      (PrimeSearchInvariant.index_mem_footprint
        regs.primeRegisters slot))

private theorem output_mem_tailFootprint_internal
    (regs : Registers) (start : ℕ) (slot : Fin 17)
    (hslot : start ≤ slot.val) :
    outputAddress regs slot ∈ tailFootprint regs start := by
  exact Finset.mem_union_right _ <|
    Finset.mem_image.mpr
      ⟨slot, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hslot⟩, rfl⟩

private theorem output_not_mem_tailFootprint_internal
    (regs : Registers) (start : ℕ) (slot : Fin 17)
    (hslot : slot.val < start) :
    outputAddress regs slot ∉ tailFootprint regs start := by
  intro haddress
  simp only [tailFootprint, Finset.mem_union, Finset.mem_image,
    Finset.mem_filter, Finset.mem_univ, true_and] at haddress
  rcases haddress with (hstack | hprime) | ⟨other, hother, heq⟩
  · obtain ⟨scratchSlot, _, hscratch⟩ :=
      Finset.mem_image.mp hstack
    exact
      (stack_index_ne_output_internal regs scratchSlot slot)
        hscratch
  · obtain ⟨primeSlot, _, hprimeSlot⟩ :=
      Finset.mem_image.mp hprime
    exact
      (prime_index_ne_output_internal regs primeSlot slot)
        hprimeSlot
  · have hsame : other = slot := by
      by_contra hne
      exact (outputAddress_ne regs hne) heq
    subst other
    omega

private theorem computeProtectedLog_tailWrites_internal
    (regs : Registers) (start : ℕ) (source : ℕ)
    (resultSlot : Fin 17) (hresult : start ≤ resultSlot.val) :
    RAM.Structured.Footprint.CmdWritesWithin
      (tailFootprint regs start)
      (computeProtectedLog regs source
        (outputAddress regs resultSlot)) := by
  have hstack (slot : Fin 7) :
      regs.stackRegisters.index slot ∈ tailFootprint regs start :=
    stack_mem_tailFootprint_internal regs start slot
  have hout :
      outputAddress regs resultSlot ∈ tailFootprint regs start :=
    output_mem_tailFootprint_internal regs start resultSlot hresult
  simp [computeProtectedLog, copy, protectedLogBody,
    protectedLogTest, NeighborhoodProgram.pop,
    NeighborhoodProgram.popBody, NeighborhoodProgram.popTestOp,
    Cmd.seqList, RAM.Structured.Footprint.CmdWritesWithin,
    RAM.Structured.Footprint.BasicWritesWithin, hstack, hout]

private theorem computePositiveCeilSqrt_tailWrites_internal
    (regs : Registers) (start : ℕ) (source : ℕ)
    (resultSlot : Fin 17) (hresult : start ≤ resultSlot.val) :
    RAM.Structured.Footprint.CmdWritesWithin
      (tailFootprint regs start)
      (computePositiveCeilSqrt regs source
        (outputAddress regs resultSlot)) := by
  have hstack (slot : Fin 7) :
      regs.stackRegisters.index slot ∈ tailFootprint regs start :=
    stack_mem_tailFootprint_internal regs start slot
  have hout :
      outputAddress regs resultSlot ∈ tailFootprint regs start :=
    output_mem_tailFootprint_internal regs start resultSlot hresult
  simp [computePositiveCeilSqrt, sqrtBody, sqrtTest,
    Cmd.seqList, RAM.Structured.Footprint.CmdWritesWithin,
    RAM.Structured.Footprint.BasicWritesWithin, hstack, hout]

private theorem computeCeilDiv_tailWrites_internal
    (regs : Registers) (start : ℕ)
    (dividend divisor : ℕ) (resultSlot : Fin 17)
    (hresult : start ≤ resultSlot.val) :
    RAM.Structured.Footprint.CmdWritesWithin
      (tailFootprint regs start)
      (computeCeilDiv regs dividend divisor
        (outputAddress regs resultSlot)) := by
  have hstack (slot : Fin 7) :
      regs.stackRegisters.index slot ∈ tailFootprint regs start :=
    stack_mem_tailFootprint_internal regs start slot
  have hout :
      outputAddress regs resultSlot ∈ tailFootprint regs start :=
    output_mem_tailFootprint_internal regs start resultSlot hresult
  simp [computeCeilDiv, copy, NeighborhoodProgram.pop,
    NeighborhoodProgram.popBody, NeighborhoodProgram.popTestOp,
    Cmd.seqList, RAM.Structured.Footprint.CmdWritesWithin,
    RAM.Structured.Footprint.BasicWritesWithin, hstack, hout]

private theorem computePowTwo_tailWrites_internal
    (regs : Registers) (start exponent : ℕ)
    (resultSlot : Fin 17) (hresult : start ≤ resultSlot.val) :
    RAM.Structured.Footprint.CmdWritesWithin
      (tailFootprint regs start)
      (computePowTwo regs exponent
        (outputAddress regs resultSlot)) := by
  have hstack (slot : Fin 7) :
      regs.stackRegisters.index slot ∈ tailFootprint regs start :=
    stack_mem_tailFootprint_internal regs start slot
  have hout :
      outputAddress regs resultSlot ∈ tailFootprint regs start :=
    output_mem_tailFootprint_internal regs start resultSlot hresult
  simp [computePowTwo, powTwoBody, copy, Cmd.seqList,
    RAM.Structured.Footprint.CmdWritesWithin,
    RAM.Structured.Footprint.BasicWritesWithin, hstack, hout]

private theorem computeMax_tailWrites_internal
    (regs : Registers) (start left right : ℕ)
    (resultSlot : Fin 17) (hresult : start ≤ resultSlot.val) :
    RAM.Structured.Footprint.CmdWritesWithin
      (tailFootprint regs start)
      (computeMax regs left right
        (outputAddress regs resultSlot)) := by
  have hstack (slot : Fin 7) :
      regs.stackRegisters.index slot ∈ tailFootprint regs start :=
    stack_mem_tailFootprint_internal regs start slot
  have hout :
      outputAddress regs resultSlot ∈ tailFootprint regs start :=
    output_mem_tailFootprint_internal regs start resultSlot hresult
  simp [computeMax, copy,
    RAM.Structured.Footprint.CmdWritesWithin,
    RAM.Structured.Footprint.BasicWritesWithin, hstack, hout]

private def OutputsThrough
    (Q : Type*) [Fintype Q] (workTapeCount candidate count : ℕ)
    (regs : Registers) (store : Store) : Prop :=
  ∀ slot : Fin 17, slot.val < count →
    store (outputAddress regs slot) =
      expectedValues Q workTapeCount candidate slot

private theorem outputsThrough_zero_internal
    (Q : Type*) [Fintype Q] (workTapeCount candidate : ℕ)
    (regs : Registers) (store : Store) :
    OutputsThrough Q workTapeCount candidate 0 regs store := by
  intro slot hslot
  omega

private theorem outputsThrough_extend_internal
    (Q : Type*) [Fintype Q] (workTapeCount candidate : ℕ)
    (regs : Registers) (slot : Fin 17)
    {cmd : Cmd} {initial final : Store}
    (hbefore :
      OutputsThrough Q workTapeCount candidate slot.val regs initial)
    (hrun : Runs cmd initial final)
    (hwrites :
      RAM.Structured.Footprint.CmdWritesWithin
        (tailFootprint regs slot.val) cmd)
    (hnew :
      final (outputAddress regs slot) =
        expectedValues Q workTapeCount candidate slot) :
    OutputsThrough Q workTapeCount candidate (slot.val + 1)
      regs final := by
  intro current hcurrent
  by_cases hlt : current.val < slot.val
  · rw [RAM.Structured.Footprint.runs_eq_outside
      hwrites hrun
      (output_not_mem_tailFootprint_internal regs slot.val current hlt)]
    exact hbefore current hlt
  · have hval : current.val = slot.val := by omega
    have hsame : current = slot := Fin.ext hval
    subst current
    exact hnew

private theorem candidate_preserved_internal
    (regs : Registers) (start : ℕ)
    {cmd : Cmd} {initial final : Store}
    (hwrites :
      RAM.Structured.Footprint.CmdWritesWithin
        (tailFootprint regs start) cmd)
    (hrun : Runs cmd initial final) :
    final regs.candidate = initial regs.candidate := by
  apply RAM.Structured.Footprint.runs_eq_outside hwrites hrun
  intro hmem
  exact regs.candidate_not_mem_footprint
    (tailFootprint_subset_internal regs start hmem)

private theorem numericWithin_update_internal
    (allowed : Finset ℕ) (bound address value : ℕ)
    (store : Store)
    (hstore : NeighborhoodProgram.ValuesWithin allowed bound store)
    (hvalue : value ≤ bound) :
    NeighborhoodProgram.ValuesWithin allowed bound
      (Function.update store address value) := by
  intro current hcurrent
  by_cases heq : current = address
  · subst current
    simp [hvalue]
  · simp [heq, hstore current hcurrent]

private theorem copy_invariantRuns_internal
    (allowed : Finset ℕ) (bound destination source : ℕ)
    (store : Store)
    (hne : destination ≠ source)
    (hsource : store source ≤ bound)
    (hstore : NeighborhoodProgram.ValuesWithin allowed bound store) :
    ∃ final,
      InvariantRuns
        (NeighborhoodProgram.ValuesWithin allowed bound)
        (copy destination source) store final 2 ∧
      final destination = store source ∧
      ∀ address, address ≠ destination →
        final address = store address := by
  let cleared := (Basic.imm destination 0).exec store
  let final := (Basic.add destination source destination).exec cleared
  have hcleared :
      NeighborhoodProgram.ValuesWithin allowed bound cleared := by
    apply numericWithin_update_internal allowed bound destination 0
      store hstore
    omega
  have hclearedSource : cleared source = store source := by
    simp [cleared, Basic.exec, hne.symm]
  have hclearedDestination : cleared destination = 0 := by
    simp [cleared, Basic.exec]
  have hfinal :
      NeighborhoodProgram.ValuesWithin allowed bound final := by
    apply numericWithin_update_internal allowed bound destination
      (cleared source + cleared destination) cleared hcleared
    rw [hclearedSource, hclearedDestination, Nat.add_zero]
    exact hsource
  refine ⟨final, ?_, ?_, ?_⟩
  · exact InvariantRuns.seq
      (InvariantRuns.basic (Basic.imm destination 0) store
        hstore hcleared)
      (InvariantRuns.basic
        (Basic.add destination source destination) cleared
        hcleared hfinal)
  · simp [final, cleared, Basic.exec, hne.symm]
  · intro address haddress
    simp [final, cleared, Basic.exec, haddress]

private theorem protected_log_loop_runs_internal
    (regs : Registers) (result : ℕ)
    (store : Store) (word count : ℕ)
    (hword : store regs.stackRegisters.word = word)
    (hbase : store regs.stackRegisters.base = 2)
    (hbasePred : store regs.stackRegisters.basePred = 1)
    (hone : store regs.stackRegisters.one = 1)
    (hcount : store result = count)
    (htest :
      store regs.stackRegisters.test = word - 1)
    (hresultOutside :
      result ∉ regs.stackRegisters.footprint) :
    ∃ final,
      Runs
        (.whileNonzero regs.stackRegisters.test
          (protectedLogBody regs result))
        store final ∧
      final result = count + Nat.log 2 word := by
  induction word using Nat.strong_induction_on generalizing store count with
  | h word ih =>
      by_cases hsmall : word < 2
      · have htestZero :
            store regs.stackRegisters.test = 0 := by
          rw [htest]
          omega
        refine ⟨store, Runs.whileZero htestZero, ?_⟩
        rw [hcount, Nat.log_of_lt hsmall]
        omega
      · have hwordTwo : 2 ≤ word := by omega
        have htestNonzero :
            store regs.stackRegisters.test ≠ 0 := by
          rw [htest]
          omega
        obtain ⟨afterPop, hpop, hpopWord, _hpopQuotient,
            _hpopTest, hpopBase, hpopBasePred, hpopOne⟩ :=
          NeighborhoodProgram.pop_runs regs.stackRegisters store
            2 word (by omega) hword hbase hbasePred hone
        have hpopResult :
            afterPop result = count := by
          rw [RAM.Structured.Footprint.runs_eq_outside
            (pop_sourceWritesWithin_internal regs) hpop
            hresultOutside]
          exact hcount
        let afterIncrement :=
          (Basic.add result result regs.stackRegisters.one).exec
            afterPop
        have hincrementResult :
            afterIncrement result = count + 1 := by
          simp [afterIncrement, Basic.exec, hpopResult, hpopOne]
        have hincrementWord :
            afterIncrement regs.stackRegisters.word = word / 2 := by
          have hne :
              regs.stackRegisters.word ≠ result := by
            intro heq
            apply hresultOutside
            rw [← heq]
            exact
              NeighborhoodProgram.StackRegisters.index_mem_footprint
                regs.stackRegisters 0
          simp [afterIncrement, Basic.exec, hne, hpopWord,
            PackedDigits.pop]
        have hincrementBase :
            afterIncrement regs.stackRegisters.base = 2 := by
          have hne :
              regs.stackRegisters.base ≠ result := by
            intro heq
            apply hresultOutside
            rw [← heq]
            exact
              NeighborhoodProgram.StackRegisters.index_mem_footprint
                regs.stackRegisters 1
          simp [afterIncrement, Basic.exec, hne, hpopBase]
        have hincrementBasePred :
            afterIncrement regs.stackRegisters.basePred = 1 := by
          have hne :
              regs.stackRegisters.basePred ≠ result := by
            intro heq
            apply hresultOutside
            rw [← heq]
            exact
              NeighborhoodProgram.StackRegisters.index_mem_footprint
                regs.stackRegisters 2
          simp [afterIncrement, Basic.exec, hne, hpopBasePred]
        have hincrementOne :
            afterIncrement regs.stackRegisters.one = 1 := by
          have hne :
              regs.stackRegisters.one ≠ result := by
            intro heq
            apply hresultOutside
            rw [← heq]
            exact
              NeighborhoodProgram.StackRegisters.index_mem_footprint
                regs.stackRegisters 5
          simp [afterIncrement, Basic.exec, hne, hpopOne]
        let afterTest :=
          (protectedLogTest regs).exec afterIncrement
        have hafterTestWord :
            afterTest regs.stackRegisters.word = word / 2 := by
          simp [afterTest, protectedLogTest, Basic.exec,
            regs.stackRegisters.injective.eq_iff, hincrementWord]
        have hafterTestBase :
            afterTest regs.stackRegisters.base = 2 := by
          simp [afterTest, protectedLogTest, Basic.exec,
            regs.stackRegisters.injective.eq_iff, hincrementBase]
        have hafterTestBasePred :
            afterTest regs.stackRegisters.basePred = 1 := by
          simp [afterTest, protectedLogTest, Basic.exec,
            regs.stackRegisters.injective.eq_iff,
            hincrementBasePred]
        have hafterTestOne :
            afterTest regs.stackRegisters.one = 1 := by
          simp [afterTest, protectedLogTest, Basic.exec,
            regs.stackRegisters.injective.eq_iff, hincrementOne]
        have hafterTestResult :
            afterTest result = count + 1 := by
          have hne :
              result ≠ regs.stackRegisters.test := by
            intro heq
            apply hresultOutside
            rw [heq]
            exact
              NeighborhoodProgram.StackRegisters.index_mem_footprint
                regs.stackRegisters 4
          simp [afterTest, protectedLogTest, Basic.exec, hne,
            hincrementResult]
        have hafterTestTest :
            afterTest regs.stackRegisters.test =
              word / 2 - 1 := by
          simp [afterTest, protectedLogTest, Basic.exec,
            hincrementWord, hincrementOne]
        have hbody :
            Runs (protectedLogBody regs result)
              store afterTest := by
          simpa [protectedLogBody, Cmd.seqList] using
            Runs.seq hpop
              (Runs.seq
                (Runs.basic
                  (Basic.add result result regs.stackRegisters.one)
                  afterPop)
                (Runs.basic (protectedLogTest regs)
                  afterIncrement))
        have hdivLt : word / 2 < word :=
          Nat.div_lt_self (by omega) (by omega)
        obtain ⟨final, hloop, hfinal⟩ :=
          ih (word / 2) hdivLt afterTest (count + 1)
            hafterTestWord hafterTestBase hafterTestBasePred
            hafterTestOne hafterTestResult hafterTestTest
        refine ⟨final,
          Runs.whileNonzero htestNonzero hbody hloop, ?_⟩
        rw [hfinal, Nat.log_of_one_lt_of_le (by omega) hwordTwo]
        omega

private theorem protected_log_loop_invariantRuns_internal
    (regs : Registers) (allowed : Finset ℕ) (bound result : ℕ)
    (store : Store) (word count : ℕ)
    (hword : store regs.stackRegisters.word = word)
    (hbase : store regs.stackRegisters.base = 2)
    (hbasePred : store regs.stackRegisters.basePred = 1)
    (hone : store regs.stackRegisters.one = 1)
    (hcount : store result = count)
    (htest : store regs.stackRegisters.test = word - 1)
    (hresultOutside :
      result ∉ regs.stackRegisters.footprint)
    (hwordBound : word ≤ bound)
    (hcountBound : count + Nat.log 2 word ≤ bound)
    (hstore :
      NeighborhoodProgram.ValuesWithin allowed bound store) :
    ∃ final steps,
      InvariantRuns
        (NeighborhoodProgram.ValuesWithin allowed bound)
        (.whileNonzero regs.stackRegisters.test
          (protectedLogBody regs result))
        store final steps ∧
      final result = count + Nat.log 2 word := by
  induction word using Nat.strong_induction_on generalizing store count with
  | h word ih =>
      by_cases hsmall : word < 2
      · have htestZero :
            store regs.stackRegisters.test = 0 := by
          rw [htest]
          omega
        refine ⟨store, 1,
          InvariantRuns.whileZero htestZero hstore, ?_⟩
        rw [hcount, Nat.log_of_lt hsmall]
        omega
      · have hwordTwo : 2 ≤ word := by omega
        have htestNonzero :
            store regs.stackRegisters.test ≠ 0 := by
          rw [htest]
          omega
        obtain ⟨afterPop, popSteps, hpop, hpopWord,
            _hpopQuotient, _hpopTest, hpopBase, hpopBasePred,
            hpopOne⟩ :=
          NeighborhoodProgram.pop_invariantRuns
            regs.stackRegisters allowed bound store 2 word
            (by omega) hword hbase hbasePred hone hwordBound hstore
        have hpopResult :
            afterPop result = count := by
          rw [RAM.Structured.Footprint.runs_eq_outside
            (pop_sourceWritesWithin_internal regs)
            (InvariantRuns.toRuns hpop) hresultOutside]
          exact hcount
        let afterIncrement :=
          (Basic.add result result regs.stackRegisters.one).exec
            afterPop
        have hincrementResult :
            afterIncrement result = count + 1 := by
          simp [afterIncrement, Basic.exec, hpopResult, hpopOne]
        have hlogRec :
            Nat.log 2 word = Nat.log 2 (word / 2) + 1 := by
          rw [Nat.log_of_one_lt_of_le (by omega) hwordTwo]
        have hincrementBound : count + 1 ≤ bound := by
          rw [hlogRec] at hcountBound
          omega
        have hafterPopWithin :
            NeighborhoodProgram.ValuesWithin allowed bound afterPop :=
          InvariantRuns.final hpop
        have hafterIncrementWithin :
            NeighborhoodProgram.ValuesWithin allowed bound
              afterIncrement := by
          apply numericWithin_update_internal allowed bound result
            (afterPop result + afterPop regs.stackRegisters.one)
            afterPop hafterPopWithin
          rw [hpopResult, hpopOne]
          exact hincrementBound
        have hincrementWord :
            afterIncrement regs.stackRegisters.word = word / 2 := by
          have hne :
              regs.stackRegisters.word ≠ result := by
            intro heq
            apply hresultOutside
            rw [← heq]
            exact
              NeighborhoodProgram.StackRegisters.index_mem_footprint
                regs.stackRegisters 0
          simp [afterIncrement, Basic.exec, hne, hpopWord,
            PackedDigits.pop]
        have hincrementBase :
            afterIncrement regs.stackRegisters.base = 2 := by
          have hne :
              regs.stackRegisters.base ≠ result := by
            intro heq
            apply hresultOutside
            rw [← heq]
            exact
              NeighborhoodProgram.StackRegisters.index_mem_footprint
                regs.stackRegisters 1
          simp [afterIncrement, Basic.exec, hne, hpopBase]
        have hincrementBasePred :
            afterIncrement regs.stackRegisters.basePred = 1 := by
          have hne :
              regs.stackRegisters.basePred ≠ result := by
            intro heq
            apply hresultOutside
            rw [← heq]
            exact
              NeighborhoodProgram.StackRegisters.index_mem_footprint
                regs.stackRegisters 2
          simp [afterIncrement, Basic.exec, hne, hpopBasePred]
        have hincrementOne :
            afterIncrement regs.stackRegisters.one = 1 := by
          have hne :
              regs.stackRegisters.one ≠ result := by
            intro heq
            apply hresultOutside
            rw [← heq]
            exact
              NeighborhoodProgram.StackRegisters.index_mem_footprint
                regs.stackRegisters 5
          simp [afterIncrement, Basic.exec, hne, hpopOne]
        let afterTest :=
          (protectedLogTest regs).exec afterIncrement
        have hafterTestWithin :
            NeighborhoodProgram.ValuesWithin allowed bound afterTest := by
          apply numericWithin_update_internal allowed bound
            regs.stackRegisters.test
            (afterIncrement regs.stackRegisters.word -
              afterIncrement regs.stackRegisters.one)
            afterIncrement hafterIncrementWithin
          rw [hincrementWord, hincrementOne]
          exact (Nat.sub_le _ _).trans
            ((Nat.div_le_self word 2).trans hwordBound)
        have hafterTestWord :
            afterTest regs.stackRegisters.word = word / 2 := by
          simp [afterTest, protectedLogTest, Basic.exec,
            regs.stackRegisters.injective.eq_iff, hincrementWord]
        have hafterTestBase :
            afterTest regs.stackRegisters.base = 2 := by
          simp [afterTest, protectedLogTest, Basic.exec,
            regs.stackRegisters.injective.eq_iff, hincrementBase]
        have hafterTestBasePred :
            afterTest regs.stackRegisters.basePred = 1 := by
          simp [afterTest, protectedLogTest, Basic.exec,
            regs.stackRegisters.injective.eq_iff,
            hincrementBasePred]
        have hafterTestOne :
            afterTest regs.stackRegisters.one = 1 := by
          simp [afterTest, protectedLogTest, Basic.exec,
            regs.stackRegisters.injective.eq_iff, hincrementOne]
        have hafterTestResult :
            afterTest result = count + 1 := by
          have hne :
              result ≠ regs.stackRegisters.test := by
            intro heq
            apply hresultOutside
            rw [heq]
            exact
              NeighborhoodProgram.StackRegisters.index_mem_footprint
                regs.stackRegisters 4
          simp [afterTest, protectedLogTest, Basic.exec, hne,
            hincrementResult]
        have hafterTestTest :
            afterTest regs.stackRegisters.test =
              word / 2 - 1 := by
          simp [afterTest, protectedLogTest, Basic.exec,
            hincrementWord, hincrementOne]
        have hbody :
            InvariantRuns
              (NeighborhoodProgram.ValuesWithin allowed bound)
              (protectedLogBody regs result) store afterTest
              (popSteps + 2) := by
          simpa [protectedLogBody, Cmd.seqList] using
            InvariantRuns.seq hpop
              (InvariantRuns.seq
                (InvariantRuns.basic
                  (Basic.add result result regs.stackRegisters.one)
                  afterPop hafterPopWithin hafterIncrementWithin)
                (InvariantRuns.basic (protectedLogTest regs)
                  afterIncrement hafterIncrementWithin
                  hafterTestWithin))
        have hdivLt : word / 2 < word :=
          Nat.div_lt_self (by omega) (by omega)
        have hnextCountBound :
            count + 1 + Nat.log 2 (word / 2) ≤ bound := by
          rw [hlogRec] at hcountBound
          omega
        obtain ⟨final, loopSteps, hloop, hfinal⟩ :=
          ih (word / 2) hdivLt afterTest (count + 1)
            hafterTestWord hafterTestBase hafterTestBasePred
            hafterTestOne hafterTestResult hafterTestTest
            ((Nat.div_le_self word 2).trans hwordBound)
            hnextCountBound hafterTestWithin
        refine ⟨final, popSteps + 2 + loopSteps + 2,
          InvariantRuns.whileNonzero htestNonzero hbody hloop, ?_⟩
        rw [hfinal, hlogRec]
        omega

private theorem computeProtectedLog_runs_internal
    (regs : Registers) (source : ℕ) (resultSlot : Fin 17)
    (store : Store) (value : ℕ)
    (hsource : store source = value)
    (hsourceNeWord :
      regs.stackRegisters.word ≠ source) :
    ∃ final,
      Runs (computeProtectedLog regs source (outputAddress regs resultSlot))
        store final ∧
      final (outputAddress regs resultSlot) =
        Nat.log 2 value + 1 := by
  let scratch := regs.stackRegisters
  let result := outputAddress regs resultSlot
  let afterCopy :=
    copyResultStore scratch.word source store
  have hcopy :
      Runs (copy scratch.word source) store afterCopy :=
    copy_runs_internal scratch.word source store hsourceNeWord
  have hcopyWord : afterCopy scratch.word = value := by
    simpa [afterCopy, hsource] using
      copy_result_internal scratch.word source store hsourceNeWord
  let afterBase := (Basic.imm scratch.base 2).exec afterCopy
  let afterBasePred := (Basic.imm scratch.basePred 1).exec afterBase
  let afterOne := (Basic.imm scratch.one 1).exec afterBasePred
  let afterResult := (Basic.imm result 1).exec afterOne
  let afterTest := (protectedLogTest regs).exec afterResult
  have hresultOutside : result ∉ scratch.footprint := by
    intro hmem
    obtain ⟨slot, _, hslot⟩ := Finset.mem_image.mp hmem
    exact
      (stack_index_ne_output_internal regs slot resultSlot)
        hslot
  have hafterResultWord :
      afterResult scratch.word = value := by
    have hwordNeBase : scratch.word ≠ scratch.base :=
      scratch.index_ne (by decide)
    have hwordNeBasePred : scratch.word ≠ scratch.basePred :=
      scratch.index_ne (by decide)
    have hwordNeOne : scratch.word ≠ scratch.one :=
      scratch.index_ne (by decide)
    have hwordNeResult : scratch.word ≠ result := by
      intro heq
      apply hresultOutside
      rw [← heq]
      exact
        NeighborhoodProgram.StackRegisters.index_mem_footprint
          scratch 0
    simp [afterResult, afterOne, afterBasePred, afterBase,
      Basic.exec, hwordNeBase, hwordNeBasePred, hwordNeOne,
      hwordNeResult, hcopyWord]
  have hafterResultBase :
      afterResult scratch.base = 2 := by
    have hbaseNeBasePred : scratch.base ≠ scratch.basePred :=
      scratch.index_ne (by decide)
    have hbaseNeOne : scratch.base ≠ scratch.one :=
      scratch.index_ne (by decide)
    have hbaseNeResult : scratch.base ≠ result := by
      intro heq
      apply hresultOutside
      rw [← heq]
      exact
        NeighborhoodProgram.StackRegisters.index_mem_footprint
          scratch 1
    simp [afterResult, afterOne, afterBasePred, afterBase,
      Basic.exec, hbaseNeBasePred, hbaseNeOne, hbaseNeResult]
  have hafterResultBasePred :
      afterResult scratch.basePred = 1 := by
    have hpredNeOne : scratch.basePred ≠ scratch.one :=
      scratch.index_ne (by decide)
    have hpredNeResult : scratch.basePred ≠ result := by
      intro heq
      apply hresultOutside
      rw [← heq]
      exact
        NeighborhoodProgram.StackRegisters.index_mem_footprint
          scratch 2
    simp [afterResult, afterOne, afterBasePred, Basic.exec,
      hpredNeOne, hpredNeResult]
  have hafterResultOne :
      afterResult scratch.one = 1 := by
    have honeNeResult : scratch.one ≠ result := by
      intro heq
      apply hresultOutside
      rw [← heq]
      exact
        NeighborhoodProgram.StackRegisters.index_mem_footprint
          scratch 5
    simp [afterResult, afterOne, Basic.exec, honeNeResult]
  have hafterResultResult :
      afterResult result = 1 := by
    simp [afterResult, Basic.exec]
  have hafterTestWord :
      afterTest scratch.word = value := by
    simp only [afterTest, protectedLogTest, Basic.exec]
    change Function.update afterResult scratch.test
      _ scratch.word = value
    simpa [scratch.index_ne (first := 0) (second := 4)
      (by decide)] using hafterResultWord
  have hafterTestBase :
      afterTest scratch.base = 2 := by
    simp only [afterTest, protectedLogTest, Basic.exec]
    change Function.update afterResult scratch.test
      _ scratch.base = 2
    simpa [scratch.index_ne (first := 1) (second := 4)
      (by decide)] using hafterResultBase
  have hafterTestBasePred :
      afterTest scratch.basePred = 1 := by
    simp only [afterTest, protectedLogTest, Basic.exec]
    change Function.update afterResult scratch.test
      _ scratch.basePred = 1
    simpa [scratch.index_ne (first := 2) (second := 4)
      (by decide)] using hafterResultBasePred
  have hafterTestOne :
      afterTest scratch.one = 1 := by
    simp only [afterTest, protectedLogTest, Basic.exec]
    change Function.update afterResult scratch.test
      _ scratch.one = 1
    simpa [scratch.index_ne (first := 5) (second := 4)
      (by decide)] using hafterResultOne
  have hafterTestResult :
      afterTest result = 1 := by
    have hresultNeTest : result ≠ scratch.test := by
      intro heq
      apply hresultOutside
      rw [heq]
      exact
        NeighborhoodProgram.StackRegisters.index_mem_footprint
          scratch 4
    simp only [afterTest, protectedLogTest, Basic.exec]
    change Function.update afterResult scratch.test
      _ result = 1
    simpa [hresultNeTest] using hafterResultResult
  have hafterTestTest :
      afterTest scratch.test = value - 1 := by
    simp only [afterTest, protectedLogTest, Basic.exec]
    rw [hafterResultWord, hafterResultOne]
    change Function.update afterResult scratch.test
      (value - 1) scratch.test = value - 1
    simp
  obtain ⟨final, hloop, hfinal⟩ :=
    protected_log_loop_runs_internal regs result afterTest
      value 1 hafterTestWord hafterTestBase hafterTestBasePred
      hafterTestOne hafterTestResult hafterTestTest
      hresultOutside
  refine ⟨final, ?_, ?_⟩
  · simpa [computeProtectedLog, Cmd.seqList, scratch, result] using
      Runs.seq hcopy
        (Runs.seq (Runs.basic (Basic.imm scratch.base 2) afterCopy)
          (Runs.seq
            (Runs.basic (Basic.imm scratch.basePred 1) afterBase)
            (Runs.seq (Runs.basic (Basic.imm scratch.one 1)
                afterBasePred)
              (Runs.seq (Runs.basic (Basic.imm result 1) afterOne)
                (Runs.seq (Runs.basic (protectedLogTest regs)
                    afterResult)
                  hloop)))))
  · rw [hfinal]
    omega

private theorem computeProtectedLog_invariantRuns_internal
    (regs : Registers) (allowed : Finset ℕ) (bound source : ℕ)
    (resultSlot : Fin 17) (store : Store) (value : ℕ)
    (hsource : store source = value)
    (hsourceNeWord : regs.stackRegisters.word ≠ source)
    (hvalueBound : value ≤ bound)
    (hlogBound : Nat.log 2 value + 1 ≤ bound)
    (htwoBound : 2 ≤ bound)
    (hstore :
      NeighborhoodProgram.ValuesWithin allowed bound store) :
    ∃ final steps,
      InvariantRuns
        (NeighborhoodProgram.ValuesWithin allowed bound)
        (computeProtectedLog regs source
          (outputAddress regs resultSlot))
        store final steps ∧
      final (outputAddress regs resultSlot) =
        Nat.log 2 value + 1 := by
  let scratch := regs.stackRegisters
  let result := outputAddress regs resultSlot
  obtain ⟨afterCopy, hcopy, hcopyWord, _hcopyOutside⟩ :=
    copy_invariantRuns_internal allowed bound scratch.word source
      store hsourceNeWord (by simpa [hsource] using hvalueBound)
      hstore
  have hafterCopyWithin :
      NeighborhoodProgram.ValuesWithin allowed bound afterCopy :=
    InvariantRuns.final hcopy
  have hcopyWordValue : afterCopy scratch.word = value := by
    rw [hcopyWord, hsource]
  let afterBase := (Basic.imm scratch.base 2).exec afterCopy
  have hafterBaseWithin :
      NeighborhoodProgram.ValuesWithin allowed bound afterBase :=
    numericWithin_update_internal allowed bound scratch.base 2
      afterCopy hafterCopyWithin htwoBound
  let afterBasePred :=
    (Basic.imm scratch.basePred 1).exec afterBase
  have hafterBasePredWithin :
      NeighborhoodProgram.ValuesWithin allowed bound afterBasePred :=
    numericWithin_update_internal allowed bound scratch.basePred 1
      afterBase hafterBaseWithin (by omega)
  let afterOne := (Basic.imm scratch.one 1).exec afterBasePred
  have hafterOneWithin :
      NeighborhoodProgram.ValuesWithin allowed bound afterOne :=
    numericWithin_update_internal allowed bound scratch.one 1
      afterBasePred hafterBasePredWithin (by omega)
  let afterResult := (Basic.imm result 1).exec afterOne
  have hafterResultWithin :
      NeighborhoodProgram.ValuesWithin allowed bound afterResult :=
    numericWithin_update_internal allowed bound result 1 afterOne
      hafterOneWithin (by omega)
  let afterTest := (protectedLogTest regs).exec afterResult
  have hresultOutside : result ∉ scratch.footprint := by
    intro hmem
    obtain ⟨slot, _, hslot⟩ := Finset.mem_image.mp hmem
    exact
      (stack_index_ne_output_internal regs slot resultSlot) hslot
  have hafterResultWord :
      afterResult scratch.word = value := by
    have hwordNeBase : scratch.word ≠ scratch.base :=
      scratch.index_ne (by decide)
    have hwordNeBasePred : scratch.word ≠ scratch.basePred :=
      scratch.index_ne (by decide)
    have hwordNeOne : scratch.word ≠ scratch.one :=
      scratch.index_ne (by decide)
    have hwordNeResult : scratch.word ≠ result := by
      intro heq
      apply hresultOutside
      rw [← heq]
      exact
        NeighborhoodProgram.StackRegisters.index_mem_footprint
          scratch 0
    simp [afterResult, afterOne, afterBasePred, afterBase,
      Basic.exec, hwordNeBase, hwordNeBasePred, hwordNeOne,
      hwordNeResult, hcopyWordValue]
  have hafterResultBase :
      afterResult scratch.base = 2 := by
    have hbaseNeBasePred : scratch.base ≠ scratch.basePred :=
      scratch.index_ne (by decide)
    have hbaseNeOne : scratch.base ≠ scratch.one :=
      scratch.index_ne (by decide)
    have hbaseNeResult : scratch.base ≠ result := by
      intro heq
      apply hresultOutside
      rw [← heq]
      exact
        NeighborhoodProgram.StackRegisters.index_mem_footprint
          scratch 1
    simp [afterResult, afterOne, afterBasePred, afterBase,
      Basic.exec, hbaseNeBasePred, hbaseNeOne, hbaseNeResult]
  have hafterResultBasePred :
      afterResult scratch.basePred = 1 := by
    have hpredNeOne : scratch.basePred ≠ scratch.one :=
      scratch.index_ne (by decide)
    have hpredNeResult : scratch.basePred ≠ result := by
      intro heq
      apply hresultOutside
      rw [← heq]
      exact
        NeighborhoodProgram.StackRegisters.index_mem_footprint
          scratch 2
    simp [afterResult, afterOne, afterBasePred, Basic.exec,
      hpredNeOne, hpredNeResult]
  have hafterResultOne :
      afterResult scratch.one = 1 := by
    have honeNeResult : scratch.one ≠ result := by
      intro heq
      apply hresultOutside
      rw [← heq]
      exact
        NeighborhoodProgram.StackRegisters.index_mem_footprint
          scratch 5
    simp [afterResult, afterOne, Basic.exec, honeNeResult]
  have hafterResultResult : afterResult result = 1 := by
    simp [afterResult, Basic.exec]
  have hafterTestWithin :
      NeighborhoodProgram.ValuesWithin allowed bound afterTest := by
    apply numericWithin_update_internal allowed bound scratch.test
      (afterResult scratch.word - afterResult scratch.one)
      afterResult hafterResultWithin
    rw [hafterResultWord, hafterResultOne]
    exact (Nat.sub_le _ _).trans hvalueBound
  have hafterTestWord : afterTest scratch.word = value := by
    simp only [afterTest, protectedLogTest, Basic.exec]
    change Function.update afterResult scratch.test
      _ scratch.word = value
    simpa [scratch.index_ne (first := 0) (second := 4)
      (by decide)] using hafterResultWord
  have hafterTestBase : afterTest scratch.base = 2 := by
    simp only [afterTest, protectedLogTest, Basic.exec]
    change Function.update afterResult scratch.test
      _ scratch.base = 2
    simpa [scratch.index_ne (first := 1) (second := 4)
      (by decide)] using hafterResultBase
  have hafterTestBasePred :
      afterTest scratch.basePred = 1 := by
    simp only [afterTest, protectedLogTest, Basic.exec]
    change Function.update afterResult scratch.test
      _ scratch.basePred = 1
    simpa [scratch.index_ne (first := 2) (second := 4)
      (by decide)] using hafterResultBasePred
  have hafterTestOne : afterTest scratch.one = 1 := by
    simp only [afterTest, protectedLogTest, Basic.exec]
    change Function.update afterResult scratch.test
      _ scratch.one = 1
    simpa [scratch.index_ne (first := 5) (second := 4)
      (by decide)] using hafterResultOne
  have hafterTestResult : afterTest result = 1 := by
    have hne : result ≠ scratch.test := by
      intro heq
      apply hresultOutside
      rw [heq]
      exact
        NeighborhoodProgram.StackRegisters.index_mem_footprint
          scratch 4
    simp only [afterTest, protectedLogTest, Basic.exec]
    change Function.update afterResult scratch.test _ result = 1
    simpa [hne] using hafterResultResult
  have hafterTestTest : afterTest scratch.test = value - 1 := by
    simp only [afterTest, protectedLogTest, Basic.exec]
    rw [hafterResultWord, hafterResultOne]
    change Function.update afterResult scratch.test
      (value - 1) scratch.test = value - 1
    simp
  obtain ⟨final, loopSteps, hloop, hfinal⟩ :=
    protected_log_loop_invariantRuns_internal regs allowed bound
      result afterTest value 1 hafterTestWord hafterTestBase
      hafterTestBasePred hafterTestOne hafterTestResult
      hafterTestTest hresultOutside hvalueBound (by omega)
      hafterTestWithin
  refine ⟨final,
    2 + (1 + (1 + (1 + (1 + (1 + loopSteps))))), ?_, ?_⟩
  · simpa [computeProtectedLog, Cmd.seqList, scratch, result] using
      InvariantRuns.seq hcopy
        (InvariantRuns.seq
          (InvariantRuns.basic (Basic.imm scratch.base 2)
            afterCopy hafterCopyWithin hafterBaseWithin)
          (InvariantRuns.seq
            (InvariantRuns.basic (Basic.imm scratch.basePred 1)
              afterBase hafterBaseWithin hafterBasePredWithin)
            (InvariantRuns.seq
              (InvariantRuns.basic (Basic.imm scratch.one 1)
                afterBasePred hafterBasePredWithin hafterOneWithin)
              (InvariantRuns.seq
                (InvariantRuns.basic (Basic.imm result 1)
                  afterOne hafterOneWithin hafterResultWithin)
                (InvariantRuns.seq
                  (InvariantRuns.basic (protectedLogTest regs)
                    afterResult hafterResultWithin hafterTestWithin)
                  hloop)))))
  · rw [hfinal]
    omega

private theorem sqrt_loop_runs_internal
    (regs : Registers) (sourceSlot resultSlot : Fin 17)
    (store : Store) (value current remaining : ℕ)
    (hslots : sourceSlot ≠ resultSlot)
    (htarget :
      ComplexityBridge.positiveCeilSqrt value =
        current + remaining)
    (hcurrentPos : 0 < current)
    (hsource : store (outputAddress regs sourceSlot) = value)
    (hresult : store (outputAddress regs resultSlot) = current)
    (hsquare :
      store regs.stackRegisters.quotient = current * current)
    (hone : store regs.stackRegisters.one = 1)
    (htest :
      store regs.stackRegisters.test =
        value - current * current) :
    ∃ final,
      Runs
        (.whileNonzero regs.stackRegisters.test
          (sqrtBody regs (outputAddress regs sourceSlot)
            (outputAddress regs resultSlot)))
        store final ∧
      final (outputAddress regs resultSlot) =
        ComplexityBridge.positiveCeilSqrt value := by
  let scratch := regs.stackRegisters
  let source := outputAddress regs sourceSlot
  let result := outputAddress regs resultSlot
  induction remaining generalizing store current with
  | zero =>
      have hcurrent :
          ComplexityBridge.positiveCeilSqrt value = current := by
        simpa using htarget
      have hvalueLe :
          value ≤ current * current := by
        rw [← hcurrent]
        exact ComplexityBridge.positiveCeilSqrt_sq_ge value
      have htestZero : store scratch.test = 0 := by
        rw [htest]
        omega
      exact ⟨store, Runs.whileZero htestZero, hresult.trans hcurrent.symm⟩
  | succ remaining ih =>
      have hcurrentLt :
          current <
            ComplexityBridge.positiveCeilSqrt value := by
        omega
      have hvalueGt : current * current < value := by
        by_contra hnot
        have hvalueLe : value ≤ current * current := by omega
        have hceilLe :
            ComplexityBridge.ceilSqrt value ≤ current :=
          ComplexityBridge.ceilSqrt_le_iff.mpr hvalueLe
        have hpositiveLe :
            ComplexityBridge.positiveCeilSqrt value ≤ current := by
          unfold ComplexityBridge.positiveCeilSqrt
          exact max_le (by omega) hceilLe
        omega
      have htestNonzero : store scratch.test ≠ 0 := by
        rw [htest]
        omega
      let afterIncrement :=
        (Basic.add result result scratch.one).exec store
      have hincrementResult :
          afterIncrement result = current + 1 := by
        simp only [afterIncrement, Basic.exec]
        change Function.update store result
          (store result + store scratch.one) result = current + 1
        simp only [Function.update_self]
        change store (outputAddress regs resultSlot) +
          store regs.stackRegisters.one = current + 1
        rw [hresult, hone]
      have hincrementSource :
          afterIncrement source = value := by
        have hsourceNeResult : source ≠ result :=
          outputAddress_ne regs hslots
        simp only [afterIncrement, Basic.exec]
        change Function.update store result
          _ source = value
        simpa [hsourceNeResult] using hsource
      have hincrementOne :
          afterIncrement scratch.one = 1 := by
        have honeNeResult :
            scratch.one ≠ result :=
          stack_index_ne_output_internal regs 5 resultSlot
        simp only [afterIncrement, Basic.exec]
        change Function.update store result
          _ scratch.one = 1
        simpa [honeNeResult] using hone
      let afterSquare :=
        (Basic.mul scratch.quotient result result).exec
          afterIncrement
      have hafterSquareResult :
          afterSquare result = current + 1 := by
        have hresultNeQuotient :
            result ≠ scratch.quotient :=
          (stack_index_ne_output_internal regs 3 resultSlot).symm
        simp [afterSquare, Basic.exec, hresultNeQuotient,
          hincrementResult]
      have hafterSquareSource :
          afterSquare source = value := by
        have hsourceNeQuotient :
            source ≠ scratch.quotient :=
          (stack_index_ne_output_internal regs 3 sourceSlot).symm
        simp [afterSquare, Basic.exec, hsourceNeQuotient,
          hincrementSource]
      have hafterSquareOne :
          afterSquare scratch.one = 1 := by
        have honeNeQuotient :
            scratch.one ≠ scratch.quotient :=
          scratch.index_ne (by decide)
        simp [afterSquare, Basic.exec, honeNeQuotient,
          hincrementOne]
      have hafterSquareSquare :
          afterSquare scratch.quotient =
            (current + 1) * (current + 1) := by
        simp [afterSquare, Basic.exec, hincrementResult]
      let afterTest :=
        (sqrtTest regs source).exec afterSquare
      have hafterTestResult :
          afterTest result = current + 1 := by
        have hresultNeTest :
            result ≠ scratch.test :=
          (stack_index_ne_output_internal regs 4 resultSlot).symm
        simp only [afterTest, sqrtTest, Basic.exec]
        change Function.update afterSquare scratch.test
          _ result = current + 1
        simpa [hresultNeTest] using hafterSquareResult
      have hafterTestSource :
          afterTest source = value := by
        have hsourceNeTest :
            source ≠ scratch.test :=
          (stack_index_ne_output_internal regs 4 sourceSlot).symm
        simp only [afterTest, sqrtTest, Basic.exec]
        change Function.update afterSquare scratch.test
          _ source = value
        simpa [hsourceNeTest] using hafterSquareSource
      have hafterTestOne :
          afterTest scratch.one = 1 := by
        have honeNeTest :
            scratch.one ≠ scratch.test :=
          scratch.index_ne (by decide)
        simp only [afterTest, sqrtTest, Basic.exec]
        change Function.update afterSquare scratch.test
          _ scratch.one = 1
        simpa [honeNeTest] using hafterSquareOne
      have hafterTestSquare :
          afterTest scratch.quotient =
            (current + 1) * (current + 1) := by
        have hquotientNeTest :
            scratch.quotient ≠ scratch.test :=
          scratch.index_ne (by decide)
        simp only [afterTest, sqrtTest, Basic.exec]
        change Function.update afterSquare scratch.test
          _ scratch.quotient =
            (current + 1) * (current + 1)
        simpa [hquotientNeTest] using hafterSquareSquare
      have hafterTestTest :
          afterTest scratch.test =
            value - (current + 1) * (current + 1) := by
        simp only [afterTest, sqrtTest, Basic.exec]
        change Function.update afterSquare scratch.test
          (afterSquare source - afterSquare scratch.quotient)
          scratch.test =
            value - (current + 1) * (current + 1)
        simp [hafterSquareSource, hafterSquareSquare]
      have hbody :
          Runs (sqrtBody regs source result)
            store afterTest := by
        simpa [sqrtBody, Cmd.seqList] using
          Runs.seq
            (Runs.basic
              (Basic.add result result scratch.one) store)
            (Runs.seq
              (Runs.basic
                (Basic.mul scratch.quotient result result)
                afterIncrement)
              (Runs.basic (sqrtTest regs source)
                afterSquare))
      have htargetNext :
          ComplexityBridge.positiveCeilSqrt value =
            current + 1 + remaining := by
        omega
      obtain ⟨final, hloop, hfinal⟩ :=
        ih afterTest (current + 1) htargetNext (by omega)
          hafterTestSource hafterTestResult hafterTestSquare
          hafterTestOne hafterTestTest
      exact ⟨final,
        Runs.whileNonzero htestNonzero hbody hloop, hfinal⟩

private theorem sqrt_loop_invariantRuns_internal
    (regs : Registers) (allowed : Finset ℕ) (bound : ℕ)
    (sourceSlot resultSlot : Fin 17)
    (store : Store) (value current remaining : ℕ)
    (hslots : sourceSlot ≠ resultSlot)
    (htarget :
      ComplexityBridge.positiveCeilSqrt value =
        current + remaining)
    (hcurrentPos : 0 < current)
    (hsource : store (outputAddress regs sourceSlot) = value)
    (hresult : store (outputAddress regs resultSlot) = current)
    (hsquare :
      store regs.stackRegisters.quotient = current * current)
    (hone : store regs.stackRegisters.one = 1)
    (htest :
      store regs.stackRegisters.test =
        value - current * current)
    (hvalueBound : value ≤ bound)
    (htargetBound :
      ComplexityBridge.positiveCeilSqrt value ≤ bound)
    (hsquareBound :
      ComplexityBridge.positiveCeilSqrt value *
        ComplexityBridge.positiveCeilSqrt value ≤ bound)
    (hstore :
      NeighborhoodProgram.ValuesWithin allowed bound store) :
    ∃ final steps,
      InvariantRuns
        (NeighborhoodProgram.ValuesWithin allowed bound)
        (.whileNonzero regs.stackRegisters.test
          (sqrtBody regs (outputAddress regs sourceSlot)
            (outputAddress regs resultSlot)))
        store final steps ∧
      final (outputAddress regs resultSlot) =
        ComplexityBridge.positiveCeilSqrt value := by
  let scratch := regs.stackRegisters
  let source := outputAddress regs sourceSlot
  let result := outputAddress regs resultSlot
  induction remaining generalizing store current with
  | zero =>
      have hcurrent :
          ComplexityBridge.positiveCeilSqrt value = current := by
        simpa using htarget
      have hvalueLe :
          value ≤ current * current := by
        rw [← hcurrent]
        exact ComplexityBridge.positiveCeilSqrt_sq_ge value
      have htestZero : store scratch.test = 0 := by
        rw [htest]
        omega
      exact ⟨store, 1,
        InvariantRuns.whileZero htestZero hstore,
        hresult.trans hcurrent.symm⟩
  | succ remaining ih =>
      have hcurrentLt :
          current <
            ComplexityBridge.positiveCeilSqrt value := by
        omega
      have hvalueGt : current * current < value := by
        by_contra hnot
        have hvalueLe : value ≤ current * current := by omega
        have hceilLe :
            ComplexityBridge.ceilSqrt value ≤ current :=
          ComplexityBridge.ceilSqrt_le_iff.mpr hvalueLe
        have hpositiveLe :
            ComplexityBridge.positiveCeilSqrt value ≤ current := by
          unfold ComplexityBridge.positiveCeilSqrt
          exact max_le (by omega) hceilLe
        omega
      have htestNonzero : store scratch.test ≠ 0 := by
        rw [htest]
        omega
      let afterIncrement :=
        (Basic.add result result scratch.one).exec store
      have hincrementResult :
          afterIncrement result = current + 1 := by
        simp only [afterIncrement, Basic.exec]
        change Function.update store result
          (store result + store scratch.one) result = current + 1
        simp only [Function.update_self]
        change store (outputAddress regs resultSlot) +
          store regs.stackRegisters.one = current + 1
        rw [hresult, hone]
      have hincrementBound : current + 1 ≤ bound :=
        (by omega : current + 1 ≤
          ComplexityBridge.positiveCeilSqrt value).trans
          htargetBound
      have hafterIncrementWithin :
          NeighborhoodProgram.ValuesWithin allowed bound
            afterIncrement := by
        apply numericWithin_update_internal allowed bound result
          (store result + store scratch.one) store hstore
        rw [hresult, hone]
        exact hincrementBound
      have hincrementSource :
          afterIncrement source = value := by
        have hsourceNeResult : source ≠ result :=
          outputAddress_ne regs hslots
        simp only [afterIncrement, Basic.exec]
        change Function.update store result _ source = value
        simpa [hsourceNeResult] using hsource
      have hincrementOne :
          afterIncrement scratch.one = 1 := by
        have honeNeResult :
            scratch.one ≠ result :=
          stack_index_ne_output_internal regs 5 resultSlot
        simp only [afterIncrement, Basic.exec]
        change Function.update store result _ scratch.one = 1
        simpa [honeNeResult] using hone
      let afterSquare :=
        (Basic.mul scratch.quotient result result).exec
          afterIncrement
      have hafterSquareWithin :
          NeighborhoodProgram.ValuesWithin allowed bound afterSquare := by
        apply numericWithin_update_internal allowed bound
          scratch.quotient
          (afterIncrement result * afterIncrement result)
          afterIncrement hafterIncrementWithin
        rw [hincrementResult]
        exact Nat.mul_le_mul
          (by omega : current + 1 ≤
            ComplexityBridge.positiveCeilSqrt value)
          (by omega : current + 1 ≤
            ComplexityBridge.positiveCeilSqrt value) |>.trans
          hsquareBound
      have hafterSquareResult :
          afterSquare result = current + 1 := by
        have hresultNeQuotient :
            result ≠ scratch.quotient :=
          (stack_index_ne_output_internal regs 3 resultSlot).symm
        simp [afterSquare, Basic.exec, hresultNeQuotient,
          hincrementResult]
      have hafterSquareSource :
          afterSquare source = value := by
        have hsourceNeQuotient :
            source ≠ scratch.quotient :=
          (stack_index_ne_output_internal regs 3 sourceSlot).symm
        simp [afterSquare, Basic.exec, hsourceNeQuotient,
          hincrementSource]
      have hafterSquareOne :
          afterSquare scratch.one = 1 := by
        have honeNeQuotient :
            scratch.one ≠ scratch.quotient :=
          scratch.index_ne (by decide)
        simp [afterSquare, Basic.exec, honeNeQuotient,
          hincrementOne]
      have hafterSquareSquare :
          afterSquare scratch.quotient =
            (current + 1) * (current + 1) := by
        simp [afterSquare, Basic.exec, hincrementResult]
      let afterTest :=
        (sqrtTest regs source).exec afterSquare
      have hafterTestWithin :
          NeighborhoodProgram.ValuesWithin allowed bound afterTest := by
        apply numericWithin_update_internal allowed bound scratch.test
          (afterSquare source - afterSquare scratch.quotient)
          afterSquare hafterSquareWithin
        rw [hafterSquareSource]
        exact (Nat.sub_le _ _).trans hvalueBound
      have hafterTestResult :
          afterTest result = current + 1 := by
        have hresultNeTest :
            result ≠ scratch.test :=
          (stack_index_ne_output_internal regs 4 resultSlot).symm
        simp only [afterTest, sqrtTest, Basic.exec]
        change Function.update afterSquare scratch.test
          _ result = current + 1
        simpa [hresultNeTest] using hafterSquareResult
      have hafterTestSource :
          afterTest source = value := by
        have hsourceNeTest :
            source ≠ scratch.test :=
          (stack_index_ne_output_internal regs 4 sourceSlot).symm
        simp only [afterTest, sqrtTest, Basic.exec]
        change Function.update afterSquare scratch.test
          _ source = value
        simpa [hsourceNeTest] using hafterSquareSource
      have hafterTestOne :
          afterTest scratch.one = 1 := by
        have honeNeTest :
            scratch.one ≠ scratch.test :=
          scratch.index_ne (by decide)
        simp only [afterTest, sqrtTest, Basic.exec]
        change Function.update afterSquare scratch.test
          _ scratch.one = 1
        simpa [honeNeTest] using hafterSquareOne
      have hafterTestSquare :
          afterTest scratch.quotient =
            (current + 1) * (current + 1) := by
        have hquotientNeTest :
            scratch.quotient ≠ scratch.test :=
          scratch.index_ne (by decide)
        simp only [afterTest, sqrtTest, Basic.exec]
        change Function.update afterSquare scratch.test
          _ scratch.quotient =
            (current + 1) * (current + 1)
        simpa [hquotientNeTest] using hafterSquareSquare
      have hafterTestTest :
          afterTest scratch.test =
            value - (current + 1) * (current + 1) := by
        simp only [afterTest, sqrtTest, Basic.exec]
        change Function.update afterSquare scratch.test
          (afterSquare source - afterSquare scratch.quotient)
          scratch.test =
            value - (current + 1) * (current + 1)
        simp [hafterSquareSource, hafterSquareSquare]
      have hbody :
          InvariantRuns
            (NeighborhoodProgram.ValuesWithin allowed bound)
            (sqrtBody regs source result) store afterTest 3 := by
        simpa [sqrtBody, Cmd.seqList] using
          InvariantRuns.seq
            (InvariantRuns.basic
              (Basic.add result result scratch.one) store
              hstore hafterIncrementWithin)
            (InvariantRuns.seq
              (InvariantRuns.basic
                (Basic.mul scratch.quotient result result)
                afterIncrement hafterIncrementWithin
                hafterSquareWithin)
              (InvariantRuns.basic (sqrtTest regs source)
                afterSquare hafterSquareWithin hafterTestWithin))
      have htargetNext :
          ComplexityBridge.positiveCeilSqrt value =
            current + 1 + remaining := by
        omega
      obtain ⟨final, loopSteps, hloop, hfinal⟩ :=
        ih afterTest (current + 1) htargetNext (by omega)
          hafterTestSource hafterTestResult hafterTestSquare
          hafterTestOne hafterTestTest hafterTestWithin
      exact ⟨final, 3 + loopSteps + 2,
        InvariantRuns.whileNonzero htestNonzero hbody hloop,
        hfinal⟩

private theorem computePositiveCeilSqrt_runs_internal
    (regs : Registers) (sourceSlot resultSlot : Fin 17)
    (store : Store) (value : ℕ)
    (hslots : sourceSlot ≠ resultSlot)
    (hsource : store (outputAddress regs sourceSlot) = value) :
    ∃ final,
      Runs
        (computePositiveCeilSqrt regs (outputAddress regs sourceSlot)
          (outputAddress regs resultSlot))
        store final ∧
      final (outputAddress regs resultSlot) =
        ComplexityBridge.positiveCeilSqrt value := by
  let scratch := regs.stackRegisters
  let source := outputAddress regs sourceSlot
  let result := outputAddress regs resultSlot
  let afterOne := (Basic.imm scratch.one 1).exec store
  let afterResult := (Basic.imm result 1).exec afterOne
  let afterSquare := (Basic.imm scratch.quotient 1).exec afterResult
  let afterTest := (sqrtTest regs source).exec afterSquare
  have hsourceNeOne :
      source ≠ scratch.one :=
    (stack_index_ne_output_internal regs 5 sourceSlot).symm
  have hsourceNeResult :
      source ≠ result :=
    outputAddress_ne regs hslots
  have hsourceNeQuotient :
      source ≠ scratch.quotient :=
    (stack_index_ne_output_internal regs 3 sourceSlot).symm
  have hsourceNeTest :
      source ≠ scratch.test :=
    (stack_index_ne_output_internal regs 4 sourceSlot).symm
  have hresultNeQuotient :
      result ≠ scratch.quotient :=
    (stack_index_ne_output_internal regs 3 resultSlot).symm
  have hresultNeTest :
      result ≠ scratch.test :=
    (stack_index_ne_output_internal regs 4 resultSlot).symm
  have honeNeResult :
      scratch.one ≠ result :=
    stack_index_ne_output_internal regs 5 resultSlot
  have honeNeQuotient :
      scratch.one ≠ scratch.quotient :=
    scratch.index_ne (by decide)
  have honeNeTest :
      scratch.one ≠ scratch.test :=
    scratch.index_ne (by decide)
  have hquotientNeTest :
      scratch.quotient ≠ scratch.test :=
    scratch.index_ne (by decide)
  have hafterSquareSource : afterSquare source = value := by
    simp [afterSquare, afterResult, afterOne, Basic.exec,
      hsourceNeOne, hsourceNeResult, hsourceNeQuotient]
    simpa [source] using hsource
  have hafterSquareResult : afterSquare result = 1 := by
    simp [afterSquare, afterResult, Basic.exec, hresultNeQuotient]
  have hafterSquareOne : afterSquare scratch.one = 1 := by
    simp [afterSquare, afterResult, afterOne, Basic.exec,
      honeNeResult, honeNeQuotient]
  have hafterSquareSquare : afterSquare scratch.quotient = 1 := by
    simp [afterSquare, Basic.exec]
  have hafterTestSource : afterTest source = value := by
    simp only [afterTest, sqrtTest, Basic.exec]
    change Function.update afterSquare scratch.test
      _ source = value
    simpa [hsourceNeTest] using hafterSquareSource
  have hafterTestResult : afterTest result = 1 := by
    simp only [afterTest, sqrtTest, Basic.exec]
    change Function.update afterSquare scratch.test
      _ result = 1
    simpa [hresultNeTest] using hafterSquareResult
  have hafterTestOne : afterTest scratch.one = 1 := by
    simp only [afterTest, sqrtTest, Basic.exec]
    change Function.update afterSquare scratch.test
      _ scratch.one = 1
    simpa [honeNeTest] using hafterSquareOne
  have hafterTestSquare : afterTest scratch.quotient = 1 := by
    simp only [afterTest, sqrtTest, Basic.exec]
    change Function.update afterSquare scratch.test
      _ scratch.quotient = 1
    simpa [hquotientNeTest] using hafterSquareSquare
  have hafterTestTest :
      afterTest scratch.test = value - 1 := by
    simp only [afterTest, sqrtTest, Basic.exec]
    change Function.update afterSquare scratch.test
      (afterSquare source - afterSquare scratch.quotient)
      scratch.test = value - 1
    simp [hafterSquareSource, hafterSquareSquare]
  have htarget :
      ComplexityBridge.positiveCeilSqrt value =
        1 +
          (ComplexityBridge.positiveCeilSqrt value - 1) := by
    have hpositive :=
      ComplexityBridge.positiveCeilSqrt_pos value
    omega
  obtain ⟨final, hloop, hfinal⟩ :=
    sqrt_loop_runs_internal regs sourceSlot resultSlot afterTest
      value 1 (ComplexityBridge.positiveCeilSqrt value - 1)
      hslots htarget (by omega) hafterTestSource hafterTestResult
      (by simpa using hafterTestSquare) hafterTestOne
      (by simpa using hafterTestTest)
  refine ⟨final, ?_, hfinal⟩
  simpa [computePositiveCeilSqrt, Cmd.seqList, scratch, source,
    result] using
    Runs.seq (Runs.basic (Basic.imm scratch.one 1) store)
      (Runs.seq (Runs.basic (Basic.imm result 1) afterOne)
        (Runs.seq
          (Runs.basic (Basic.imm scratch.quotient 1) afterResult)
          (Runs.seq (Runs.basic (sqrtTest regs source) afterSquare)
            hloop)))

private theorem computePositiveCeilSqrt_invariantRuns_internal
    (regs : Registers) (allowed : Finset ℕ) (bound : ℕ)
    (sourceSlot resultSlot : Fin 17)
    (store : Store) (value : ℕ)
    (hslots : sourceSlot ≠ resultSlot)
    (hsource : store (outputAddress regs sourceSlot) = value)
    (hvalueBound : value ≤ bound)
    (htargetBound :
      ComplexityBridge.positiveCeilSqrt value ≤ bound)
    (hsquareBound :
      ComplexityBridge.positiveCeilSqrt value *
        ComplexityBridge.positiveCeilSqrt value ≤ bound)
    (hstore :
      NeighborhoodProgram.ValuesWithin allowed bound store) :
    ∃ final steps,
      InvariantRuns
        (NeighborhoodProgram.ValuesWithin allowed bound)
        (computePositiveCeilSqrt regs
          (outputAddress regs sourceSlot)
          (outputAddress regs resultSlot))
        store final steps ∧
      final (outputAddress regs resultSlot) =
        ComplexityBridge.positiveCeilSqrt value := by
  let scratch := regs.stackRegisters
  let source := outputAddress regs sourceSlot
  let result := outputAddress regs resultSlot
  have honeBound : 1 ≤ bound := by
    have hpositive :=
      ComplexityBridge.positiveCeilSqrt_pos value
    omega
  let afterOne := (Basic.imm scratch.one 1).exec store
  have hafterOneWithin :
      NeighborhoodProgram.ValuesWithin allowed bound afterOne :=
    numericWithin_update_internal allowed bound scratch.one 1
      store hstore honeBound
  let afterResult := (Basic.imm result 1).exec afterOne
  have hafterResultWithin :
      NeighborhoodProgram.ValuesWithin allowed bound afterResult :=
    numericWithin_update_internal allowed bound result 1
      afterOne hafterOneWithin honeBound
  let afterSquare := (Basic.imm scratch.quotient 1).exec afterResult
  have hafterSquareWithin :
      NeighborhoodProgram.ValuesWithin allowed bound afterSquare :=
    numericWithin_update_internal allowed bound scratch.quotient 1
      afterResult hafterResultWithin honeBound
  let afterTest := (sqrtTest regs source).exec afterSquare
  have hsourceNeOne :
      source ≠ scratch.one :=
    (stack_index_ne_output_internal regs 5 sourceSlot).symm
  have hsourceNeResult :
      source ≠ result :=
    outputAddress_ne regs hslots
  have hsourceNeQuotient :
      source ≠ scratch.quotient :=
    (stack_index_ne_output_internal regs 3 sourceSlot).symm
  have hsourceNeTest :
      source ≠ scratch.test :=
    (stack_index_ne_output_internal regs 4 sourceSlot).symm
  have hresultNeQuotient :
      result ≠ scratch.quotient :=
    (stack_index_ne_output_internal regs 3 resultSlot).symm
  have hresultNeTest :
      result ≠ scratch.test :=
    (stack_index_ne_output_internal regs 4 resultSlot).symm
  have honeNeResult :
      scratch.one ≠ result :=
    stack_index_ne_output_internal regs 5 resultSlot
  have honeNeQuotient :
      scratch.one ≠ scratch.quotient :=
    scratch.index_ne (by decide)
  have honeNeTest :
      scratch.one ≠ scratch.test :=
    scratch.index_ne (by decide)
  have hquotientNeTest :
      scratch.quotient ≠ scratch.test :=
    scratch.index_ne (by decide)
  have hafterSquareSource : afterSquare source = value := by
    simp [afterSquare, afterResult, afterOne, Basic.exec,
      hsourceNeOne, hsourceNeResult, hsourceNeQuotient]
    simpa [source] using hsource
  have hafterSquareResult : afterSquare result = 1 := by
    simp [afterSquare, afterResult, Basic.exec, hresultNeQuotient]
  have hafterSquareOne : afterSquare scratch.one = 1 := by
    simp [afterSquare, afterResult, afterOne, Basic.exec,
      honeNeResult, honeNeQuotient]
  have hafterSquareSquare : afterSquare scratch.quotient = 1 := by
    simp [afterSquare, Basic.exec]
  have hafterTestWithin :
      NeighborhoodProgram.ValuesWithin allowed bound afterTest := by
    apply numericWithin_update_internal allowed bound scratch.test
      (afterSquare source - afterSquare scratch.quotient)
      afterSquare hafterSquareWithin
    rw [hafterSquareSource]
    exact (Nat.sub_le _ _).trans hvalueBound
  have hafterTestSource : afterTest source = value := by
    simp only [afterTest, sqrtTest, Basic.exec]
    change Function.update afterSquare scratch.test _ source = value
    simpa [hsourceNeTest] using hafterSquareSource
  have hafterTestResult : afterTest result = 1 := by
    simp only [afterTest, sqrtTest, Basic.exec]
    change Function.update afterSquare scratch.test _ result = 1
    simpa [hresultNeTest] using hafterSquareResult
  have hafterTestOne : afterTest scratch.one = 1 := by
    simp only [afterTest, sqrtTest, Basic.exec]
    change Function.update afterSquare scratch.test _ scratch.one = 1
    simpa [honeNeTest] using hafterSquareOne
  have hafterTestSquare : afterTest scratch.quotient = 1 := by
    simp only [afterTest, sqrtTest, Basic.exec]
    change Function.update afterSquare scratch.test
      _ scratch.quotient = 1
    simpa [hquotientNeTest] using hafterSquareSquare
  have hafterTestTest : afterTest scratch.test = value - 1 := by
    simp only [afterTest, sqrtTest, Basic.exec]
    change Function.update afterSquare scratch.test
      (afterSquare source - afterSquare scratch.quotient)
      scratch.test = value - 1
    simp [hafterSquareSource, hafterSquareSquare]
  have htarget :
      ComplexityBridge.positiveCeilSqrt value =
        1 + (ComplexityBridge.positiveCeilSqrt value - 1) := by
    have hpositive :=
      ComplexityBridge.positiveCeilSqrt_pos value
    omega
  obtain ⟨final, loopSteps, hloop, hfinal⟩ :=
    sqrt_loop_invariantRuns_internal regs allowed bound
      sourceSlot resultSlot afterTest value 1
      (ComplexityBridge.positiveCeilSqrt value - 1) hslots htarget
      (by omega) hafterTestSource hafterTestResult
      (by simpa using hafterTestSquare) hafterTestOne
      (by simpa using hafterTestTest) hvalueBound htargetBound
      hsquareBound hafterTestWithin
  refine ⟨final, 1 + (1 + (1 + (1 + loopSteps))), ?_, hfinal⟩
  simpa [computePositiveCeilSqrt, Cmd.seqList, scratch, source,
    result] using
    InvariantRuns.seq
      (InvariantRuns.basic (Basic.imm scratch.one 1) store
        hstore hafterOneWithin)
      (InvariantRuns.seq
        (InvariantRuns.basic (Basic.imm result 1) afterOne
          hafterOneWithin hafterResultWithin)
        (InvariantRuns.seq
          (InvariantRuns.basic (Basic.imm scratch.quotient 1)
            afterResult hafterResultWithin hafterSquareWithin)
          (InvariantRuns.seq
            (InvariantRuns.basic (sqrtTest regs source) afterSquare
              hafterSquareWithin hafterTestWithin)
            hloop)))

private theorem computeCeilDiv_runs_internal
    (regs : Registers)
    (dividend divisor : ℕ) (resultSlot : Fin 17)
    (store : Store) (dividendValue divisorValue : ℕ)
    (hdividend : store dividend = dividendValue)
    (hdivisor : store divisor = divisorValue)
    (hdivisorPos : 0 < divisorValue)
    (hdividendNeWord : regs.stackRegisters.word ≠ dividend)
    (hdivisorNeWord : regs.stackRegisters.word ≠ divisor)
    (hdivisorNeBase : regs.stackRegisters.base ≠ divisor)
    (hdividendNeOne : regs.stackRegisters.one ≠ dividend)
    (hdivisorNeOne : regs.stackRegisters.one ≠ divisor) :
    ∃ final,
      Runs
        (computeCeilDiv regs dividend divisor
          (outputAddress regs resultSlot))
        store final ∧
      final (outputAddress regs resultSlot) =
        dividendValue ⌈/⌉ divisorValue := by
  let scratch := regs.stackRegisters
  let result := outputAddress regs resultSlot
  let afterOne := (Basic.imm scratch.one 1).exec store
  have hafterOneDividend :
      afterOne dividend = dividendValue := by
    have hne : scratch.one ≠ dividend := by
      simpa [scratch] using hdividendNeOne
    simp only [afterOne, Basic.exec]
    change Function.update store scratch.one 1 dividend =
      dividendValue
    rw [Function.update_apply, if_neg hne.symm]
    exact hdividend
  have hafterOneDivisor :
      afterOne divisor = divisorValue := by
    have hne : scratch.one ≠ divisor := by
      simpa [scratch] using hdivisorNeOne
    simp only [afterOne, Basic.exec]
    change Function.update store scratch.one 1 divisor =
      divisorValue
    rw [Function.update_apply, if_neg hne.symm]
    exact hdivisor
  let afterWord :=
    copyResultStore scratch.word dividend afterOne
  have hcopyWord :
      Runs (copy scratch.word dividend) afterOne afterWord :=
    copy_runs_internal scratch.word dividend afterOne
      hdividendNeWord
  have hafterWordWord :
      afterWord scratch.word = dividendValue := by
    simpa [afterWord, hafterOneDividend] using
      copy_result_internal scratch.word dividend afterOne
        hdividendNeWord
  have hafterWordDivisor :
      afterWord divisor = divisorValue := by
    have hne : scratch.word ≠ divisor := by
      simpa [scratch] using hdivisorNeWord
    change Function.update afterOne scratch.word
      (afterOne dividend) divisor = divisorValue
    rw [Function.update_apply, if_neg hne.symm]
    exact hafterOneDivisor
  have hafterWordOne : afterWord scratch.one = 1 := by
    have honeNeWord :
        scratch.one ≠ scratch.word :=
      scratch.index_ne (by decide)
    simp [afterWord, copyResultStore, honeNeWord, afterOne,
      Basic.exec]
  let afterBase :=
    copyResultStore scratch.base divisor afterWord
  have hcopyBase :
      Runs (copy scratch.base divisor) afterWord afterBase :=
    copy_runs_internal scratch.base divisor afterWord
      hdivisorNeBase
  have hafterBaseBase :
      afterBase scratch.base = divisorValue := by
    simpa [afterBase, hafterWordDivisor] using
      copy_result_internal scratch.base divisor afterWord
        hdivisorNeBase
  have hafterBaseWord :
      afterBase scratch.word = dividendValue := by
    have hwordNeBase :
        scratch.word ≠ scratch.base :=
      scratch.index_ne (by decide)
    simp [afterBase, copyResultStore, hwordNeBase,
      hafterWordWord]
  have hafterBaseOne :
      afterBase scratch.one = 1 := by
    have honeNeBase :
        scratch.one ≠ scratch.base :=
      scratch.index_ne (by decide)
    simp [afterBase, copyResultStore, honeNeBase,
      hafterWordOne]
  let afterBasePred :=
    (Basic.sub scratch.basePred scratch.base scratch.one).exec
      afterBase
  have hafterPredBase :
      afterBasePred scratch.base = divisorValue := by
    have hbaseNePred :
        scratch.base ≠ scratch.basePred :=
      scratch.index_ne (by decide)
    simp [afterBasePred, Basic.exec, hbaseNePred,
      hafterBaseBase]
  have hafterPredBasePred :
      afterBasePred scratch.basePred = divisorValue - 1 := by
    simp [afterBasePred, Basic.exec, hafterBaseBase,
      hafterBaseOne]
  have hafterPredWord :
      afterBasePred scratch.word = dividendValue := by
    have hwordNePred :
        scratch.word ≠ scratch.basePred :=
      scratch.index_ne (by decide)
    simp [afterBasePred, Basic.exec, hwordNePred,
      hafterBaseWord]
  have hafterPredOne :
      afterBasePred scratch.one = 1 := by
    have honeNePred :
        scratch.one ≠ scratch.basePred :=
      scratch.index_ne (by decide)
    simp [afterBasePred, Basic.exec, honeNePred,
      hafterBaseOne]
  let afterNumerator :=
    (Basic.add scratch.word scratch.word scratch.basePred).exec
      afterBasePred
  have hafterNumeratorWord :
      afterNumerator scratch.word =
        dividendValue + (divisorValue - 1) := by
    simp [afterNumerator, Basic.exec, hafterPredWord,
      hafterPredBasePred]
  have hafterNumeratorBase :
      afterNumerator scratch.base = divisorValue := by
    have hbaseNeWord :
        scratch.base ≠ scratch.word :=
      scratch.index_ne (by decide)
    simp [afterNumerator, Basic.exec, hbaseNeWord,
      hafterPredBase]
  have hafterNumeratorBasePred :
      afterNumerator scratch.basePred = divisorValue - 1 := by
    have hpredNeWord :
        scratch.basePred ≠ scratch.word :=
      scratch.index_ne (by decide)
    simp [afterNumerator, Basic.exec, hpredNeWord,
      hafterPredBasePred]
  have hafterNumeratorOne :
      afterNumerator scratch.one = 1 := by
    have honeNeWord :
        scratch.one ≠ scratch.word :=
      scratch.index_ne (by decide)
    simp [afterNumerator, Basic.exec, honeNeWord,
      hafterPredOne]
  obtain ⟨afterPop, hpop, hpopWord, _hquotient, _htest,
      _hbase, _hbasePred, _hone⟩ :=
    NeighborhoodProgram.pop_runs scratch afterNumerator
      divisorValue (dividendValue + (divisorValue - 1))
      hdivisorPos hafterNumeratorWord hafterNumeratorBase
      hafterNumeratorBasePred hafterNumeratorOne
  let final :=
    copyResultStore result scratch.word afterPop
  have hresultNeWord :
      result ≠ scratch.word :=
    (stack_index_ne_output_internal regs 0 resultSlot).symm
  have hcopyResult :
      Runs (copy result scratch.word) afterPop final :=
    copy_runs_internal result scratch.word afterPop hresultNeWord
  have hfinal :
      final result =
        (dividendValue + (divisorValue - 1)) /
          divisorValue := by
    simpa [final, hpopWord, PackedDigits.pop] using
      copy_result_internal result scratch.word afterPop
        hresultNeWord
  refine ⟨final, ?_, ?_⟩
  · simpa [computeCeilDiv, Cmd.seqList, scratch, result] using
      Runs.seq (Runs.basic (Basic.imm scratch.one 1) store)
        (Runs.seq hcopyWord
          (Runs.seq hcopyBase
            (Runs.seq
              (Runs.basic
                (Basic.sub scratch.basePred scratch.base scratch.one)
                afterBase)
              (Runs.seq
                (Runs.basic
                  (Basic.add scratch.word scratch.word
                    scratch.basePred)
                  afterBasePred)
                (Runs.seq hpop hcopyResult)))))
  · rw [hfinal, Nat.ceilDiv_eq_add_pred_div]
    rw [Nat.add_sub_assoc (by omega)]

private theorem computeCeilDiv_invariantRuns_internal
    (regs : Registers) (allowed : Finset ℕ) (bound : ℕ)
    (dividend divisor : ℕ) (resultSlot : Fin 17)
    (store : Store) (dividendValue divisorValue : ℕ)
    (hdividend : store dividend = dividendValue)
    (hdivisor : store divisor = divisorValue)
    (hdivisorPos : 0 < divisorValue)
    (hdividendNeWord : regs.stackRegisters.word ≠ dividend)
    (hdivisorNeWord : regs.stackRegisters.word ≠ divisor)
    (hdivisorNeBase : regs.stackRegisters.base ≠ divisor)
    (hdividendNeOne : regs.stackRegisters.one ≠ dividend)
    (hdivisorNeOne : regs.stackRegisters.one ≠ divisor)
    (hdividendBound : dividendValue ≤ bound)
    (hdivisorBound : divisorValue ≤ bound)
    (hnumeratorBound :
      dividendValue + (divisorValue - 1) ≤ bound)
    (hstore :
      NeighborhoodProgram.ValuesWithin allowed bound store) :
    ∃ final steps,
      InvariantRuns
        (NeighborhoodProgram.ValuesWithin allowed bound)
        (computeCeilDiv regs dividend divisor
          (outputAddress regs resultSlot))
        store final steps ∧
      final (outputAddress regs resultSlot) =
        dividendValue ⌈/⌉ divisorValue := by
  let scratch := regs.stackRegisters
  let result := outputAddress regs resultSlot
  let afterOne := (Basic.imm scratch.one 1).exec store
  have hafterOneWithin :
      NeighborhoodProgram.ValuesWithin allowed bound afterOne :=
    numericWithin_update_internal allowed bound scratch.one 1 store
      hstore (by omega)
  have hafterOneDividend : afterOne dividend = dividendValue := by
    simp only [afterOne, Basic.exec]
    rw [Function.update_apply, if_neg hdividendNeOne.symm]
    exact hdividend
  have hafterOneDivisor : afterOne divisor = divisorValue := by
    simp only [afterOne, Basic.exec]
    rw [Function.update_apply, if_neg hdivisorNeOne.symm]
    exact hdivisor
  obtain ⟨afterWord, hcopyWord, hafterWordWord,
      hafterWordOutside⟩ :=
    copy_invariantRuns_internal allowed bound scratch.word dividend
      afterOne hdividendNeWord
      (by simpa [hafterOneDividend] using hdividendBound)
      hafterOneWithin
  have hafterWordWithin :
      NeighborhoodProgram.ValuesWithin allowed bound afterWord :=
    InvariantRuns.final hcopyWord
  have hafterWordWordValue :
      afterWord scratch.word = dividendValue := by
    rw [hafterWordWord, hafterOneDividend]
  have hafterWordDivisor :
      afterWord divisor = divisorValue := by
    rw [hafterWordOutside divisor hdivisorNeWord.symm]
    exact hafterOneDivisor
  have hafterWordOne : afterWord scratch.one = 1 := by
    rw [hafterWordOutside scratch.one
      (scratch.index_ne (first := 5) (second := 0) (by decide))]
    simp [afterOne, Basic.exec]
  obtain ⟨afterBase, hcopyBase, hafterBaseBase,
      hafterBaseOutside⟩ :=
    copy_invariantRuns_internal allowed bound scratch.base divisor
      afterWord hdivisorNeBase
      (by simpa [hafterWordDivisor] using hdivisorBound)
      hafterWordWithin
  have hafterBaseWithin :
      NeighborhoodProgram.ValuesWithin allowed bound afterBase :=
    InvariantRuns.final hcopyBase
  have hafterBaseBaseValue :
      afterBase scratch.base = divisorValue := by
    rw [hafterBaseBase, hafterWordDivisor]
  have hafterBaseWord :
      afterBase scratch.word = dividendValue := by
    rw [hafterBaseOutside scratch.word
      (scratch.index_ne (first := 0) (second := 1) (by decide))]
    exact hafterWordWordValue
  have hafterBaseOne : afterBase scratch.one = 1 := by
    rw [hafterBaseOutside scratch.one
      (scratch.index_ne (first := 5) (second := 1) (by decide))]
    exact hafterWordOne
  let afterBasePred :=
    (Basic.sub scratch.basePred scratch.base scratch.one).exec
      afterBase
  have hafterBasePredWithin :
      NeighborhoodProgram.ValuesWithin allowed bound afterBasePred := by
    apply numericWithin_update_internal allowed bound scratch.basePred
      (afterBase scratch.base - afterBase scratch.one)
      afterBase hafterBaseWithin
    rw [hafterBaseBaseValue, hafterBaseOne]
    exact (Nat.sub_le _ _).trans hdivisorBound
  have hafterPredBase :
      afterBasePred scratch.base = divisorValue := by
    simp [afterBasePred, Basic.exec,
      scratch.index_ne (first := 1) (second := 2) (by decide),
      hafterBaseBaseValue]
  have hafterPredBasePred :
      afterBasePred scratch.basePred = divisorValue - 1 := by
    simp [afterBasePred, Basic.exec, hafterBaseBaseValue,
      hafterBaseOne]
  have hafterPredWord :
      afterBasePred scratch.word = dividendValue := by
    simp [afterBasePred, Basic.exec,
      scratch.index_ne (first := 0) (second := 2) (by decide),
      hafterBaseWord]
  have hafterPredOne :
      afterBasePred scratch.one = 1 := by
    simp [afterBasePred, Basic.exec,
      scratch.index_ne (first := 5) (second := 2) (by decide),
      hafterBaseOne]
  let afterNumerator :=
    (Basic.add scratch.word scratch.word scratch.basePred).exec
      afterBasePred
  have hafterNumeratorWithin :
      NeighborhoodProgram.ValuesWithin allowed bound
        afterNumerator := by
    apply numericWithin_update_internal allowed bound scratch.word
      (afterBasePred scratch.word +
        afterBasePred scratch.basePred)
      afterBasePred hafterBasePredWithin
    rw [hafterPredWord, hafterPredBasePred]
    exact hnumeratorBound
  have hafterNumeratorWord :
      afterNumerator scratch.word =
        dividendValue + (divisorValue - 1) := by
    simp [afterNumerator, Basic.exec, hafterPredWord,
      hafterPredBasePred]
  have hafterNumeratorBase :
      afterNumerator scratch.base = divisorValue := by
    simp [afterNumerator, Basic.exec,
      scratch.index_ne (first := 1) (second := 0) (by decide),
      hafterPredBase]
  have hafterNumeratorBasePred :
      afterNumerator scratch.basePred = divisorValue - 1 := by
    simp [afterNumerator, Basic.exec,
      scratch.index_ne (first := 2) (second := 0) (by decide),
      hafterPredBasePred]
  have hafterNumeratorOne :
      afterNumerator scratch.one = 1 := by
    simp [afterNumerator, Basic.exec,
      scratch.index_ne (first := 5) (second := 0) (by decide),
      hafterPredOne]
  obtain ⟨afterPop, popSteps, hpop, hpopWord,
      _hquotient, _htest, _hbase, _hbasePred, _hone⟩ :=
    NeighborhoodProgram.pop_invariantRuns scratch allowed bound
      afterNumerator divisorValue
      (dividendValue + (divisorValue - 1)) hdivisorPos
      hafterNumeratorWord hafterNumeratorBase
      hafterNumeratorBasePred hafterNumeratorOne
      hnumeratorBound hafterNumeratorWithin
  have hafterPopWithin :
      NeighborhoodProgram.ValuesWithin allowed bound afterPop :=
    InvariantRuns.final hpop
  have hresultNeWord :
      result ≠ scratch.word :=
    (stack_index_ne_output_internal regs 0 resultSlot).symm
  have hpopWordBound : afterPop scratch.word ≤ bound := by
    rw [hpopWord, PackedDigits.pop]
    exact (Nat.div_le_self _ _).trans hnumeratorBound
  obtain ⟨final, hcopyResult, hfinalResult,
      _hfinalOutside⟩ :=
    copy_invariantRuns_internal allowed bound result scratch.word
      afterPop hresultNeWord hpopWordBound hafterPopWithin
  have hfinal :
      final result =
        (dividendValue + (divisorValue - 1)) /
          divisorValue := by
    rw [hfinalResult, hpopWord, PackedDigits.pop]
  refine ⟨final,
    1 + (2 + (2 + (1 + (1 + (popSteps + 2))))), ?_, ?_⟩
  · simpa [computeCeilDiv, Cmd.seqList, scratch, result] using
      InvariantRuns.seq
        (InvariantRuns.basic (Basic.imm scratch.one 1) store
          hstore hafterOneWithin)
        (InvariantRuns.seq hcopyWord
          (InvariantRuns.seq hcopyBase
            (InvariantRuns.seq
              (InvariantRuns.basic
                (Basic.sub scratch.basePred scratch.base scratch.one)
                afterBase hafterBaseWithin hafterBasePredWithin)
              (InvariantRuns.seq
                (InvariantRuns.basic
                  (Basic.add scratch.word scratch.word
                    scratch.basePred)
                  afterBasePred hafterBasePredWithin
                  hafterNumeratorWithin)
                (InvariantRuns.seq hpop hcopyResult)))))
  · rw [hfinal, Nat.ceilDiv_eq_add_pred_div]
    rw [Nat.add_sub_assoc (by omega)]

private theorem pow_two_loop_runs_internal
    (regs : Registers) (resultSlot : Fin 17)
    (store : Store) (remaining accumulator : ℕ)
    (hremaining :
      store regs.stackRegisters.word = remaining)
    (hbase : store regs.stackRegisters.base = 2)
    (hone : store regs.stackRegisters.one = 1)
    (haccumulator :
      store (outputAddress regs resultSlot) = accumulator) :
    ∃ final,
      Runs
        (.whileNonzero regs.stackRegisters.word
          (powTwoBody regs (outputAddress regs resultSlot)))
        store final ∧
      final (outputAddress regs resultSlot) =
        accumulator * 2 ^ remaining := by
  let scratch := regs.stackRegisters
  let result := outputAddress regs resultSlot
  induction remaining generalizing store accumulator with
  | zero =>
      have hzero : store scratch.word = 0 := by
        simpa using hremaining
      refine ⟨store, Runs.whileZero hzero, ?_⟩
      simp [haccumulator]
  | succ remaining ih =>
      have hnonzero : store scratch.word ≠ 0 := by
        rw [hremaining]
        omega
      let afterMul :=
        (Basic.mul result result scratch.base).exec store
      have hafterMulResult :
          afterMul result = accumulator * 2 := by
        simp only [afterMul, Basic.exec]
        change Function.update store result
          (store result * store scratch.base) result =
            accumulator * 2
        simp only [Function.update_apply]
        change store (outputAddress regs resultSlot) *
          store regs.stackRegisters.base = accumulator * 2
        rw [haccumulator, hbase]
      have hafterMulWord :
          afterMul scratch.word = remaining + 1 := by
        have hwordNeResult :
            scratch.word ≠ result :=
          stack_index_ne_output_internal regs 0 resultSlot
        simp only [afterMul, Basic.exec]
        change Function.update store result
          _ scratch.word = remaining + 1
        rw [Function.update_apply, if_neg hwordNeResult]
        simpa [scratch] using hremaining
      have hafterMulBase :
          afterMul scratch.base = 2 := by
        have hbaseNeResult :
            scratch.base ≠ result :=
          stack_index_ne_output_internal regs 1 resultSlot
        simp only [afterMul, Basic.exec]
        change Function.update store result
          _ scratch.base = 2
        rw [Function.update_apply, if_neg hbaseNeResult]
        simpa [scratch] using hbase
      have hafterMulOne :
          afterMul scratch.one = 1 := by
        have honeNeResult :
            scratch.one ≠ result :=
          stack_index_ne_output_internal regs 5 resultSlot
        simp only [afterMul, Basic.exec]
        change Function.update store result
          _ scratch.one = 1
        rw [Function.update_apply, if_neg honeNeResult]
        simpa [scratch] using hone
      let afterDecrement :=
        (Basic.sub scratch.word scratch.word scratch.one).exec
          afterMul
      have hafterDecrementWord :
          afterDecrement scratch.word = remaining := by
        simp [afterDecrement, Basic.exec, hafterMulWord,
          hafterMulOne]
      have hafterDecrementResult :
          afterDecrement result = accumulator * 2 := by
        have hresultNeWord :
            result ≠ scratch.word :=
          (stack_index_ne_output_internal regs 0 resultSlot).symm
        simp [afterDecrement, Basic.exec, hresultNeWord,
          hafterMulResult]
      have hafterDecrementBase :
          afterDecrement scratch.base = 2 := by
        have hbaseNeWord :
            scratch.base ≠ scratch.word :=
          scratch.index_ne (by decide)
        simp [afterDecrement, Basic.exec, hbaseNeWord,
          hafterMulBase]
      have hafterDecrementOne :
          afterDecrement scratch.one = 1 := by
        have honeNeWord :
            scratch.one ≠ scratch.word :=
          scratch.index_ne (by decide)
        simp [afterDecrement, Basic.exec, honeNeWord,
          hafterMulOne]
      have hbody :
          Runs (powTwoBody regs result)
            store afterDecrement := by
        exact Runs.seq
          (Runs.basic (Basic.mul result result scratch.base) store)
          (Runs.basic
            (Basic.sub scratch.word scratch.word scratch.one)
            afterMul)
      obtain ⟨final, hloop, hfinal⟩ :=
        ih afterDecrement (accumulator * 2)
          hafterDecrementWord hafterDecrementBase
          hafterDecrementOne hafterDecrementResult
      refine ⟨final,
        Runs.whileNonzero hnonzero hbody hloop, ?_⟩
      rw [hfinal, pow_succ]
      ring

private theorem pow_two_loop_invariantRuns_internal
    (regs : Registers) (allowed : Finset ℕ) (bound : ℕ)
    (resultSlot : Fin 17)
    (store : Store) (remaining accumulator : ℕ)
    (hremaining :
      store regs.stackRegisters.word = remaining)
    (hbase : store regs.stackRegisters.base = 2)
    (hone : store regs.stackRegisters.one = 1)
    (haccumulator :
      store (outputAddress regs resultSlot) = accumulator)
    (hremainingBound : remaining ≤ bound)
    (htotalBound : accumulator * 2 ^ remaining ≤ bound)
    (hstore :
      NeighborhoodProgram.ValuesWithin allowed bound store) :
    ∃ final steps,
      InvariantRuns
        (NeighborhoodProgram.ValuesWithin allowed bound)
        (.whileNonzero regs.stackRegisters.word
          (powTwoBody regs (outputAddress regs resultSlot)))
        store final steps ∧
      final (outputAddress regs resultSlot) =
        accumulator * 2 ^ remaining := by
  let scratch := regs.stackRegisters
  let result := outputAddress regs resultSlot
  induction remaining generalizing store accumulator with
  | zero =>
      have hzero : store scratch.word = 0 := by
        simpa using hremaining
      refine ⟨store, 1,
        InvariantRuns.whileZero hzero hstore, ?_⟩
      simp [haccumulator]
  | succ remaining ih =>
      have hnonzero : store scratch.word ≠ 0 := by
        rw [hremaining]
        omega
      let afterMul :=
        (Basic.mul result result scratch.base).exec store
      have hafterMulResult :
          afterMul result = accumulator * 2 := by
        simp only [afterMul, Basic.exec]
        change Function.update store result
          (store result * store scratch.base) result =
            accumulator * 2
        simp only [Function.update_self]
        change store (outputAddress regs resultSlot) *
          store regs.stackRegisters.base = accumulator * 2
        rw [haccumulator, hbase]
      have hmulBound : accumulator * 2 ≤ bound := by
        calc
          accumulator * 2 ≤
              accumulator * (2 ^ remaining * 2) :=
            Nat.mul_le_mul_left accumulator
              (Nat.mul_le_mul_right 2 Nat.one_le_two_pow)
          _ = accumulator * 2 ^ (remaining + 1) := by
            rw [pow_succ]
          _ ≤ bound := htotalBound
      have hafterMulWithin :
          NeighborhoodProgram.ValuesWithin allowed bound afterMul := by
        apply numericWithin_update_internal allowed bound result
          (store result * store scratch.base) store hstore
        rw [haccumulator, hbase]
        exact hmulBound
      have hafterMulWord :
          afterMul scratch.word = remaining + 1 := by
        have hwordNeResult :
            scratch.word ≠ result :=
          stack_index_ne_output_internal regs 0 resultSlot
        simp only [afterMul, Basic.exec]
        change Function.update store result _ scratch.word =
          remaining + 1
        rw [Function.update_apply, if_neg hwordNeResult]
        simpa [scratch] using hremaining
      have hafterMulBase : afterMul scratch.base = 2 := by
        have hbaseNeResult :
            scratch.base ≠ result :=
          stack_index_ne_output_internal regs 1 resultSlot
        simp only [afterMul, Basic.exec]
        change Function.update store result _ scratch.base = 2
        rw [Function.update_apply, if_neg hbaseNeResult]
        simpa [scratch] using hbase
      have hafterMulOne : afterMul scratch.one = 1 := by
        have honeNeResult :
            scratch.one ≠ result :=
          stack_index_ne_output_internal regs 5 resultSlot
        simp only [afterMul, Basic.exec]
        change Function.update store result _ scratch.one = 1
        rw [Function.update_apply, if_neg honeNeResult]
        simpa [scratch] using hone
      let afterDecrement :=
        (Basic.sub scratch.word scratch.word scratch.one).exec
          afterMul
      have hafterDecrementWithin :
          NeighborhoodProgram.ValuesWithin allowed bound
            afterDecrement := by
        apply numericWithin_update_internal allowed bound scratch.word
          (afterMul scratch.word - afterMul scratch.one)
          afterMul hafterMulWithin
        rw [hafterMulWord, hafterMulOne]
        omega
      have hafterDecrementWord :
          afterDecrement scratch.word = remaining := by
        simp [afterDecrement, Basic.exec, hafterMulWord,
          hafterMulOne]
      have hafterDecrementBase :
          afterDecrement scratch.base = 2 := by
        have hbaseNeWord : scratch.base ≠ scratch.word :=
          scratch.index_ne (by decide)
        simp [afterDecrement, Basic.exec, hbaseNeWord,
          hafterMulBase]
      have hafterDecrementOne :
          afterDecrement scratch.one = 1 := by
        have honeNeWord : scratch.one ≠ scratch.word :=
          scratch.index_ne (by decide)
        simp [afterDecrement, Basic.exec, honeNeWord,
          hafterMulOne]
      have hafterDecrementResult :
          afterDecrement result = accumulator * 2 := by
        have hresultNeWord :
            result ≠ scratch.word :=
          (stack_index_ne_output_internal regs 0 resultSlot).symm
        simp [afterDecrement, Basic.exec, hresultNeWord,
          hafterMulResult]
      have hbody :
          InvariantRuns
            (NeighborhoodProgram.ValuesWithin allowed bound)
            (powTwoBody regs result) store afterDecrement 2 := by
        exact InvariantRuns.seq
          (InvariantRuns.basic
            (Basic.mul result result scratch.base) store
            hstore hafterMulWithin)
          (InvariantRuns.basic
            (Basic.sub scratch.word scratch.word scratch.one)
            afterMul hafterMulWithin hafterDecrementWithin)
      have hnextTotal :
          accumulator * 2 * 2 ^ remaining ≤ bound := by
        calc
          accumulator * 2 * 2 ^ remaining =
              accumulator * 2 ^ (remaining + 1) := by
            rw [pow_succ]
            ring
          _ ≤ bound := htotalBound
      obtain ⟨final, loopSteps, hloop, hfinal⟩ :=
        ih afterDecrement (accumulator * 2)
          hafterDecrementWord hafterDecrementBase
          hafterDecrementOne hafterDecrementResult
          (by omega) hnextTotal hafterDecrementWithin
      refine ⟨final, 2 + loopSteps + 2,
        InvariantRuns.whileNonzero hnonzero hbody hloop, ?_⟩
      rw [hfinal, pow_succ]
      ring

private theorem computePowTwo_runs_internal
    (regs : Registers) (exponent : ℕ) (resultSlot : Fin 17)
    (store : Store) (exponentValue : ℕ)
    (hexponent : store exponent = exponentValue)
    (hexponentNeWord : regs.stackRegisters.word ≠ exponent)
    (hexponentNeOne : regs.stackRegisters.one ≠ exponent)
    (hexponentNeBase : regs.stackRegisters.base ≠ exponent) :
    ∃ final,
      Runs
        (computePowTwo regs exponent (outputAddress regs resultSlot))
        store final ∧
      final (outputAddress regs resultSlot) = 2 ^ exponentValue := by
  let scratch := regs.stackRegisters
  let result := outputAddress regs resultSlot
  let afterOne := (Basic.imm scratch.one 1).exec store
  have hafterOneExponent :
      afterOne exponent = exponentValue := by
    have hne : scratch.one ≠ exponent := by
      simpa [scratch] using hexponentNeOne
    simp only [afterOne, Basic.exec]
    change Function.update store scratch.one 1 exponent =
      exponentValue
    rw [Function.update_apply, if_neg hne.symm]
    exact hexponent
  let afterBase := (Basic.imm scratch.base 2).exec afterOne
  have hafterBaseExponent :
      afterBase exponent = exponentValue := by
    have hne : scratch.base ≠ exponent := by
      simpa [scratch] using hexponentNeBase
    simp only [afterBase, Basic.exec]
    change Function.update afterOne scratch.base 2 exponent =
      exponentValue
    rw [Function.update_apply, if_neg hne.symm]
    exact hafterOneExponent
  have hafterBaseOne : afterBase scratch.one = 1 := by
    have honeNeBase :
        scratch.one ≠ scratch.base :=
      scratch.index_ne (by decide)
    simp [afterBase, afterOne, Basic.exec, honeNeBase]
  let afterWord :=
    copyResultStore scratch.word exponent afterBase
  have hcopyWord :
      Runs (copy scratch.word exponent) afterBase afterWord :=
    copy_runs_internal scratch.word exponent afterBase
      hexponentNeWord
  have hafterWordWord :
      afterWord scratch.word = exponentValue := by
    simpa [afterWord, hafterBaseExponent] using
      copy_result_internal scratch.word exponent afterBase
        hexponentNeWord
  have hafterWordBase : afterWord scratch.base = 2 := by
    have hbaseNeWord :
        scratch.base ≠ scratch.word :=
      scratch.index_ne (by decide)
    simp [afterWord, copyResultStore, hbaseNeWord, afterBase,
      Basic.exec]
  have hafterWordOne : afterWord scratch.one = 1 := by
    have honeNeWord :
        scratch.one ≠ scratch.word :=
      scratch.index_ne (by decide)
    simp [afterWord, copyResultStore, honeNeWord, hafterBaseOne]
  let afterResult := (Basic.imm result 1).exec afterWord
  have hresultOutside : result ∉ scratch.footprint := by
    intro hmem
    obtain ⟨slot, _, hslot⟩ := Finset.mem_image.mp hmem
    exact
      (stack_index_ne_output_internal regs slot resultSlot)
        hslot
  have hafterResultWord :
      afterResult scratch.word = exponentValue := by
    have hwordNeResult : scratch.word ≠ result := by
      intro heq
      apply hresultOutside
      rw [← heq]
      exact
        NeighborhoodProgram.StackRegisters.index_mem_footprint
          scratch 0
    simp [afterResult, Basic.exec, hwordNeResult,
      hafterWordWord]
  have hafterResultBase :
      afterResult scratch.base = 2 := by
    have hbaseNeResult : scratch.base ≠ result := by
      intro heq
      apply hresultOutside
      rw [← heq]
      exact
        NeighborhoodProgram.StackRegisters.index_mem_footprint
          scratch 1
    simp [afterResult, Basic.exec, hbaseNeResult,
      hafterWordBase]
  have hafterResultOne :
      afterResult scratch.one = 1 := by
    have honeNeResult : scratch.one ≠ result := by
      intro heq
      apply hresultOutside
      rw [← heq]
      exact
        NeighborhoodProgram.StackRegisters.index_mem_footprint
          scratch 5
    simp [afterResult, Basic.exec, honeNeResult,
      hafterWordOne]
  have hafterResultResult : afterResult result = 1 := by
    simp [afterResult, Basic.exec]
  obtain ⟨final, hloop, hfinal⟩ :=
    pow_two_loop_runs_internal regs resultSlot afterResult
      exponentValue 1 hafterResultWord hafterResultBase
      hafterResultOne hafterResultResult
  refine ⟨final, ?_, ?_⟩
  · simpa [computePowTwo, Cmd.seqList, scratch, result] using
      Runs.seq (Runs.basic (Basic.imm scratch.one 1) store)
        (Runs.seq (Runs.basic (Basic.imm scratch.base 2) afterOne)
          (Runs.seq hcopyWord
            (Runs.seq (Runs.basic (Basic.imm result 1) afterWord)
              hloop)))
  · simpa using hfinal

private theorem computePowTwo_invariantRuns_internal
    (regs : Registers) (allowed : Finset ℕ) (bound exponent : ℕ)
    (resultSlot : Fin 17) (store : Store) (exponentValue : ℕ)
    (hexponent : store exponent = exponentValue)
    (hexponentNeWord : regs.stackRegisters.word ≠ exponent)
    (hexponentNeOne : regs.stackRegisters.one ≠ exponent)
    (hexponentNeBase : regs.stackRegisters.base ≠ exponent)
    (hexponentBound : exponentValue ≤ bound)
    (hpowerBound : 2 ^ exponentValue ≤ bound)
    (htwoBound : 2 ≤ bound)
    (hstore :
      NeighborhoodProgram.ValuesWithin allowed bound store) :
    ∃ final steps,
      InvariantRuns
        (NeighborhoodProgram.ValuesWithin allowed bound)
        (computePowTwo regs exponent
          (outputAddress regs resultSlot))
        store final steps ∧
      final (outputAddress regs resultSlot) = 2 ^ exponentValue := by
  let scratch := regs.stackRegisters
  let result := outputAddress regs resultSlot
  let afterOne := (Basic.imm scratch.one 1).exec store
  have hafterOneWithin :
      NeighborhoodProgram.ValuesWithin allowed bound afterOne :=
    numericWithin_update_internal allowed bound scratch.one 1 store
      hstore (by omega)
  have hafterOneExponent :
      afterOne exponent = exponentValue := by
    simp only [afterOne, Basic.exec]
    rw [Function.update_apply, if_neg hexponentNeOne.symm]
    exact hexponent
  let afterBase := (Basic.imm scratch.base 2).exec afterOne
  have hafterBaseWithin :
      NeighborhoodProgram.ValuesWithin allowed bound afterBase :=
    numericWithin_update_internal allowed bound scratch.base 2
      afterOne hafterOneWithin htwoBound
  have hafterBaseExponent :
      afterBase exponent = exponentValue := by
    simp only [afterBase, Basic.exec]
    rw [Function.update_apply, if_neg hexponentNeBase.symm]
    exact hafterOneExponent
  have hafterBaseOne : afterBase scratch.one = 1 := by
    simp [afterBase, afterOne, Basic.exec,
      scratch.index_ne (first := 5) (second := 1) (by decide)]
  obtain ⟨afterWord, hcopyWord, hafterWordWord,
      hafterWordOutside⟩ :=
    copy_invariantRuns_internal allowed bound scratch.word exponent
      afterBase hexponentNeWord
      (by simpa [hafterBaseExponent] using hexponentBound)
      hafterBaseWithin
  have hafterWordWithin :
      NeighborhoodProgram.ValuesWithin allowed bound afterWord :=
    InvariantRuns.final hcopyWord
  have hafterWordWordValue :
      afterWord scratch.word = exponentValue := by
    rw [hafterWordWord, hafterBaseExponent]
  have hafterWordBase : afterWord scratch.base = 2 := by
    rw [hafterWordOutside scratch.base
      (scratch.index_ne (first := 1) (second := 0) (by decide))]
    simp [afterBase, Basic.exec]
  have hafterWordOne : afterWord scratch.one = 1 := by
    rw [hafterWordOutside scratch.one
      (scratch.index_ne (first := 5) (second := 0) (by decide))]
    exact hafterBaseOne
  let afterResult := (Basic.imm result 1).exec afterWord
  have hafterResultWithin :
      NeighborhoodProgram.ValuesWithin allowed bound afterResult :=
    numericWithin_update_internal allowed bound result 1 afterWord
      hafterWordWithin (by omega)
  have hresultOutside : result ∉ scratch.footprint := by
    intro hmem
    obtain ⟨slot, _, hslot⟩ := Finset.mem_image.mp hmem
    exact
      (stack_index_ne_output_internal regs slot resultSlot) hslot
  have hafterResultWord :
      afterResult scratch.word = exponentValue := by
    have hne : scratch.word ≠ result := by
      intro heq
      apply hresultOutside
      rw [← heq]
      exact
        NeighborhoodProgram.StackRegisters.index_mem_footprint
          scratch 0
    simp [afterResult, Basic.exec, hne, hafterWordWordValue]
  have hafterResultBase : afterResult scratch.base = 2 := by
    have hne : scratch.base ≠ result := by
      intro heq
      apply hresultOutside
      rw [← heq]
      exact
        NeighborhoodProgram.StackRegisters.index_mem_footprint
          scratch 1
    simp [afterResult, Basic.exec, hne, hafterWordBase]
  have hafterResultOne : afterResult scratch.one = 1 := by
    have hne : scratch.one ≠ result := by
      intro heq
      apply hresultOutside
      rw [← heq]
      exact
        NeighborhoodProgram.StackRegisters.index_mem_footprint
          scratch 5
    simp [afterResult, Basic.exec, hne, hafterWordOne]
  have hafterResultResult : afterResult result = 1 := by
    simp [afterResult, Basic.exec]
  obtain ⟨final, loopSteps, hloop, hfinal⟩ :=
    pow_two_loop_invariantRuns_internal regs allowed bound
      resultSlot afterResult exponentValue 1 hafterResultWord
      hafterResultBase hafterResultOne hafterResultResult
      hexponentBound (by simpa using hpowerBound)
      hafterResultWithin
  refine ⟨final, 1 + (1 + (2 + (1 + loopSteps))), ?_, ?_⟩
  · simpa [computePowTwo, Cmd.seqList, scratch, result] using
      InvariantRuns.seq
        (InvariantRuns.basic (Basic.imm scratch.one 1) store
          hstore hafterOneWithin)
        (InvariantRuns.seq
          (InvariantRuns.basic (Basic.imm scratch.base 2)
            afterOne hafterOneWithin hafterBaseWithin)
          (InvariantRuns.seq hcopyWord
            (InvariantRuns.seq
              (InvariantRuns.basic (Basic.imm result 1)
                afterWord hafterWordWithin hafterResultWithin)
              hloop)))
  · simpa using hfinal

private theorem computeMax_runs_internal
    (regs : Registers) (left right : ℕ)
    (resultSlot : Fin 17) (store : Store)
    (leftValue rightValue : ℕ)
    (hleft : store left = leftValue)
    (hright : store right = rightValue)
    (hresultNeLeft :
      outputAddress regs resultSlot ≠ left)
    (hresultNeRight :
      outputAddress regs resultSlot ≠ right)
    (htestNeLeft : regs.stackRegisters.test ≠ left)
    (htestNeRight : regs.stackRegisters.test ≠ right) :
    ∃ final,
      Runs
        (computeMax regs left right (outputAddress regs resultSlot))
        store final ∧
      final (outputAddress regs resultSlot) =
        max leftValue rightValue := by
  let scratch := regs.stackRegisters
  let result := outputAddress regs resultSlot
  let afterTest := (Basic.sub scratch.test left right).exec store
  have hafterTest :
      afterTest scratch.test = leftValue - rightValue := by
    simp [afterTest, Basic.exec, hleft, hright]
  by_cases hle : leftValue ≤ rightValue
  · have htestZero : afterTest scratch.test = 0 := by
      rw [hafterTest]
      omega
    let final := copyResultStore result right afterTest
    have hcopy :
        Runs (copy result right) afterTest final :=
      copy_runs_internal result right afterTest hresultNeRight
    have hfinal : final result = rightValue := by
      have hcopied : final result = afterTest right := by
        simpa [final] using
          copy_result_internal result right afterTest
            hresultNeRight
      rw [hcopied]
      have hne : scratch.test ≠ right := by
        simpa [scratch] using htestNeRight
      simp only [afterTest, Basic.exec]
      change Function.update store scratch.test _ right =
        rightValue
      rw [Function.update_apply, if_neg hne.symm]
      exact hright
    refine ⟨final, ?_, ?_⟩
    · exact Runs.seq
        (Runs.basic (Basic.sub scratch.test left right) store)
        (Runs.ifZero htestZero hcopy)
    · rw [hfinal, max_eq_right hle]
  · have hlt : rightValue < leftValue := by omega
    have htestNonzero :
        afterTest scratch.test ≠ 0 := by
      rw [hafterTest]
      omega
    let final := copyResultStore result left afterTest
    have hcopy :
        Runs (copy result left) afterTest final :=
      copy_runs_internal result left afterTest hresultNeLeft
    have hfinal : final result = leftValue := by
      have hcopied : final result = afterTest left := by
        simpa [final] using
          copy_result_internal result left afterTest
            hresultNeLeft
      rw [hcopied]
      have hne : scratch.test ≠ left := by
        simpa [scratch] using htestNeLeft
      simp only [afterTest, Basic.exec]
      change Function.update store scratch.test _ left =
        leftValue
      rw [Function.update_apply, if_neg hne.symm]
      exact hleft
    refine ⟨final, ?_, ?_⟩
    · exact Runs.seq
        (Runs.basic (Basic.sub scratch.test left right) store)
        (Runs.ifNonzero htestNonzero hcopy)
    · rw [hfinal, max_eq_left hlt.le]

private theorem computeMax_invariantRuns_internal
    (regs : Registers) (allowed : Finset ℕ) (bound left right : ℕ)
    (resultSlot : Fin 17) (store : Store)
    (leftValue rightValue : ℕ)
    (hleft : store left = leftValue)
    (hright : store right = rightValue)
    (hresultNeLeft : outputAddress regs resultSlot ≠ left)
    (hresultNeRight : outputAddress regs resultSlot ≠ right)
    (htestNeLeft : regs.stackRegisters.test ≠ left)
    (htestNeRight : regs.stackRegisters.test ≠ right)
    (hleftBound : leftValue ≤ bound)
    (hrightBound : rightValue ≤ bound)
    (hstore :
      NeighborhoodProgram.ValuesWithin allowed bound store) :
    ∃ final steps,
      InvariantRuns
        (NeighborhoodProgram.ValuesWithin allowed bound)
        (computeMax regs left right
          (outputAddress regs resultSlot))
        store final steps ∧
      final (outputAddress regs resultSlot) =
        max leftValue rightValue := by
  let scratch := regs.stackRegisters
  let result := outputAddress regs resultSlot
  let afterTest := (Basic.sub scratch.test left right).exec store
  have hafterTestWithin :
      NeighborhoodProgram.ValuesWithin allowed bound afterTest := by
    apply numericWithin_update_internal allowed bound scratch.test
      (store left - store right) store hstore
    rw [hleft, hright]
    exact (Nat.sub_le _ _).trans hleftBound
  have hafterTest :
      afterTest scratch.test = leftValue - rightValue := by
    simp [afterTest, Basic.exec, hleft, hright]
  by_cases hle : leftValue ≤ rightValue
  · have htestZero : afterTest scratch.test = 0 := by
      rw [hafterTest]
      omega
    have hafterTestRight : afterTest right = rightValue := by
      simp only [afterTest, Basic.exec]
      rw [Function.update_apply, if_neg htestNeRight.symm]
      exact hright
    obtain ⟨final, hcopy, hfinal, _⟩ :=
      copy_invariantRuns_internal allowed bound result right
        afterTest hresultNeRight
        (by simpa [hafterTestRight] using hrightBound)
        hafterTestWithin
    refine ⟨final, 1 + (2 + 1), ?_, ?_⟩
    · exact InvariantRuns.seq
        (InvariantRuns.basic
          (Basic.sub scratch.test left right) store
          hstore hafterTestWithin)
        (InvariantRuns.ifZero htestZero hcopy)
    · rw [hfinal, hafterTestRight, max_eq_right hle]
  · have hlt : rightValue < leftValue := by omega
    have htestNonzero : afterTest scratch.test ≠ 0 := by
      rw [hafterTest]
      omega
    have hafterTestLeft : afterTest left = leftValue := by
      simp only [afterTest, Basic.exec]
      rw [Function.update_apply, if_neg htestNeLeft.symm]
      exact hleft
    obtain ⟨final, hcopy, hfinal, _⟩ :=
      copy_invariantRuns_internal allowed bound result left
        afterTest hresultNeLeft
        (by simpa [hafterTestLeft] using hleftBound)
        hafterTestWithin
    refine ⟨final, 1 + (2 + 2), ?_, ?_⟩
    · exact InvariantRuns.seq
        (InvariantRuns.basic
          (Basic.sub scratch.test left right) store
          hstore hafterTestWithin)
        (InvariantRuns.ifNonzero htestNonzero hcopy)
    · rw [hfinal, hafterTestLeft, max_eq_left hlt.le]

private theorem computeCanonicalModulus_invariantRuns_internal
    (regs : Registers) (allowed : Finset ℕ) (width : ℕ)
    (store : Store) (degree : ℕ)
    (hdegree : store regs.degreeEndpoint = degree)
    (hprimeFootprint :
      PrimeSearchInvariant.footprint regs.primeRegisters ⊆ allowed)
    (hlowerWidth : Nat.size (degree + 2) + 2 ≤ width)
    (htwoCap : 2 ≤ 2 ^ width - 1)
    (hstore :
      NeighborhoodProgram.ValuesWithin allowed (2 ^ width - 1)
        store) :
    ∃ final steps,
      InvariantRuns
        (NeighborhoodProgram.ValuesWithin allowed (2 ^ width - 1))
        (computeCanonicalModulus regs) store final steps ∧
      final regs.primeRegisters.candidate =
        PrimeField.Search.searchModulus degree ∧
      final regs.modulusPred =
        PrimeField.Search.searchModulus degree - 1 := by
  let scratch := regs.stackRegisters
  let prime := regs.primeRegisters
  let cap := 2 ^ width - 1
  let afterOne := (Basic.imm scratch.one 1).exec store
  have hafterOneWithin :
      NeighborhoodProgram.ValuesWithin allowed cap afterOne :=
    numericWithin_update_internal allowed cap scratch.one 1 store
      hstore (by simpa [cap] using (show 1 ≤ 2 ^ width - 1 by omega))
  let afterValue := (Basic.imm scratch.value 2).exec afterOne
  have hafterValueWithin :
      NeighborhoodProgram.ValuesWithin allowed cap afterValue :=
    numericWithin_update_internal allowed cap scratch.value 2
      afterOne hafterOneWithin (by simpa [cap] using htwoCap)
  have hdegreeAfterOne : afterOne regs.degreeEndpoint = degree := by
    have hne :
        scratch.one ≠ regs.degreeEndpoint :=
      stack_index_ne_output_internal regs 5 (10 : Fin 17)
    simp only [afterOne, Basic.exec]
    rw [Function.update_apply, if_neg hne.symm]
    exact hdegree
  have hdegreeAfterValue :
      afterValue regs.degreeEndpoint = degree := by
    have hne :
        scratch.value ≠ regs.degreeEndpoint :=
      stack_index_ne_output_internal regs 6 (10 : Fin 17)
    simp only [afterValue, Basic.exec]
    rw [Function.update_apply, if_neg hne.symm]
    exact hdegreeAfterOne
  have hvalueAfterValue : afterValue scratch.value = 2 := by
    simp [afterValue, Basic.exec]
  let primed :=
    (Basic.add prime.candidate regs.degreeEndpoint scratch.value).exec
      afterValue
  have hlowerCap : degree + 2 ≤ cap := by
    rw [numericCap_iff_size_internal]
    omega
  have hprimedWithin :
      NeighborhoodProgram.ValuesWithin allowed cap primed := by
    apply numericWithin_update_internal allowed cap prime.candidate
      (afterValue regs.degreeEndpoint + afterValue scratch.value)
      afterValue hafterValueWithin
    rw [hdegreeAfterValue, hvalueAfterValue]
    exact hlowerCap
  have hprimed :
      primed prime.candidate = degree + 2 := by
    simp [primed, Basic.exec, hdegreeAfterValue, hvalueAfterValue]
  have hprimedBit :
      SearchProgram.MutableValuesWithin allowed width primed := by
    simpa [SearchProgram.MutableValuesWithin] using
      (numericWithin_cap_iff_internal allowed width primed).mp
        hprimedWithin
  obtain ⟨searched, searchSteps, hsearch, hsearchPost⟩ :=
    PrimeSearchInvariant.searchInvariantRuns prime allowed width
      (degree + 2) hprimeFootprint
      (by simpa [bitlen] using hlowerWidth)
      primed hprimed hprimedBit
  have hsearchNumeric :
      InvariantRuns
        (NeighborhoodProgram.ValuesWithin allowed cap)
        (PrimeSearch.search prime) primed searched searchSteps := by
    apply invariantRuns_mono_internal
      (firstInvariant :=
        SearchProgram.MutableValuesWithin allowed width)
      (secondInvariant :=
        NeighborhoodProgram.ValuesWithin allowed cap)
      (fun current hcurrent => by
        simpa [cap, SearchProgram.MutableValuesWithin] using
          (numericWithin_cap_iff_internal allowed width current).mpr
            (by
              simpa [SearchProgram.MutableValuesWithin] using
                hcurrent))
      hsearch
  have hsearchedWithin :
      NeighborhoodProgram.ValuesWithin allowed cap searched :=
    InvariantRuns.final hsearchNumeric
  have hmodulus :
      searched prime.candidate =
        PrimeField.Search.searchModulus degree := by
    exact
      Runtime.CanonicalPrime.PrimeSearch.SearchPost.candidate_eq_searchModulus
        prime searched degree hsearchPost
  let refreshedOne := (Basic.imm scratch.one 1).exec searched
  have hrefreshedOneWithin :
      NeighborhoodProgram.ValuesWithin allowed cap refreshedOne :=
    numericWithin_update_internal allowed cap scratch.one 1
      searched hsearchedWithin
      (by simpa [cap] using (show 1 ≤ 2 ^ width - 1 by omega))
  have hrefreshedOne : refreshedOne scratch.one = 1 := by
    simp [refreshedOne, Basic.exec]
  have hrefreshedModulus :
      refreshedOne prime.candidate =
        PrimeField.Search.searchModulus degree := by
    have hne : scratch.one ≠ prime.candidate :=
      stack_index_ne_prime_internal regs 5 0
    simp only [refreshedOne, Basic.exec]
    rw [Function.update_apply, if_neg hne.symm]
    exact hmodulus
  let final :=
    (Basic.sub regs.modulusPred prime.candidate scratch.one).exec
      refreshedOne
  have hfinalWithin :
      NeighborhoodProgram.ValuesWithin allowed cap final := by
    apply numericWithin_update_internal allowed cap regs.modulusPred
      (refreshedOne prime.candidate - refreshedOne scratch.one)
      refreshedOne hrefreshedOneWithin
    exact (Nat.sub_le _ _).trans
      (by
        exact hrefreshedOneWithin prime.candidate
          (hprimeFootprint
            (PrimeSearchInvariant.index_mem_footprint prime 0)))
  have hfinalPred :
      final regs.modulusPred =
        PrimeField.Search.searchModulus degree - 1 := by
    simp [final, Basic.exec, hrefreshedModulus, hrefreshedOne]
  have hfinalModulus :
      final prime.candidate =
        PrimeField.Search.searchModulus degree := by
    have hne : regs.modulusPred ≠ prime.candidate :=
      (prime_index_ne_output_internal regs 0 (16 : Fin 17)).symm
    simp only [final, Basic.exec]
    rw [Function.update_apply, if_neg hne.symm]
    exact hrefreshedModulus
  refine ⟨final,
    1 + (1 + (1 + (searchSteps + (1 + 1)))), ?_,
    hfinalModulus, hfinalPred⟩
  simpa [computeCanonicalModulus, Cmd.seqList, scratch, prime,
    afterOne, afterValue, primed, refreshedOne, final] using
    InvariantRuns.seq
      (InvariantRuns.basic (Basic.imm scratch.one 1) store
        hstore hafterOneWithin)
      (InvariantRuns.seq
        (InvariantRuns.basic (Basic.imm scratch.value 2)
          afterOne hafterOneWithin hafterValueWithin)
        (InvariantRuns.seq
          (InvariantRuns.basic
            (Basic.add prime.candidate regs.degreeEndpoint
              scratch.value) afterValue hafterValueWithin
              hprimedWithin)
          (InvariantRuns.seq hsearchNumeric
            (InvariantRuns.seq
              (InvariantRuns.basic (Basic.imm scratch.one 1)
                searched hsearchedWithin hrefreshedOneWithin)
              (InvariantRuns.basic
                (Basic.sub regs.modulusPred prime.candidate
                  scratch.one) refreshedOne hrefreshedOneWithin
                  hfinalWithin)))))

theorem program_sourceWritesWithin_internal
    (Q : Type*) [Fintype Q] (workTapeCount : ℕ)
    (regs : Registers) :
    RAM.Structured.Footprint.CmdWritesWithin regs.footprint
      (program Q workTapeCount regs) := by
  have hstack (slot : Fin 7) :
      regs.stackRegisters.index slot ∈ regs.footprint :=
    stack_footprint_subset_internal regs
      (NeighborhoodProgram.StackRegisters.index_mem_footprint
        regs.stackRegisters slot)
  have hprime (slot : Fin 8) :
      regs.primeRegisters.index slot ∈ regs.footprint :=
    prime_footprint_subset_internal regs
      (PrimeSearchInvariant.index_mem_footprint
        regs.primeRegisters slot)
  simp [program, computeProtectedLog, protectedLogBody,
    protectedLogTest, computePositiveCeilSqrt, sqrtBody, sqrtTest,
    computeCeilDiv, computePowTwo, powTwoBody, computeMax, copy,
    computeRadicand, computeBooleanWidth, computeFanIn,
    computeChunkBits, computeGroupedDegree, computeFieldBits,
    computeFrameBits, computeBankDigitCount,
    computeCanonicalModulus,
    NeighborhoodProgram.pop, NeighborhoodProgram.popBody,
    NeighborhoodProgram.popTestOp, PrimeSearch.search,
    PrimeSearch.searchBody, PrimeSearch.primality,
    PrimeSearch.primalitySetupOps, PrimeSearch.trialSetupOps,
    PrimeSearch.trialLoop, PrimeSearch.trialBody,
    PrimeSearch.refreshSearchTest, PrimeSearch.decrementDivisor,
    RuntimeArithmetic.reduce, RuntimeArithmetic.reduceBody,
    RuntimeArithmetic.reduceTestOp,
    PrimeSearch.Registers.reduceRegisters, Cmd.seqList, Cmd.basics,
    RAM.Structured.Footprint.CmdWritesWithin,
    RAM.Structured.Footprint.BasicWritesWithin,
    hstack, hprime]

theorem program_runs_internal
    (Q : Type*) [Fintype Q] (workTapeCount : ℕ)
    (regs : Registers) (store : Store) (candidate : ℕ)
    (hcandidate : store regs.candidate = candidate) :
    ∃ final,
      Runs (program Q workTapeCount regs) store final ∧
      Post Q workTapeCount candidate regs store final := by
  have hwordCandidate :
      regs.stackRegisters.word ≠ regs.candidate := by
    exact (regs.candidate_ne ⟨17, by omega⟩).symm
  have honeCandidate :
      regs.stackRegisters.one ≠ regs.candidate := by
    exact (regs.candidate_ne ⟨22, by omega⟩).symm

  have hw0 :
      RAM.Structured.Footprint.CmdWritesWithin
        (tailFootprint regs 0)
        (computeProtectedLog regs regs.candidate regs.protectedLog) := by
    simpa using
      computeProtectedLog_tailWrites_internal regs 0 regs.candidate
        (0 : Fin 17) (by omega)
  obtain ⟨store1, hrun0, hout0⟩ :=
    computeProtectedLog_runs_internal regs regs.candidate
      (0 : Fin 17) store candidate hcandidate hwordCandidate
  have houtputs0 :
      OutputsThrough Q workTapeCount candidate 0 regs store :=
    outputsThrough_zero_internal Q workTapeCount candidate regs store
  have houtputs1 :
      OutputsThrough Q workTapeCount candidate 1 regs store1 :=
    outputsThrough_extend_internal Q workTapeCount candidate regs
      (0 : Fin 17) houtputs0 hrun0 hw0 (by
        simpa [expectedValues, protectedLog] using hout0)
  have hcandidate1 : store1 regs.candidate = candidate := by
    rw [candidate_preserved_internal regs 0 hw0 hrun0]
    exact hcandidate

  let store2 :=
    (Basic.mul regs.radicand regs.candidate regs.protectedLog).exec
      store1
  have hrun1 : Runs (computeRadicand regs) store1 store2 := by
    simpa [computeRadicand, store2] using
      Runs.basic
        (Basic.mul regs.radicand regs.candidate regs.protectedLog)
        store1
  have hout1 :
      store2 regs.radicand = radicand candidate := by
    have hlog := houtputs1 (0 : Fin 17) (by omega)
    simp only [expectedValues, Matrix.cons_val_zero] at hlog
    change store1 regs.protectedLog = protectedLog candidate at hlog
    simp [store2, Basic.exec, radicand, hcandidate1, hlog]
  have hw1 :
      RAM.Structured.Footprint.CmdWritesWithin
        (tailFootprint regs 1) (computeRadicand regs) := by
    simpa [computeRadicand,
      RAM.Structured.Footprint.CmdWritesWithin,
      RAM.Structured.Footprint.BasicWritesWithin] using
      output_mem_tailFootprint_internal regs 1 (1 : Fin 17)
        (by omega)
  have houtputs2 :
      OutputsThrough Q workTapeCount candidate 2 regs store2 :=
    outputsThrough_extend_internal Q workTapeCount candidate regs
      (1 : Fin 17) houtputs1 hrun1 hw1 (by
        simpa [expectedValues] using hout1)
  have hcandidate2 : store2 regs.candidate = candidate := by
    rw [candidate_preserved_internal regs 1 hw1 hrun1]
    exact hcandidate1

  have hw2 :
      RAM.Structured.Footprint.CmdWritesWithin
        (tailFootprint regs 2)
        (computePositiveCeilSqrt regs regs.radicand
          regs.blockLength) := by
    simpa using
      computePositiveCeilSqrt_tailWrites_internal regs 2
        regs.radicand (2 : Fin 17) (by omega)
  obtain ⟨store3, hrun2, hout2⟩ :=
    computePositiveCeilSqrt_runs_internal regs
      (1 : Fin 17) (2 : Fin 17) store2 (radicand candidate)
      (by decide) hout1
  have houtputs3 :
      OutputsThrough Q workTapeCount candidate 3 regs store3 :=
    outputsThrough_extend_internal Q workTapeCount candidate regs
      (2 : Fin 17) houtputs2 hrun2 hw2 (by
        simpa [expectedValues, blockLength, radicand] using hout2)
  have hcandidate3 : store3 regs.candidate = candidate := by
    rw [candidate_preserved_internal regs 2 hw2 hrun2]
    exact hcandidate2

  have hblock :
      store3 regs.blockLength = blockLength candidate := by
    simpa using houtputs3 (2 : Fin 17) (by omega)
  have hw3 :
      RAM.Structured.Footprint.CmdWritesWithin
        (tailFootprint regs 3)
        (computeCeilDiv regs regs.candidate regs.blockLength
          regs.horizon) := by
    simpa using
      computeCeilDiv_tailWrites_internal regs 3 regs.candidate
        regs.blockLength (3 : Fin 17) (by omega)
  obtain ⟨store4, hrun3, hout3⟩ :=
    computeCeilDiv_runs_internal regs regs.candidate
      regs.blockLength (3 : Fin 17) store3 candidate
      (blockLength candidate) hcandidate3 hblock
      (WorkspaceAccounting.blockLength_pos candidate)
      hwordCandidate
      (stack_index_ne_output_internal regs 0 (2 : Fin 17))
      (stack_index_ne_output_internal regs 1 (2 : Fin 17))
      honeCandidate
      (stack_index_ne_output_internal regs 5 (2 : Fin 17))
  have houtputs4 :
      OutputsThrough Q workTapeCount candidate 4 regs store4 :=
    outputsThrough_extend_internal Q workTapeCount candidate regs
      (3 : Fin 17) houtputs3 hrun3 hw3 (by
        simpa [expectedValues, horizon,
          WorkspaceAccounting.horizon] using hout3)
  have hcandidate4 : store4 regs.candidate = candidate := by
    rw [candidate_preserved_internal regs 3 hw3 hrun3]
    exact hcandidate3

  let store5a :=
    (Basic.imm regs.stackRegisters.value 5).exec store4
  let store5b :=
    (Basic.mul regs.booleanWidth regs.stackRegisters.value
      regs.blockLength).exec store5a
  let store5c :=
    (Basic.imm regs.stackRegisters.value (Fintype.card Q)).exec
      store5b
  let store5 :=
    (Basic.add regs.booleanWidth regs.stackRegisters.value
      regs.booleanWidth).exec store5c
  have hrun4 :
      Runs (computeBooleanWidth Q regs) store4 store5 := by
    simpa [computeBooleanWidth, Cmd.seqList, store5a, store5b,
      store5c, store5] using
      Runs.seq
        (Runs.basic (Basic.imm regs.stackRegisters.value 5) store4)
        (Runs.seq
          (Runs.basic
            (Basic.mul regs.booleanWidth regs.stackRegisters.value
              regs.blockLength) store5a)
          (Runs.seq
            (Runs.basic
              (Basic.imm regs.stackRegisters.value (Fintype.card Q))
              store5b)
            (Runs.basic
              (Basic.add regs.booleanWidth
                regs.stackRegisters.value regs.booleanWidth)
              store5c)))
  have hout4 :
      store5 regs.booleanWidth = booleanWidth Q candidate := by
    have hblock4 := houtputs4 (2 : Fin 17) (by omega)
    simp only [expectedValues, Matrix.cons_val_two] at hblock4
    change store4 regs.blockLength = blockLength candidate at hblock4
    have hvalueNeBoolean :
        regs.stackRegisters.value ≠ regs.booleanWidth :=
      stack_index_ne_output_internal regs 6 (4 : Fin 17)
    have hvalueNeBlock :
        regs.stackRegisters.value ≠ regs.blockLength :=
      stack_index_ne_output_internal regs 6 (2 : Fin 17)
    have hblock5a :
        store5a regs.blockLength = blockLength candidate := by
      simp only [store5a, Basic.exec]
      rw [Function.update_apply, if_neg hvalueNeBlock.symm]
      exact hblock4
    have hvalue5a :
        store5a regs.stackRegisters.value = 5 := by
      simp [store5a, Basic.exec]
    have hboolean5b :
        store5b regs.booleanWidth =
          5 * blockLength candidate := by
      simp [store5b, Basic.exec, hvalue5a, hblock5a]
    have hboolean5c :
        store5c regs.booleanWidth =
          5 * blockLength candidate := by
      simp only [store5c, Basic.exec]
      rw [Function.update_apply, if_neg hvalueNeBoolean.symm]
      exact hboolean5b
    have hvalue5c :
        store5c regs.stackRegisters.value = Fintype.card Q := by
      simp [store5c, Basic.exec]
    simp [store5, Basic.exec, booleanWidth,
      WorkspaceAccounting.booleanWidth, hboolean5c, hvalue5c]
  have hw4 :
      RAM.Structured.Footprint.CmdWritesWithin
        (tailFootprint regs 4) (computeBooleanWidth Q regs) := by
    have hstack (slot : Fin 7) :
        regs.stackRegisters.index slot ∈ tailFootprint regs 4 :=
      stack_mem_tailFootprint_internal regs 4 slot
    have hout :
        regs.booleanWidth ∈ tailFootprint regs 4 :=
      output_mem_tailFootprint_internal regs 4 (4 : Fin 17)
        (by omega)
    simp [computeBooleanWidth, Cmd.seqList,
      RAM.Structured.Footprint.CmdWritesWithin,
      RAM.Structured.Footprint.BasicWritesWithin, hstack, hout]
  have houtputs5 :
      OutputsThrough Q workTapeCount candidate 5 regs store5 :=
    outputsThrough_extend_internal Q workTapeCount candidate regs
      (4 : Fin 17) houtputs4 hrun4 hw4 (by
        simpa [expectedValues] using hout4)
  have hcandidate5 : store5 regs.candidate = candidate := by
    rw [candidate_preserved_internal regs 4 hw4 hrun4]
    exact hcandidate4

  let store6 :=
    (Basic.imm regs.fanIn (4 * (workTapeCount + 2))).exec store5
  have hrun5 :
      Runs (computeFanIn workTapeCount regs) store5 store6 := by
    simpa [computeFanIn, store6] using
      Runs.basic
        (Basic.imm regs.fanIn (4 * (workTapeCount + 2))) store5
  have hout5 :
      store6 regs.fanIn = fanIn workTapeCount := by
    simp [store6, Basic.exec, fanIn, WorkspaceAccounting.fanIn]
  have hw5 :
      RAM.Structured.Footprint.CmdWritesWithin
        (tailFootprint regs 5)
        (computeFanIn workTapeCount regs) := by
    simpa [computeFanIn,
      RAM.Structured.Footprint.CmdWritesWithin,
      RAM.Structured.Footprint.BasicWritesWithin] using
      output_mem_tailFootprint_internal regs 5 (5 : Fin 17)
        (by omega)
  have houtputs6 :
      OutputsThrough Q workTapeCount candidate 6 regs store6 :=
    outputsThrough_extend_internal Q workTapeCount candidate regs
      (5 : Fin 17) houtputs5 hrun5 hw5 (by
        simpa [expectedValues] using hout5)
  have hcandidate6 : store6 regs.candidate = candidate := by
    rw [candidate_preserved_internal regs 5 hw5 hrun5]
    exact hcandidate5

  have hfan6 :
      store6 regs.fanIn = fanIn workTapeCount := by
    simpa using houtputs6 (5 : Fin 17) (by omega)
  have hboolean6 :
      store6 regs.booleanWidth = booleanWidth Q candidate := by
    simpa using houtputs6 (4 : Fin 17) (by omega)
  let store7a :=
    (Basic.mul regs.stackRegisters.value regs.fanIn
      regs.booleanWidth).exec store6
  have hvalue7a :
      store7a regs.stackRegisters.value =
        fanIn workTapeCount * booleanWidth Q candidate := by
    simp [store7a, Basic.exec, hfan6, hboolean6]
  have hrun6a :
      Runs
        (.basic (Basic.mul regs.stackRegisters.value regs.fanIn
          regs.booleanWidth)) store6 store7a :=
    Runs.basic _ _
  obtain ⟨store7, hrun6b, hout6⟩ :=
    computeProtectedLog_runs_internal regs
      regs.stackRegisters.value (6 : Fin 17) store7a
      (fanIn workTapeCount * booleanWidth Q candidate)
      hvalue7a (regs.stackRegisters.index_ne (by decide))
  have hrun6 :
      Runs (computeChunkBits regs) store6 store7 := by
    simpa [computeChunkBits] using Runs.seq hrun6a hrun6b
  have hw6 :
      RAM.Structured.Footprint.CmdWritesWithin
        (tailFootprint regs 6) (computeChunkBits regs) := by
    have hvalue :
        regs.stackRegisters.value ∈ tailFootprint regs 6 :=
      stack_mem_tailFootprint_internal regs 6 (6 : Fin 7)
    have hlog :=
      computeProtectedLog_tailWrites_internal regs 6
        regs.stackRegisters.value (6 : Fin 17) (by omega)
    simpa [computeChunkBits,
      RAM.Structured.Footprint.CmdWritesWithin,
      RAM.Structured.Footprint.BasicWritesWithin] using
      And.intro hvalue hlog
  have houtputs7 :
      OutputsThrough Q workTapeCount candidate 7 regs store7 :=
    outputsThrough_extend_internal Q workTapeCount candidate regs
      (6 : Fin 17) houtputs6 hrun6 hw6 (by
        simpa [expectedValues, chunkBits,
          WorkspaceAccounting.chunkBits,
          GroupedExtension.LogarithmicParameters.chunkBits,
          fanIn, booleanWidth] using hout6)
  have hcandidate7 : store7 regs.candidate = candidate := by
    rw [candidate_preserved_internal regs 6 hw6 hrun6]
    exact hcandidate6

  have hboolean7 :
      store7 regs.booleanWidth = booleanWidth Q candidate := by
    simpa using houtputs7 (4 : Fin 17) (by omega)
  have hchunkBits7 :
      store7 regs.chunkBits =
        chunkBits Q workTapeCount candidate := by
    simpa using houtputs7 (6 : Fin 17) (by omega)
  have hw7 :
      RAM.Structured.Footprint.CmdWritesWithin
        (tailFootprint regs 7)
        (computeCeilDiv regs regs.booleanWidth regs.chunkBits
          regs.chunkCount) := by
    simpa using
      computeCeilDiv_tailWrites_internal regs 7
        regs.booleanWidth regs.chunkBits (7 : Fin 17) (by omega)
  obtain ⟨store8, hrun7, hout7⟩ :=
    computeCeilDiv_runs_internal regs regs.booleanWidth
      regs.chunkBits (7 : Fin 17) store7
      (booleanWidth Q candidate)
      (chunkBits Q workTapeCount candidate)
      hboolean7 hchunkBits7
      (by
        exact
          GroupedExtension.LogarithmicParameters.chunkBits_pos
            (booleanWidth Q candidate) (fanIn workTapeCount))
      (stack_index_ne_output_internal regs 0 (4 : Fin 17))
      (stack_index_ne_output_internal regs 0 (6 : Fin 17))
      (stack_index_ne_output_internal regs 1 (6 : Fin 17))
      (stack_index_ne_output_internal regs 5 (4 : Fin 17))
      (stack_index_ne_output_internal regs 5 (6 : Fin 17))
  have houtputs8 :
      OutputsThrough Q workTapeCount candidate 8 regs store8 :=
    outputsThrough_extend_internal Q workTapeCount candidate regs
      (7 : Fin 17) houtputs7 hrun7 hw7 (by
        simpa [expectedValues, chunkCount,
          WorkspaceAccounting.chunkCount,
          GroupedExtension.LogarithmicParameters.chunkCount]
          using hout7)
  have hcandidate8 : store8 regs.candidate = candidate := by
    rw [candidate_preserved_internal regs 7 hw7 hrun7]
    exact hcandidate7

  have hchunkBits8 :
      store8 regs.chunkBits =
        chunkBits Q workTapeCount candidate := by
    simpa using houtputs8 (6 : Fin 17) (by omega)
  have hw8 :
      RAM.Structured.Footprint.CmdWritesWithin
        (tailFootprint regs 8)
        (computePowTwo regs regs.chunkBits regs.domainSize) := by
    simpa using
      computePowTwo_tailWrites_internal regs 8 regs.chunkBits
        (8 : Fin 17) (by omega)
  obtain ⟨store9, hrun8, hout8⟩ :=
    computePowTwo_runs_internal regs regs.chunkBits
      (8 : Fin 17) store8 (chunkBits Q workTapeCount candidate)
      hchunkBits8
      (stack_index_ne_output_internal regs 0 (6 : Fin 17))
      (stack_index_ne_output_internal regs 5 (6 : Fin 17))
      (stack_index_ne_output_internal regs 1 (6 : Fin 17))
  have houtputs9 :
      OutputsThrough Q workTapeCount candidate 9 regs store9 :=
    outputsThrough_extend_internal Q workTapeCount candidate regs
      (8 : Fin 17) houtputs8 hrun8 hw8 (by
        simpa [expectedValues, domainSize,
          PrimeGrouped.Logarithmic.domainSize] using hout8)
  have hcandidate9 : store9 regs.candidate = candidate := by
    rw [candidate_preserved_internal regs 8 hw8 hrun8]
    exact hcandidate8

  have hdomain9 :
      store9 regs.domainSize =
        domainSize Q workTapeCount candidate := by
    simpa using houtputs9 (8 : Fin 17) (by omega)
  have hfan9 :
      store9 regs.fanIn = fanIn workTapeCount := by
    simpa using houtputs9 (5 : Fin 17) (by omega)
  have hchunkCount9 :
      store9 regs.chunkCount =
        chunkCount Q workTapeCount candidate := by
    simpa using houtputs9 (7 : Fin 17) (by omega)
  let store10a :=
    (Basic.imm regs.stackRegisters.one 1).exec store9
  let store10b :=
    (Basic.sub regs.stackRegisters.value regs.domainSize
      regs.stackRegisters.one).exec store10a
  let store10c :=
    (Basic.mul regs.groupedDegree regs.fanIn regs.chunkCount).exec
      store10b
  let store10 :=
    (Basic.mul regs.groupedDegree regs.groupedDegree
      regs.stackRegisters.value).exec store10c
  have hrun9 :
      Runs (computeGroupedDegree regs) store9 store10 := by
    simpa [computeGroupedDegree, Cmd.seqList, store10a, store10b,
      store10c, store10] using
      Runs.seq
        (Runs.basic (Basic.imm regs.stackRegisters.one 1) store9)
        (Runs.seq
          (Runs.basic
            (Basic.sub regs.stackRegisters.value regs.domainSize
              regs.stackRegisters.one) store10a)
          (Runs.seq
            (Runs.basic
              (Basic.mul regs.groupedDegree regs.fanIn
                regs.chunkCount) store10b)
            (Runs.basic
              (Basic.mul regs.groupedDegree regs.groupedDegree
                regs.stackRegisters.value) store10c)))
  have hone10a :
      store10a regs.stackRegisters.one = 1 := by
    simp [store10a, Basic.exec]
  have hdomain10a :
      store10a regs.domainSize =
        domainSize Q workTapeCount candidate := by
    have hne :
        regs.stackRegisters.one ≠ regs.domainSize :=
      stack_index_ne_output_internal regs 5 (8 : Fin 17)
    simp only [store10a, Basic.exec]
    rw [Function.update_apply, if_neg hne.symm]
    exact hdomain9
  have hvalue10b :
      store10b regs.stackRegisters.value =
        domainSize Q workTapeCount candidate - 1 := by
    simp [store10b, Basic.exec, hdomain10a, hone10a]
  have hfan10b :
      store10b regs.fanIn = fanIn workTapeCount := by
    have honeNe :
        regs.stackRegisters.one ≠ regs.fanIn :=
      stack_index_ne_output_internal regs 5 (5 : Fin 17)
    have hvalueNe :
        regs.stackRegisters.value ≠ regs.fanIn :=
      stack_index_ne_output_internal regs 6 (5 : Fin 17)
    simp [store10b, store10a, Basic.exec, honeNe.symm,
      hvalueNe.symm, hfan9]
  have hcount10b :
      store10b regs.chunkCount =
        chunkCount Q workTapeCount candidate := by
    have honeNe :
        regs.stackRegisters.one ≠ regs.chunkCount :=
      stack_index_ne_output_internal regs 5 (7 : Fin 17)
    have hvalueNe :
        regs.stackRegisters.value ≠ regs.chunkCount :=
      stack_index_ne_output_internal regs 6 (7 : Fin 17)
    simp [store10b, store10a, Basic.exec, honeNe.symm,
      hvalueNe.symm, hchunkCount9]
  have hgrouped10c :
      store10c regs.groupedDegree =
        fanIn workTapeCount *
          chunkCount Q workTapeCount candidate := by
    simp [store10c, Basic.exec, hfan10b, hcount10b]
  have hvalue10c :
      store10c regs.stackRegisters.value =
        domainSize Q workTapeCount candidate - 1 := by
    have hne :
        regs.groupedDegree ≠ regs.stackRegisters.value :=
      (stack_index_ne_output_internal regs 6 (9 : Fin 17)).symm
    simp only [store10c, Basic.exec]
    rw [Function.update_apply, if_neg hne.symm]
    exact hvalue10b
  have hout9 :
      store10 regs.groupedDegree =
        groupedDegree Q workTapeCount candidate := by
    simp only [store10, Basic.exec, Function.update_self]
    rw [hgrouped10c, hvalue10c]
    rfl
  have hvalue10 :
      store10 regs.stackRegisters.value =
        domainSize Q workTapeCount candidate - 1 := by
    have hne :
        regs.groupedDegree ≠ regs.stackRegisters.value :=
      (stack_index_ne_output_internal regs 6 (9 : Fin 17)).symm
    simp only [store10, Basic.exec]
    rw [Function.update_apply, if_neg hne.symm]
    exact hvalue10c
  have hw9 :
      RAM.Structured.Footprint.CmdWritesWithin
        (tailFootprint regs 9) (computeGroupedDegree regs) := by
    have hstack (slot : Fin 7) :
        regs.stackRegisters.index slot ∈ tailFootprint regs 9 :=
      stack_mem_tailFootprint_internal regs 9 slot
    have hout :
        regs.groupedDegree ∈ tailFootprint regs 9 :=
      output_mem_tailFootprint_internal regs 9 (9 : Fin 17)
        (by omega)
    simp [computeGroupedDegree, Cmd.seqList,
      RAM.Structured.Footprint.CmdWritesWithin,
      RAM.Structured.Footprint.BasicWritesWithin, hstack, hout]
  have houtputs10 :
      OutputsThrough Q workTapeCount candidate 10 regs store10 :=
    outputsThrough_extend_internal Q workTapeCount candidate regs
      (9 : Fin 17) houtputs9 hrun9 hw9 (by
        simpa [expectedValues] using hout9)
  have hcandidate10 : store10 regs.candidate = candidate := by
    rw [candidate_preserved_internal regs 9 hw9 hrun9]
    exact hcandidate9

  have hgrouped10 :
      store10 regs.groupedDegree =
        groupedDegree Q workTapeCount candidate := by
    simpa using houtputs10 (9 : Fin 17) (by omega)
  have hw10 :
      RAM.Structured.Footprint.CmdWritesWithin
        (tailFootprint regs 10)
        (computeMax regs regs.groupedDegree
          regs.stackRegisters.value regs.degreeEndpoint) := by
    simpa using
      computeMax_tailWrites_internal regs 10 regs.groupedDegree
        regs.stackRegisters.value (10 : Fin 17) (by omega)
  obtain ⟨store11, hrun10, hout10⟩ :=
    computeMax_runs_internal regs regs.groupedDegree
      regs.stackRegisters.value (10 : Fin 17) store10
      (groupedDegree Q workTapeCount candidate)
      (domainSize Q workTapeCount candidate - 1)
      hgrouped10 hvalue10
      (outputAddress_ne regs
        (first := (10 : Fin 17)) (second := (9 : Fin 17))
        (by decide))
      (stack_index_ne_output_internal regs 6 (10 : Fin 17)).symm
      (stack_index_ne_output_internal regs 4 (9 : Fin 17))
      (regs.stackRegisters.index_ne (by decide))
  have houtputs11 :
      OutputsThrough Q workTapeCount candidate 11 regs store11 :=
    outputsThrough_extend_internal Q workTapeCount candidate regs
      (10 : Fin 17) houtputs10 hrun10 hw10 (by
        simpa [expectedValues, degreeEndpoint,
          PrimeGrouped.Logarithmic.degreeEndpoint] using hout10)
  have hcandidate11 : store11 regs.candidate = candidate := by
    rw [candidate_preserved_internal regs 10 hw10 hrun10]
    exact hcandidate10

  have hchunkBits11 :
      store11 regs.chunkBits =
        chunkBits Q workTapeCount candidate := by
    simpa using houtputs11 (6 : Fin 17) (by omega)
  let store12a :=
    (Basic.imm regs.stackRegisters.value 2).exec store11
  let store12 :=
    (Basic.mul regs.fieldBits regs.stackRegisters.value
      regs.chunkBits).exec store12a
  have hrun11 :
      Runs (computeFieldBits regs) store11 store12 := by
    simpa [computeFieldBits, store12a, store12] using
      Runs.seq
        (Runs.basic (Basic.imm regs.stackRegisters.value 2) store11)
        (Runs.basic
          (Basic.mul regs.fieldBits regs.stackRegisters.value
            regs.chunkBits) store12a)
  have hchunkBits12a :
      store12a regs.chunkBits =
        chunkBits Q workTapeCount candidate := by
    have hne :
        regs.stackRegisters.value ≠ regs.chunkBits :=
      stack_index_ne_output_internal regs 6 (6 : Fin 17)
    simp only [store12a, Basic.exec]
    rw [Function.update_apply, if_neg hne.symm]
    exact hchunkBits11
  have hvalue12a :
      store12a regs.stackRegisters.value = 2 := by
    simp [store12a, Basic.exec]
  have hout11 :
      store12 regs.fieldBits =
        fieldBits Q workTapeCount candidate := by
    simp only [store12, Basic.exec, Function.update_self]
    rw [hvalue12a, hchunkBits12a]
    rfl
  have hw11 :
      RAM.Structured.Footprint.CmdWritesWithin
        (tailFootprint regs 11) (computeFieldBits regs) := by
    have hstack :
        regs.stackRegisters.value ∈ tailFootprint regs 11 :=
      stack_mem_tailFootprint_internal regs 11 (6 : Fin 7)
    have hout :
        regs.fieldBits ∈ tailFootprint regs 11 :=
      output_mem_tailFootprint_internal regs 11 (11 : Fin 17)
        (by omega)
    simp [computeFieldBits,
      RAM.Structured.Footprint.CmdWritesWithin,
      RAM.Structured.Footprint.BasicWritesWithin, hstack, hout]
  have houtputs12 :
      OutputsThrough Q workTapeCount candidate 12 regs store12 :=
    outputsThrough_extend_internal Q workTapeCount candidate regs
      (11 : Fin 17) houtputs11 hrun11 hw11 (by
        simpa [expectedValues] using hout11)
  have hcandidate12 : store12 regs.candidate = candidate := by
    rw [candidate_preserved_internal regs 11 hw11 hrun11]
    exact hcandidate11

  have hchunkBits12 :
      store12 regs.chunkBits =
        chunkBits Q workTapeCount candidate := by
    simpa using houtputs12 (6 : Fin 17) (by omega)
  let store13a :=
    (Basic.imm regs.stackRegisters.value 24).exec store12
  let store13 :=
    (Basic.mul regs.frameBits regs.stackRegisters.value
      regs.chunkBits).exec store13a
  have hrun12 :
      Runs (computeFrameBits regs) store12 store13 := by
    simpa [computeFrameBits, store13a, store13] using
      Runs.seq
        (Runs.basic (Basic.imm regs.stackRegisters.value 24) store12)
        (Runs.basic
          (Basic.mul regs.frameBits regs.stackRegisters.value
            regs.chunkBits) store13a)
  have hchunkBits13a :
      store13a regs.chunkBits =
        chunkBits Q workTapeCount candidate := by
    have hne :
        regs.stackRegisters.value ≠ regs.chunkBits :=
      stack_index_ne_output_internal regs 6 (6 : Fin 17)
    simp only [store13a, Basic.exec]
    rw [Function.update_apply, if_neg hne.symm]
    exact hchunkBits12
  have hvalue13a :
      store13a regs.stackRegisters.value = 24 := by
    simp [store13a, Basic.exec]
  have hout12 :
      store13 regs.frameBits =
        frameBits Q workTapeCount candidate := by
    simp only [store13, Basic.exec, Function.update_self]
    rw [hvalue13a, hchunkBits13a]
    simpa [frameBits, chunkBits] using
      (WorkspaceAccounting.frameBits_eq
        Q workTapeCount candidate).symm
  have hw12 :
      RAM.Structured.Footprint.CmdWritesWithin
        (tailFootprint regs 12) (computeFrameBits regs) := by
    have hstack :
        regs.stackRegisters.value ∈ tailFootprint regs 12 :=
      stack_mem_tailFootprint_internal regs 12 (6 : Fin 7)
    have hout :
        regs.frameBits ∈ tailFootprint regs 12 :=
      output_mem_tailFootprint_internal regs 12 (12 : Fin 17)
        (by omega)
    simp [computeFrameBits,
      RAM.Structured.Footprint.CmdWritesWithin,
      RAM.Structured.Footprint.BasicWritesWithin, hstack, hout]
  have houtputs13 :
      OutputsThrough Q workTapeCount candidate 13 regs store13 :=
    outputsThrough_extend_internal Q workTapeCount candidate regs
      (12 : Fin 17) houtputs12 hrun12 hw12 (by
        simpa [expectedValues] using hout12)
  have hcandidate13 : store13 regs.candidate = candidate := by
    rw [candidate_preserved_internal regs 12 hw12 hrun12]
    exact hcandidate12

  have hframeBits13 :
      store13 regs.frameBits =
        frameBits Q workTapeCount candidate := by
    simpa using houtputs13 (12 : Fin 17) (by omega)
  have hw13 :
      RAM.Structured.Footprint.CmdWritesWithin
        (tailFootprint regs 13)
        (computePowTwo regs regs.frameBits regs.frameRadix) := by
    simpa using
      computePowTwo_tailWrites_internal regs 13 regs.frameBits
        (13 : Fin 17) (by omega)
  obtain ⟨store14, hrun13, hout13⟩ :=
    computePowTwo_runs_internal regs regs.frameBits
      (13 : Fin 17) store13 (frameBits Q workTapeCount candidate)
      hframeBits13
      (stack_index_ne_output_internal regs 0 (12 : Fin 17))
      (stack_index_ne_output_internal regs 5 (12 : Fin 17))
      (stack_index_ne_output_internal regs 1 (12 : Fin 17))
  have houtputs14 :
      OutputsThrough Q workTapeCount candidate 14 regs store14 :=
    outputsThrough_extend_internal Q workTapeCount candidate regs
      (13 : Fin 17) houtputs13 hrun13 hw13 (by
        simpa [expectedValues, frameRadix,
          NeighborhoodProgram.frameRadix] using hout13)
  have hcandidate14 : store14 regs.candidate = candidate := by
    rw [candidate_preserved_internal regs 13 hw13 hrun13]
    exact hcandidate13

  have hfieldBits14 :
      store14 regs.fieldBits =
        fieldBits Q workTapeCount candidate := by
    simpa using houtputs14 (11 : Fin 17) (by omega)
  have hw14 :
      RAM.Structured.Footprint.CmdWritesWithin
        (tailFootprint regs 14)
        (computePowTwo regs regs.fieldBits regs.bankRadix) := by
    simpa using
      computePowTwo_tailWrites_internal regs 14 regs.fieldBits
        (14 : Fin 17) (by omega)
  obtain ⟨store15, hrun14, hout14⟩ :=
    computePowTwo_runs_internal regs regs.fieldBits
      (14 : Fin 17) store14 (fieldBits Q workTapeCount candidate)
      hfieldBits14
      (stack_index_ne_output_internal regs 0 (11 : Fin 17))
      (stack_index_ne_output_internal regs 5 (11 : Fin 17))
      (stack_index_ne_output_internal regs 1 (11 : Fin 17))
  have houtputs15 :
      OutputsThrough Q workTapeCount candidate 15 regs store15 :=
    outputsThrough_extend_internal Q workTapeCount candidate regs
      (14 : Fin 17) houtputs14 hrun14 hw14 (by
        simpa [expectedValues, bankRadix,
          NeighborhoodProgram.bankRadix] using hout14)
  have hcandidate15 : store15 regs.candidate = candidate := by
    rw [candidate_preserved_internal regs 14 hw14 hrun14]
    exact hcandidate14

  have hfan15 :
      store15 regs.fanIn = fanIn workTapeCount := by
    simpa using houtputs15 (5 : Fin 17) (by omega)
  have hchunkCount15 :
      store15 regs.chunkCount =
        chunkCount Q workTapeCount candidate := by
    simpa using houtputs15 (7 : Fin 17) (by omega)
  let store16a :=
    (Basic.imm regs.stackRegisters.one 1).exec store15
  let store16b :=
    (Basic.add regs.bankDigitCount regs.fanIn
      regs.stackRegisters.one).exec store16a
  let store16 :=
    (Basic.mul regs.bankDigitCount regs.bankDigitCount
      regs.chunkCount).exec store16b
  have hrun15 :
      Runs (computeBankDigitCount regs) store15 store16 := by
    simpa [computeBankDigitCount, Cmd.seqList, store16a,
      store16b, store16] using
      Runs.seq
        (Runs.basic (Basic.imm regs.stackRegisters.one 1) store15)
        (Runs.seq
          (Runs.basic
            (Basic.add regs.bankDigitCount regs.fanIn
              regs.stackRegisters.one) store16a)
          (Runs.basic
            (Basic.mul regs.bankDigitCount regs.bankDigitCount
              regs.chunkCount) store16b))
  have hone16a :
      store16a regs.stackRegisters.one = 1 := by
    simp [store16a, Basic.exec]
  have hfan16a :
      store16a regs.fanIn = fanIn workTapeCount := by
    have hne :
        regs.stackRegisters.one ≠ regs.fanIn :=
      stack_index_ne_output_internal regs 5 (5 : Fin 17)
    simp only [store16a, Basic.exec]
    rw [Function.update_apply, if_neg hne.symm]
    exact hfan15
  have hbank16b :
      store16b regs.bankDigitCount =
        fanIn workTapeCount + 1 := by
    simp [store16b, Basic.exec, hfan16a, hone16a]
  have hcount16b :
      store16b regs.chunkCount =
        chunkCount Q workTapeCount candidate := by
    have honeNe :
        regs.stackRegisters.one ≠ regs.chunkCount :=
      stack_index_ne_output_internal regs 5 (7 : Fin 17)
    have hbankNe :
        regs.bankDigitCount ≠ regs.chunkCount :=
      outputAddress_ne regs
        (first := (15 : Fin 17)) (second := (7 : Fin 17))
        (by decide)
    simp [store16b, store16a, Basic.exec, honeNe.symm,
      hbankNe.symm, hchunkCount15]
  have hout15 :
      store16 regs.bankDigitCount =
        bankDigitCount Q workTapeCount candidate := by
    simp only [store16, Basic.exec, Function.update_self]
    rw [hbank16b, hcount16b]
    rfl
  have hw15 :
      RAM.Structured.Footprint.CmdWritesWithin
        (tailFootprint regs 15) (computeBankDigitCount regs) := by
    have hstack :
        regs.stackRegisters.one ∈ tailFootprint regs 15 :=
      stack_mem_tailFootprint_internal regs 15 (5 : Fin 7)
    have hout :
        regs.bankDigitCount ∈ tailFootprint regs 15 :=
      output_mem_tailFootprint_internal regs 15 (15 : Fin 17)
        (by omega)
    simp [computeBankDigitCount, Cmd.seqList,
      RAM.Structured.Footprint.CmdWritesWithin,
      RAM.Structured.Footprint.BasicWritesWithin, hstack, hout]
  have houtputs16 :
      OutputsThrough Q workTapeCount candidate 16 regs store16 :=
    outputsThrough_extend_internal Q workTapeCount candidate regs
      (15 : Fin 17) houtputs15 hrun15 hw15 (by
        simpa [expectedValues] using hout15)
  have hcandidate16 : store16 regs.candidate = candidate := by
    rw [candidate_preserved_internal regs 15 hw15 hrun15]
    exact hcandidate15

  have hdegree16 :
      store16 regs.degreeEndpoint =
        degreeEndpoint Q workTapeCount candidate := by
    simpa using houtputs16 (10 : Fin 17) (by omega)
  let store17a :=
    (Basic.imm regs.stackRegisters.one 1).exec store16
  let store17b :=
    (Basic.imm regs.stackRegisters.value 2).exec store17a
  let store17c :=
    (Basic.add regs.primeRegisters.candidate regs.degreeEndpoint
      regs.stackRegisters.value).exec store17b
  have hdegree17a :
      store17a regs.degreeEndpoint =
        degreeEndpoint Q workTapeCount candidate := by
    have hne :
        regs.stackRegisters.one ≠ regs.degreeEndpoint :=
      stack_index_ne_output_internal regs 5 (10 : Fin 17)
    simp only [store17a, Basic.exec]
    rw [Function.update_apply, if_neg hne.symm]
    exact hdegree16
  have hdegree17b :
      store17b regs.degreeEndpoint =
        degreeEndpoint Q workTapeCount candidate := by
    have hne :
        regs.stackRegisters.value ≠ regs.degreeEndpoint :=
      stack_index_ne_output_internal regs 6 (10 : Fin 17)
    simp only [store17b, Basic.exec]
    rw [Function.update_apply, if_neg hne.symm]
    exact hdegree17a
  have hvalue17b :
      store17b regs.stackRegisters.value = 2 := by
    simp [store17b, Basic.exec]
  have hlower17c :
      store17c regs.primeRegisters.candidate =
        degreeEndpoint Q workTapeCount candidate + 2 := by
    simp [store17c, Basic.exec, hdegree17b, hvalue17b]
  obtain ⟨store17d, hrunSearch, _hsearchPost, hmodulus17d⟩ :=
    CanonicalPrime.search_runs regs.primeRegisters store17c
      (degreeEndpoint Q workTapeCount candidate) hlower17c
  let store17e :=
    (Basic.imm regs.stackRegisters.one 1).exec store17d
  let store17 :=
    (Basic.sub regs.modulusPred regs.primeRegisters.candidate
      regs.stackRegisters.one).exec store17e
  have hmodulus17e :
      store17e regs.primeRegisters.candidate =
        canonicalModulus Q workTapeCount candidate := by
    have hne :
        regs.stackRegisters.one ≠
          regs.primeRegisters.candidate :=
      stack_index_ne_prime_internal regs 5 0
    simp only [store17e, Basic.exec]
    rw [Function.update_apply, if_neg hne.symm]
    exact hmodulus17d
  have hone17e :
      store17e regs.stackRegisters.one = 1 := by
    simp [store17e, Basic.exec]
  have hout16 :
      store17 regs.modulusPred =
        canonicalModulus Q workTapeCount candidate - 1 := by
    simp [store17, Basic.exec, hmodulus17e, hone17e]
  have hmodulus17 :
      store17 regs.primeRegisters.candidate =
        canonicalModulus Q workTapeCount candidate := by
    have hne :
        regs.modulusPred ≠ regs.primeRegisters.candidate :=
      (prime_index_ne_output_internal regs 0 (16 : Fin 17)).symm
    simp only [store17, Basic.exec]
    rw [Function.update_apply, if_neg hne.symm]
    exact hmodulus17e
  have hrun16 :
      Runs (computeCanonicalModulus regs) store16 store17 := by
    simpa [computeCanonicalModulus, Cmd.seqList, store17a,
      store17b, store17c, store17e, store17] using
      Runs.seq
        (Runs.basic (Basic.imm regs.stackRegisters.one 1) store16)
        (Runs.seq
          (Runs.basic
            (Basic.imm regs.stackRegisters.value 2) store17a)
          (Runs.seq
            (Runs.basic
              (Basic.add regs.primeRegisters.candidate
                regs.degreeEndpoint regs.stackRegisters.value)
              store17b)
            (Runs.seq hrunSearch
              (Runs.seq
                (Runs.basic
                  (Basic.imm regs.stackRegisters.one 1) store17d)
                (Runs.basic
                  (Basic.sub regs.modulusPred
                    regs.primeRegisters.candidate
                    regs.stackRegisters.one) store17e)))))
  have hw16 :
      RAM.Structured.Footprint.CmdWritesWithin
        (tailFootprint regs 16)
        (computeCanonicalModulus regs) := by
    have hstack (slot : Fin 7) :
        regs.stackRegisters.index slot ∈ tailFootprint regs 16 :=
      stack_mem_tailFootprint_internal regs 16 slot
    have hprime (slot : Fin 8) :
        regs.primeRegisters.index slot ∈ tailFootprint regs 16 :=
      prime_mem_tailFootprint_internal regs 16 slot
    have hout :
        regs.modulusPred ∈ tailFootprint regs 16 :=
      output_mem_tailFootprint_internal regs 16 (16 : Fin 17)
        (by omega)
    simp [computeCanonicalModulus, PrimeSearch.search,
      PrimeSearch.searchBody, PrimeSearch.primality,
      PrimeSearch.primalitySetupOps, PrimeSearch.trialSetupOps,
      PrimeSearch.trialLoop, PrimeSearch.trialBody,
      PrimeSearch.refreshSearchTest, PrimeSearch.decrementDivisor,
      RuntimeArithmetic.reduce, RuntimeArithmetic.reduceBody,
      RuntimeArithmetic.reduceTestOp,
      PrimeSearch.Registers.reduceRegisters,
      Cmd.seqList, Cmd.basics,
      RAM.Structured.Footprint.CmdWritesWithin,
      RAM.Structured.Footprint.BasicWritesWithin,
      hstack, hprime, hout]
  have houtputs17 :
      OutputsThrough Q workTapeCount candidate 17 regs store17 :=
    outputsThrough_extend_internal Q workTapeCount candidate regs
      (16 : Fin 17) houtputs16 hrun16 hw16 (by
        simpa [expectedValues] using hout16)
  have hcandidate17 : store17 regs.candidate = candidate := by
    rw [candidate_preserved_internal regs 16 hw16 hrun16]
    exact hcandidate16

  have hrunProgram :
      Runs (program Q workTapeCount regs) store store17 := by
    simpa [program, Cmd.seqList] using
      Runs.seq hrun0
        (Runs.seq hrun1
          (Runs.seq hrun2
            (Runs.seq hrun3
              (Runs.seq hrun4
                (Runs.seq hrun5
                  (Runs.seq hrun6
                    (Runs.seq hrun7
                      (Runs.seq hrun8
                        (Runs.seq hrun9
                          (Runs.seq hrun10
                            (Runs.seq hrun11
                              (Runs.seq hrun12
                                (Runs.seq hrun13
                                  (Runs.seq hrun14
                                    (Runs.seq hrun15 hrun16)))))))))))))))
  refine ⟨store17, hrunProgram, ?_⟩
  refine
    { candidate_eq := hcandidate17
      protectedLog_eq := by
        simpa using houtputs17 (0 : Fin 17) (by omega)
      radicand_eq := by
        simpa using houtputs17 (1 : Fin 17) (by omega)
      blockLength_eq := by
        simpa using houtputs17 (2 : Fin 17) (by omega)
      horizon_eq := by
        simpa using houtputs17 (3 : Fin 17) (by omega)
      booleanWidth_eq := by
        simpa using houtputs17 (4 : Fin 17) (by omega)
      fanIn_eq := by
        simpa using houtputs17 (5 : Fin 17) (by omega)
      chunkBits_eq := by
        simpa using houtputs17 (6 : Fin 17) (by omega)
      chunkCount_eq := by
        simpa using houtputs17 (7 : Fin 17) (by omega)
      domainSize_eq := by
        simpa using houtputs17 (8 : Fin 17) (by omega)
      groupedDegree_eq := by
        simpa using houtputs17 (9 : Fin 17) (by omega)
      degreeEndpoint_eq := by
        simpa using houtputs17 (10 : Fin 17) (by omega)
      fieldBits_eq := by
        simpa using houtputs17 (11 : Fin 17) (by omega)
      frameBits_eq := by
        simpa using houtputs17 (12 : Fin 17) (by omega)
      frameRadix_eq := by
        simpa using houtputs17 (13 : Fin 17) (by omega)
      bankRadix_eq := by
        simpa using houtputs17 (14 : Fin 17) (by omega)
      bankDigitCount_eq := by
        simpa using houtputs17 (15 : Fin 17) (by omega)
      modulus_eq := hmodulus17
      modulusPred_eq := by
        simpa using houtputs17 (16 : Fin 17) (by omega)
      eq_outside := by
        intro address haddress
        exact RAM.Structured.Footprint.runs_eq_outside
          (program_sourceWritesWithin_internal Q workTapeCount regs)
          hrunProgram haddress }

theorem program_invariantRuns_internal
    (Q : Type*) [Fintype Q] (workTapeCount : ℕ)
    (regs : Registers) (store : Store)
    (candidate target : ℕ)
    (hcandidate : store regs.candidate = candidate)
    (hcandidateLe : candidate ≤ target)
    (hstore :
      ValuesWithin regs.footprint
        (NeighborhoodProgram.fixedRegisterCount *
          WorkspaceAccounting.trialEnvelopeBits
            Q workTapeCount target) store) :
    ∃ final steps,
      InvariantRuns
        (ValuesWithin regs.footprint
          (NeighborhoodProgram.fixedRegisterCount *
            WorkspaceAccounting.trialEnvelopeBits
              Q workTapeCount target))
        (program Q workTapeCount regs) store final steps ∧
      Post Q workTapeCount candidate regs store final := by
  let width := valueWidth Q workTapeCount target
  let cap := 2 ^ width - 1
  have hbounds :=
    parameterValueBounds_internal Q workTapeCount hcandidateLe
  have hstoreNumeric :
      NeighborhoodProgram.ValuesWithin regs.footprint cap store := by
    rw [show cap = 2 ^ width - 1 by rfl,
      numericWithin_cap_iff_internal]
    simpa [width, valueWidth] using hstore
  have hcapOfSize {value : ℕ}
      (hvalue : Nat.size value ≤ width) :
      value ≤ cap := by
    simpa [cap] using
      (numericCap_iff_size_internal value width).2 hvalue
  have htwoCap : 2 ≤ cap := by
    simpa [cap, width] using hbounds.two_le_cap
  have honeCap : 1 ≤ cap := by omega
  have hcandidateCap : candidate ≤ cap :=
    hcapOfSize (by
      simpa [width] using hbounds.candidate_size)
  have hprotectedLogCap : protectedLog candidate ≤ cap :=
    hcapOfSize (by
      simpa [width] using hbounds.protectedLog_size)
  have hradicandCap : radicand candidate ≤ cap :=
    hcapOfSize (by
      simpa [width] using hbounds.radicand_size)
  have hblockLengthCap : blockLength candidate ≤ cap :=
    hcapOfSize (by
      simpa [width] using hbounds.blockLength_size)
  have hblockLengthSqCap :
      blockLength candidate * blockLength candidate ≤ cap :=
    hcapOfSize (by
      simpa [width] using hbounds.blockLengthSq_size)
  have hceilDividendCap :
      candidate + (blockLength candidate - 1) ≤ cap :=
    hcapOfSize (by
      simpa [width] using hbounds.ceilDividend_size)
  have hwordCandidate :
      regs.stackRegisters.word ≠ regs.candidate := by
    exact (regs.candidate_ne ⟨17, by omega⟩).symm
  have honeCandidate :
      regs.stackRegisters.one ≠ regs.candidate := by
    exact (regs.candidate_ne ⟨22, by omega⟩).symm

  have hw0 :
      RAM.Structured.Footprint.CmdWritesWithin
        (tailFootprint regs 0)
        (computeProtectedLog regs regs.candidate regs.protectedLog) := by
    simpa using
      computeProtectedLog_tailWrites_internal regs 0 regs.candidate
        (0 : Fin 17) (by omega)
  obtain ⟨store1, steps0, hinv0, hout0⟩ :=
    computeProtectedLog_invariantRuns_internal regs regs.footprint cap
      regs.candidate (0 : Fin 17) store candidate hcandidate
      hwordCandidate hcandidateCap
      (by simpa [protectedLog] using hprotectedLogCap)
      htwoCap hstoreNumeric
  have hrun0 :
      Runs (computeProtectedLog regs regs.candidate regs.protectedLog)
        store store1 :=
    InvariantRuns.toRuns hinv0
  have houtputs0 :
      OutputsThrough Q workTapeCount candidate 0 regs store :=
    outputsThrough_zero_internal Q workTapeCount candidate regs store
  have houtputs1 :
      OutputsThrough Q workTapeCount candidate 1 regs store1 :=
    outputsThrough_extend_internal Q workTapeCount candidate regs
      (0 : Fin 17) houtputs0 hrun0 hw0 (by
        simpa [expectedValues, protectedLog] using hout0)
  have hcandidate1 : store1 regs.candidate = candidate := by
    rw [candidate_preserved_internal regs 0 hw0 hrun0]
    exact hcandidate

  let store2 :=
    (Basic.mul regs.radicand regs.candidate regs.protectedLog).exec
      store1
  have hrun1 : Runs (computeRadicand regs) store1 store2 := by
    simpa [computeRadicand, store2] using
      Runs.basic
        (Basic.mul regs.radicand regs.candidate regs.protectedLog)
        store1
  have hout1 :
      store2 regs.radicand = radicand candidate := by
    have hlog := houtputs1 (0 : Fin 17) (by omega)
    simp only [expectedValues, Matrix.cons_val_zero] at hlog
    change store1 regs.protectedLog = protectedLog candidate at hlog
    simp [store2, Basic.exec, radicand, hcandidate1, hlog]
  have hstore2Within :
      NeighborhoodProgram.ValuesWithin regs.footprint cap store2 := by
    apply numericWithin_update_internal regs.footprint cap
      regs.radicand
      (store1 regs.candidate * store1 regs.protectedLog) store1
      (InvariantRuns.final hinv0)
    rw [hcandidate1]
    have hlog := houtputs1 (0 : Fin 17) (by omega)
    change store1 regs.protectedLog = protectedLog candidate at hlog
    rw [hlog]
    exact hradicandCap
  have hinv1 :
      InvariantRuns
        (NeighborhoodProgram.ValuesWithin regs.footprint cap)
        (computeRadicand regs) store1 store2 1 := by
    simpa [computeRadicand, store2] using
      InvariantRuns.basic
        (Basic.mul regs.radicand regs.candidate regs.protectedLog)
        store1 (InvariantRuns.final hinv0) hstore2Within
  have hw1 :
      RAM.Structured.Footprint.CmdWritesWithin
        (tailFootprint regs 1) (computeRadicand regs) := by
    simpa [computeRadicand,
      RAM.Structured.Footprint.CmdWritesWithin,
      RAM.Structured.Footprint.BasicWritesWithin] using
      output_mem_tailFootprint_internal regs 1 (1 : Fin 17)
        (by omega)
  have houtputs2 :
      OutputsThrough Q workTapeCount candidate 2 regs store2 :=
    outputsThrough_extend_internal Q workTapeCount candidate regs
      (1 : Fin 17) houtputs1 hrun1 hw1 (by
        simpa [expectedValues] using hout1)
  have hcandidate2 : store2 regs.candidate = candidate := by
    rw [candidate_preserved_internal regs 1 hw1 hrun1]
    exact hcandidate1

  have hw2 :
      RAM.Structured.Footprint.CmdWritesWithin
        (tailFootprint regs 2)
        (computePositiveCeilSqrt regs regs.radicand
          regs.blockLength) := by
    simpa using
      computePositiveCeilSqrt_tailWrites_internal regs 2
        regs.radicand (2 : Fin 17) (by omega)
  obtain ⟨store3, steps2, hinv2, hout2⟩ :=
    computePositiveCeilSqrt_invariantRuns_internal regs
      regs.footprint cap (1 : Fin 17) (2 : Fin 17) store2
      (radicand candidate) (by decide) hout1 hradicandCap
      (by simpa [blockLength, radicand] using hblockLengthCap)
      (by simpa [blockLength, radicand] using hblockLengthSqCap)
      hstore2Within
  have hrun2 :
      Runs
        (computePositiveCeilSqrt regs regs.radicand regs.blockLength)
        store2 store3 :=
    InvariantRuns.toRuns hinv2
  have houtputs3 :
      OutputsThrough Q workTapeCount candidate 3 regs store3 :=
    outputsThrough_extend_internal Q workTapeCount candidate regs
      (2 : Fin 17) houtputs2 hrun2 hw2 (by
        simpa [expectedValues, blockLength, radicand] using hout2)
  have hcandidate3 : store3 regs.candidate = candidate := by
    rw [candidate_preserved_internal regs 2 hw2 hrun2]
    exact hcandidate2

  have hblock :
      store3 regs.blockLength = blockLength candidate := by
    simpa using houtputs3 (2 : Fin 17) (by omega)
  have hw3 :
      RAM.Structured.Footprint.CmdWritesWithin
        (tailFootprint regs 3)
        (computeCeilDiv regs regs.candidate regs.blockLength
          regs.horizon) := by
    simpa using
      computeCeilDiv_tailWrites_internal regs 3 regs.candidate
        regs.blockLength (3 : Fin 17) (by omega)
  obtain ⟨store4, steps3, hinv3, hout3⟩ :=
    computeCeilDiv_invariantRuns_internal regs regs.footprint cap
      regs.candidate regs.blockLength (3 : Fin 17) store3
      candidate (blockLength candidate) hcandidate3 hblock
      (WorkspaceAccounting.blockLength_pos candidate)
      hwordCandidate
      (stack_index_ne_output_internal regs 0 (2 : Fin 17))
      (stack_index_ne_output_internal regs 1 (2 : Fin 17))
      honeCandidate
      (stack_index_ne_output_internal regs 5 (2 : Fin 17))
      hcandidateCap hblockLengthCap hceilDividendCap
      (InvariantRuns.final hinv2)
  have hrun3 :
      Runs
        (computeCeilDiv regs regs.candidate regs.blockLength
          regs.horizon) store3 store4 :=
    InvariantRuns.toRuns hinv3
  have houtputs4 :
      OutputsThrough Q workTapeCount candidate 4 regs store4 :=
    outputsThrough_extend_internal Q workTapeCount candidate regs
      (3 : Fin 17) houtputs3 hrun3 hw3 (by
        simpa [expectedValues, horizon,
          WorkspaceAccounting.horizon] using hout3)

  have hbooleanWidthCap : booleanWidth Q candidate ≤ cap :=
    hcapOfSize (by
      simpa [width] using hbounds.booleanWidth_size)
  have hfanInCap : fanIn workTapeCount ≤ cap :=
    hcapOfSize (by
      simpa [width] using hbounds.fanIn_size)
  have hfanInBooleanWidthCap :
      fanIn workTapeCount * booleanWidth Q candidate ≤ cap :=
    hcapOfSize (by
      simpa [width] using hbounds.fanInBooleanWidth_size)
  have hchunkBitsCap :
      chunkBits Q workTapeCount candidate ≤ cap :=
    hcapOfSize (by
      simpa [width] using hbounds.chunkBits_size)
  have hchunkDividendCap :
      booleanWidth Q candidate +
        (chunkBits Q workTapeCount candidate - 1) ≤ cap :=
    hcapOfSize (by
      simpa [width] using hbounds.chunkDividend_size)
  have hchunkCountCap :
      chunkCount Q workTapeCount candidate ≤ cap :=
    hcapOfSize (by
      simpa [width] using hbounds.chunkCount_size)
  have hdomainSizeCap :
      domainSize Q workTapeCount candidate ≤ cap :=
    hcapOfSize (by
      simpa [width] using hbounds.domainSize_size)

  let store5a :=
    (Basic.imm regs.stackRegisters.value 5).exec store4
  let store5b :=
    (Basic.mul regs.booleanWidth regs.stackRegisters.value
      regs.blockLength).exec store5a
  let store5c :=
    (Basic.imm regs.stackRegisters.value (Fintype.card Q)).exec
      store5b
  let store5 :=
    (Basic.add regs.booleanWidth regs.stackRegisters.value
      regs.booleanWidth).exec store5c
  have hblock4 :
      store4 regs.blockLength = blockLength candidate := by
    simpa using houtputs4 (2 : Fin 17) (by omega)
  have hvalueNeBoolean :
      regs.stackRegisters.value ≠ regs.booleanWidth :=
    stack_index_ne_output_internal regs 6 (4 : Fin 17)
  have hvalueNeBlock :
      regs.stackRegisters.value ≠ regs.blockLength :=
    stack_index_ne_output_internal regs 6 (2 : Fin 17)
  have hblock5a :
      store5a regs.blockLength = blockLength candidate := by
    simp only [store5a, Basic.exec]
    rw [Function.update_apply, if_neg hvalueNeBlock.symm]
    exact hblock4
  have hvalue5a :
      store5a regs.stackRegisters.value = 5 := by
    simp [store5a, Basic.exec]
  have hboolean5b :
      store5b regs.booleanWidth =
        5 * blockLength candidate := by
    simp [store5b, Basic.exec, hvalue5a, hblock5a]
  have hboolean5c :
      store5c regs.booleanWidth =
        5 * blockLength candidate := by
    simp only [store5c, Basic.exec]
    rw [Function.update_apply, if_neg hvalueNeBoolean.symm]
    exact hboolean5b
  have hvalue5c :
      store5c regs.stackRegisters.value = Fintype.card Q := by
    simp [store5c, Basic.exec]
  have hout4 :
      store5 regs.booleanWidth = booleanWidth Q candidate := by
    simp [store5, Basic.exec, booleanWidth,
      WorkspaceAccounting.booleanWidth, hboolean5c, hvalue5c]
  have hfiveCap : 5 ≤ cap := by
    have hpositive : 0 < blockLength candidate := by
      simpa [blockLength] using
        WorkspaceAccounting.blockLength_pos candidate
    calc
      5 ≤ 5 * blockLength candidate := by omega
      _ ≤ Fintype.card Q + 5 * blockLength candidate := by omega
      _ = booleanWidth Q candidate := by
        rfl
      _ ≤ cap := hbooleanWidthCap
  have hfiveBlockCap :
      5 * blockLength candidate ≤ cap := by
    calc
      5 * blockLength candidate ≤
          Fintype.card Q + 5 * blockLength candidate := by omega
      _ = booleanWidth Q candidate := by
        rfl
      _ ≤ cap := hbooleanWidthCap
  have hcardCap : Fintype.card Q ≤ cap := by
    calc
      Fintype.card Q ≤
          Fintype.card Q + 5 * blockLength candidate := by omega
      _ = booleanWidth Q candidate := by
        rfl
      _ ≤ cap := hbooleanWidthCap
  have hstore5aWithin :
      NeighborhoodProgram.ValuesWithin regs.footprint cap store5a :=
    numericWithin_update_internal regs.footprint cap
      regs.stackRegisters.value 5 store4
      (InvariantRuns.final hinv3) hfiveCap
  have hstore5bWithin :
      NeighborhoodProgram.ValuesWithin regs.footprint cap store5b := by
    apply numericWithin_update_internal regs.footprint cap
      regs.booleanWidth
      (store5a regs.stackRegisters.value *
        store5a regs.blockLength)
      store5a hstore5aWithin
    rw [hvalue5a, hblock5a]
    exact hfiveBlockCap
  have hstore5cWithin :
      NeighborhoodProgram.ValuesWithin regs.footprint cap store5c :=
    numericWithin_update_internal regs.footprint cap
      regs.stackRegisters.value (Fintype.card Q) store5b
      hstore5bWithin hcardCap
  have hstore5Within :
      NeighborhoodProgram.ValuesWithin regs.footprint cap store5 := by
    apply numericWithin_update_internal regs.footprint cap
      regs.booleanWidth
      (store5c regs.stackRegisters.value +
        store5c regs.booleanWidth)
      store5c hstore5cWithin
    rw [hvalue5c, hboolean5c]
    simpa [booleanWidth, WorkspaceAccounting.booleanWidth,
      Nat.add_comm] using hbooleanWidthCap
  have hinv4 :
      InvariantRuns
        (NeighborhoodProgram.ValuesWithin regs.footprint cap)
        (computeBooleanWidth Q regs) store4 store5 4 := by
    simpa [computeBooleanWidth, Cmd.seqList, store5a, store5b,
      store5c, store5] using
      InvariantRuns.seq
        (InvariantRuns.basic
          (Basic.imm regs.stackRegisters.value 5) store4
          (InvariantRuns.final hinv3) hstore5aWithin)
        (InvariantRuns.seq
          (InvariantRuns.basic
            (Basic.mul regs.booleanWidth regs.stackRegisters.value
              regs.blockLength) store5a
            hstore5aWithin hstore5bWithin)
          (InvariantRuns.seq
            (InvariantRuns.basic
              (Basic.imm regs.stackRegisters.value (Fintype.card Q))
              store5b hstore5bWithin hstore5cWithin)
            (InvariantRuns.basic
              (Basic.add regs.booleanWidth
                regs.stackRegisters.value regs.booleanWidth)
              store5c hstore5cWithin hstore5Within)))
  have hrun4 : Runs (computeBooleanWidth Q regs) store4 store5 :=
    InvariantRuns.toRuns hinv4
  have hw4 :
      RAM.Structured.Footprint.CmdWritesWithin
        (tailFootprint regs 4) (computeBooleanWidth Q regs) := by
    have hstack (slot : Fin 7) :
        regs.stackRegisters.index slot ∈ tailFootprint regs 4 :=
      stack_mem_tailFootprint_internal regs 4 slot
    have hout :
        regs.booleanWidth ∈ tailFootprint regs 4 :=
      output_mem_tailFootprint_internal regs 4 (4 : Fin 17)
        (by omega)
    simp [computeBooleanWidth, Cmd.seqList,
      RAM.Structured.Footprint.CmdWritesWithin,
      RAM.Structured.Footprint.BasicWritesWithin, hstack, hout]
  have houtputs5 :
      OutputsThrough Q workTapeCount candidate 5 regs store5 :=
    outputsThrough_extend_internal Q workTapeCount candidate regs
      (4 : Fin 17) houtputs4 hrun4 hw4 (by
        simpa [expectedValues] using hout4)

  let store6 :=
    (Basic.imm regs.fanIn (4 * (workTapeCount + 2))).exec store5
  have hout5 :
      store6 regs.fanIn = fanIn workTapeCount := by
    simp [store6, Basic.exec, fanIn, WorkspaceAccounting.fanIn]
  have hstore6Within :
      NeighborhoodProgram.ValuesWithin regs.footprint cap store6 := by
    apply numericWithin_update_internal regs.footprint cap regs.fanIn
      (4 * (workTapeCount + 2)) store5 hstore5Within
    simpa [fanIn, WorkspaceAccounting.fanIn] using hfanInCap
  have hinv5 :
      InvariantRuns
        (NeighborhoodProgram.ValuesWithin regs.footprint cap)
        (computeFanIn workTapeCount regs) store5 store6 1 := by
    simpa [computeFanIn, store6] using
      InvariantRuns.basic
        (Basic.imm regs.fanIn (4 * (workTapeCount + 2))) store5
        hstore5Within hstore6Within
  have hrun5 :
      Runs (computeFanIn workTapeCount regs) store5 store6 :=
    InvariantRuns.toRuns hinv5
  have hw5 :
      RAM.Structured.Footprint.CmdWritesWithin
        (tailFootprint regs 5)
        (computeFanIn workTapeCount regs) := by
    simpa [computeFanIn,
      RAM.Structured.Footprint.CmdWritesWithin,
      RAM.Structured.Footprint.BasicWritesWithin] using
      output_mem_tailFootprint_internal regs 5 (5 : Fin 17)
        (by omega)
  have houtputs6 :
      OutputsThrough Q workTapeCount candidate 6 regs store6 :=
    outputsThrough_extend_internal Q workTapeCount candidate regs
      (5 : Fin 17) houtputs5 hrun5 hw5 (by
        simpa [expectedValues] using hout5)

  have hfan6 :
      store6 regs.fanIn = fanIn workTapeCount := by
    simpa using houtputs6 (5 : Fin 17) (by omega)
  have hboolean6 :
      store6 regs.booleanWidth = booleanWidth Q candidate := by
    simpa using houtputs6 (4 : Fin 17) (by omega)
  let store7a :=
    (Basic.mul regs.stackRegisters.value regs.fanIn
      regs.booleanWidth).exec store6
  have hvalue7a :
      store7a regs.stackRegisters.value =
        fanIn workTapeCount * booleanWidth Q candidate := by
    simp [store7a, Basic.exec, hfan6, hboolean6]
  have hstore7aWithin :
      NeighborhoodProgram.ValuesWithin regs.footprint cap store7a := by
    apply numericWithin_update_internal regs.footprint cap
      regs.stackRegisters.value
      (store6 regs.fanIn * store6 regs.booleanWidth)
      store6 hstore6Within
    rw [hfan6, hboolean6]
    exact hfanInBooleanWidthCap
  have hinv6a :
      InvariantRuns
        (NeighborhoodProgram.ValuesWithin regs.footprint cap)
        (.basic (Basic.mul regs.stackRegisters.value regs.fanIn
          regs.booleanWidth)) store6 store7a 1 := by
    simpa [store7a] using
      InvariantRuns.basic
        (Basic.mul regs.stackRegisters.value regs.fanIn
          regs.booleanWidth) store6 hstore6Within hstore7aWithin
  obtain ⟨store7, steps6b, hinv6b, hout6⟩ :=
    computeProtectedLog_invariantRuns_internal regs regs.footprint cap
      regs.stackRegisters.value (6 : Fin 17) store7a
      (fanIn workTapeCount * booleanWidth Q candidate)
      hvalue7a (regs.stackRegisters.index_ne (by decide))
      hfanInBooleanWidthCap
      (by
        simpa [chunkBits, WorkspaceAccounting.chunkBits,
          GroupedExtension.LogarithmicParameters.chunkBits,
          fanIn, booleanWidth] using hchunkBitsCap)
      htwoCap hstore7aWithin
  have hinv6 :
      InvariantRuns
        (NeighborhoodProgram.ValuesWithin regs.footprint cap)
        (computeChunkBits regs) store6 store7 (1 + steps6b) := by
    simpa [computeChunkBits] using
      InvariantRuns.seq hinv6a hinv6b
  have hrun6 : Runs (computeChunkBits regs) store6 store7 :=
    InvariantRuns.toRuns hinv6
  have hw6 :
      RAM.Structured.Footprint.CmdWritesWithin
        (tailFootprint regs 6) (computeChunkBits regs) := by
    have hvalue :
        regs.stackRegisters.value ∈ tailFootprint regs 6 :=
      stack_mem_tailFootprint_internal regs 6 (6 : Fin 7)
    have hlog :=
      computeProtectedLog_tailWrites_internal regs 6
        regs.stackRegisters.value (6 : Fin 17) (by omega)
    simpa [computeChunkBits,
      RAM.Structured.Footprint.CmdWritesWithin,
      RAM.Structured.Footprint.BasicWritesWithin] using
      And.intro hvalue hlog
  have houtputs7 :
      OutputsThrough Q workTapeCount candidate 7 regs store7 :=
    outputsThrough_extend_internal Q workTapeCount candidate regs
      (6 : Fin 17) houtputs6 hrun6 hw6 (by
        simpa [expectedValues, chunkBits,
          WorkspaceAccounting.chunkBits,
          GroupedExtension.LogarithmicParameters.chunkBits,
          fanIn, booleanWidth] using hout6)

  have hboolean7 :
      store7 regs.booleanWidth = booleanWidth Q candidate := by
    simpa using houtputs7 (4 : Fin 17) (by omega)
  have hchunkBits7 :
      store7 regs.chunkBits =
        chunkBits Q workTapeCount candidate := by
    simpa using houtputs7 (6 : Fin 17) (by omega)
  have hw7 :
      RAM.Structured.Footprint.CmdWritesWithin
        (tailFootprint regs 7)
        (computeCeilDiv regs regs.booleanWidth regs.chunkBits
          regs.chunkCount) := by
    simpa using
      computeCeilDiv_tailWrites_internal regs 7
        regs.booleanWidth regs.chunkBits (7 : Fin 17) (by omega)
  obtain ⟨store8, steps7, hinv7, hout7⟩ :=
    computeCeilDiv_invariantRuns_internal regs regs.footprint cap
      regs.booleanWidth regs.chunkBits (7 : Fin 17) store7
      (booleanWidth Q candidate)
      (chunkBits Q workTapeCount candidate)
      hboolean7 hchunkBits7
      (GroupedExtension.LogarithmicParameters.chunkBits_pos
        (booleanWidth Q candidate) (fanIn workTapeCount))
      (stack_index_ne_output_internal regs 0 (4 : Fin 17))
      (stack_index_ne_output_internal regs 0 (6 : Fin 17))
      (stack_index_ne_output_internal regs 1 (6 : Fin 17))
      (stack_index_ne_output_internal regs 5 (4 : Fin 17))
      (stack_index_ne_output_internal regs 5 (6 : Fin 17))
      hbooleanWidthCap hchunkBitsCap hchunkDividendCap
      (InvariantRuns.final hinv6)
  have hrun7 :
      Runs
        (computeCeilDiv regs regs.booleanWidth regs.chunkBits
          regs.chunkCount) store7 store8 :=
    InvariantRuns.toRuns hinv7
  have houtputs8 :
      OutputsThrough Q workTapeCount candidate 8 regs store8 :=
    outputsThrough_extend_internal Q workTapeCount candidate regs
      (7 : Fin 17) houtputs7 hrun7 hw7 (by
        simpa [expectedValues, chunkCount,
          WorkspaceAccounting.chunkCount,
          GroupedExtension.LogarithmicParameters.chunkCount]
          using hout7)

  have hchunkBits8 :
      store8 regs.chunkBits =
        chunkBits Q workTapeCount candidate := by
    simpa using houtputs8 (6 : Fin 17) (by omega)
  have hw8 :
      RAM.Structured.Footprint.CmdWritesWithin
        (tailFootprint regs 8)
        (computePowTwo regs regs.chunkBits regs.domainSize) := by
    simpa using
      computePowTwo_tailWrites_internal regs 8 regs.chunkBits
        (8 : Fin 17) (by omega)
  obtain ⟨store9, steps8, hinv8, hout8⟩ :=
    computePowTwo_invariantRuns_internal regs regs.footprint cap
      regs.chunkBits (8 : Fin 17) store8
      (chunkBits Q workTapeCount candidate) hchunkBits8
      (stack_index_ne_output_internal regs 0 (6 : Fin 17))
      (stack_index_ne_output_internal regs 5 (6 : Fin 17))
      (stack_index_ne_output_internal regs 1 (6 : Fin 17))
      hchunkBitsCap
      (by simpa [domainSize,
          PrimeGrouped.Logarithmic.domainSize] using hdomainSizeCap)
      htwoCap (InvariantRuns.final hinv7)
  have hrun8 :
      Runs (computePowTwo regs regs.chunkBits regs.domainSize)
        store8 store9 :=
    InvariantRuns.toRuns hinv8
  have houtputs9 :
      OutputsThrough Q workTapeCount candidate 9 regs store9 :=
    outputsThrough_extend_internal Q workTapeCount candidate regs
      (8 : Fin 17) houtputs8 hrun8 hw8 (by
        simpa [expectedValues, domainSize,
          PrimeGrouped.Logarithmic.domainSize] using hout8)

  have hfanInChunkCountCap :
      fanIn workTapeCount *
        chunkCount Q workTapeCount candidate ≤ cap :=
    hcapOfSize (by
      simpa [width] using hbounds.fanInChunkCount_size)
  have hgroupedDegreeCap :
      groupedDegree Q workTapeCount candidate ≤ cap :=
    hcapOfSize (by
      simpa [width] using hbounds.groupedDegree_size)
  have hdegreeEndpointCap :
      degreeEndpoint Q workTapeCount candidate ≤ cap :=
    hcapOfSize (by
      simpa [width] using hbounds.degreeEndpoint_size)
  have hfieldBitsCap :
      fieldBits Q workTapeCount candidate ≤ cap :=
    hcapOfSize (by
      simpa [width] using hbounds.fieldBits_size)
  have hframeBitsCap :
      frameBits Q workTapeCount candidate ≤ cap :=
    hcapOfSize (by
      simpa [width] using hbounds.frameBits_size)

  have hdomain9 :
      store9 regs.domainSize =
        domainSize Q workTapeCount candidate := by
    simpa using houtputs9 (8 : Fin 17) (by omega)
  have hfan9 :
      store9 regs.fanIn = fanIn workTapeCount := by
    simpa using houtputs9 (5 : Fin 17) (by omega)
  have hchunkCount9 :
      store9 regs.chunkCount =
        chunkCount Q workTapeCount candidate := by
    simpa using houtputs9 (7 : Fin 17) (by omega)
  let store10a :=
    (Basic.imm regs.stackRegisters.one 1).exec store9
  let store10b :=
    (Basic.sub regs.stackRegisters.value regs.domainSize
      regs.stackRegisters.one).exec store10a
  let store10c :=
    (Basic.mul regs.groupedDegree regs.fanIn regs.chunkCount).exec
      store10b
  let store10 :=
    (Basic.mul regs.groupedDegree regs.groupedDegree
      regs.stackRegisters.value).exec store10c
  have hone10a :
      store10a regs.stackRegisters.one = 1 := by
    simp [store10a, Basic.exec]
  have hdomain10a :
      store10a regs.domainSize =
        domainSize Q workTapeCount candidate := by
    have hne :
        regs.stackRegisters.one ≠ regs.domainSize :=
      stack_index_ne_output_internal regs 5 (8 : Fin 17)
    simp only [store10a, Basic.exec]
    rw [Function.update_apply, if_neg hne.symm]
    exact hdomain9
  have hvalue10b :
      store10b regs.stackRegisters.value =
        domainSize Q workTapeCount candidate - 1 := by
    simp [store10b, Basic.exec, hdomain10a, hone10a]
  have hfan10b :
      store10b regs.fanIn = fanIn workTapeCount := by
    have honeNe :
        regs.stackRegisters.one ≠ regs.fanIn :=
      stack_index_ne_output_internal regs 5 (5 : Fin 17)
    have hvalueNe :
        regs.stackRegisters.value ≠ regs.fanIn :=
      stack_index_ne_output_internal regs 6 (5 : Fin 17)
    simp [store10b, store10a, Basic.exec, honeNe.symm,
      hvalueNe.symm, hfan9]
  have hcount10b :
      store10b regs.chunkCount =
        chunkCount Q workTapeCount candidate := by
    have honeNe :
        regs.stackRegisters.one ≠ regs.chunkCount :=
      stack_index_ne_output_internal regs 5 (7 : Fin 17)
    have hvalueNe :
        regs.stackRegisters.value ≠ regs.chunkCount :=
      stack_index_ne_output_internal regs 6 (7 : Fin 17)
    simp [store10b, store10a, Basic.exec, honeNe.symm,
      hvalueNe.symm, hchunkCount9]
  have hgrouped10c :
      store10c regs.groupedDegree =
        fanIn workTapeCount *
          chunkCount Q workTapeCount candidate := by
    simp [store10c, Basic.exec, hfan10b, hcount10b]
  have hvalue10c :
      store10c regs.stackRegisters.value =
        domainSize Q workTapeCount candidate - 1 := by
    have hne :
        regs.groupedDegree ≠ regs.stackRegisters.value :=
      (stack_index_ne_output_internal regs 6 (9 : Fin 17)).symm
    simp only [store10c, Basic.exec]
    rw [Function.update_apply, if_neg hne.symm]
    exact hvalue10b
  have hout9 :
      store10 regs.groupedDegree =
        groupedDegree Q workTapeCount candidate := by
    simp only [store10, Basic.exec, Function.update_self]
    rw [hgrouped10c, hvalue10c]
    rfl
  have hvalue10 :
      store10 regs.stackRegisters.value =
        domainSize Q workTapeCount candidate - 1 := by
    have hne :
        regs.groupedDegree ≠ regs.stackRegisters.value :=
      (stack_index_ne_output_internal regs 6 (9 : Fin 17)).symm
    simp only [store10, Basic.exec]
    rw [Function.update_apply, if_neg hne.symm]
    exact hvalue10c
  have hstore10aWithin :
      NeighborhoodProgram.ValuesWithin regs.footprint cap store10a :=
    numericWithin_update_internal regs.footprint cap
      regs.stackRegisters.one 1 store9
      (InvariantRuns.final hinv8) honeCap
  have hstore10bWithin :
      NeighborhoodProgram.ValuesWithin regs.footprint cap store10b := by
    apply numericWithin_update_internal regs.footprint cap
      regs.stackRegisters.value
      (store10a regs.domainSize - store10a regs.stackRegisters.one)
      store10a hstore10aWithin
    rw [hdomain10a, hone10a]
    exact (Nat.sub_le _ _).trans hdomainSizeCap
  have hstore10cWithin :
      NeighborhoodProgram.ValuesWithin regs.footprint cap store10c := by
    apply numericWithin_update_internal regs.footprint cap
      regs.groupedDegree
      (store10b regs.fanIn * store10b regs.chunkCount)
      store10b hstore10bWithin
    rw [hfan10b, hcount10b]
    exact hfanInChunkCountCap
  have hstore10Within :
      NeighborhoodProgram.ValuesWithin regs.footprint cap store10 := by
    apply numericWithin_update_internal regs.footprint cap
      regs.groupedDegree
      (store10c regs.groupedDegree *
        store10c regs.stackRegisters.value)
      store10c hstore10cWithin
    rw [hgrouped10c, hvalue10c]
    exact hgroupedDegreeCap
  have hinv9 :
      InvariantRuns
        (NeighborhoodProgram.ValuesWithin regs.footprint cap)
        (computeGroupedDegree regs) store9 store10 4 := by
    simpa [computeGroupedDegree, Cmd.seqList, store10a, store10b,
      store10c, store10] using
      InvariantRuns.seq
        (InvariantRuns.basic
          (Basic.imm regs.stackRegisters.one 1) store9
          (InvariantRuns.final hinv8) hstore10aWithin)
        (InvariantRuns.seq
          (InvariantRuns.basic
            (Basic.sub regs.stackRegisters.value regs.domainSize
              regs.stackRegisters.one) store10a
            hstore10aWithin hstore10bWithin)
          (InvariantRuns.seq
            (InvariantRuns.basic
              (Basic.mul regs.groupedDegree regs.fanIn
                regs.chunkCount) store10b
              hstore10bWithin hstore10cWithin)
            (InvariantRuns.basic
              (Basic.mul regs.groupedDegree regs.groupedDegree
                regs.stackRegisters.value) store10c
              hstore10cWithin hstore10Within)))
  have hrun9 : Runs (computeGroupedDegree regs) store9 store10 :=
    InvariantRuns.toRuns hinv9
  have hw9 :
      RAM.Structured.Footprint.CmdWritesWithin
        (tailFootprint regs 9) (computeGroupedDegree regs) := by
    have hstack (slot : Fin 7) :
        regs.stackRegisters.index slot ∈ tailFootprint regs 9 :=
      stack_mem_tailFootprint_internal regs 9 slot
    have hout :
        regs.groupedDegree ∈ tailFootprint regs 9 :=
      output_mem_tailFootprint_internal regs 9 (9 : Fin 17)
        (by omega)
    simp [computeGroupedDegree, Cmd.seqList,
      RAM.Structured.Footprint.CmdWritesWithin,
      RAM.Structured.Footprint.BasicWritesWithin, hstack, hout]
  have houtputs10 :
      OutputsThrough Q workTapeCount candidate 10 regs store10 :=
    outputsThrough_extend_internal Q workTapeCount candidate regs
      (9 : Fin 17) houtputs9 hrun9 hw9 (by
        simpa [expectedValues] using hout9)

  have hgrouped10 :
      store10 regs.groupedDegree =
        groupedDegree Q workTapeCount candidate := by
    simpa using houtputs10 (9 : Fin 17) (by omega)
  have hw10 :
      RAM.Structured.Footprint.CmdWritesWithin
        (tailFootprint regs 10)
        (computeMax regs regs.groupedDegree
          regs.stackRegisters.value regs.degreeEndpoint) := by
    simpa using
      computeMax_tailWrites_internal regs 10 regs.groupedDegree
        regs.stackRegisters.value (10 : Fin 17) (by omega)
  obtain ⟨store11, steps10, hinv10, hout10⟩ :=
    computeMax_invariantRuns_internal regs regs.footprint cap
      regs.groupedDegree regs.stackRegisters.value (10 : Fin 17)
      store10 (groupedDegree Q workTapeCount candidate)
      (domainSize Q workTapeCount candidate - 1)
      hgrouped10 hvalue10
      (outputAddress_ne regs
        (first := (10 : Fin 17)) (second := (9 : Fin 17))
        (by decide))
      (stack_index_ne_output_internal regs 6 (10 : Fin 17)).symm
      (stack_index_ne_output_internal regs 4 (9 : Fin 17))
      (regs.stackRegisters.index_ne (by decide))
      hgroupedDegreeCap
      ((Nat.sub_le _ _).trans hdomainSizeCap)
      hstore10Within
  have hrun10 :
      Runs
        (computeMax regs regs.groupedDegree
          regs.stackRegisters.value regs.degreeEndpoint)
        store10 store11 :=
    InvariantRuns.toRuns hinv10
  have houtputs11 :
      OutputsThrough Q workTapeCount candidate 11 regs store11 :=
    outputsThrough_extend_internal Q workTapeCount candidate regs
      (10 : Fin 17) houtputs10 hrun10 hw10 (by
        simpa [expectedValues, degreeEndpoint,
          PrimeGrouped.Logarithmic.degreeEndpoint] using hout10)

  have hchunkBits11 :
      store11 regs.chunkBits =
        chunkBits Q workTapeCount candidate := by
    simpa using houtputs11 (6 : Fin 17) (by omega)
  let store12a :=
    (Basic.imm regs.stackRegisters.value 2).exec store11
  let store12 :=
    (Basic.mul regs.fieldBits regs.stackRegisters.value
      regs.chunkBits).exec store12a
  have hchunkBits12a :
      store12a regs.chunkBits =
        chunkBits Q workTapeCount candidate := by
    have hne :
        regs.stackRegisters.value ≠ regs.chunkBits :=
      stack_index_ne_output_internal regs 6 (6 : Fin 17)
    simp only [store12a, Basic.exec]
    rw [Function.update_apply, if_neg hne.symm]
    exact hchunkBits11
  have hvalue12a :
      store12a regs.stackRegisters.value = 2 := by
    simp [store12a, Basic.exec]
  have hout11 :
      store12 regs.fieldBits =
        fieldBits Q workTapeCount candidate := by
    simp only [store12, Basic.exec, Function.update_self]
    rw [hvalue12a, hchunkBits12a]
    rfl
  have hstore12aWithin :
      NeighborhoodProgram.ValuesWithin regs.footprint cap store12a :=
    numericWithin_update_internal regs.footprint cap
      regs.stackRegisters.value 2 store11
      (InvariantRuns.final hinv10) htwoCap
  have hstore12Within :
      NeighborhoodProgram.ValuesWithin regs.footprint cap store12 := by
    apply numericWithin_update_internal regs.footprint cap
      regs.fieldBits
      (store12a regs.stackRegisters.value * store12a regs.chunkBits)
      store12a hstore12aWithin
    rw [hvalue12a, hchunkBits12a]
    exact hfieldBitsCap
  have hinv11 :
      InvariantRuns
        (NeighborhoodProgram.ValuesWithin regs.footprint cap)
        (computeFieldBits regs) store11 store12 2 := by
    simpa [computeFieldBits, store12a, store12] using
      InvariantRuns.seq
        (InvariantRuns.basic
          (Basic.imm regs.stackRegisters.value 2) store11
          (InvariantRuns.final hinv10) hstore12aWithin)
        (InvariantRuns.basic
          (Basic.mul regs.fieldBits regs.stackRegisters.value
            regs.chunkBits) store12a
          hstore12aWithin hstore12Within)
  have hrun11 : Runs (computeFieldBits regs) store11 store12 :=
    InvariantRuns.toRuns hinv11
  have hw11 :
      RAM.Structured.Footprint.CmdWritesWithin
        (tailFootprint regs 11) (computeFieldBits regs) := by
    have hstack :
        regs.stackRegisters.value ∈ tailFootprint regs 11 :=
      stack_mem_tailFootprint_internal regs 11 (6 : Fin 7)
    have hout :
        regs.fieldBits ∈ tailFootprint regs 11 :=
      output_mem_tailFootprint_internal regs 11 (11 : Fin 17)
        (by omega)
    simp [computeFieldBits,
      RAM.Structured.Footprint.CmdWritesWithin,
      RAM.Structured.Footprint.BasicWritesWithin, hstack, hout]
  have houtputs12 :
      OutputsThrough Q workTapeCount candidate 12 regs store12 :=
    outputsThrough_extend_internal Q workTapeCount candidate regs
      (11 : Fin 17) houtputs11 hrun11 hw11 (by
        simpa [expectedValues] using hout11)

  have hchunkBits12 :
      store12 regs.chunkBits =
        chunkBits Q workTapeCount candidate := by
    simpa using houtputs12 (6 : Fin 17) (by omega)
  let store13a :=
    (Basic.imm regs.stackRegisters.value 24).exec store12
  let store13 :=
    (Basic.mul regs.frameBits regs.stackRegisters.value
      regs.chunkBits).exec store13a
  have hchunkBits13a :
      store13a regs.chunkBits =
        chunkBits Q workTapeCount candidate := by
    have hne :
        regs.stackRegisters.value ≠ regs.chunkBits :=
      stack_index_ne_output_internal regs 6 (6 : Fin 17)
    simp only [store13a, Basic.exec]
    rw [Function.update_apply, if_neg hne.symm]
    exact hchunkBits12
  have hvalue13a :
      store13a regs.stackRegisters.value = 24 := by
    simp [store13a, Basic.exec]
  have hout12 :
      store13 regs.frameBits =
        frameBits Q workTapeCount candidate := by
    simp only [store13, Basic.exec, Function.update_self]
    rw [hvalue13a, hchunkBits13a]
    simpa [frameBits, chunkBits] using
      (WorkspaceAccounting.frameBits_eq
        Q workTapeCount candidate).symm
  have htwentyFourCap : 24 ≤ cap := by
    have hchunkPositive :
        0 < WorkspaceAccounting.chunkBits
          Q workTapeCount candidate :=
      GroupedExtension.LogarithmicParameters.chunkBits_pos
        (booleanWidth Q candidate) (fanIn workTapeCount)
    have htwentyFourLe :
        24 ≤ WorkspaceAccounting.frameBits
          Q workTapeCount candidate := by
      rw [WorkspaceAccounting.frameBits_eq]
      omega
    exact htwentyFourLe.trans hframeBitsCap
  have hstore13aWithin :
      NeighborhoodProgram.ValuesWithin regs.footprint cap store13a :=
    numericWithin_update_internal regs.footprint cap
      regs.stackRegisters.value 24 store12
      hstore12Within htwentyFourCap
  have hstore13Within :
      NeighborhoodProgram.ValuesWithin regs.footprint cap store13 := by
    apply numericWithin_update_internal regs.footprint cap
      regs.frameBits
      (store13a regs.stackRegisters.value * store13a regs.chunkBits)
      store13a hstore13aWithin
    rw [hvalue13a, hchunkBits13a]
    rw [← WorkspaceAccounting.frameBits_eq Q workTapeCount candidate]
    exact hframeBitsCap
  have hinv12 :
      InvariantRuns
        (NeighborhoodProgram.ValuesWithin regs.footprint cap)
        (computeFrameBits regs) store12 store13 2 := by
    simpa [computeFrameBits, store13a, store13] using
      InvariantRuns.seq
        (InvariantRuns.basic
          (Basic.imm regs.stackRegisters.value 24) store12
          hstore12Within hstore13aWithin)
        (InvariantRuns.basic
          (Basic.mul regs.frameBits regs.stackRegisters.value
            regs.chunkBits) store13a
          hstore13aWithin hstore13Within)
  have hrun12 : Runs (computeFrameBits regs) store12 store13 :=
    InvariantRuns.toRuns hinv12
  have hw12 :
      RAM.Structured.Footprint.CmdWritesWithin
        (tailFootprint regs 12) (computeFrameBits regs) := by
    have hstack :
        regs.stackRegisters.value ∈ tailFootprint regs 12 :=
      stack_mem_tailFootprint_internal regs 12 (6 : Fin 7)
    have hout :
        regs.frameBits ∈ tailFootprint regs 12 :=
      output_mem_tailFootprint_internal regs 12 (12 : Fin 17)
        (by omega)
    simp [computeFrameBits,
      RAM.Structured.Footprint.CmdWritesWithin,
      RAM.Structured.Footprint.BasicWritesWithin, hstack, hout]
  have houtputs13 :
      OutputsThrough Q workTapeCount candidate 13 regs store13 :=
    outputsThrough_extend_internal Q workTapeCount candidate regs
      (12 : Fin 17) houtputs12 hrun12 hw12 (by
        simpa [expectedValues] using hout12)

  have hframeRadixCap :
      frameRadix Q workTapeCount candidate ≤ cap :=
    hcapOfSize (by
      simpa [width] using hbounds.frameRadix_size)
  have hbankRadixCap :
      bankRadix Q workTapeCount candidate ≤ cap :=
    hcapOfSize (by
      simpa [width] using hbounds.bankRadix_size)
  have hfanInSuccCap : fanIn workTapeCount + 1 ≤ cap :=
    hcapOfSize (by
      simpa [width] using hbounds.fanInSucc_size)
  have hbankDigitCountCap :
      bankDigitCount Q workTapeCount candidate ≤ cap :=
    hcapOfSize (by
      simpa [width] using hbounds.bankDigitCount_size)

  have hframeBits13 :
      store13 regs.frameBits =
        frameBits Q workTapeCount candidate := by
    simpa using houtputs13 (12 : Fin 17) (by omega)
  have hw13 :
      RAM.Structured.Footprint.CmdWritesWithin
        (tailFootprint regs 13)
        (computePowTwo regs regs.frameBits regs.frameRadix) := by
    simpa using
      computePowTwo_tailWrites_internal regs 13 regs.frameBits
        (13 : Fin 17) (by omega)
  obtain ⟨store14, steps13, hinv13, hout13⟩ :=
    computePowTwo_invariantRuns_internal regs regs.footprint cap
      regs.frameBits (13 : Fin 17) store13
      (frameBits Q workTapeCount candidate) hframeBits13
      (stack_index_ne_output_internal regs 0 (12 : Fin 17))
      (stack_index_ne_output_internal regs 5 (12 : Fin 17))
      (stack_index_ne_output_internal regs 1 (12 : Fin 17))
      hframeBitsCap
      (by simpa [frameRadix,
          NeighborhoodProgram.frameRadix] using hframeRadixCap)
      htwoCap hstore13Within
  have hrun13 :
      Runs (computePowTwo regs regs.frameBits regs.frameRadix)
        store13 store14 :=
    InvariantRuns.toRuns hinv13
  have houtputs14 :
      OutputsThrough Q workTapeCount candidate 14 regs store14 :=
    outputsThrough_extend_internal Q workTapeCount candidate regs
      (13 : Fin 17) houtputs13 hrun13 hw13 (by
        simpa [expectedValues, frameRadix,
          NeighborhoodProgram.frameRadix] using hout13)

  have hfieldBits14 :
      store14 regs.fieldBits =
        fieldBits Q workTapeCount candidate := by
    simpa using houtputs14 (11 : Fin 17) (by omega)
  have hw14 :
      RAM.Structured.Footprint.CmdWritesWithin
        (tailFootprint regs 14)
        (computePowTwo regs regs.fieldBits regs.bankRadix) := by
    simpa using
      computePowTwo_tailWrites_internal regs 14 regs.fieldBits
        (14 : Fin 17) (by omega)
  obtain ⟨store15, steps14, hinv14, hout14⟩ :=
    computePowTwo_invariantRuns_internal regs regs.footprint cap
      regs.fieldBits (14 : Fin 17) store14
      (fieldBits Q workTapeCount candidate) hfieldBits14
      (stack_index_ne_output_internal regs 0 (11 : Fin 17))
      (stack_index_ne_output_internal regs 5 (11 : Fin 17))
      (stack_index_ne_output_internal regs 1 (11 : Fin 17))
      hfieldBitsCap
      (by simpa [bankRadix,
          NeighborhoodProgram.bankRadix] using hbankRadixCap)
      htwoCap (InvariantRuns.final hinv13)
  have hrun14 :
      Runs (computePowTwo regs regs.fieldBits regs.bankRadix)
        store14 store15 :=
    InvariantRuns.toRuns hinv14
  have houtputs15 :
      OutputsThrough Q workTapeCount candidate 15 regs store15 :=
    outputsThrough_extend_internal Q workTapeCount candidate regs
      (14 : Fin 17) houtputs14 hrun14 hw14 (by
        simpa [expectedValues, bankRadix,
          NeighborhoodProgram.bankRadix] using hout14)

  have hfan15 :
      store15 regs.fanIn = fanIn workTapeCount := by
    simpa using houtputs15 (5 : Fin 17) (by omega)
  have hchunkCount15 :
      store15 regs.chunkCount =
        chunkCount Q workTapeCount candidate := by
    simpa using houtputs15 (7 : Fin 17) (by omega)
  let store16a :=
    (Basic.imm regs.stackRegisters.one 1).exec store15
  let store16b :=
    (Basic.add regs.bankDigitCount regs.fanIn
      regs.stackRegisters.one).exec store16a
  let store16 :=
    (Basic.mul regs.bankDigitCount regs.bankDigitCount
      regs.chunkCount).exec store16b
  have hone16a :
      store16a regs.stackRegisters.one = 1 := by
    simp [store16a, Basic.exec]
  have hfan16a :
      store16a regs.fanIn = fanIn workTapeCount := by
    have hne :
        regs.stackRegisters.one ≠ regs.fanIn :=
      stack_index_ne_output_internal regs 5 (5 : Fin 17)
    simp only [store16a, Basic.exec]
    rw [Function.update_apply, if_neg hne.symm]
    exact hfan15
  have hbank16b :
      store16b regs.bankDigitCount =
        fanIn workTapeCount + 1 := by
    simp [store16b, Basic.exec, hfan16a, hone16a]
  have hcount16b :
      store16b regs.chunkCount =
        chunkCount Q workTapeCount candidate := by
    have honeNe :
        regs.stackRegisters.one ≠ regs.chunkCount :=
      stack_index_ne_output_internal regs 5 (7 : Fin 17)
    have hbankNe :
        regs.bankDigitCount ≠ regs.chunkCount :=
      outputAddress_ne regs
        (first := (15 : Fin 17)) (second := (7 : Fin 17))
        (by decide)
    simp [store16b, store16a, Basic.exec, honeNe.symm,
      hbankNe.symm, hchunkCount15]
  have hout15 :
      store16 regs.bankDigitCount =
        bankDigitCount Q workTapeCount candidate := by
    simp only [store16, Basic.exec, Function.update_self]
    rw [hbank16b, hcount16b]
    rfl
  have hstore16aWithin :
      NeighborhoodProgram.ValuesWithin regs.footprint cap store16a :=
    numericWithin_update_internal regs.footprint cap
      regs.stackRegisters.one 1 store15
      (InvariantRuns.final hinv14) honeCap
  have hstore16bWithin :
      NeighborhoodProgram.ValuesWithin regs.footprint cap store16b := by
    apply numericWithin_update_internal regs.footprint cap
      regs.bankDigitCount
      (store16a regs.fanIn + store16a regs.stackRegisters.one)
      store16a hstore16aWithin
    rw [hfan16a, hone16a]
    exact hfanInSuccCap
  have hstore16Within :
      NeighborhoodProgram.ValuesWithin regs.footprint cap store16 := by
    apply numericWithin_update_internal regs.footprint cap
      regs.bankDigitCount
      (store16b regs.bankDigitCount * store16b regs.chunkCount)
      store16b hstore16bWithin
    rw [hbank16b, hcount16b]
    exact hbankDigitCountCap
  have hinv15 :
      InvariantRuns
        (NeighborhoodProgram.ValuesWithin regs.footprint cap)
        (computeBankDigitCount regs) store15 store16 3 := by
    simpa [computeBankDigitCount, Cmd.seqList, store16a,
      store16b, store16] using
      InvariantRuns.seq
        (InvariantRuns.basic
          (Basic.imm regs.stackRegisters.one 1) store15
          (InvariantRuns.final hinv14) hstore16aWithin)
        (InvariantRuns.seq
          (InvariantRuns.basic
            (Basic.add regs.bankDigitCount regs.fanIn
              regs.stackRegisters.one) store16a
            hstore16aWithin hstore16bWithin)
          (InvariantRuns.basic
            (Basic.mul regs.bankDigitCount regs.bankDigitCount
              regs.chunkCount) store16b
            hstore16bWithin hstore16Within))
  have hrun15 :
      Runs (computeBankDigitCount regs) store15 store16 :=
    InvariantRuns.toRuns hinv15
  have hw15 :
      RAM.Structured.Footprint.CmdWritesWithin
        (tailFootprint regs 15) (computeBankDigitCount regs) := by
    have hstack :
        regs.stackRegisters.one ∈ tailFootprint regs 15 :=
      stack_mem_tailFootprint_internal regs 15 (5 : Fin 7)
    have hout :
        regs.bankDigitCount ∈ tailFootprint regs 15 :=
      output_mem_tailFootprint_internal regs 15 (15 : Fin 17)
        (by omega)
    simp [computeBankDigitCount, Cmd.seqList,
      RAM.Structured.Footprint.CmdWritesWithin,
      RAM.Structured.Footprint.BasicWritesWithin, hstack, hout]
  have houtputs16 :
      OutputsThrough Q workTapeCount candidate 16 regs store16 :=
    outputsThrough_extend_internal Q workTapeCount candidate regs
      (15 : Fin 17) houtputs15 hrun15 hw15 (by
        simpa [expectedValues] using hout15)

  have hdegree16 :
      store16 regs.degreeEndpoint =
        degreeEndpoint Q workTapeCount candidate := by
    simpa using houtputs16 (10 : Fin 17) (by omega)
  obtain ⟨store17, steps16, hinv16, _hmodulus17, _hout16⟩ :=
    computeCanonicalModulus_invariantRuns_internal regs
      regs.footprint width store16
      (degreeEndpoint Q workTapeCount candidate) hdegree16
      (prime_footprint_subset_internal regs)
      (by simpa [width] using hbounds.primeLower_size)
      (by simpa [width] using hbounds.two_le_cap)
      (by simpa [cap] using hstore16Within)

  have hprogramNumericExists :
      ∃ totalSteps,
        InvariantRuns
          (NeighborhoodProgram.ValuesWithin regs.footprint cap)
          (program Q workTapeCount regs) store store17 totalSteps := by
    refine ⟨steps0 +
      (1 +
        (steps2 +
          (steps3 +
            (4 +
              (1 +
                ((1 + steps6b) +
                  (steps7 +
                    (steps8 +
                      (4 +
                        (steps10 +
                          (2 +
                            (2 +
                              (steps13 +
                                (steps14 +
                                  (3 + steps16))))))))))))))),
      ?_⟩
    simpa [program, Cmd.seqList] using
      InvariantRuns.seq hinv0
        (InvariantRuns.seq hinv1
          (InvariantRuns.seq hinv2
            (InvariantRuns.seq hinv3
              (InvariantRuns.seq hinv4
                (InvariantRuns.seq hinv5
                  (InvariantRuns.seq hinv6
                    (InvariantRuns.seq hinv7
                      (InvariantRuns.seq hinv8
                        (InvariantRuns.seq hinv9
                          (InvariantRuns.seq hinv10
                            (InvariantRuns.seq hinv11
                              (InvariantRuns.seq hinv12
                                (InvariantRuns.seq hinv13
                                  (InvariantRuns.seq hinv14
                                    (InvariantRuns.seq hinv15
                                      hinv16)))))))))))))))
  obtain ⟨totalSteps, hinvProgramNumeric⟩ :=
    hprogramNumericExists
  have hinvProgramBit :
      InvariantRuns
        (ValuesWithin regs.footprint width)
        (program Q workTapeCount regs) store store17 totalSteps := by
    apply invariantRuns_mono_internal
      (firstInvariant :=
        NeighborhoodProgram.ValuesWithin regs.footprint cap)
      (secondInvariant := ValuesWithin regs.footprint width)
      (fun current hcurrent => by
        exact
          (numericWithin_cap_iff_internal
            regs.footprint width current).mp
            (by simpa [cap] using hcurrent))
    exact hinvProgramNumeric
  obtain ⟨semanticFinal, hsemanticRun, hpost⟩ :=
    program_runs_internal Q workTapeCount regs store candidate
      hcandidate
  have hfinalEq : store17 = semanticFinal :=
    runs_final_eq_internal
      (InvariantRuns.toRuns hinvProgramBit) hsemanticRun
  refine ⟨store17, totalSteps, ?_, hfinalEq.symm ▸ hpost⟩
  simpa [width, valueWidth] using hinvProgramBit

theorem program_writesWithin_internal
    (Q : Type*) [Fintype Q] (workTapeCount : ℕ)
    (regs : Registers) :
    RegisterStore.DenseOverlay.FixedRegisters.Footprint.ProgramWritesWithin
      (program Q workTapeCount regs).compile regs.footprint := by
  exact RAM.Structured.Footprint.programWritesWithin_compile
    (program_sourceWritesWithin_internal Q workTapeCount regs)

theorem program_noStore_internal
    (Q : Type*) [Fintype Q] (workTapeCount : ℕ)
    (regs : Registers) :
    NeighborhoodProgram.cmdNoStore
      (program Q workTapeCount regs) := by
  exact cmdNoStore_of_writesWithin_internal regs.footprint _
    (program_sourceWritesWithin_internal Q workTapeCount regs)

end Internal

end CandidateParameters

end Runtime

end TimeSpaceSimulation

end Complexity
