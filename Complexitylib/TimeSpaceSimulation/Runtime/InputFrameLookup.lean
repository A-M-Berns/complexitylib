/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.Runtime.InputLookup
import Complexitylib.TimeSpaceSimulation.Runtime.SearchProgram

/-!
# Collision-safe lookup from a search-controller input frame

This module bridges the search controller's packed-prefix `InputFrame` to the
generic collision-safe `InputLookup` command. It derives the lookup register
bound and positive cache limit from the shared fixed footprint, then proves
that lookup preserves the same input frame.
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace Runtime

namespace InputFrameLookup

open RAM Structured
open NeighborhoodProgram

/-- Run one positive public-input lookup from a valid search-controller input
frame.

Every bank register must lie in the combined controller/kernel footprint, and
the bank word must be the controller's prefix-cache register. These two
allocation facts are enough to derive the register bound required by
`InputLookup.runs`; no separate numeric limit premise is needed. -/
theorem runs
    (regs : SearchProgram.Registers)
    (kernelFootprint : Finset ℕ)
    (bank : BankRegisters)
    (input : List Bool) (queried : ℕ) (store : Store)
    (hframe :
      SearchProgram.InputFrame regs kernelFootprint input store)
    (hbank :
      bank.footprint ⊆ regs.footprint ∪ kernelFootprint)
    (hword : bank.word = regs.prefixCache)
    (hpositive : 0 < queried)
    (haddress :
      store (InputLookup.address bank) = queried)
    (hone : store bank.one = 1) :
    ∃ final,
      Runs
        (InputLookup.command bank
          (SearchProgram.footprintLimit regs kernelFootprint))
        store final ∧
      InputLookup.Post bank input queried store final ∧
      SearchProgram.InputFrame
        regs kernelFootprint input final := by
  let allowed := regs.footprint ∪ kernelFootprint
  let limit := SearchProgram.footprintLimit regs kernelFootprint
  have hregisters : ∀ slot, bank.index slot ≤ limit := by
    intro slot
    change bank.index slot ≤
      allowed.sup (fun address : ℕ => address)
    exact Finset.le_sup
      (f := fun address : ℕ => address)
      (hbank (bank.index_mem_footprint slot))
  have hcacheMem : regs.prefixCache ∈ allowed :=
    Finset.mem_union_left _
      (regs.index_mem_footprint 16)
  have hlimitPositive : 0 < limit := by
    have hcacheLe :
        regs.prefixCache ≤
          allowed.sup (fun address : ℕ => address) :=
      Finset.le_sup
        (f := fun address : ℕ => address) hcacheMem
    have hcacheOne : regs.prefixCache = 1 :=
      regs.prefixCache_one
    change 0 < allowed.sup (fun address : ℕ => address)
    omega
  have hprefix :
      InputLookup.CachedPrefixRepresents input limit
        (SearchProgram.prefixCacheValue regs input limit) :=
    InputLookup.prefixCacheValue_represents
      regs input limit hlimitPositive
  have hstoreWord :
      store bank.word =
        SearchProgram.prefixCacheValue regs input limit := by
    rw [hword]
    exact hframe.1
  obtain ⟨final, hrun, hpost⟩ :=
    InputLookup.runs bank input limit queried
      (SearchProgram.prefixCacheValue regs input limit) store
      hpositive hregisters hprefix hframe.2 hstoreWord
      haddress hone
  refine ⟨final, hrun, hpost, ?_⟩
  constructor
  · calc
      final regs.prefixCache = final bank.word :=
        congrArg final hword.symm
      _ = store bank.word := hpost.word_eq
      _ = store regs.prefixCache := congrArg store hword
      _ = SearchProgram.prefixCacheValue regs input limit :=
        hframe.1
  · intro address houtside
    have hnotAllowed : address ∉ allowed := by
      intro hmember
      have hle :
          address ≤
            allowed.sup (fun candidate : ℕ => candidate) :=
        Finset.le_sup
          (f := fun candidate : ℕ => candidate) hmember
      exact (Nat.not_lt_of_ge hle) houtside
    have hnotBank : address ∉ bank.footprint :=
      fun hmember => hnotAllowed (hbank hmember)
    calc
      final address = store address :=
        RAM.Structured.Footprint.runs_eq_outside
          (InputLookup.sourceWritesWithin bank limit)
          hrun hnotBank
      _ = RAM.initRegs input address :=
        hframe.2 address houtside

end InputFrameLookup

end Runtime

end TimeSpaceSimulation

end Complexity
