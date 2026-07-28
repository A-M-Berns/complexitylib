/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.PrimeSearchInvariant.Internal

/-!
# All-prefix invariants for fixed-register prime search

The theorems in this module certify every structured source-program point of
the subtraction-based primality test and upward prime search.  The invariant
is phrased over an arbitrary larger mutable store, so the result composes
directly with the Williams outer controller.
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace Runtime

namespace PrimeSearchInvariant

open RAM Structured

/-- Fixed-register primality preserves an arbitrary larger mutable-word
bound at every source-program point.  `bound` may be larger than the tested
candidate, which is useful while an outer search streams candidates upward. -/
theorem primalityInvariantRuns
    (regs : PrimeSearch.Registers)
    (allowed : Finset ℕ) (valueBits bound candidate : ℕ)
    (hfootprint : footprint regs ⊆ allowed)
    (hbound : bitlen bound ≤ valueBits)
    (hboundPos : 0 < bound)
    (hcandidateBound : candidate ≤ bound)
    (store : Store)
    (hcandidate : store regs.candidate = candidate)
    (hstore :
      SearchProgram.MutableValuesWithin allowed valueBits store) :
    ∃ final steps,
      InvariantRuns
        (SearchProgram.MutableValuesWithin allowed valueBits)
        (PrimeSearch.primality regs) store final steps ∧
      PrimeSearch.PrimalityPost regs candidate final :=
  Internal.primalityInvariantRuns_internal regs allowed valueBits
    bound candidate hfootprint hbound hboundPos hcandidateBound
    store hcandidate hstore

/-- Upward prime search preserves an arbitrary larger mutable-word bound at
every source-program point.  Two extra bits uniformly cover the small lower
bound zero as well as the positive cases supplied by Bertrand's postulate. -/
theorem searchInvariantRuns
    (regs : PrimeSearch.Registers)
    (allowed : Finset ℕ) (valueBits lower : ℕ)
    (hfootprint : footprint regs ⊆ allowed)
    (hwidth : bitlen lower + 2 ≤ valueBits)
    (store : Store)
    (hlower : store regs.candidate = lower)
    (hstore :
      SearchProgram.MutableValuesWithin allowed valueBits store) :
    ∃ final steps,
      InvariantRuns
        (SearchProgram.MutableValuesWithin allowed valueBits)
        (PrimeSearch.search regs) store final steps ∧
      PrimeSearch.SearchPost regs lower final :=
  Internal.searchInvariantRuns_internal regs allowed valueBits lower
    hfootprint hwidth store hlower hstore

/-- The embedded prime-search allocation lies in the controller's common
mutable footprint. -/
theorem controllerPrimeFootprint_subset
    (regs : SearchProgram.Registers)
    (kernel : SearchProgram.TrialKernel regs) :
    footprint regs.primeRegisters ⊆
      regs.footprint ∪ kernel.footprint := by
  intro address haddress
  obtain ⟨slot, _, rfl⟩ := Finset.mem_image.mp haddress
  exact Finset.mem_union_left _
    (SearchProgram.Registers.index_mem_footprint regs
      (SearchProgram.Registers.primeSlot slot))

/-- Adapter discharging the `PrefixEnvelope` prime-search field for every
candidate in a bounded interval, including candidates zero and one. -/
theorem prefixEnvelopePrimeSearchInvariantRuns
    (regs : SearchProgram.Registers)
    (kernel : SearchProgram.TrialKernel regs)
    (input : List Bool) (target valueBits : ℕ)
    (hwidth : bitlen target + 2 ≤ valueBits) :
    ∀ candidate store,
      input.length ≤ candidate →
      candidate ≤ target →
      store regs.prime = candidate →
      SearchProgram.MutableValuesWithin
        (regs.footprint ∪ kernel.footprint) valueBits store →
      ∃ final steps,
        InvariantRuns
          (SearchProgram.MutableValuesWithin
            (regs.footprint ∪ kernel.footprint) valueBits)
          (PrimeSearch.search regs.primeRegisters)
          store final steps ∧
        PrimeSearch.SearchPost
          regs.primeRegisters candidate final := by
  intro candidate store hlower hupper hcandidate hstore
  have hcandidateWidth :
      bitlen candidate + 2 ≤ valueBits := by
    apply le_trans _ hwidth
    exact Nat.add_le_add_right
      (by simpa [bitlen] using Nat.size_le_size hupper) 2
  exact searchInvariantRuns regs.primeRegisters
    (regs.footprint ∪ kernel.footprint) valueBits candidate
    (controllerPrimeFootprint_subset regs kernel)
    hcandidateWidth store hcandidate hstore

end PrimeSearchInvariant

end Runtime

end TimeSpaceSimulation

end Complexity
