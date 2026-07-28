/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.Runtime.InputLookup
import Complexitylib.TimeSpaceSimulation.Runtime.PrimeSearchInvariant
import Complexitylib.TimeSpaceSimulation.Runtime.SearchProgram

/-!
# Concrete outer-search resource envelopes -- proof internals
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace Runtime

namespace SearchEnvelope

open RAM Structured

namespace Internal

private def ExecListInvariant
    (invariant : Store → Prop) : List Basic → Store → Prop
  | [], store => invariant store
  | op :: rest, store =>
      invariant store ∧
        ExecListInvariant invariant rest (Basic.exec op store)

private theorem execListInvariant_initial
    {invariant : Store → Prop} {ops : List Basic} {store : Store}
    (hinvariant : ExecListInvariant invariant ops store) :
    invariant store := by
  cases ops with
  | nil =>
      exact hinvariant
  | cons op rest =>
      exact hinvariant.1

private theorem execListInvariant_final
    {invariant : Store → Prop} {ops : List Basic} {store : Store}
    (hinvariant : ExecListInvariant invariant ops store) :
    invariant (Basic.execList ops store) := by
  induction ops generalizing store with
  | nil =>
      exact hinvariant
  | cons op rest ih =>
      exact ih hinvariant.2

private theorem execListInvariant_append
    {invariant : Store → Prop}
    (first second : List Basic) (store : Store) :
    ExecListInvariant invariant (first ++ second) store ↔
      ExecListInvariant invariant first store ∧
        ExecListInvariant invariant second
          (Basic.execList first store) := by
  induction first generalizing store with
  | nil =>
      constructor
      · intro hsecond
        exact ⟨execListInvariant_initial hsecond, hsecond⟩
      · exact fun hboth => hboth.2
  | cons op rest ih =>
      simp only [List.cons_append, ExecListInvariant, Basic.execList]
      rw [ih (Basic.exec op store)]
      constructor
      · rintro ⟨hstore, hrest, hsecond⟩
        exact ⟨⟨hstore, hrest⟩, hsecond⟩
      · rintro ⟨⟨hstore, hrest⟩, hsecond⟩
        exact ⟨hstore, hrest, hsecond⟩

private theorem invariantRuns_basics
    {invariant : Store → Prop}
    (ops : List Basic) (store : Store)
    (hinvariant : ExecListInvariant invariant ops store) :
    ∃ steps,
      InvariantRuns invariant (Cmd.basics ops) store
        (Basic.execList ops store) steps := by
  induction ops generalizing store with
  | nil =>
      exact ⟨0, InvariantRuns.skip store hinvariant⟩
  | cons op rest ih =>
      cases rest with
      | nil =>
          exact ⟨1,
            InvariantRuns.basic op store
              hinvariant.1 hinvariant.2⟩
      | cons next tail =>
          obtain ⟨steps, hrest⟩ :=
            ih (Basic.exec op store) hinvariant.2
          exact ⟨1 + steps,
            InvariantRuns.seq
              (InvariantRuns.basic op store hinvariant.1
                (execListInvariant_initial hinvariant.2))
              hrest⟩

private theorem initRegs_bitlen_le
    (input : List Bool) (valueBits : ℕ)
    (hone : 1 ≤ valueBits)
    (hinput : bitlen input.length ≤ valueBits)
    (address : ℕ) :
    bitlen (RAM.initRegs input address) ≤ valueBits := by
  by_cases hzero : address = 0
  · subst address
    simpa [RAM.initRegs] using hinput
  · have hpositive : 0 < address := by
      omega
    have hvalue :=
      InputLookup.initRegs_lt_two_of_pos input hpositive
    apply le_trans (show bitlen (RAM.initRegs input address) ≤ 1 by
      rw [bitlen, Nat.size_le]
      simpa using hvalue)
    exact hone

private theorem initRegs_mutableValuesWithin
    (allowed : Finset ℕ) (input : List Bool) (valueBits : ℕ)
    (hone : 1 ≤ valueBits)
    (hinput : bitlen input.length ≤ valueBits) :
    SearchProgram.MutableValuesWithin allowed valueBits
      (RAM.initRegs input) := by
  intro address _
  exact initRegs_bitlen_le input valueBits hone hinput address

private theorem cacheOps_execListInvariant
    (regs : SearchProgram.Registers)
    (allowed : Finset ℕ) (input : List Bool)
    (limit valueBits : ℕ)
    (hpositive : 0 < limit)
    (hone : 1 ≤ valueBits)
    (hinput : bitlen input.length ≤ valueBits)
    (hlimit : limit ≤ valueBits) :
    ExecListInvariant
      (SearchProgram.MutableValuesWithin allowed valueBits)
      (SearchProgram.cacheInputPrefixOps regs limit)
      (RAM.initRegs input) := by
  induction limit with
  | zero =>
      omega
  | succ limit ih =>
      have hinitial :=
        initRegs_mutableValuesWithin
          allowed input valueBits hone hinput
      by_cases hzero : limit = 0
      · subst limit
        have hafter :
            SearchProgram.MutableValuesWithin allowed valueBits
              (Basic.exec
                (.mul regs.prefixCache regs.prefixCache
                  regs.prefixCache)
                (RAM.initRegs input)) := by
          intro address haddress
          by_cases heq : address = regs.prefixCache
          · subst address
            simp only [Basic.exec, Function.update_self]
            have hcachePositive :
                0 < regs.prefixCache := by
              change 0 < regs.index 16
              rw [regs.prefixCache_one]
              omega
            have hcache :=
              InputLookup.initRegs_lt_two_of_pos
                input hcachePositive
            have hcacheCases :
                RAM.initRegs input regs.prefixCache = 0 ∨
                  RAM.initRegs input regs.prefixCache = 1 := by
              omega
            have hproduct :
                RAM.initRegs input regs.prefixCache *
                    RAM.initRegs input regs.prefixCache <
                  2 := by
              rcases hcacheCases with hcacheZero | hcacheOne
              · simp [hcacheZero]
              · simp [hcacheOne]
            apply le_trans
              (show bitlen
                  (RAM.initRegs input regs.prefixCache *
                    RAM.initRegs input regs.prefixCache) ≤ 1 by
                rw [bitlen, Nat.size_le]
                simpa using hproduct)
            exact hone
          · simpa [Basic.exec, Function.update_of_ne heq] using
              hinitial address haddress
        have hlist :
            ExecListInvariant
              (SearchProgram.MutableValuesWithin
                allowed valueBits)
              [.mul regs.prefixCache regs.prefixCache
                regs.prefixCache]
              (RAM.initRegs input) :=
          ⟨hinitial, hafter⟩
        simpa [SearchProgram.cacheInputPrefixOps] using hlist
      · have hlimitPositive : 0 < limit := by
          omega
        have hlimitLe : limit ≤ valueBits := by
          omega
        have hold :=
          ih hlimitPositive hlimitLe
        let oldStore :=
          Basic.execList
            (SearchProgram.cacheInputPrefixOps regs limit)
            (RAM.initRegs input)
        let doubled :=
          Basic.exec
            (.add regs.prefixCache regs.prefixCache
              regs.prefixCache)
            oldStore
        let next :=
          Basic.exec
            (.add regs.prefixCache regs.prefixCache (limit + 1))
            doubled
        have holdFinal :
            SearchProgram.MutableValuesWithin allowed valueBits
              oldStore := by
          exact execListInvariant_final hold
        have holdCache :
            oldStore regs.prefixCache =
              InputLookup.packedPrefix input limit := by
          simpa [oldStore, SearchProgram.prefixCacheValue] using
            InputLookup.prefixCacheValue_eq_packedPrefix
              regs input limit hlimitPositive
        have hdouble :
            SearchProgram.MutableValuesWithin allowed valueBits
              doubled := by
          intro address haddress
          by_cases heq : address = regs.prefixCache
          · subst address
            have hword :=
              InputLookup.packedPrefix_lt_pow input limit
            have htwice :
                InputLookup.packedPrefix input limit +
                    InputLookup.packedPrefix input limit <
                  2 ^ (limit + 1) := by
              rw [pow_succ]
              omega
            have hsize :
                bitlen
                    (InputLookup.packedPrefix input limit +
                      InputLookup.packedPrefix input limit) ≤
                  limit + 1 := by
              rw [bitlen, Nat.size_le]
              exact htwice
            simpa [doubled, Basic.exec, holdCache] using
              hsize.trans hlimit
          · simpa [doubled, Basic.exec,
              Function.update_of_ne heq] using
              holdFinal address haddress
        have haddressNe :
            limit + 1 ≠ regs.prefixCache := by
          change limit + 1 ≠ regs.index 16
          rw [regs.prefixCache_one]
          omega
        have holdAddress :
            oldStore (limit + 1) =
              RAM.initRegs input (limit + 1) := by
          simpa [oldStore] using
            InputLookup.prefixCacheOps_eq_outside
              regs input limit haddressNe
        have hpush :
            InputLookup.packedPrefix input (limit + 1) =
              Runtime.PackedDigits.push 2
                (RAM.initRegs input (limit + 1))
                (InputLookup.packedPrefix input limit) := by
          simp [InputLookup.packedPrefix, List.range_succ]
        have hnextCache :
            next regs.prefixCache =
              InputLookup.packedPrefix input (limit + 1) := by
          simp [next, doubled, Basic.exec, haddressNe,
            holdCache, holdAddress, hpush,
            Runtime.PackedDigits.push]
          omega
        have hnext :
            SearchProgram.MutableValuesWithin allowed valueBits
              next := by
          intro address haddress
          by_cases heq : address = regs.prefixCache
          · subst address
            rw [hnextCache]
            apply le_trans
              (show bitlen
                  (InputLookup.packedPrefix input (limit + 1)) ≤
                    limit + 1 by
                rw [bitlen, Nat.size_le]
                exact InputLookup.packedPrefix_lt_pow
                  input (limit + 1))
            exact hlimit
          · simpa [next, Basic.exec,
              Function.update_of_ne heq] using
              hdouble address haddress
        have htail :
            ExecListInvariant
              (SearchProgram.MutableValuesWithin
                allowed valueBits)
              [.add regs.prefixCache regs.prefixCache
                  regs.prefixCache,
                .add regs.prefixCache regs.prefixCache (limit + 1)]
              oldStore :=
          ⟨holdFinal, hdouble, hnext⟩
        rw [InputLookup.cacheInputPrefixOps_succ
          regs limit hlimitPositive]
        exact
          (execListInvariant_append
            (SearchProgram.cacheInputPrefixOps regs limit)
            [.add regs.prefixCache regs.prefixCache
                regs.prefixCache,
              .add regs.prefixCache regs.prefixCache (limit + 1)]
            (RAM.initRegs input)).2
            ⟨hold, htail⟩

theorem cacheInvariantRuns_internal
    (regs : SearchProgram.Registers)
    (kernel : SearchProgram.TrialKernel regs)
    (input : List Bool) (valueBits : ℕ)
    (hone : 1 ≤ valueBits)
    (hinput : bitlen input.length ≤ valueBits)
    (hlimit :
      SearchProgram.footprintLimit regs kernel.footprint ≤
        valueBits) :
    ∃ cached steps,
      InvariantRuns
        (SearchProgram.MutableValuesWithin
          (regs.footprint ∪ kernel.footprint) valueBits)
        (SearchProgram.cacheInputPrefix regs
          (SearchProgram.footprintLimit regs kernel.footprint))
        (RAM.initRegs input) cached steps ∧
      SearchProgram.InputFrame
        regs kernel.footprint input cached := by
  let allowed := regs.footprint ∪ kernel.footprint
  let limit :=
    SearchProgram.footprintLimit regs kernel.footprint
  let cached :=
    Basic.execList
      (SearchProgram.cacheInputPrefixOps regs limit)
      (RAM.initRegs input)
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
  have hlist :
      ExecListInvariant
        (SearchProgram.MutableValuesWithin allowed valueBits)
        (SearchProgram.cacheInputPrefixOps regs limit)
        (RAM.initRegs input) := by
    apply cacheOps_execListInvariant
    · exact hlimitPositive
    · exact hone
    · exact hinput
    · exact hlimit
  obtain ⟨steps, hinvariant⟩ :=
    invariantRuns_basics
      (SearchProgram.cacheInputPrefixOps regs limit)
      (RAM.initRegs input) hlist
  have hframe :
      SearchProgram.InputFrame
        regs kernel.footprint input cached := by
    simpa [limit, cached] using
      (SearchProgram.cacheInputPrefix_runs_inputFrame
        regs kernel input).2
  exact ⟨cached, steps, by
    simpa [SearchProgram.cacheInputPrefix, allowed,
      limit, cached] using hinvariant, hframe⟩

theorem prefixEnvelopeOfBounds_internal
    (regs : SearchProgram.Registers)
    (kernel : SearchProgram.TrialKernel regs)
    (input : List Bool) (target valueBits : ℕ)
    (hinput : bitlen input.length ≤ valueBits)
    (hlimit :
      SearchProgram.footprintLimit regs kernel.footprint ≤
        valueBits)
    (htarget : bitlen target + 2 ≤ valueBits)
    (hguessCount :
      ∀ candidate,
        input.length ≤ candidate →
        candidate ≤ target →
        bitlen (kernel.guessCount candidate) ≤ valueBits)
    (hkernelPrefix :
      ∀ candidate,
        input.length ≤ candidate →
        candidate ≤ target →
        ∀ prime guess,
          guess < kernel.guessCount candidate →
          kernel.prefixValueBits input candidate prime guess ≤
            valueBits) :
    SearchProgram.PrefixEnvelope
      regs kernel input target valueBits := by
  have hone : 1 ≤ valueBits := by omega
  have htargetBitlen : bitlen target ≤ valueBits := by omega
  refine
    { one_le := hone
      target_bitlen := htargetBitlen
      cacheInvariantRuns := ?_
      primeSearchInvariantRuns := ?_
      guessCount_bitlen := hguessCount
      kernelPrefix_le := hkernelPrefix }
  · exact cacheInvariantRuns_internal regs kernel input valueBits
      hone hinput hlimit
  · exact
      PrimeSearchInvariant.prefixEnvelopePrimeSearchInvariantRuns
        regs kernel input target valueBits htarget

end Internal

end SearchEnvelope

end Runtime

end TimeSpaceSimulation

end Complexity
