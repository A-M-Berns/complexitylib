/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.Models.RandomAccessMachine.Structured.Footprint
import Complexitylib.TimeSpaceSimulation.Runtime.InputLookup.Defs
import Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodProgram

/-!
# Collision-safe public-input lookup internals
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace Runtime

namespace InputLookup

open RAM Structured
open NeighborhoodProgram

namespace Internal

theorem initRegs_lt_two_of_pos_internal
    (input : List Bool) {address : ℕ}
    (hpositive : 0 < address) :
    RAM.initRegs input address < 2 := by
  rw [RAM.initRegs, if_neg (by omega)]
  cases hbit : input[address - 1]? with
  | none =>
      simp
  | some bit =>
      cases bit <;> simp

theorem packedPrefix_represents_internal
    (input : List Bool) (limit : ℕ) :
    CachedPrefixRepresents input limit
      (packedPrefix input limit) := by
  induction limit with
  | zero =>
      intro address hpositive haddress
      omega
  | succ limit ih =>
      intro address hpositive haddress
      have hpush :
          packedPrefix input (limit + 1) =
            PackedDigits.push 2 (RAM.initRegs input (limit + 1))
              (packedPrefix input limit) := by
        simp [packedPrefix, List.range_succ]
      rw [hpush]
      by_cases htop : address = limit + 1
      · subst address
        simpa only [Nat.sub_self] using PackedDigits.digit_push_zero
          (initRegs_lt_two_of_pos_internal input (by omega))
      · have hlower : address ≤ limit := by
          omega
        have hshift :
            limit + 1 - address = (limit - address) + 1 := by
          omega
        rw [hshift, PackedDigits.digit_push_succ
          (by omega)
          (initRegs_lt_two_of_pos_internal input (by omega))]
        exact ih address hpositive hlower

theorem packedPrefix_lt_pow_internal
    (input : List Bool) (limit : ℕ) :
    packedPrefix input limit < 2 ^ limit := by
  induction limit with
  | zero =>
      simp [packedPrefix]
  | succ limit ih =>
      have hpush :
          packedPrefix input (limit + 1) =
            PackedDigits.push 2 (RAM.initRegs input (limit + 1))
              (packedPrefix input limit) := by
        simp [packedPrefix, List.range_succ]
      rw [hpush]
      exact PackedDigits.push_lt_pow ih
        (initRegs_lt_two_of_pos_internal input (by omega))

private theorem execList_append
    (first second : List Basic) (store : Store) :
    Basic.execList (first ++ second) store =
      Basic.execList second (Basic.execList first store) := by
  induction first generalizing store with
  | nil =>
      rfl
  | cons op rest ih =>
      simp only [List.cons_append, Basic.execList]
      exact ih (Basic.exec op store)

private theorem execList_eq_outside
    {allowed : Finset ℕ} (ops : List Basic) (store : Store)
    (hwrites : ∀ op ∈ ops,
      RAM.Structured.Footprint.BasicWritesWithin allowed op)
    {address : ℕ} (haddress : address ∉ allowed) :
    Basic.execList ops store address = store address := by
  induction ops generalizing store with
  | nil =>
      rfl
  | cons op rest ih =>
      have hop := hwrites op (by simp)
      have hrest :
          ∀ candidate ∈ rest,
            RAM.Structured.Footprint.BasicWritesWithin
              allowed candidate := by
        intro candidate hcandidate
        exact hwrites candidate (by simp [hcandidate])
      rw [Basic.execList, ih (Basic.exec op store) hrest]
      cases op <;>
        simp only [RAM.Structured.Footprint.BasicWritesWithin] at hop
      all_goals
        simp only [Basic.exec]
        rw [Function.update_of_ne]
        exact fun heq => haddress (heq ▸ hop)

private theorem cacheInputPrefixOps_writesWithin
    (regs : SearchProgram.Registers) (limit : ℕ) :
    ∀ op ∈ SearchProgram.cacheInputPrefixOps regs limit,
      RAM.Structured.Footprint.BasicWritesWithin
        {regs.prefixCache} op := by
  intro op hop
  simp only [SearchProgram.cacheInputPrefixOps, List.mem_cons,
    List.mem_flatMap] at hop
  rcases hop with hop | ⟨offset, _hoffset, hop⟩
  · subst op
    simp [RAM.Structured.Footprint.BasicWritesWithin]
  · rcases hop with rfl | hop
    · simp [RAM.Structured.Footprint.BasicWritesWithin]
    · rcases hop with rfl | hop
      · simp [RAM.Structured.Footprint.BasicWritesWithin]
      · simp at hop

theorem prefixCacheOps_eq_outside_internal
    (regs : SearchProgram.Registers) (input : List Bool)
    (limit : ℕ) {address : ℕ}
    (haddress : address ≠ regs.prefixCache) :
    Basic.execList
        (SearchProgram.cacheInputPrefixOps regs limit)
        (RAM.initRegs input) address =
      RAM.initRegs input address := by
  apply execList_eq_outside
    (SearchProgram.cacheInputPrefixOps regs limit)
    (RAM.initRegs input)
    (cacheInputPrefixOps_writesWithin regs limit)
  simpa only [Finset.mem_singleton] using haddress

theorem cacheInputPrefixOps_succ_internal
    (regs : SearchProgram.Registers) (limit : ℕ)
    (hpositive : 0 < limit) :
    SearchProgram.cacheInputPrefixOps regs (limit + 1) =
      SearchProgram.cacheInputPrefixOps regs limit ++
        [.add regs.prefixCache regs.prefixCache regs.prefixCache,
          .add regs.prefixCache regs.prefixCache (limit + 1)] := by
  cases limit with
  | zero =>
      omega
  | succ pred =>
      simp [SearchProgram.cacheInputPrefixOps, List.range_succ]

theorem prefixCacheValue_eq_packedPrefix_internal
    (regs : SearchProgram.Registers) (input : List Bool)
    (limit : ℕ) (hpositive : 0 < limit) :
    SearchProgram.prefixCacheValue regs input limit =
      packedPrefix input limit := by
  induction limit with
  | zero =>
      omega
  | succ limit ih =>
      by_cases hzero : limit = 0
      · subst limit
        simp [SearchProgram.prefixCacheValue,
          SearchProgram.cacheInputPrefixOps, packedPrefix,
          Basic.execList, Basic.exec, regs.prefixCache_one,
          RAM.initRegs, PackedDigits.push]
        cases hbit : input[0]? with
        | none =>
            simp
        | some bit =>
            cases bit <;> simp
      · have hlimitPositive : 0 < limit := by
          omega
        have hpreviousCache :
            SearchProgram.prefixCacheValue regs input limit =
              packedPrefix input limit :=
          ih hlimitPositive
        have hpreviousAddress :
            Basic.execList
                (SearchProgram.cacheInputPrefixOps regs limit)
                (RAM.initRegs input) (limit + 1) =
              RAM.initRegs input (limit + 1) := by
          apply execList_eq_outside
            (SearchProgram.cacheInputPrefixOps regs limit)
            (RAM.initRegs input)
            (cacheInputPrefixOps_writesWithin regs limit)
          simp only [Finset.mem_singleton,
            regs.prefixCache_one]
          omega
        have hpush :
            packedPrefix input (limit + 1) =
              PackedDigits.push 2
                (RAM.initRegs input (limit + 1))
                (packedPrefix input limit) := by
          simp [packedPrefix, List.range_succ]
        rw [SearchProgram.prefixCacheValue,
          cacheInputPrefixOps_succ_internal
            regs limit hlimitPositive,
          execList_append, hpush]
        simp only [Basic.execList, Basic.exec]
        have haddressNe :
            limit + 1 ≠ regs.prefixCache := by
          change limit + 1 ≠ regs.index 16
          rw [regs.prefixCache_one]
          omega
        simp [haddressNe]
        have hcache :
            Basic.execList
                (SearchProgram.cacheInputPrefixOps regs limit)
                (RAM.initRegs input) regs.prefixCache =
              packedPrefix input limit := by
          simpa only [SearchProgram.prefixCacheValue] using
            hpreviousCache
        rw [hcache, hpreviousAddress]
        simp only [PackedDigits.push]
        omega

theorem prefixCacheValue_represents_internal
    (regs : SearchProgram.Registers) (input : List Bool)
    (limit : ℕ) (hpositive : 0 < limit) :
    CachedPrefixRepresents input limit
      (SearchProgram.prefixCacheValue regs input limit) := by
  rw [prefixCacheValue_eq_packedPrefix_internal
    regs input limit hpositive]
  exact packedPrefix_represents_internal input limit

theorem sourceWritesWithin_internal
    (regs : BankRegisters) (limit : ℕ) :
    RAM.Structured.Footprint.CmdWritesWithin
      regs.footprint (command regs limit) := by
  simp only [command, RAM.Structured.Footprint.CmdWritesWithin,
    RAM.Structured.Footprint.BasicWritesWithin]
  constructor
  · exact regs.index_mem_footprint 10
  constructor
  · exact regs.index_mem_footprint 5
  constructor
  · exact regs.index_mem_footprint 10
  · constructor
    · exact regs.index_mem_footprint 8
    constructor
    · exact regs.index_mem_footprint 8
    constructor
    · exact regs.index_mem_footprint 2
    constructor
    · exact regs.index_mem_footprint 3
    · exact bankRead_sourceWritesWithin regs

theorem runs_internal
    (regs : BankRegisters) (input : List Bool)
    (limit address word : ℕ) (store : Store)
    (hpositive : 0 < address)
    (hregisters : ∀ slot, regs.index slot ≤ limit)
    (hprefix : CachedPrefixRepresents input limit word)
    (hsuffix : ∀ queried, limit < queried →
      store queried = RAM.initRegs input queried)
    (hword : store regs.word = word)
    (haddress : store (InputLookup.address regs) = address)
    (hone : store regs.one = 1) :
    ∃ final,
      Runs (command regs limit) store final ∧
      Post regs input address store final := by
  let afterLimit :=
    Basic.exec (.imm regs.result (limit + 1)) store
  let afterTest :=
    Basic.exec
      (.sub regs.test regs.result (InputLookup.address regs))
      afterLimit
  have hlimitRun :
      Runs (.basic (.imm regs.result (limit + 1)))
        store afterLimit := by
    exact Runs.basic _ _
  have htestRun :
      Runs (.basic
        (.sub regs.test regs.result
          (InputLookup.address regs)))
        afterLimit afterTest := by
    exact Runs.basic _ _
  have hprelude :
      Runs
        (.seq (.basic (.imm regs.result (limit + 1)))
          (.basic
            (.sub regs.test regs.result
              (InputLookup.address regs))))
        store afterTest :=
    Runs.seq hlimitRun htestRun
  by_cases hcached : address ≤ limit
  · have htest : afterTest regs.test ≠ 0 := by
      simp [afterTest, afterLimit, Basic.exec,
        InputLookup.address, regs.index_ne
          (by decide : (11 : Fin 12) ≠ 10), haddress]
      omega
    let afterIndexInit :=
      Basic.exec (.imm regs.indexCount limit) afterTest
    let afterIndex :=
      Basic.exec
        (.sub regs.indexCount regs.indexCount
          (InputLookup.address regs))
        afterIndexInit
    let afterBase :=
      Basic.exec (.imm regs.base 2) afterIndex
    let ready :=
      Basic.exec (.imm regs.basePred 1) afterBase
    have hindexInitRun :
        Runs (.basic (.imm regs.indexCount limit))
          afterTest afterIndexInit := by
      exact Runs.basic _ _
    have hindexRun :
        Runs (.basic
          (.sub regs.indexCount regs.indexCount
            (InputLookup.address regs)))
          afterIndexInit afterIndex := by
      exact Runs.basic _ _
    have hbaseRun :
        Runs (.basic (.imm regs.base 2))
          afterIndex afterBase := by
      exact Runs.basic _ _
    have hbasePredRun :
        Runs (.basic (.imm regs.basePred 1))
          afterBase ready := by
      exact Runs.basic _ _
    have hreadyWord : ready regs.word = word := by
      simp [ready, afterBase, afterIndex, afterIndexInit,
        afterTest, afterLimit, Basic.exec,
        regs.index_ne (by decide : (0 : Fin 12) ≠ 3),
        regs.index_ne (by decide : (0 : Fin 12) ≠ 2),
        regs.index_ne (by decide : (0 : Fin 12) ≠ 8),
        regs.index_ne (by decide : (0 : Fin 12) ≠ 5),
        regs.index_ne (by decide : (0 : Fin 12) ≠ 10),
        hword]
    have hreadyBase : ready regs.base = 2 := by
      simp [ready, afterBase, Basic.exec,
        regs.index_ne (by decide : (2 : Fin 12) ≠ 3)]
    have hreadyBasePred : ready regs.basePred = 1 := by
      simp [ready, Basic.exec]
    have hreadyOne : ready regs.one = 1 := by
      simp [ready, afterBase, afterIndex, afterIndexInit,
        afterTest, afterLimit, Basic.exec,
        regs.index_ne (by decide : (6 : Fin 12) ≠ 3),
        regs.index_ne (by decide : (6 : Fin 12) ≠ 2),
        regs.index_ne (by decide : (6 : Fin 12) ≠ 8),
        regs.index_ne (by decide : (6 : Fin 12) ≠ 5),
        regs.index_ne (by decide : (6 : Fin 12) ≠ 10),
        hone]
    have hreadyIndex :
        ready regs.indexCount = limit - address := by
      simp [ready, afterBase, afterIndex, afterIndexInit,
        afterTest, afterLimit, Basic.exec,
        InputLookup.address,
        regs.index_ne (by decide : (8 : Fin 12) ≠ 3),
        regs.index_ne (by decide : (8 : Fin 12) ≠ 2),
        regs.index_ne (by decide : (11 : Fin 12) ≠ 8),
        regs.index_ne (by decide : (11 : Fin 12) ≠ 5),
        regs.index_ne (by decide : (11 : Fin 12) ≠ 10),
        haddress]
    have hreadyAddress :
        ready (InputLookup.address regs) = address := by
      simp [ready, afterBase, afterIndex, afterIndexInit,
        afterTest, afterLimit, Basic.exec,
        InputLookup.address,
        regs.index_ne (by decide : (11 : Fin 12) ≠ 3),
        regs.index_ne (by decide : (11 : Fin 12) ≠ 2),
        regs.index_ne (by decide : (11 : Fin 12) ≠ 8),
        regs.index_ne (by decide : (11 : Fin 12) ≠ 5),
        regs.index_ne (by decide : (11 : Fin 12) ≠ 10),
        haddress]
    obtain ⟨final, hbank, hfinalWord, _hbuffer,
        _hindex, _hcompleted, hresult, _hbase,
        _hbasePred, hfinalOne, hfinalAddress⟩ :=
      bankRead_runs regs ready 2 word (limit - address)
        (by omega) hreadyWord hreadyBase hreadyBasePred
        hreadyOne hreadyIndex
    have htail :
        Runs
          (.seq (.basic (.imm regs.indexCount limit))
            (.seq
              (.basic
                (.sub regs.indexCount regs.indexCount
                  (InputLookup.address regs)))
              (.seq (.basic (.imm regs.base 2))
                (.seq (.basic (.imm regs.basePred 1))
                  (bankRead regs)))))
          afterTest final :=
      Runs.seq hindexInitRun
        (Runs.seq hindexRun
          (Runs.seq hbaseRun
            (Runs.seq hbasePredRun hbank)))
    refine ⟨final, ?_, ?_⟩
    · simpa [command] using
        Runs.seq hlimitRun
          (Runs.seq htestRun (Runs.ifNonzero htest htail))
    · refine
        { result_eq := ?_
          address_eq := ?_
          word_eq := ?_
          one_eq := ?_ }
      · exact hresult.trans
          (hprefix address hpositive hcached)
      · exact hfinalAddress.trans hreadyAddress
      · exact hfinalWord.trans hword.symm
      · exact hfinalOne.trans hone.symm
  · have houtside : limit < address := by
      omega
    have htest : afterTest regs.test = 0 := by
      simp [afterTest, afterLimit, Basic.exec,
        InputLookup.address, regs.index_ne
          (by decide : (11 : Fin 12) ≠ 10), haddress]
      omega
    let final :=
      Basic.exec
        (.load regs.result (InputLookup.address regs))
        afterTest
    have hloadRun :
        Runs (.basic
          (.load regs.result (InputLookup.address regs)))
          afterTest final := by
      exact Runs.basic _ _
    have haddressNotMem :
        address ∉ regs.footprint := by
      intro hmember
      simp only [BankRegisters.footprint, Finset.mem_image,
        Finset.mem_univ, true_and] at hmember
      obtain ⟨slot, hslot⟩ := hmember
      rw [← hslot] at houtside
      exact (Nat.not_lt_of_ge (hregisters slot)) houtside
    have hpreludeWrites :
        RAM.Structured.Footprint.CmdWritesWithin
          regs.footprint
          (.seq
            (.basic (.imm regs.result (limit + 1)))
            (.basic
              (.sub regs.test regs.result
                (InputLookup.address regs)))) := by
      simp [RAM.Structured.Footprint.CmdWritesWithin,
        RAM.Structured.Footprint.BasicWritesWithin]
    have hafterAddress :
        afterTest address = store address :=
      RAM.Structured.Footprint.runs_eq_outside
        hpreludeWrites hprelude haddressNotMem
    have hafterAddressRegister :
        afterTest (InputLookup.address regs) = address := by
      simp [afterTest, afterLimit, Basic.exec,
        InputLookup.address,
        regs.index_ne (by decide : (11 : Fin 12) ≠ 5),
        regs.index_ne (by decide : (11 : Fin 12) ≠ 10),
        haddress]
    refine ⟨final, ?_, ?_⟩
    · simpa [command] using
        Runs.seq hlimitRun
          (Runs.seq htestRun (Runs.ifZero htest hloadRun))
    · refine
        { result_eq := ?_
          address_eq := ?_
          word_eq := ?_
          one_eq := ?_ }
      · simp [final, Basic.exec, hafterAddressRegister,
          hafterAddress, hsuffix address houtside]
      · simp [final, afterTest, afterLimit, Basic.exec,
          InputLookup.address,
          regs.index_ne (by decide : (11 : Fin 12) ≠ 10),
          regs.index_ne (by decide : (11 : Fin 12) ≠ 5),
          haddress]
      · simp [final, afterTest, afterLimit, Basic.exec,
          regs.index_ne (by decide : (0 : Fin 12) ≠ 10),
          regs.index_ne (by decide : (0 : Fin 12) ≠ 5),
          hword]
      · simp [final, afterTest, afterLimit, Basic.exec,
          regs.index_ne (by decide : (6 : Fin 12) ≠ 10),
          regs.index_ne (by decide : (6 : Fin 12) ≠ 5),
          hone]

end Internal

end InputLookup

end Runtime

end TimeSpaceSimulation

end Complexity
