/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.ProviderVectorCollection.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.ProviderResultDecoding
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.ProviderVectorSemantics
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.Layout
import Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodTrial

/-!
# Uniform packed collection of consistency-provider vectors -- proofs
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace ProviderVectorCollection
namespace Internal

open RAM Structured
open NeighborhoodExecutableEvaluation

private theorem basics_runs (operations : List Basic) (store : Store) :
    Runs (Cmd.basics operations) store
      (Basic.execList operations store) := by
  obtain ⟨cost, space, hexec⟩ :=
    RAM.Structured.Internal.exec_basics_exists operations store
  exact ⟨operations.length, cost, space, hexec⟩

private theorem installRowFrom_congr
    (base chunkCount child remaining word : ℕ)
    (first second : ℕ → ℕ)
    (heq :
      ∀ chunk, chunk < remaining →
        first chunk = second chunk) :
    installRowFrom base chunkCount child first remaining word =
      installRowFrom base chunkCount child second remaining word := by
  induction remaining generalizing word with
  | zero =>
      rfl
  | succ remaining ih =>
      simp only [installRowFrom]
      rw [heq remaining (by omega)]
      apply ih
      intro chunk hchunk
      exact heq chunk (by omega)

private theorem providerCoordinate_eq_iff
    {chunkCount firstChild firstChunk secondChild secondChunk : ℕ}
    (hcount : 0 < chunkCount)
    (hfirstChunk : firstChunk < chunkCount)
    (hsecondChunk : secondChunk < chunkCount) :
    providerCoordinate chunkCount firstChild firstChunk =
        providerCoordinate chunkCount secondChild secondChunk ↔
      firstChild = secondChild ∧ firstChunk = secondChunk := by
  constructor
  · intro heq
    have hmod :=
      congrArg (fun value => value % chunkCount) heq
    have hchunk : firstChunk = secondChunk := by
      simpa [providerCoordinate, Nat.add_mod,
        Nat.mod_eq_of_lt hfirstChunk,
        Nat.mod_eq_of_lt hsecondChunk] using hmod
    subst secondChunk
    exact
      ⟨Nat.mul_right_cancel hcount
          (Nat.add_right_cancel heq),
        rfl⟩
  · rintro ⟨rfl, rfl⟩
    rfl

private theorem installRowFrom_digit_ne
    {base chunkCount child remaining word digitIndex : ℕ}
    {value : ℕ → ℕ}
    (hbase : 0 < base)
    (hvalue :
      ∀ chunk, chunk < remaining → value chunk < base)
    (hne :
      ∀ chunk, chunk < remaining →
        digitIndex ≠
          providerCoordinate chunkCount child chunk) :
    PackedDigits.digit base
        (installRowFrom
          base chunkCount child value remaining word)
        digitIndex =
      PackedDigits.digit base word digitIndex := by
  induction remaining generalizing word with
  | zero =>
      rfl
  | succ remaining ih =>
      simp only [installRowFrom]
      rw [ih]
      · apply NeighborhoodProgram.replaceAt_digit_ne hbase
          (hvalue remaining (by omega))
        exact hne remaining (by omega)
      · intro chunk hchunk
        exact hvalue chunk (by omega)
      · intro chunk hchunk
        exact hne chunk (by omega)

private theorem installRowFrom_digit_eq
    {base chunkCount child remaining word chunk : ℕ}
    {value : ℕ → ℕ}
    (hbase : 0 < base)
    (hchunk : chunk < remaining)
    (hvalue :
      ∀ current, current < remaining → value current < base) :
    PackedDigits.digit base
        (installRowFrom
          base chunkCount child value remaining word)
        (providerCoordinate chunkCount child chunk) =
      value chunk := by
  induction remaining generalizing word with
  | zero =>
      omega
  | succ remaining ih =>
      simp only [installRowFrom]
      by_cases heq : chunk = remaining
      · subst chunk
        rw [installRowFrom_digit_ne hbase]
        · exact NeighborhoodProgram.replaceAt_digit_eq hbase
            (hvalue remaining (by omega))
        · intro current hcurrent
          exact hvalue current (by omega)
        · intro current hcurrent hcoordinate
          exact
            (Nat.add_left_cancel hcoordinate).not_gt hcurrent
      · apply ih
        · omega
        · intro current hcurrent
          exact hvalue current (by omega)

private theorem installRow_digit_eq
    {base chunkCount child word chunk : ℕ}
    {value : ℕ → ℕ}
    (hbase : 0 < base)
    (hchunk : chunk < chunkCount)
    (hvalue :
      ∀ current, current < chunkCount → value current < base) :
    PackedDigits.digit base
        (installRow base chunkCount child value word)
        (providerCoordinate chunkCount child chunk) =
      value chunk :=
  installRowFrom_digit_eq hbase hchunk hvalue

private theorem installRow_digit_ne_child
    {base chunkCount child word targetChild targetChunk : ℕ}
    {value : ℕ → ℕ}
    (hbase : 0 < base)
    (hcount : 0 < chunkCount)
    (htargetChunk : targetChunk < chunkCount)
    (hchild : targetChild ≠ child)
    (hvalue :
      ∀ current, current < chunkCount → value current < base) :
    PackedDigits.digit base
        (installRow base chunkCount child value word)
        (providerCoordinate chunkCount targetChild targetChunk) =
      PackedDigits.digit base word
        (providerCoordinate chunkCount targetChild targetChunk) := by
  unfold installRow
  apply installRowFrom_digit_ne hbase hvalue
  intro current hcurrent heq
  have hchildren :=
    (providerCoordinate_eq_iff
      hcount htargetChunk hcurrent).mp heq
  exact hchild hchildren.1

@[simp] private theorem collection_word
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) :
    (collectionBankRegisters controller regs).word =
      controller.hasNext := rfl

@[simp] private theorem collection_base
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) :
    (collectionBankRegisters controller regs).base =
      regs.index 14 := rfl

@[simp] private theorem collection_basePred
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) :
    (collectionBankRegisters controller regs).basePred =
      regs.index 1 := rfl

@[simp] private theorem collection_one
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) :
    (collectionBankRegisters controller regs).one =
      regs.index 17 := rfl

@[simp] private theorem collection_indexCount
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) :
    (collectionBankRegisters controller regs).indexCount =
      regs.index 10 := rfl

@[simp] private theorem collection_replacement
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) :
    (collectionBankRegisters controller regs).replacement =
      regs.index 12 := rfl

private theorem cmdWritesWithin_mono
    {small large : Finset ℕ} {command : Cmd}
    (hsubset : small ⊆ large)
    (hwrites : Footprint.CmdWritesWithin small command) :
    Footprint.CmdWritesWithin large command := by
  induction command with
  | skip =>
      trivial
  | basic operation =>
      cases operation <;>
        simp_all [Footprint.CmdWritesWithin,
          Footprint.BasicWritesWithin]
      all_goals exact hsubset hwrites
  | seq first second firstIH secondIH =>
      exact ⟨firstIH hwrites.1, secondIH hwrites.2⟩
  | ifZero test onZero onNonzero zeroIH nonzeroIH =>
      exact ⟨zeroIH hwrites.1, nonzeroIH hwrites.2⟩
  | whileNonzero test body bodyIH =>
      exact bodyIH hwrites

private theorem resultBank_footprint_subset
    (regs : NeighborhoodTrial.Registers controller) :
    (resultBankRegisters regs).footprint ⊆ regs.footprint := by
  intro address haddress
  obtain ⟨slot, _, rfl⟩ := Finset.mem_image.mp haddress
  apply Finset.mem_union_left
  exact Layout.index_mem_layout_footprint regs (resultBankMap slot)

private theorem collectionBank_footprint_subset
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) :
    (collectionBankRegisters controller regs).footprint ⊆
      regs.footprint := by
  intro address haddress
  obtain ⟨slot, _, rfl⟩ := Finset.mem_image.mp haddress
  rcases Fin.eq_zero_or_eq_succ slot with rfl | ⟨tail, rfl⟩
  · change controller.hasNext ∈ regs.footprint
    apply Finset.mem_union_right
    simp [NeighborhoodTrial.Registers.outputFootprint]
  · apply Finset.mem_union_left
    change
      regs.index (collectionBankTailMap tail) ∈
        regs.layout.footprint
    exact Layout.index_mem_layout_footprint
      regs (collectionBankTailMap tail)

private theorem resultBank_footprint_subset_currentResult
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) :
    (resultBankRegisters regs).footprint ⊆
      currentResultFootprint controller regs := by
  intro address haddress
  simp only [currentResultFootprint, Finset.mem_union]
  exact Or.inl (Or.inl haddress)

private theorem collectionBank_footprint_subset_currentResult
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) :
    (collectionBankRegisters controller regs).footprint ⊆
      currentResultFootprint controller regs := by
  intro address haddress
  simp only [currentResultFootprint, Finset.mem_union]
  exact Or.inl (Or.inr haddress)

private theorem workspace_mem_footprint
    (regs : NeighborhoodTrial.Registers controller)
    (slot : Fin 34) :
    regs.index slot ∈ regs.footprint :=
  Finset.mem_union_left _
    (Layout.index_mem_layout_footprint regs slot)

private theorem prepareSource_writesWithin_layout
    (workTapeCount : ℕ)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin regs.layout.footprint
      (Cmd.basics
        (prepareSourceOps workTapeCount controller regs)) := by
  simp only [prepareSourceOps, Cmd.basics, List.map_cons,
    List.map_nil, Cmd.seqList, Footprint.CmdWritesWithin,
    Footprint.BasicWritesWithin]
  exact
    ⟨Layout.index_mem_layout_footprint regs (resultBankMap 6),
      Layout.index_mem_layout_footprint regs 31,
      Layout.index_mem_layout_footprint regs 30,
      Layout.index_mem_layout_footprint regs 30,
      Layout.index_mem_layout_footprint regs 30,
      Layout.index_mem_layout_footprint regs (resultBankMap 8),
      Layout.index_mem_layout_footprint regs (resultBankMap 8),
      Layout.index_mem_layout_footprint regs (resultBankMap 3)⟩

private theorem prepareTarget_writesWithin_layout
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin regs.layout.footprint
      (Cmd.basics (prepareTargetOps controller regs)) := by
  simp only [prepareTargetOps, Cmd.basics, List.map_cons,
    List.map_nil, Cmd.seqList, Footprint.CmdWritesWithin,
    Footprint.BasicWritesWithin]
  exact
    ⟨Layout.index_mem_layout_footprint regs 30,
      Layout.index_mem_layout_footprint regs 30,
      Layout.index_mem_layout_footprint regs 30,
      Layout.index_mem_layout_footprint regs 30,
      Layout.index_mem_layout_footprint regs
        (collectionBankTailMap 7),
      Layout.index_mem_layout_footprint regs
        (collectionBankTailMap 7),
      Layout.index_mem_layout_footprint regs
        (collectionBankTailMap 2)⟩

private theorem resultBank_workspace_not_mem
    (regs : NeighborhoodTrial.Registers controller)
    (target : Fin 34)
    (hmap : ∀ slot : Fin 12, resultBankMap slot ≠ target) :
    regs.index target ∉ (resultBankRegisters regs).footprint := by
  intro hmem
  obtain ⟨slot, _, heq⟩ := Finset.mem_image.mp hmem
  exact hmap slot (regs.injective heq)

private theorem resultBank_controller_not_mem
    (regs : NeighborhoodTrial.Registers controller)
    (controllerSlot : Fin 17) :
    controller.index controllerSlot ∉
      (resultBankRegisters regs).footprint := by
  intro hmem
  obtain ⟨slot, _, heq⟩ := Finset.mem_image.mp hmem
  exact regs.index_ne_controller
    (resultBankMap slot) controllerSlot heq

private theorem collectionBank_workspace_not_mem
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (target : Fin 34)
    (hmap :
      ∀ slot : Fin 11, collectionBankTailMap slot ≠ target) :
    regs.index target ∉
      (collectionBankRegisters controller regs).footprint := by
  intro hmem
  obtain ⟨slot, _, heq⟩ := Finset.mem_image.mp hmem
  rcases Fin.eq_zero_or_eq_succ slot with rfl | ⟨tail, rfl⟩
  · exact regs.index_ne_controller target (5 : Fin 17) heq.symm
  · exact hmap tail (regs.injective heq)

private theorem collectionBank_controller_not_mem
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (controllerSlot : Fin 17)
    (hne : controllerSlot ≠ 5) :
    controller.index controllerSlot ∉
      (collectionBankRegisters controller regs).footprint := by
  intro hmem
  obtain ⟨slot, _, heq⟩ := Finset.mem_image.mp hmem
  rcases Fin.eq_zero_or_eq_succ slot with rfl | ⟨tail, rfl⟩
  · exact hne (controller.injective heq.symm)
  · exact regs.index_ne_controller
      (collectionBankTailMap tail) controllerSlot heq

private theorem currentResult_workspace_not_mem
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (target : Fin 34)
    (hsource :
      ∀ slot : Fin 12, resultBankMap slot ≠ target)
    (hcollection :
      ∀ slot : Fin 11, collectionBankTailMap slot ≠ target)
    (hcoordinate : target ≠ 30)
    (hremaining : target ≠ 31) :
    regs.index target ∉ currentResultFootprint controller regs := by
  rw [currentResultFootprint, Finset.mem_union,
    Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
  push Not
  exact
    ⟨⟨resultBank_workspace_not_mem regs target hsource,
        collectionBank_workspace_not_mem
          controller regs target hcollection⟩,
      ⟨fun heq => hcoordinate (regs.injective heq),
        fun heq => hremaining (regs.injective heq)⟩⟩

private theorem currentResult_controller_not_mem
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (slot : Fin 17)
    (hne : slot ≠ 5) :
    controller.index slot ∉
      currentResultFootprint controller regs := by
  rw [currentResultFootprint, Finset.mem_union,
    Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
  push Not
  exact
    ⟨⟨resultBank_controller_not_mem regs slot,
        collectionBank_controller_not_mem
          controller regs slot hne⟩,
      ⟨(regs.index_ne_controller (30 : Fin 34) slot).symm,
        (regs.index_ne_controller (31 : Fin 34) slot).symm⟩⟩

theorem collectChunkBody_writesWithin_internal
    (workTapeCount : ℕ)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin regs.footprint
      (collectChunkBody workTapeCount controller regs) := by
  let source := resultBankRegisters regs
  let target := collectionBankRegisters controller regs
  have hsource :
      Footprint.CmdWritesWithin regs.footprint
        (NeighborhoodProgram.bankRead source) :=
    cmdWritesWithin_mono
      (resultBank_footprint_subset regs)
      (NeighborhoodProgram.bankRead_sourceWritesWithin source)
  have htarget :
      Footprint.CmdWritesWithin regs.footprint
        (NeighborhoodProgram.bankReplace target) :=
    cmdWritesWithin_mono
      (collectionBank_footprint_subset controller regs)
      (NeighborhoodProgram.bankReplace_sourceWritesWithin target)
  have hprepareSource :
      Footprint.CmdWritesWithin regs.footprint
        (Cmd.basics
          (prepareSourceOps workTapeCount controller regs)) := by
    simp only [prepareSourceOps, Cmd.basics, List.map_cons,
      List.map_nil, Cmd.seqList, Footprint.CmdWritesWithin,
      Footprint.BasicWritesWithin]
    exact
      ⟨workspace_mem_footprint regs (resultBankMap 6),
        workspace_mem_footprint regs 31,
        workspace_mem_footprint regs 30,
        workspace_mem_footprint regs 30,
        workspace_mem_footprint regs 30,
        workspace_mem_footprint regs (resultBankMap 8),
        workspace_mem_footprint regs (resultBankMap 8),
        workspace_mem_footprint regs (resultBankMap 3)⟩
  have htargetIndex :
      target.indexCount ∈ regs.footprint := by
    apply collectionBank_footprint_subset controller regs
    exact NeighborhoodProgram.BankRegisters.index_mem_footprint
      target 8
  have htargetBasePred :
      target.basePred ∈ regs.footprint := by
    apply collectionBank_footprint_subset controller regs
    exact NeighborhoodProgram.BankRegisters.index_mem_footprint
      target 3
  have hprepareTarget :
      Footprint.CmdWritesWithin regs.footprint
        (Cmd.basics (prepareTargetOps controller regs)) := by
    simp only [prepareTargetOps, Cmd.basics, List.map_cons,
      List.map_nil, Cmd.seqList, Footprint.CmdWritesWithin,
      Footprint.BasicWritesWithin]
    exact
      ⟨workspace_mem_footprint regs 30,
        workspace_mem_footprint regs 30,
        workspace_mem_footprint regs 30,
        workspace_mem_footprint regs 30,
        htargetIndex, htargetIndex, htargetBasePred⟩
  change
    Footprint.CmdWritesWithin regs.footprint
      (Cmd.seq
        (Cmd.basics
          (prepareSourceOps workTapeCount controller regs))
        (Cmd.seq (NeighborhoodProgram.bankRead source)
          (Cmd.seq
            (Cmd.basics (prepareTargetOps controller regs))
            (NeighborhoodProgram.bankReplace target))))
  exact
    ⟨hprepareSource, hsource, hprepareTarget, htarget⟩

theorem collectCurrentResult_writesWithin_internal
    (workTapeCount : ℕ)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin regs.footprint
      (collectCurrentResult workTapeCount controller regs) := by
  simp only [collectCurrentResult, Footprint.CmdWritesWithin,
    Footprint.BasicWritesWithin]
  exact
    ⟨⟨workspace_mem_footprint regs 31,
        workspace_mem_footprint regs 31⟩,
      collectChunkBody_writesWithin_internal
        workTapeCount controller regs⟩

theorem collectCurrentResult_precise_writesWithin_internal
    (workTapeCount : ℕ)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin
      (currentResultFootprint controller regs)
      (collectCurrentResult workTapeCount controller regs) := by
  let source := resultBankRegisters regs
  let target := collectionBankRegisters controller regs
  have hsource :
      Footprint.CmdWritesWithin
        (currentResultFootprint controller regs)
        (NeighborhoodProgram.bankRead source) :=
    cmdWritesWithin_mono
      (resultBank_footprint_subset_currentResult controller regs)
      (NeighborhoodProgram.bankRead_sourceWritesWithin source)
  have htarget :
      Footprint.CmdWritesWithin
        (currentResultFootprint controller regs)
        (NeighborhoodProgram.bankReplace target) :=
    cmdWritesWithin_mono
      (collectionBank_footprint_subset_currentResult
        controller regs)
      (NeighborhoodProgram.bankReplace_sourceWritesWithin target)
  have hcoordinate :
      coordinate regs ∈ currentResultFootprint controller regs := by
    simp [currentResultFootprint]
  have hremaining :
      chunkRemaining regs ∈
        currentResultFootprint controller regs := by
    simp [currentResultFootprint]
  have hsourceIndex
      (slot : Fin 12) :
      source.index slot ∈
        currentResultFootprint controller regs := by
    apply resultBank_footprint_subset_currentResult controller regs
    exact NeighborhoodProgram.BankRegisters.index_mem_footprint
      source slot
  have htargetIndex
      (slot : Fin 12) :
      target.index slot ∈
        currentResultFootprint controller regs := by
    apply collectionBank_footprint_subset_currentResult controller regs
    exact NeighborhoodProgram.BankRegisters.index_mem_footprint
      target slot
  have hprepareSource :
      Footprint.CmdWritesWithin
        (currentResultFootprint controller regs)
        (Cmd.basics
          (prepareSourceOps workTapeCount controller regs)) := by
    simp only [prepareSourceOps, Cmd.basics, List.map_cons,
      List.map_nil, Cmd.seqList, Footprint.CmdWritesWithin,
      Footprint.BasicWritesWithin]
    exact
      ⟨hsourceIndex 6, hremaining, hcoordinate, hcoordinate,
        hcoordinate, hsourceIndex 8, hsourceIndex 8,
        hsourceIndex 3⟩
  have hprepareTarget :
      Footprint.CmdWritesWithin
        (currentResultFootprint controller regs)
        (Cmd.basics (prepareTargetOps controller regs)) := by
    simp only [prepareTargetOps, Cmd.basics, List.map_cons,
      List.map_nil, Cmd.seqList, Footprint.CmdWritesWithin,
      Footprint.BasicWritesWithin]
    exact
      ⟨hcoordinate, hcoordinate, hcoordinate, hcoordinate,
        htargetIndex 8, htargetIndex 8, htargetIndex 3⟩
  have hbody :
      Footprint.CmdWritesWithin
        (currentResultFootprint controller regs)
        (collectChunkBody workTapeCount controller regs) := by
    change
      Footprint.CmdWritesWithin
        (currentResultFootprint controller regs)
        (Cmd.seq
          (Cmd.basics
            (prepareSourceOps workTapeCount controller regs))
          (Cmd.seq (NeighborhoodProgram.bankRead source)
            (Cmd.seq
              (Cmd.basics (prepareTargetOps controller regs))
              (NeighborhoodProgram.bankReplace target))))
    exact ⟨hprepareSource, hsource, hprepareTarget, htarget⟩
  simp only [collectCurrentResult, Footprint.CmdWritesWithin,
    Footprint.BasicWritesWithin]
  exact ⟨⟨hremaining, hremaining⟩, hbody⟩

private theorem collectCurrentResult_workspace_eq
    (workTapeCount : ℕ)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (store final : Store)
    (hrun :
      Runs (collectCurrentResult workTapeCount controller regs)
        store final)
    (target : Fin 34)
    (hsource :
      ∀ slot : Fin 12, resultBankMap slot ≠ target)
    (hcollection :
      ∀ slot : Fin 11, collectionBankTailMap slot ≠ target)
    (hcoordinate : target ≠ 30)
    (hremaining : target ≠ 31) :
    final (regs.index target) = store (regs.index target) :=
  Footprint.runs_eq_outside
    (collectCurrentResult_precise_writesWithin_internal
      workTapeCount controller regs)
    hrun
    (currentResult_workspace_not_mem controller regs target
      hsource hcollection hcoordinate hremaining)

private theorem collectCurrentResult_controller_eq
    (workTapeCount : ℕ)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (store final : Store)
    (hrun :
      Runs (collectCurrentResult workTapeCount controller regs)
        store final)
    (slot : Fin 17)
    (hne : slot ≠ 5) :
    final (controller.index slot) =
      store (controller.index slot) :=
  Footprint.runs_eq_outside
    (collectCurrentResult_precise_writesWithin_internal
      workTapeCount controller regs)
    hrun
    (currentResult_controller_not_mem controller regs slot hne)

private theorem collectCurrentResult_preserves_parameters
    {tm : TM workTapeCount}
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (store final : Store)
    (hrun :
      Runs (collectCurrentResult workTapeCount controller regs)
        store final)
    (hparameters :
      Representation.Parameters regs instanceData store)
    (hbase :
      final (resultBankRegisters regs).base =
        Representation.fieldBase instanceData)
    (hchunkCount :
      final (Layout.chunkCount regs) =
        TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
          (payloadWidth tm instanceData.blockLength)
          (graphFanIn workTapeCount)) :
    Representation.Parameters regs instanceData final := by
  constructor
  · exact
      (collectCurrentResult_workspace_eq
        workTapeCount controller regs store final hrun 2
        (by decide) (by decide) (by decide) (by decide)).trans
        hparameters.blockLength_eq
  · exact
      (collectCurrentResult_workspace_eq
        workTapeCount controller regs store final hrun 3
        (by decide) (by decide) (by decide) (by decide)).trans
        hparameters.horizon_eq
  · exact
      (collectCurrentResult_workspace_eq
        workTapeCount controller regs store final hrun 8
        (by decide) (by decide) (by decide) (by decide)).trans
        hparameters.digitBase_eq
  · simpa [resultBankRegisters, resultBankMap] using hbase
  · exact
      (collectCurrentResult_workspace_eq
        workTapeCount controller regs store final hrun 13
        (by decide) (by decide) (by decide) (by decide)).trans
        hparameters.frameBase_eq
  · exact hchunkCount
  · exact
      (collectCurrentResult_workspace_eq
        workTapeCount controller regs store final hrun 15
        (by decide) (by decide) (by decide) (by decide)).trans
        hparameters.bankDigitCount_eq
  · exact
      (collectCurrentResult_workspace_eq
        workTapeCount controller regs store final hrun 24
        (by decide) (by decide) (by decide) (by decide)).trans
        hparameters.modulus_eq
  · exact
      (collectCurrentResult_workspace_eq
        workTapeCount controller regs store final hrun 16
        (by decide) (by decide) (by decide) (by decide)).trans
        hparameters.modulusPred_eq

private theorem seqList_map_collectChild_writesWithin
    (tm : TM workTapeCount)
    (order : FiniteEncoding.StateOrder tm)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (combine : Cmd)
    (hcombine :
      Footprint.CmdWritesWithin regs.layout.footprint combine) :
    ∀ list : List (Fin (graphFanIn workTapeCount)),
      Footprint.CmdWritesWithin regs.footprint
        (Cmd.seqList
          (list.map
            (collectChild tm order controller regs combine))) := by
  intro list
  induction list with
  | nil =>
      trivial
  | cons child rest ih =>
      have hcursor :
          controller.verdict ∈ regs.footprint := by
        apply Finset.mem_union_right
        simp [NeighborhoodTrial.Registers.outputFootprint]
      have hevaluate :
          Footprint.CmdWritesWithin regs.footprint
            (ProviderQueryEvaluation.evaluate
              tm order controller regs combine) :=
        cmdWritesWithin_mono Finset.subset_union_left
          (ProviderQueryEvaluation.evaluate_writesWithin
            tm order controller regs combine hcombine)
      have hchild :
          Footprint.CmdWritesWithin regs.footprint
            (collectChild tm order controller regs combine child) := by
        simpa only [collectChild, Cmd.seqList,
          Footprint.CmdWritesWithin,
          Footprint.BasicWritesWithin] using
          And.intro hcursor
            (And.intro hevaluate
              (collectCurrentResult_writesWithin_internal
                workTapeCount controller regs))
      cases rest with
      | nil =>
          simpa [Cmd.seqList] using hchild
      | cons next tail =>
          simpa only [List.map_cons, Cmd.seqList,
            Footprint.CmdWritesWithin] using And.intro hchild ih

theorem collect_writesWithin_internal
    (tm : TM workTapeCount)
    (order : FiniteEncoding.StateOrder tm)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (combine : Cmd)
    (hcombine :
      Footprint.CmdWritesWithin regs.layout.footprint combine) :
    Footprint.CmdWritesWithin regs.footprint
      (collect tm order controller regs combine) := by
  have hhasNext :
      controller.hasNext ∈ regs.footprint := by
    apply Finset.mem_union_right
    simp [NeighborhoodTrial.Registers.outputFootprint]
  have hverdict :
      controller.verdict ∈ regs.footprint := by
    apply Finset.mem_union_right
    simp [NeighborhoodTrial.Registers.outputFootprint]
  simpa only [collect, Cmd.seqList,
    Footprint.CmdWritesWithin, Footprint.BasicWritesWithin] using
    And.intro hhasNext
      (And.intro
        (seqList_map_collectChild_writesWithin
          tm order controller regs combine hcombine
          (children workTapeCount))
        hverdict)

theorem collectChunkBody_runs_internal
    (workTapeCount : ℕ)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store)
    (remaining chunkCount child sourceWord base word : ℕ)
    (hbase : 0 < base)
    (hremaining :
      store (chunkRemaining regs) = remaining + 1)
    (hchunkCount :
      store (Layout.chunkCount regs) = chunkCount)
    (hchild : store controller.verdict = child)
    (hsourceWord :
      store (resultBankRegisters regs).word = sourceWord)
    (hbaseValue :
      store (resultBankRegisters regs).base = base)
    (hword : store controller.hasNext = word) :
    ∃ final,
      Runs
        (collectChunkBody workTapeCount controller regs)
        store final ∧
      final (chunkRemaining regs) = remaining ∧
      final (resultBankRegisters regs).word = sourceWord ∧
      final controller.hasNext =
        NeighborhoodProgram.replaceAt base word
          (providerCoordinate chunkCount child remaining)
          (PackedDigits.digit base sourceWord
            (providerCoordinate chunkCount
              (graphFanIn workTapeCount) remaining)) ∧
      final (resultBankRegisters regs).base = base ∧
      final (Layout.chunkCount regs) = chunkCount ∧
      final controller.verdict = child := by
  let source := resultBankRegisters regs
  let target := collectionBankRegisters controller regs
  let sourceCoordinate :=
    providerCoordinate chunkCount
      (graphFanIn workTapeCount) remaining
  let targetCoordinate :=
    providerCoordinate chunkCount child remaining
  let afterSource :=
    Basic.execList
      (prepareSourceOps workTapeCount controller regs) store
  have hprepareSource :
      Runs
        (Cmd.basics
          (prepareSourceOps workTapeCount controller regs))
        store afterSource :=
    basics_runs _ _
  have hsourceRemaining :
      afterSource (chunkRemaining regs) = remaining := by
    simp [afterSource, prepareSourceOps, Basic.execList, Basic.exec,
      resultBankRegisters, resultBankMap,
      chunkRemaining, coordinate, Layout.chunkCount,
      regs.injective.eq_iff, hremaining, hchunkCount]
  have hsourceCoordinate :
      afterSource source.indexCount = sourceCoordinate := by
    simp [afterSource, prepareSourceOps, Basic.execList, Basic.exec,
      source, sourceCoordinate, providerCoordinate,
      resultBankRegisters, resultBankMap,
      chunkRemaining, coordinate, Layout.chunkCount,
      regs.injective.eq_iff, hremaining, hchunkCount]
  have hsourceWordReady :
      afterSource source.word = sourceWord := by
    simpa [afterSource, prepareSourceOps, Basic.execList, Basic.exec,
      source, resultBankRegisters, resultBankMap,
      chunkRemaining, coordinate, Layout.chunkCount,
      regs.injective.eq_iff] using hsourceWord
  have hsourceBaseReady :
      afterSource source.base = base := by
    simpa [afterSource, prepareSourceOps, Basic.execList, Basic.exec,
      source, resultBankRegisters, resultBankMap,
      chunkRemaining, coordinate, Layout.chunkCount,
      regs.injective.eq_iff] using hbaseValue
  have hsourceBasePred :
      afterSource source.basePred = base - 1 := by
    rw [show afterSource source.basePred =
        store source.base - 1 by
      simp [afterSource, prepareSourceOps, Basic.execList, Basic.exec,
        source, resultBankRegisters, resultBankMap,
        chunkRemaining, coordinate, Layout.chunkCount,
        regs.injective.eq_iff]]
    exact congrArg (fun value => value - 1) hbaseValue
  have hsourceOne :
      afterSource source.one = 1 := by
    simp [afterSource, prepareSourceOps, Basic.execList, Basic.exec,
      source, resultBankRegisters, resultBankMap,
      chunkRemaining, coordinate, Layout.chunkCount,
      regs.injective.eq_iff]
  obtain
    ⟨afterRead, hread, hreadWord, _, _, _, hreadResult,
      hreadBase, _, hreadOne, _⟩ :=
    NeighborhoodProgram.bankRead_runs source afterSource base
      sourceWord sourceCoordinate hbase hsourceWordReady
      hsourceBaseReady hsourceBasePred hsourceOne
      hsourceCoordinate
  have hsourceController
      (slot : Fin 17) :
      afterSource (controller.index slot) =
        store (controller.index slot) := by
    apply Footprint.runs_eq_outside
      (prepareSource_writesWithin_layout
        workTapeCount controller regs)
      hprepareSource
    exact fun hlayout =>
      Finset.disjoint_left.mp
        (NeighborhoodTrial.Registers.layout_disjoint_controller regs)
        hlayout (controller.index_mem_footprint slot)
  have hreadRemaining :
      afterRead (chunkRemaining regs) = remaining := by
    rw [Footprint.runs_eq_outside
      (NeighborhoodProgram.bankRead_sourceWritesWithin source)
      hread
      (resultBank_workspace_not_mem regs 31 (by decide))]
    exact hsourceRemaining
  have hsourceChunkCount :
      afterSource (Layout.chunkCount regs) = chunkCount := by
    simpa [afterSource, prepareSourceOps, Basic.execList, Basic.exec,
      source, resultBankRegisters, resultBankMap,
      chunkRemaining, coordinate, Layout.chunkCount,
      regs.injective.eq_iff] using hchunkCount
  have hreadChunkCount :
      afterRead (Layout.chunkCount regs) = chunkCount := by
    rw [Footprint.runs_eq_outside
      (NeighborhoodProgram.bankRead_sourceWritesWithin source)
      hread
      (resultBank_workspace_not_mem regs 7 (by decide))]
    exact hsourceChunkCount
  have hreadChild :
      afterRead controller.verdict = child := by
    rw [Footprint.runs_eq_outside
      (NeighborhoodProgram.bankRead_sourceWritesWithin source)
      hread (resultBank_controller_not_mem regs 4)]
    exact (hsourceController 4).trans hchild
  have hreadCollectedWord :
      afterRead controller.hasNext = word := by
    rw [Footprint.runs_eq_outside
      (NeighborhoodProgram.bankRead_sourceWritesWithin source)
      hread (resultBank_controller_not_mem regs 5)]
    exact (hsourceController 5).trans hword
  let afterTarget :=
    Basic.execList
      (prepareTargetOps controller regs) afterRead
  have hprepareTarget :
      Runs (Cmd.basics (prepareTargetOps controller regs))
        afterRead afterTarget :=
    basics_runs _ _
  have htargetCoordinate :
      afterTarget target.indexCount = targetCoordinate := by
    change afterTarget (regs.index 10) = targetCoordinate
    simp [afterTarget, prepareTargetOps, Basic.execList, Basic.exec,
      targetCoordinate, providerCoordinate,
      chunkRemaining, coordinate,
      Layout.chunkCount, regs.injective.eq_iff,
      hreadRemaining, hreadChunkCount]
    left
    rw [Function.update_of_ne
      (regs.index_ne_controller
        (30 : Fin 34) (4 : Fin 17)).symm]
    exact hreadChild
  have htargetWordReady :
      afterTarget target.word = word := by
    have houtside :
        afterTarget controller.hasNext =
          afterRead controller.hasNext := by
      apply Footprint.runs_eq_outside
        (prepareTarget_writesWithin_layout controller regs)
        hprepareTarget
      exact fun hlayout =>
        Finset.disjoint_left.mp
          (NeighborhoodTrial.Registers.layout_disjoint_controller regs)
          hlayout (controller.index_mem_footprint 5)
    exact houtside.trans hreadCollectedWord
  have htargetBaseReady :
      afterTarget target.base = base := by
    change afterTarget (regs.index 14) = base
    simpa [afterTarget, prepareTargetOps, Basic.execList, Basic.exec,
      source, resultBankRegisters, resultBankMap,
      chunkRemaining, coordinate, Layout.chunkCount,
      regs.injective.eq_iff] using hreadBase
  have htargetBasePred :
      afterTarget target.basePred = base - 1 := by
    change afterTarget (regs.index 1) = base - 1
    change afterRead (regs.index 14) = base at hreadBase
    change afterRead (regs.index 17) = 1 at hreadOne
    simp [afterTarget, prepareTargetOps, Basic.execList, Basic.exec,
      chunkRemaining, coordinate, Layout.chunkCount,
      regs.injective.eq_iff, hreadBase, hreadOne]
  have htargetOne :
      afterTarget target.one = 1 := by
    change afterTarget (regs.index 17) = 1
    simpa [afterTarget, prepareTargetOps, Basic.execList, Basic.exec,
      source, resultBankRegisters, resultBankMap,
      chunkRemaining, coordinate, Layout.chunkCount,
      regs.injective.eq_iff] using hreadOne
  have htargetReplacement :
      afterTarget target.replacement =
        PackedDigits.digit base sourceWord sourceCoordinate := by
    change
      afterTarget (regs.index 12) =
        PackedDigits.digit base sourceWord sourceCoordinate
    simpa [afterTarget, prepareTargetOps, Basic.execList, Basic.exec,
      source, resultBankRegisters, resultBankMap,
      chunkRemaining, coordinate, Layout.chunkCount,
      regs.injective.eq_iff] using hreadResult
  obtain
    ⟨final, hreplace, hfinalWord, _, _, _, _, hfinalBase,
      _, _, _⟩ :=
    NeighborhoodProgram.bankReplace_runs target afterTarget
      base word targetCoordinate
      (PackedDigits.digit base sourceWord sourceCoordinate)
      hbase htargetWordReady htargetBaseReady htargetBasePred
      htargetOne htargetCoordinate htargetReplacement
  have htargetSourceWord :
      afterTarget source.word = sourceWord := by
    change afterTarget (regs.index 33) = sourceWord
    simpa [afterTarget, prepareTargetOps, Basic.execList, Basic.exec,
      source, resultBankRegisters, resultBankMap,
      chunkRemaining, coordinate, Layout.chunkCount,
      regs.injective.eq_iff] using hreadWord
  have hfinalSourceWord :
      final source.word = sourceWord := by
    change final (regs.index 33) = sourceWord
    rw [Footprint.runs_eq_outside
      (NeighborhoodProgram.bankReplace_sourceWritesWithin target)
      hreplace
      (collectionBank_workspace_not_mem
        controller regs 33 (by decide))]
    exact htargetSourceWord
  have htargetRemaining :
      afterTarget (chunkRemaining regs) = remaining := by
    change afterTarget (regs.index 31) = remaining
    simp [afterTarget, prepareTargetOps, Basic.execList, Basic.exec,
      chunkRemaining, coordinate,
      Layout.chunkCount, regs.injective.eq_iff, hreadRemaining]
  have hfinalRemaining :
      final (chunkRemaining regs) = remaining := by
    rw [Footprint.runs_eq_outside
      (NeighborhoodProgram.bankReplace_sourceWritesWithin target)
      hreplace
      (collectionBank_workspace_not_mem
        controller regs 31 (by decide))]
    exact htargetRemaining
  have htargetChunkCount :
      afterTarget (Layout.chunkCount regs) = chunkCount := by
    change afterTarget (regs.index 7) = chunkCount
    simp [afterTarget, prepareTargetOps, Basic.execList, Basic.exec,
      chunkRemaining, coordinate,
      Layout.chunkCount, regs.injective.eq_iff, hreadChunkCount]
  have hfinalChunkCount :
      final (Layout.chunkCount regs) = chunkCount := by
    rw [Footprint.runs_eq_outside
      (NeighborhoodProgram.bankReplace_sourceWritesWithin target)
      hreplace
      (collectionBank_workspace_not_mem
        controller regs 7 (by decide))]
    exact htargetChunkCount
  have htargetChild :
      afterTarget controller.verdict = child := by
    have houtside :
        afterTarget controller.verdict =
          afterRead controller.verdict := by
      apply Footprint.runs_eq_outside
        (prepareTarget_writesWithin_layout controller regs)
        hprepareTarget
      exact fun hlayout =>
        Finset.disjoint_left.mp
          (NeighborhoodTrial.Registers.layout_disjoint_controller regs)
          hlayout (controller.index_mem_footprint 4)
    exact houtside.trans hreadChild
  have hfinalChild :
      final controller.verdict = child := by
    rw [Footprint.runs_eq_outside
      (NeighborhoodProgram.bankReplace_sourceWritesWithin target)
      hreplace
      (collectionBank_controller_not_mem
        controller regs 4 (by decide))]
    exact htargetChild
  have hrun :
      Runs (collectChunkBody workTapeCount controller regs)
        store final := by
    simpa only [collectChunkBody, Cmd.seqList] using
      Runs.seq hprepareSource
        (Runs.seq hread (Runs.seq hprepareTarget hreplace))
  exact
    ⟨final, hrun, hfinalRemaining, hfinalSourceWord,
      by
        simpa [target, targetCoordinate, sourceCoordinate] using
          hfinalWord,
      by simpa [source, target] using hfinalBase,
      hfinalChunkCount, hfinalChild⟩

theorem collectChunks_runs_internal
    (workTapeCount : ℕ)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (remaining chunkCount child sourceWord base word : ℕ)
    (hbase : 0 < base)
    (store : Store)
    (hremaining :
      store (chunkRemaining regs) = remaining)
    (hchunkCount :
      store (Layout.chunkCount regs) = chunkCount)
    (hchild : store controller.verdict = child)
    (hsourceWord :
      store (resultBankRegisters regs).word = sourceWord)
    (hbaseValue :
      store (resultBankRegisters regs).base = base)
    (hword : store controller.hasNext = word) :
    ∃ final,
      Runs
        (.whileNonzero (chunkRemaining regs)
          (collectChunkBody workTapeCount controller regs))
        store final ∧
      final (chunkRemaining regs) = 0 ∧
      final (resultBankRegisters regs).word = sourceWord ∧
      final controller.hasNext =
        installRowFrom base chunkCount child
          (fun chunk =>
            PackedDigits.digit base sourceWord
              (providerCoordinate chunkCount
                (graphFanIn workTapeCount) chunk))
          remaining word ∧
      final (resultBankRegisters regs).base = base ∧
      final (Layout.chunkCount regs) = chunkCount ∧
      final controller.verdict = child := by
  induction remaining generalizing store word with
  | zero =>
      refine
        ⟨store, Runs.whileZero hremaining, hremaining,
          hsourceWord, ?_, hbaseValue, hchunkCount, hchild⟩
      simpa [installRowFrom] using hword
  | succ remaining ih =>
      let nextWord :=
        NeighborhoodProgram.replaceAt base word
          (providerCoordinate chunkCount child remaining)
          (PackedDigits.digit base sourceWord
            (providerCoordinate chunkCount
              (graphFanIn workTapeCount) remaining))
      obtain
        ⟨middle, hbody, hmiddleRemaining, hmiddleSource,
          hmiddleWord, hmiddleBase, hmiddleChunkCount,
          hmiddleChild⟩ :=
        collectChunkBody_runs_internal
          workTapeCount controller regs store remaining
          chunkCount child sourceWord base word hbase
          hremaining hchunkCount hchild hsourceWord
          hbaseValue hword
      obtain
        ⟨final, hloop, hfinalRemaining, hfinalSource,
          hfinalWord, hfinalBase, hfinalChunkCount,
          hfinalChild⟩ :=
        ih nextWord middle hmiddleRemaining hmiddleChunkCount
          hmiddleChild hmiddleSource hmiddleBase
          (by simpa [nextWord] using hmiddleWord)
      have hnonzero :
          store (chunkRemaining regs) ≠ 0 := by
        rw [hremaining]
        omega
      refine
        ⟨final, Runs.whileNonzero hnonzero hbody hloop,
          hfinalRemaining, hfinalSource, ?_, hfinalBase,
          hfinalChunkCount, hfinalChild⟩
      simpa [installRowFrom, nextWord] using hfinalWord

theorem collectCurrentResult_runs_internal
    (workTapeCount : ℕ)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (chunkCount child sourceWord base word : ℕ)
    (hbase : 0 < base)
    (store : Store)
    (hchunkCount :
      store (Layout.chunkCount regs) = chunkCount)
    (hchild : store controller.verdict = child)
    (hsourceWord :
      store (resultBankRegisters regs).word = sourceWord)
    (hbaseValue :
      store (resultBankRegisters regs).base = base)
    (hword : store controller.hasNext = word) :
    ∃ final,
      Runs
        (collectCurrentResult workTapeCount controller regs)
        store final ∧
      final (chunkRemaining regs) = 0 ∧
      final (resultBankRegisters regs).word = sourceWord ∧
      final controller.hasNext =
        installRow base chunkCount child
          (fun chunk =>
            PackedDigits.digit base sourceWord
              (providerCoordinate chunkCount
                (graphFanIn workTapeCount) chunk))
          word ∧
      final (resultBankRegisters regs).base = base ∧
      final (Layout.chunkCount regs) = chunkCount ∧
      final controller.verdict = child := by
  let afterZero :=
    (Basic.imm (chunkRemaining regs) 0).exec store
  let initialized :=
    (Basic.add (chunkRemaining regs) (Layout.chunkCount regs)
      (chunkRemaining regs)).exec afterZero
  have hzero :
      Runs (.basic (.imm (chunkRemaining regs) 0))
        store afterZero :=
    Runs.basic _ _
  have hinitialize :
      Runs
        (.basic
          (.add (chunkRemaining regs) (Layout.chunkCount regs)
            (chunkRemaining regs)))
        afterZero initialized :=
    Runs.basic _ _
  have hinitializedRemaining :
      initialized (chunkRemaining regs) = chunkCount := by
    simp [initialized, afterZero, Basic.exec,
      chunkRemaining, Layout.chunkCount,
      regs.injective.eq_iff, hchunkCount]
  have hinitializedChunkCount :
      initialized (Layout.chunkCount regs) = chunkCount := by
    simp [initialized, afterZero, Basic.exec,
      chunkRemaining, Layout.chunkCount,
      regs.injective.eq_iff, hchunkCount]
  have hinitializedSource :
      initialized (resultBankRegisters regs).word =
        sourceWord := by
    simpa [initialized, afterZero, Basic.exec,
      chunkRemaining, Layout.chunkCount,
      resultBankRegisters, resultBankMap,
      regs.injective.eq_iff] using hsourceWord
  have hinitializedBase :
      initialized (resultBankRegisters regs).base = base := by
    simpa [initialized, afterZero, Basic.exec,
      chunkRemaining, Layout.chunkCount,
      resultBankRegisters, resultBankMap,
      regs.injective.eq_iff] using hbaseValue
  have hinitializedController
      (slot : Fin 17) :
      initialized (controller.index slot) =
        store (controller.index slot) := by
    simp only [initialized, afterZero, Basic.exec]
    rw [Function.update_of_ne
      (regs.index_ne_controller (31 : Fin 34) slot).symm]
    rw [Function.update_of_ne
      (regs.index_ne_controller (31 : Fin 34) slot).symm]
  obtain
    ⟨final, hloop, hfinalRemaining, hfinalSource,
      hfinalWord, hfinalBase, hfinalChunkCount,
      hfinalChild⟩ :=
    collectChunks_runs_internal
      workTapeCount controller regs chunkCount chunkCount child
      sourceWord base word hbase initialized
      hinitializedRemaining hinitializedChunkCount
      ((hinitializedController 4).trans hchild)
      hinitializedSource hinitializedBase
      ((hinitializedController 5).trans hword)
  have hrun :
      Runs (collectCurrentResult workTapeCount controller regs)
        store final := by
    simpa [collectCurrentResult] using
      Runs.seq (Runs.seq hzero hinitialize) hloop
  exact
    ⟨final, hrun, hfinalRemaining, hfinalSource,
      by simpa [installRow] using hfinalWord,
      hfinalBase, hfinalChunkCount, hfinalChild⟩

private theorem fieldBase_pos
    {tm : TM workTapeCount}
    (instanceData : NeighborhoodProgram.ResidueInstance tm) :
    0 < Representation.fieldBase instanceData := by
  unfold Representation.fieldBase Representation.digitBase
    CandidateParameters.domainSize
  exact Nat.pow_pos
    (TreeEval.CookMertz.PrimeGrouped.Logarithmic.domainSize_pos _ _)

private theorem chunkCount_pos
    {tm : TM workTapeCount}
    (instanceData : NeighborhoodProgram.ResidueInstance tm) :
    0 <
      TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
        (payloadWidth tm instanceData.blockLength)
        (graphFanIn workTapeCount) := by
  apply
    TreeEval.CookMertz.GroupedExtension.LogarithmicParameters.chunkCount_pos
  change
    0 <
      ComputationGraph.CompactEncoding.width
        instanceData.blockLength tm.Q
  rw [ComputationGraph.CompactEncoding.width_eq]
  have hcard : 0 < Fintype.card tm.Q :=
    Fintype.card_pos_iff.mpr ⟨tm.qstart⟩
  omega

private theorem query_source_digit_eq
    {tm : TM workTapeCount}
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (interval : Fin instanceData.horizon)
    (child : Fin (graphFanIn workTapeCount))
    (store : Store)
    (hquery :
      Representation.QueryState regs instanceData
        (NeighborhoodScheduler.run
          (NeighborhoodScheduler.Decision.queryInitial
            (ProviderRootInitialization.providerRoot
              instanceData interval child)))
        store)
    (chunk :
      Fin
        (TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
          (payloadWidth tm instanceData.blockLength)
          (graphFanIn workTapeCount))) :
    PackedDigits.digit
        (Representation.fieldBase instanceData)
        (store (resultBankRegisters regs).word)
        (providerCoordinate
          (TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
            (payloadWidth tm instanceData.blockLength)
            (graphFanIn workTapeCount))
          (graphFanIn workTapeCount) chunk.val) =
      ProviderResultDecoding.resultResidues
        tm instanceData interval child chunk := by
  simpa [ProviderResultDecoding.resultResidues,
    NeighborhoodProgram.residueBankIndex,
    providerCoordinate, resultBankRegisters, resultBankMap,
    NeighborhoodTrial.Registers.layout] using
    hquery.bank
      (Fin.last (graphFanIn workTapeCount)) chunk

theorem collectCurrentResult_runs_with_provider_row_internal
    {tm : TM workTapeCount}
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (interval : Fin instanceData.horizon)
    (child : Fin (graphFanIn workTapeCount))
    (store : Store)
    (word : ℕ)
    (hquery :
      Representation.QueryState regs instanceData
        (NeighborhoodScheduler.run
          (NeighborhoodScheduler.Decision.queryInitial
            (ProviderRootInitialization.providerRoot
              instanceData interval child)))
        store)
    (hframe :
      SearchProgram.InputFrame
        controller regs.footprint instanceData.x store)
    (hinputLength :
      store controller.inputLength = instanceData.x.length)
    (hone : store controller.one = 1)
    (hguess : store controller.guess = guess)
    (hsuccess : store controller.success = interval.val)
    (hchild : store controller.verdict = child.val)
    (hword : store controller.hasNext = word) :
    ∃ final,
      Runs
        (collectCurrentResult workTapeCount controller regs)
        store final ∧
      Representation.Parameters regs instanceData final ∧
      SearchProgram.InputFrame
        controller regs.footprint instanceData.x final ∧
      final controller.inputLength = instanceData.x.length ∧
      final controller.one = 1 ∧
      final controller.guess = guess ∧
      final controller.success = interval.val ∧
      final controller.verdict = child.val ∧
      final controller.hasNext =
        installRow
          (Representation.fieldBase instanceData)
          (TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
            (payloadWidth tm instanceData.blockLength)
            (graphFanIn workTapeCount))
          child.val
          (providerResidue tm instanceData interval child)
          word ∧
      (∀ chunk,
        PackedDigits.digit
            (Representation.fieldBase instanceData)
            (final controller.hasNext)
            (providerCoordinate
              (TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
                (payloadWidth tm instanceData.blockLength)
                (graphFanIn workTapeCount))
              child.val chunk.val) =
          ProviderResultDecoding.resultResidues
            tm instanceData interval child chunk) ∧
      (∀ (targetChild : Fin (graphFanIn workTapeCount)),
        targetChild ≠ child →
        ∀ (targetChunk :
          Fin
            (TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
              (payloadWidth tm instanceData.blockLength)
              (graphFanIn workTapeCount))),
          PackedDigits.digit
              (Representation.fieldBase instanceData)
              (final controller.hasNext)
              (providerCoordinate
                (TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
                  (payloadWidth tm instanceData.blockLength)
                  (graphFanIn workTapeCount))
                targetChild.val targetChunk.val) =
            PackedDigits.digit
              (Representation.fieldBase instanceData) word
              (providerCoordinate
                (TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
                  (payloadWidth tm instanceData.blockLength)
                  (graphFanIn workTapeCount))
                targetChild.val targetChunk.val)) := by
  let base := Representation.fieldBase instanceData
  let count :=
    TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
      (payloadWidth tm instanceData.blockLength)
      (graphFanIn workTapeCount)
  let sourceWord := store (resultBankRegisters regs).word
  have hbase : 0 < base := fieldBase_pos instanceData
  have hcount : 0 < count := chunkCount_pos instanceData
  have hsourceBase :
      store (resultBankRegisters regs).base = base := by
    simpa [base, resultBankRegisters, resultBankMap] using
      hquery.parameters.bankBase_eq
  obtain
    ⟨final, hrun, _, _, hfinalWord, hfinalBase,
      hfinalCount, hfinalChild⟩ :=
    collectCurrentResult_runs_internal
      workTapeCount controller regs count child.val
      sourceWord base word hbase store
      (by simpa [count] using hquery.parameters.chunkCount_eq)
      hchild rfl hsourceBase hword
  have hvalue
      (chunk : ℕ) (hchunk : chunk < count) :
      PackedDigits.digit base sourceWord
          (providerCoordinate count
            (graphFanIn workTapeCount) chunk) =
        providerResidue tm instanceData interval child chunk := by
    let finiteChunk : Fin count := ⟨chunk, hchunk⟩
    have hchunk' :
        chunk <
          TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
            (payloadWidth tm instanceData.blockLength)
            (graphFanIn workTapeCount) := by
      simpa [count] using hchunk
    rw [providerResidue, dif_pos hchunk']
    simpa [base, count, sourceWord, finiteChunk] using
      query_source_digit_eq
        regs instanceData interval child store hquery finiteChunk
  have hproviderBound :
      ∀ chunk, chunk < count →
        providerResidue tm instanceData interval child chunk <
          base := by
    intro chunk hchunk
    rw [← hvalue chunk hchunk]
    exact PackedDigits.digit_lt hbase
  have hsemanticWord :
      final controller.hasNext =
        installRow base count child.val
          (providerResidue tm instanceData interval child) word := by
    rw [hfinalWord]
    unfold installRow
    apply installRowFrom_congr
    exact hvalue
  have hparameters :
      Representation.Parameters regs instanceData final :=
    collectCurrentResult_preserves_parameters
      controller regs instanceData store final hrun hquery.parameters
      (by simpa [base] using hfinalBase)
      (by simpa [count] using hfinalCount)
  have hfinalFrame :
      SearchProgram.InputFrame
        controller regs.footprint instanceData.x final :=
    NeighborhoodTrial.Registers.runs_preserves_inputFrame
      regs
      (collectCurrentResult_writesWithin_internal
        workTapeCount controller regs)
      hrun hframe
  have hpreserveController
      (slot : Fin 17) (hne : slot ≠ 5) :
      final (controller.index slot) =
        store (controller.index slot) :=
    collectCurrentResult_controller_eq
      workTapeCount controller regs store final hrun slot hne
  refine
    ⟨final, hrun, hparameters, hfinalFrame,
      (hpreserveController 0 (by decide)).trans hinputLength,
      (hpreserveController 14 (by decide)).trans hone,
      (hpreserveController 2 (by decide)).trans hguess,
      (hpreserveController 3 (by decide)).trans hsuccess,
      hfinalChild, ?_, ?_, ?_⟩
  · simpa [base, count] using hsemanticWord
  · intro chunk
    rw [hsemanticWord]
    have hrow :=
      installRow_digit_eq
        (base := base) (chunkCount := count)
        (child := child.val) (word := word)
        hbase chunk.isLt hproviderBound
    calc
      PackedDigits.digit
            (Representation.fieldBase instanceData)
            (installRow base count child.val
              (providerResidue tm instanceData interval child) word)
            (providerCoordinate count child.val chunk.val) =
          providerResidue
            tm instanceData interval child chunk.val := by
        simpa [base, count] using hrow
      _ = ProviderResultDecoding.resultResidues
            tm instanceData interval child chunk := by
        unfold providerResidue
        rw [dif_pos chunk.isLt]
  · intro targetChild hne targetChunk
    rw [hsemanticWord]
    exact
      installRow_digit_ne_child
        (base := base) (chunkCount := count)
        (child := child.val) (word := word)
        (targetChild := targetChild.val)
        (targetChunk := targetChunk.val)
        hbase hcount targetChunk.isLt
        (fun heq => hne (Fin.ext heq)) hproviderBound

theorem collectChild_runs_internal
    {tm : TM workTapeCount}
    (order : FiniteEncoding.StateOrder tm)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (combine : Cmd)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (code :
      Fin
        (3 ^
          NeighborhoodGraph.Guess.Enumeration.movementCount
            workTapeCount instanceData.horizon))
    (interval : Fin instanceData.horizon)
    (child : Fin (graphFanIn workTapeCount))
    (store : Store)
    (word : ℕ)
    (hcombineWrites :
      Footprint.CmdWritesWithin regs.layout.footprint combine)
    (hcombine : SchedulerStep.CombineSpec tm order regs combine)
    (hencoding :
      instanceData.encoding =
        FiniteEncoding.ofStateOrder order instanceData.blockLength)
    (hguess :
      instanceData.guess =
        NeighborhoodGraph.Guess.Enumeration.candidateGuess code)
    (hstoreGuess : store controller.guess = code.val)
    (hstoreInterval : store controller.success = interval.val)
    (hparameters :
      Representation.Parameters regs instanceData store)
    (hframe :
      SearchProgram.InputFrame
        controller regs.footprint instanceData.x store)
    (hinputLength :
      store controller.inputLength = instanceData.x.length)
    (hone : store controller.one = 1)
    (hword : store controller.hasNext = word) :
    ∃ final,
      Runs
        (collectChild tm order controller regs combine child)
        store final ∧
      Representation.Parameters regs instanceData final ∧
      SearchProgram.InputFrame
        controller regs.footprint instanceData.x final ∧
      final controller.inputLength = instanceData.x.length ∧
      final controller.one = 1 ∧
      final controller.guess = code.val ∧
      final controller.success = interval.val ∧
      final controller.verdict = child.val ∧
      final controller.hasNext =
        installRow
          (Representation.fieldBase instanceData)
          (TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
            (payloadWidth tm instanceData.blockLength)
            (graphFanIn workTapeCount))
          child.val
          (providerResidue tm instanceData interval child)
          word ∧
      (∀ chunk,
        PackedDigits.digit
            (Representation.fieldBase instanceData)
            (final controller.hasNext)
            (providerCoordinate
              (TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
                (payloadWidth tm instanceData.blockLength)
                (graphFanIn workTapeCount))
              child.val chunk.val) =
          ProviderResultDecoding.resultResidues
            tm instanceData interval child chunk) ∧
      (∀ (targetChild : Fin (graphFanIn workTapeCount)),
        targetChild ≠ child →
        ∀ (targetChunk :
          Fin
            (TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
              (payloadWidth tm instanceData.blockLength)
              (graphFanIn workTapeCount))),
          PackedDigits.digit
              (Representation.fieldBase instanceData)
              (final controller.hasNext)
              (providerCoordinate
                (TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
                  (payloadWidth tm instanceData.blockLength)
                  (graphFanIn workTapeCount))
                targetChild.val targetChunk.val) =
            PackedDigits.digit
              (Representation.fieldBase instanceData) word
              (providerCoordinate
                (TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
                  (payloadWidth tm instanceData.blockLength)
                  (graphFanIn workTapeCount))
                targetChild.val targetChunk.val)) := by
  let selected :=
    (Basic.imm controller.verdict child.val).exec store
  have hcursor :
      Runs (.basic (.imm controller.verdict child.val))
        store selected :=
    Runs.basic _ _
  have hcursorWrites :
      Footprint.CmdWritesWithin regs.footprint
        (.basic (.imm controller.verdict child.val)) := by
    change controller.verdict ∈ regs.footprint
    apply Finset.mem_union_right
    simp [NeighborhoodTrial.Registers.outputFootprint]
  have hselectedWorkspace
      (slot : Fin 34) :
      selected (regs.index slot) = store (regs.index slot) := by
    simp [selected, Basic.exec, regs.index_ne_controller]
  have hselectedParameters :
      Representation.Parameters regs instanceData selected := by
    constructor
    · exact (hselectedWorkspace 2).trans hparameters.blockLength_eq
    · exact (hselectedWorkspace 3).trans hparameters.horizon_eq
    · exact (hselectedWorkspace 8).trans hparameters.digitBase_eq
    · exact (hselectedWorkspace 14).trans hparameters.bankBase_eq
    · exact (hselectedWorkspace 13).trans hparameters.frameBase_eq
    · exact (hselectedWorkspace 7).trans hparameters.chunkCount_eq
    · exact
        (hselectedWorkspace 15).trans
          hparameters.bankDigitCount_eq
    · exact (hselectedWorkspace 24).trans hparameters.modulus_eq
    · exact
        (hselectedWorkspace 16).trans hparameters.modulusPred_eq
  have hselectedFrame :
      SearchProgram.InputFrame
        controller regs.footprint instanceData.x selected :=
    NeighborhoodTrial.Registers.runs_preserves_inputFrame
      regs hcursorWrites hcursor hframe
  have hselectedController
      (slot : Fin 17) (hne : slot ≠ 4) :
      selected (controller.index slot) =
        store (controller.index slot) := by
    simp [selected, Basic.exec,
      SearchProgram.Registers.index_inj_iff, hne]
  have hselectedChild :
      selected controller.verdict = child.val := by
    simp [selected, Basic.exec]
  obtain
    ⟨afterQuery, hqueryRun, hquery, hqueryFrame,
      hqueryInputLength, hqueryOne, hqueryGuess,
      hqueryInterval, hqueryChild⟩ :=
    ProviderQueryEvaluation.evaluate_runs
      order controller regs combine instanceData code interval child
      selected hcombineWrites hcombine hencoding hguess
      ((hselectedController 2 (by decide)).trans hstoreGuess)
      ((hselectedController 3 (by decide)).trans hstoreInterval)
      hselectedChild hselectedParameters hselectedFrame
      ((hselectedController 0 (by decide)).trans hinputLength)
      ((hselectedController 14 (by decide)).trans hone)
  have hqueryWord :
      afterQuery controller.hasNext = word := by
    have hpreserve :
        afterQuery controller.hasNext =
          selected controller.hasNext := by
      apply Footprint.runs_eq_outside
        (ProviderQueryEvaluation.evaluate_writesWithin
          tm order controller regs combine hcombineWrites)
        hqueryRun
      exact fun hlayout =>
        Finset.disjoint_left.mp
          (NeighborhoodTrial.Registers.layout_disjoint_controller regs)
          hlayout (controller.index_mem_footprint 5)
    exact hpreserve.trans
      ((hselectedController 5 (by decide)).trans hword)
  obtain
    ⟨final, hcollectRun, hfinalParameters, hfinalFrame,
      hfinalInputLength, hfinalOne, hfinalGuess,
      hfinalInterval, hfinalChild, hfinalWord,
      hfinalRow, hfinalOtherRows⟩ :=
    collectCurrentResult_runs_with_provider_row_internal
      controller regs instanceData interval child afterQuery word
      hquery hqueryFrame hqueryInputLength hqueryOne hqueryGuess
      hqueryInterval hqueryChild hqueryWord
  have hrun :
      Runs (collectChild tm order controller regs combine child)
        store final := by
    simpa only [collectChild, Cmd.seqList] using
      Runs.seq hcursor (Runs.seq hqueryRun hcollectRun)
  exact
    ⟨final, hrun, hfinalParameters, hfinalFrame,
      hfinalInputLength, hfinalOne, hfinalGuess,
      hfinalInterval, hfinalChild, hfinalWord,
      hfinalRow, hfinalOtherRows⟩

private theorem collectChildren_runs_internal
    {tm : TM workTapeCount}
    (order : FiniteEncoding.StateOrder tm)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (combine : Cmd)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (code :
      Fin
        (3 ^
          NeighborhoodGraph.Guess.Enumeration.movementCount
            workTapeCount instanceData.horizon))
    (interval : Fin instanceData.horizon)
    (list : List (Fin (graphFanIn workTapeCount)))
    (store : Store)
    (word : ℕ)
    (hcombineWrites :
      Footprint.CmdWritesWithin regs.layout.footprint combine)
    (hcombine : SchedulerStep.CombineSpec tm order regs combine)
    (hencoding :
      instanceData.encoding =
        FiniteEncoding.ofStateOrder order instanceData.blockLength)
    (hguess :
      instanceData.guess =
        NeighborhoodGraph.Guess.Enumeration.candidateGuess code)
    (hnodup : list.Nodup)
    (hstoreGuess : store controller.guess = code.val)
    (hstoreInterval : store controller.success = interval.val)
    (hparameters :
      Representation.Parameters regs instanceData store)
    (hframe :
      SearchProgram.InputFrame
        controller regs.footprint instanceData.x store)
    (hinputLength :
      store controller.inputLength = instanceData.x.length)
    (hone : store controller.one = 1)
    (hword : store controller.hasNext = word) :
    ∃ final,
      Runs
        (Cmd.seqList
          (list.map
            (collectChild tm order controller regs combine)))
        store final ∧
      Representation.Parameters regs instanceData final ∧
      SearchProgram.InputFrame
        controller regs.footprint instanceData.x final ∧
      final controller.inputLength = instanceData.x.length ∧
      final controller.one = 1 ∧
      final controller.guess = code.val ∧
      final controller.success = interval.val ∧
      final controller.hasNext =
        installChildren
          (Representation.fieldBase instanceData)
          (TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
            (payloadWidth tm instanceData.blockLength)
            (graphFanIn workTapeCount))
          (fun child =>
            providerResidue tm instanceData interval child)
          list word ∧
      (∀ targetChild, targetChild ∈ list →
        ∀ (targetChunk :
          Fin
            (TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
              (payloadWidth tm instanceData.blockLength)
              (graphFanIn workTapeCount))),
          PackedDigits.digit
              (Representation.fieldBase instanceData)
              (final controller.hasNext)
              (providerCoordinate
                (TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
                  (payloadWidth tm instanceData.blockLength)
                  (graphFanIn workTapeCount))
                targetChild.val targetChunk.val) =
            ProviderResultDecoding.resultResidues
              tm instanceData interval targetChild targetChunk) ∧
      (∀ targetChild, targetChild ∉ list →
        ∀ (targetChunk :
          Fin
            (TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
              (payloadWidth tm instanceData.blockLength)
              (graphFanIn workTapeCount))),
          PackedDigits.digit
              (Representation.fieldBase instanceData)
              (final controller.hasNext)
              (providerCoordinate
                (TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
                  (payloadWidth tm instanceData.blockLength)
                  (graphFanIn workTapeCount))
                targetChild.val targetChunk.val) =
            PackedDigits.digit
              (Representation.fieldBase instanceData) word
              (providerCoordinate
                (TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
                  (payloadWidth tm instanceData.blockLength)
                  (graphFanIn workTapeCount))
                targetChild.val targetChunk.val)) := by
  induction list generalizing store word with
  | nil =>
      refine
        ⟨store, Runs.skip store, hparameters, hframe,
          hinputLength, hone, hstoreGuess, hstoreInterval,
          ?_, ?_, ?_⟩
      · simpa [installChildren] using hword
      · intro targetChild hmem
        simp at hmem
      · intro targetChild _ targetChunk
        rw [hword]
  | cons child rest ih =>
      have hrestNodup : rest.Nodup := hnodup.tail
      have hchildNotMem : child ∉ rest := hnodup.notMem
      obtain
        ⟨middle, hchildRun, hmiddleParameters, hmiddleFrame,
          hmiddleInputLength, hmiddleOne, hmiddleGuess,
          hmiddleInterval, _, hmiddleWord, hmiddleRow,
          hmiddleOtherRows⟩ :=
        collectChild_runs_internal
          order controller regs combine instanceData code interval
          child store word hcombineWrites hcombine hencoding hguess
          hstoreGuess hstoreInterval hparameters hframe
          hinputLength hone hword
      cases rest with
      | nil =>
          refine
            ⟨middle, ?_, hmiddleParameters, hmiddleFrame,
              hmiddleInputLength, hmiddleOne, hmiddleGuess,
              hmiddleInterval, ?_, ?_, ?_⟩
          · simpa [Cmd.seqList] using hchildRun
          · simpa [installChildren] using hmiddleWord
          · intro targetChild hmem targetChunk
            have heq : targetChild = child := by
              simpa using hmem
            subst targetChild
            exact hmiddleRow targetChunk
          · intro targetChild hmem targetChunk
            apply hmiddleOtherRows targetChild
            intro heq
            subst targetChild
            exact hmem (by simp)
      | cons next tail =>
          let nextWord :=
            installRow
              (Representation.fieldBase instanceData)
              (TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
                (payloadWidth tm instanceData.blockLength)
                (graphFanIn workTapeCount))
              child.val
              (providerResidue tm instanceData interval child)
              word
          obtain
            ⟨final, hrestRun, hfinalParameters, hfinalFrame,
              hfinalInputLength, hfinalOne, hfinalGuess,
              hfinalInterval, hfinalWord, hfinalRows,
              hfinalOutside⟩ :=
            ih (store := middle) (word := nextWord)
              hrestNodup hmiddleGuess hmiddleInterval
              hmiddleParameters hmiddleFrame hmiddleInputLength
              hmiddleOne
              (by simpa [nextWord] using hmiddleWord)
          have hrun :
              Runs
                (Cmd.seqList
                  ((child :: next :: tail).map
                    (collectChild
                      tm order controller regs combine)))
                store final := by
            simpa only [List.map_cons, Cmd.seqList] using
              Runs.seq hchildRun hrestRun
          refine
            ⟨final, hrun, hfinalParameters, hfinalFrame,
              hfinalInputLength, hfinalOne, hfinalGuess,
              hfinalInterval, ?_, ?_, ?_⟩
          · simpa [installChildren, nextWord] using hfinalWord
          · intro targetChild hmem targetChunk
            by_cases heq : targetChild = child
            · subst targetChild
              calc
                PackedDigits.digit
                      (Representation.fieldBase instanceData)
                      (final controller.hasNext)
                      (providerCoordinate
                        (TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
                          (payloadWidth tm instanceData.blockLength)
                          (graphFanIn workTapeCount))
                        child.val targetChunk.val) =
                    PackedDigits.digit
                      (Representation.fieldBase instanceData)
                      (middle controller.hasNext)
                      (providerCoordinate
                        (TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
                          (payloadWidth tm instanceData.blockLength)
                          (graphFanIn workTapeCount))
                        child.val targetChunk.val) := by
                  rw [hmiddleWord]
                  exact hfinalOutside child hchildNotMem targetChunk
                _ = ProviderResultDecoding.resultResidues
                      tm instanceData interval child targetChunk :=
                  hmiddleRow targetChunk
            · apply hfinalRows targetChild
              simpa [heq] using hmem
          · intro targetChild hmem targetChunk
            have htargetNe : targetChild ≠ child := by
              intro heq
              subst targetChild
              exact hmem (by simp)
            calc
              PackedDigits.digit
                    (Representation.fieldBase instanceData)
                    (final controller.hasNext)
                    (providerCoordinate
                      (TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
                        (payloadWidth tm instanceData.blockLength)
                        (graphFanIn workTapeCount))
                      targetChild.val targetChunk.val) =
                  PackedDigits.digit
                    (Representation.fieldBase instanceData)
                    (middle controller.hasNext)
                    (providerCoordinate
                      (TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
                        (payloadWidth tm instanceData.blockLength)
                        (graphFanIn workTapeCount))
                      targetChild.val targetChunk.val) := by
                rw [hmiddleWord]
                apply hfinalOutside targetChild
                intro htargetMem
                exact hmem (by simp [htargetMem])
              _ = PackedDigits.digit
                    (Representation.fieldBase instanceData) word
                    (providerCoordinate
                      (TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
                        (payloadWidth tm instanceData.blockLength)
                        (graphFanIn workTapeCount))
                      targetChild.val targetChunk.val) :=
                hmiddleOtherRows targetChild htargetNe targetChunk

theorem collect_runs_internal
    {tm : TM workTapeCount}
    (order : FiniteEncoding.StateOrder tm)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (combine : Cmd)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (code :
      Fin
        (3 ^
          NeighborhoodGraph.Guess.Enumeration.movementCount
            workTapeCount instanceData.horizon))
    (interval : Fin instanceData.horizon)
    (store : Store)
    (hcombineWrites :
      Footprint.CmdWritesWithin regs.layout.footprint combine)
    (hcombine : SchedulerStep.CombineSpec tm order regs combine)
    (hencoding :
      instanceData.encoding =
        FiniteEncoding.ofStateOrder order instanceData.blockLength)
    (hguess :
      instanceData.guess =
        NeighborhoodGraph.Guess.Enumeration.candidateGuess code)
    (hstoreGuess : store controller.guess = code.val)
    (hstoreInterval : store controller.success = interval.val)
    (hparameters :
      Representation.Parameters regs instanceData store)
    (hframe :
      SearchProgram.InputFrame
        controller regs.footprint instanceData.x store)
    (hinputLength :
      store controller.inputLength = instanceData.x.length)
    (hone : store controller.one = 1) :
    ∃ final,
      Runs (collect tm order controller regs combine) store final ∧
      Representation.Parameters regs instanceData final ∧
      SearchProgram.InputFrame
        controller regs.footprint instanceData.x final ∧
      final controller.inputLength = instanceData.x.length ∧
      final controller.one = 1 ∧
      final controller.guess = code.val ∧
      final controller.success = interval.val ∧
      final controller.verdict = graphFanIn workTapeCount ∧
      final controller.hasNext =
        collectedWord
          (Representation.fieldBase instanceData)
          (TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
            (payloadWidth tm instanceData.blockLength)
            (graphFanIn workTapeCount))
          (fun child =>
            providerResidue tm instanceData interval child) ∧
      ∀ child chunk,
        PackedDigits.digit
            (Representation.fieldBase instanceData)
            (final controller.hasNext)
            (providerCoordinate
              (TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
                (payloadWidth tm instanceData.blockLength)
                (graphFanIn workTapeCount))
              child.val chunk.val) =
          ProviderResultDecoding.resultResidues
            tm instanceData interval child chunk := by
  let cleared :=
    (Basic.imm controller.hasNext 0).exec store
  have hclear :
      Runs (.basic (.imm controller.hasNext 0)) store cleared :=
    Runs.basic _ _
  have hclearWrites :
      Footprint.CmdWritesWithin regs.footprint
        (.basic (.imm controller.hasNext 0)) := by
    change controller.hasNext ∈ regs.footprint
    apply Finset.mem_union_right
    simp [NeighborhoodTrial.Registers.outputFootprint]
  have hclearedWorkspace
      (slot : Fin 34) :
      cleared (regs.index slot) = store (regs.index slot) := by
    simp [cleared, Basic.exec, regs.index_ne_controller]
  have hclearedParameters :
      Representation.Parameters regs instanceData cleared := by
    constructor
    · exact (hclearedWorkspace 2).trans hparameters.blockLength_eq
    · exact (hclearedWorkspace 3).trans hparameters.horizon_eq
    · exact (hclearedWorkspace 8).trans hparameters.digitBase_eq
    · exact (hclearedWorkspace 14).trans hparameters.bankBase_eq
    · exact (hclearedWorkspace 13).trans hparameters.frameBase_eq
    · exact (hclearedWorkspace 7).trans hparameters.chunkCount_eq
    · exact
        (hclearedWorkspace 15).trans
          hparameters.bankDigitCount_eq
    · exact (hclearedWorkspace 24).trans hparameters.modulus_eq
    · exact
        (hclearedWorkspace 16).trans hparameters.modulusPred_eq
  have hclearedFrame :
      SearchProgram.InputFrame
        controller regs.footprint instanceData.x cleared :=
    NeighborhoodTrial.Registers.runs_preserves_inputFrame
      regs hclearWrites hclear hframe
  have hclearedController
      (slot : Fin 17) (hne : slot ≠ 5) :
      cleared (controller.index slot) =
        store (controller.index slot) := by
    simp [cleared, Basic.exec,
      SearchProgram.Registers.index_inj_iff, hne]
  have hclearedWord :
      cleared controller.hasNext = 0 := by
    simp [cleared, Basic.exec]
  obtain
    ⟨middle, hchildrenRun, hmiddleParameters, hmiddleFrame,
      hmiddleInputLength, hmiddleOne, hmiddleGuess,
      hmiddleInterval, hmiddleWord, hmiddleRows, _⟩ :=
    collectChildren_runs_internal
      order controller regs combine instanceData code interval
      (children workTapeCount) cleared 0 hcombineWrites hcombine
      hencoding hguess (by
        exact List.nodup_finRange _)
      ((hclearedController 2 (by decide)).trans hstoreGuess)
      ((hclearedController 3 (by decide)).trans hstoreInterval)
      hclearedParameters hclearedFrame
      ((hclearedController 0 (by decide)).trans hinputLength)
      ((hclearedController 14 (by decide)).trans hone)
      hclearedWord
  let final :=
    (Basic.imm controller.verdict
      (graphFanIn workTapeCount)).exec middle
  have hfinish :
      Runs
        (.basic
          (.imm controller.verdict (graphFanIn workTapeCount)))
        middle final :=
    Runs.basic _ _
  have hfinishWrites :
      Footprint.CmdWritesWithin regs.footprint
        (.basic
          (.imm controller.verdict
            (graphFanIn workTapeCount))) := by
    change controller.verdict ∈ regs.footprint
    apply Finset.mem_union_right
    simp [NeighborhoodTrial.Registers.outputFootprint]
  have hfinalWorkspace
      (slot : Fin 34) :
      final (regs.index slot) = middle (regs.index slot) := by
    simp [final, Basic.exec, regs.index_ne_controller]
  have hfinalParameters :
      Representation.Parameters regs instanceData final := by
    constructor
    · exact
        (hfinalWorkspace 2).trans
          hmiddleParameters.blockLength_eq
    · exact
        (hfinalWorkspace 3).trans
          hmiddleParameters.horizon_eq
    · exact
        (hfinalWorkspace 8).trans
          hmiddleParameters.digitBase_eq
    · exact
        (hfinalWorkspace 14).trans
          hmiddleParameters.bankBase_eq
    · exact
        (hfinalWorkspace 13).trans
          hmiddleParameters.frameBase_eq
    · exact
        (hfinalWorkspace 7).trans
          hmiddleParameters.chunkCount_eq
    · exact
        (hfinalWorkspace 15).trans
          hmiddleParameters.bankDigitCount_eq
    · exact
        (hfinalWorkspace 24).trans
          hmiddleParameters.modulus_eq
    · exact
        (hfinalWorkspace 16).trans
          hmiddleParameters.modulusPred_eq
  have hfinalFrame :
      SearchProgram.InputFrame
        controller regs.footprint instanceData.x final :=
    NeighborhoodTrial.Registers.runs_preserves_inputFrame
      regs hfinishWrites hfinish hmiddleFrame
  have hfinalController
      (slot : Fin 17) (hne : slot ≠ 4) :
      final (controller.index slot) =
        middle (controller.index slot) := by
    simp [final, Basic.exec,
      SearchProgram.Registers.index_inj_iff, hne]
  have hfinalVerdict :
      final controller.verdict = graphFanIn workTapeCount := by
    simp [final, Basic.exec]
  have hrun :
      Runs (collect tm order controller regs combine) store final := by
    simpa only [collect, Cmd.seqList] using
      Runs.seq hclear (Runs.seq hchildrenRun hfinish)
  refine
    ⟨final, hrun, hfinalParameters, hfinalFrame,
      (hfinalController 0 (by decide)).trans hmiddleInputLength,
      (hfinalController 14 (by decide)).trans hmiddleOne,
      (hfinalController 2 (by decide)).trans hmiddleGuess,
      (hfinalController 3 (by decide)).trans hmiddleInterval,
      hfinalVerdict, ?_, ?_⟩
  · rw [hfinalController 5 (by decide)]
    simpa [collectedWord] using hmiddleWord
  · intro child chunk
    rw [hfinalController 5 (by decide)]
    exact hmiddleRows child (by simp [children]) chunk

theorem decodedCollectedVector_eq_results_internal
    (tm : TM workTapeCount)
    (controller : SearchProgram.Registers)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (interval : Fin instanceData.horizon)
    (store : Store)
    (hresidues :
      ∀ child chunk,
        PackedDigits.digit
            (Representation.fieldBase instanceData)
            (store controller.hasNext)
            (providerCoordinate
              (TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
                (payloadWidth tm instanceData.blockLength)
                (graphFanIn workTapeCount))
              child.val chunk.val) =
          ProviderResultDecoding.resultResidues
            tm instanceData interval child chunk) :
    decodedCollectedVector tm controller instanceData store =
      fun child =>
        ProviderResultDecoding.decodedResult
          tm instanceData interval child := by
  funext child
  have hstored :
      storedCollectedResidues
          tm controller instanceData store child =
        ProviderResultDecoding.resultResidues
          tm instanceData interval child := by
    funext chunk
    exact hresidues child chunk
  unfold decodedCollectedVector decodedCollectedResult
    ProviderResultDecoding.decodedResult
  rw [hstored]

theorem decodedCollectedVector_eq_expected_internal
    (tm : TM workTapeCount)
    (controller : SearchProgram.Registers)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (interval : Fin instanceData.horizon)
    (store : Store)
    (hresidues :
      ∀ child chunk,
        PackedDigits.digit
            (Representation.fieldBase instanceData)
            (store controller.hasNext)
            (providerCoordinate
              (TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
                (payloadWidth tm instanceData.blockLength)
                (graphFanIn workTapeCount))
              child.val chunk.val) =
          ProviderResultDecoding.resultResidues
            tm instanceData interval child chunk)
    (hprefix :
      ∀ boundary : Fin (instanceData.horizon + 1),
        boundary.val ≤ interval.val →
          ∀ tape : TapeIndex workTapeCount,
            instanceData.guess.derivedCenter tape boundary.val =
              some (NeighborhoodGraph.Guess.actualCenterTrajectory
                tm instanceData.x instanceData.blockLength
                  tape boundary.val)) :
    decodedCollectedVector tm controller instanceData store =
      fun child =>
        ProviderResultDecoding.expectedContent
          tm instanceData interval child := by
  rw [decodedCollectedVector_eq_results_internal
    tm controller instanceData interval store hresidues]
  funext child
  exact ProviderResultDecoding.decodedResult_eq_expectedContent
    instanceData interval child hprefix

theorem providerVector_eq_some_decodedCollectedVector_internal
    (tm : TM workTapeCount)
    (controller : SearchProgram.Registers)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (interval : Fin instanceData.horizon)
    (store : Store)
    (hresidues :
      ∀ child chunk,
        PackedDigits.digit
            (Representation.fieldBase instanceData)
            (store controller.hasNext)
            (providerCoordinate
              (TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
                (payloadWidth tm instanceData.blockLength)
                (graphFanIn workTapeCount))
              child.val chunk.val) =
          ProviderResultDecoding.resultResidues
            tm instanceData interval child chunk)
    (hprefix :
      ∀ boundary : Fin (instanceData.horizon + 1),
        boundary.val ≤ interval.val →
          ∀ tape : TapeIndex workTapeCount,
            instanceData.guess.derivedCenter tape boundary.val =
              some (NeighborhoodGraph.Guess.actualCenterTrajectory
                tm instanceData.x instanceData.blockLength
                  tape boundary.val)) :
    ProviderVectorSemantics.providerVector?
        tm instanceData interval =
      some
        (decodedCollectedVector
          tm controller instanceData store) := by
  apply
    (ProviderVectorSemantics.providerVector_eq_some_iff
      tm instanceData interval
        (decodedCollectedVector
          tm controller instanceData store)).2
  intro child
  have hdecoded :=
    congrFun
      (decodedCollectedVector_eq_results_internal
        tm controller instanceData interval store hresidues)
      child
  rw [hdecoded]
  have hroot :=
    ProviderResultDecoding.providerRoot_eq_graph_predecessorAt
      instanceData interval child hprefix
  rw [ProviderVectorSemantics.queryContent?, hroot]
  exact
    (ProviderResultDecoding.some_decodedResult_eq_schedulerNodeContent
      instanceData interval child
        (NeighborhoodGraph.predecessorAt
          tm instanceData.x instanceData.blockLength
            interval.val child)
      hroot).symm

end Internal
end ProviderVectorCollection
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
