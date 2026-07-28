/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.PackedComputationKernel.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.CombineTerm
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.LocalAssignmentSemantics
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.PackedLocalInitialization
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.PackedLocalOutputChunk
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.PackedLocalRepresentation
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.PackedLocalTrace

/-!
# Fixed packed computation-factor kernel -- proofs
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace PackedComputationKernel
namespace Internal

open RAM Structured
open TreeEval CookMertz

variable {controller : SearchProgram.Registers}

@[simp]
theorem guessCode_val_internal
    {tm : TM workTapeCount}
    (instanceData : NeighborhoodProgram.ResidueInstance tm) :
    (guessCode instanceData).val = instanceData.guessCode := by
  simp [guessCode]

theorem guess_eq_candidateGuess_internal
    {tm : TM workTapeCount}
    (instanceData : NeighborhoodProgram.ResidueInstance tm) :
    instanceData.guess =
      NeighborhoodGraph.Guess.Enumeration.candidateGuess
        (guessCode instanceData) := by
  simpa [guessCode] using instanceData.guess_eq

private theorem computationNodeDigits_fit
    {tm : TM workTapeCount}
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (tape : TapeIndex workTapeCount)
    (slot : NeighborhoodGraph.Slot)
    (interval : Fin instanceData.horizon) :
    ∀ digit ∈
        FrameCodec.nodeDigits
          (show
            NeighborhoodEvaluator.QueryNode
              workTapeCount instanceData.horizon
            from .graph (.computation tape slot interval.val)),
      digit < Representation.digitBase instanceData := by
  have hfanIn :
      NeighborhoodExecutableEvaluation.graphFanIn workTapeCount <
        Representation.digitBase instanceData := by
    simpa [Representation.digitBase,
      NeighborhoodExecutableEvaluation.graphFanIn,
      NeighborhoodEvaluator.fanIn,
      CandidateParameters.fanIn] using
      CandidateParameters.RadixBounds.fanIn_lt_domainSize
        tm.Q workTapeCount instanceData.candidateTime
  have htape :
      workTapeCount + 2 <
        Representation.digitBase instanceData := by
    unfold NeighborhoodExecutableEvaluation.graphFanIn
      NeighborhoodEvaluator.fanIn at hfanIn
    omega
  have hhorizon :
      instanceData.horizon <
        Representation.digitBase instanceData := by
    have hbound :=
      CandidateParameters.RadixBounds.horizon_lt_domainSize
        tm.Q workTapeCount instanceData.candidateTime
    rw [instanceData.horizon_eq]
    simpa [Representation.digitBase] using hbound
  have hfanInMin :
      4 ≤
        NeighborhoodExecutableEvaluation.graphFanIn workTapeCount := by
    simp [NeighborhoodExecutableEvaluation.graphFanIn,
      NeighborhoodEvaluator.fanIn]
  have hbase :
      2 < Representation.digitBase instanceData :=
    lt_of_lt_of_le (by omega) (Nat.le_of_lt hfanIn)
  intro digit hdigit
  simp only [FrameCodec.nodeDigits, List.mem_cons,
    List.mem_nil_iff, or_false] at hdigit
  rcases hdigit with rfl | rfl | rfl | rfl
  · exact hbase
  · exact tape.isLt.trans htape
  · exact slot.toFin.isLt.trans (by omega)
  · exact interval.isLt.trans hhorizon

private theorem digitBase_eq_two_pow_chunkBits
    {tm : TM workTapeCount}
    (instanceData : NeighborhoodProgram.ResidueInstance tm) :
    Representation.digitBase instanceData =
      2 ^
        PrimeGrouped.Logarithmic.chunkBits
          (NeighborhoodExecutableEvaluation.payloadWidth
            tm instanceData.blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount) := by
  unfold Representation.digitBase CandidateParameters.domainSize
    PrimeGrouped.Logarithmic.domainSize
  rw [Representation.payloadWidth_eq_booleanWidth instanceData]
  rfl

private theorem basics_runs
    (ops : List Basic) (store : Store) :
    Runs (Cmd.basics ops) store (Basic.execList ops store) := by
  obtain ⟨cost, space, hexec⟩ :=
    RAM.Structured.Internal.exec_basics_exists ops store
  exact ⟨ops.length, cost, space, hexec⟩

private theorem pop_cmdWritesWithin
    (regs : NeighborhoodProgram.StackRegisters) :
    Footprint.CmdWritesWithin regs.footprint
      (NeighborhoodProgram.pop regs) := by
  unfold NeighborhoodProgram.pop NeighborhoodProgram.popBody
    NeighborhoodProgram.popTestOp
  simp only [Cmd.seqList, Footprint.CmdWritesWithin,
    Footprint.BasicWritesWithin]
  exact
    ⟨regs.index_mem_footprint 3,
      regs.index_mem_footprint 4,
      ⟨regs.index_mem_footprint 0,
        regs.index_mem_footprint 3,
        regs.index_mem_footprint 4⟩,
      regs.index_mem_footprint 0,
      regs.index_mem_footprint 0,
      regs.index_mem_footprint 3⟩

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

/-- Source-write footprint of the destructive local-prefix loop. -/
def dropFootprint
    (regs : NeighborhoodTrial.Registers controller) : Finset ℕ :=
  (stackRegisters regs).footprint ∪
    {(CombineValue.rangeRegisters regs).count}

private theorem dropPrefix_writesWithin
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (dropFootprint regs)
      (dropPrefix regs) := by
  unfold dropPrefix dropBody
  constructor
  · exact cmdWritesWithin_mono
      (smaller := (stackRegisters regs).footprint)
      (larger := dropFootprint regs)
      (by
        intro address haddress
        exact Finset.mem_union_left _ haddress)
      (NeighborhoodProgram.pop (stackRegisters regs))
      (pop_cmdWritesWithin (stackRegisters regs))
  · exact Finset.mem_union_right _
      (Finset.mem_singleton_self _)

private theorem rangeCount_not_mem_stack
    (regs : NeighborhoodTrial.Registers controller) :
    (CombineValue.rangeRegisters regs).count ∉
      (stackRegisters regs).footprint := by
  simp only [NeighborhoodProgram.StackRegisters.footprint,
    Finset.mem_image, Finset.mem_univ, true_and, not_exists]
  intro index heq
  have hindex := regs.injective heq
  change
    PackedLocalHeadScan.bankMap
        (NeighborhoodProgram.BankRegisters.mainMap index) =
      (10 : Fin 34) at hindex
  exact
    (show
      ∀ index : Fin 7,
        PackedLocalHeadScan.bankMap
            (NeighborhoodProgram.BankRegisters.mainMap index) ≠
          (10 : Fin 34) by
      decide)
      index hindex

private theorem rangeOne_not_mem_stack
    (regs : NeighborhoodTrial.Registers controller) :
    (CombineValue.rangeRegisters regs).one ∉
      (stackRegisters regs).footprint := by
  simp only [NeighborhoodProgram.StackRegisters.footprint,
    Finset.mem_image, Finset.mem_univ, true_and, not_exists]
  intro index heq
  have hindex := regs.injective heq
  change
    PackedLocalHeadScan.bankMap
        (NeighborhoodProgram.BankRegisters.mainMap index) =
      (17 : Fin 34) at hindex
  exact
    (show
      ∀ index : Fin 7,
        PackedLocalHeadScan.bankMap
            (NeighborhoodProgram.BankRegisters.mainMap index) ≠
          (17 : Fin 34) by
      decide)
      index hindex

private theorem dropPrefix_runs
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store) (base word count : ℕ)
    (hbase : 0 < base)
    (hword : store (stackRegisters regs).word = word)
    (hbaseValue : store (stackRegisters regs).base = base)
    (hbasePred :
      store (stackRegisters regs).basePred = base - 1)
    (hstackOne : store (stackRegisters regs).one = 1)
    (hcount :
      store (CombineValue.rangeRegisters regs).count = count)
    (hrangeOne :
      store (CombineValue.rangeRegisters regs).one = 1) :
    ∃ final,
      Runs (dropPrefix regs) store final ∧
      final (stackRegisters regs).word =
        PackedDigits.drop base count word ∧
      final (CombineValue.rangeRegisters regs).count = 0 := by
  induction count generalizing store word with
  | zero =>
      refine ⟨store, Runs.whileZero hcount, ?_, hcount⟩
      simpa [PackedDigits.drop] using hword
  | succ count ih =>
      obtain ⟨afterPop, hpop, hpopWord, _hquotient, _htest,
          hpopBase, hpopBasePred, hpopOne⟩ :=
        NeighborhoodProgram.pop_runs (stackRegisters regs) store
          base word hbase hword hbaseValue hbasePred hstackOne
      have hpopCount :
          afterPop (CombineValue.rangeRegisters regs).count =
            count + 1 := by
        rw [Footprint.runs_eq_outside
          (pop_cmdWritesWithin (stackRegisters regs)) hpop]
        · exact hcount
        · exact rangeCount_not_mem_stack regs
      have hpopRangeOne :
          afterPop (CombineValue.rangeRegisters regs).one = 1 := by
        rw [Footprint.runs_eq_outside
          (pop_cmdWritesWithin (stackRegisters regs)) hpop]
        · exact hrangeOne
        · exact rangeOne_not_mem_stack regs
      let afterDecrement :=
        Basic.exec
          (.sub (CombineValue.rangeRegisters regs).count
            (CombineValue.rangeRegisters regs).count
            (CombineValue.rangeRegisters regs).one)
          afterPop
      have hdecrement :
          Runs
            (.basic
              (.sub (CombineValue.rangeRegisters regs).count
                (CombineValue.rangeRegisters regs).count
                (CombineValue.rangeRegisters regs).one))
            afterPop afterDecrement :=
        Runs.basic _ _
      have hdecrementCount :
          afterDecrement (CombineValue.rangeRegisters regs).count =
            count := by
        simp [afterDecrement, Basic.exec, hpopCount, hpopRangeOne]
      have hdecrementWord :
          afterDecrement (stackRegisters regs).word =
            PackedDigits.pop base word := by
        simpa [afterDecrement, Basic.exec,
          stackRegisters, bankRegisters,
          PackedLocalStep.bankRegisters,
          PackedLocalHeadScan.bankRegisters,
          PackedLocalHeadScan.bankMap,
          NeighborhoodProgram.BankRegisters.mainStack,
          NeighborhoodProgram.BankRegisters.mainMap,
          CombineValue.rangeRegisters, regs.injective.eq_iff] using
          hpopWord
      have hdecrementBase :
          afterDecrement (stackRegisters regs).base = base := by
        simpa [afterDecrement, Basic.exec,
          stackRegisters, bankRegisters,
          PackedLocalStep.bankRegisters,
          PackedLocalHeadScan.bankRegisters,
          PackedLocalHeadScan.bankMap,
          NeighborhoodProgram.BankRegisters.mainStack,
          NeighborhoodProgram.BankRegisters.mainMap,
          CombineValue.rangeRegisters, regs.injective.eq_iff] using
          hpopBase
      have hdecrementBasePred :
          afterDecrement (stackRegisters regs).basePred =
            base - 1 := by
        simpa [afterDecrement, Basic.exec,
          stackRegisters, bankRegisters,
          PackedLocalStep.bankRegisters,
          PackedLocalHeadScan.bankRegisters,
          PackedLocalHeadScan.bankMap,
          NeighborhoodProgram.BankRegisters.mainStack,
          NeighborhoodProgram.BankRegisters.mainMap,
          CombineValue.rangeRegisters, regs.injective.eq_iff] using
          hpopBasePred
      have hdecrementStackOne :
          afterDecrement (stackRegisters regs).one = 1 := by
        simpa [afterDecrement, Basic.exec,
          stackRegisters, bankRegisters,
          PackedLocalStep.bankRegisters,
          PackedLocalHeadScan.bankRegisters,
          PackedLocalHeadScan.bankMap,
          NeighborhoodProgram.BankRegisters.mainStack,
          NeighborhoodProgram.BankRegisters.mainMap,
          CombineValue.rangeRegisters, regs.injective.eq_iff] using
          hpopOne
      have hdecrementRangeOne :
          afterDecrement (CombineValue.rangeRegisters regs).one = 1 := by
        simpa [afterDecrement, Basic.exec,
          CombineValue.rangeRegisters, regs.injective.eq_iff] using
          hpopRangeOne
      obtain ⟨final, hloop, hloopWord, hloopCount⟩ :=
        ih afterDecrement (PackedDigits.pop base word)
          hdecrementWord hdecrementBase hdecrementBasePred
          hdecrementStackOne hdecrementCount hdecrementRangeOne
      refine
        ⟨final,
          Runs.whileNonzero (by omega)
            (Runs.seq hpop hdecrement) hloop,
          ?_, hloopCount⟩
      simpa [PackedDigits.drop] using hloopWord

private theorem footprint_slot
    (regs : NeighborhoodTrial.Registers controller)
    (slot : Fin 17) :
    regs.index (PackedLocalStep.writeMap slot) ∈ footprint regs := by
  exact Finset.mem_image.mpr ⟨slot, Finset.mem_univ _, rfl⟩

private theorem footprint_index_not_mem
    (regs : NeighborhoodTrial.Registers controller)
    (slot : Fin 34)
    (hslot :
      ∀ writeSlot : Fin 17,
        PackedLocalStep.writeMap writeSlot ≠ slot) :
    regs.index slot ∉ footprint regs := by
  simp only [footprint, PackedLocalStep.footprint,
    Finset.mem_image, Finset.mem_univ, true_and, not_exists]
  intro writeSlot heq
  exact hslot writeSlot (regs.injective heq)

private theorem controllerGuess_not_mem_footprint
    (regs : NeighborhoodTrial.Registers controller) :
    controller.guess ∉ footprint regs := by
  simp only [footprint, PackedLocalStep.footprint,
    Finset.mem_image, Finset.mem_univ, true_and, not_exists]
  intro writeSlot heq
  exact regs.index_ne_controller
    (PackedLocalStep.writeMap writeSlot) (2 : Fin 17) heq

private theorem copy_writesWithin
    (allowed : Finset ℕ) (destination source : ℕ)
    (hdestination : destination ∈ allowed) :
    Footprint.CmdWritesWithin allowed
      (CombineTerm.copy destination source) := by
  exact ⟨hdestination, hdestination⟩

private theorem stackFootprint_subset
    (regs : NeighborhoodTrial.Registers controller) :
    (stackRegisters regs).footprint ⊆ footprint regs := by
  intro address haddress
  simp only [NeighborhoodProgram.StackRegisters.footprint,
    Finset.mem_image, Finset.mem_univ, true_and] at haddress
  obtain ⟨slot, rfl⟩ := haddress
  fin_cases slot
  · simpa [stackRegisters, bankRegisters,
      PackedLocalStep.bankRegisters,
      PackedLocalHeadScan.bankRegisters,
      PackedLocalHeadScan.bankMap,
      NeighborhoodProgram.BankRegisters.mainStack,
      NeighborhoodProgram.BankRegisters.mainMap] using
      footprint_slot regs (16 : Fin 17)
  · simpa [stackRegisters, bankRegisters,
      PackedLocalStep.bankRegisters,
      PackedLocalHeadScan.bankRegisters,
      PackedLocalHeadScan.bankMap,
      NeighborhoodProgram.BankRegisters.mainStack,
      NeighborhoodProgram.BankRegisters.mainMap] using
      footprint_slot regs (1 : Fin 17)
  · simpa [stackRegisters, bankRegisters,
      PackedLocalStep.bankRegisters,
      PackedLocalHeadScan.bankRegisters,
      PackedLocalHeadScan.bankMap,
      NeighborhoodProgram.BankRegisters.mainStack,
      NeighborhoodProgram.BankRegisters.mainMap] using
      footprint_slot regs (2 : Fin 17)
  · simpa [stackRegisters, bankRegisters,
      PackedLocalStep.bankRegisters,
      PackedLocalHeadScan.bankRegisters,
      PackedLocalHeadScan.bankMap,
      NeighborhoodProgram.BankRegisters.mainStack,
      NeighborhoodProgram.BankRegisters.mainMap] using
      footprint_slot regs (3 : Fin 17)
  · simpa [stackRegisters, bankRegisters,
      PackedLocalStep.bankRegisters,
      PackedLocalHeadScan.bankRegisters,
      PackedLocalHeadScan.bankMap,
      NeighborhoodProgram.BankRegisters.mainStack,
      NeighborhoodProgram.BankRegisters.mainMap] using
      footprint_slot regs (4 : Fin 17)
  · simpa [stackRegisters, bankRegisters,
      PackedLocalStep.bankRegisters,
      PackedLocalHeadScan.bankRegisters,
      PackedLocalHeadScan.bankMap,
      NeighborhoodProgram.BankRegisters.mainStack,
      NeighborhoodProgram.BankRegisters.mainMap] using
      footprint_slot regs (5 : Fin 17)
  · simpa [stackRegisters, bankRegisters,
      PackedLocalStep.bankRegisters,
      PackedLocalHeadScan.bankRegisters,
      PackedLocalHeadScan.bankMap,
      NeighborhoodProgram.BankRegisters.mainStack,
      NeighborhoodProgram.BankRegisters.mainMap] using
      footprint_slot regs (7 : Fin 17)

private theorem dropFootprint_subset
    (regs : NeighborhoodTrial.Registers controller) :
    dropFootprint regs ⊆ footprint regs := by
  intro address haddress
  rcases Finset.mem_union.mp haddress with hstack | hcount
  · exact stackFootprint_subset regs hstack
  · have hcount' :
        address = (CombineValue.rangeRegisters regs).count :=
      Finset.mem_singleton.mp hcount
    subst address
    simpa [CombineValue.rangeRegisters] using
      footprint_slot regs (6 : Fin 17)

private theorem initializeDrop_writesWithin
    (tm : TM workTapeCount)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (footprint regs)
      (initializeDrop tm regs) := by
  simp only [initializeDrop, Cmd.basics]
  exact
    ⟨by
        simpa [bankRegisters, PackedLocalStep.bankRegisters,
          PackedLocalHeadScan.bankRegisters,
          PackedLocalHeadScan.bankMap] using
          footprint_slot regs (7 : Fin 17),
      by
        simpa [CombineValue.rangeRegisters] using
          footprint_slot regs (6 : Fin 17),
      by
        simpa [bankRegisters, PackedLocalStep.bankRegisters,
          PackedLocalHeadScan.bankRegisters,
          PackedLocalHeadScan.bankMap] using
          footprint_slot regs (7 : Fin 17),
      by
        simpa [CombineValue.rangeRegisters] using
          footprint_slot regs (6 : Fin 17),
      by
        simpa [bankRegisters, PackedLocalStep.bankRegisters,
          PackedLocalHeadScan.bankRegisters,
          PackedLocalHeadScan.bankMap] using
          footprint_slot regs (1 : Fin 17),
      by
        simpa [bankRegisters, PackedLocalStep.bankRegisters,
          PackedLocalHeadScan.bankRegisters,
          PackedLocalHeadScan.bankMap] using
          footprint_slot regs (2 : Fin 17),
      by
        simpa [bankRegisters, PackedLocalStep.bankRegisters,
          PackedLocalHeadScan.bankRegisters,
          PackedLocalHeadScan.bankMap] using
          footprint_slot regs (5 : Fin 17)⟩

private theorem finish_writesWithin
    (tm : TM workTapeCount)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (footprint regs) (finish tm regs) := by
  simp only [finish, Cmd.seqList, Footprint.CmdWritesWithin]
  exact
    ⟨copy_writesWithin _ _ _
        (by
          simpa [savedPacked, CombineValue.rangeRegisters] using
            footprint_slot regs (11 : Fin 17)),
      initializeDrop_writesWithin tm regs,
      cmdWritesWithin_mono
        (smaller := dropFootprint regs)
        (larger := footprint regs)
        (dropFootprint_subset regs)
        (dropPrefix regs)
        (dropPrefix_writesWithin regs),
      copy_writesWithin _ _ _
        (by
          simpa [CombineValue.rangeRegisters] using
            footprint_slot regs (6 : Fin 17)),
      copy_writesWithin _ _ _
        (by
          simpa [CombineTerm.packedValue] using
            footprint_slot regs (4 : Fin 17)),
      by
        simpa [PackedLocalOutputChunk.restoreRangeOne,
          CombineValue.rangeRegisters] using
          footprint_slot regs (9 : Fin 17)⟩

private theorem savedPacked_not_mem_dropFootprint
    (regs : NeighborhoodTrial.Registers controller) :
    savedPacked regs ∉ dropFootprint regs := by
  simp only [dropFootprint, Finset.mem_union,
    Finset.mem_singleton, not_or]
  constructor
  · simp only [NeighborhoodProgram.StackRegisters.footprint,
      Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    intro index heq
    have hindex := regs.injective heq
    change
      PackedLocalHeadScan.bankMap
          (NeighborhoodProgram.BankRegisters.mainMap index) =
        (19 : Fin 34) at hindex
    exact
      (show
        ∀ index : Fin 7,
          PackedLocalHeadScan.bankMap
              (NeighborhoodProgram.BankRegisters.mainMap index) ≠
            (19 : Fin 34) by
        decide)
        index hindex
  · exact regs.injective.ne (by decide)

private theorem rangeAccumulator_not_mem_dropFootprint
    (regs : NeighborhoodTrial.Registers controller) :
    (CombineValue.rangeRegisters regs).accumulator ∉
      dropFootprint regs := by
  simp only [dropFootprint, Finset.mem_union,
    Finset.mem_singleton, not_or]
  constructor
  · simp only [NeighborhoodProgram.StackRegisters.footprint,
      Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    intro index heq
    have hindex := regs.injective heq
    change
      PackedLocalHeadScan.bankMap
          (NeighborhoodProgram.BankRegisters.mainMap index) =
        (18 : Fin 34) at hindex
    exact
      (show
        ∀ index : Fin 7,
          PackedLocalHeadScan.bankMap
              (NeighborhoodProgram.BankRegisters.mainMap index) ≠
            (18 : Fin 34) by
        decide)
        index hindex
  · exact regs.injective.ne (by decide)

private theorem finish_runs
    (tm : TM workTapeCount)
    (regs : NeighborhoodTrial.Registers controller)
    (blockLength suffix word packed : ℕ)
    (store : Store)
    (hblock :
      store (Layout.blockLength regs) = blockLength)
    (hword : store (bankRegisters regs).word = word)
    (hsuffix :
      PackedDigits.drop
          (PackedLocalConfiguration.radix tm)
          (PackedLocalConfiguration.digitCount
            workTapeCount blockLength)
          word =
        suffix)
    (hpacked :
      store (CombineTerm.packedValue regs) = packed)
    (hone :
      store (CombineValue.rangeRegisters regs).one = 1) :
    ∃ final,
      Runs (finish tm regs) store final ∧
      final (bankRegisters regs).word = suffix ∧
      final (CombineValue.rangeRegisters regs).count = suffix ∧
      final (CombineTerm.packedValue regs) = packed ∧
      final (CombineValue.rangeRegisters regs).one = 1 ∧
      final (CombineValue.rangeRegisters regs).accumulator =
        store (CombineValue.rangeRegisters regs).accumulator := by
  obtain ⟨saved, hsave, hsaveValue, hsaveOutside⟩ :=
    CombineTerm.copy_runs_internal
      (savedPacked regs) (CombineTerm.packedValue regs) store
      (regs.injective.ne (by decide))
  have hsavedPacked :
      saved (savedPacked regs) = packed :=
    hsaveValue.trans hpacked
  have hsavedWord :
      saved (bankRegisters regs).word = word := by
    rw [hsaveOutside _]
    · exact hword
    · exact regs.injective.ne (by decide)
  have hsavedBlock :
      saved (Layout.blockLength regs) = blockLength := by
    rw [hsaveOutside _]
    · exact hblock
    · exact regs.injective.ne (by decide)
  have hsavedOne :
      saved (CombineValue.rangeRegisters regs).one = 1 := by
    rw [hsaveOutside _]
    · exact hone
    · exact regs.injective.ne (by decide)
  have hsavedAccumulator :
      saved (CombineValue.rangeRegisters regs).accumulator =
        store (CombineValue.rangeRegisters regs).accumulator := by
    rw [hsaveOutside _]
    exact regs.injective.ne (by decide)
  let initialized :=
    Basic.execList
      [.imm (bankRegisters regs).value ((workTapeCount + 2) * 3),
        .mul (CombineValue.rangeRegisters regs).count
          (bankRegisters regs).value (Layout.blockLength regs),
        .imm (bankRegisters regs).value 1,
        .add (CombineValue.rangeRegisters regs).count
          (CombineValue.rangeRegisters regs).count
          (bankRegisters regs).value,
        .imm (bankRegisters regs).base
          (PackedLocalConfiguration.radix tm),
        .imm (bankRegisters regs).basePred
          (PackedLocalConfiguration.radix tm - 1),
        .imm (bankRegisters regs).one 1]
      saved
  have hinitialize :
      Runs (initializeDrop tm regs) saved initialized := by
    simpa [initializeDrop, initialized] using
      basics_runs
        [.imm (bankRegisters regs).value ((workTapeCount + 2) * 3),
          .mul (CombineValue.rangeRegisters regs).count
            (bankRegisters regs).value (Layout.blockLength regs),
          .imm (bankRegisters regs).value 1,
          .add (CombineValue.rangeRegisters regs).count
            (CombineValue.rangeRegisters regs).count
            (bankRegisters regs).value,
          .imm (bankRegisters regs).base
            (PackedLocalConfiguration.radix tm),
          .imm (bankRegisters regs).basePred
            (PackedLocalConfiguration.radix tm - 1),
          .imm (bankRegisters regs).one 1]
        saved
  have hinitializedCount :
      initialized (CombineValue.rangeRegisters regs).count =
        PackedLocalConfiguration.digitCount
          workTapeCount blockLength := by
    simp only [initialized, Basic.execList, Basic.exec]
    simp [bankRegisters, PackedLocalStep.bankRegisters,
      PackedLocalHeadScan.bankRegisters,
      PackedLocalHeadScan.bankMap, CombineValue.rangeRegisters,
      Layout.blockLength, regs.injective.eq_iff, hsavedBlock,
      PackedLocalConfiguration.digitCount,
      PackedLocalConfiguration.tapeSpan]
    ring
  have hinitializedWord :
      initialized (bankRegisters regs).word = word := by
    simpa [initialized, Basic.execList, Basic.exec,
      bankRegisters, PackedLocalStep.bankRegisters,
      PackedLocalHeadScan.bankRegisters,
      PackedLocalHeadScan.bankMap, CombineValue.rangeRegisters,
      Layout.blockLength, regs.injective.eq_iff] using hsavedWord
  have hinitializedBase :
      initialized (stackRegisters regs).base =
        PackedLocalConfiguration.radix tm := by
    change
      initialized (bankRegisters regs).base =
        PackedLocalConfiguration.radix tm
    simp [initialized, Basic.execList, Basic.exec,
      bankRegisters,
      PackedLocalStep.bankRegisters,
      PackedLocalHeadScan.bankRegisters,
      PackedLocalHeadScan.bankMap,
      CombineValue.rangeRegisters, Layout.blockLength,
      regs.injective.eq_iff]
  have hinitializedBasePred :
      initialized (stackRegisters regs).basePred =
        PackedLocalConfiguration.radix tm - 1 := by
    change
      initialized (bankRegisters regs).basePred =
        PackedLocalConfiguration.radix tm - 1
    simp [initialized, Basic.execList, Basic.exec,
      bankRegisters,
      PackedLocalStep.bankRegisters,
      PackedLocalHeadScan.bankRegisters,
      PackedLocalHeadScan.bankMap,
      CombineValue.rangeRegisters, Layout.blockLength,
      regs.injective.eq_iff]
  have hinitializedStackOne :
      initialized (stackRegisters regs).one = 1 := by
    change initialized (bankRegisters regs).one = 1
    simp [initialized, Basic.execList, Basic.exec,
      bankRegisters,
      PackedLocalStep.bankRegisters,
      PackedLocalHeadScan.bankRegisters,
      PackedLocalHeadScan.bankMap,
      CombineValue.rangeRegisters, Layout.blockLength,
      regs.injective.eq_iff]
  have hinitializedRangeOne :
      initialized (CombineValue.rangeRegisters regs).one = 1 := by
    simpa [initialized, Basic.execList, Basic.exec,
      bankRegisters, PackedLocalStep.bankRegisters,
      PackedLocalHeadScan.bankRegisters,
      PackedLocalHeadScan.bankMap, CombineValue.rangeRegisters,
      Layout.blockLength, regs.injective.eq_iff] using hsavedOne
  have hinitializedAccumulator :
      initialized (CombineValue.rangeRegisters regs).accumulator =
        store (CombineValue.rangeRegisters regs).accumulator := by
    simpa [initialized, Basic.execList, Basic.exec,
      bankRegisters, PackedLocalStep.bankRegisters,
      PackedLocalHeadScan.bankRegisters,
      PackedLocalHeadScan.bankMap, CombineValue.rangeRegisters,
      Layout.blockLength, regs.injective.eq_iff] using
      hsavedAccumulator
  obtain ⟨dropped, hdrop, hdropWord, hdropCount⟩ :=
    dropPrefix_runs regs initialized
      (PackedLocalConfiguration.radix tm) word
      (PackedLocalConfiguration.digitCount workTapeCount blockLength)
      (PackedLocalConfiguration.radix_pos tm)
      hinitializedWord hinitializedBase hinitializedBasePred
      hinitializedStackOne hinitializedCount hinitializedRangeOne
  have hdropSuffix :
      dropped (bankRegisters regs).word = suffix := by
    exact hdropWord.trans hsuffix
  have hinitializedSaved :
      initialized (savedPacked regs) = packed := by
    simpa [initialized, Basic.execList, Basic.exec,
      bankRegisters, PackedLocalStep.bankRegisters,
      PackedLocalHeadScan.bankRegisters,
      PackedLocalHeadScan.bankMap, CombineValue.rangeRegisters,
      Layout.blockLength, savedPacked, regs.injective.eq_iff] using
      hsavedPacked
  have hdroppedSaved :
      dropped (savedPacked regs) = packed := by
    rw [Footprint.runs_eq_outside
      (dropPrefix_writesWithin regs) hdrop
      (savedPacked_not_mem_dropFootprint regs)]
    exact hinitializedSaved
  have hdroppedAccumulator :
      dropped (CombineValue.rangeRegisters regs).accumulator =
        store (CombineValue.rangeRegisters regs).accumulator := by
    rw [Footprint.runs_eq_outside
      (dropPrefix_writesWithin regs) hdrop
      (rangeAccumulator_not_mem_dropFootprint regs)]
    exact hinitializedAccumulator
  obtain ⟨counted, hrestoreCount, hcountedValue,
      hcountedOutside⟩ :=
    CombineTerm.copy_runs_internal
      (CombineValue.rangeRegisters regs).count
      (bankRegisters regs).word dropped
      (regs.injective.ne (by decide))
  have hcountedCount :
      counted (CombineValue.rangeRegisters regs).count = suffix :=
    hcountedValue.trans hdropSuffix
  have hcountedWord :
      counted (bankRegisters regs).word = suffix := by
    rw [hcountedOutside _]
    · exact hdropSuffix
    · exact regs.injective.ne (by decide)
  have hcountedSaved :
      counted (savedPacked regs) = packed := by
    rw [hcountedOutside _]
    · exact hdroppedSaved
    · exact regs.injective.ne (by decide)
  have hcountedAccumulator :
      counted (CombineValue.rangeRegisters regs).accumulator =
        store (CombineValue.rangeRegisters regs).accumulator := by
    rw [hcountedOutside _]
    · exact hdroppedAccumulator
    · exact regs.injective.ne (by decide)
  obtain ⟨restored, hrestorePacked, hrestoredPacked,
      hrestoredOutside⟩ :=
    CombineTerm.copy_runs_internal
      (CombineTerm.packedValue regs) (savedPacked regs) counted
      (regs.injective.ne (by decide))
  have hrestoredPackedValue :
      restored (CombineTerm.packedValue regs) = packed :=
    hrestoredPacked.trans hcountedSaved
  have hrestoredCount :
      restored (CombineValue.rangeRegisters regs).count = suffix := by
    rw [hrestoredOutside _]
    · exact hcountedCount
    · exact regs.injective.ne (by decide)
  have hrestoredWord :
      restored (bankRegisters regs).word = suffix := by
    rw [hrestoredOutside _]
    · exact hcountedWord
    · exact regs.injective.ne (by decide)
  have hrestoredAccumulator :
      restored (CombineValue.rangeRegisters regs).accumulator =
        store (CombineValue.rangeRegisters regs).accumulator := by
    rw [hrestoredOutside _]
    · exact hcountedAccumulator
    · exact regs.injective.ne (by decide)
  let final :=
    Basic.exec
      (.imm (CombineValue.rangeRegisters regs).one 1)
      restored
  have hrestoreOne :
      Runs
        (.basic
          (.imm (CombineValue.rangeRegisters regs).one 1))
        restored final :=
    Runs.basic _ _
  refine
    ⟨final,
      by
        simpa [finish, Cmd.seqList] using
          Runs.seq hsave
            (Runs.seq hinitialize
              (Runs.seq hdrop
                (Runs.seq hrestoreCount
                  (Runs.seq hrestorePacked hrestoreOne)))),
      ?_, ?_, ?_, ?_, ?_⟩
  · simpa [final, Basic.exec, bankRegisters,
      PackedLocalStep.bankRegisters,
      PackedLocalHeadScan.bankRegisters,
      PackedLocalHeadScan.bankMap,
      CombineValue.rangeRegisters, regs.injective.eq_iff] using
      hrestoredWord
  · simpa [final, Basic.exec, CombineValue.rangeRegisters,
      regs.injective.eq_iff] using hrestoredCount
  · simpa [final, Basic.exec, CombineValue.rangeRegisters,
      CombineTerm.packedValue, regs.injective.eq_iff] using
      hrestoredPackedValue
  · simp [final, Basic.exec]
  · simpa [final, Basic.exec, CombineValue.rangeRegisters,
      regs.injective.eq_iff] using hrestoredAccumulator

theorem command_writesWithin_internal
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (footprint regs)
      (command tm order controller regs) := by
  simp only [command, Cmd.seqList, Footprint.CmdWritesWithin]
  exact
    ⟨copy_writesWithin _ _ _
        (by
          simpa [bankRegisters, PackedLocalStep.bankRegisters,
            PackedLocalHeadScan.bankRegisters,
            PackedLocalHeadScan.bankMap] using
            footprint_slot regs (16 : Fin 17)),
      by
        simpa [footprint, PackedLocalStep.footprint,
          PackedLocalStep.writeMap,
          PackedLocalInitialization.footprint,
          PackedLocalInitialization.writeMap] using
          PackedLocalInitialization.build_writesWithin
            tm order controller regs,
      copy_writesWithin _ _ _
        (by
          simpa [CombineValue.rangeRegisters] using
            footprint_slot regs (6 : Fin 17)),
      PackedLocalTrace.trace_writesWithin tm order controller regs,
      PackedLocalOutputChunk.build_writesWithin tm controller regs,
      finish_writesWithin tm regs⟩

private theorem preservesABI_of_eq_outside
    (regs : NeighborhoodTrial.Registers controller)
    {initial final : Store}
    (houtside :
      ∀ address, address ∉ footprint regs →
        final address = initial address) :
    ControlDecode.PreservesABI regs initial final := by
  exact
    { fuel_eq :=
        houtside _ (footprint_index_not_mem regs 22 (by decide))
      nodeCode_eq :=
        houtside _ (footprint_index_not_mem regs 23 (by decide))
      scalar_eq :=
        houtside _ (footprint_index_not_mem regs 25 (by decide))
      out_eq :=
        houtside _ (footprint_index_not_mem regs 26 (by decide))
      phaseCode_eq :=
        houtside _ (footprint_index_not_mem regs 27 (by decide))
      active_eq :=
        houtside _ (footprint_index_not_mem regs 28 (by decide))
      blockLength_eq :=
        houtside _ (footprint_index_not_mem regs 2 (by decide))
      horizon_eq :=
        houtside _ (footprint_index_not_mem regs 3 (by decide))
      chunkCount_eq :=
        houtside _ (footprint_index_not_mem regs 7 (by decide))
      chunkRadix_eq :=
        houtside _ (footprint_index_not_mem regs 8 (by decide))
      frameRadix_eq :=
        houtside _ (footprint_index_not_mem regs 13 (by decide))
      bankRadix_eq :=
        houtside _ (footprint_index_not_mem regs 14 (by decide))
      bankDigitCount_eq :=
        houtside _ (footprint_index_not_mem regs 15 (by decide))
      modulusPred_eq :=
        houtside _ (footprint_index_not_mem regs 16 (by decide))
      modulus_eq :=
        houtside _ (footprint_index_not_mem regs 24 (by decide)) }

private theorem context_of_run
    {tm : TM workTapeCount}
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (tape : TapeIndex workTapeCount)
    (slot : NeighborhoodGraph.Slot)
    (interval : Fin instanceData.horizon)
    (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (code :
      Fin
        (3 ^
          NeighborhoodGraph.Guess.Enumeration.movementCount
            workTapeCount instanceData.horizon))
    (outputChunk :
      Fin
        (PrimeGrouped.Logarithmic.chunkCount
          (NeighborhoodExecutableEvaluation.payloadWidth
            tm instanceData.blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount)))
    (cmd : Cmd) {initial final : Store}
    (hwrites : Footprint.CmdWritesWithin (footprint regs) cmd)
    (hrun : Runs cmd initial final)
    (hcontext :
      Context regs instanceData frame tape slot interval logicalBank code
        outputChunk initial) :
    Context regs instanceData frame tape slot interval logicalBank code
      outputChunk final := by
  have houtside :
      ∀ address, address ∉ footprint regs →
        final address = initial address :=
    fun address haddress =>
      Footprint.runs_eq_outside hwrites hrun haddress
  have habi :=
    preservesABI_of_eq_outside regs houtside
  have hbank :
      final regs.layout.bank = initial regs.layout.bank := by
    exact houtside _
      (footprint_index_not_mem regs 33 (by decide))
  exact
    { computation :=
        CombineTerm.Internal.computationFrameContext_transport_internal
          regs instanceData frame tape slot interval.val logicalBank
          hcontext.computation habi hbank
      guess_eq := by
        rw [houtside controller.guess
          (controllerGuess_not_mem_footprint regs)]
        exact hcontext.guess_eq
      cursor_eq := habi.active_eq.trans hcontext.cursor_eq }

theorem command_spec_internal
    {tm : TM workTapeCount}
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (tape : TapeIndex workTapeCount)
    (slot : NeighborhoodGraph.Slot)
    (interval : Fin instanceData.horizon)
    (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (code :
      Fin
        (3 ^
          NeighborhoodGraph.Guess.Enumeration.movementCount
            workTapeCount instanceData.horizon))
    (outputChunk :
      Fin
        (PrimeGrouped.Logarithmic.chunkCount
          (NeighborhoodExecutableEvaluation.payloadWidth
            tm instanceData.blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount)))
    (hencoding :
      instanceData.encoding =
        NeighborhoodExecutableEvaluation.FiniteEncoding.ofStateOrder
          order instanceData.blockLength)
    (hguess :
      instanceData.guess =
        NeighborhoodGraph.Guess.Enumeration.candidateGuess code) :
    SpecAt order regs instanceData frame tape slot interval logicalBank code
      outputChunk := by
  intro store assignment hcontext hremaining hmodulus hmodulusPred hone
  let range := CombineValue.rangeRegisters regs
  let suffix := store range.count
  have hfits :=
    computationNodeDigits_fit instanceData tape slot interval
  obtain ⟨savedSuffix, hsaveSuffix, hsavedWord,
      hsaveSuffixOutside⟩ :=
    CombineTerm.copy_runs_internal
      (bankRegisters regs).word range.count store
      (regs.injective.ne (by decide))
  have hsavedContext :
      Context regs instanceData frame tape slot interval logicalBank code
        outputChunk savedSuffix := by
    exact context_of_run regs instanceData frame tape slot interval
      logicalBank code outputChunk (saveSuffix regs)
      (copy_writesWithin _ _ _
        (by
          simpa [bankRegisters, PackedLocalStep.bankRegisters,
            PackedLocalHeadScan.bankRegisters,
            PackedLocalHeadScan.bankMap] using
            footprint_slot regs (16 : Fin 17)))
      hsaveSuffix hcontext
  have hsavedRemaining :
      savedSuffix range.remaining = assignment := by
    rw [hsaveSuffixOutside _]
    · exact hremaining
    · exact regs.injective.ne (by decide)
  have hsavedOne : savedSuffix range.one = 1 := by
    rw [hsaveSuffixOutside _]
    · exact hone
    · exact regs.injective.ne (by decide)
  have hsavedWordValue :
      savedSuffix (bankRegisters regs).word = suffix := by
    exact hsavedWord
  obtain ⟨initialized, hinitialize, hinitializedPost⟩ :=
    PackedLocalInitialization.build_runs order regs instanceData tape
      slot interval logicalBank code assignment
      suffix savedSuffix hfits
      hsavedContext.computation.computation
      hsavedContext.guess_eq hguess hsavedRemaining
      hsavedWordValue hsavedOne
  have hinitializedContext :
      Context regs instanceData frame tape slot interval logicalBank code
        outputChunk initialized := by
    exact context_of_run regs instanceData frame tape slot interval
      logicalBank code outputChunk
      (PackedLocalInitialization.build tm order controller regs)
      (by
        simpa [footprint, PackedLocalStep.footprint,
          PackedLocalStep.writeMap,
          PackedLocalInitialization.footprint,
          PackedLocalInitialization.writeMap] using
          PackedLocalInitialization.build_writesWithin
            tm order controller regs)
      hinitialize hsavedContext
  obtain ⟨counted, hinstallCount, hcountedValue,
      hcountedOutside⟩ :=
    CombineTerm.copy_runs_internal range.count
      (Layout.blockLength regs) initialized
      (regs.injective.ne (by decide))
  have hcountedContext :
      Context regs instanceData frame tape slot interval logicalBank code
        outputChunk counted := by
    exact context_of_run regs instanceData frame tape slot interval
      logicalBank code outputChunk (installTraceCount regs)
      (copy_writesWithin _ _ _
        (by
          simpa [range, CombineValue.rangeRegisters] using
            footprint_slot regs (6 : Fin 17)))
      hinstallCount hinitializedContext
  have hcountedCount :
      counted range.count = instanceData.blockLength := by
    exact hcountedValue.trans
      hinitializedContext.computation.computation.parameters.blockLength_eq
  have hcountedWord :
      counted (PackedLocalStep.bankRegisters regs).word =
        PackedLocalConfiguration.assignmentStartWord
          tm order instanceData.blockLength instanceData.positive
          instanceData.guess interval assignment suffix := by
    rw [hcountedOutside _]
    · exact hinitializedPost.word_eq
    · exact regs.injective.ne (by decide)
  have hcountedRemaining :
      counted range.remaining = assignment := by
    rw [hcountedOutside _]
    · exact hinitializedPost.assignment_eq
    · exact regs.injective.ne (by decide)
  have hcountedOne : counted range.one = 1 := by
    rw [hcountedOutside _]
    · exact hinitializedPost.one_eq
    · exact regs.injective.ne (by decide)
  obtain ⟨traced, htrace, htracePost⟩ :=
    PackedLocalTrace.trace_runs order regs instanceData tape slot
      interval logicalBank code assignment suffix
      counted hfits hcountedContext.computation.computation
      hcountedContext.guess_eq hguess hcountedWord
      hcountedRemaining hcountedCount hcountedOne
  have htracedContext :
      Context regs instanceData frame tape slot interval logicalBank code
        outputChunk traced := by
    exact context_of_run regs instanceData frame tape slot interval
      logicalBank code outputChunk
      (PackedLocalTrace.trace tm order controller regs)
      (PackedLocalTrace.trace_writesWithin
        tm order controller regs)
      htrace hcountedContext
  let width :=
    PrimeGrouped.Logarithmic.chunkBits
      (NeighborhoodExecutableEvaluation.payloadWidth
        tm instanceData.blockLength)
      (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount)
  let centers :=
    NeighborhoodGraph.Guess.Consistency.guessedCenters
      instanceData.guess interval.val
  let inputs :=
    LocalAssignmentSemantics.assignmentInputs
      tm order instanceData.blockLength instanceData.positive assignment
  let finalCfg :=
    GuessedLocalEvaluation.localTraceAtCenters
      tm instanceData.blockLength centers inputs
  let word := traced (bankRegisters regs).word
  have hcanonical :
      word =
        PackedLocalConfiguration.assignmentFinalWord
          tm order instanceData.blockLength instanceData.positive
          instanceData.guess interval assignment suffix := by
    have heq :=
      PackedLocalRepresentation.Represents.eq_encodeAbove
        tm order instanceData.blockLength centers finalCfg suffix word
        htracePost.represents
    simpa [word, centers, inputs, finalCfg,
      PackedLocalConfiguration.assignmentFinalWord] using heq
  have hfitsWidth :
      ∀ digit ∈
          FrameCodec.nodeDigits
            (show
              NeighborhoodEvaluator.QueryNode
                workTapeCount instanceData.horizon
              from .graph (.computation tape slot interval.val)),
        digit < 2 ^ width := by
    intro digit hdigit
    simpa [width, digitBase_eq_two_pow_chunkBits instanceData] using
      hfits digit hdigit
  have hnode :
      traced (Layout.nodeCode regs) =
        FrameCodec.encodeNode (2 ^ width)
          (show
            NeighborhoodEvaluator.QueryNode
              workTapeCount instanceData.horizon
            from .graph (.computation tape slot interval.val)) := by
    simpa [width, digitBase_eq_two_pow_chunkBits instanceData] using
      htracedContext.computation.computation.nodeCode_eq
  have hradix :
      traced (Layout.chunkRadix regs) = 2 ^ width := by
    simpa [width, digitBase_eq_two_pow_chunkBits instanceData] using
      htracedContext.computation.computation.parameters.digitBase_eq
  have hheads :=
    PackedLocalConfiguration.localTrace_head_window
      tm instanceData.blockLength instanceData.positive centers inputs tape
  obtain ⟨outputted, houtput, houtputPost⟩ :=
    PackedLocalOutputChunk.build_runs
      tm order instanceData.horizon instanceData.blockLength
      instanceData.positive instanceData.guess
      code hguess interval tape slot finalCfg
      suffix word controller regs traced outputChunk.val width
      hfitsWidth hnode hradix htracedContext.guess_eq
      htracedContext.computation.computation.parameters.blockLength_eq
      rfl htracePost.represents
      (htracePost.context.one_eq.trans hcountedOne)
      htracedContext.cursor_eq hheads.1 hheads.2
  have houtputContext :
      Context regs instanceData frame tape slot interval logicalBank code
        outputChunk outputted := by
    exact context_of_run regs instanceData frame tape slot interval
      logicalBank code outputChunk
      (PackedLocalOutputChunk.build tm controller regs)
      (by
        simpa [footprint] using
          PackedLocalOutputChunk.build_writesWithin
            tm controller regs)
      houtput htracedContext
  let expected :=
    CombineTerm.packedAssignmentValue
      (NeighborhoodExecutableEvaluation.payloadWidth
        tm instanceData.blockLength)
      (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount)
      (GuessedLocalEvaluation.booleanCombineAtGuess
        tm instanceData.blockLength instanceData.encoding
        instanceData.positive instanceData.guess interval tape slot)
      outputChunk assignment
  have hsemantic :
      PackedOutputChunkSemantics.packedOutputChunk
          tm instanceData.blockLength
          (centers tape) tape slot word outputChunk.val width =
        expected := by
    rw [hcanonical]
    simpa [expected, width, centers, hencoding] using
      (PackedOutputChunkSemantics.packedOutputChunk_assignmentFinalWord
        tm order instanceData.blockLength instanceData.positive
        instanceData.guess interval tape slot outputChunk assignment
        suffix).trans
        (LocalAssignmentSemantics.packedAssignmentValue_eq_outputChunkValue
          tm order instanceData.blockLength instanceData.positive
          instanceData.guess interval tape slot outputChunk assignment).symm
  have houtputPacked :
      outputted (CombineTerm.packedValue regs) = expected :=
    houtputPost.packed_eq.trans hsemantic
  have hwordSuffix :
      PackedDigits.drop
          (PackedLocalConfiguration.radix tm)
          (PackedLocalConfiguration.digitCount
            workTapeCount instanceData.blockLength)
          word =
        suffix := by
    simpa [word] using htracePost.represents.suffix_eq
  obtain ⟨final, hfinish, hfinalWord, hfinalCount,
      hfinalPacked, hfinalOne, hfinalAccumulator⟩ :=
    finish_runs tm regs instanceData.blockLength suffix word expected
      outputted
      houtputContext.computation.computation.parameters.blockLength_eq
      houtputPost.word_eq hwordSuffix houtputPacked houtputPost.one_eq
  have hfinalContext :
      Context regs instanceData frame tape slot interval logicalBank code
        outputChunk final := by
    exact context_of_run regs instanceData frame tape slot interval
      logicalBank code outputChunk (finish tm regs)
      (finish_writesWithin tm regs) hfinish houtputContext
  have hrun :
      Runs (command tm order controller regs) store final := by
    simpa [command, Cmd.seqList] using
      Runs.seq hsaveSuffix
        (Runs.seq hinitialize
          (Runs.seq hinstallCount
            (Runs.seq htrace
              (Runs.seq houtput hfinish))))
  have houtside :
      ∀ address, address ∉ footprint regs →
        final address = store address :=
    fun address haddress =>
      Footprint.runs_eq_outside
        (command_writesWithin_internal tm order controller regs)
        hrun haddress
  have hsavedSuffixAccumulator :
      savedSuffix range.accumulator = store range.accumulator := by
    rw [hsaveSuffixOutside _]
    exact regs.injective.ne (by decide)
  have hcountedAccumulator :
      counted range.accumulator = initialized range.accumulator := by
    rw [hcountedOutside _]
    exact regs.injective.ne (by decide)
  have haccumulator :
      final range.accumulator = store range.accumulator :=
    hfinalAccumulator.trans
      (houtputPost.outerAccumulator_eq.trans
        (htracePost.context.accumulator_eq.trans
          (hcountedAccumulator.trans
            (hinitializedPost.accumulator_eq.trans
              hsavedSuffixAccumulator))))
  have hremainingFinal :
      final range.remaining = assignment := by
    rw [houtside _]
    · exact hremaining
    · simpa [range, CombineValue.rangeRegisters] using
        footprint_index_not_mem regs (21 : Fin 34) (by decide)
  have hmodulusFinal :
      final range.modulus = store range.modulus := by
    apply houtside
    simpa [range, CombineValue.rangeRegisters] using
      footprint_index_not_mem regs (24 : Fin 34) (by decide)
  have hmodulusPredFinal :
      final range.modulusPred = store range.modulusPred := by
    apply houtside
    simpa [range, CombineValue.rangeRegisters] using
      footprint_index_not_mem regs (16 : Fin 34) (by decide)
  refine ⟨final, hrun, ?_, ?_, hfinalContext⟩
  · exact
      { packed_eq := by simpa [expected] using hfinalPacked
        accumulator_eq := haccumulator
        remaining_eq := hremainingFinal
        modulus_eq := hmodulusFinal
        modulusPred_eq := hmodulusPredFinal
        one_eq := hfinalOne.trans hone.symm
        count_eq := by simpa [suffix] using hfinalCount }
  · simpa [suffix] using hfinalWord

end Internal
end PackedComputationKernel
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
