/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.Models.RandomAccessMachine.Structured.Footprint
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.AssignmentBit
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.AssignmentCodeSemantics
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.AssignmentPayloadBit.Defs
import Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodProgram

/-!
# Uniform semantic payload-bit lookup -- proofs
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace AssignmentPayloadBit
namespace Internal

open RAM Structured
open TreeEval CookMertz
open NeighborhoodExecutableEvaluation

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

private theorem pop_writesWithin
    (stack : NeighborhoodProgram.StackRegisters) :
    Footprint.CmdWritesWithin
      stack.footprint (NeighborhoodProgram.pop stack) := by
  simp [NeighborhoodProgram.pop, NeighborhoodProgram.popBody,
    NeighborhoodProgram.popTestOp, Cmd.seqList,
    Footprint.CmdWritesWithin, Footprint.BasicWritesWithin,
    NeighborhoodProgram.StackRegisters.index_mem_footprint]

private theorem copy_writesWithin
    {allowed : Finset ℕ} {destination source : ℕ}
    (hdestination : destination ∈ allowed) :
    Footprint.CmdWritesWithin allowed
      (CombineTerm.copy destination source) := by
  simpa [CombineTerm.copy, Footprint.CmdWritesWithin,
    Footprint.BasicWritesWithin] using
    And.intro hdestination hdestination

private theorem recovered_not_mem_exponentFootprint
    (regs : NeighborhoodTrial.Registers controller) :
    recoveredChunkBits regs ∉
      (exponentStackRegisters regs).footprint := by
  simp only [NeighborhoodProgram.StackRegisters.footprint,
    Finset.mem_image, Finset.mem_univ, true_and, not_exists]
  intro slot heq
  have hslot := regs.injective heq
  change exponentStackMap slot = (20 : Fin 34) at hslot
  fin_cases slot <;> contradiction

private theorem recovered_ne_exponentIndex
    (regs : NeighborhoodTrial.Registers controller)
    (slot : Fin 7) :
    recoveredChunkBits regs ≠
      (exponentStackRegisters regs).index slot := by
  intro heq
  apply recovered_not_mem_exponentFootprint regs
  exact Finset.mem_image.mpr
    ⟨slot, Finset.mem_univ _, heq.symm⟩

theorem recoverChunkBits_writesWithin_internal
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin
      (recoveryFootprint regs) (recoverChunkBits regs) := by
  let stack := exponentStackRegisters regs
  have hstack :
      stack.footprint ⊆ recoveryFootprint regs :=
    Finset.subset_union_left
  have hpop :
      Footprint.CmdWritesWithin
        (recoveryFootprint regs) (NeighborhoodProgram.pop stack) :=
    cmdWritesWithin_mono hstack _ (pop_writesWithin stack)
  have hrecovered :
      recoveredChunkBits regs ∈ recoveryFootprint regs := by
    simp [recoveryFootprint]
  have hword :=
    hstack (NeighborhoodProgram.StackRegisters.index_mem_footprint
      stack 0)
  have hbase :=
    hstack (NeighborhoodProgram.StackRegisters.index_mem_footprint
      stack 1)
  have hbasePred :=
    hstack (NeighborhoodProgram.StackRegisters.index_mem_footprint
      stack 2)
  have htest :=
    hstack (NeighborhoodProgram.StackRegisters.index_mem_footprint
      stack 4)
  have hone :=
    hstack (NeighborhoodProgram.StackRegisters.index_mem_footprint
      stack 5)
  simp only [recoverChunkBits, recoverChunkBitsBody,
    CombineTerm.copy, Cmd.seqList, Footprint.CmdWritesWithin,
    Footprint.BasicWritesWithin]
  exact
    ⟨⟨hword, hword⟩, hbase, hbasePred, hone,
      hrecovered, htest,
      hpop, hrecovered, htest⟩

theorem prepareIndex_writesWithin_internal
    (workTapeCount : ℕ)
    (regs : NeighborhoodTrial.Registers controller)
    (child : Fin (graphFanIn workTapeCount)) :
    Footprint.CmdWritesWithin
      (writeFootprint regs)
      (prepareIndex workTapeCount regs child) := by
  have hword :
      (exponentStackRegisters regs).word ∈
        writeFootprint regs := by
    exact Finset.mem_union_left _
      (Finset.mem_union_left _
        (Finset.mem_union_left _
          (NeighborhoodProgram.StackRegisters.index_mem_footprint
            (exponentStackRegisters regs) 0)))
  have hindex :
      AssignmentBit.digitIndex regs ∈ writeFootprint regs := by
    exact Finset.mem_union_left _
      (Finset.mem_union_right _
        (Finset.mem_singleton_self _))
  simpa [prepareIndex, Cmd.seqList,
    Footprint.CmdWritesWithin, Footprint.BasicWritesWithin] using
    And.intro hindex
      (And.intro hindex
        (And.intro hindex
          (And.intro hindex
            (And.intro hword
              (And.intro hword
                (And.intro hword
                  (And.intro hword hindex)))))))

theorem read_writesWithin_internal
    (workTapeCount : ℕ)
    (regs : NeighborhoodTrial.Registers controller)
    (child : Fin (graphFanIn workTapeCount)) :
    Footprint.CmdWritesWithin
      (writeFootprint regs)
      (read workTapeCount regs child) := by
  have hrecover :
      Footprint.CmdWritesWithin
        (writeFootprint regs) (recoverChunkBits regs) :=
    cmdWritesWithin_mono
      (Finset.subset_union_left.trans
        Finset.subset_union_left)
      _ (recoverChunkBits_writesWithin_internal regs)
  have hread :
      Footprint.CmdWritesWithin
        (writeFootprint regs) (AssignmentBit.read regs) :=
    cmdWritesWithin_mono
      (Finset.subset_union_right :
        AssignmentBit.writeFootprint regs ⊆
          writeFootprint regs)
      _ (AssignmentBit.read_writesWithin regs)
  simpa only [read, Cmd.seqList, Footprint.CmdWritesWithin] using
    And.intro hrecover
      (And.intro
        (prepareIndex_writesWithin_internal
          workTapeCount regs child)
        hread)

private theorem exponentFootprint_subset_combineScratch
    (regs : NeighborhoodTrial.Registers controller) :
    (exponentStackRegisters regs).footprint ⊆
      CombineValue.combineScratchFootprint regs := by
  intro address haddress
  rcases Finset.mem_image.mp haddress with ⟨slot, _, rfl⟩
  fin_cases slot
  · exact Finset.mem_image.mpr
      ⟨(0 : Fin 19), Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr
      ⟨(1 : Fin 19), Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr
      ⟨(2 : Fin 19), Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr
      ⟨(3 : Fin 19), Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr
      ⟨(5 : Fin 19), Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr
      ⟨(7 : Fin 19), Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr
      ⟨(8 : Fin 19), Finset.mem_univ _, rfl⟩

private theorem assignmentBitFootprint_subset_combineScratch
    (regs : NeighborhoodTrial.Registers controller) :
    AssignmentBit.writeFootprint regs ⊆
      CombineValue.combineScratchFootprint regs := by
  intro address haddress
  change address ∈
    (AssignmentBit.digitRegisters regs).writeFootprint ∪
      {(AssignmentBit.digitRegisters regs).divisor} at haddress
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

theorem writeFootprint_subset_combineScratch_internal
    (regs : NeighborhoodTrial.Registers controller) :
    writeFootprint regs ⊆
      CombineValue.combineScratchFootprint regs := by
  intro address haddress
  change
    address ∈
      (recoveryFootprint regs ∪
        {AssignmentBit.digitIndex regs}) ∪
          AssignmentBit.writeFootprint regs at haddress
  rw [Finset.mem_union] at haddress
  rcases haddress with hprefix | hassignment
  rw [Finset.mem_union] at hprefix
  rcases hprefix with hrecovery | hindex
  change address ∈
    (exponentStackRegisters regs).footprint ∪
      {recoveredChunkBits regs} at hrecovery
  rw [Finset.mem_union] at hrecovery
  rcases hrecovery with hstack | hrecovered
  · exact exponentFootprint_subset_combineScratch regs hstack
  · simp only [Finset.mem_singleton] at hrecovered
    subst address
    exact Finset.mem_image.mpr
      ⟨(12 : Fin 19), Finset.mem_univ _, rfl⟩
  · simp only [Finset.mem_singleton] at hindex
    subst address
    exact Finset.mem_image.mpr
      ⟨(14 : Fin 19), Finset.mem_univ _, rfl⟩
  · exact assignmentBitFootprint_subset_combineScratch
      regs hassignment

theorem read_combineScratch_writesWithin_internal
    (workTapeCount : ℕ)
    (regs : NeighborhoodTrial.Registers controller)
    (child : Fin (graphFanIn workTapeCount)) :
    Footprint.CmdWritesWithin
      (CombineValue.combineScratchFootprint regs)
      (read workTapeCount regs child) :=
  cmdWritesWithin_mono
    (writeFootprint_subset_combineScratch_internal regs)
    _ (read_writesWithin_internal workTapeCount regs child)

theorem read_layout_writesWithin_internal
    (workTapeCount : ℕ)
    (regs : NeighborhoodTrial.Registers controller)
    (child : Fin (graphFanIn workTapeCount)) :
    Footprint.CmdWritesWithin
      regs.layout.footprint
      (read workTapeCount regs child) :=
  cmdWritesWithin_mono
    (CombineValue.combineScratchFootprint_subset_layout regs)
    _ (read_combineScratch_writesWithin_internal
      workTapeCount regs child)

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

private theorem recoverLoop_runs
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store) (remaining completed : ℕ)
    (hword :
      store (exponentStackRegisters regs).word = 2 ^ remaining)
    (hrecovered :
      store (recoveredChunkBits regs) = completed)
    (htest :
      store (exponentStackRegisters regs).test =
        2 ^ remaining - 1)
    (hbase : store (exponentStackRegisters regs).base = 2)
    (hbasePred :
      store (exponentStackRegisters regs).basePred = 1)
    (hone : store (exponentStackRegisters regs).one = 1) :
    ∃ final,
      Runs
        (.whileNonzero (exponentStackRegisters regs).test
          (recoverChunkBitsBody regs))
        store final ∧
      final (exponentStackRegisters regs).word = 1 ∧
      final (recoveredChunkBits regs) = completed + remaining ∧
      final (exponentStackRegisters regs).test = 0 ∧
      final (exponentStackRegisters regs).base = 2 ∧
      final (exponentStackRegisters regs).basePred = 1 ∧
      final (exponentStackRegisters regs).one = 1 := by
  induction remaining generalizing store completed with
  | zero =>
      have htestZero :
          store (exponentStackRegisters regs).test = 0 := by
        simpa using htest
      exact
        ⟨store, Runs.whileZero htestZero, by simpa using hword,
          by simpa using hrecovered, htestZero, hbase,
          hbasePred, hone⟩
  | succ remaining ih =>
      have htestNonzero :
          store (exponentStackRegisters regs).test ≠ 0 := by
        rw [htest]
        have hpow : 0 < 2 ^ (remaining + 1) :=
          pow_pos (by omega) _
        omega
      obtain ⟨afterPop, hpop, hpopWord, _hpopQuotient,
          _hpopTest, hpopBase, hpopBasePred, hpopOne⟩ :=
        NeighborhoodProgram.pop_runs
          (exponentStackRegisters regs) store
          2 (2 ^ (remaining + 1)) (by omega)
          hword hbase (by simpa using hbasePred) hone
      have hpopWord0 :
          afterPop (exponentStackRegisters regs).word =
            PackedDigits.pop 2 (2 ^ (remaining + 1)) := by
        simpa using hpopWord
      have hpopBase0 :
          afterPop (exponentStackRegisters regs).base = 2 := by
        simpa using hpopBase
      have hpopBasePred0 :
          afterPop (exponentStackRegisters regs).basePred = 1 := by
        simpa using hpopBasePred
      have hpopOne0 :
          afterPop (exponentStackRegisters regs).one = 1 := by
        simpa using hpopOne
      have hpopWord' :
          afterPop (exponentStackRegisters regs).word =
            2 ^ remaining := by
        rw [hpopWord0]
        simp [PackedDigits.pop, pow_succ]
      have hpopRecovered :
          afterPop (recoveredChunkBits regs) = completed := by
        rw [Footprint.runs_eq_outside
          (pop_writesWithin
            (exponentStackRegisters regs)) hpop]
        · exact hrecovered
        · exact recovered_not_mem_exponentFootprint regs
      let afterIncrement :=
        Basic.exec
          (.add (recoveredChunkBits regs)
            (recoveredChunkBits regs)
            (exponentStackRegisters regs).one)
          afterPop
      let afterTest :=
        Basic.exec
          (.sub (exponentStackRegisters regs).test
            (exponentStackRegisters regs).word
            (exponentStackRegisters regs).one)
          afterIncrement
      have hbody :
          Runs (recoverChunkBitsBody regs) store afterTest := by
        simpa [recoverChunkBitsBody, Cmd.seqList,
          afterIncrement, afterTest] using
          Runs.seq hpop
            (Runs.seq
              (Runs.basic
                (.add (recoveredChunkBits regs)
                  (recoveredChunkBits regs)
                  (exponentStackRegisters regs).one)
                afterPop)
              (Runs.basic
                (.sub (exponentStackRegisters regs).test
                  (exponentStackRegisters regs).word
                  (exponentStackRegisters regs).one)
                afterIncrement))
      have hnextWord :
          afterTest (exponentStackRegisters regs).word =
            2 ^ remaining := by
        simp [afterTest, afterIncrement, Basic.exec,
          (exponentStackRegisters regs).index_ne
            (by decide : (0 : Fin 7) ≠ 4),
          (recovered_ne_exponentIndex regs 0).symm, hpopWord']
      have hnextRecovered :
          afterTest (recoveredChunkBits regs) =
            completed + 1 := by
        simp [afterTest, afterIncrement, Basic.exec,
          recovered_ne_exponentIndex regs 4,
          hpopRecovered, hpopOne0]
      have hnextTest :
          afterTest (exponentStackRegisters regs).test =
            2 ^ remaining - 1 := by
        simp [afterTest, Basic.exec]
        have hwordAfterIncrement :
            afterIncrement
                (exponentStackRegisters regs).word =
              2 ^ remaining := by
          simp [afterIncrement, Basic.exec,
            (recovered_ne_exponentIndex regs 0).symm, hpopWord']
        have honeAfterIncrement :
            afterIncrement
                (exponentStackRegisters regs).one = 1 := by
          simp [afterIncrement, Basic.exec,
            (recovered_ne_exponentIndex regs 5).symm, hpopOne0]
        rw [hwordAfterIncrement, honeAfterIncrement]
      have hnextBase :
          afterTest (exponentStackRegisters regs).base = 2 := by
        simp [afterTest, afterIncrement, Basic.exec,
          (exponentStackRegisters regs).index_ne
            (by decide : (1 : Fin 7) ≠ 4),
          (recovered_ne_exponentIndex regs 1).symm, hpopBase0]
      have hnextBasePred :
          afterTest (exponentStackRegisters regs).basePred = 1 := by
        simp [afterTest, afterIncrement, Basic.exec,
          (exponentStackRegisters regs).index_ne
            (by decide : (2 : Fin 7) ≠ 4),
          (recovered_ne_exponentIndex regs 2).symm,
          hpopBasePred0]
      have hnextOne :
          afterTest (exponentStackRegisters regs).one = 1 := by
        simp [afterTest, afterIncrement, Basic.exec,
          (exponentStackRegisters regs).index_ne
            (by decide : (5 : Fin 7) ≠ 4),
          (recovered_ne_exponentIndex regs 5).symm, hpopOne0]
      obtain ⟨final, hloop, hfinalWord,
          hfinalRecovered, hfinalTest, hfinalBase,
          hfinalBasePred, hfinalOne⟩ :=
        ih afterTest (completed + 1) hnextWord
          hnextRecovered hnextTest hnextBase hnextBasePred
          hnextOne
      refine
        ⟨final,
          Runs.whileNonzero htestNonzero hbody hloop,
          hfinalWord, ?_, hfinalTest, hfinalBase,
          hfinalBasePred, hfinalOne⟩
      rw [hfinalRecovered]
      omega

theorem recoverChunkBits_runs_internal
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store) (chunkBits : ℕ)
    (hradix :
      store (Layout.chunkRadix regs) = 2 ^ chunkBits) :
    ∃ final,
      Runs (recoverChunkBits regs) store final ∧
      final (recoveredChunkBits regs) = chunkBits ∧
      final (exponentStackRegisters regs).word = 1 ∧
      final (exponentStackRegisters regs).test = 0 ∧
      final (exponentStackRegisters regs).base = 2 ∧
      final (exponentStackRegisters regs).basePred = 1 ∧
      final (exponentStackRegisters regs).one = 1 ∧
      ∀ address, address ∉ recoveryFootprint regs →
        final address = store address := by
  obtain ⟨copied, hcopy, hcopyValue, hcopyOutside⟩ :=
    copy_runs (exponentStackRegisters regs).word
      (Layout.chunkRadix regs) store
      (regs.injective.ne (by decide))
  let afterBase :=
    Basic.exec
      (.imm (exponentStackRegisters regs).base 2) copied
  let afterBasePred :=
    Basic.exec
      (.imm (exponentStackRegisters regs).basePred 1)
      afterBase
  let afterOne :=
    Basic.exec
      (.imm (exponentStackRegisters regs).one 1)
      afterBasePred
  let afterRecovered :=
    Basic.exec (.imm (recoveredChunkBits regs) 0) afterOne
  let ready :=
    Basic.exec
      (.sub (exponentStackRegisters regs).test
        (exponentStackRegisters regs).word
        (exponentStackRegisters regs).one)
      afterRecovered
  have hreadyWord :
      ready (exponentStackRegisters regs).word =
        2 ^ chunkBits := by
    simp [ready, afterRecovered, afterOne, afterBasePred,
      afterBase, Basic.exec,
      (exponentStackRegisters regs).index_ne
        (by decide : (0 : Fin 7) ≠ 1),
      (exponentStackRegisters regs).index_ne
        (by decide : (0 : Fin 7) ≠ 2),
      (exponentStackRegisters regs).index_ne
        (by decide : (0 : Fin 7) ≠ 5),
      (exponentStackRegisters regs).index_ne
        (by decide : (0 : Fin 7) ≠ 4),
      (recovered_ne_exponentIndex regs 0).symm,
      hcopyValue, hradix]
  have hreadyRecovered :
      ready (recoveredChunkBits regs) = 0 := by
    simp [ready, afterRecovered, Basic.exec,
      recovered_ne_exponentIndex regs 4]
  have hreadyTest :
      ready (exponentStackRegisters regs).test =
        2 ^ chunkBits - 1 := by
    simp [ready, afterRecovered, afterOne, afterBasePred,
      afterBase, Basic.exec,
      (exponentStackRegisters regs).index_ne
        (by decide : (0 : Fin 7) ≠ 1),
      (exponentStackRegisters regs).index_ne
        (by decide : (0 : Fin 7) ≠ 2),
      (exponentStackRegisters regs).index_ne
        (by decide : (0 : Fin 7) ≠ 5),
      (recovered_ne_exponentIndex regs 0).symm,
      (recovered_ne_exponentIndex regs 5).symm,
      hcopyValue, hradix]
  have hreadyBase :
      ready (exponentStackRegisters regs).base = 2 := by
    simp [ready, afterRecovered, afterOne, afterBasePred,
      afterBase, Basic.exec,
      (exponentStackRegisters regs).index_ne
        (by decide : (1 : Fin 7) ≠ 2),
      (exponentStackRegisters regs).index_ne
        (by decide : (1 : Fin 7) ≠ 5),
      (exponentStackRegisters regs).index_ne
        (by decide : (1 : Fin 7) ≠ 4),
      (recovered_ne_exponentIndex regs 1).symm]
  have hreadyBasePred :
      ready (exponentStackRegisters regs).basePred = 1 := by
    simp [ready, afterRecovered, afterOne, afterBasePred,
      Basic.exec,
      (exponentStackRegisters regs).index_ne
        (by decide : (2 : Fin 7) ≠ 5),
      (exponentStackRegisters regs).index_ne
        (by decide : (2 : Fin 7) ≠ 4),
      (recovered_ne_exponentIndex regs 2).symm]
  have hreadyOne :
      ready (exponentStackRegisters regs).one = 1 := by
    simp [ready, afterRecovered, afterOne, Basic.exec,
      (exponentStackRegisters regs).index_ne
        (by decide : (5 : Fin 7) ≠ 4),
      (recovered_ne_exponentIndex regs 5).symm]
  obtain ⟨final, hloop, hfinalWord, hfinalRecovered,
      hfinalTest, hfinalBase, hfinalBasePred, hfinalOne⟩ :=
    recoverLoop_runs regs ready chunkBits 0
      hreadyWord hreadyRecovered hreadyTest hreadyBase
      hreadyBasePred hreadyOne
  have hrun : Runs (recoverChunkBits regs) store final := by
    simpa [recoverChunkBits, Cmd.seqList, afterBase,
      afterBasePred, afterOne, afterRecovered, ready] using
      Runs.seq hcopy
        (Runs.seq
          (Runs.basic
            (.imm (exponentStackRegisters regs).base 2) copied)
          (Runs.seq
            (Runs.basic
              (.imm (exponentStackRegisters regs).basePred 1)
              afterBase)
            (Runs.seq
              (Runs.basic
                (.imm (exponentStackRegisters regs).one 1)
                afterBasePred)
              (Runs.seq
                (Runs.basic
                  (.imm (recoveredChunkBits regs) 0) afterOne)
                (Runs.seq
                  (Runs.basic
                    (.sub (exponentStackRegisters regs).test
                      (exponentStackRegisters regs).word
                      (exponentStackRegisters regs).one)
                    afterRecovered)
                  hloop)))))
  refine
    ⟨final, hrun, by simpa using hfinalRecovered,
      hfinalWord, hfinalTest, hfinalBase, hfinalBasePred,
      hfinalOne, ?_⟩
  intro address haddress
  exact Footprint.runs_eq_outside
    (recoverChunkBits_writesWithin_internal regs)
    hrun haddress

private theorem prepareIndex_runs
    (workTapeCount : ℕ)
    (regs : NeighborhoodTrial.Registers controller)
    (child : Fin (graphFanIn workTapeCount))
    (store : Store) (chunkCount chunkBits position : ℕ)
    (hchunkCount :
      store (Layout.chunkCount regs) = chunkCount)
    (hchunkBits :
      store (recoveredChunkBits regs) = chunkBits)
    (hposition :
      store (payloadPosition regs) = position)
    (hone :
      store (exponentStackRegisters regs).one = 1) :
    ∃ final,
      Runs (prepareIndex workTapeCount regs child) store final ∧
      final (AssignmentBit.digitIndex regs) =
        assignmentIndex workTapeCount chunkCount chunkBits
          child position := by
  let stack := exponentStackRegisters regs
  let index := AssignmentBit.digitIndex regs
  let afterFanIn :=
    Basic.exec (.imm index (graphFanIn workTapeCount)) store
  let afterCount :=
    Basic.exec (.mul index index (Layout.chunkCount regs))
      afterFanIn
  let afterWidth :=
    Basic.exec (.mul index index (recoveredChunkBits regs))
      afterCount
  let afterPred :=
    Basic.exec (.sub index index stack.one) afterWidth
  let afterChild := Basic.exec (.imm stack.word child.val) afterPred
  let afterChildCount :=
    Basic.exec
      (.mul stack.word stack.word (Layout.chunkCount regs))
      afterChild
  let afterChildWidth :=
    Basic.exec
      (.mul stack.word stack.word (recoveredChunkBits regs))
      afterChildCount
  let afterPosition :=
    Basic.exec
      (.add stack.word stack.word (payloadPosition regs))
      afterChildWidth
  let final :=
    Basic.exec (.sub index index stack.word) afterPosition
  have hrun :
      Runs (prepareIndex workTapeCount regs child) store final := by
    simpa [prepareIndex, Cmd.seqList, afterFanIn, afterCount,
      afterWidth, afterPred, afterChild, afterChildCount,
      afterChildWidth, afterPosition, final] using
      Runs.seq
        (Runs.basic
          (.imm index (graphFanIn workTapeCount)) store)
        (Runs.seq
          (Runs.basic
            (.mul index index (Layout.chunkCount regs))
            afterFanIn)
          (Runs.seq
            (Runs.basic
              (.mul index index (recoveredChunkBits regs))
              afterCount)
            (Runs.seq
              (Runs.basic (.sub index index stack.one)
                afterWidth)
              (Runs.seq
                (Runs.basic (.imm stack.word child.val)
                  afterPred)
                (Runs.seq
                  (Runs.basic
                    (.mul stack.word stack.word
                      (Layout.chunkCount regs))
                    afterChild)
                  (Runs.seq
                    (Runs.basic
                      (.mul stack.word stack.word
                        (recoveredChunkBits regs))
                      afterChildCount)
                    (Runs.seq
                      (Runs.basic
                        (.add stack.word stack.word
                          (payloadPosition regs))
                        afterChildWidth)
                      (Runs.basic
                        (.sub index index stack.word)
                        afterPosition))))))))
  refine ⟨final, hrun, ?_⟩
  simp [final, afterPosition, afterChildWidth,
    afterChildCount, afterChild, afterPred, afterWidth,
    afterCount, afterFanIn, Basic.exec, assignmentIndex,
    index, stack, exponentStackRegisters, exponentStackMap,
    AssignmentBit.digitIndex, recoveredChunkBits,
    payloadPosition, Layout.codecScratch, Layout.chunkCount,
    regs.injective.eq_iff, hchunkCount, hchunkBits, hposition]
  have hone' := hone
  simp [exponentStackRegisters, exponentStackMap] at hone'
  rw [hone']
  congr 2
  ring

theorem assignmentIndex_eq_lowOrderBitIndex_internal
    (workTapeCount payloadWidth : ℕ)
    (child : Fin (graphFanIn workTapeCount))
    (position : Fin payloadWidth) :
    assignmentIndex workTapeCount
        (PrimeGrouped.Logarithmic.chunkCount
          payloadWidth (graphFanIn workTapeCount))
        (PrimeGrouped.Logarithmic.chunkBits
          payloadWidth (graphFanIn workTapeCount))
        child position.val =
      AssignmentCodeSemantics.lowOrderBitIndex
        payloadWidth (graphFanIn workTapeCount)
        child position := by
  rw [AssignmentCodeSemantics.lowOrderBitIndex_eq]
  rfl

private theorem preservedAddresses_not_mem
    (regs : NeighborhoodTrial.Registers controller) :
    payloadPosition regs ∉ writeFootprint regs ∧
    (CombineValue.rangeRegisters regs).accumulator ∉
      writeFootprint regs ∧
    (CombineValue.rangeRegisters regs).remaining ∉
      writeFootprint regs ∧
    (CombineValue.rangeRegisters regs).modulus ∉
      writeFootprint regs ∧
    (CombineValue.rangeRegisters regs).modulusPred ∉
      writeFootprint regs ∧
    (CombineValue.rangeRegisters regs).one ∉
      writeFootprint regs ∧
    (CombineValue.rangeRegisters regs).count ∉
      writeFootprint regs ∧
    (CombineValue.rangeRegisters regs).term ∉
      writeFootprint regs ∧
    (Layout.frameStackRegisters regs).word ∉
      writeFootprint regs ∧
    regs.layout.bank ∉ writeFootprint regs := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [writeFootprint, recoveryFootprint,
      exponentStackRegisters, exponentStackMap,
      AssignmentBit.writeFootprint, AssignmentBit.digitRegisters,
      AssignmentBit.digitMap,
      CombineTerm.DigitRegisters.writeFootprint,
      CombineValue.rangeRegisters, Layout.frameStackRegisters,
      Layout.frameStackMap,
      NeighborhoodTrial.Registers.layout,
    NeighborhoodProgram.StackRegisters.footprint,
      regs.injective.eq_iff] <;>
    intro slot <;> fin_cases slot <;> decide

theorem remaining_not_mem_writeFootprint_internal
    (regs : NeighborhoodTrial.Registers controller) :
    (CombineValue.rangeRegisters regs).remaining ∉
      writeFootprint regs :=
  (preservedAddresses_not_mem regs).2.2.1

theorem accumulator_not_mem_writeFootprint_internal
    (regs : NeighborhoodTrial.Registers controller) :
    (CombineValue.rangeRegisters regs).accumulator ∉
      writeFootprint regs :=
  (preservedAddresses_not_mem regs).2.1

theorem count_not_mem_writeFootprint_internal
    (regs : NeighborhoodTrial.Registers controller) :
    (CombineValue.rangeRegisters regs).count ∉
      writeFootprint regs := by
  rcases preservedAddresses_not_mem regs with
    ⟨_, _, _, _, _, _, hcount, _, _, _⟩
  exact hcount

theorem catalyticBank_not_mem_writeFootprint_internal
    (regs : NeighborhoodTrial.Registers controller) :
    regs.layout.bank ∉ writeFootprint regs := by
  rcases preservedAddresses_not_mem regs with
    ⟨_, _, _, _, _, _, _, _, _, hbank⟩
  exact hbank

theorem read_runs_internal
    (workTapeCount payloadWidth : ℕ)
    (regs : NeighborhoodTrial.Registers controller)
    (child : Fin (graphFanIn workTapeCount))
    (position : Fin payloadWidth)
    (store : Store) (code : ℕ)
    (hchunkCount :
      store (Layout.chunkCount regs) =
        PrimeGrouped.Logarithmic.chunkCount
          payloadWidth (graphFanIn workTapeCount))
    (hradix :
      store (Layout.chunkRadix regs) =
        2 ^
          PrimeGrouped.Logarithmic.chunkBits
            payloadWidth (graphFanIn workTapeCount))
    (hcode :
      store (CombineValue.rangeRegisters regs).remaining = code)
    (hposition :
      store (payloadPosition regs) = position.val) :
    ∃ final,
      Runs (read workTapeCount regs child) store final ∧
      Post workTapeCount payloadWidth code regs child position
        store final := by
  let chunkCount :=
    PrimeGrouped.Logarithmic.chunkCount
      payloadWidth (graphFanIn workTapeCount)
  let chunkBits :=
    PrimeGrouped.Logarithmic.chunkBits
      payloadWidth (graphFanIn workTapeCount)
  obtain ⟨recovered, hrecover, hrecoverBits, _hrecoverWord,
      _hrecoverTest, _hrecoverBase, _hrecoverBasePred,
      hrecoverOne, hrecoverOutside⟩ :=
    recoverChunkBits_runs_internal regs store chunkBits hradix
  have hrecoverCount :
      recovered (Layout.chunkCount regs) = chunkCount := by
    rw [hrecoverOutside (Layout.chunkCount regs)]
    · exact hchunkCount
    · simp [recoveryFootprint, exponentStackRegisters,
        exponentStackMap,
        NeighborhoodProgram.StackRegisters.footprint,
        Layout.chunkCount, regs.injective.eq_iff]
      intro slot
      fin_cases slot <;> decide
  have hrecoverPosition :
      recovered (payloadPosition regs) = position.val := by
    rw [hrecoverOutside (payloadPosition regs)]
    · exact hposition
    · simp [recoveryFootprint, exponentStackRegisters,
        exponentStackMap,
        NeighborhoodProgram.StackRegisters.footprint,
        payloadPosition, Layout.codecScratch,
        regs.injective.eq_iff]
      intro slot
      fin_cases slot <;> decide
  obtain ⟨prepared, hprepare, hprepareIndex⟩ :=
    prepareIndex_runs workTapeCount regs child recovered
      chunkCount chunkBits position.val hrecoverCount
      hrecoverBits hrecoverPosition hrecoverOne
  have hprepareCode :
      prepared (CombineValue.rangeRegisters regs).remaining = code := by
    rw [Footprint.runs_eq_outside
      (prepareIndex_writesWithin_internal
        workTapeCount regs child) hprepare]
    · rw [hrecoverOutside
        (CombineValue.rangeRegisters regs).remaining]
      · exact hcode
      · simp [recoveryFootprint, exponentStackRegisters,
          exponentStackMap,
          NeighborhoodProgram.StackRegisters.footprint,
          CombineValue.rangeRegisters, regs.injective.eq_iff]
        intro slot
        fin_cases slot <;> decide
    · exact (preservedAddresses_not_mem regs).2.2.1
  have hsemanticIndex :
      prepared (AssignmentBit.digitIndex regs) =
        AssignmentCodeSemantics.lowOrderBitIndex
          payloadWidth (graphFanIn workTapeCount)
          child position := by
    rw [hprepareIndex]
    exact assignmentIndex_eq_lowOrderBitIndex_internal
      workTapeCount payloadWidth child position
  obtain ⟨final, hbitRun, hbitPost, _hbitABI⟩ :=
    AssignmentBit.read_runs regs prepared code
      (AssignmentCodeSemantics.lowOrderBitIndex
        payloadWidth (graphFanIn workTapeCount) child position)
      hprepareCode hsemanticIndex
  have hrun :
      Runs (read workTapeCount regs child) store final := by
    simpa [read, Cmd.seqList] using
      Runs.seq hrecover (Runs.seq hprepare hbitRun)
  have houtside :
      ∀ address, address ∉ writeFootprint regs →
        final address = store address := by
    intro address haddress
    exact Footprint.runs_eq_outside
      (read_writesWithin_internal workTapeCount regs child)
      hrun haddress
  rcases preservedAddresses_not_mem regs with
    ⟨hpositionOutside, haccumulatorOutside, hremainingOutside,
      hmodulusOutside, hmodulusPredOutside, honeOutside,
      hcountOutside, htermOutside, hstackOutside, hbankOutside⟩
  refine ⟨final, hrun, ?_⟩
  exact
    { value_eq :=
        hbitPost.value_eq.trans
          (AssignmentCodeSemantics.assignmentBit_toNat_eq_radixDigit
            payloadWidth (graphFanIn workTapeCount) code
            child position).symm
      index_eq := hbitPost.index_eq
      position_eq :=
        (houtside (payloadPosition regs) hpositionOutside).trans
          hposition
      accumulator_eq :=
        houtside _ haccumulatorOutside
      remaining_eq :=
        (houtside _ hremainingOutside).trans hcode
      modulus_eq := houtside _ hmodulusOutside
      modulusPred_eq := houtside _ hmodulusPredOutside
      one_eq := houtside _ honeOutside
      count_eq := houtside _ hcountOutside
      term_eq := houtside _ htermOutside
      stack_eq := houtside _ hstackOutside
      bank_eq := houtside _ hbankOutside
      abi :=
        CombineValue.preservesABI_of_combineScratch regs
          (read_combineScratch_writesWithin_internal
            workTapeCount regs child)
          hrun
      eq_outside := houtside }

end Internal
end AssignmentPayloadBit
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
