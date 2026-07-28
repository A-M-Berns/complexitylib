/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.PackedLocalStep.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.PackedLocalHeadScan
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.PackedLocalRepresentation
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.FrameBounds
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.Representation
import Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodProgram

/-!
# Fixed-source packed local transition -- proofs
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace PackedLocalStep
namespace Internal

open RAM Structured

variable {controller : SearchProgram.Registers}

private theorem cmdWritesWithin_mono
    {small large : Finset ℕ} {command : Cmd}
    (hwrites : Footprint.CmdWritesWithin small command)
    (hsubset : small ⊆ large) :
    Footprint.CmdWritesWithin large command := by
  induction command with
  | skip =>
      trivial
  | basic operation =>
      cases operation <;>
        simp only [Footprint.CmdWritesWithin,
          Footprint.BasicWritesWithin] at hwrites ⊢
      all_goals
        exact hsubset hwrites
  | seq first second ihFirst ihSecond =>
      exact
        ⟨ihFirst hwrites.1, ihSecond hwrites.2⟩
  | ifZero test onZero onNonzero ihZero ihNonzero =>
      exact
        ⟨ihZero hwrites.1, ihNonzero hwrites.2⟩
  | whileNonzero test body ih =>
      exact ih hwrites

private theorem write_slot_mem
    (regs : NeighborhoodTrial.Registers controller)
    (slot : Fin 17) :
    regs.index (writeMap slot) ∈ footprint regs :=
  Finset.mem_image.mpr
    ⟨slot, Finset.mem_univ slot, rfl⟩

private theorem physical_slot_mem
    (regs : NeighborhoodTrial.Registers controller)
    {slot : Fin 34} :
      slot.val = 0 ∨ slot.val = 1 ∨ slot.val = 4 ∨
      slot.val = 5 ∨ slot.val = 6 ∨ slot.val = 9 ∨
      slot.val = 10 ∨ slot.val = 11 ∨ slot.val = 12 ∨
      slot.val = 17 ∨ slot.val = 18 ∨ slot.val = 19 ∨
      slot.val = 20 ∨ slot.val = 29 ∨ slot.val = 30 ∨
      slot.val = 31 ∨ slot.val = 32 →
        regs.index slot ∈ footprint regs := by
  intro hslot
  fin_cases slot <;> simp_all [footprint, writeMap]
  all_goals
    first
    | exact ⟨0, rfl⟩
    | exact ⟨1, rfl⟩
    | exact ⟨2, rfl⟩
    | exact ⟨3, rfl⟩
    | exact ⟨4, rfl⟩
    | exact ⟨5, rfl⟩
    | exact ⟨6, rfl⟩
    | exact ⟨7, rfl⟩
    | exact ⟨8, rfl⟩
    | exact ⟨9, rfl⟩
    | exact ⟨10, rfl⟩
    | exact ⟨11, rfl⟩
    | exact ⟨12, rfl⟩
    | exact ⟨13, rfl⟩
    | exact ⟨14, rfl⟩
    | exact ⟨15, rfl⟩
    | exact ⟨16, rfl⟩

private theorem bank_footprint_subset
    (regs : NeighborhoodTrial.Registers controller) :
    (bankRegisters regs).footprint ⊆ footprint regs := by
  intro address haddress
  simp only [NeighborhoodProgram.BankRegisters.footprint,
    Finset.mem_image, Finset.mem_univ, true_and] at haddress
  obtain ⟨slot, rfl⟩ := haddress
  apply physical_slot_mem regs
  fin_cases slot <;>
    simp [PackedLocalHeadScan.bankMap]

private theorem headScan_footprint_subset
    (regs : NeighborhoodTrial.Registers controller) :
    PackedLocalHeadScan.footprint regs ⊆ footprint regs := by
  intro address haddress
  simp only [PackedLocalHeadScan.footprint, Finset.mem_union,
    NeighborhoodProgram.BankRegisters.footprint,
    Finset.mem_image, Finset.mem_univ, true_and,
    Finset.mem_singleton] at haddress
  rcases haddress with ⟨slot, rfl⟩ | rfl
  · exact bank_footprint_subset regs
      ((bankRegisters regs).index_mem_footprint slot)
  · apply physical_slot_mem regs
    simp

private theorem control_footprint_subset
    (regs : NeighborhoodTrial.Registers controller) :
    ControlDecode.scratchFootprint regs ⊆ footprint regs := by
  intro address haddress
  simp only [ControlDecode.scratchFootprint,
    Finset.mem_image, Finset.mem_univ, true_and] at haddress
  obtain ⟨slot, rfl⟩ := haddress
  apply physical_slot_mem regs
  fin_cases slot <;>
    simp [ControlDecode.scratchMap]

private theorem center_footprint_subset
    (regs : NeighborhoodTrial.Registers controller) :
    CombineSafeCenter.footprint regs ⊆ footprint regs := by
  intro address haddress
  simp only [CombineSafeCenter.footprint,
    Finset.mem_image, Finset.mem_univ, true_and] at haddress
  obtain ⟨slot, rfl⟩ := haddress
  apply physical_slot_mem regs
  fin_cases slot <;>
    simp [CombineSafeCenter.scratchMap]

private theorem copy_writesWithin
    (regs : NeighborhoodTrial.Registers controller)
    (destination source : ℕ)
    (hdestination : destination ∈ footprint regs) :
    Footprint.CmdWritesWithin (footprint regs)
      (copy destination source) := by
  exact ⟨hdestination, hdestination⟩

private theorem seqList_writesWithin
    (regs : NeighborhoodTrial.Registers controller)
    (commands : List Cmd)
    (hcommands :
      ∀ command ∈ commands,
        Footprint.CmdWritesWithin (footprint regs) command) :
    Footprint.CmdWritesWithin (footprint regs)
      (Cmd.seqList commands) := by
  induction commands with
  | nil =>
      trivial
  | cons first rest ih =>
      cases rest with
      | nil =>
          exact hcommands first (by simp)
      | cons second rest =>
          exact
            ⟨hcommands first (by simp),
              ih (by
                intro command hcommand
                exact hcommands command (by simp [hcommand]))⟩

private theorem initializeBank_writesWithin
    (tm : TM workTapeCount)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (footprint regs)
      (initializeBank tm regs) := by
  simp only [initializeBank, Cmd.basics]
  exact
    ⟨bank_footprint_subset regs
        ((bankRegisters regs).index_mem_footprint 2),
      bank_footprint_subset regs
        ((bankRegisters regs).index_mem_footprint 3),
      bank_footprint_subset regs
        ((bankRegisters regs).index_mem_footprint 6)⟩

private theorem restoreRangeOne_writesWithin
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (footprint regs)
      (restoreRangeOne regs) := by
  apply physical_slot_mem regs
  simp

private theorem equalImmediate_writesWithin
    (regs : NeighborhoodTrial.Registers controller)
    (value output : ℕ) (constant : ℕ)
    (houtput : output ∈ footprint regs) :
    Footprint.CmdWritesWithin (footprint regs)
      (equalImmediate regs value output constant) := by
  simp only [equalImmediate, Cmd.seqList,
    Footprint.CmdWritesWithin, Footprint.BasicWritesWithin]
  exact
    ⟨bank_footprint_subset regs
        ((bankRegisters regs).index_mem_footprint 7),
      bank_footprint_subset regs
        ((bankRegisters regs).index_mem_footprint 5),
      bank_footprint_subset regs
        ((bankRegisters regs).index_mem_footprint 4),
      houtput⟩

private theorem readState_writesWithin
    (tm : TM workTapeCount)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (footprint regs)
      (readState tm regs) := by
  simp only [readState, Cmd.seqList, Footprint.CmdWritesWithin,
    Footprint.BasicWritesWithin]
  exact
    ⟨initializeBank_writesWithin tm regs,
      bank_footprint_subset regs
        ((bankRegisters regs).index_mem_footprint 8),
      cmdWritesWithin_mono
        (NeighborhoodProgram.bankRead_sourceWritesWithin
          (bankRegisters regs))
        (bank_footprint_subset regs),
      restoreRangeOne_writesWithin regs⟩

private theorem replaceState_writesWithin
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (nextState : tm.Q)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (footprint regs)
      (replaceState tm order nextState regs) := by
  simp only [replaceState, Cmd.seqList, Footprint.CmdWritesWithin,
    Footprint.BasicWritesWithin]
  exact
    ⟨initializeBank_writesWithin tm regs,
      bank_footprint_subset regs
        ((bankRegisters regs).index_mem_footprint 8),
      bank_footprint_subset regs
        ((bankRegisters regs).index_mem_footprint 11),
      cmdWritesWithin_mono
        (NeighborhoodProgram.bankReplace_sourceWritesWithin
          (bankRegisters regs))
        (bank_footprint_subset regs),
      restoreRangeOne_writesWithin regs⟩

private theorem dispatchGamma_writesWithin
    (regs : NeighborhoodTrial.Registers controller)
    (next : Γ → Cmd)
    (hnext :
      ∀ symbol,
        Footprint.CmdWritesWithin (footprint regs)
          (next symbol)) :
    Footprint.CmdWritesWithin (footprint regs)
      (dispatchGamma regs next) := by
  simp only [dispatchGamma, Footprint.CmdWritesWithin,
    Footprint.BasicWritesWithin]
  exact
    ⟨hnext .zero,
      bank_footprint_subset regs
        ((bankRegisters regs).index_mem_footprint 5),
      hnext .one,
      bank_footprint_subset regs
        ((bankRegisters regs).index_mem_footprint 5),
      hnext .blank,
      hnext .start⟩

private theorem scanAndDispatch_writesWithin
    (tm : TM workTapeCount)
    (tape : TapeIndex workTapeCount)
    (regs : NeighborhoodTrial.Registers controller)
    (next : Γ → Cmd)
    (hnext :
      ∀ symbol,
        Footprint.CmdWritesWithin (footprint regs)
          (next symbol)) :
    Footprint.CmdWritesWithin (footprint regs)
      (scanAndDispatch tm tape regs next) := by
  simp only [scanAndDispatch, Cmd.seqList,
    Footprint.CmdWritesWithin, Footprint.BasicWritesWithin]
  exact
    ⟨cmdWritesWithin_mono
        (PackedLocalHeadScan.scan_writesWithin tm tape regs)
        (headScan_footprint_subset regs),
      bank_footprint_subset regs
        ((bankRegisters regs).index_mem_footprint 6),
      dispatchGamma_writesWithin regs next hnext⟩

private theorem dispatchWorkHeads_writesWithin
    (tm : TM workTapeCount)
    (regs : NeighborhoodTrial.Registers controller)
    (next : (Fin workTapeCount → Γ) → Cmd)
    (hnext :
      ∀ symbols,
        Footprint.CmdWritesWithin (footprint regs)
          (next symbols)) :
    ∀ tapes workHeads,
      Footprint.CmdWritesWithin (footprint regs)
        (dispatchWorkHeads tm regs next tapes workHeads) := by
  intro tapes
  induction tapes with
  | nil =>
      intro workHeads
      exact hnext workHeads
  | cons tape tapes ih =>
      intro workHeads
      apply scanAndDispatch_writesWithin
      intro symbol
      exact ih (Function.update workHeads tape symbol)

private theorem deriveTapeCenter_writesWithin
    (workTapeCount : ℕ)
    (controller : SearchProgram.Registers)
    (tape : TapeIndex workTapeCount)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (footprint regs)
      (deriveTapeCenter workTapeCount controller tape regs) := by
  simp only [deriveTapeCenter, Cmd.seqList,
    Footprint.CmdWritesWithin, Footprint.BasicWritesWithin]
  exact
    ⟨cmdWritesWithin_mono
        (ControlDecode.decodeNode_writesWithin regs)
        (control_footprint_subset regs),
      physical_slot_mem regs (by
        simp),
      cmdWritesWithin_mono
        (CombineSafeCenter.deriveCenter_writesWithin
          workTapeCount controller regs)
        (center_footprint_subset regs)⟩

private theorem saveRangeContext_writesWithin
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (footprint regs)
      (saveRangeContext regs) := by
  constructor
  · apply copy_writesWithin
    apply physical_slot_mem regs
    simp
  · apply copy_writesWithin
    apply physical_slot_mem regs
    simp

private theorem restoreRangeContext_writesWithin
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (footprint regs)
      (restoreRangeContext regs) := by
  simp only [restoreRangeContext, Cmd.seqList,
    Footprint.CmdWritesWithin]
  exact
    ⟨copy_writesWithin regs _ _
        (physical_slot_mem regs (by
          simp)),
      copy_writesWithin regs _ _
        (physical_slot_mem regs (by
          simp)),
      restoreRangeOne_writesWithin regs⟩

private theorem recordOrigin_writesWithin
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (footprint regs)
      (recordOrigin regs) := by
  simp only [recordOrigin, Cmd.seqList,
    Footprint.CmdWritesWithin, Footprint.BasicWritesWithin]
  exact
    ⟨bank_footprint_subset regs
        ((bankRegisters regs).index_mem_footprint 6),
      bank_footprint_subset regs
        ((bankRegisters regs).index_mem_footprint 5),
      bank_footprint_subset regs
        ((bankRegisters regs).index_mem_footprint 5),
      bank_footprint_subset regs
        ((bankRegisters regs).index_mem_footprint 5),
      physical_slot_mem regs (by simp),
      physical_slot_mem regs (by simp)⟩

private theorem prepareSavedCellIndex_writesWithin
    (tape : TapeIndex workTapeCount)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (footprint regs)
      (prepareSavedCellIndex tape regs) := by
  simp only [prepareSavedCellIndex, Cmd.basics]
  repeat' apply And.intro
  all_goals
    apply bank_footprint_subset regs
    exact (bankRegisters regs).index_mem_footprint _

private theorem readSavedCell_writesWithin
    (tm : TM workTapeCount)
    (tape : TapeIndex workTapeCount)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (footprint regs)
      (readSavedCell tm tape regs) := by
  simp only [readSavedCell, Cmd.seqList,
    Footprint.CmdWritesWithin]
  exact
    ⟨initializeBank_writesWithin tm regs,
      prepareSavedCellIndex_writesWithin tape regs,
      cmdWritesWithin_mono
        (NeighborhoodProgram.bankRead_sourceWritesWithin
          (bankRegisters regs))
        (bank_footprint_subset regs),
      restoreRangeOne_writesWithin regs⟩

private theorem replaceSavedCell_writesWithin
    (tm : TM workTapeCount)
    (tape : TapeIndex workTapeCount)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (footprint regs)
      (replaceSavedCell tm tape regs) := by
  simp only [replaceSavedCell, Cmd.seqList,
    Footprint.CmdWritesWithin]
  exact
    ⟨initializeBank_writesWithin tm regs,
      prepareSavedCellIndex_writesWithin tape regs,
      cmdWritesWithin_mono
        (NeighborhoodProgram.bankReplace_sourceWritesWithin
          (bankRegisters regs))
        (bank_footprint_subset regs),
      restoreRangeOne_writesWithin regs⟩

private theorem prepareOldCell_writesWithin
    (write : Option Γw)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (footprint regs)
      (prepareOldCell write regs) := by
  cases write with
  | none =>
      simp only [prepareOldCell, Footprint.CmdWritesWithin,
        Footprint.BasicWritesWithin]
      exact
        ⟨bank_footprint_subset regs
            ((bankRegisters regs).index_mem_footprint 7),
          bank_footprint_subset regs
            ((bankRegisters regs).index_mem_footprint 11)⟩
  | some symbol =>
      simp only [prepareOldCell, Footprint.CmdWritesWithin,
        Footprint.BasicWritesWithin]
      exact
        ⟨bank_footprint_subset regs
            ((bankRegisters regs).index_mem_footprint 11),
          bank_footprint_subset regs
            ((bankRegisters regs).index_mem_footprint 7),
          bank_footprint_subset regs
            ((bankRegisters regs).index_mem_footprint 11)⟩

private theorem moveSavedHead_writesWithin
    (direction : Dir3)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (footprint regs)
      (moveSavedHead direction regs) := by
  cases direction <;>
    simp only [moveSavedHead, Footprint.CmdWritesWithin,
      Footprint.BasicWritesWithin]
  · apply physical_slot_mem regs
    simp
  · apply physical_slot_mem regs
    simp

private theorem markSavedCell_writesWithin
    (tm : TM workTapeCount)
    (tape : TapeIndex workTapeCount)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (footprint regs)
      (markSavedCell tm tape regs) := by
  simp only [markSavedCell, Cmd.seqList,
    Footprint.CmdWritesWithin, Footprint.BasicWritesWithin]
  exact
    ⟨readSavedCell_writesWithin tm tape regs,
      bank_footprint_subset regs
        ((bankRegisters regs).index_mem_footprint 7),
      bank_footprint_subset regs
        ((bankRegisters regs).index_mem_footprint 11),
      replaceSavedCell_writesWithin tm tape regs⟩

private theorem updateTape_writesWithin
    (tm : TM workTapeCount)
    (controller : SearchProgram.Registers)
    (tape : TapeIndex workTapeCount)
    (write : Option Γw)
    (direction : Dir3)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (footprint regs)
      (updateTape tm controller tape write direction regs) := by
  simp only [updateTape, Cmd.seqList,
    Footprint.CmdWritesWithin, Footprint.BasicWritesWithin]
  exact
    ⟨cmdWritesWithin_mono
        (PackedLocalHeadScan.scan_writesWithin tm tape regs)
        (headScan_footprint_subset regs),
      copy_writesWithin regs _ _
        (physical_slot_mem regs (by
          simp)),
      saveRangeContext_writesWithin regs,
      deriveTapeCenter_writesWithin
        workTapeCount controller tape regs,
      restoreRangeContext_writesWithin regs,
      recordOrigin_writesWithin regs,
      readSavedCell_writesWithin tm tape regs,
      prepareOldCell_writesWithin write regs,
      replaceSavedCell_writesWithin tm tape regs,
      initializeBank_writesWithin tm regs,
      moveSavedHead_writesWithin direction regs,
      markSavedCell_writesWithin tm tape regs,
      bank_footprint_subset regs
        ((bankRegisters regs).index_mem_footprint 6),
      restoreRangeOne_writesWithin regs⟩

private theorem transitionAction_writesWithin
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (state : tm.Q) (inputSymbol : Γ)
    (workSymbols : Fin workTapeCount → Γ)
    (outputSymbol : Γ) :
    Footprint.CmdWritesWithin (footprint regs)
      (transitionAction tm order controller regs state inputSymbol
        workSymbols outputSymbol) := by
  simp only [transitionAction]
  generalize hdelta :
      tm.δ state inputSymbol workSymbols outputSymbol = transition
  rcases transition with
    ⟨nextState, workWrites, outputWrite, inputDirection,
      workDirections, outputDirection⟩
  apply seqList_writesWithin
  intro command hcommand
  simp only [hdelta] at hcommand
  rcases List.mem_append.mp hcommand with hprefix | htail
  · rcases List.mem_append.mp hprefix with hinput | hwork
    · simp only [List.mem_singleton] at hinput
      subst command
      exact updateTape_writesWithin tm controller
        (TapeIndex.input workTapeCount) none inputDirection regs
    · simp only [List.mem_map] at hwork
      obtain ⟨tape, _htape, rfl⟩ := hwork
      exact updateTape_writesWithin tm controller
        (TapeIndex.work tape) (some (workWrites tape))
        (workDirections tape) regs
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at htail
    rcases htail with hout | hstate
    · subst command
      exact updateTape_writesWithin tm controller
        (TapeIndex.output workTapeCount) (some outputWrite)
        outputDirection regs
    · subst command
      exact replaceState_writesWithin tm order nextState regs

private theorem dispatchTransition_writesWithin
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (state : tm.Q) :
    Footprint.CmdWritesWithin (footprint regs)
      (dispatchTransition tm order controller regs state) := by
  simp only [dispatchTransition]
  split
  · trivial
  · apply scanAndDispatch_writesWithin
    intro inputSymbol
    apply dispatchWorkHeads_writesWithin
    intro workSymbols
    apply scanAndDispatch_writesWithin
    intro outputSymbol
    exact transitionAction_writesWithin tm order controller regs
      state inputSymbol workSymbols outputSymbol

private theorem dispatchStates_writesWithin
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) :
    ∀ sourceStates,
      Footprint.CmdWritesWithin (footprint regs)
        (dispatchStates tm order controller regs sourceStates) := by
  intro sourceStates
  induction sourceStates with
  | nil =>
      trivial
  | cons state sourceStates ih =>
      simp only [dispatchStates, Footprint.CmdWritesWithin]
      exact
        ⟨equalImmediate_writesWithin regs _ _ _
            (bank_footprint_subset regs
              ((bankRegisters regs).index_mem_footprint 1)),
          dispatchTransition_writesWithin
            tm order controller regs state,
          ih⟩

theorem step_writesWithin_internal
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (footprint regs)
      (step tm order controller regs) := by
  exact
    ⟨readState_writesWithin tm regs,
      dispatchStates_writesWithin tm order controller regs
        (states tm order)⟩

theorem step_compiledWritesWithin_internal
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) :
    RAM.RegisterStore.DenseOverlay.FixedRegisters.Footprint.ProgramWritesWithin
      (step tm order controller regs).compile
      (footprint regs) :=
  Footprint.programWritesWithin_compile
    (step_writesWithin_internal tm order controller regs)

private theorem tapeAt_updateNamedTape_same
    (cfg : Cfg workTapeCount Q)
    (tape : TapeIndex workTapeCount)
    (write : Option Γw) (direction : Dir3) :
    tapeAt (updateNamedTape cfg tape write direction) tape =
      tapeAction (tapeAt cfg tape) write direction := by
  unfold updateNamedTape tapeAt
  split_ifs with hinput houtput <;> simp_all [tapeAction]

private theorem tapeAt_updateNamedTape_ne
    (cfg : Cfg workTapeCount Q)
    (selected tape : TapeIndex workTapeCount)
    (write : Option Γw) (direction : Dir3)
    (hne : tape ≠ selected) :
    tapeAt (updateNamedTape cfg selected write direction) tape =
      tapeAt cfg tape := by
  unfold updateNamedTape tapeAt
  split_ifs with hselectedInput hselectedOutput hinput houtput <;>
    simp_all [Function.update]
  · exfalso
    apply hne
    apply Fin.ext
    omega
  · intro heq
    exfalso
    apply hne
    apply Fin.ext
    omega

private theorem fixed_index_not_mem_footprint
    (regs : NeighborhoodTrial.Registers controller)
    (slot : Fin 34)
    (hslot : ∀ writeSlot, slot ≠ writeMap writeSlot) :
    regs.index slot ∉ footprint regs := by
  intro hmember
  simp only [footprint, Finset.mem_image, Finset.mem_univ,
    true_and] at hmember
  obtain ⟨writeSlot, hwriteSlot⟩ := hmember
  exact hslot writeSlot (regs.injective hwriteSlot.symm)

private theorem fixed_index_not_mem_bank
    (regs : NeighborhoodTrial.Registers controller)
    (slot : Fin 34)
    (hslot :
      ∀ bankSlot, slot ≠ PackedLocalHeadScan.bankMap bankSlot) :
    regs.index slot ∉ (bankRegisters regs).footprint := by
  intro hmember
  simp only [NeighborhoodProgram.BankRegisters.footprint,
    Finset.mem_image, Finset.mem_univ, true_and] at hmember
  obtain ⟨bankSlot, hbankSlot⟩ := hmember
  exact hslot bankSlot (regs.injective hbankSlot.symm)

private theorem controller_guess_eq_of_runs
    (regs : NeighborhoodTrial.Registers controller)
    {command : Cmd} {initial final : Store}
    (hwrites : Footprint.CmdWritesWithin (footprint regs) command)
    (hrun : Runs command initial final) :
    final controller.guess = initial controller.guess := by
  apply Footprint.runs_eq_outside hwrites hrun
  intro hmember
  simp only [footprint, Finset.mem_image, Finset.mem_univ,
    true_and] at hmember
  obtain ⟨writeSlot, hwriteSlot⟩ := hmember
  exact regs.index_ne_controller (writeMap writeSlot) (2 : Fin 17)
    hwriteSlot

private theorem preservesABI_of_runs
    (regs : NeighborhoodTrial.Registers controller)
    {command : Cmd} {initial final : Store}
    (hwrites : Footprint.CmdWritesWithin (footprint regs) command)
    (hrun : Runs command initial final) :
    ControlDecode.PreservesABI regs initial final := by
  have fixed
      (slot : Fin 34)
      (hslot : ∀ writeSlot, slot ≠ writeMap writeSlot) :
      final (regs.index slot) = initial (regs.index slot) :=
    Footprint.runs_eq_outside hwrites hrun
      (fixed_index_not_mem_footprint regs slot hslot)
  exact
    { fuel_eq := fixed 22 (by
        intro slot
        fin_cases slot <;> decide)
      nodeCode_eq := fixed 23 (by
        intro slot
        fin_cases slot <;> decide)
      scalar_eq := fixed 25 (by
        intro slot
        fin_cases slot <;> decide)
      out_eq := fixed 26 (by
        intro slot
        fin_cases slot <;> decide)
      phaseCode_eq := fixed 27 (by
        intro slot
        fin_cases slot <;> decide)
      active_eq := fixed 28 (by
        intro slot
        fin_cases slot <;> decide)
      blockLength_eq := fixed 2 (by
        intro slot
        fin_cases slot <;> decide)
      horizon_eq := fixed 3 (by
        intro slot
        fin_cases slot <;> decide)
      chunkCount_eq := fixed 7 (by
        intro slot
        fin_cases slot <;> decide)
      chunkRadix_eq := fixed 8 (by
        intro slot
        fin_cases slot <;> decide)
      frameRadix_eq := fixed 13 (by
        intro slot
        fin_cases slot <;> decide)
      bankRadix_eq := fixed 14 (by
        intro slot
        fin_cases slot <;> decide)
      bankDigitCount_eq := fixed 15 (by
        intro slot
        fin_cases slot <;> decide)
      modulusPred_eq := fixed 16 (by
        intro slot
        fin_cases slot <;> decide)
      modulus_eq := fixed 24 (by
        intro slot
        fin_cases slot <;> decide) }

private theorem computationContext_of_runs
    {tm : TM workTapeCount}
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (nodeTape : TapeIndex workTapeCount)
    (slot : NeighborhoodGraph.Slot)
    (interval : ℕ)
    (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    {command : Cmd} {initial final : Store}
    (hwrites : Footprint.CmdWritesWithin (footprint regs) command)
    (hrun : Runs command initial final)
    (hcontext :
      CombineTerm.ComputationContext regs instanceData nodeTape slot
        interval logicalBank initial) :
    CombineTerm.ComputationContext regs instanceData nodeTape slot
      interval logicalBank final := by
  apply CombineTerm.Internal.computationContext_transport_internal
    regs instanceData nodeTape slot interval logicalBank hcontext
      (preservesABI_of_runs regs hwrites hrun)
  exact Footprint.runs_eq_outside hwrites hrun
    (fixed_index_not_mem_footprint regs 33 (by
      intro writeSlot
      fin_cases writeSlot <;> decide))

private theorem basics_runs (ops : List Basic) (store : Store) :
    Runs (Cmd.basics ops) store (Basic.execList ops store) := by
  obtain ⟨cost, space, hexec⟩ :=
    RAM.Structured.Internal.exec_basics_exists ops store
  exact ⟨ops.length, cost, space, hexec⟩

private theorem copy_runs
    (destination source : ℕ) (store : Store)
    (hne : destination ≠ source) :
    ∃ final,
      Runs (copy destination source) store final ∧
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

private theorem initializeBank_runs
    (tm : TM workTapeCount)
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store) (word : ℕ)
    (hword : store (bankRegisters regs).word = word) :
    ∃ final,
      Runs (initializeBank tm regs) store final ∧
      final (bankRegisters regs).word = word ∧
      final (bankRegisters regs).base =
        PackedLocalConfiguration.radix tm ∧
      final (bankRegisters regs).basePred =
        PackedLocalConfiguration.radix tm - 1 ∧
      final (bankRegisters regs).one = 1 ∧
      ∀ address,
        address ≠ (bankRegisters regs).base →
        address ≠ (bankRegisters regs).basePred →
        address ≠ (bankRegisters regs).one →
        final address = store address := by
  let ops : List Basic :=
    [.imm (bankRegisters regs).base
        (PackedLocalConfiguration.radix tm),
      .imm (bankRegisters regs).basePred
        (PackedLocalConfiguration.radix tm - 1),
      .imm (bankRegisters regs).one 1]
  let final := Basic.execList ops store
  refine ⟨final, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [initializeBank, ops] using basics_runs ops store
  · calc
      final (bankRegisters regs).word =
          store (bankRegisters regs).word := by
        simp [final, ops, Basic.execList, Basic.exec,
          bankRegisters, PackedLocalHeadScan.bankRegisters,
          PackedLocalHeadScan.bankMap, regs.injective.eq_iff]
      _ = word := hword
  · simp [final, ops, Basic.execList, Basic.exec,
      bankRegisters, PackedLocalHeadScan.bankRegisters,
      PackedLocalHeadScan.bankMap, regs.injective.eq_iff]
  · simp [final, ops, Basic.execList, Basic.exec,
      bankRegisters, PackedLocalHeadScan.bankRegisters,
      PackedLocalHeadScan.bankMap, regs.injective.eq_iff]
  · constructor
    · simp [final, ops, Basic.execList, Basic.exec,
        bankRegisters, PackedLocalHeadScan.bankRegisters]
    · intro address hbase hbasePred hone
      simp [final, ops, Basic.execList, Basic.exec,
        Function.update_of_ne, hbase, hbasePred, hone]

private theorem prepareSavedCellIndex_runs
    (tape : TapeIndex workTapeCount)
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store)
    (blockLength word saved replacement : ℕ)
    (hblock : store (Layout.blockLength regs) = blockLength)
    (hword : store (bankRegisters regs).word = word)
    (hsaved : store (savedHead regs) = saved)
    (hreplacement :
      store (bankRegisters regs).replacement = replacement)
    (hone : store (bankRegisters regs).one = 1) :
    ∃ final,
      Runs (prepareSavedCellIndex tape regs) store final ∧
      final (bankRegisters regs).indexCount =
        PackedLocalConfiguration.cellIndex blockLength tape saved ∧
      final (bankRegisters regs).word = word ∧
      final (bankRegisters regs).replacement = replacement ∧
      final (savedHead regs) = saved ∧
      final (Layout.blockLength regs) = blockLength ∧
      final (bankRegisters regs).one = 1 ∧
      ∀ address,
        address ≠ (bankRegisters regs).indexCount →
        address ≠ (bankRegisters regs).result →
        final address = store address := by
  let ops : List Basic :=
    [.imm (bankRegisters regs).indexCount 0,
      .add (bankRegisters regs).indexCount
        (Layout.blockLength regs) (bankRegisters regs).indexCount,
      .add (bankRegisters regs).indexCount
        (Layout.blockLength regs) (bankRegisters regs).indexCount,
      .add (bankRegisters regs).indexCount
        (Layout.blockLength regs) (bankRegisters regs).indexCount,
      .imm (bankRegisters regs).result tape.val,
      .mul (bankRegisters regs).indexCount
        (bankRegisters regs).result (bankRegisters regs).indexCount,
      .add (bankRegisters regs).indexCount
        (savedHead regs) (bankRegisters regs).indexCount,
      .add (bankRegisters regs).indexCount
        (bankRegisters regs).indexCount (bankRegisters regs).one]
  let final := Basic.execList ops store
  refine ⟨final, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [prepareSavedCellIndex, ops] using
      basics_runs ops store
  · simp [final, ops, Basic.execList, Basic.exec,
      bankRegisters, PackedLocalHeadScan.bankRegisters,
      PackedLocalHeadScan.bankMap, savedHead,
      CombineValue.rangeRegisters, regs.injective.eq_iff,
      PackedLocalConfiguration.cellIndex,
      PackedLocalConfiguration.tapeSpan, hblock]
    change
      store (savedHead regs) +
          tape.val * (blockLength + (blockLength + blockLength)) +
          store (bankRegisters regs).one =
        1 + tape.val * (3 * blockLength) + saved
    rw [hsaved, hone]
    have hthree :
        blockLength + (blockLength + blockLength) =
          3 * blockLength := by
      omega
    rw [hthree]
    omega
  · calc
      final (bankRegisters regs).word =
          store (bankRegisters regs).word := by
        simp [final, ops, Basic.execList, Basic.exec,
          bankRegisters, PackedLocalHeadScan.bankRegisters,
          PackedLocalHeadScan.bankMap, savedHead,
          CombineValue.rangeRegisters, regs.injective.eq_iff]
      _ = word := hword
  · calc
      final (bankRegisters regs).replacement =
          store (bankRegisters regs).replacement := by
        simp [final, ops, Basic.execList, Basic.exec,
          bankRegisters, PackedLocalHeadScan.bankRegisters,
          PackedLocalHeadScan.bankMap, savedHead,
          CombineValue.rangeRegisters, regs.injective.eq_iff]
      _ = replacement := hreplacement
  · calc
      final (savedHead regs) = store (savedHead regs) := by
        simp [final, ops, Basic.execList, Basic.exec,
          bankRegisters, PackedLocalHeadScan.bankRegisters,
          PackedLocalHeadScan.bankMap, savedHead,
          CombineValue.rangeRegisters, regs.injective.eq_iff]
      _ = saved := hsaved
  · calc
      final (Layout.blockLength regs) =
          store (Layout.blockLength regs) := by
        simp [final, ops, Basic.execList, Basic.exec,
          bankRegisters, PackedLocalHeadScan.bankRegisters,
          PackedLocalHeadScan.bankMap, savedHead,
          CombineValue.rangeRegisters, regs.injective.eq_iff]
      _ = blockLength := hblock
  · calc
      final (bankRegisters regs).one =
          store (bankRegisters regs).one := by
        simp [final, ops, Basic.execList, Basic.exec,
          bankRegisters, PackedLocalHeadScan.bankRegisters,
          PackedLocalHeadScan.bankMap, savedHead,
          CombineValue.rangeRegisters, regs.injective.eq_iff]
      _ = 1 := hone
  · intro address hindex hresult
    simp [final, ops, Basic.execList, Basic.exec,
      Function.update_of_ne, hindex, hresult]

private theorem readSavedCell_runs
    (tm : TM workTapeCount)
    (tape : TapeIndex workTapeCount)
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store)
    (blockLength word saved : ℕ)
    (hblock : store (Layout.blockLength regs) = blockLength)
    (hword : store (bankRegisters regs).word = word)
    (hsaved : store (savedHead regs) = saved) :
    ∃ final,
      Runs (readSavedCell tm tape regs) store final ∧
      final (bankRegisters regs).word = word ∧
      final (bankRegisters regs).result =
        PackedDigits.digit (PackedLocalConfiguration.radix tm) word
          (PackedLocalConfiguration.cellIndex blockLength tape saved) ∧
      final (savedHead regs) = saved ∧
      final (Layout.blockLength regs) = blockLength ∧
      final (bankRegisters regs).one = 1 ∧
      final (CombineValue.rangeRegisters regs).one = 1 ∧
      ∀ address, address ∉ (bankRegisters regs).footprint →
        final address = store address := by
  obtain ⟨initialized, hinitializeRun, hinitializedWord,
      hinitializedBase, hinitializedBasePred, hinitializedOne,
      hinitializedOutside⟩ :=
    initializeBank_runs tm regs store word hword
  have hinitializedSaved :
      initialized (savedHead regs) = saved := by
    rw [hinitializedOutside (savedHead regs)]
    · exact hsaved
    all_goals
      exact regs.injective.ne (by decide)
  have hinitializedBlock :
      initialized (Layout.blockLength regs) = blockLength := by
    rw [hinitializedOutside (Layout.blockLength regs)]
    · exact hblock
    all_goals
      exact regs.injective.ne (by decide)
  have hinitializedReplacement :
      initialized (bankRegisters regs).replacement =
        store (bankRegisters regs).replacement := by
    apply hinitializedOutside
    all_goals
      exact (bankRegisters regs).index_ne (by decide)
  obtain ⟨prepared, hprepareRun, hpreparedIndex,
      hpreparedWord, hpreparedReplacement, hpreparedSaved,
      hpreparedBlock, hpreparedOne, hpreparedOutside⟩ :=
    prepareSavedCellIndex_runs tape regs initialized
      blockLength word saved
      (store (bankRegisters regs).replacement)
      hinitializedBlock hinitializedWord hinitializedSaved
      hinitializedReplacement hinitializedOne
  have hpreparedBase :
      prepared (bankRegisters regs).base =
        PackedLocalConfiguration.radix tm := by
    rw [hpreparedOutside (bankRegisters regs).base
      ((bankRegisters regs).index_ne (by decide))
      ((bankRegisters regs).index_ne (by decide))]
    exact hinitializedBase
  have hpreparedBasePred :
      prepared (bankRegisters regs).basePred =
        PackedLocalConfiguration.radix tm - 1 := by
    rw [hpreparedOutside (bankRegisters regs).basePred
      ((bankRegisters regs).index_ne (by decide))
      ((bankRegisters regs).index_ne (by decide))]
    exact hinitializedBasePred
  obtain ⟨read, hreadRun, hreadWord, _hreadBuffer,
      _hreadIndex, _hreadCompleted, hreadResult, _hreadBase,
      _hreadBasePred, hreadOne, _hreadReplacement⟩ :=
    NeighborhoodProgram.bankRead_runs (bankRegisters regs) prepared
      (PackedLocalConfiguration.radix tm) word
      (PackedLocalConfiguration.cellIndex blockLength tape saved)
      (PackedLocalConfiguration.radix_pos tm) hpreparedWord
      hpreparedBase hpreparedBasePred hpreparedOne hpreparedIndex
  have hreadSaved :
      read (savedHead regs) = saved := by
    calc
      read (savedHead regs) = prepared (savedHead regs) := by
        simpa [savedHead, CombineValue.rangeRegisters] using
          Footprint.runs_eq_outside
            (NeighborhoodProgram.bankRead_sourceWritesWithin
              (bankRegisters regs))
            hreadRun
            (fixed_index_not_mem_bank regs 19 (by
              intro bankSlot
              fin_cases bankSlot <;> decide))
      _ = saved := hpreparedSaved
  have hreadBlock :
      read (Layout.blockLength regs) = blockLength := by
    calc
      read (Layout.blockLength regs) =
          prepared (Layout.blockLength regs) := by
        simpa using
          Footprint.runs_eq_outside
            (NeighborhoodProgram.bankRead_sourceWritesWithin
              (bankRegisters regs))
            hreadRun
            (fixed_index_not_mem_bank regs 2 (by
              intro bankSlot
              fin_cases bankSlot <;> decide))
      _ = blockLength := hpreparedBlock
  let final :=
    (Basic.imm (CombineValue.rangeRegisters regs).one 1).exec read
  have hrestoreRun :
      Runs (restoreRangeOne regs) read final := by
    exact Runs.basic _ _
  refine ⟨final, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [readSavedCell, Cmd.seqList] using
      Runs.seq hinitializeRun
        (Runs.seq hprepareRun (Runs.seq hreadRun hrestoreRun))
  · simpa [final, Basic.exec, CombineValue.rangeRegisters,
      bankRegisters, PackedLocalHeadScan.bankRegisters,
      PackedLocalHeadScan.bankMap, regs.injective.eq_iff] using
      hreadWord
  · simpa [final, Basic.exec, CombineValue.rangeRegisters,
      bankRegisters, PackedLocalHeadScan.bankRegisters,
      PackedLocalHeadScan.bankMap, regs.injective.eq_iff] using
      hreadResult
  · simpa [final, Basic.exec, CombineValue.rangeRegisters,
      savedHead, bankRegisters, PackedLocalHeadScan.bankRegisters,
      PackedLocalHeadScan.bankMap, regs.injective.eq_iff] using
      hreadSaved
  · simpa [final, Basic.exec, CombineValue.rangeRegisters,
      regs.injective.eq_iff] using hreadBlock
  · simpa [final, Basic.exec, CombineValue.rangeRegisters,
      bankRegisters, PackedLocalHeadScan.bankRegisters,
      PackedLocalHeadScan.bankMap, regs.injective.eq_iff] using
      hreadOne
  · simp [final, Basic.exec]
  · intro address haddress
    have outsideNe (slot : Fin 12) :
        address ≠ (bankRegisters regs).index slot := by
      intro heq
      apply haddress
      rw [heq]
      exact (bankRegisters regs).index_mem_footprint slot
    have hneRangeOne :
        address ≠ (CombineValue.rangeRegisters regs).one := by
      simpa [CombineValue.rangeRegisters, bankRegisters,
        PackedLocalHeadScan.bankRegisters, PackedLocalHeadScan.bankMap] using
        outsideNe 9
    calc
      final address = read address := by
        simp [final, Basic.exec, hneRangeOne]
      _ = prepared address :=
        Footprint.runs_eq_outside
          (NeighborhoodProgram.bankRead_sourceWritesWithin
            (bankRegisters regs))
          hreadRun haddress
      _ = initialized address :=
        hpreparedOutside address (outsideNe 8) (outsideNe 10)
      _ = store address :=
        hinitializedOutside address (outsideNe 2)
          (outsideNe 3) (outsideNe 6)

private theorem replaceSavedCell_runs
    (tm : TM workTapeCount)
    (tape : TapeIndex workTapeCount)
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store)
    (blockLength word saved replacement : ℕ)
    (hblock : store (Layout.blockLength regs) = blockLength)
    (hword : store (bankRegisters regs).word = word)
    (hsaved : store (savedHead regs) = saved)
    (hreplacement :
      store (bankRegisters regs).replacement = replacement) :
    ∃ final,
      Runs (replaceSavedCell tm tape regs) store final ∧
      final (bankRegisters regs).word =
        NeighborhoodProgram.replaceAt
          (PackedLocalConfiguration.radix tm) word
          (PackedLocalConfiguration.cellIndex blockLength tape saved)
          replacement ∧
      final (bankRegisters regs).result =
        PackedDigits.digit (PackedLocalConfiguration.radix tm) word
          (PackedLocalConfiguration.cellIndex blockLength tape saved) ∧
      final (savedHead regs) = saved ∧
      final (Layout.blockLength regs) = blockLength ∧
      final (bankRegisters regs).one = 1 ∧
      final (CombineValue.rangeRegisters regs).one = 1 ∧
      ∀ address, address ∉ (bankRegisters regs).footprint →
        final address = store address := by
  obtain ⟨initialized, hinitializeRun, hinitializedWord,
      hinitializedBase, hinitializedBasePred, hinitializedOne,
      hinitializedOutside⟩ :=
    initializeBank_runs tm regs store word hword
  have hinitializedSaved :
      initialized (savedHead regs) = saved := by
    rw [hinitializedOutside (savedHead regs)]
    · exact hsaved
    all_goals
      exact regs.injective.ne (by decide)
  have hinitializedBlock :
      initialized (Layout.blockLength regs) = blockLength := by
    rw [hinitializedOutside (Layout.blockLength regs)]
    · exact hblock
    all_goals
      exact regs.injective.ne (by decide)
  have hinitializedReplacement :
      initialized (bankRegisters regs).replacement = replacement := by
    rw [hinitializedOutside (bankRegisters regs).replacement]
    · exact hreplacement
    all_goals
      exact (bankRegisters regs).index_ne (by decide)
  obtain ⟨prepared, hprepareRun, hpreparedIndex,
      hpreparedWord, hpreparedReplacement, hpreparedSaved,
      hpreparedBlock, hpreparedOne, hpreparedOutside⟩ :=
    prepareSavedCellIndex_runs tape regs initialized
      blockLength word saved replacement hinitializedBlock
      hinitializedWord hinitializedSaved hinitializedReplacement
      hinitializedOne
  have hpreparedBase :
      prepared (bankRegisters regs).base =
        PackedLocalConfiguration.radix tm := by
    rw [hpreparedOutside (bankRegisters regs).base
      ((bankRegisters regs).index_ne (by decide))
      ((bankRegisters regs).index_ne (by decide))]
    exact hinitializedBase
  have hpreparedBasePred :
      prepared (bankRegisters regs).basePred =
        PackedLocalConfiguration.radix tm - 1 := by
    rw [hpreparedOutside (bankRegisters regs).basePred
      ((bankRegisters regs).index_ne (by decide))
      ((bankRegisters regs).index_ne (by decide))]
    exact hinitializedBasePred
  obtain ⟨replaced, hreplaceRun, hreplaceWord, _hreplaceBuffer,
      _hreplaceIndex, _hreplaceCompleted, hreplaceResult,
      _hreplaceBase, _hreplaceBasePred, hreplaceOne,
      _hreplaceReplacement⟩ :=
    NeighborhoodProgram.bankReplace_runs (bankRegisters regs) prepared
      (PackedLocalConfiguration.radix tm) word
      (PackedLocalConfiguration.cellIndex blockLength tape saved)
      replacement (PackedLocalConfiguration.radix_pos tm)
      hpreparedWord hpreparedBase hpreparedBasePred hpreparedOne
      hpreparedIndex hpreparedReplacement
  have hreplacedSaved :
      replaced (savedHead regs) = saved := by
    calc
      replaced (savedHead regs) = prepared (savedHead regs) := by
        simpa [savedHead, CombineValue.rangeRegisters] using
          Footprint.runs_eq_outside
            (NeighborhoodProgram.bankReplace_sourceWritesWithin
              (bankRegisters regs))
            hreplaceRun
            (fixed_index_not_mem_bank regs 19 (by
              intro bankSlot
              fin_cases bankSlot <;> decide))
      _ = saved := hpreparedSaved
  have hreplacedBlock :
      replaced (Layout.blockLength regs) = blockLength := by
    calc
      replaced (Layout.blockLength regs) =
          prepared (Layout.blockLength regs) := by
        simpa using
          Footprint.runs_eq_outside
            (NeighborhoodProgram.bankReplace_sourceWritesWithin
              (bankRegisters regs))
            hreplaceRun
            (fixed_index_not_mem_bank regs 2 (by
              intro bankSlot
              fin_cases bankSlot <;> decide))
      _ = blockLength := hpreparedBlock
  let final :=
    (Basic.imm (CombineValue.rangeRegisters regs).one 1).exec replaced
  have hrestoreRun :
      Runs (restoreRangeOne regs) replaced final := by
    exact Runs.basic _ _
  refine ⟨final, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [replaceSavedCell, Cmd.seqList] using
      Runs.seq hinitializeRun
        (Runs.seq hprepareRun (Runs.seq hreplaceRun hrestoreRun))
  · simpa [final, Basic.exec, CombineValue.rangeRegisters,
      bankRegisters, PackedLocalHeadScan.bankRegisters,
      PackedLocalHeadScan.bankMap, regs.injective.eq_iff] using
      hreplaceWord
  · simpa [final, Basic.exec, CombineValue.rangeRegisters,
      bankRegisters, PackedLocalHeadScan.bankRegisters,
      PackedLocalHeadScan.bankMap, regs.injective.eq_iff] using
      hreplaceResult
  · simpa [final, Basic.exec, CombineValue.rangeRegisters,
      savedHead, bankRegisters, PackedLocalHeadScan.bankRegisters,
      PackedLocalHeadScan.bankMap, regs.injective.eq_iff] using
      hreplacedSaved
  · simpa [final, Basic.exec, CombineValue.rangeRegisters,
      regs.injective.eq_iff] using hreplacedBlock
  · simpa [final, Basic.exec, CombineValue.rangeRegisters,
      bankRegisters, PackedLocalHeadScan.bankRegisters,
      PackedLocalHeadScan.bankMap, regs.injective.eq_iff] using
      hreplaceOne
  · simp [final, Basic.exec]
  · intro address haddress
    have outsideNe (slot : Fin 12) :
        address ≠ (bankRegisters regs).index slot := by
      intro heq
      apply haddress
      rw [heq]
      exact (bankRegisters regs).index_mem_footprint slot
    have hneRangeOne :
        address ≠ (CombineValue.rangeRegisters regs).one := by
      simpa [CombineValue.rangeRegisters, bankRegisters,
        PackedLocalHeadScan.bankRegisters, PackedLocalHeadScan.bankMap] using
        outsideNe 9
    calc
      final address = replaced address := by
        simp [final, Basic.exec, hneRangeOne]
      _ = prepared address :=
        Footprint.runs_eq_outside
          (NeighborhoodProgram.bankReplace_sourceWritesWithin
            (bankRegisters regs))
          hreplaceRun haddress
      _ = initialized address :=
        hpreparedOutside address (outsideNe 8) (outsideNe 10)
      _ = store address :=
        hinitializedOutside address (outsideNe 2)
          (outsideNe 3) (outsideNe 6)

private theorem two_replaceAt_represents
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (blockLength : ℕ)
    (centers : TapeIndex workTapeCount → ℕ)
    (cfg nextCfg : Cfg workTapeCount tm.Q)
    (suffix word oldIndex oldReplacement newIndex
      newReplacement : ℕ)
    (hrep :
      PackedLocalRepresentation.Represents tm order blockLength
        centers cfg suffix word)
    (holdIndex :
      oldIndex <
        PackedLocalConfiguration.digitCount
          workTapeCount blockLength)
    (hnewIndex :
      newIndex <
        PackedLocalConfiguration.digitCount
          workTapeCount blockLength)
    (holdReplacement :
      oldReplacement < PackedLocalConfiguration.radix tm)
    (hnewReplacement :
      newReplacement < PackedLocalConfiguration.radix tm)
    (hupdate :
      ∀ coordinate,
        coordinate <
            PackedLocalConfiguration.digitCount
              workTapeCount blockLength →
          PackedLocalConfiguration.configurationDigit
              tm order blockLength centers nextCfg coordinate =
            if coordinate = newIndex then
              newReplacement
            else if coordinate = oldIndex then
              oldReplacement
            else
              PackedLocalConfiguration.configurationDigit
                tm order blockLength centers cfg coordinate) :
    PackedLocalRepresentation.Represents tm order blockLength
      centers nextCfg suffix
      (NeighborhoodProgram.replaceAt
        (PackedLocalConfiguration.radix tm)
        (NeighborhoodProgram.replaceAt
          (PackedLocalConfiguration.radix tm) word oldIndex
          oldReplacement)
        newIndex newReplacement) := by
  constructor
  · intro coordinate hcoordinate
    rw [hupdate coordinate hcoordinate]
    by_cases hnew : coordinate = newIndex
    · subst coordinate
      rw [NeighborhoodProgram.replaceAt_digit_eq
        (PackedLocalConfiguration.radix_pos tm) hnewReplacement]
      simp
    · rw [NeighborhoodProgram.replaceAt_digit_ne
        (PackedLocalConfiguration.radix_pos tm) hnewReplacement hnew]
      by_cases hold : coordinate = oldIndex
      · subst coordinate
        rw [NeighborhoodProgram.replaceAt_digit_eq
          (PackedLocalConfiguration.radix_pos tm) holdReplacement]
        simp [hnew]
      · rw [NeighborhoodProgram.replaceAt_digit_ne
          (PackedLocalConfiguration.radix_pos tm) holdReplacement hold]
        simp [hnew, hold, hrep.digit_eq coordinate hcoordinate]
  · rw [PackedLocalRepresentation.drop_replaceAt
      (PackedLocalConfiguration.radix_pos tm) hnewIndex
      hnewReplacement]
    rw [PackedLocalRepresentation.drop_replaceAt
      (PackedLocalConfiguration.radix_pos tm) holdIndex
      holdReplacement]
    exact hrep.suffix_eq

private theorem tapeAction_head
    (tape : Tape) (write : Option Γw) (direction : Dir3) :
    (tapeAction tape write direction).head =
      (tape.move direction).head := by
  cases write <;> cases direction <;>
    simp [tapeAction, Tape.writeAndMove, Tape.move,
      Tape.write_head]

private theorem tapeAction_cells_of_ne
    (tape : Tape) (write : Option Γw) (direction : Dir3)
    (position : ℕ) (hne : position ≠ tape.head) :
    (tapeAction tape write direction).cells position =
      tape.cells position := by
  cases write with
  | none =>
      simp [tapeAction, Tape.move_cells]
  | some symbol =>
      by_cases hzero : tape.head = 0
      · cases direction <;>
          simp [tapeAction, Tape.writeAndMove, Tape.move,
            Tape.write, hzero]
      · cases direction <;>
          simp [tapeAction, Tape.writeAndMove, Tape.move,
            Tape.write, hzero, Function.update_of_ne, hne]

private theorem tapeAction_cells_head
    (tape : Tape) (write : Option Γw) (direction : Dir3) :
    (tapeAction tape write direction).cells tape.head =
      match write with
      | none => tape.cells tape.head
      | some symbol =>
          if tape.head = 0 then tape.cells tape.head else symbol.toΓ := by
  cases write with
  | none =>
      simp [tapeAction, Tape.move_cells]
  | some symbol =>
      by_cases hzero : tape.head = 0
      · simp [tapeAction, Tape.writeAndMove, Tape.move_cells,
          Tape.write, hzero]
      · simp [tapeAction, Tape.writeAndMove, Tape.move_cells,
          Tape.write, hzero]

private theorem absolutePosition_localHead
    (blockLength center head : ℕ)
    (hlower :
      PackedLocalConfiguration.windowStart blockLength center ≤ head) :
    PackedLocalConfiguration.absolutePosition blockLength center
        (PackedLocalConfiguration.localHead blockLength center head) =
      head := by
  simp [PackedLocalConfiguration.absolutePosition,
    PackedLocalConfiguration.localHead]
  omega

private theorem cellDigit_updateNamedTape
    (cfg : Cfg workTapeCount Q)
    (selected : TapeIndex workTapeCount)
    (write : Option Γw) (direction : Dir3)
    (blockLength : ℕ)
    (centers : TapeIndex workTapeCount → ℕ)
    (localPosition : ℕ)
    (hlower :
      PackedLocalConfiguration.windowStart blockLength
          (centers selected) ≤
        (tapeAt cfg selected).head)
    (hnextLower :
      PackedLocalConfiguration.windowStart blockLength
          (centers selected) ≤
        (tapeAction (tapeAt cfg selected) write direction).head) :
    let current := tapeAt cfg selected
    let updated := tapeAction current write direction
    let oldLocal :=
      PackedLocalConfiguration.localHead blockLength
        (centers selected) current.head
    let newLocal :=
      PackedLocalConfiguration.localHead blockLength
        (centers selected) updated.head
    PackedLocalConfiguration.cellDigit
        (updateNamedTape cfg selected write direction)
        blockLength centers selected localPosition =
      if localPosition = newLocal then
        CompactValueCodeSemantics.gammaCode
            (updated.cells updated.head) + 4
      else if localPosition = oldLocal then
        CompactValueCodeSemantics.gammaCode
          (updated.cells current.head)
      else
        PackedLocalConfiguration.cellDigit cfg blockLength centers
          selected localPosition := by
  dsimp only
  simp only [PackedLocalConfiguration.cellDigit]
  rw [tapeAt_updateNamedTape_same]
  let current := tapeAt cfg selected
  let updated := tapeAction current write direction
  let oldLocal :=
    PackedLocalConfiguration.localHead blockLength
      (centers selected) current.head
  let newLocal :=
    PackedLocalConfiguration.localHead blockLength
      (centers selected) updated.head
  let position :=
    PackedLocalConfiguration.absolutePosition blockLength
      (centers selected) localPosition
  have holdAbsolute :
      PackedLocalConfiguration.absolutePosition blockLength
          (centers selected) oldLocal =
        current.head :=
    absolutePosition_localHead blockLength
      (centers selected) current.head hlower
  have hnewAbsolute :
      PackedLocalConfiguration.absolutePosition blockLength
          (centers selected) newLocal =
        updated.head :=
    absolutePosition_localHead blockLength
      (centers selected) updated.head hnextLower
  change
    CompactValueCodeSemantics.gammaCode (updated.cells position) +
          4 * (decide (updated.head = position)).toNat =
      if localPosition = newLocal then
        CompactValueCodeSemantics.gammaCode
            (updated.cells updated.head) + 4
      else if localPosition = oldLocal then
        CompactValueCodeSemantics.gammaCode
          (updated.cells current.head)
      else
        CompactValueCodeSemantics.gammaCode (current.cells position) +
          4 * (decide (current.head = position)).toNat
  by_cases hnew : localPosition = newLocal
  · subst localPosition
    dsimp only [position]
    simp [hnewAbsolute]
  · rw [if_neg hnew]
    by_cases hold : localPosition = oldLocal
    · subst localPosition
      rw [if_pos rfl]
      have hheadNe : updated.head ≠ current.head := by
        intro heq
        apply hnew
        dsimp only [newLocal, oldLocal]
        simp only [PackedLocalConfiguration.localHead, heq]
      dsimp only [position]
      simp [holdAbsolute, hheadNe]
    · rw [if_neg hold]
      have hpositionOld : position ≠ current.head := by
        intro heq
        apply hold
        dsimp only [position] at heq
        rw [← holdAbsolute] at heq
        simp only [PackedLocalConfiguration.absolutePosition] at heq
        omega
      have hpositionNew : updated.head ≠ position := by
        intro heq
        apply hnew
        dsimp only [position] at heq
        rw [← hnewAbsolute] at heq
        simp only [PackedLocalConfiguration.absolutePosition] at heq
        omega
      rw [tapeAction_cells_of_ne current write direction
        position hpositionOld]
      simp [hpositionNew, Ne.symm hpositionOld]

private theorem cellIndex_injective
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (firstTape secondTape : TapeIndex workTapeCount)
    (firstPosition secondPosition : ℕ)
    (hfirst :
      firstPosition <
        PackedLocalConfiguration.tapeSpan blockLength)
    (hsecond :
      secondPosition <
        PackedLocalConfiguration.tapeSpan blockLength)
    (heq :
      PackedLocalConfiguration.cellIndex blockLength firstTape
          firstPosition =
        PackedLocalConfiguration.cellIndex blockLength secondTape
          secondPosition) :
    firstTape = secondTape ∧ firstPosition = secondPosition := by
  let span := PackedLocalConfiguration.tapeSpan blockLength
  have hspan : 0 < span := by
    simp [span, PackedLocalConfiguration.tapeSpan]
    omega
  have hflat :
      firstTape.val * span + firstPosition =
        secondTape.val * span + secondPosition := by
    simp only [PackedLocalConfiguration.cellIndex] at heq
    change
      1 + firstTape.val * span + firstPosition =
        1 + secondTape.val * span + secondPosition at heq
    omega
  have hposition : firstPosition = secondPosition := by
    have hfirstSpan : firstPosition < span := hfirst
    have hsecondSpan : secondPosition < span := hsecond
    have hmod := congrArg (fun value => value % span) hflat
    simpa [Nat.add_mod, Nat.mul_mod,
      Nat.mod_eq_of_lt hfirstSpan,
      Nat.mod_eq_of_lt hsecondSpan] using hmod
  subst secondPosition
  have hmul :
      firstTape.val * span = secondTape.val * span := by
    omega
  constructor
  · apply Fin.ext
    exact Nat.eq_of_mul_eq_mul_right hspan hmul
  · rfl

private theorem coordinate_decompose
    (workTapeCount blockLength coordinate : ℕ)
    (hpositive : 0 < blockLength)
    (hcoordinatePos : coordinate ≠ 0)
    (hcoordinate :
      coordinate <
        PackedLocalConfiguration.digitCount
          workTapeCount blockLength) :
    ∃ (tape : TapeIndex workTapeCount) (localPosition : ℕ),
      localPosition <
          PackedLocalConfiguration.tapeSpan blockLength ∧
      coordinate =
        PackedLocalConfiguration.cellIndex
          blockLength tape localPosition := by
  let span := PackedLocalConfiguration.tapeSpan blockLength
  let flat := coordinate - 1
  let tapeNumber := flat / span
  let localPosition := flat % span
  have hspan : 0 < span := by
    simp [span, PackedLocalConfiguration.tapeSpan]
    omega
  have hflat :
      flat <
        (workTapeCount + 2) * span := by
    dsimp only [flat, span]
    unfold PackedLocalConfiguration.digitCount at hcoordinate
    omega
  have htapeNumber : tapeNumber < workTapeCount + 2 := by
    apply (Nat.div_lt_iff_lt_mul hspan).2
    simpa [Nat.mul_comm] using hflat
  let tape : TapeIndex workTapeCount :=
    PackedLocalConfiguration.tapeOfNat workTapeCount tapeNumber
  have htape :
      tape.val = tapeNumber := by
    simp [tape, PackedLocalConfiguration.tapeOfNat,
      Nat.mod_eq_of_lt htapeNumber]
  have hlocal : localPosition < span :=
    Nat.mod_lt flat hspan
  refine ⟨tape, localPosition, hlocal, ?_⟩
  have hsplit :
      tapeNumber * span + localPosition = flat := by
    simpa [tapeNumber, localPosition, Nat.mul_comm] using
      Nat.div_add_mod flat span
  simp only [PackedLocalConfiguration.cellIndex]
  rw [htape]
  dsimp only [flat] at hsplit
  dsimp only [localPosition, tapeNumber, span] at hsplit ⊢
  omega

private theorem state_updateNamedTape
    (cfg : Cfg workTapeCount Q)
    (selected : TapeIndex workTapeCount)
    (write : Option Γw) (direction : Dir3) :
    (updateNamedTape cfg selected write direction).state = cfg.state := by
  unfold updateNamedTape
  split_ifs <;> rfl

private theorem configurationDigit_updateNamedTape
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (cfg : Cfg workTapeCount tm.Q)
    (selected : TapeIndex workTapeCount)
    (write : Option Γw) (direction : Dir3)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (centers : TapeIndex workTapeCount → ℕ)
    (hlower :
      PackedLocalConfiguration.windowStart blockLength
          (centers selected) ≤
        (tapeAt cfg selected).head)
    (hupper :
      (tapeAt cfg selected).head <
        PackedLocalConfiguration.windowStart blockLength
            (centers selected) +
          PackedLocalConfiguration.tapeSpan blockLength)
    (hnextLower :
      PackedLocalConfiguration.windowStart blockLength
          (centers selected) ≤
        (tapeAction (tapeAt cfg selected) write direction).head)
    (hnextUpper :
      (tapeAction (tapeAt cfg selected) write direction).head <
        PackedLocalConfiguration.windowStart blockLength
            (centers selected) +
          PackedLocalConfiguration.tapeSpan blockLength) :
    let current := tapeAt cfg selected
    let updated := tapeAction current write direction
    let nextCfg :=
      updateNamedTape cfg selected write direction
    let oldLocal :=
      PackedLocalConfiguration.localHead blockLength
        (centers selected) current.head
    let newLocal :=
      PackedLocalConfiguration.localHead blockLength
        (centers selected) updated.head
    let oldIndex :=
      PackedLocalConfiguration.cellIndex blockLength selected oldLocal
    let newIndex :=
      PackedLocalConfiguration.cellIndex blockLength selected newLocal
    let oldReplacement :=
      CompactValueCodeSemantics.gammaCode
        (updated.cells current.head)
    let newReplacement :=
      CompactValueCodeSemantics.gammaCode
          (updated.cells updated.head) + 4
    ∀ coordinate,
      coordinate <
          PackedLocalConfiguration.digitCount
            workTapeCount blockLength →
        PackedLocalConfiguration.configurationDigit
            tm order blockLength centers nextCfg coordinate =
          if coordinate = newIndex then
            newReplacement
          else if coordinate = oldIndex then
            oldReplacement
          else
            PackedLocalConfiguration.configurationDigit
              tm order blockLength centers cfg coordinate := by
  dsimp only
  intro coordinate hcoordinate
  let current := tapeAt cfg selected
  let updated := tapeAction current write direction
  let nextCfg :=
    updateNamedTape cfg selected write direction
  let oldLocal :=
    PackedLocalConfiguration.localHead blockLength
      (centers selected) current.head
  let newLocal :=
    PackedLocalConfiguration.localHead blockLength
      (centers selected) updated.head
  let oldIndex :=
    PackedLocalConfiguration.cellIndex blockLength selected oldLocal
  let newIndex :=
    PackedLocalConfiguration.cellIndex blockLength selected newLocal
  let oldReplacement :=
    CompactValueCodeSemantics.gammaCode
      (updated.cells current.head)
  let newReplacement :=
    CompactValueCodeSemantics.gammaCode
        (updated.cells updated.head) + 4
  change
    PackedLocalConfiguration.configurationDigit
        tm order blockLength centers nextCfg coordinate =
      if coordinate = newIndex then
        newReplacement
      else if coordinate = oldIndex then
        oldReplacement
      else
        PackedLocalConfiguration.configurationDigit
          tm order blockLength centers cfg coordinate
  have holdLocal :
      oldLocal <
        PackedLocalConfiguration.tapeSpan blockLength := by
    dsimp only [oldLocal, current]
    simp only [PackedLocalConfiguration.localHead]
    omega
  have hnewLocal :
      newLocal <
        PackedLocalConfiguration.tapeSpan blockLength := by
    dsimp only [newLocal, updated, current]
    simp only [PackedLocalConfiguration.localHead]
    omega
  by_cases hzero : coordinate = 0
  · subst coordinate
    have holdNe : 0 ≠ oldIndex := by
      dsimp only [oldIndex]
      unfold PackedLocalConfiguration.cellIndex
      omega
    have hnewNe : 0 ≠ newIndex := by
      dsimp only [newIndex]
      unfold PackedLocalConfiguration.cellIndex
      omega
    simp [PackedLocalConfiguration.configurationDigit, hnewNe, holdNe,
      nextCfg, state_updateNamedTape]
  · obtain ⟨tape, localPosition, hlocal, rfl⟩ :=
      coordinate_decompose workTapeCount blockLength coordinate
        hpositive hzero hcoordinate
    rw [PackedLocalConfiguration.configurationDigit_cell
      tm order blockLength hpositive centers nextCfg tape
        localPosition hlocal]
    rw [PackedLocalConfiguration.configurationDigit_cell
      tm order blockLength hpositive centers cfg tape
        localPosition hlocal]
    by_cases htape : tape = selected
    · subst tape
      rw [cellDigit_updateNamedTape cfg selected write direction
        blockLength centers localPosition hlower hnextLower]
      have hnewEq :
          PackedLocalConfiguration.cellIndex blockLength selected
              localPosition = newIndex ↔
            localPosition = newLocal := by
        simp [newIndex, PackedLocalConfiguration.cellIndex]
      have holdEq :
          PackedLocalConfiguration.cellIndex blockLength selected
              localPosition = oldIndex ↔
            localPosition = oldLocal := by
        simp [oldIndex, PackedLocalConfiguration.cellIndex]
      simp only [hnewEq, holdEq]
      rfl
    · have hnotNew :
          PackedLocalConfiguration.cellIndex blockLength tape
              localPosition ≠ newIndex := by
        intro heq
        apply htape
        exact
          (cellIndex_injective blockLength hpositive tape
            selected localPosition newLocal hlocal hnewLocal heq).1
      have hnotOld :
          PackedLocalConfiguration.cellIndex blockLength tape
              localPosition ≠ oldIndex := by
        intro heq
        apply htape
        exact
          (cellIndex_injective blockLength hpositive tape
            selected localPosition oldLocal hlocal holdLocal heq).1
      rw [if_neg hnotNew, if_neg hnotOld]
      simp only [PackedLocalConfiguration.cellDigit]
      rw [tapeAt_updateNamedTape_ne cfg selected tape write direction
        htape]

private theorem gammaCode_lt_four (symbol : Γ) :
    CompactValueCodeSemantics.gammaCode symbol < 4 := by
  cases symbol <;>
    simp [CompactValueCodeSemantics.gammaCode,
      NeighborhoodExecutableEvaluation.FiniteEncoding.gammaEquiv]

private theorem updateNamedTape_represents
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (centers : TapeIndex workTapeCount → ℕ)
    (cfg : Cfg workTapeCount tm.Q)
    (selected : TapeIndex workTapeCount)
    (write : Option Γw) (direction : Dir3)
    (suffix word : ℕ)
    (hrep :
      PackedLocalRepresentation.Represents tm order blockLength
        centers cfg suffix word)
    (hlower :
      PackedLocalConfiguration.windowStart blockLength
          (centers selected) ≤
        (tapeAt cfg selected).head)
    (hupper :
      (tapeAt cfg selected).head <
        PackedLocalConfiguration.windowStart blockLength
            (centers selected) +
          PackedLocalConfiguration.tapeSpan blockLength)
    (hnextLower :
      PackedLocalConfiguration.windowStart blockLength
          (centers selected) ≤
        (tapeAction (tapeAt cfg selected) write direction).head)
    (hnextUpper :
      (tapeAction (tapeAt cfg selected) write direction).head <
        PackedLocalConfiguration.windowStart blockLength
            (centers selected) +
          PackedLocalConfiguration.tapeSpan blockLength) :
    let current := tapeAt cfg selected
    let updated := tapeAction current write direction
    let oldLocal :=
      PackedLocalConfiguration.localHead blockLength
        (centers selected) current.head
    let newLocal :=
      PackedLocalConfiguration.localHead blockLength
        (centers selected) updated.head
    let oldIndex :=
      PackedLocalConfiguration.cellIndex blockLength selected oldLocal
    let newIndex :=
      PackedLocalConfiguration.cellIndex blockLength selected newLocal
    let oldReplacement :=
      CompactValueCodeSemantics.gammaCode
        (updated.cells current.head)
    let newReplacement :=
      CompactValueCodeSemantics.gammaCode
          (updated.cells updated.head) + 4
    PackedLocalRepresentation.Represents tm order blockLength centers
      (updateNamedTape cfg selected write direction) suffix
      (NeighborhoodProgram.replaceAt
        (PackedLocalConfiguration.radix tm)
        (NeighborhoodProgram.replaceAt
          (PackedLocalConfiguration.radix tm) word oldIndex
          oldReplacement)
        newIndex newReplacement) := by
  dsimp only
  let current := tapeAt cfg selected
  let updated := tapeAction current write direction
  let oldLocal :=
    PackedLocalConfiguration.localHead blockLength
      (centers selected) current.head
  let newLocal :=
    PackedLocalConfiguration.localHead blockLength
      (centers selected) updated.head
  let oldIndex :=
    PackedLocalConfiguration.cellIndex blockLength selected oldLocal
  let newIndex :=
    PackedLocalConfiguration.cellIndex blockLength selected newLocal
  let oldReplacement :=
    CompactValueCodeSemantics.gammaCode
      (updated.cells current.head)
  let newReplacement :=
    CompactValueCodeSemantics.gammaCode
        (updated.cells updated.head) + 4
  have holdLocal :
      oldLocal <
        PackedLocalConfiguration.tapeSpan blockLength := by
    dsimp only [oldLocal, current]
    simp only [PackedLocalConfiguration.localHead]
    omega
  have hnewLocal :
      newLocal <
        PackedLocalConfiguration.tapeSpan blockLength := by
    dsimp only [newLocal, updated, current]
    simp only [PackedLocalConfiguration.localHead]
    omega
  apply two_replaceAt_represents tm order blockLength centers cfg
    (updateNamedTape cfg selected write direction) suffix word
    oldIndex oldReplacement newIndex newReplacement hrep
  · exact PackedLocalConfiguration.cellIndex_lt_digitCount
      blockLength selected oldLocal holdLocal
  · exact PackedLocalConfiguration.cellIndex_lt_digitCount
      blockLength selected newLocal hnewLocal
  · have hcode :=
      gammaCode_lt_four (updated.cells current.head)
    exact lt_of_lt_of_le hcode (by
      simp [PackedLocalConfiguration.radix])
  · have hcode :=
      gammaCode_lt_four (updated.cells updated.head)
    have : newReplacement < 16 := by
      dsimp only [newReplacement]
      omega
    exact lt_of_lt_of_le this (by
      simp [PackedLocalConfiguration.radix])
  · exact configurationDigit_updateNamedTape tm order cfg
      selected write direction blockLength hpositive centers
      hlower hupper hnextLower hnextUpper

private theorem saveRangeContext_runs
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store) (accumulator count : ℕ)
    (haccumulator :
      store (CombineValue.rangeRegisters regs).accumulator =
        accumulator)
    (hcount :
      store (CombineValue.rangeRegisters regs).count = count) :
    ∃ final,
      Runs (saveRangeContext regs) store final ∧
      final (originFlag regs) = accumulator ∧
      final (CombineValue.rangeRegisters regs).one = count ∧
      ∀ address,
        address ≠ originFlag regs →
        address ≠ (CombineValue.rangeRegisters regs).one →
        final address = store address := by
  obtain ⟨savedAccumulator, hsaveAccumulatorRun,
      hsaveAccumulatorValue, hsaveAccumulatorOutside⟩ :=
    copy_runs (originFlag regs)
      (CombineValue.rangeRegisters regs).accumulator store
      (regs.injective.ne (by decide))
  have hsavedCount :
      savedAccumulator (CombineValue.rangeRegisters regs).count =
        count := by
    rw [hsaveAccumulatorOutside
      (CombineValue.rangeRegisters regs).count
      (regs.injective.ne (by decide))]
    exact hcount
  obtain ⟨final, hsaveCountRun, hsaveCountValue,
      hsaveCountOutside⟩ :=
    copy_runs (CombineValue.rangeRegisters regs).one
      (CombineValue.rangeRegisters regs).count savedAccumulator
      (regs.injective.ne (by decide))
  refine ⟨final, ?_, ?_, hsaveCountValue.trans hsavedCount, ?_⟩
  · simpa [saveRangeContext] using
      Runs.seq hsaveAccumulatorRun hsaveCountRun
  · rw [hsaveCountOutside (originFlag regs)
      (regs.injective.ne (by decide))]
    exact hsaveAccumulatorValue.trans haccumulator
  · intro address horigin hone
    rw [hsaveCountOutside address hone]
    exact hsaveAccumulatorOutside address horigin

private theorem restoreRangeContext_runs
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store) (accumulator count : ℕ)
    (horigin : store (originFlag regs) = accumulator)
    (hone :
      store (CombineValue.rangeRegisters regs).one = count) :
    ∃ final,
      Runs (restoreRangeContext regs) store final ∧
      final (CombineValue.rangeRegisters regs).accumulator =
        accumulator ∧
      final (CombineValue.rangeRegisters regs).count = count ∧
      final (CombineValue.rangeRegisters regs).one = 1 ∧
      ∀ address,
        address ≠ (CombineValue.rangeRegisters regs).accumulator →
        address ≠ (CombineValue.rangeRegisters regs).count →
        address ≠ (CombineValue.rangeRegisters regs).one →
        final address = store address := by
  obtain ⟨restoredAccumulator, hrestoreAccumulatorRun,
      hrestoreAccumulatorValue, hrestoreAccumulatorOutside⟩ :=
    copy_runs
      (CombineValue.rangeRegisters regs).accumulator
      (originFlag regs) store
      (regs.injective.ne (by decide))
  have hrestoredOne :
      restoredAccumulator (CombineValue.rangeRegisters regs).one =
        count := by
    rw [hrestoreAccumulatorOutside
      (CombineValue.rangeRegisters regs).one
      (regs.injective.ne (by decide))]
    exact hone
  obtain ⟨restoredCount, hrestoreCountRun,
      hrestoreCountValue, hrestoreCountOutside⟩ :=
    copy_runs (CombineValue.rangeRegisters regs).count
      (CombineValue.rangeRegisters regs).one restoredAccumulator
      (regs.injective.ne (by decide))
  let final :=
    (Basic.imm (CombineValue.rangeRegisters regs).one 1).exec
      restoredCount
  have hrestoreOneRun :
      Runs (restoreRangeOne regs) restoredCount final :=
    Runs.basic _ _
  refine ⟨final, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [restoreRangeContext, Cmd.seqList] using
      Runs.seq hrestoreAccumulatorRun
        (Runs.seq hrestoreCountRun hrestoreOneRun)
  · calc
      final (CombineValue.rangeRegisters regs).accumulator =
          restoredCount
            (CombineValue.rangeRegisters regs).accumulator := by
        simp [final, Basic.exec, CombineValue.rangeRegisters,
          regs.injective.eq_iff]
      _ = restoredAccumulator
            (CombineValue.rangeRegisters regs).accumulator := by
        rw [hrestoreCountOutside
          (CombineValue.rangeRegisters regs).accumulator
          (regs.injective.ne (by decide))]
      _ = accumulator := hrestoreAccumulatorValue.trans horigin
  · calc
      final (CombineValue.rangeRegisters regs).count =
          restoredCount (CombineValue.rangeRegisters regs).count := by
        simp [final, Basic.exec, CombineValue.rangeRegisters,
          regs.injective.eq_iff]
      _ = count := hrestoreCountValue.trans hrestoredOne
  · simp [final, Basic.exec]
  · intro address haccumulator hcount' hone'
    simp only [final, Basic.exec]
    rw [Function.update_of_ne hone']
    rw [hrestoreCountOutside address hcount']
    exact hrestoreAccumulatorOutside address haccumulator

private theorem recordOrigin_runs
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store) (blockLength center saved : ℕ)
    (hblock : store (Layout.blockLength regs) = blockLength)
    (hcenter :
      store (CombineSafeCenter.centerValue regs) = center)
    (hsaved : store (savedHead regs) = saved) :
    ∃ final,
      Runs (recordOrigin regs) store final ∧
      final (originFlag regs) =
        (if
            PackedLocalConfiguration.absolutePosition
                blockLength center saved = 0 then
            1
          else
            0) ∧
      ∀ address,
        address ≠ (bankRegisters regs).one →
        address ≠ (bankRegisters regs).test →
        address ≠ originFlag regs →
        final address = store address := by
  let first :=
    (Basic.imm (bankRegisters regs).one 1).exec store
  let second :=
    (Basic.sub (bankRegisters regs).test
      (CombineSafeCenter.centerValue regs)
      (bankRegisters regs).one).exec first
  let third :=
    (Basic.mul (bankRegisters regs).test
      (bankRegisters regs).test
      (Layout.blockLength regs)).exec second
  let prepared :=
    (Basic.add (bankRegisters regs).test
      (bankRegisters regs).test (savedHead regs)).exec third
  have hpreparedTest :
      prepared (bankRegisters regs).test =
        PackedLocalConfiguration.absolutePosition
          blockLength center saved := by
    simp [prepared, third, second, first, Basic.exec,
      PackedLocalConfiguration.absolutePosition,
      PackedLocalConfiguration.windowStart,
      bankRegisters, PackedLocalHeadScan.bankRegisters,
      PackedLocalHeadScan.bankMap, savedHead,
      CombineValue.rangeRegisters, CombineSafeCenter.centerValue,
      CombineSafeCenter.centerMap, regs.injective.eq_iff]
    change
      (store (CombineSafeCenter.centerValue regs) - 1) *
            store (Layout.blockLength regs) +
          store (savedHead regs) =
        (center - 1) * blockLength + saved
    rw [hcenter, hblock, hsaved]
  by_cases hzero :
      PackedLocalConfiguration.absolutePosition
          blockLength center saved = 0
  · let final := (Basic.imm (originFlag regs) 1).exec prepared
    refine ⟨final, ?_, ?_, ?_⟩
    · have hbranch :
          Runs
            (.ifZero (bankRegisters regs).test
              (.basic (.imm (originFlag regs) 1))
              (.basic (.imm (originFlag regs) 0)))
            prepared final := by
        apply Runs.ifZero
        · exact hpreparedTest.trans hzero
        · exact Runs.basic _ _
      simpa [recordOrigin, Cmd.seqList] using
        Runs.seq (Runs.basic _ _)
          (Runs.seq (Runs.basic _ _)
            (Runs.seq (Runs.basic _ _)
              (Runs.seq (Runs.basic _ _) hbranch)))
    · simp [final, Basic.exec, hzero]
    · intro address hone htest horigin
      simp [final, prepared, third, second, first, Basic.exec,
        Function.update_of_ne, hone, htest, horigin]
  · let final := (Basic.imm (originFlag regs) 0).exec prepared
    refine ⟨final, ?_, ?_, ?_⟩
    · have hbranch :
          Runs
            (.ifZero (bankRegisters regs).test
              (.basic (.imm (originFlag regs) 1))
              (.basic (.imm (originFlag regs) 0)))
            prepared final := by
        apply Runs.ifNonzero
        · intro htest
          exact hzero (hpreparedTest.symm.trans htest)
        · exact Runs.basic _ _
      simpa [recordOrigin, Cmd.seqList] using
        Runs.seq (Runs.basic _ _)
          (Runs.seq (Runs.basic _ _)
            (Runs.seq (Runs.basic _ _)
              (Runs.seq (Runs.basic _ _) hbranch)))
    · simp [final, Basic.exec, hzero]
    · intro address hone htest horigin
      simp [final, prepared, third, second, first, Basic.exec,
        Function.update_of_ne, hone, htest, horigin]

private theorem prepareOldCell_runs
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store) (current : Tape)
    (write : Option Γw) (direction : Dir3)
    (hresult :
      store (bankRegisters regs).result =
        CompactValueCodeSemantics.gammaCode
            (current.cells current.head) + 4)
    (horigin :
      store (originFlag regs) =
        if current.head = 0 then 1 else 0) :
    ∃ final,
      Runs (prepareOldCell write regs) store final ∧
      final (bankRegisters regs).replacement =
        CompactValueCodeSemantics.gammaCode
          ((tapeAction current write direction).cells current.head) ∧
      ∀ address,
        address ≠ (bankRegisters regs).value →
        address ≠ (bankRegisters regs).replacement →
        final address = store address := by
  let valueSet :=
    (Basic.imm (bankRegisters regs).value 4).exec store
  let preserved :=
    (Basic.sub (bankRegisters regs).replacement
      (bankRegisters regs).result
      (bankRegisters regs).value).exec valueSet
  have hpreserveRun :
      Runs
        (Cmd.seq
          (.basic (.imm (bankRegisters regs).value 4))
          (.basic
            (.sub (bankRegisters regs).replacement
              (bankRegisters regs).result
              (bankRegisters regs).value)))
        store preserved :=
    Runs.seq (Runs.basic _ _) (Runs.basic _ _)
  have hpreservedReplacement :
      preserved (bankRegisters regs).replacement =
        CompactValueCodeSemantics.gammaCode
          (current.cells current.head) := by
    simp [preserved, valueSet, Basic.exec,
      bankRegisters, PackedLocalHeadScan.bankRegisters,
      PackedLocalHeadScan.bankMap, regs.injective.eq_iff]
    change
      store (bankRegisters regs).result - 4 =
        CompactValueCodeSemantics.gammaCode
          (current.cells current.head)
    rw [hresult]
    have hcode :=
      gammaCode_lt_four (current.cells current.head)
    omega
  have hpreservedOutside :
      ∀ address,
        address ≠ (bankRegisters regs).value →
        address ≠ (bankRegisters regs).replacement →
        preserved address = store address := by
    intro address hvalue hreplacement
    simp [preserved, valueSet, Basic.exec,
      Function.update_of_ne, hvalue, hreplacement]
  cases write with
  | none =>
      refine ⟨preserved, ?_, ?_, hpreservedOutside⟩
      · simpa [prepareOldCell] using hpreserveRun
      · simpa [tapeAction, Tape.move_cells] using
          hpreservedReplacement
  | some symbol =>
      by_cases hzero : current.head = 0
      · have horiginNonzero :
            store (originFlag regs) ≠ 0 := by
          rw [horigin]
          simp [hzero]
        refine ⟨preserved, ?_, ?_, hpreservedOutside⟩
        · simpa [prepareOldCell] using
            Runs.ifNonzero horiginNonzero hpreserveRun
        · rw [tapeAction_cells_head]
          simpa [hzero] using hpreservedReplacement
      · let final :=
          (Basic.imm (bankRegisters regs).replacement
            (CompactValueCodeSemantics.gammaCode symbol.toΓ)).exec
            store
        have horiginZero :
            store (originFlag regs) = 0 := by
          rw [horigin]
          simp [hzero]
        refine ⟨final, ?_, ?_, ?_⟩
        · simpa [prepareOldCell] using
            Runs.ifZero horiginZero (Runs.basic _ _)
        · rw [tapeAction_cells_head]
          simp [final, Basic.exec, hzero]
        · intro address _hvalue hreplacement
          simp [final, Basic.exec, Function.update_of_ne,
            hreplacement]

private theorem moveSavedHead_runs
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store) (current : Tape)
    (write : Option Γw) (direction : Dir3)
    (blockLength center oldLocal : ℕ)
    (hsaved : store (savedHead regs) = oldLocal)
    (hone : store (bankRegisters regs).one = 1)
    (hold :
      oldLocal =
        PackedLocalConfiguration.localHead blockLength center
          current.head)
    (hlower :
      PackedLocalConfiguration.windowStart blockLength center ≤
        current.head)
    (hnextLower :
      PackedLocalConfiguration.windowStart blockLength center ≤
        (tapeAction current write direction).head) :
    ∃ final,
      Runs (moveSavedHead direction regs) store final ∧
      final (savedHead regs) =
        PackedLocalConfiguration.localHead blockLength center
          (tapeAction current write direction).head ∧
      ∀ address, address ≠ savedHead regs →
        final address = store address := by
  have hhead :=
    tapeAction_head current write direction
  cases direction with
  | left =>
      let final :=
        (Basic.sub (savedHead regs) (savedHead regs)
          (bankRegisters regs).one).exec store
      refine ⟨final, Runs.basic _ _, ?_, ?_⟩
      · simp [final, Basic.exec]
        rw [hsaved, hone, hold]
        rw [hhead]
        simp only [Tape.move,
          PackedLocalConfiguration.localHead]
        omega
      · intro address haddress
        simp [final, Basic.exec, Function.update_of_ne, haddress]
  | right =>
      let final :=
        (Basic.add (savedHead regs) (savedHead regs)
          (bankRegisters regs).one).exec store
      refine ⟨final, Runs.basic _ _, ?_, ?_⟩
      · simp [final, Basic.exec]
        rw [hsaved, hone, hold]
        rw [hhead]
        simp only [Tape.move,
          PackedLocalConfiguration.localHead]
        omega
      · intro address haddress
        simp [final, Basic.exec, Function.update_of_ne, haddress]
  | stay =>
      refine ⟨store, Runs.skip _, ?_, fun _ _ => rfl⟩
      rw [hsaved, hold, hhead]
      rfl

private theorem markSavedCell_runs
    (tm : TM workTapeCount)
    (tape : TapeIndex workTapeCount)
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store)
    (blockLength word saved : ℕ)
    (hblock : store (Layout.blockLength regs) = blockLength)
    (hword : store (bankRegisters regs).word = word)
    (hsaved : store (savedHead regs) = saved) :
    ∃ final,
      Runs (markSavedCell tm tape regs) store final ∧
      final (bankRegisters regs).word =
        NeighborhoodProgram.replaceAt
          (PackedLocalConfiguration.radix tm) word
          (PackedLocalConfiguration.cellIndex blockLength tape saved)
          (PackedDigits.digit
              (PackedLocalConfiguration.radix tm) word
              (PackedLocalConfiguration.cellIndex
                blockLength tape saved) + 4) ∧
      final (savedHead regs) = saved ∧
      final (Layout.blockLength regs) = blockLength ∧
      final (bankRegisters regs).one = 1 ∧
      final (CombineValue.rangeRegisters regs).one = 1 ∧
      ∀ address, address ∉ (bankRegisters regs).footprint →
        final address = store address := by
  obtain ⟨read, hreadRun, hreadWord, hreadResult,
      hreadSaved, hreadBlock, _hreadOne, _hreadRangeOne,
      hreadOutside⟩ :=
    readSavedCell_runs tm tape regs store blockLength word
      saved hblock hword hsaved
  let valueSet :=
    (Basic.imm (bankRegisters regs).value 4).exec read
  have hvalueRun :
      Runs (.basic (.imm (bankRegisters regs).value 4))
        read valueSet :=
    Runs.basic _ _
  let replacementSet :=
    (Basic.add (bankRegisters regs).replacement
      (bankRegisters regs).result
      (bankRegisters regs).value).exec valueSet
  have hreplacementRun :
      Runs
        (.basic
          (.add (bankRegisters regs).replacement
            (bankRegisters regs).result
            (bankRegisters regs).value))
        valueSet replacementSet :=
    Runs.basic _ _
  have hreplacementValue :
      replacementSet (bankRegisters regs).replacement =
        PackedDigits.digit
            (PackedLocalConfiguration.radix tm) word
            (PackedLocalConfiguration.cellIndex
              blockLength tape saved) + 4 := by
    simp [replacementSet, valueSet, Basic.exec,
      bankRegisters, PackedLocalHeadScan.bankRegisters,
      PackedLocalHeadScan.bankMap, regs.injective.eq_iff]
    change
      read (bankRegisters regs).result =
        PackedDigits.digit
          (PackedLocalConfiguration.radix tm) word
          (PackedLocalConfiguration.cellIndex blockLength tape saved)
    exact hreadResult
  have hreplacementWord :
      replacementSet (bankRegisters regs).word = word := by
    simp [replacementSet, valueSet, Basic.exec,
      bankRegisters, PackedLocalHeadScan.bankRegisters,
      PackedLocalHeadScan.bankMap, regs.injective.eq_iff]
    change read (bankRegisters regs).word = word
    exact hreadWord
  have hreplacementSaved :
      replacementSet (savedHead regs) = saved := by
    simp [replacementSet, valueSet, Basic.exec,
      bankRegisters, PackedLocalHeadScan.bankRegisters,
      PackedLocalHeadScan.bankMap, savedHead,
      CombineValue.rangeRegisters, regs.injective.eq_iff]
    exact hreadSaved
  have hreplacementBlock :
      replacementSet (Layout.blockLength regs) = blockLength := by
    simp [replacementSet, valueSet, Basic.exec,
      bankRegisters, PackedLocalHeadScan.bankRegisters,
      PackedLocalHeadScan.bankMap, regs.injective.eq_iff]
    exact hreadBlock
  obtain ⟨final, hreplaceRun, hfinalWord, _hfinalResult,
      hfinalSaved, hfinalBlock, hfinalOne, hfinalRangeOne,
      hfinalOutside⟩ :=
    replaceSavedCell_runs tm tape regs replacementSet
      blockLength word saved
      (PackedDigits.digit
          (PackedLocalConfiguration.radix tm) word
          (PackedLocalConfiguration.cellIndex blockLength tape saved) +
        4)
      hreplacementBlock hreplacementWord hreplacementSaved
      hreplacementValue
  refine ⟨final, ?_, hfinalWord, hfinalSaved, hfinalBlock,
    hfinalOne, hfinalRangeOne, ?_⟩
  · simpa [markSavedCell, Cmd.seqList] using
      Runs.seq hreadRun
        (Runs.seq hvalueRun
          (Runs.seq hreplacementRun hreplaceRun))
  · intro address haddress
    have outsideNe (slot : Fin 12) :
        address ≠ (bankRegisters regs).index slot := by
      intro heq
      apply haddress
      rw [heq]
      exact (bankRegisters regs).index_mem_footprint slot
    calc
      final address = replacementSet address :=
        hfinalOutside address haddress
      _ = read address := by
        simp [replacementSet, valueSet, Basic.exec,
          outsideNe 7, outsideNe 11]
      _ = store address :=
        hreadOutside address haddress

private theorem guess_not_mem_control
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) :
    controller.guess ∉ ControlDecode.scratchFootprint regs := by
  intro hmember
  simp only [ControlDecode.scratchFootprint, Finset.mem_image,
    Finset.mem_univ, true_and] at hmember
  obtain ⟨slot, hslot⟩ := hmember
  exact regs.index_ne_controller
    (ControlDecode.scratchMap slot) (2 : Fin 17) hslot

private theorem fixed_index_not_mem_control
    (regs : NeighborhoodTrial.Registers controller)
    (slot : Fin 34)
    (hslot : ∀ scratch, slot ≠ ControlDecode.scratchMap scratch) :
    regs.index slot ∉ ControlDecode.scratchFootprint regs := by
  intro hmember
  simp only [ControlDecode.scratchFootprint, Finset.mem_image,
    Finset.mem_univ, true_and] at hmember
  obtain ⟨scratch, hscratch⟩ := hmember
  exact hslot scratch (regs.injective hscratch.symm)

private theorem fixed_index_not_mem_center
    (regs : NeighborhoodTrial.Registers controller)
    (slot : Fin 34)
    (hslot : ∀ scratch, slot ≠ CombineSafeCenter.scratchMap scratch) :
    regs.index slot ∉ CombineSafeCenter.footprint regs := by
  intro hmember
  simp only [CombineSafeCenter.footprint, Finset.mem_image,
    Finset.mem_univ, true_and] at hmember
  obtain ⟨scratch, hscratch⟩ := hmember
  exact hslot scratch (regs.injective hscratch.symm)

private theorem deriveTapeCenter_runs
    {tm : TM workTapeCount}
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (nodeTape : TapeIndex workTapeCount)
    (slot : NeighborhoodGraph.Slot)
    (interval : ℕ)
    (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (selectedTape : TapeIndex workTapeCount)
    (code :
      Fin
        (3 ^
          NeighborhoodGraph.Guess.Enumeration.movementCount
            workTapeCount instanceData.horizon))
    (store : Store)
    (hfits :
      ∀ digit ∈
          FrameCodec.nodeDigits
            (show
              NeighborhoodEvaluator.QueryNode
                workTapeCount instanceData.horizon
              from .graph (.computation nodeTape slot interval)),
        digit < Representation.digitBase instanceData)
    (hcontext :
      CombineTerm.ComputationContext regs instanceData nodeTape slot
        interval logicalBank store)
    (hguess : store controller.guess = code.val) :
    ∃ final,
      Runs
        (deriveTapeCenter workTapeCount controller selectedTape regs)
        store final ∧
      final (CombineSafeCenter.centerValue regs) =
        ChildNode.centerOutputValue
          (ChildNode.derivedCenterValue workTapeCount code.val
            selectedTape.val interval) ∧
      final controller.guess = code.val ∧
      ∀ address,
        address ∉ ControlDecode.scratchFootprint regs →
        address ∉ CombineSafeCenter.footprint regs →
        final address = store address := by
  obtain ⟨decoded, hdecodeRun, hdecoded⟩ :=
    CombineTerm.decodeComputationNode_runs regs instanceData nodeTape
      slot interval logicalBank store hfits hcontext
  have hdecodedGuess :
      decoded controller.guess = code.val := by
    rw [Footprint.runs_eq_outside
      (ControlDecode.decodeNode_writesWithin regs) hdecodeRun
      (guess_not_mem_control controller regs)]
    exact hguess
  have hdecodedInterval :
      decoded (ControlDecode.nodePayload1 regs) = interval := by
    simpa [ControlDecode.expectedNodeValues] using
      hdecoded.decoded.payload1_eq
  let selected :=
    (Basic.imm (ControlDecode.nodeTape regs) selectedTape.val).exec
      decoded
  have hselectRun :
      Runs
        (.basic
          (.imm (ControlDecode.nodeTape regs) selectedTape.val))
        decoded selected :=
    Runs.basic _ _
  have hselectedTape :
      selected (ControlDecode.nodeTape regs) = selectedTape.val := by
    simp [selected, Basic.exec]
  have hselectedInterval :
      selected (ControlDecode.nodePayload1 regs) = interval := by
    simp [selected, Basic.exec, ControlDecode.nodeTape,
      ControlDecode.nodePayload1, ControlDecode.first,
      ControlDecode.third, regs.injective.eq_iff,
      hdecodedInterval]
  have hselectedGuess :
      selected controller.guess = code.val := by
    simp only [selected, Basic.exec]
    rw [Function.update_of_ne]
    · exact hdecodedGuess
    · exact (regs.index_ne_controller
        (9 : Fin 34) (2 : Fin 17)).symm
  obtain ⟨final, hcenterRun, hcenterPost⟩ :=
    CombineSafeCenter.deriveCenter_runs workTapeCount controller regs
      selected code.val selectedTape.val interval hselectedGuess
      hselectedTape hselectedInterval
  refine ⟨final, ?_, hcenterPost.center_eq, hcenterPost.guess_eq,
    ?_⟩
  · simpa [deriveTapeCenter, Cmd.seqList] using
      Runs.seq hdecodeRun (Runs.seq hselectRun hcenterRun)
  · intro address hcontrol hcenter
    calc
      final address = selected address :=
        hcenterPost.eq_outside address hcenter
      _ = decoded address := by
        simp only [selected, Basic.exec]
        rw [Function.update_of_ne]
        intro heq
        apply hcontrol
        subst address
        exact Finset.mem_image.mpr
          ⟨(2 : Fin 7), Finset.mem_univ _, rfl⟩
      _ = store address :=
        Footprint.runs_eq_outside
          (ControlDecode.decodeNode_writesWithin regs)
          hdecodeRun hcontrol

private theorem centerOutputValue_derivedCenter
    {tm : TM workTapeCount}
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (code :
      Fin
        (3 ^
          NeighborhoodGraph.Guess.Enumeration.movementCount
            workTapeCount instanceData.horizon))
    (tape : TapeIndex workTapeCount)
    (interval : ℕ) (hinterval : interval ≤ instanceData.horizon)
    (hguess :
      instanceData.guess =
        NeighborhoodGraph.Guess.Enumeration.candidateGuess code) :
    ChildNode.centerOutputValue
        (ChildNode.derivedCenterValue workTapeCount code.val tape.val
          interval) =
      NeighborhoodGraph.Guess.Consistency.guessedCenters
        instanceData.guess interval tape := by
  rw [ChildNode.derivedCenterValue_candidateGuess
    code tape interval hinterval]
  rw [hguess]
  simp only [NeighborhoodGraph.Guess.Consistency.guessedCenters]
  cases
      (NeighborhoodGraph.Guess.Enumeration.candidateGuess code).derivedCenter
        tape interval <;>
    rfl

theorem updateTape_runs_internal
    {tm : TM workTapeCount}
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (nodeTape : TapeIndex workTapeCount)
    (slot : NeighborhoodGraph.Slot)
    (interval : ℕ)
    (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (code :
      Fin
        (3 ^
          NeighborhoodGraph.Guess.Enumeration.movementCount
            workTapeCount instanceData.horizon))
    (selected : TapeIndex workTapeCount)
    (write : Option Γw) (direction : Dir3)
    (centers : TapeIndex workTapeCount → ℕ)
    (cfg : Cfg workTapeCount tm.Q)
    (suffix word : ℕ)
    (store : Store)
    (hfits :
      ∀ digit ∈
          FrameCodec.nodeDigits
            (show
              NeighborhoodEvaluator.QueryNode
                workTapeCount instanceData.horizon
              from .graph (.computation nodeTape slot interval)),
        digit < Representation.digitBase instanceData)
    (hcontext :
      CombineTerm.ComputationContext regs instanceData nodeTape slot
        interval logicalBank store)
    (hstoreGuess : store controller.guess = code.val)
    (hguess :
      instanceData.guess =
        NeighborhoodGraph.Guess.Enumeration.candidateGuess code)
    (hinterval : interval ≤ instanceData.horizon)
    (hcenters :
      centers =
        NeighborhoodGraph.Guess.Consistency.guessedCenters
          instanceData.guess interval)
    (hrep :
      PackedLocalRepresentation.Represents
        tm order instanceData.blockLength centers cfg suffix word)
    (hheads :
      HeadsInWindow instanceData.blockLength centers cfg)
    (hnextHeads :
      HeadsInWindow instanceData.blockLength centers
        (updateNamedTape cfg selected write direction))
    (hword : store (bankRegisters regs).word = word)
    (hrangeOne :
      store (CombineValue.rangeRegisters regs).one = 1) :
    ∃ final,
      Runs
        (updateTape tm controller selected write direction regs)
        store final ∧
      Post tm order instanceData.blockLength centers
        (updateNamedTape cfg selected write direction)
        suffix regs store final := by
  let current := tapeAt cfg selected
  let updated := tapeAction current write direction
  let oldLocal :=
    PackedLocalConfiguration.localHead instanceData.blockLength
      (centers selected) current.head
  let newLocal :=
    PackedLocalConfiguration.localHead instanceData.blockLength
      (centers selected) updated.head
  let oldIndex :=
    PackedLocalConfiguration.cellIndex instanceData.blockLength
      selected oldLocal
  let newIndex :=
    PackedLocalConfiguration.cellIndex instanceData.blockLength
      selected newLocal
  let oldReplacement :=
    CompactValueCodeSemantics.gammaCode
      (updated.cells current.head)
  let newReplacement :=
    CompactValueCodeSemantics.gammaCode
        (updated.cells updated.head) + 4
  let wordAfterOld :=
    NeighborhoodProgram.replaceAt
      (PackedLocalConfiguration.radix tm) word oldIndex oldReplacement
  have hblock :
      store (Layout.blockLength regs) = instanceData.blockLength :=
    hcontext.parameters.blockLength_eq
  obtain ⟨hlower, hupper⟩ := hheads selected
  obtain ⟨hnextLowerRaw, hnextUpperRaw⟩ :=
    hnextHeads selected
  have hnextLower :
      PackedLocalConfiguration.windowStart instanceData.blockLength
          (centers selected) ≤
        updated.head := by
    simpa [updated, current, tapeAt_updateNamedTape_same] using
      hnextLowerRaw
  have hnextUpper :
      updated.head <
        PackedLocalConfiguration.windowStart instanceData.blockLength
            (centers selected) +
          PackedLocalConfiguration.tapeSpan instanceData.blockLength := by
    simpa [updated, current, tapeAt_updateNamedTape_same] using
      hnextUpperRaw
  have holdLocal :
      oldLocal <
        PackedLocalConfiguration.tapeSpan instanceData.blockLength := by
    dsimp only [oldLocal, current]
    simp only [PackedLocalConfiguration.localHead]
    omega
  have hnewLocal :
      newLocal <
        PackedLocalConfiguration.tapeSpan instanceData.blockLength := by
    dsimp only [newLocal]
    simp only [PackedLocalConfiguration.localHead]
    omega
  obtain ⟨scanned, hscanRun, hscanPost, hscanPreserves⟩ :=
    PackedLocalHeadScan.scan_runs_represents tm order
      instanceData.blockLength instanceData.positive centers cfg
      selected suffix word regs store hblock hword hrep hrangeOne
      hlower hupper
  obtain ⟨headSaved, hcopyRun, hcopyValue, hcopyOutside⟩ :=
    copy_runs (savedHead regs)
      (PackedLocalHeadScan.headOffset regs) scanned
      (regs.injective.ne (by decide))
  have hheadSavedValue :
      headSaved (savedHead regs) = oldLocal := by
    calc
      headSaved (savedHead regs) =
          scanned (PackedLocalHeadScan.headOffset regs) :=
        hcopyValue
      _ = oldLocal := by
        simpa [oldLocal, current] using hscanPost.head_eq
  have hheadSavedAccumulator :
      headSaved (CombineValue.rangeRegisters regs).accumulator =
        store (CombineValue.rangeRegisters regs).accumulator := by
    calc
      headSaved (CombineValue.rangeRegisters regs).accumulator =
          scanned (CombineValue.rangeRegisters regs).accumulator :=
        hcopyOutside _ (regs.injective.ne (by decide))
      _ = store (CombineValue.rangeRegisters regs).accumulator :=
        hscanPreserves.accumulator_eq
  have hheadSavedCount :
      headSaved (CombineValue.rangeRegisters regs).count =
        store (CombineValue.rangeRegisters regs).count := by
    calc
      headSaved (CombineValue.rangeRegisters regs).count =
          scanned (CombineValue.rangeRegisters regs).count :=
        hcopyOutside _ (regs.injective.ne (by decide))
      _ = store (CombineValue.rangeRegisters regs).count :=
        hscanPreserves.count_eq
  obtain ⟨rangeSaved, hsaveRun, hrangeSavedAccumulator,
      hrangeSavedCount, hsaveOutside⟩ :=
    saveRangeContext_runs regs headSaved
      (store (CombineValue.rangeRegisters regs).accumulator)
      (store (CombineValue.rangeRegisters regs).count)
      hheadSavedAccumulator hheadSavedCount
  have hrangeSavedHead :
      rangeSaved (savedHead regs) = oldLocal := by
    rw [hsaveOutside (savedHead regs)
      (regs.injective.ne (by decide))
      (regs.injective.ne (by decide))]
    exact hheadSavedValue
  have hrangeSavedWord :
      rangeSaved (bankRegisters regs).word = word := by
    rw [hsaveOutside (bankRegisters regs).word
      (regs.injective.ne (by decide))
      (regs.injective.ne (by decide))]
    rw [hcopyOutside (bankRegisters regs).word
      (regs.injective.ne (by decide))]
    exact hscanPost.word_eq
  have hrangeSavedBlock :
      rangeSaved (Layout.blockLength regs) =
        instanceData.blockLength := by
    rw [hsaveOutside (Layout.blockLength regs)
      (regs.injective.ne (by decide))
      (regs.injective.ne (by decide))]
    rw [hcopyOutside (Layout.blockLength regs)
      (regs.injective.ne (by decide))]
    exact hscanPreserves.abi.blockLength_eq.trans hblock
  have hprefixRun :
      Runs
        (Cmd.seq
          (PackedLocalHeadScan.scan tm selected regs)
          (Cmd.seq
            (copy (savedHead regs)
              (PackedLocalHeadScan.headOffset regs))
            (saveRangeContext regs)))
        store rangeSaved :=
    Runs.seq hscanRun (Runs.seq hcopyRun hsaveRun)
  have hprefixWrites :
      Footprint.CmdWritesWithin (footprint regs)
        (Cmd.seq
          (PackedLocalHeadScan.scan tm selected regs)
          (Cmd.seq
            (copy (savedHead regs)
              (PackedLocalHeadScan.headOffset regs))
            (saveRangeContext regs))) :=
    ⟨cmdWritesWithin_mono
        (PackedLocalHeadScan.scan_writesWithin tm selected regs)
        (headScan_footprint_subset regs),
      copy_writesWithin regs _ _
        (physical_slot_mem regs (by simp)),
      saveRangeContext_writesWithin regs⟩
  have hrangeSavedContext :=
    computationContext_of_runs regs instanceData nodeTape slot
      interval logicalBank hprefixWrites hprefixRun hcontext
  have hrangeSavedGuess :
      rangeSaved controller.guess = code.val := by
    exact
      (controller_guess_eq_of_runs regs hprefixWrites hprefixRun).trans
        hstoreGuess
  obtain ⟨centered, hcenterRun, hcenterValue, hcenterGuess,
      hcenterOutside⟩ :=
    deriveTapeCenter_runs regs instanceData nodeTape slot interval
      logicalBank selected code rangeSaved hfits hrangeSavedContext
      hrangeSavedGuess
  have hcenteredCenter :
      centered (CombineSafeCenter.centerValue regs) =
        centers selected := by
    exact
      hcenterValue.trans
        ((centerOutputValue_derivedCenter instanceData code selected
            interval hinterval hguess).trans
          (congrFun hcenters selected).symm)
  have hcenteredOrigin :
      centered (originFlag regs) =
        store (CombineValue.rangeRegisters regs).accumulator := by
    calc
      centered (originFlag regs) = rangeSaved (originFlag regs) := by
        apply hcenterOutside
        · simpa [originFlag, Layout.codecScratch] using
            fixed_index_not_mem_control regs 31 (by
              intro scratch
              fin_cases scratch <;> decide)
        · simpa [originFlag, Layout.codecScratch] using
            fixed_index_not_mem_center regs 31 (by
              intro scratch
              fin_cases scratch <;> decide)
      _ = store (CombineValue.rangeRegisters regs).accumulator :=
        hrangeSavedAccumulator
  have hcenteredCount :
      centered (CombineValue.rangeRegisters regs).one =
        store (CombineValue.rangeRegisters regs).count := by
    calc
      centered (CombineValue.rangeRegisters regs).one =
          rangeSaved (CombineValue.rangeRegisters regs).one := by
        apply hcenterOutside
        · simpa [CombineValue.rangeRegisters] using
            fixed_index_not_mem_control regs 17 (by
              intro scratch
              fin_cases scratch <;> decide)
        · simpa [CombineValue.rangeRegisters] using
            fixed_index_not_mem_center regs 17 (by
              intro scratch
              fin_cases scratch <;> decide)
      _ = store (CombineValue.rangeRegisters regs).count :=
        hrangeSavedCount
  have hcenteredHead :
      centered (savedHead regs) = oldLocal := by
    calc
      centered (savedHead regs) = rangeSaved (savedHead regs) := by
        apply hcenterOutside
        · simpa [savedHead, CombineValue.rangeRegisters] using
            fixed_index_not_mem_control regs 19 (by
              intro scratch
              fin_cases scratch <;> decide)
        · simpa [savedHead, CombineValue.rangeRegisters] using
            fixed_index_not_mem_center regs 19 (by
              intro scratch
              fin_cases scratch <;> decide)
      _ = oldLocal := hrangeSavedHead
  have hcenteredWord :
      centered (bankRegisters regs).word = word := by
    calc
      centered (bankRegisters regs).word =
          rangeSaved (bankRegisters regs).word := by
        apply hcenterOutside
        · simpa [bankRegisters, PackedLocalHeadScan.bankRegisters,
            PackedLocalHeadScan.bankMap] using
            fixed_index_not_mem_control regs 32 (by
              intro scratch
              fin_cases scratch <;> decide)
        · simpa [bankRegisters, PackedLocalHeadScan.bankRegisters,
            PackedLocalHeadScan.bankMap] using
            fixed_index_not_mem_center regs 32 (by
              intro scratch
              fin_cases scratch <;> decide)
      _ = word := hrangeSavedWord
  have hcenteredBlock :
      centered (Layout.blockLength regs) =
        instanceData.blockLength := by
    calc
      centered (Layout.blockLength regs) =
          rangeSaved (Layout.blockLength regs) := by
        apply hcenterOutside
        · simpa using
            fixed_index_not_mem_control regs 2 (by
              intro scratch
              fin_cases scratch <;> decide)
        · simpa using
            fixed_index_not_mem_center regs 2 (by
              intro scratch
              fin_cases scratch <;> decide)
      _ = instanceData.blockLength := hrangeSavedBlock
  obtain ⟨restored, hrestoreRun, hrestoredAccumulator,
      hrestoredCount, hrestoredOne, hrestoreOutside⟩ :=
    restoreRangeContext_runs regs centered
      (store (CombineValue.rangeRegisters regs).accumulator)
      (store (CombineValue.rangeRegisters regs).count)
      hcenteredOrigin hcenteredCount
  have hrestoredCenter :
      restored (CombineSafeCenter.centerValue regs) =
        centers selected := by
    rw [hrestoreOutside (CombineSafeCenter.centerValue regs)
      (regs.injective.ne (by decide))
      (regs.injective.ne (by decide))
      (regs.injective.ne (by decide))]
    exact hcenteredCenter
  have hrestoredHead :
      restored (savedHead regs) = oldLocal := by
    rw [hrestoreOutside (savedHead regs)
      (regs.injective.ne (by decide))
      (regs.injective.ne (by decide))
      (regs.injective.ne (by decide))]
    exact hcenteredHead
  have hrestoredWord :
      restored (bankRegisters regs).word = word := by
    rw [hrestoreOutside (bankRegisters regs).word
      (regs.injective.ne (by decide))
      (regs.injective.ne (by decide))
      (regs.injective.ne (by decide))]
    exact hcenteredWord
  have hrestoredBlock :
      restored (Layout.blockLength regs) =
        instanceData.blockLength := by
    rw [hrestoreOutside (Layout.blockLength regs)
      (regs.injective.ne (by decide))
      (regs.injective.ne (by decide))
      (regs.injective.ne (by decide))]
    exact hcenteredBlock
  obtain ⟨originRecorded, horiginRun, horiginValue,
      horiginOutside⟩ :=
    recordOrigin_runs regs restored instanceData.blockLength
      (centers selected) oldLocal hrestoredBlock hrestoredCenter
      hrestoredHead
  have horiginExact :
      originRecorded (originFlag regs) =
        (if current.head = 0 then 1 else 0) := by
    rw [horiginValue]
    rw [absolutePosition_localHead instanceData.blockLength
      (centers selected) current.head]
    simpa [oldLocal]
  have horiginRecordedBlock :
      originRecorded (Layout.blockLength regs) =
        instanceData.blockLength := by
    rw [horiginOutside (Layout.blockLength regs)
      (regs.injective.ne (by decide))
      (regs.injective.ne (by decide))
      (regs.injective.ne (by decide))]
    exact hrestoredBlock
  have horiginRecordedWord :
      originRecorded (bankRegisters regs).word = word := by
    rw [horiginOutside (bankRegisters regs).word
      (regs.injective.ne (by decide))
      (regs.injective.ne (by decide))
      (regs.injective.ne (by decide))]
    exact hrestoredWord
  have horiginRecordedHead :
      originRecorded (savedHead regs) = oldLocal := by
    rw [horiginOutside (savedHead regs)
      (regs.injective.ne (by decide))
      (regs.injective.ne (by decide))
      (regs.injective.ne (by decide))]
    exact hrestoredHead
  obtain ⟨oldRead, hreadRun, hreadWord, hreadResult,
      hreadHead, hreadBlock, hreadOne, hreadRangeOne,
      hreadOutside⟩ :=
    readSavedCell_runs tm selected regs originRecorded
      instanceData.blockLength word oldLocal
      horiginRecordedBlock horiginRecordedWord horiginRecordedHead
  have hreadOrigin :
      oldRead (originFlag regs) =
        (if current.head = 0 then 1 else 0) := by
    calc
      oldRead (originFlag regs) =
          originRecorded (originFlag regs) :=
        hreadOutside (originFlag regs)
          (fixed_index_not_mem_bank regs 31 (by
            intro bankSlot
            fin_cases bankSlot <;> decide))
      _ = (if current.head = 0 then 1 else 0) := horiginExact
  have hreadResultExact :
      oldRead (bankRegisters regs).result =
        CompactValueCodeSemantics.gammaCode
            (current.cells current.head) + 4 := by
    calc
      oldRead (bankRegisters regs).result =
          PackedDigits.digit (PackedLocalConfiguration.radix tm) word
            (PackedLocalConfiguration.cellIndex
              instanceData.blockLength selected oldLocal) :=
        hreadResult
      _ = PackedLocalConfiguration.cellDigit cfg
          instanceData.blockLength centers selected oldLocal :=
        PackedLocalRepresentation.represents_cell tm order
          instanceData.blockLength instanceData.positive centers cfg
          suffix word hrep selected oldLocal holdLocal
      _ = CompactValueCodeSemantics.gammaCode
            (current.cells current.head) + 4 := by
        simp only [PackedLocalConfiguration.cellDigit]
        rw [absolutePosition_localHead instanceData.blockLength
          (centers selected) current.head]
        · simp [current]
        · exact hlower
  obtain ⟨oldPrepared, hprepareOldRun, hprepareOldReplacement,
      hprepareOldOutside⟩ :=
    prepareOldCell_runs regs oldRead current write direction
      hreadResultExact hreadOrigin
  have hpreparedReplacement :
      oldPrepared (bankRegisters regs).replacement =
        oldReplacement := by
    simpa [oldReplacement, updated] using hprepareOldReplacement
  have hpreparedWord :
      oldPrepared (bankRegisters regs).word = word := by
    rw [hprepareOldOutside (bankRegisters regs).word
      ((bankRegisters regs).index_ne (by decide))
      ((bankRegisters regs).index_ne (by decide))]
    exact hreadWord
  have hpreparedHead :
      oldPrepared (savedHead regs) = oldLocal := by
    rw [hprepareOldOutside (savedHead regs)
      (regs.injective.ne (by decide))
      (regs.injective.ne (by decide))]
    exact hreadHead
  have hpreparedBlock :
      oldPrepared (Layout.blockLength regs) =
        instanceData.blockLength := by
    rw [hprepareOldOutside (Layout.blockLength regs)
      (regs.injective.ne (by decide))
      (regs.injective.ne (by decide))]
    exact hreadBlock
  obtain ⟨oldReplaced, hreplaceRun, hreplaceWord, _hreplaceResult,
      hreplaceHead, hreplaceBlock, hreplaceOne, hreplaceRangeOne,
      hreplaceOutside⟩ :=
    replaceSavedCell_runs tm selected regs oldPrepared
      instanceData.blockLength word oldLocal oldReplacement
      hpreparedBlock hpreparedWord hpreparedHead hpreparedReplacement
  have hreplaceWordExact :
      oldReplaced (bankRegisters regs).word = wordAfterOld := by
    simpa [wordAfterOld, oldIndex] using hreplaceWord
  obtain ⟨bankInitialized, hinitializeRun, hinitializedWord,
      _hinitializedBase, _hinitializedBasePred, hinitializedOne,
      hinitializedOutside⟩ :=
    initializeBank_runs tm regs oldReplaced wordAfterOld
      hreplaceWordExact
  have hinitializedHead :
      bankInitialized (savedHead regs) = oldLocal := by
    rw [hinitializedOutside (savedHead regs)
      (regs.injective.ne (by decide))
      (regs.injective.ne (by decide))
      (regs.injective.ne (by decide))]
    exact hreplaceHead
  have hinitializedBlock :
      bankInitialized (Layout.blockLength regs) =
        instanceData.blockLength := by
    rw [hinitializedOutside (Layout.blockLength regs)
      (regs.injective.ne (by decide))
      (regs.injective.ne (by decide))
      (regs.injective.ne (by decide))]
    exact hreplaceBlock
  obtain ⟨moved, hmoveRun, hmoveHead, hmoveOutside⟩ :=
    moveSavedHead_runs regs bankInitialized current write direction
      instanceData.blockLength (centers selected) oldLocal
      hinitializedHead hinitializedOne (by rfl) hlower hnextLower
  have hmovedWord :
      moved (bankRegisters regs).word = wordAfterOld := by
    rw [hmoveOutside (bankRegisters regs).word
      (regs.injective.ne (by decide))]
    exact hinitializedWord
  have hmovedBlock :
      moved (Layout.blockLength regs) =
        instanceData.blockLength := by
    rw [hmoveOutside (Layout.blockLength regs)
      (regs.injective.ne (by decide))]
    exact hinitializedBlock
  obtain ⟨marked, hmarkRun, hmarkWord, hmarkHead, hmarkBlock,
      hmarkOne, hmarkRangeOne, hmarkOutside⟩ :=
    markSavedCell_runs tm selected regs moved
      instanceData.blockLength wordAfterOld newLocal hmovedBlock
      hmovedWord hmoveHead
  have holdReplacement :
      oldReplacement < PackedLocalConfiguration.radix tm := by
    have hcode :=
      gammaCode_lt_four (updated.cells current.head)
    exact lt_of_lt_of_le hcode (by
      simp [PackedLocalConfiguration.radix])
  have hnewReplacement :
      newReplacement < PackedLocalConfiguration.radix tm := by
    have hcode :=
      gammaCode_lt_four (updated.cells updated.head)
    have hsmall : newReplacement < 16 := by
      dsimp only [newReplacement]
      omega
    exact lt_of_lt_of_le hsmall (by
      simp [PackedLocalConfiguration.radix])
  have hnewDigit :
      PackedDigits.digit (PackedLocalConfiguration.radix tm)
          wordAfterOld newIndex =
        CompactValueCodeSemantics.gammaCode
          (updated.cells updated.head) := by
    dsimp only [wordAfterOld]
    by_cases heq : newIndex = oldIndex
    · rw [heq, NeighborhoodProgram.replaceAt_digit_eq
        (PackedLocalConfiguration.radix_pos tm) holdReplacement]
      have hlocalEq : newLocal = oldLocal := by
        dsimp only [newIndex, oldIndex] at heq
        simp only [PackedLocalConfiguration.cellIndex] at heq
        omega
      have hheadEq : updated.head = current.head := by
        calc
          updated.head =
              PackedLocalConfiguration.absolutePosition
                instanceData.blockLength (centers selected)
                newLocal := by
            symm
            exact absolutePosition_localHead
              instanceData.blockLength (centers selected)
              updated.head hnextLower
          _ = PackedLocalConfiguration.absolutePosition
                instanceData.blockLength (centers selected)
                oldLocal := by rw [hlocalEq]
          _ = current.head :=
            absolutePosition_localHead instanceData.blockLength
              (centers selected) current.head hlower
      simp [oldReplacement, hheadEq]
    · rw [NeighborhoodProgram.replaceAt_digit_ne
        (PackedLocalConfiguration.radix_pos tm) holdReplacement heq]
      rw [PackedLocalRepresentation.represents_cell tm order
        instanceData.blockLength instanceData.positive centers cfg
        suffix word hrep selected newLocal hnewLocal]
      simp only [PackedLocalConfiguration.cellDigit]
      rw [absolutePosition_localHead instanceData.blockLength
        (centers selected) updated.head hnextLower]
      have hheadNe : current.head ≠ updated.head := by
        intro hhead
        apply heq
        dsimp only [newIndex, oldIndex, newLocal, oldLocal]
        simp [hhead]
      have hcells :
          updated.cells updated.head =
            current.cells updated.head := by
        dsimp only [updated]
        apply tapeAction_cells_of_ne
        exact Ne.symm hheadNe
      rw [hcells]
      simp [current, hheadNe]
  have hmarkWordExact :
      marked (bankRegisters regs).word =
        NeighborhoodProgram.replaceAt
          (PackedLocalConfiguration.radix tm) wordAfterOld newIndex
          newReplacement := by
    simpa [newIndex, newReplacement, hnewDigit] using hmarkWord
  have hmarkedRep :
      PackedLocalRepresentation.Represents tm order
        instanceData.blockLength centers
        (updateNamedTape cfg selected write direction)
        suffix (marked (bankRegisters regs).word) := by
    rw [hmarkWordExact]
    simpa [wordAfterOld, current, updated, oldLocal, newLocal,
      oldIndex, newIndex, oldReplacement, newReplacement] using
      updateNamedTape_represents tm order instanceData.blockLength
        instanceData.positive centers cfg selected write direction
        suffix word hrep hlower hupper
        (by simpa [updated, current] using hnextLower)
        (by simpa [updated, current] using hnextUpper)
  have hmarkedAccumulator :
      marked (CombineValue.rangeRegisters regs).accumulator =
        store (CombineValue.rangeRegisters regs).accumulator := by
    calc
      marked (CombineValue.rangeRegisters regs).accumulator =
          moved (CombineValue.rangeRegisters regs).accumulator :=
        hmarkOutside _
          (fixed_index_not_mem_bank regs 18 (by
            intro bankSlot
            fin_cases bankSlot <;> decide))
      _ = bankInitialized
          (CombineValue.rangeRegisters regs).accumulator :=
        hmoveOutside _ (regs.injective.ne (by decide))
      _ = oldReplaced
          (CombineValue.rangeRegisters regs).accumulator :=
        hinitializedOutside _
          (regs.injective.ne (by decide))
          (regs.injective.ne (by decide))
          (regs.injective.ne (by decide))
      _ = oldPrepared
          (CombineValue.rangeRegisters regs).accumulator :=
        hreplaceOutside _
          (fixed_index_not_mem_bank regs 18 (by
            intro bankSlot
            fin_cases bankSlot <;> decide))
      _ = oldRead (CombineValue.rangeRegisters regs).accumulator :=
        hprepareOldOutside _
          (regs.injective.ne (by decide))
          (regs.injective.ne (by decide))
      _ = originRecorded
          (CombineValue.rangeRegisters regs).accumulator :=
        hreadOutside _
          (fixed_index_not_mem_bank regs 18 (by
            intro bankSlot
            fin_cases bankSlot <;> decide))
      _ = restored (CombineValue.rangeRegisters regs).accumulator :=
        horiginOutside _
          (regs.injective.ne (by decide))
          (regs.injective.ne (by decide))
          (regs.injective.ne (by decide))
      _ = store (CombineValue.rangeRegisters regs).accumulator :=
        hrestoredAccumulator
  have hmarkedCount :
      marked (CombineValue.rangeRegisters regs).count =
        store (CombineValue.rangeRegisters regs).count := by
    calc
      marked (CombineValue.rangeRegisters regs).count =
          moved (CombineValue.rangeRegisters regs).count :=
        hmarkOutside _
          (fixed_index_not_mem_bank regs 10 (by
            intro bankSlot
            fin_cases bankSlot <;> decide))
      _ = bankInitialized (CombineValue.rangeRegisters regs).count :=
        hmoveOutside _ (regs.injective.ne (by decide))
      _ = oldReplaced (CombineValue.rangeRegisters regs).count :=
        hinitializedOutside _
          (regs.injective.ne (by decide))
          (regs.injective.ne (by decide))
          (regs.injective.ne (by decide))
      _ = oldPrepared (CombineValue.rangeRegisters regs).count :=
        hreplaceOutside _
          (fixed_index_not_mem_bank regs 10 (by
            intro bankSlot
            fin_cases bankSlot <;> decide))
      _ = oldRead (CombineValue.rangeRegisters regs).count :=
        hprepareOldOutside _
          (regs.injective.ne (by decide))
          (regs.injective.ne (by decide))
      _ = originRecorded (CombineValue.rangeRegisters regs).count :=
        hreadOutside _
          (fixed_index_not_mem_bank regs 10 (by
            intro bankSlot
            fin_cases bankSlot <;> decide))
      _ = restored (CombineValue.rangeRegisters regs).count :=
        horiginOutside _
          (regs.injective.ne (by decide))
          (regs.injective.ne (by decide))
          (regs.injective.ne (by decide))
      _ = store (CombineValue.rangeRegisters regs).count :=
        hrestoredCount
  let bankOneSet :=
    (Basic.imm (bankRegisters regs).one 1).exec marked
  have hbankOneRun :
      Runs (.basic (.imm (bankRegisters regs).one 1))
        marked bankOneSet :=
    Runs.basic _ _
  let final :=
    (Basic.imm (CombineValue.rangeRegisters regs).one 1).exec
      bankOneSet
  have hfinalOneRun :
      Runs (restoreRangeOne regs) bankOneSet final :=
    Runs.basic _ _
  have hfullRun :
      Runs
        (updateTape tm controller selected write direction regs)
        store final := by
    simpa [updateTape, Cmd.seqList] using
      Runs.seq hscanRun
        (Runs.seq hcopyRun
          (Runs.seq hsaveRun
            (Runs.seq hcenterRun
              (Runs.seq hrestoreRun
                (Runs.seq horiginRun
                  (Runs.seq hreadRun
                    (Runs.seq hprepareOldRun
                      (Runs.seq hreplaceRun
                        (Runs.seq hinitializeRun
                          (Runs.seq hmoveRun
                            (Runs.seq hmarkRun
                              (Runs.seq hbankOneRun
                                hfinalOneRun))))))))))))
  have hfinalWord :
      final (bankRegisters regs).word =
        marked (bankRegisters regs).word := by
    simp [final, bankOneSet, Basic.exec,
      CombineValue.rangeRegisters, bankRegisters,
      PackedLocalHeadScan.bankRegisters, PackedLocalHeadScan.bankMap,
      regs.injective.eq_iff]
  have hfinalAccumulator :
      final (CombineValue.rangeRegisters regs).accumulator =
        store (CombineValue.rangeRegisters regs).accumulator := by
    calc
      final (CombineValue.rangeRegisters regs).accumulator =
          marked (CombineValue.rangeRegisters regs).accumulator := by
        simp [final, bankOneSet, Basic.exec,
          CombineValue.rangeRegisters, bankRegisters,
          PackedLocalHeadScan.bankRegisters,
          PackedLocalHeadScan.bankMap, regs.injective.eq_iff]
      _ = store (CombineValue.rangeRegisters regs).accumulator :=
        hmarkedAccumulator
  have hfinalCount :
      final (CombineValue.rangeRegisters regs).count =
        store (CombineValue.rangeRegisters regs).count := by
    calc
      final (CombineValue.rangeRegisters regs).count =
          marked (CombineValue.rangeRegisters regs).count := by
        simp [final, bankOneSet, Basic.exec,
          CombineValue.rangeRegisters, bankRegisters,
          PackedLocalHeadScan.bankRegisters,
          PackedLocalHeadScan.bankMap, regs.injective.eq_iff]
      _ = store (CombineValue.rangeRegisters regs).count :=
        hmarkedCount
  have hfinalOne :
      final (CombineValue.rangeRegisters regs).one = 1 := by
    simp [final, Basic.exec]
  have hfinalRep :
      PackedLocalRepresentation.Represents tm order
        instanceData.blockLength centers
        (updateNamedTape cfg selected write direction)
        suffix (final (bankRegisters regs).word) := by
    rw [hfinalWord]
    exact hmarkedRep
  have houtside :
      ∀ address, address ∉ footprint regs →
        final address = store address := by
    intro address haddress
    exact Footprint.runs_eq_outside
      (updateTape_writesWithin tm controller selected write direction
        regs)
      hfullRun haddress
  refine ⟨final, hfullRun, ?_⟩
  exact
    { represents := hfinalRep
      context :=
        { assignment_eq := houtside _
            (by
              simpa [CombineValue.rangeRegisters] using
                fixed_index_not_mem_footprint regs 21 (by
                  intro writeSlot
                  fin_cases writeSlot <;> decide))
          accumulator_eq := hfinalAccumulator
          count_eq := hfinalCount
          one_eq := hfinalOne.trans hrangeOne.symm
          catalyticWord_eq := houtside _
            (fixed_index_not_mem_footprint regs 33 (by
              intro writeSlot
              fin_cases writeSlot <;> decide))
          abi := preservesABI_of_runs regs
            (updateTape_writesWithin tm controller selected write
              direction regs)
            hfullRun }
      eq_outside := houtside }

private def setState
    (cfg : Cfg workTapeCount Q) (state : Q) :
    Cfg workTapeCount Q :=
  { cfg with state }

private theorem configurationDigit_setState
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (blockLength : ℕ)
    (centers : TapeIndex workTapeCount → ℕ)
    (cfg : Cfg workTapeCount tm.Q)
    (state : tm.Q)
    (coordinate : ℕ) :
    PackedLocalConfiguration.configurationDigit tm order blockLength
        centers (setState cfg state) coordinate =
      if coordinate = 0 then
        CompactValueCodeSemantics.stateCode order state
      else
        PackedLocalConfiguration.configurationDigit tm order blockLength
          centers cfg coordinate := by
  by_cases hzero : coordinate = 0
  · subst coordinate
    simp [PackedLocalConfiguration.configurationDigit, setState]
  · simp [PackedLocalConfiguration.configurationDigit, setState,
      PackedLocalConfiguration.cellDigit, tapeAt, hzero]

private theorem setState_represents
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (blockLength : ℕ)
    (centers : TapeIndex workTapeCount → ℕ)
    (cfg : Cfg workTapeCount tm.Q)
    (state : tm.Q)
    (suffix word : ℕ)
    (hrep :
      PackedLocalRepresentation.Represents tm order blockLength
        centers cfg suffix word) :
    PackedLocalRepresentation.Represents tm order blockLength centers
      (setState cfg state) suffix
      (NeighborhoodProgram.replaceAt
        (PackedLocalConfiguration.radix tm) word 0
        (CompactValueCodeSemantics.stateCode order state)) := by
  apply PackedLocalRepresentation.replaceAt_represents tm order
    blockLength centers cfg (setState cfg state) suffix word 0
      (CompactValueCodeSemantics.stateCode order state) hrep
  · simp [PackedLocalConfiguration.digitCount]
  · exact PackedLocalConfiguration.stateCode_lt_radix tm order state
  · intro coordinate _hcoordinate
    exact configurationDigit_setState tm order blockLength centers cfg
      state coordinate

private theorem readState_runs
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (blockLength : ℕ)
    (centers : TapeIndex workTapeCount → ℕ)
    (cfg : Cfg workTapeCount tm.Q)
    (suffix word : ℕ)
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store)
    (hword : store (bankRegisters regs).word = word)
    (hrep :
      PackedLocalRepresentation.Represents tm order blockLength
        centers cfg suffix word) :
    ∃ final,
      Runs (readState tm regs) store final ∧
      final (bankRegisters regs).word = word ∧
      final (bankRegisters regs).result =
        CompactValueCodeSemantics.stateCode order cfg.state ∧
      final (bankRegisters regs).one = 1 ∧
      final (CombineValue.rangeRegisters regs).one = 1 ∧
      ∀ address, address ∉ (bankRegisters regs).footprint →
        final address = store address := by
  obtain ⟨initialized, hinitializeRun, hinitializedWord,
      hinitializedBase, hinitializedBasePred, hinitializedOne,
      hinitializedOutside⟩ :=
    initializeBank_runs tm regs store word hword
  let indexed :=
    (Basic.imm (bankRegisters regs).indexCount 0).exec initialized
  have hindexRun :
      Runs (.basic (.imm (bankRegisters regs).indexCount 0))
        initialized indexed :=
    Runs.basic _ _
  have hindexedWord :
      indexed (bankRegisters regs).word = word := by
    calc
      indexed (bankRegisters regs).word =
          initialized (bankRegisters regs).word := by
        simp [indexed, Basic.exec, bankRegisters,
          PackedLocalHeadScan.bankRegisters,
          PackedLocalHeadScan.bankMap, regs.injective.eq_iff]
      _ = word := hinitializedWord
  have hindexedBase :
      indexed (bankRegisters regs).base =
        PackedLocalConfiguration.radix tm := by
    calc
      indexed (bankRegisters regs).base =
          initialized (bankRegisters regs).base := by
        simp [indexed, Basic.exec, bankRegisters,
          PackedLocalHeadScan.bankRegisters,
          PackedLocalHeadScan.bankMap, regs.injective.eq_iff]
      _ = PackedLocalConfiguration.radix tm := hinitializedBase
  have hindexedBasePred :
      indexed (bankRegisters regs).basePred =
        PackedLocalConfiguration.radix tm - 1 := by
    calc
      indexed (bankRegisters regs).basePred =
          initialized (bankRegisters regs).basePred := by
        simp [indexed, Basic.exec, bankRegisters,
          PackedLocalHeadScan.bankRegisters,
          PackedLocalHeadScan.bankMap, regs.injective.eq_iff]
      _ = PackedLocalConfiguration.radix tm - 1 :=
        hinitializedBasePred
  have hindexedOne :
      indexed (bankRegisters regs).one = 1 := by
    calc
      indexed (bankRegisters regs).one =
          initialized (bankRegisters regs).one := by
        simp [indexed, Basic.exec, bankRegisters,
          PackedLocalHeadScan.bankRegisters,
          PackedLocalHeadScan.bankMap, regs.injective.eq_iff]
      _ = 1 := hinitializedOne
  have hindexedCoordinate :
      indexed (bankRegisters regs).indexCount = 0 := by
    simp [indexed, Basic.exec]
  obtain ⟨read, hreadRun, hreadWord, _hreadBuffer,
      _hreadIndex, _hreadCompleted, hreadResult, _hreadBase,
      _hreadBasePred, hreadOne, _hreadReplacement⟩ :=
    NeighborhoodProgram.bankRead_runs (bankRegisters regs) indexed
      (PackedLocalConfiguration.radix tm) word 0
      (PackedLocalConfiguration.radix_pos tm) hindexedWord
      hindexedBase hindexedBasePred hindexedOne hindexedCoordinate
  let final :=
    (Basic.imm (CombineValue.rangeRegisters regs).one 1).exec read
  have hrestoreRun :
      Runs (restoreRangeOne regs) read final :=
    Runs.basic _ _
  refine ⟨final, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [readState, Cmd.seqList] using
      Runs.seq hinitializeRun
        (Runs.seq hindexRun (Runs.seq hreadRun hrestoreRun))
  · simpa [final, Basic.exec, CombineValue.rangeRegisters,
      bankRegisters, PackedLocalHeadScan.bankRegisters,
      PackedLocalHeadScan.bankMap, regs.injective.eq_iff] using
      hreadWord
  · calc
      final (bankRegisters regs).result =
          PackedDigits.digit (PackedLocalConfiguration.radix tm)
            word 0 := by
        simpa [final, Basic.exec, CombineValue.rangeRegisters,
          bankRegisters, PackedLocalHeadScan.bankRegisters,
          PackedLocalHeadScan.bankMap, regs.injective.eq_iff] using
          hreadResult
      _ = CompactValueCodeSemantics.stateCode order cfg.state :=
        PackedLocalRepresentation.represents_state tm order blockLength
          centers cfg suffix word hrep
  · simpa [final, Basic.exec, CombineValue.rangeRegisters,
      bankRegisters, PackedLocalHeadScan.bankRegisters,
      PackedLocalHeadScan.bankMap, regs.injective.eq_iff] using
      hreadOne
  · simp [final, Basic.exec]
  · intro address haddress
    have outsideNe (slot : Fin 12) :
        address ≠ (bankRegisters regs).index slot := by
      intro heq
      apply haddress
      rw [heq]
      exact (bankRegisters regs).index_mem_footprint slot
    have hneRangeOne :
        address ≠ (CombineValue.rangeRegisters regs).one := by
      simpa [CombineValue.rangeRegisters, bankRegisters,
        PackedLocalHeadScan.bankRegisters, PackedLocalHeadScan.bankMap] using
        outsideNe 9
    calc
      final address = read address := by
        simp [final, Basic.exec, hneRangeOne]
      _ = indexed address :=
        Footprint.runs_eq_outside
          (NeighborhoodProgram.bankRead_sourceWritesWithin
            (bankRegisters regs))
          hreadRun haddress
      _ = initialized address := by
        simp [indexed, Basic.exec, outsideNe 8]
      _ = store address :=
        hinitializedOutside address (outsideNe 2)
          (outsideNe 3) (outsideNe 6)

private theorem replaceState_runs
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (state : tm.Q)
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store)
    (word : ℕ)
    (hword : store (bankRegisters regs).word = word) :
    ∃ final,
      Runs (replaceState tm order state regs) store final ∧
      final (bankRegisters regs).word =
        NeighborhoodProgram.replaceAt
          (PackedLocalConfiguration.radix tm) word 0
          (CompactValueCodeSemantics.stateCode order state) ∧
      final (bankRegisters regs).one = 1 ∧
      final (CombineValue.rangeRegisters regs).one = 1 ∧
      ∀ address, address ∉ (bankRegisters regs).footprint →
        final address = store address := by
  obtain ⟨initialized, hinitializeRun, hinitializedWord,
      hinitializedBase, hinitializedBasePred, hinitializedOne,
      hinitializedOutside⟩ :=
    initializeBank_runs tm regs store word hword
  let indexed :=
    (Basic.imm (bankRegisters regs).indexCount 0).exec initialized
  have hindexRun :
      Runs (.basic (.imm (bankRegisters regs).indexCount 0))
        initialized indexed :=
    Runs.basic _ _
  have hindexedOutside :
      ∀ address, address ≠ (bankRegisters regs).indexCount →
        indexed address = initialized address := by
    intro address haddress
    simp [indexed, Basic.exec, haddress]
  let replacementSet :=
    (Basic.imm (bankRegisters regs).replacement
      (CompactValueCodeSemantics.stateCode order state)).exec indexed
  have hreplacementRun :
      Runs
        (.basic
          (.imm (bankRegisters regs).replacement
            (CompactValueCodeSemantics.stateCode order state)))
        indexed replacementSet :=
    Runs.basic _ _
  have hreplacementOutside :
      ∀ address, address ≠ (bankRegisters regs).replacement →
        replacementSet address = indexed address := by
    intro address haddress
    simp [replacementSet, Basic.exec, haddress]
  have hreplacementWord :
      replacementSet (bankRegisters regs).word = word := by
    rw [hreplacementOutside _ ((bankRegisters regs).index_ne
      (by decide))]
    rw [hindexedOutside _ ((bankRegisters regs).index_ne
      (by decide))]
    exact hinitializedWord
  have hreplacementBase :
      replacementSet (bankRegisters regs).base =
        PackedLocalConfiguration.radix tm := by
    rw [hreplacementOutside _ ((bankRegisters regs).index_ne
      (by decide))]
    rw [hindexedOutside _ ((bankRegisters regs).index_ne
      (by decide))]
    exact hinitializedBase
  have hreplacementBasePred :
      replacementSet (bankRegisters regs).basePred =
        PackedLocalConfiguration.radix tm - 1 := by
    rw [hreplacementOutside _ ((bankRegisters regs).index_ne
      (by decide))]
    rw [hindexedOutside _ ((bankRegisters regs).index_ne
      (by decide))]
    exact hinitializedBasePred
  have hreplacementOne :
      replacementSet (bankRegisters regs).one = 1 := by
    rw [hreplacementOutside _ ((bankRegisters regs).index_ne
      (by decide))]
    rw [hindexedOutside _ ((bankRegisters regs).index_ne
      (by decide))]
    exact hinitializedOne
  have hreplacementIndex :
      replacementSet (bankRegisters regs).indexCount = 0 := by
    rw [hreplacementOutside _ ((bankRegisters regs).index_ne
      (by decide))]
    simp [indexed, Basic.exec]
  have hreplacementValue :
      replacementSet (bankRegisters regs).replacement =
        CompactValueCodeSemantics.stateCode order state := by
    simp [replacementSet, Basic.exec]
  obtain ⟨replaced, hreplaceRun, hreplaceWord, _hreplaceBuffer,
      _hreplaceIndex, _hreplaceCompleted, _hreplaceResult,
      _hreplaceBase, _hreplaceBasePred, hreplaceOne,
      _hreplaceReplacement⟩ :=
    NeighborhoodProgram.bankReplace_runs (bankRegisters regs)
      replacementSet (PackedLocalConfiguration.radix tm) word 0
      (CompactValueCodeSemantics.stateCode order state)
      (PackedLocalConfiguration.radix_pos tm) hreplacementWord
      hreplacementBase hreplacementBasePred hreplacementOne
      hreplacementIndex hreplacementValue
  let final :=
    (Basic.imm (CombineValue.rangeRegisters regs).one 1).exec
      replaced
  have hrestoreRun :
      Runs (restoreRangeOne regs) replaced final :=
    Runs.basic _ _
  refine ⟨final, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [replaceState, Cmd.seqList] using
      Runs.seq hinitializeRun
        (Runs.seq hindexRun
          (Runs.seq hreplacementRun
            (Runs.seq hreplaceRun hrestoreRun)))
  · simpa [final, Basic.exec, CombineValue.rangeRegisters,
      bankRegisters, PackedLocalHeadScan.bankRegisters,
      PackedLocalHeadScan.bankMap, regs.injective.eq_iff] using
      hreplaceWord
  · simpa [final, Basic.exec, CombineValue.rangeRegisters,
      bankRegisters, PackedLocalHeadScan.bankRegisters,
      PackedLocalHeadScan.bankMap, regs.injective.eq_iff] using
      hreplaceOne
  · simp [final, Basic.exec]
  · intro address haddress
    have outsideNe (slot : Fin 12) :
        address ≠ (bankRegisters regs).index slot := by
      intro heq
      apply haddress
      rw [heq]
      exact (bankRegisters regs).index_mem_footprint slot
    have hneRangeOne :
        address ≠ (CombineValue.rangeRegisters regs).one := by
      simpa [CombineValue.rangeRegisters, bankRegisters,
        PackedLocalHeadScan.bankRegisters, PackedLocalHeadScan.bankMap] using
        outsideNe 9
    calc
      final address = replaced address := by
        simp [final, Basic.exec, hneRangeOne]
      _ = replacementSet address :=
        Footprint.runs_eq_outside
          (NeighborhoodProgram.bankReplace_sourceWritesWithin
            (bankRegisters regs))
          hreplaceRun haddress
      _ = indexed address :=
        hreplacementOutside address (outsideNe 11)
      _ = initialized address :=
        hindexedOutside address (outsideNe 8)
      _ = store address :=
        hinitializedOutside address (outsideNe 2)
          (outsideNe 3) (outsideNe 6)

private theorem dispatchGamma_prepare
    (regs : NeighborhoodTrial.Registers controller)
    (next : Γ → Cmd)
    (symbol : Γ)
    (store : Store)
    (hresult :
      store (bankRegisters regs).result =
        CompactValueCodeSemantics.gammaCode symbol)
    (hone : store (bankRegisters regs).one = 1) :
    ∃ prepared,
      (∀ final, Runs (next symbol) prepared final →
        Runs (dispatchGamma regs next) store final) ∧
      ∀ address, address ≠ (bankRegisters regs).test →
        prepared address = store address := by
  cases symbol with
  | zero =>
      refine ⟨store, ?_, fun _ _ => rfl⟩
      intro final hnext
      simpa [dispatchGamma,
        CompactValueCodeSemantics.gammaCode,
        NeighborhoodExecutableEvaluation.FiniteEncoding.gammaEquiv] using
        Runs.ifZero hresult hnext
  | one =>
      let prepared :=
        (Basic.sub (bankRegisters regs).test
          (bankRegisters regs).result
          (bankRegisters regs).one).exec store
      have hprefixRun :
          Runs
            (.basic
              (.sub (bankRegisters regs).test
                (bankRegisters regs).result
                (bankRegisters regs).one))
            store prepared :=
        Runs.basic _ _
      have hresultNonzero :
          store (bankRegisters regs).result ≠ 0 := by
        rw [hresult]
        decide
      have htestZero :
          prepared (bankRegisters regs).test = 0 := by
        simp only [prepared, Basic.exec, Function.update_self]
        rw [hresult, hone]
        decide
      refine ⟨prepared, ?_, ?_⟩
      · intro final hnext
        simpa [dispatchGamma,
          CompactValueCodeSemantics.gammaCode,
          NeighborhoodExecutableEvaluation.FiniteEncoding.gammaEquiv] using
          Runs.ifNonzero hresultNonzero
            (Runs.seq hprefixRun (Runs.ifZero htestZero hnext))
      · intro address haddress
        simp [prepared, Basic.exec, haddress]
  | blank =>
      let first :=
        (Basic.sub (bankRegisters regs).test
          (bankRegisters regs).result
          (bankRegisters regs).one).exec store
      have hfirstRun :
          Runs
            (.basic
              (.sub (bankRegisters regs).test
                (bankRegisters regs).result
                (bankRegisters regs).one))
            store first :=
        Runs.basic _ _
      let prepared :=
        (Basic.sub (bankRegisters regs).test
          (bankRegisters regs).test
          (bankRegisters regs).one).exec first
      have hsecondRun :
          Runs
            (.basic
              (.sub (bankRegisters regs).test
                (bankRegisters regs).test
                (bankRegisters regs).one))
            first prepared :=
        Runs.basic _ _
      have hresultNonzero :
          store (bankRegisters regs).result ≠ 0 := by
        rw [hresult]
        decide
      have hfirstValue :
          first (bankRegisters regs).test = 1 := by
        simp only [first, Basic.exec, Function.update_self]
        rw [hresult, hone]
        decide
      have hfirstOne :
          first (bankRegisters regs).one = 1 := by
        calc
          first (bankRegisters regs).one =
              store (bankRegisters regs).one := by
            simp [first, Basic.exec,
              (bankRegisters regs).index_ne
                (first := (6 : Fin 12)) (second := (5 : Fin 12))
                (by decide)]
          _ = 1 := hone
      have hfirstNonzero :
          first (bankRegisters regs).test ≠ 0 := by
        omega
      have htestZero :
          prepared (bankRegisters regs).test = 0 := by
        simp only [prepared, Basic.exec, Function.update_self]
        rw [hfirstValue, hfirstOne]
      refine ⟨prepared, ?_, ?_⟩
      · intro final hnext
        simpa [dispatchGamma,
          CompactValueCodeSemantics.gammaCode,
          NeighborhoodExecutableEvaluation.FiniteEncoding.gammaEquiv] using
          Runs.ifNonzero hresultNonzero
            (Runs.seq hfirstRun
              (Runs.ifNonzero hfirstNonzero
                (Runs.seq hsecondRun (Runs.ifZero htestZero hnext))))
      · intro address haddress
        simp [prepared, first, Basic.exec, haddress]
  | start =>
      let first :=
        (Basic.sub (bankRegisters regs).test
          (bankRegisters regs).result
          (bankRegisters regs).one).exec store
      have hfirstRun :
          Runs
            (.basic
              (.sub (bankRegisters regs).test
                (bankRegisters regs).result
                (bankRegisters regs).one))
            store first :=
        Runs.basic _ _
      let prepared :=
        (Basic.sub (bankRegisters regs).test
          (bankRegisters regs).test
          (bankRegisters regs).one).exec first
      have hsecondRun :
          Runs
            (.basic
              (.sub (bankRegisters regs).test
                (bankRegisters regs).test
                (bankRegisters regs).one))
            first prepared :=
        Runs.basic _ _
      have hresultNonzero :
          store (bankRegisters regs).result ≠ 0 := by
        rw [hresult]
        decide
      have hfirstValue :
          first (bankRegisters regs).test = 2 := by
        simp only [first, Basic.exec, Function.update_self]
        rw [hresult, hone]
        decide
      have hfirstOne :
          first (bankRegisters regs).one = 1 := by
        calc
          first (bankRegisters regs).one =
              store (bankRegisters regs).one := by
            simp [first, Basic.exec,
              (bankRegisters regs).index_ne
                (first := (6 : Fin 12)) (second := (5 : Fin 12))
                (by decide)]
          _ = 1 := hone
      have hfirstNonzero :
          first (bankRegisters regs).test ≠ 0 := by
        omega
      have htestNonzero :
          prepared (bankRegisters regs).test ≠ 0 := by
        simp only [prepared, Basic.exec, Function.update_self]
        rw [hfirstValue, hfirstOne]
        decide
      refine ⟨prepared, ?_, ?_⟩
      · intro final hnext
        simpa [dispatchGamma,
          CompactValueCodeSemantics.gammaCode,
          NeighborhoodExecutableEvaluation.FiniteEncoding.gammaEquiv] using
          Runs.ifNonzero hresultNonzero
            (Runs.seq hfirstRun
              (Runs.ifNonzero hfirstNonzero
                (Runs.seq hsecondRun
                  (Runs.ifNonzero htestNonzero hnext))))
      · intro address haddress
        simp [prepared, first, Basic.exec, haddress]

private theorem scanAndDispatch_prepare
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (centers : TapeIndex workTapeCount → ℕ)
    (cfg : Cfg workTapeCount tm.Q)
    (tape : TapeIndex workTapeCount)
    (suffix word : ℕ)
    (regs : NeighborhoodTrial.Registers controller)
    (next : Γ → Cmd)
    (store : Store)
    (hblock : store (Layout.blockLength regs) = blockLength)
    (hword : store (bankRegisters regs).word = word)
    (hrep :
      PackedLocalRepresentation.Represents tm order blockLength
        centers cfg suffix word)
    (hrangeOne :
      store (CombineValue.rangeRegisters regs).one = 1)
    (hlower :
      PackedLocalConfiguration.windowStart blockLength
          (centers tape) ≤
        (tapeAt cfg tape).head)
    (hupper :
      (tapeAt cfg tape).head <
        PackedLocalConfiguration.windowStart blockLength
            (centers tape) +
          PackedLocalConfiguration.tapeSpan blockLength) :
    let symbol :=
      (tapeAt cfg tape).cells (tapeAt cfg tape).head
    ∃ prepared,
      (∀ final, Runs (next symbol) prepared final →
        Runs (scanAndDispatch tm tape regs next) store final) ∧
      prepared (bankRegisters regs).word = word ∧
      prepared (CombineValue.rangeRegisters regs).one = 1 ∧
      ∀ address, address ∉ PackedLocalHeadScan.footprint regs →
        prepared address = store address := by
  dsimp only
  let symbol :=
    (tapeAt cfg tape).cells (tapeAt cfg tape).head
  obtain ⟨scanned, hscanRun, hscanPost, _hscanPreserves⟩ :=
    PackedLocalHeadScan.scan_runs_represents tm order blockLength
      hpositive centers cfg tape suffix word regs store hblock hword
      hrep hrangeOne hlower hupper
  let oneSet :=
    (Basic.imm (bankRegisters regs).one 1).exec scanned
  have honeRun :
      Runs (.basic (.imm (bankRegisters regs).one 1))
        scanned oneSet :=
    Runs.basic _ _
  have honeValue :
      oneSet (bankRegisters regs).one = 1 := by
    simp [oneSet, Basic.exec]
  have honeResult :
      oneSet (bankRegisters regs).result =
        CompactValueCodeSemantics.gammaCode symbol := by
    calc
      oneSet (bankRegisters regs).result =
          scanned (bankRegisters regs).result := by
        simp [oneSet, Basic.exec,
          (bankRegisters regs).index_ne
            (first := (10 : Fin 12)) (second := (6 : Fin 12))
            (by decide)]
      _ = CompactValueCodeSemantics.gammaCode symbol := by
        simpa [symbol, PackedLocalHeadScan.symbolCode] using
          hscanPost.symbol_eq
  obtain ⟨prepared, hdispatch, hdispatchOutside⟩ :=
    dispatchGamma_prepare regs next symbol oneSet honeResult honeValue
  have hpreparedWord :
      prepared (bankRegisters regs).word = word := by
    calc
      prepared (bankRegisters regs).word =
          oneSet (bankRegisters regs).word :=
        hdispatchOutside _
          ((bankRegisters regs).index_ne
            (first := (0 : Fin 12)) (second := (5 : Fin 12))
            (by decide))
      _ = scanned (bankRegisters regs).word := by
        simp [oneSet, Basic.exec,
          (bankRegisters regs).index_ne
            (first := (0 : Fin 12)) (second := (6 : Fin 12))
            (by decide)]
      _ = word := hscanPost.word_eq
  have hpreparedRangeOne :
      prepared (CombineValue.rangeRegisters regs).one = 1 := by
    calc
      prepared (CombineValue.rangeRegisters regs).one =
          oneSet (CombineValue.rangeRegisters regs).one :=
        hdispatchOutside _ (regs.injective.ne (by decide))
      _ = scanned (CombineValue.rangeRegisters regs).one := by
        simp [oneSet, Basic.exec, CombineValue.rangeRegisters,
          bankRegisters, PackedLocalHeadScan.bankRegisters,
          PackedLocalHeadScan.bankMap, regs.injective.eq_iff]
      _ = store (CombineValue.rangeRegisters regs).one :=
        hscanPost.rangeOne_eq
      _ = 1 := hrangeOne
  refine ⟨prepared, ?_, hpreparedWord, hpreparedRangeOne, ?_⟩
  · intro final hnext
    simpa [scanAndDispatch, Cmd.seqList] using
      Runs.seq hscanRun (Runs.seq honeRun (hdispatch final hnext))
  · intro address haddress
    have hneOne : address ≠ (bankRegisters regs).one := by
      intro heq
      apply haddress
      rw [heq]
      exact Finset.mem_union.mpr
        (Or.inl ((bankRegisters regs).index_mem_footprint 6))
    have hneTest : address ≠ (bankRegisters regs).test := by
      intro heq
      apply haddress
      rw [heq]
      exact Finset.mem_union.mpr
        (Or.inl ((bankRegisters regs).index_mem_footprint 5))
    calc
      prepared address = oneSet address :=
        hdispatchOutside address hneTest
      _ = scanned address := by
        simp [oneSet, Basic.exec, hneOne]
      _ = store address := hscanPost.eq_outside address haddress

private theorem fixed_index_not_mem_headScan
    (regs : NeighborhoodTrial.Registers controller)
    (slot : Fin 34)
    (hbank :
      ∀ bankSlot, slot ≠ PackedLocalHeadScan.bankMap bankSlot)
    (hcountdown : slot ≠ 30) :
    regs.index slot ∉ PackedLocalHeadScan.footprint regs := by
  intro hmember
  simp only [PackedLocalHeadScan.footprint, Finset.mem_union,
    NeighborhoodProgram.BankRegisters.footprint,
    Finset.mem_image, Finset.mem_univ, true_and,
    Finset.mem_singleton] at hmember
  rcases hmember with ⟨bankSlot, hslot⟩ | hslot
  · exact hbank bankSlot (regs.injective hslot.symm)
  · exact hcountdown (regs.injective hslot)

private theorem controller_guess_not_mem_headScan
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) :
    controller.guess ∉ PackedLocalHeadScan.footprint regs := by
  intro hmember
  simp only [PackedLocalHeadScan.footprint, Finset.mem_union,
    NeighborhoodProgram.BankRegisters.footprint,
    Finset.mem_image, Finset.mem_univ, true_and,
    Finset.mem_singleton] at hmember
  rcases hmember with ⟨bankSlot, hslot⟩ | hslot
  · exact regs.index_ne_controller
      (PackedLocalHeadScan.bankMap bankSlot) (2 : Fin 17) hslot
  · exact regs.index_ne_controller
      (30 : Fin 34) (2 : Fin 17) hslot.symm

private theorem computationContext_of_headScanOutside
    {tm : TM workTapeCount}
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (nodeTape : TapeIndex workTapeCount)
    (slot : NeighborhoodGraph.Slot)
    (interval : ℕ)
    (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (initial final : Store)
    (houtside :
      ∀ address, address ∉ PackedLocalHeadScan.footprint regs →
        final address = initial address)
    (hcontext :
      CombineTerm.ComputationContext regs instanceData nodeTape slot
        interval logicalBank initial) :
    CombineTerm.ComputationContext regs instanceData nodeTape slot
      interval logicalBank final := by
  have fixed
      (physical : Fin 34)
      (hbank :
        ∀ bankSlot,
          physical ≠ PackedLocalHeadScan.bankMap bankSlot)
      (hcountdown : physical ≠ 30) :
      final (regs.index physical) = initial (regs.index physical) :=
    houtside _ (fixed_index_not_mem_headScan regs physical hbank
      hcountdown)
  have habi : ControlDecode.PreservesABI regs initial final :=
    { fuel_eq := fixed 22 (by
        intro bankSlot
        fin_cases bankSlot <;> decide) (by decide)
      nodeCode_eq := fixed 23 (by
        intro bankSlot
        fin_cases bankSlot <;> decide) (by decide)
      scalar_eq := fixed 25 (by
        intro bankSlot
        fin_cases bankSlot <;> decide) (by decide)
      out_eq := fixed 26 (by
        intro bankSlot
        fin_cases bankSlot <;> decide) (by decide)
      phaseCode_eq := fixed 27 (by
        intro bankSlot
        fin_cases bankSlot <;> decide) (by decide)
      active_eq := fixed 28 (by
        intro bankSlot
        fin_cases bankSlot <;> decide) (by decide)
      blockLength_eq := fixed 2 (by
        intro bankSlot
        fin_cases bankSlot <;> decide) (by decide)
      horizon_eq := fixed 3 (by
        intro bankSlot
        fin_cases bankSlot <;> decide) (by decide)
      chunkCount_eq := fixed 7 (by
        intro bankSlot
        fin_cases bankSlot <;> decide) (by decide)
      chunkRadix_eq := fixed 8 (by
        intro bankSlot
        fin_cases bankSlot <;> decide) (by decide)
      frameRadix_eq := fixed 13 (by
        intro bankSlot
        fin_cases bankSlot <;> decide) (by decide)
      bankRadix_eq := fixed 14 (by
        intro bankSlot
        fin_cases bankSlot <;> decide) (by decide)
      bankDigitCount_eq := fixed 15 (by
        intro bankSlot
        fin_cases bankSlot <;> decide) (by decide)
      modulusPred_eq := fixed 16 (by
        intro bankSlot
        fin_cases bankSlot <;> decide) (by decide)
      modulus_eq := fixed 24 (by
        intro bankSlot
        fin_cases bankSlot <;> decide) (by decide) }
  apply CombineTerm.Internal.computationContext_transport_internal
    regs instanceData nodeTape slot interval logicalBank hcontext habi
  exact fixed 33 (by
    intro bankSlot
    fin_cases bankSlot <;> decide) (by decide)

private def collectWorkHeads
    (cfg : Cfg workTapeCount Q) :
    List (Fin workTapeCount) → (Fin workTapeCount → Γ) →
      (Fin workTapeCount → Γ)
  | [], workHeads => workHeads
  | tape :: tapes, workHeads =>
      collectWorkHeads cfg tapes
        (Function.update workHeads tape (cfg.work tape).read)

private theorem dispatchWorkHeads_prepare
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (centers : TapeIndex workTapeCount → ℕ)
    (cfg : Cfg workTapeCount tm.Q)
    (suffix word : ℕ)
    (regs : NeighborhoodTrial.Registers controller)
    (next : (Fin workTapeCount → Γ) → Cmd)
    (hrep :
      PackedLocalRepresentation.Represents tm order blockLength
        centers cfg suffix word)
    (hheads : HeadsInWindow blockLength centers cfg) :
    ∀ tapes workHeads store,
      store (Layout.blockLength regs) = blockLength →
      store (bankRegisters regs).word = word →
      store (CombineValue.rangeRegisters regs).one = 1 →
      ∃ prepared,
        (∀ final,
          Runs
              (next (collectWorkHeads cfg tapes workHeads))
              prepared final →
            Runs
              (dispatchWorkHeads tm regs next tapes workHeads)
              store final) ∧
        prepared (bankRegisters regs).word = word ∧
        prepared (CombineValue.rangeRegisters regs).one = 1 ∧
        ∀ address,
          address ∉ PackedLocalHeadScan.footprint regs →
            prepared address = store address := by
  intro tapes
  induction tapes with
  | nil =>
      intro workHeads store _hblock hword hrangeOne
      exact
        ⟨store, fun _ hrun => hrun, hword, hrangeOne,
          fun _ _ => rfl⟩
  | cons tape tapes ih =>
      intro workHeads store hblock hword hrangeOne
      obtain ⟨hlower, hupper⟩ :=
        hheads (TapeIndex.work tape)
      obtain ⟨afterScan, hscanDispatch, hscanWord,
          hscanRangeOne, hscanOutside⟩ :=
        scanAndDispatch_prepare tm order blockLength hpositive
          centers cfg (TapeIndex.work tape) suffix word regs
          (fun symbol =>
            dispatchWorkHeads tm regs next tapes
              (Function.update workHeads tape symbol))
          store hblock hword hrep hrangeOne hlower hupper
      have hafterBlock :
          afterScan (Layout.blockLength regs) = blockLength := by
        calc
          afterScan (Layout.blockLength regs) =
              store (Layout.blockLength regs) :=
            hscanOutside _
              (fixed_index_not_mem_headScan regs 2 (by
                intro bankSlot
                fin_cases bankSlot <;> decide) (by decide))
          _ = blockLength := hblock
      obtain ⟨prepared, hrestDispatch, hpreparedWord,
          hpreparedRangeOne, hpreparedOutside⟩ :=
        ih
          (Function.update workHeads tape (cfg.work tape).read)
          afterScan hafterBlock hscanWord hscanRangeOne
      refine ⟨prepared, ?_, hpreparedWord, hpreparedRangeOne, ?_⟩
      · intro final hnext
        apply hscanDispatch
        simpa [tapeAt_work, Tape.read] using
          hrestDispatch final (by
            simpa [collectWorkHeads] using hnext)
      · intro address haddress
        calc
          prepared address = afterScan address :=
            hpreparedOutside address haddress
          _ = store address := hscanOutside address haddress

private theorem collectWorkHeads_apply
    (cfg : Cfg workTapeCount Q)
    (tapes : List (Fin workTapeCount))
    (hnodup : tapes.Nodup)
    (workHeads : Fin workTapeCount → Γ)
    (index : Fin workTapeCount) :
    collectWorkHeads cfg tapes workHeads index =
      if index ∈ tapes then (cfg.work index).read
      else workHeads index := by
  induction tapes generalizing workHeads with
  | nil =>
      simp [collectWorkHeads]
  | cons tape tapes ih =>
      have hparts := List.nodup_cons.mp hnodup
      rw [collectWorkHeads]
      rw [ih hparts.2]
      by_cases heq : index = tape
      · subst index
        simp [hparts.1]
      · by_cases hmem : index ∈ tapes
        · simp [heq, hmem]
        · simp [heq, hmem, Function.update]

private theorem collectWorkHeads_finRange
    (cfg : Cfg workTapeCount Q) :
    collectWorkHeads cfg (List.finRange workTapeCount)
        (fun _ => Γ.blank) =
      fun index => (cfg.work index).read := by
  funext index
  rw [collectWorkHeads_apply cfg (List.finRange workTapeCount)
    (List.nodup_finRange workTapeCount) (fun _ => Γ.blank) index]
  simp

private structure LiveState
    {tm : TM workTapeCount}
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (nodeTape : TapeIndex workTapeCount)
    (slot : NeighborhoodGraph.Slot)
    (interval : ℕ)
    (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (code :
      Fin
        (3 ^
          NeighborhoodGraph.Guess.Enumeration.movementCount
            workTapeCount instanceData.horizon))
    (centers : TapeIndex workTapeCount → ℕ)
    (suffix : ℕ)
    (initial : Store)
    (cfg : Cfg workTapeCount tm.Q)
    (store : Store) : Prop where
  represents :
    PackedLocalRepresentation.Represents tm order
      instanceData.blockLength centers cfg suffix
        (store (bankRegisters regs).word)
  computation :
    CombineTerm.ComputationContext regs instanceData nodeTape slot
      interval logicalBank store
  guess_eq : store controller.guess = code.val
  rangeOne_eq :
    store (CombineValue.rangeRegisters regs).one = 1
  accumulator_eq :
    store (CombineValue.rangeRegisters regs).accumulator =
      initial (CombineValue.rangeRegisters regs).accumulator
  count_eq :
    store (CombineValue.rangeRegisters regs).count =
      initial (CombineValue.rangeRegisters regs).count

private theorem liveState_updateTape
    {tm : TM workTapeCount}
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (nodeTape : TapeIndex workTapeCount)
    (slot : NeighborhoodGraph.Slot)
    (interval : ℕ)
    (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (code :
      Fin
        (3 ^
          NeighborhoodGraph.Guess.Enumeration.movementCount
            workTapeCount instanceData.horizon))
    (centers : TapeIndex workTapeCount → ℕ)
    (suffix : ℕ)
    (initial store : Store)
    (cfg : Cfg workTapeCount tm.Q)
    (selected : TapeIndex workTapeCount)
    (write : Option Γw) (direction : Dir3)
    (hfits :
      ∀ digit ∈
          FrameCodec.nodeDigits
            (show
              NeighborhoodEvaluator.QueryNode
                workTapeCount instanceData.horizon
              from .graph (.computation nodeTape slot interval)),
        digit < Representation.digitBase instanceData)
    (hguess :
      instanceData.guess =
        NeighborhoodGraph.Guess.Enumeration.candidateGuess code)
    (hinterval : interval ≤ instanceData.horizon)
    (hcenters :
      centers =
        NeighborhoodGraph.Guess.Consistency.guessedCenters
          instanceData.guess interval)
    (hlive :
      LiveState order regs instanceData nodeTape slot interval
        logicalBank code centers suffix initial cfg store)
    (hheads :
      HeadsInWindow instanceData.blockLength centers cfg)
    (hnextHeads :
      HeadsInWindow instanceData.blockLength centers
        (updateNamedTape cfg selected write direction)) :
    ∃ final,
      Runs (updateTape tm controller selected write direction regs)
        store final ∧
      LiveState order regs instanceData nodeTape slot interval
        logicalBank code centers suffix initial
        (updateNamedTape cfg selected write direction) final := by
  obtain ⟨final, hrun, hpost⟩ :=
    updateTape_runs_internal order regs instanceData nodeTape slot
      interval logicalBank code selected write direction centers cfg
      suffix (store (bankRegisters regs).word) store hfits
      hlive.computation hlive.guess_eq hguess hinterval hcenters
      hlive.represents hheads hnextHeads rfl hlive.rangeOne_eq
  refine ⟨final, hrun, ?_⟩
  exact
    { represents := hpost.represents
      computation := computationContext_of_runs regs instanceData
        nodeTape slot interval logicalBank
        (updateTape_writesWithin tm controller selected write direction
          regs)
        hrun hlive.computation
      guess_eq :=
        (controller_guess_eq_of_runs regs
          (updateTape_writesWithin tm controller selected write
            direction regs)
          hrun).trans hlive.guess_eq
      rangeOne_eq := hpost.context.one_eq.trans hlive.rangeOne_eq
      accumulator_eq :=
        hpost.context.accumulator_eq.trans hlive.accumulator_eq
      count_eq := hpost.context.count_eq.trans hlive.count_eq }

private theorem headsInWindow_updateNamedTape
    (blockLength : ℕ)
    (centers : TapeIndex workTapeCount → ℕ)
    (cfg : Cfg workTapeCount Q)
    (selected : TapeIndex workTapeCount)
    (write : Option Γw) (direction : Dir3)
    (hheads : HeadsInWindow blockLength centers cfg)
    (hselected :
      PackedLocalConfiguration.windowStart blockLength
          (centers selected) ≤
        (tapeAction (tapeAt cfg selected) write direction).head ∧
      (tapeAction (tapeAt cfg selected) write direction).head <
        PackedLocalConfiguration.windowStart blockLength
            (centers selected) +
          PackedLocalConfiguration.tapeSpan blockLength) :
    HeadsInWindow blockLength centers
      (updateNamedTape cfg selected write direction) := by
  intro tape
  by_cases heq : tape = selected
  · subst tape
    simpa [tapeAt_updateNamedTape_same] using hselected
  · simpa [tapeAt_updateNamedTape_ne cfg selected tape write direction
      heq] using hheads tape

private def updateWorkTapes
    (cfg : Cfg workTapeCount Q)
    (writes : Fin workTapeCount → Γw)
    (directions : Fin workTapeCount → Dir3) :
    List (Fin workTapeCount) → Cfg workTapeCount Q
  | [] => cfg
  | tape :: tapes =>
      updateWorkTapes
        (updateNamedTape cfg (TapeIndex.work tape)
          (some (writes tape)) (directions tape))
        writes directions tapes

private theorem tapeAt_setState
    (cfg : Cfg workTapeCount Q) (state : Q)
    (tape : TapeIndex workTapeCount) :
    tapeAt (setState cfg state) tape = tapeAt cfg tape := by
  unfold setState tapeAt
  split_ifs <;> rfl

private theorem headsInWindow_setState
    (blockLength : ℕ)
    (centers : TapeIndex workTapeCount → ℕ)
    (cfg : Cfg workTapeCount Q) (state : Q)
    (hheads : HeadsInWindow blockLength centers cfg) :
    HeadsInWindow blockLength centers (setState cfg state) := by
  intro tape
  simpa [tapeAt_setState] using hheads tape

private theorem tapeAt_updateWorkTapes_ne
    (cfg : Cfg workTapeCount Q)
    (writes : Fin workTapeCount → Γw)
    (directions : Fin workTapeCount → Dir3)
    (tapes : List (Fin workTapeCount))
    (named : TapeIndex workTapeCount)
    (hne :
      ∀ tape, tape ∈ tapes → named ≠ TapeIndex.work tape) :
    tapeAt (updateWorkTapes cfg writes directions tapes) named =
      tapeAt cfg named := by
  induction tapes generalizing cfg with
  | nil =>
      rfl
  | cons tape tapes ih =>
      rw [updateWorkTapes]
      rw [ih]
      · exact tapeAt_updateNamedTape_ne cfg (TapeIndex.work tape)
          named (some (writes tape)) (directions tape)
          (hne tape (by simp))
      · intro current hcurrent
        exact hne current (by simp [hcurrent])

private theorem tapeAt_updateWorkTapes_mem
    (cfg : Cfg workTapeCount Q)
    (writes : Fin workTapeCount → Γw)
    (directions : Fin workTapeCount → Dir3)
    (tapes : List (Fin workTapeCount))
    (hnodup : tapes.Nodup)
    (index : Fin workTapeCount)
    (hmem : index ∈ tapes) :
    tapeAt (updateWorkTapes cfg writes directions tapes)
        (TapeIndex.work index) =
      tapeAction (tapeAt cfg (TapeIndex.work index))
        (some (writes index)) (directions index) := by
  induction tapes generalizing cfg with
  | nil =>
      simp at hmem
  | cons tape tapes ih =>
      have hparts := List.nodup_cons.mp hnodup
      rw [updateWorkTapes]
      by_cases heq : index = tape
      · subst index
        rw [tapeAt_updateWorkTapes_ne]
        · exact tapeAt_updateNamedTape_same cfg
            (TapeIndex.work tape) (some (writes tape))
            (directions tape)
        · intro current hcurrent hnamed
          apply hparts.1
          have hcurrentEq : current = tape := by
            apply Fin.ext
            have hval := congrArg Fin.val hnamed
            simp [TapeIndex.work] at hval
            omega
          simpa [hcurrentEq] using hcurrent
      · have htail : index ∈ tapes := by
          simpa [heq] using hmem
        rw [ih
          (updateNamedTape cfg (TapeIndex.work tape)
            (some (writes tape)) (directions tape))
          hparts.2 htail]
        rw [tapeAt_updateNamedTape_ne cfg (TapeIndex.work tape)
          (TapeIndex.work index) (some (writes tape))
          (directions tape)]
        intro hnamed
        apply heq
        apply Fin.ext
        have hval := congrArg Fin.val hnamed
        simp [TapeIndex.work] at hval
        omega

private def seqThen : List Cmd → Cmd → Cmd
  | [], tail => tail
  | command :: commands, tail =>
      Cmd.seq command (seqThen commands tail)

private theorem seqList_cons_of_ne_nil
    (command : Cmd) (commands : List Cmd)
    (hne : commands ≠ []) :
    Cmd.seqList (command :: commands) =
      Cmd.seq command (Cmd.seqList commands) := by
  cases commands with
  | nil =>
      exact False.elim (hne rfl)
  | cons next rest =>
      cases rest <;> rfl

private theorem seqList_append_eq_seqThen
    (commands suffix : List Cmd)
    (hsuffix : suffix ≠ []) :
    Cmd.seqList (commands ++ suffix) =
      seqThen commands (Cmd.seqList suffix) := by
  cases suffix with
  | nil =>
      exact False.elim (hsuffix rfl)
  | cons first rest =>
      induction commands with
      | nil =>
          rfl
      | cons command commands ih =>
          rw [List.cons_append]
          rw [seqList_cons_of_ne_nil command
            (commands ++ first :: rest) (by simp)]
          rw [ih]
          rfl

private theorem liveState_updateWorkTapes
    {tm : TM workTapeCount}
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (nodeTape : TapeIndex workTapeCount)
    (slot : NeighborhoodGraph.Slot)
    (interval : ℕ)
    (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (code :
      Fin
        (3 ^
          NeighborhoodGraph.Guess.Enumeration.movementCount
            workTapeCount instanceData.horizon))
    (centers : TapeIndex workTapeCount → ℕ)
    (suffix : ℕ)
    (initial : Store)
    (writes : Fin workTapeCount → Γw)
    (directions : Fin workTapeCount → Dir3)
    (hfits :
      ∀ digit ∈
          FrameCodec.nodeDigits
            (show
              NeighborhoodEvaluator.QueryNode
                workTapeCount instanceData.horizon
              from .graph (.computation nodeTape slot interval)),
        digit < Representation.digitBase instanceData)
    (hguess :
      instanceData.guess =
        NeighborhoodGraph.Guess.Enumeration.candidateGuess code)
    (hinterval : interval ≤ instanceData.horizon)
    (hcenters :
      centers =
        NeighborhoodGraph.Guess.Consistency.guessedCenters
          instanceData.guess interval) :
    ∀ (tapes : List (Fin workTapeCount))
      (cfg : Cfg workTapeCount tm.Q) (store : Store),
      tapes.Nodup →
      LiveState order regs instanceData nodeTape slot interval
        logicalBank code centers suffix initial cfg store →
      HeadsInWindow instanceData.blockLength centers cfg →
      (∀ tape, tape ∈ tapes →
        PackedLocalConfiguration.windowStart
            instanceData.blockLength
            (centers (TapeIndex.work tape)) ≤
          (tapeAction (tapeAt cfg (TapeIndex.work tape))
            (some (writes tape)) (directions tape)).head ∧
        (tapeAction (tapeAt cfg (TapeIndex.work tape))
            (some (writes tape)) (directions tape)).head <
          PackedLocalConfiguration.windowStart
              instanceData.blockLength
              (centers (TapeIndex.work tape)) +
            PackedLocalConfiguration.tapeSpan
              instanceData.blockLength) →
      ∃ final,
        (∀ tail terminal,
          Runs tail final terminal →
            Runs
              (seqThen
                (tapes.map fun tape =>
                  updateTape tm controller (TapeIndex.work tape)
                    (some (writes tape)) (directions tape) regs)
                tail)
              store terminal) ∧
        LiveState order regs instanceData nodeTape slot interval
          logicalBank code centers suffix initial
          (updateWorkTapes cfg writes directions tapes) final ∧
        HeadsInWindow instanceData.blockLength centers
          (updateWorkTapes cfg writes directions tapes) := by
  intro tapes
  induction tapes with
  | nil =>
      intro cfg store _hnodup hlive hheads _hactions
      exact ⟨store, (by
        intro tail terminal hrun
        simpa [seqThen] using hrun),
        by simpa [updateWorkTapes] using hlive,
        by simpa [updateWorkTapes] using hheads⟩
  | cons tape tapes ih =>
      intro cfg store hnodup hlive hheads hactions
      have hparts := List.nodup_cons.mp hnodup
      have hselected :=
        hactions tape (by simp)
      have hnextHeads :
          HeadsInWindow instanceData.blockLength centers
            (updateNamedTape cfg (TapeIndex.work tape)
              (some (writes tape)) (directions tape)) :=
        headsInWindow_updateNamedTape instanceData.blockLength
          centers cfg (TapeIndex.work tape) (some (writes tape))
          (directions tape) hheads hselected
      obtain ⟨afterTape, htapeRun, hafterLive⟩ :=
        liveState_updateTape order regs instanceData nodeTape slot
          interval logicalBank code centers suffix initial store cfg
          (TapeIndex.work tape) (some (writes tape))
          (directions tape) hfits hguess hinterval hcenters hlive
          hheads hnextHeads
      have htailActions :
          ∀ current,
            current ∈ tapes →
              PackedLocalConfiguration.windowStart
                  instanceData.blockLength
                  (centers (TapeIndex.work current)) ≤
                (tapeAction
                    (tapeAt
                      (updateNamedTape cfg (TapeIndex.work tape)
                        (some (writes tape)) (directions tape))
                      (TapeIndex.work current))
                    (some (writes current))
                    (directions current)).head ∧
              (tapeAction
                  (tapeAt
                    (updateNamedTape cfg (TapeIndex.work tape)
                      (some (writes tape)) (directions tape))
                    (TapeIndex.work current))
                  (some (writes current))
                  (directions current)).head <
                PackedLocalConfiguration.windowStart
                    instanceData.blockLength
                    (centers (TapeIndex.work current)) +
                  PackedLocalConfiguration.tapeSpan
                    instanceData.blockLength := by
        intro current hcurrent
        have hne : current ≠ tape := by
          intro heq
          subst current
          exact hparts.1 hcurrent
        have hnamedNe :
            TapeIndex.work current ≠ TapeIndex.work tape := by
          intro heq
          apply hne
          apply Fin.ext
          have hval := congrArg Fin.val heq
          simp [TapeIndex.work] at hval
          omega
        simpa [tapeAt_updateNamedTape_ne cfg
          (TapeIndex.work tape) (TapeIndex.work current)
          (some (writes tape)) (directions tape) hnamedNe] using
          hactions current (by simp [hcurrent])
      obtain ⟨final, htailPrefix, hfinalLive, hfinalHeads⟩ :=
        ih
          (updateNamedTape cfg (TapeIndex.work tape)
            (some (writes tape)) (directions tape))
          afterTape hparts.2 hafterLive hnextHeads htailActions
      refine ⟨final, ?_, ?_, ?_⟩
      · intro tail terminal htail
        simpa [seqThen] using
          Runs.seq htapeRun (htailPrefix tail terminal htail)
      · simpa [updateWorkTapes] using hfinalLive
      · simpa [updateWorkTapes] using hfinalHeads

private def transitionTapes
    (cfg : Cfg workTapeCount Q)
    (workWrites : Fin workTapeCount → Γw)
    (outputWrite : Γw)
    (inputDirection : Dir3)
    (workDirections : Fin workTapeCount → Dir3)
    (outputDirection : Dir3) :
    Cfg workTapeCount Q :=
  let inputCfg :=
    updateNamedTape cfg (TapeIndex.input workTapeCount)
      none inputDirection
  let workCfg :=
    updateWorkTapes inputCfg workWrites workDirections
      (List.finRange workTapeCount)
  updateNamedTape workCfg (TapeIndex.output workTapeCount)
    (some outputWrite) outputDirection

private def transitionCfg
    (cfg : Cfg workTapeCount Q)
    (nextState : Q)
    (workWrites : Fin workTapeCount → Γw)
    (outputWrite : Γw)
    (inputDirection : Dir3)
    (workDirections : Fin workTapeCount → Dir3)
    (outputDirection : Dir3) :
    Cfg workTapeCount Q :=
  setState
    (transitionTapes cfg workWrites outputWrite inputDirection
      workDirections outputDirection)
    nextState

private theorem input_ne_work
    (index : Fin workTapeCount) :
    TapeIndex.input workTapeCount ≠ TapeIndex.work index := by
  intro heq
  have hval := congrArg Fin.val heq
  simp [TapeIndex.input, TapeIndex.work] at hval

private theorem work_ne_input
    (index : Fin workTapeCount) :
    TapeIndex.work index ≠ TapeIndex.input workTapeCount :=
  Ne.symm (input_ne_work index)

private theorem output_ne_work
    (index : Fin workTapeCount) :
    TapeIndex.output workTapeCount ≠ TapeIndex.work index := by
  intro heq
  have hval := congrArg Fin.val heq
  simp [TapeIndex.output, TapeIndex.work] at hval
  omega

private theorem work_ne_output
    (index : Fin workTapeCount) :
    TapeIndex.work index ≠ TapeIndex.output workTapeCount :=
  Ne.symm (output_ne_work index)

private theorem input_ne_output :
    TapeIndex.input workTapeCount ≠ TapeIndex.output workTapeCount := by
  intro heq
  have hval := congrArg Fin.val heq
  simp [TapeIndex.input, TapeIndex.output] at hval

private theorem output_ne_input :
    TapeIndex.output workTapeCount ≠ TapeIndex.input workTapeCount :=
  Ne.symm input_ne_output

private theorem tapeAt_transitionCfg_input
    (cfg : Cfg workTapeCount Q)
    (nextState : Q)
    (workWrites : Fin workTapeCount → Γw)
    (outputWrite : Γw)
    (inputDirection : Dir3)
    (workDirections : Fin workTapeCount → Dir3)
    (outputDirection : Dir3) :
    tapeAt
        (transitionCfg cfg nextState workWrites outputWrite
          inputDirection workDirections outputDirection)
        (TapeIndex.input workTapeCount) =
      tapeAction (tapeAt cfg (TapeIndex.input workTapeCount))
        none inputDirection := by
  unfold transitionCfg transitionTapes
  rw [tapeAt_setState]
  rw [tapeAt_updateNamedTape_ne _ (TapeIndex.output workTapeCount)
    (TapeIndex.input workTapeCount) (some outputWrite)
    outputDirection input_ne_output]
  rw [tapeAt_updateWorkTapes_ne]
  · exact tapeAt_updateNamedTape_same cfg
      (TapeIndex.input workTapeCount) none inputDirection
  · intro index _hindex
    exact input_ne_work index

private theorem tapeAt_transitionCfg_work
    (cfg : Cfg workTapeCount Q)
    (nextState : Q)
    (workWrites : Fin workTapeCount → Γw)
    (outputWrite : Γw)
    (inputDirection : Dir3)
    (workDirections : Fin workTapeCount → Dir3)
    (outputDirection : Dir3)
    (index : Fin workTapeCount) :
    tapeAt
        (transitionCfg cfg nextState workWrites outputWrite
          inputDirection workDirections outputDirection)
        (TapeIndex.work index) =
      tapeAction (tapeAt cfg (TapeIndex.work index))
        (some (workWrites index)) (workDirections index) := by
  unfold transitionCfg transitionTapes
  rw [tapeAt_setState]
  rw [tapeAt_updateNamedTape_ne _ (TapeIndex.output workTapeCount)
    (TapeIndex.work index) (some outputWrite) outputDirection
    (work_ne_output index)]
  rw [tapeAt_updateWorkTapes_mem _ workWrites workDirections
    (List.finRange workTapeCount)
    (List.nodup_finRange workTapeCount) index (by simp)]
  rw [tapeAt_updateNamedTape_ne cfg
    (TapeIndex.input workTapeCount) (TapeIndex.work index)
    none inputDirection (work_ne_input index)]

private theorem tapeAt_transitionCfg_output
    (cfg : Cfg workTapeCount Q)
    (nextState : Q)
    (workWrites : Fin workTapeCount → Γw)
    (outputWrite : Γw)
    (inputDirection : Dir3)
    (workDirections : Fin workTapeCount → Dir3)
    (outputDirection : Dir3) :
    tapeAt
        (transitionCfg cfg nextState workWrites outputWrite
          inputDirection workDirections outputDirection)
        (TapeIndex.output workTapeCount) =
      tapeAction (tapeAt cfg (TapeIndex.output workTapeCount))
        (some outputWrite) outputDirection := by
  unfold transitionCfg transitionTapes
  rw [tapeAt_setState]
  rw [tapeAt_updateNamedTape_same]
  congr 1
  rw [tapeAt_updateWorkTapes_ne]
  · exact tapeAt_updateNamedTape_ne cfg
      (TapeIndex.input workTapeCount)
      (TapeIndex.output workTapeCount) none inputDirection
      output_ne_input
  · intro index _hindex
    exact output_ne_work index

private theorem transitionCfg_eq
    (cfg : Cfg workTapeCount Q)
    (nextState : Q)
    (workWrites : Fin workTapeCount → Γw)
    (outputWrite : Γw)
    (inputDirection : Dir3)
    (workDirections : Fin workTapeCount → Dir3)
    (outputDirection : Dir3) :
    transitionCfg cfg nextState workWrites outputWrite inputDirection
        workDirections outputDirection =
      { state := nextState
        input := cfg.input.move inputDirection
        work := fun index =>
          (cfg.work index).writeAndMove
            (workWrites index) (workDirections index)
        output :=
          cfg.output.writeAndMove outputWrite outputDirection } := by
  apply Cfg.ext
  · rfl
  · simpa only [tapeAt_input, tapeAction] using
      tapeAt_transitionCfg_input cfg nextState workWrites outputWrite
        inputDirection workDirections outputDirection
  · funext index
    simpa only [tapeAt_work, tapeAction] using
      tapeAt_transitionCfg_work cfg nextState workWrites outputWrite
        inputDirection workDirections outputDirection index
  · simpa only [tapeAt_output, tapeAction] using
      tapeAt_transitionCfg_output cfg nextState workWrites outputWrite
        inputDirection workDirections outputDirection

private theorem transitionCfg_eq_step_getD
    (tm : TM workTapeCount)
    (cfg : Cfg workTapeCount tm.Q)
    (nextState : tm.Q)
    (workWrites : Fin workTapeCount → Γw)
    (outputWrite : Γw)
    (inputDirection : Dir3)
    (workDirections : Fin workTapeCount → Dir3)
    (outputDirection : Dir3)
    (hstate : cfg.state ≠ tm.qhalt)
    (hdelta :
      tm.δ cfg.state cfg.input.read (fun index => (cfg.work index).read)
          cfg.output.read =
        (nextState, workWrites, outputWrite, inputDirection,
          workDirections, outputDirection)) :
    transitionCfg cfg nextState workWrites outputWrite inputDirection
        workDirections outputDirection =
      (tm.step cfg).getD cfg := by
  rw [transitionCfg_eq]
  simp only [TM.step, hstate, ↓reduceIte, hdelta, Option.getD_some]

private theorem transitionAction_runs
    {tm : TM workTapeCount}
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (nodeTape : TapeIndex workTapeCount)
    (slot : NeighborhoodGraph.Slot)
    (interval : ℕ)
    (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (code :
      Fin
        (3 ^
          NeighborhoodGraph.Guess.Enumeration.movementCount
            workTapeCount instanceData.horizon))
    (centers : TapeIndex workTapeCount → ℕ)
    (suffix : ℕ)
    (initial : Store)
    (cfg : Cfg workTapeCount tm.Q)
    (store : Store)
    (state nextState : tm.Q)
    (inputSymbol : Γ)
    (workSymbols : Fin workTapeCount → Γ)
    (outputSymbol : Γ)
    (workWrites : Fin workTapeCount → Γw)
    (outputWrite : Γw)
    (inputDirection : Dir3)
    (workDirections : Fin workTapeCount → Dir3)
    (outputDirection : Dir3)
    (hdelta :
      tm.δ state inputSymbol workSymbols outputSymbol =
        (nextState, workWrites, outputWrite, inputDirection,
          workDirections, outputDirection))
    (hfits :
      ∀ digit ∈
          FrameCodec.nodeDigits
            (show
              NeighborhoodEvaluator.QueryNode
                workTapeCount instanceData.horizon
              from .graph (.computation nodeTape slot interval)),
        digit < Representation.digitBase instanceData)
    (hguess :
      instanceData.guess =
        NeighborhoodGraph.Guess.Enumeration.candidateGuess code)
    (hinterval : interval ≤ instanceData.horizon)
    (hcenters :
      centers =
        NeighborhoodGraph.Guess.Consistency.guessedCenters
          instanceData.guess interval)
    (hlive :
      LiveState order regs instanceData nodeTape slot interval
        logicalBank code centers suffix initial cfg store)
    (hheads :
      HeadsInWindow instanceData.blockLength centers cfg)
    (hnextHeads :
      HeadsInWindow instanceData.blockLength centers
        (transitionCfg cfg nextState workWrites outputWrite
          inputDirection workDirections outputDirection)) :
    ∃ final,
      Runs
        (transitionAction tm order controller regs state inputSymbol
          workSymbols outputSymbol)
        store final ∧
      LiveState order regs instanceData nodeTape slot interval
        logicalBank code centers suffix initial
        (transitionCfg cfg nextState workWrites outputWrite
          inputDirection workDirections outputDirection)
        final := by
  have hinputAction :
      PackedLocalConfiguration.windowStart instanceData.blockLength
          (centers (TapeIndex.input workTapeCount)) ≤
        (tapeAction (tapeAt cfg (TapeIndex.input workTapeCount))
          none inputDirection).head ∧
      (tapeAction (tapeAt cfg (TapeIndex.input workTapeCount))
          none inputDirection).head <
        PackedLocalConfiguration.windowStart instanceData.blockLength
            (centers (TapeIndex.input workTapeCount)) +
          PackedLocalConfiguration.tapeSpan instanceData.blockLength := by
    simpa only [tapeAt_transitionCfg_input] using
      hnextHeads (TapeIndex.input workTapeCount)
  have hinputHeads :
      HeadsInWindow instanceData.blockLength centers
        (updateNamedTape cfg (TapeIndex.input workTapeCount)
          none inputDirection) :=
    headsInWindow_updateNamedTape instanceData.blockLength centers cfg
      (TapeIndex.input workTapeCount) none inputDirection hheads
      hinputAction
  obtain ⟨afterInput, hinputRun, hinputLive⟩ :=
    liveState_updateTape order regs instanceData nodeTape slot interval
      logicalBank code centers suffix initial store cfg
      (TapeIndex.input workTapeCount) none inputDirection hfits hguess
      hinterval hcenters hlive hheads hinputHeads
  have hworkActions :
      ∀ tape, tape ∈ List.finRange workTapeCount →
        PackedLocalConfiguration.windowStart instanceData.blockLength
            (centers (TapeIndex.work tape)) ≤
          (tapeAction
            (tapeAt
              (updateNamedTape cfg (TapeIndex.input workTapeCount)
                none inputDirection)
              (TapeIndex.work tape))
            (some (workWrites tape)) (workDirections tape)).head ∧
        (tapeAction
          (tapeAt
            (updateNamedTape cfg (TapeIndex.input workTapeCount)
              none inputDirection)
            (TapeIndex.work tape))
          (some (workWrites tape)) (workDirections tape)).head <
        PackedLocalConfiguration.windowStart instanceData.blockLength
            (centers (TapeIndex.work tape)) +
          PackedLocalConfiguration.tapeSpan instanceData.blockLength := by
    intro tape _htape
    have hnext := hnextHeads (TapeIndex.work tape)
    rw [tapeAt_transitionCfg_work] at hnext
    simpa only [tapeAt_updateNamedTape_ne cfg
      (TapeIndex.input workTapeCount) (TapeIndex.work tape)
      none inputDirection (work_ne_input tape)] using hnext
  obtain ⟨afterWork, hworkPrefix, hworkLive, hworkHeads⟩ :=
    liveState_updateWorkTapes order regs instanceData nodeTape slot
      interval logicalBank code centers suffix initial workWrites
      workDirections hfits hguess hinterval hcenters
      (List.finRange workTapeCount)
      (updateNamedTape cfg (TapeIndex.input workTapeCount)
        none inputDirection)
      afterInput (List.nodup_finRange workTapeCount) hinputLive
      hinputHeads hworkActions
  have hworkOutput :
      tapeAt
          (updateWorkTapes
            (updateNamedTape cfg (TapeIndex.input workTapeCount)
              none inputDirection)
            workWrites workDirections (List.finRange workTapeCount))
          (TapeIndex.output workTapeCount) =
        tapeAt cfg (TapeIndex.output workTapeCount) := by
    rw [tapeAt_updateWorkTapes_ne]
    · exact tapeAt_updateNamedTape_ne cfg
        (TapeIndex.input workTapeCount)
        (TapeIndex.output workTapeCount) none inputDirection
        output_ne_input
    · intro tape _htape
      exact output_ne_work tape
  have houtputAction :
      PackedLocalConfiguration.windowStart instanceData.blockLength
          (centers (TapeIndex.output workTapeCount)) ≤
        (tapeAction
          (tapeAt
            (updateWorkTapes
              (updateNamedTape cfg (TapeIndex.input workTapeCount)
                none inputDirection)
              workWrites workDirections (List.finRange workTapeCount))
            (TapeIndex.output workTapeCount))
          (some outputWrite) outputDirection).head ∧
      (tapeAction
        (tapeAt
          (updateWorkTapes
            (updateNamedTape cfg (TapeIndex.input workTapeCount)
              none inputDirection)
            workWrites workDirections (List.finRange workTapeCount))
          (TapeIndex.output workTapeCount))
        (some outputWrite) outputDirection).head <
        PackedLocalConfiguration.windowStart instanceData.blockLength
            (centers (TapeIndex.output workTapeCount)) +
          PackedLocalConfiguration.tapeSpan instanceData.blockLength := by
    have hnext := hnextHeads (TapeIndex.output workTapeCount)
    rw [tapeAt_transitionCfg_output] at hnext
    simpa only [hworkOutput] using hnext
  have houtputHeads :
      HeadsInWindow instanceData.blockLength centers
        (updateNamedTape
          (updateWorkTapes
            (updateNamedTape cfg (TapeIndex.input workTapeCount)
              none inputDirection)
            workWrites workDirections (List.finRange workTapeCount))
          (TapeIndex.output workTapeCount)
          (some outputWrite) outputDirection) :=
    headsInWindow_updateNamedTape instanceData.blockLength centers
      (updateWorkTapes
        (updateNamedTape cfg (TapeIndex.input workTapeCount)
          none inputDirection)
        workWrites workDirections (List.finRange workTapeCount))
      (TapeIndex.output workTapeCount) (some outputWrite)
      outputDirection hworkHeads houtputAction
  obtain ⟨afterOutput, houtputRun, houtputLive⟩ :=
    liveState_updateTape order regs instanceData nodeTape slot interval
      logicalBank code centers suffix initial afterWork
      (updateWorkTapes
        (updateNamedTape cfg (TapeIndex.input workTapeCount)
          none inputDirection)
        workWrites workDirections (List.finRange workTapeCount))
      (TapeIndex.output workTapeCount) (some outputWrite)
      outputDirection hfits hguess hinterval hcenters hworkLive
      hworkHeads houtputHeads
  obtain ⟨final, hstateRun, hstateWord, hstateBankOne,
      hstateRangeOne, hstateOutside⟩ :=
    replaceState_runs tm order nextState regs afterOutput
      (afterOutput (bankRegisters regs).word) rfl
  refine ⟨final, ?_, ?_⟩
  · have htailRun :
        Runs
          (Cmd.seqList
            [updateTape tm controller (TapeIndex.output workTapeCount)
                (some outputWrite) outputDirection regs,
              replaceState tm order nextState regs])
          afterWork final := by
      exact Runs.seq houtputRun hstateRun
    have hworkRun :=
      hworkPrefix
        (Cmd.seqList
          [updateTape tm controller (TapeIndex.output workTapeCount)
              (some outputWrite) outputDirection regs,
            replaceState tm order nextState regs])
        final htailRun
    have hcomposed := Runs.seq hinputRun hworkRun
    simp only [transitionAction, hdelta]
    rw [seqList_append_eq_seqThen
      ([updateTape tm controller (TapeIndex.input workTapeCount)
          none inputDirection regs] ++
        (List.finRange workTapeCount).map fun tape =>
          updateTape tm controller (TapeIndex.work tape)
            (some (workWrites tape)) (workDirections tape) regs)
      [updateTape tm controller (TapeIndex.output workTapeCount)
          (some outputWrite) outputDirection regs,
        replaceState tm order nextState regs]
      (by simp)]
    simpa only [seqThen] using hcomposed
  · refine
      { represents := ?_
        computation :=
          computationContext_of_runs regs instanceData nodeTape slot
            interval logicalBank
            (replaceState_writesWithin tm order nextState regs)
            hstateRun houtputLive.computation
        guess_eq :=
          (controller_guess_eq_of_runs regs
            (replaceState_writesWithin tm order nextState regs)
            hstateRun).trans houtputLive.guess_eq
        rangeOne_eq := hstateRangeOne
        accumulator_eq := ?_
        count_eq := ?_ }
    · rw [hstateWord]
      simpa only [transitionCfg, transitionTapes] using
        setState_represents tm order instanceData.blockLength centers
          (updateNamedTape
            (updateWorkTapes
              (updateNamedTape cfg (TapeIndex.input workTapeCount)
                none inputDirection)
              workWrites workDirections (List.finRange workTapeCount))
            (TapeIndex.output workTapeCount)
            (some outputWrite) outputDirection)
          nextState suffix (afterOutput (bankRegisters regs).word)
          houtputLive.represents
    · calc
        final (CombineValue.rangeRegisters regs).accumulator =
            afterOutput
              (CombineValue.rangeRegisters regs).accumulator :=
          hstateOutside _
            (fixed_index_not_mem_bank regs 18 (by
              intro bankSlot
              fin_cases bankSlot <;> decide))
        _ = initial (CombineValue.rangeRegisters regs).accumulator :=
          houtputLive.accumulator_eq
    · calc
        final (CombineValue.rangeRegisters regs).count =
            afterOutput (CombineValue.rangeRegisters regs).count :=
          hstateOutside _
            (fixed_index_not_mem_bank regs 10 (by
              intro bankSlot
              fin_cases bankSlot <;> decide))
        _ = initial (CombineValue.rangeRegisters regs).count :=
          houtputLive.count_eq

private theorem liveState_of_headScanOutside
    {tm : TM workTapeCount}
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (nodeTape : TapeIndex workTapeCount)
    (slot : NeighborhoodGraph.Slot)
    (interval : ℕ)
    (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (code :
      Fin
        (3 ^
          NeighborhoodGraph.Guess.Enumeration.movementCount
            workTapeCount instanceData.horizon))
    (centers : TapeIndex workTapeCount → ℕ)
    (suffix : ℕ)
    (initial : Store)
    (cfg : Cfg workTapeCount tm.Q)
    (before after : Store)
    (hlive :
      LiveState order regs instanceData nodeTape slot interval
        logicalBank code centers suffix initial cfg before)
    (hword :
      after (bankRegisters regs).word =
        before (bankRegisters regs).word)
    (hrangeOne :
      after (CombineValue.rangeRegisters regs).one = 1)
    (houtside :
      ∀ address, address ∉ PackedLocalHeadScan.footprint regs →
        after address = before address) :
    LiveState order regs instanceData nodeTape slot interval
      logicalBank code centers suffix initial cfg after := by
  exact
    { represents := by
        simpa only [hword] using hlive.represents
      computation :=
        computationContext_of_headScanOutside regs instanceData nodeTape
          slot interval logicalBank before after houtside
          hlive.computation
      guess_eq := by
        calc
          after controller.guess = before controller.guess :=
            houtside _ (controller_guess_not_mem_headScan controller regs)
          _ = code.val := hlive.guess_eq
      rangeOne_eq := hrangeOne
      accumulator_eq := by
        calc
          after (CombineValue.rangeRegisters regs).accumulator =
              before (CombineValue.rangeRegisters regs).accumulator :=
            houtside _
              (fixed_index_not_mem_headScan regs 18 (by
                intro bankSlot
                fin_cases bankSlot <;> decide) (by decide))
          _ = initial (CombineValue.rangeRegisters regs).accumulator :=
            hlive.accumulator_eq
      count_eq := by
        calc
          after (CombineValue.rangeRegisters regs).count =
              before (CombineValue.rangeRegisters regs).count :=
            houtside _
              (fixed_index_not_mem_headScan regs 10 (by
                intro bankSlot
                fin_cases bankSlot <;> decide) (by decide))
          _ = initial (CombineValue.rangeRegisters regs).count :=
            hlive.count_eq }

private theorem dispatchTransition_runs
    {tm : TM workTapeCount}
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (nodeTape : TapeIndex workTapeCount)
    (slot : NeighborhoodGraph.Slot)
    (interval : ℕ)
    (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (code :
      Fin
        (3 ^
          NeighborhoodGraph.Guess.Enumeration.movementCount
            workTapeCount instanceData.horizon))
    (centers : TapeIndex workTapeCount → ℕ)
    (suffix : ℕ)
    (initial : Store)
    (cfg : Cfg workTapeCount tm.Q)
    (store : Store)
    (hfits :
      ∀ digit ∈
          FrameCodec.nodeDigits
            (show
              NeighborhoodEvaluator.QueryNode
                workTapeCount instanceData.horizon
              from .graph (.computation nodeTape slot interval)),
        digit < Representation.digitBase instanceData)
    (hguess :
      instanceData.guess =
        NeighborhoodGraph.Guess.Enumeration.candidateGuess code)
    (hinterval : interval ≤ instanceData.horizon)
    (hcenters :
      centers =
        NeighborhoodGraph.Guess.Consistency.guessedCenters
          instanceData.guess interval)
    (hlive :
      LiveState order regs instanceData nodeTape slot interval
        logicalBank code centers suffix initial cfg store)
    (hheads :
      HeadsInWindow instanceData.blockLength centers cfg)
    (hnextHeads :
      HeadsInWindow instanceData.blockLength centers
        ((tm.step cfg).getD cfg)) :
    ∃ final,
      Runs
        (dispatchTransition tm order controller regs cfg.state)
        store final ∧
      LiveState order regs instanceData nodeTape slot interval
        logicalBank code centers suffix initial
        ((tm.step cfg).getD cfg) final := by
  by_cases hhalt : cfg.state = tm.qhalt
  · refine ⟨store, ?_, ?_⟩
    · simpa [dispatchTransition, hhalt] using Runs.skip store
    · simpa [TM.step, hhalt] using hlive
  · obtain ⟨hinputLower, hinputUpper⟩ :=
      hheads (TapeIndex.input workTapeCount)
    obtain ⟨afterInputScan, hinputDispatch, hinputWord,
        hinputRangeOne, hinputOutside⟩ :=
      scanAndDispatch_prepare tm order instanceData.blockLength
        instanceData.positive centers cfg
        (TapeIndex.input workTapeCount) suffix
        (store (bankRegisters regs).word) regs
        (fun inputSymbol =>
          dispatchWorkHeads tm regs
            (fun workSymbols =>
              scanAndDispatch tm (TapeIndex.output workTapeCount) regs
                (transitionAction tm order controller regs cfg.state
                  inputSymbol workSymbols))
            (List.finRange workTapeCount) (fun _ => Γ.blank))
        store hlive.computation.parameters.blockLength_eq rfl
        hlive.represents hlive.rangeOne_eq hinputLower hinputUpper
    have hinputLive :
        LiveState order regs instanceData nodeTape slot interval
          logicalBank code centers suffix initial cfg afterInputScan :=
      liveState_of_headScanOutside order regs instanceData nodeTape slot
        interval logicalBank code centers suffix initial cfg store
        afterInputScan hlive hinputWord hinputRangeOne hinputOutside
    obtain ⟨afterWorkScan, hworkDispatch, hworkWord,
        hworkRangeOne, hworkOutside⟩ :=
      dispatchWorkHeads_prepare tm order instanceData.blockLength
        instanceData.positive centers cfg suffix
        (store (bankRegisters regs).word) regs
        (fun workSymbols =>
          scanAndDispatch tm (TapeIndex.output workTapeCount) regs
            (transitionAction tm order controller regs cfg.state
              cfg.input.read workSymbols))
        hlive.represents hheads (List.finRange workTapeCount)
        (fun _ => Γ.blank) afterInputScan
        hinputLive.computation.parameters.blockLength_eq hinputWord
        hinputRangeOne
    have hworkLive :
        LiveState order regs instanceData nodeTape slot interval
          logicalBank code centers suffix initial cfg afterWorkScan :=
      liveState_of_headScanOutside order regs instanceData nodeTape slot
        interval logicalBank code centers suffix initial cfg
        afterInputScan afterWorkScan hinputLive
        (hworkWord.trans hinputWord.symm) hworkRangeOne hworkOutside
    let gatheredWork :=
      collectWorkHeads cfg (List.finRange workTapeCount)
        (fun _ => Γ.blank)
    obtain ⟨houtputLower, houtputUpper⟩ :=
      hheads (TapeIndex.output workTapeCount)
    obtain ⟨afterOutputScan, houtputDispatch, houtputWord,
        houtputRangeOne, houtputOutside⟩ :=
      scanAndDispatch_prepare tm order instanceData.blockLength
        instanceData.positive centers cfg
        (TapeIndex.output workTapeCount) suffix
        (store (bankRegisters regs).word) regs
        (transitionAction tm order controller regs cfg.state
          cfg.input.read gatheredWork)
        afterWorkScan hworkLive.computation.parameters.blockLength_eq
        hworkWord hlive.represents hworkRangeOne houtputLower
        houtputUpper
    have houtputLive :
        LiveState order regs instanceData nodeTape slot interval
          logicalBank code centers suffix initial cfg afterOutputScan :=
      liveState_of_headScanOutside order regs instanceData nodeTape slot
        interval logicalBank code centers suffix initial cfg
        afterWorkScan afterOutputScan hworkLive
        (houtputWord.trans hworkWord.symm) houtputRangeOne
        houtputOutside
    generalize hdelta :
        tm.δ cfg.state cfg.input.read gatheredWork cfg.output.read =
          transition
    rcases transition with
      ⟨nextState, workWrites, outputWrite, inputDirection,
        workDirections, outputDirection⟩
    have hdeltaActual :
        tm.δ cfg.state cfg.input.read
            (fun index => (cfg.work index).read) cfg.output.read =
          (nextState, workWrites, outputWrite, inputDirection,
            workDirections, outputDirection) := by
      simpa only [gatheredWork, collectWorkHeads_finRange] using hdelta
    have htransitionEq :
        transitionCfg cfg nextState workWrites outputWrite
            inputDirection workDirections outputDirection =
          (tm.step cfg).getD cfg :=
      transitionCfg_eq_step_getD tm cfg nextState workWrites
        outputWrite inputDirection workDirections outputDirection
        hhalt hdeltaActual
    have htransitionHeads :
        HeadsInWindow instanceData.blockLength centers
          (transitionCfg cfg nextState workWrites outputWrite
            inputDirection workDirections outputDirection) := by
      rw [htransitionEq]
      exact hnextHeads
    obtain ⟨final, htransitionRun, hfinalLiveRaw⟩ :=
      transitionAction_runs order regs instanceData nodeTape slot
        interval logicalBank code centers suffix initial cfg
        afterOutputScan cfg.state nextState cfg.input.read gatheredWork
        cfg.output.read workWrites outputWrite inputDirection
        workDirections outputDirection hdelta hfits hguess hinterval
        hcenters houtputLive hheads htransitionHeads
    have hfinalLive :
        LiveState order regs instanceData nodeTape slot interval
          logicalBank code centers suffix initial
          ((tm.step cfg).getD cfg) final := by
      rw [← htransitionEq]
      exact hfinalLiveRaw
    have houtputRun :
        Runs
          (scanAndDispatch tm (TapeIndex.output workTapeCount) regs
            (transitionAction tm order controller regs cfg.state
              cfg.input.read gatheredWork))
          afterWorkScan final := by
      apply houtputDispatch
      simpa only [tapeAt_output, Tape.read] using htransitionRun
    have hworkRun :
        Runs
          (dispatchWorkHeads tm regs
            (fun workSymbols =>
              scanAndDispatch tm (TapeIndex.output workTapeCount) regs
                (transitionAction tm order controller regs cfg.state
                  cfg.input.read workSymbols))
            (List.finRange workTapeCount) (fun _ => Γ.blank))
          afterInputScan final := by
      apply hworkDispatch
      simpa only [gatheredWork] using houtputRun
    have hinputRun :
        Runs
          (scanAndDispatch tm (TapeIndex.input workTapeCount) regs
            (fun inputSymbol =>
              dispatchWorkHeads tm regs
                (fun workSymbols =>
                  scanAndDispatch tm
                    (TapeIndex.output workTapeCount) regs
                    (transitionAction tm order controller regs cfg.state
                      inputSymbol workSymbols))
                (List.finRange workTapeCount) (fun _ => Γ.blank)))
          store final := by
      apply hinputDispatch
      simpa only [tapeAt_input, Tape.read] using hworkRun
    refine ⟨final, ?_, hfinalLive⟩
    simpa [dispatchTransition, hhalt] using hinputRun

private theorem equalImmediate_runs
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store)
    (constant : ℕ) :
    ∃ final,
      Runs
        (equalImmediate regs (bankRegisters regs).result
          (bankRegisters regs).buffer constant)
        store final ∧
      (final (bankRegisters regs).buffer = 0 ↔
        store (bankRegisters regs).result = constant) ∧
      final (bankRegisters regs).result =
        store (bankRegisters regs).result ∧
      final (bankRegisters regs).word =
        store (bankRegisters regs).word ∧
      final (bankRegisters regs).one =
        store (bankRegisters regs).one ∧
      final (CombineValue.rangeRegisters regs).one =
        store (CombineValue.rangeRegisters regs).one ∧
      ∀ address, address ∉ (bankRegisters regs).footprint →
        final address = store address := by
  let valueSet :=
    (Basic.imm (bankRegisters regs).value constant).exec store
  let leftSet :=
    (Basic.sub (bankRegisters regs).test
      (bankRegisters regs).result
      (bankRegisters regs).value).exec valueSet
  let rightSet :=
    (Basic.sub (bankRegisters regs).quotient
      (bankRegisters regs).value
      (bankRegisters regs).result).exec leftSet
  let final :=
    (Basic.add (bankRegisters regs).buffer
      (bankRegisters regs).test
      (bankRegisters regs).quotient).exec rightSet
  have hvalueRun :
      Runs
        (.basic (.imm (bankRegisters regs).value constant))
        store valueSet :=
    Runs.basic _ _
  have hleftRun :
      Runs
        (.basic
          (.sub (bankRegisters regs).test
            (bankRegisters regs).result
            (bankRegisters regs).value))
        valueSet leftSet :=
    Runs.basic _ _
  have hrightRun :
      Runs
        (.basic
          (.sub (bankRegisters regs).quotient
            (bankRegisters regs).value
            (bankRegisters regs).result))
        leftSet rightSet :=
    Runs.basic _ _
  have hfinalRun :
      Runs
        (.basic
          (.add (bankRegisters regs).buffer
            (bankRegisters regs).test
            (bankRegisters regs).quotient))
        rightSet final :=
    Runs.basic _ _
  have hbuffer :
      final (bankRegisters regs).buffer =
        (store (bankRegisters regs).result - constant) +
          (constant - store (bankRegisters regs).result) := by
    simp [final, rightSet, leftSet, valueSet, Basic.exec,
      (bankRegisters regs).index_ne]
  refine ⟨final, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [equalImmediate, Cmd.seqList] using
      Runs.seq hvalueRun
        (Runs.seq hleftRun (Runs.seq hrightRun hfinalRun))
  · rw [hbuffer]
    omega
  · simp [final, rightSet, leftSet, valueSet, Basic.exec,
      (bankRegisters regs).index_ne]
  · simp [final, rightSet, leftSet, valueSet, Basic.exec,
      (bankRegisters regs).index_ne]
  · simp [final, rightSet, leftSet, valueSet, Basic.exec,
      (bankRegisters regs).index_ne]
  · simp [final, rightSet, leftSet, valueSet, Basic.exec,
      CombineValue.rangeRegisters, bankRegisters,
      PackedLocalHeadScan.bankRegisters, PackedLocalHeadScan.bankMap,
      regs.injective.eq_iff]
  · intro address haddress
    have outsideNe (bankSlot : Fin 12) :
        address ≠ (bankRegisters regs).index bankSlot := by
      intro heq
      apply haddress
      rw [heq]
      exact (bankRegisters regs).index_mem_footprint bankSlot
    simp [final, rightSet, leftSet, valueSet, Basic.exec,
      outsideNe]

private theorem liveState_of_bankOutside
    {tm : TM workTapeCount}
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (nodeTape : TapeIndex workTapeCount)
    (slot : NeighborhoodGraph.Slot)
    (interval : ℕ)
    (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (code :
      Fin
        (3 ^
          NeighborhoodGraph.Guess.Enumeration.movementCount
            workTapeCount instanceData.horizon))
    (centers : TapeIndex workTapeCount → ℕ)
    (suffix : ℕ)
    (initial : Store)
    (cfg : Cfg workTapeCount tm.Q)
    (before after : Store)
    (hlive :
      LiveState order regs instanceData nodeTape slot interval
        logicalBank code centers suffix initial cfg before)
    (hword :
      after (bankRegisters regs).word =
        before (bankRegisters regs).word)
    (hrangeOne :
      after (CombineValue.rangeRegisters regs).one = 1)
    (houtside :
      ∀ address, address ∉ (bankRegisters regs).footprint →
        after address = before address) :
    LiveState order regs instanceData nodeTape slot interval
      logicalBank code centers suffix initial cfg after := by
  apply liveState_of_headScanOutside order regs instanceData nodeTape
    slot interval logicalBank code centers suffix initial cfg before
    after hlive hword hrangeOne
  intro address haddress
  apply houtside address
  intro hbank
  apply haddress
  exact Finset.mem_union.mpr (Or.inl hbank)

private theorem stateCode_eq_iff
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (first second : tm.Q) :
    CompactValueCodeSemantics.stateCode order first =
        CompactValueCodeSemantics.stateCode order second ↔
      first = second := by
  constructor
  · intro heq
    apply order.state.injective
    apply Fin.ext
    exact heq
  · intro heq
    subst second
    rfl

private theorem dispatchStates_runs
    {tm : TM workTapeCount}
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (nodeTape : TapeIndex workTapeCount)
    (slot : NeighborhoodGraph.Slot)
    (interval : ℕ)
    (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (code :
      Fin
        (3 ^
          NeighborhoodGraph.Guess.Enumeration.movementCount
            workTapeCount instanceData.horizon))
    (centers : TapeIndex workTapeCount → ℕ)
    (suffix : ℕ)
    (initial : Store)
    (cfg : Cfg workTapeCount tm.Q)
    (hfits :
      ∀ digit ∈
          FrameCodec.nodeDigits
            (show
              NeighborhoodEvaluator.QueryNode
                workTapeCount instanceData.horizon
              from .graph (.computation nodeTape slot interval)),
        digit < Representation.digitBase instanceData)
    (hguess :
      instanceData.guess =
        NeighborhoodGraph.Guess.Enumeration.candidateGuess code)
    (hinterval : interval ≤ instanceData.horizon)
    (hcenters :
      centers =
        NeighborhoodGraph.Guess.Consistency.guessedCenters
          instanceData.guess interval)
    (hheads :
      HeadsInWindow instanceData.blockLength centers cfg)
    (hnextHeads :
      HeadsInWindow instanceData.blockLength centers
        ((tm.step cfg).getD cfg)) :
    ∀ (sourceStates : List tm.Q) (store : Store),
      cfg.state ∈ sourceStates →
      LiveState order regs instanceData nodeTape slot interval
        logicalBank code centers suffix initial cfg store →
      store (bankRegisters regs).result =
        CompactValueCodeSemantics.stateCode order cfg.state →
      ∃ final,
        Runs
          (dispatchStates tm order controller regs sourceStates)
          store final ∧
        LiveState order regs instanceData nodeTape slot interval
          logicalBank code centers suffix initial
          ((tm.step cfg).getD cfg) final := by
  intro sourceStates
  induction sourceStates with
  | nil =>
      intro store hmem _hlive _hresult
      simp at hmem
  | cons state sourceStates ih =>
      intro store hmem hlive hresult
      obtain ⟨afterEqual, hequalRun, hzeroIff, hequalResult,
          hequalWord, _hequalBankOne, hequalRangeOneEq,
          hequalOutside⟩ :=
        equalImmediate_runs regs store
          (CompactValueCodeSemantics.stateCode order state)
      have hequalRangeOne :
          afterEqual (CombineValue.rangeRegisters regs).one = 1 := by
        exact hequalRangeOneEq.trans hlive.rangeOne_eq
      have hequalLive :
          LiveState order regs instanceData nodeTape slot interval
            logicalBank code centers suffix initial cfg afterEqual :=
        liveState_of_bankOutside order regs instanceData nodeTape slot
          interval logicalBank code centers suffix initial cfg store
          afterEqual hlive hequalWord hequalRangeOne hequalOutside
      by_cases hstate : state = cfg.state
      · subst state
        have hzero :
            afterEqual (bankRegisters regs).buffer = 0 :=
          hzeroIff.mpr hresult
        obtain ⟨final, htransitionRun, hfinalLive⟩ :=
          dispatchTransition_runs order regs instanceData nodeTape slot
            interval logicalBank code centers suffix initial cfg
            afterEqual hfits hguess hinterval hcenters hequalLive
            hheads hnextHeads
        refine ⟨final, ?_, hfinalLive⟩
        simpa [dispatchStates] using
          Runs.seq hequalRun
            (Runs.ifZero hzero htransitionRun)
      · have htailMem : cfg.state ∈ sourceStates := by
          rcases List.mem_cons.mp hmem with heq | htail
          · exact False.elim (hstate heq.symm)
          · exact htail
        have hnonzero :
            afterEqual (bankRegisters regs).buffer ≠ 0 := by
          intro hzero
          have hcodes :
              CompactValueCodeSemantics.stateCode order cfg.state =
                CompactValueCodeSemantics.stateCode order state := by
            rw [← hresult]
            exact hzeroIff.mp hzero
          exact hstate (stateCode_eq_iff order cfg.state state
            |>.mp hcodes).symm
        obtain ⟨final, htailRun, hfinalLive⟩ :=
          ih afterEqual htailMem hequalLive
            (hequalResult.trans hresult)
        refine ⟨final, ?_, hfinalLive⟩
        simpa [dispatchStates] using
          Runs.seq hequalRun
            (Runs.ifNonzero hnonzero htailRun)

private theorem state_mem_states
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (state : tm.Q) :
    state ∈ states tm order := by
  unfold states
  rw [List.mem_map]
  exact
    ⟨order.state state, by simp,
      order.state.symm_apply_apply state⟩

theorem step_runs_internal
    {tm : TM workTapeCount}
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (nodeTape : TapeIndex workTapeCount)
    (slot : NeighborhoodGraph.Slot)
    (interval : ℕ)
    (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (code :
      Fin
        (3 ^
          NeighborhoodGraph.Guess.Enumeration.movementCount
            workTapeCount instanceData.horizon))
    (centers : TapeIndex workTapeCount → ℕ)
    (cfg : Cfg workTapeCount tm.Q)
    (suffix word : ℕ)
    (store : Store)
    (hfits :
      ∀ digit ∈
          FrameCodec.nodeDigits
            (show
              NeighborhoodEvaluator.QueryNode
                workTapeCount instanceData.horizon
              from .graph (.computation nodeTape slot interval)),
        digit < Representation.digitBase instanceData)
    (hcontext :
      CombineTerm.ComputationContext regs instanceData nodeTape slot
        interval logicalBank store)
    (hstoreGuess : store controller.guess = code.val)
    (hguess :
      instanceData.guess =
        NeighborhoodGraph.Guess.Enumeration.candidateGuess code)
    (hinterval : interval ≤ instanceData.horizon)
    (hcenters :
      centers =
        NeighborhoodGraph.Guess.Consistency.guessedCenters
          instanceData.guess interval)
    (hrep :
      PackedLocalRepresentation.Represents tm order
        instanceData.blockLength centers cfg suffix word)
    (hheads :
      HeadsInWindow instanceData.blockLength centers cfg)
    (hnextHeads :
      HeadsInWindow instanceData.blockLength centers
        ((tm.step cfg).getD cfg))
    (hword : store (bankRegisters regs).word = word)
    (hrangeOne :
      store (CombineValue.rangeRegisters regs).one = 1) :
    ∃ final,
      Runs (step tm order controller regs) store final ∧
      Post tm order instanceData.blockLength centers
        ((tm.step cfg).getD cfg) suffix regs store final := by
  have hstartLive :
      LiveState order regs instanceData nodeTape slot interval
        logicalBank code centers suffix store cfg store :=
    { represents := by
        simpa only [hword] using hrep
      computation := hcontext
      guess_eq := hstoreGuess
      rangeOne_eq := hrangeOne
      accumulator_eq := rfl
      count_eq := rfl }
  obtain ⟨afterRead, hreadRun, hreadWord, hreadResult,
      _hreadBankOne, hreadRangeOne, hreadOutside⟩ :=
    readState_runs tm order instanceData.blockLength centers cfg suffix
      word regs store hword hrep
  have hreadLive :
      LiveState order regs instanceData nodeTape slot interval
        logicalBank code centers suffix store cfg afterRead :=
    liveState_of_bankOutside order regs instanceData nodeTape slot
      interval logicalBank code centers suffix store cfg store
      afterRead hstartLive (hreadWord.trans hword.symm)
      hreadRangeOne hreadOutside
  obtain ⟨final, hdispatchRun, hfinalLive⟩ :=
    dispatchStates_runs order regs instanceData nodeTape slot interval
      logicalBank code centers suffix store cfg hfits hguess hinterval
      hcenters hheads hnextHeads (states tm order) afterRead
      (state_mem_states tm order cfg.state) hreadLive hreadResult
  have hfullRun :
      Runs (step tm order controller regs) store final := by
    simpa [step] using Runs.seq hreadRun hdispatchRun
  have houtside :
      ∀ address, address ∉ footprint regs →
        final address = store address := by
    intro address haddress
    exact Footprint.runs_eq_outside
      (step_writesWithin_internal tm order controller regs)
      hfullRun haddress
  refine ⟨final, hfullRun, ?_⟩
  exact
    { represents := hfinalLive.represents
      context :=
        { assignment_eq := houtside _
            (by
              simpa [CombineValue.rangeRegisters] using
                fixed_index_not_mem_footprint regs 21 (by
                  intro writeSlot
                  fin_cases writeSlot <;> decide))
          accumulator_eq := hfinalLive.accumulator_eq
          count_eq := hfinalLive.count_eq
          one_eq := hfinalLive.rangeOne_eq.trans hrangeOne.symm
          catalyticWord_eq := houtside _
            (fixed_index_not_mem_footprint regs 33 (by
              intro writeSlot
              fin_cases writeSlot <;> decide))
          abi := preservesABI_of_runs regs
            (step_writesWithin_internal tm order controller regs)
            hfullRun }
      eq_outside := houtside }

end Internal
end PackedLocalStep
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
