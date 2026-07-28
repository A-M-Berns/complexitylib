/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.PackedLocalInitialization.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.AssignmentPayloadBit
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.CombineSafeCenter
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.CombineTerm
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.PackedLocalConfiguration
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.PackedLocalRepresentation
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodProgram

/-!
# Fixed-source packed local initialization -- proofs
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace PackedLocalInitialization
namespace Internal

open RAM Structured
open NeighborhoodGraph
open TreeEval CookMertz

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
      exact ⟨ihFirst hwrites.1, ihSecond hwrites.2⟩
  | ifZero test onZero onNonzero ihZero ihNonzero =>
      exact ⟨ihZero hwrites.1, ihNonzero hwrites.2⟩
  | whileNonzero test body ih =>
      exact ih hwrites

private theorem write_slot_mem
    (regs : NeighborhoodTrial.Registers controller)
    (slot : Fin 17) :
    regs.index (writeMap slot) ∈
      footprint regs :=
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
  fin_cases slot <;>
    simp_all
  all_goals
    first
    | exact write_slot_mem regs 0
    | exact write_slot_mem regs 1
    | exact write_slot_mem regs 2
    | exact write_slot_mem regs 3
    | exact write_slot_mem regs 4
    | exact write_slot_mem regs 5
    | exact write_slot_mem regs 6
    | exact write_slot_mem regs 7
    | exact write_slot_mem regs 8
    | exact write_slot_mem regs 9
    | exact write_slot_mem regs 10
    | exact write_slot_mem regs 11
    | exact write_slot_mem regs 12
    | exact write_slot_mem regs 13
    | exact write_slot_mem regs 14
    | exact write_slot_mem regs 15
    | exact write_slot_mem regs 16

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

private theorem fixed_index_not_mem_footprint
    (regs : NeighborhoodTrial.Registers controller)
    (slot : Fin 34)
    (hslot :
      ∀ writeSlot, slot ≠ writeMap writeSlot) :
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
    (hslot :
      ∀ scratch, slot ≠ CombineSafeCenter.scratchMap scratch) :
    regs.index slot ∉ CombineSafeCenter.footprint regs := by
  intro hmember
  simp only [CombineSafeCenter.footprint, Finset.mem_image,
    Finset.mem_univ, true_and] at hmember
  obtain ⟨scratch, hscratch⟩ := hmember
  exact hslot scratch (regs.injective hscratch.symm)

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
    { fuel_eq := fixed 22 (by decide)
      nodeCode_eq := fixed 23 (by decide)
      scalar_eq := fixed 25 (by decide)
      out_eq := fixed 26 (by decide)
      phaseCode_eq := fixed 27 (by decide)
      active_eq := fixed 28 (by decide)
      blockLength_eq := fixed 2 (by decide)
      horizon_eq := fixed 3 (by decide)
      chunkCount_eq := fixed 7 (by decide)
      chunkRadix_eq := fixed 8 (by decide)
      frameRadix_eq := fixed 13 (by decide)
      bankRadix_eq := fixed 14 (by decide)
      bankDigitCount_eq := fixed 15 (by decide)
      modulusPred_eq := fixed 16 (by decide)
      modulus_eq := fixed 24 (by decide) }

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
    (fixed_index_not_mem_footprint regs 33 (by decide))

private theorem control_footprint_subset
    (regs : NeighborhoodTrial.Registers controller) :
    ControlDecode.scratchFootprint regs ⊆ footprint regs := by
  intro address haddress
  simp only [ControlDecode.scratchFootprint, Finset.mem_image,
    Finset.mem_univ, true_and] at haddress
  obtain ⟨slot, rfl⟩ := haddress
  apply physical_slot_mem regs
  fin_cases slot <;>
    simp [ControlDecode.scratchMap]

private theorem center_footprint_subset
    (regs : NeighborhoodTrial.Registers controller) :
    CombineSafeCenter.footprint regs ⊆ footprint regs := by
  intro address haddress
  simp only [CombineSafeCenter.footprint, Finset.mem_image,
    Finset.mem_univ, true_and] at haddress
  obtain ⟨slot, rfl⟩ := haddress
  apply physical_slot_mem regs
  fin_cases slot <;>
    simp [CombineSafeCenter.scratchMap]

private theorem assignmentPayload_footprint_subset
    (regs : NeighborhoodTrial.Registers controller) :
    AssignmentPayloadBit.writeFootprint regs ⊆ footprint regs := by
  have hnotRemaining :
      regs.index 21 ∉
        AssignmentPayloadBit.writeFootprint regs := by
    simpa [CombineValue.rangeRegisters] using
      AssignmentPayloadBit.remaining_not_mem_writeFootprint regs
  have hnotCatalytic :
      regs.index 33 ∉
        AssignmentPayloadBit.writeFootprint regs := by
    simpa [NeighborhoodTrial.Registers.layout] using
      AssignmentPayloadBit.catalyticBank_not_mem_writeFootprint regs
  intro address haddress
  have hcoarse :=
    AssignmentPayloadBit.writeFootprint_subset_combineScratch
      regs haddress
  simp only [CombineValue.combineScratchFootprint,
    Finset.mem_image, Finset.mem_univ, true_and] at hcoarse
  obtain ⟨slot, rfl⟩ := hcoarse
  by_cases hremaining : slot.val = 13
  · have hmap :
        CombineValue.combineScratchMap slot = 21 := by
      fin_cases slot <;>
        simp_all [CombineValue.combineScratchMap]
    rw [hmap] at haddress
    exact (hnotRemaining haddress).elim
  · by_cases hcatalytic : slot.val = 18
    · have hmap :
          CombineValue.combineScratchMap slot = 33 := by
        fin_cases slot <;>
          simp_all [CombineValue.combineScratchMap]
      rw [hmap] at haddress
      exact (hnotCatalytic haddress).elim
    · apply physical_slot_mem regs
      fin_cases slot <;>
        simp_all [CombineValue.combineScratchMap]

/-- Initializer writes after center derivation exclude the live outer
accumulator and immutable assignment count. -/
private def emissionFootprint
    (regs : NeighborhoodTrial.Registers controller) : Finset ℕ :=
  ((footprint regs).erase
    (CombineValue.rangeRegisters regs).accumulator).erase
      (CombineValue.rangeRegisters regs).count

private theorem emissionFootprint_subset
    (regs : NeighborhoodTrial.Registers controller) :
    emissionFootprint regs ⊆ footprint regs := by
  intro address haddress
  simp only [emissionFootprint, Finset.mem_erase] at haddress
  exact haddress.2.2

private theorem not_mem_emissionFootprint
    (regs : NeighborhoodTrial.Registers controller)
    {address : ℕ}
    (haddress : address ∉ footprint regs) :
    address ∉ emissionFootprint regs :=
  fun hmember => haddress (emissionFootprint_subset regs hmember)

private theorem mem_emissionFootprint
    (regs : NeighborhoodTrial.Registers controller)
    {address : ℕ}
    (haddress : address ∈ footprint regs)
    (haccumulator :
      address ≠ (CombineValue.rangeRegisters regs).accumulator)
    (hcount :
      address ≠ (CombineValue.rangeRegisters regs).count) :
    address ∈ emissionFootprint regs := by
  simp only [emissionFootprint, Finset.mem_erase]
  exact ⟨hcount, haccumulator, haddress⟩

private theorem physical_slot_mem_emission
    (regs : NeighborhoodTrial.Registers controller)
    {slot : Fin 34} :
      slot.val = 0 ∨ slot.val = 1 ∨ slot.val = 4 ∨
      slot.val = 5 ∨ slot.val = 6 ∨ slot.val = 9 ∨
      slot.val = 11 ∨ slot.val = 12 ∨ slot.val = 17 ∨
      slot.val = 19 ∨ slot.val = 20 ∨ slot.val = 29 ∨
      slot.val = 30 ∨ slot.val = 31 ∨ slot.val = 32 →
        regs.index slot ∈ emissionFootprint regs := by
  intro hslot
  apply mem_emissionFootprint regs
  · apply physical_slot_mem regs
    rcases hslot with h | h | h | h | h | h | h | h |
      h | h | h | h | h | h | h
    all_goals simp_all
  · intro heq
    have hslotEq := regs.injective heq
    have hval :
        slot.val = (18 : Fin 34).val :=
      congrArg Fin.val hslotEq
    rcases hslot with h | h | h | h | h | h | h | h |
      h | h | h | h | h | h | h <;> omega
  · intro heq
    have hslotEq := regs.injective heq
    have hval :
        slot.val = (10 : Fin 34).val :=
      congrArg Fin.val hslotEq
    rcases hslot with h | h | h | h | h | h | h | h |
      h | h | h | h | h | h | h <;> omega

private theorem bank_footprint_subset_emission
    (regs : NeighborhoodTrial.Registers controller) :
    (bankRegisters regs).footprint ⊆ emissionFootprint regs := by
  intro address haddress
  simp only [NeighborhoodProgram.BankRegisters.footprint,
    Finset.mem_image, Finset.mem_univ, true_and] at haddress
  obtain ⟨slot, rfl⟩ := haddress
  apply physical_slot_mem_emission regs
  fin_cases slot <;>
    simp [PackedLocalHeadScan.bankMap]

private theorem assignmentPayload_footprint_subset_emission
    (regs : NeighborhoodTrial.Registers controller) :
    AssignmentPayloadBit.writeFootprint regs ⊆
      emissionFootprint regs := by
  intro address haddress
  apply mem_emissionFootprint regs
  · exact assignmentPayload_footprint_subset regs haddress
  · intro heq
    apply
      (AssignmentPayloadBit.accumulator_not_mem_writeFootprint
        regs)
    simpa [heq] using haddress
  · intro heq
    apply
      (AssignmentPayloadBit.count_not_mem_writeFootprint regs)
    simpa [heq] using haddress

private theorem copy_emission_writesWithin
    (regs : NeighborhoodTrial.Registers controller)
    (destination source : ℕ)
    (hdestination : destination ∈ emissionFootprint regs) :
    Footprint.CmdWritesWithin (emissionFootprint regs)
      (copy destination source) :=
  ⟨hdestination, hdestination⟩

private theorem copy_writesWithin
    (regs : NeighborhoodTrial.Registers controller)
    (destination source : ℕ)
    (hdestination : destination ∈ footprint regs) :
    Footprint.CmdWritesWithin (footprint regs)
      (copy destination source) :=
  ⟨hdestination, hdestination⟩

private theorem seqList_writesWithin
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
    Footprint.CmdWritesWithin (emissionFootprint regs)
      (initializeBank tm regs) := by
  simp only [initializeBank, Cmd.basics]
  exact
    ⟨bank_footprint_subset_emission regs
        ((bankRegisters regs).index_mem_footprint 2),
      bank_footprint_subset_emission regs
        ((bankRegisters regs).index_mem_footprint 3),
      bank_footprint_subset_emission regs
        ((bankRegisters regs).index_mem_footprint 6)⟩

private theorem restoreRangeOne_writesWithin
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (emissionFootprint regs)
      (restoreRangeOne regs) := by
  apply physical_slot_mem_emission regs
  simp

private theorem prepareCellPosition_writesWithin
    (tm : TM workTapeCount)
    (symbol : Γ)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (emissionFootprint regs)
      (prepareCellPosition tm symbol regs) := by
  simp only [prepareCellPosition, Cmd.seqList,
    Footprint.CmdWritesWithin, Footprint.BasicWritesWithin]
  exact
    ⟨physical_slot_mem_emission regs (by simp),
      physical_slot_mem_emission regs (by simp),
      bank_footprint_subset_emission regs
        ((bankRegisters regs).index_mem_footprint 7),
      bank_footprint_subset_emission regs
        ((bankRegisters regs).index_mem_footprint 7),
      physical_slot_mem_emission regs (by simp),
      bank_footprint_subset_emission regs
        ((bankRegisters regs).index_mem_footprint 7),
      physical_slot_mem_emission regs (by simp)⟩

private theorem readCellBit_writesWithin
    (tm : TM workTapeCount)
    (slot : Slot)
    (tape : TapeIndex workTapeCount)
    (symbol : Γ)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (emissionFootprint regs)
      (readCellBit tm slot tape symbol regs) :=
  ⟨prepareCellPosition_writesWithin tm symbol regs,
    cmdWritesWithin_mono
      (AssignmentPayloadBit.read_writesWithin
        workTapeCount regs
        (childIndex workTapeCount (.content slot, tape)))
      (assignmentPayload_footprint_subset_emission regs)⟩

private theorem decodeCell_writesWithin
    (tm : TM workTapeCount)
    (slot : Slot)
    (tape : TapeIndex workTapeCount)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (emissionFootprint regs)
      (decodeCell tm slot tape regs) := by
  simp only [decodeCell, Footprint.CmdWritesWithin,
    Footprint.BasicWritesWithin]
  have hdecoded : decodedValue regs ∈ emissionFootprint regs :=
    physical_slot_mem_emission regs (by simp)
  refine ⟨readCellBit_writesWithin tm slot tape .zero regs, ?_,
    hdecoded⟩
  refine ⟨readCellBit_writesWithin tm slot tape .one regs, ?_,
    hdecoded⟩
  refine ⟨readCellBit_writesWithin tm slot tape .blank regs, ?_,
    hdecoded⟩
  exact
    ⟨readCellBit_writesWithin tm slot tape .start regs,
      hdecoded, hdecoded⟩

private theorem pushDecoded_writesWithin
    (tm : TM workTapeCount)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (emissionFootprint regs)
      (pushDecoded tm regs) := by
  simp only [pushDecoded, Cmd.seqList, Footprint.CmdWritesWithin]
  refine ⟨initializeBank_writesWithin tm regs,
    copy_emission_writesWithin regs _ _ ?_, ?_⟩
  · exact bank_footprint_subset_emission regs
      ((bankRegisters regs).index_mem_footprint 7)
  · simp only [NeighborhoodProgram.push]
    exact
      ⟨bank_footprint_subset_emission regs
          ((bankRegisters regs).index_mem_footprint 4),
        bank_footprint_subset_emission regs
          ((bankRegisters regs).index_mem_footprint 0),
        bank_footprint_subset_emission regs
          ((bankRegisters regs).index_mem_footprint 4)⟩

private theorem pushCell_writesWithin
    (tm : TM workTapeCount)
    (slot : Slot)
    (tape : TapeIndex workTapeCount)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (emissionFootprint regs)
      (pushCell tm slot tape regs) :=
  ⟨decodeCell_writesWithin tm slot tape regs,
    pushDecoded_writesWithin tm regs⟩

private theorem pushBlockBody_writesWithin
    (tm : TM workTapeCount)
    (slot : Slot)
    (tape : TapeIndex workTapeCount)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (emissionFootprint regs)
      (pushBlockBody tm slot tape regs) := by
  exact
    ⟨physical_slot_mem_emission regs (by simp),
      pushCell_writesWithin tm slot tape regs⟩

private theorem pushBlock_writesWithin
    (tm : TM workTapeCount)
    (slot : Slot)
    (tape : TapeIndex workTapeCount)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (emissionFootprint regs)
      (pushBlock tm slot tape regs) := by
  simp only [pushBlock, Cmd.seqList, Footprint.CmdWritesWithin,
    Footprint.BasicWritesWithin]
  exact
    ⟨physical_slot_mem_emission regs (by simp),
      copy_emission_writesWithin regs _ _
        (physical_slot_mem_emission regs (by simp)),
      pushBlockBody_writesWithin tm slot tape regs⟩

private theorem pushBlankBody_writesWithin
    (tm : TM workTapeCount)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (emissionFootprint regs)
      (pushBlankBody tm regs) := by
  simp only [pushBlankBody, Cmd.seqList, Footprint.CmdWritesWithin,
    Footprint.BasicWritesWithin]
  exact
    ⟨physical_slot_mem_emission regs (by simp),
      physical_slot_mem_emission regs (by simp),
      pushDecoded_writesWithin tm regs⟩

private theorem pushBlankBlock_writesWithin
    (tm : TM workTapeCount)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (emissionFootprint regs)
      (pushBlankBlock tm regs) := by
  simp only [pushBlankBlock, Cmd.seqList, Footprint.CmdWritesWithin,
    Footprint.BasicWritesWithin]
  exact
    ⟨physical_slot_mem_emission regs (by simp),
      copy_emission_writesWithin regs _ _
        (physical_slot_mem_emission regs (by simp)),
      pushBlankBody_writesWithin tm regs⟩

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
    ⟨cmdWritesWithin_mono (ControlDecode.decodeNode_writesWithin regs)
        (control_footprint_subset regs),
      physical_slot_mem regs (by simp),
      cmdWritesWithin_mono
        (CombineSafeCenter.deriveCenter_writesWithin
          workTapeCount controller regs)
        (center_footprint_subset regs)⟩

private theorem prepareHeadPosition_writesWithin
    (tm : TM workTapeCount)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (emissionFootprint regs)
      (prepareHeadPosition tm regs) := by
  simp only [prepareHeadPosition, Cmd.seqList,
    Footprint.CmdWritesWithin, Footprint.BasicWritesWithin]
  exact
    ⟨physical_slot_mem_emission regs (by simp),
      physical_slot_mem_emission regs (by simp),
      physical_slot_mem_emission regs (by simp),
      bank_footprint_subset_emission regs
        ((bankRegisters regs).index_mem_footprint 7)⟩

private theorem decodeHeadBody_writesWithin
    (tm : TM workTapeCount)
    (tape : TapeIndex workTapeCount)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (emissionFootprint regs)
      (decodeHeadBody tm tape regs) := by
  simp only [decodeHeadBody, Cmd.seqList,
    Footprint.CmdWritesWithin, Footprint.BasicWritesWithin]
  refine
    ⟨prepareHeadPosition_writesWithin tm regs,
      cmdWritesWithin_mono
        (AssignmentPayloadBit.read_writesWithin
          workTapeCount regs
          (childIndex workTapeCount (.chronological, tape)))
        (assignmentPayload_footprint_subset_emission regs),
      ?_, ?_⟩
  · exact
      ⟨physical_slot_mem_emission regs (by simp),
        physical_slot_mem_emission regs (by simp)⟩
  · exact
      ⟨bank_footprint_subset_emission regs
          ((bankRegisters regs).index_mem_footprint 7),
        physical_slot_mem_emission regs (by simp),
        physical_slot_mem_emission regs (by simp),
        physical_slot_mem_emission regs (by simp)⟩

private theorem decodeHead_writesWithin
    (tm : TM workTapeCount)
    (tape : TapeIndex workTapeCount)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (emissionFootprint regs)
      (decodeHead tm tape regs) := by
  simp only [decodeHead, Cmd.seqList, Footprint.CmdWritesWithin,
    Footprint.BasicWritesWithin]
  exact
    ⟨physical_slot_mem_emission regs (by simp),
      copy_emission_writesWithin regs _ _
        (physical_slot_mem_emission regs (by simp)),
      physical_slot_mem_emission regs (by simp),
      decodeHeadBody_writesWithin tm tape regs,
      physical_slot_mem_emission regs (by simp)⟩

private theorem markHead_writesWithin
    (tm : TM workTapeCount)
    (centerOffsetBlocks : ℕ)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (emissionFootprint regs)
      (markHead tm centerOffsetBlocks regs) := by
  simp only [markHead, Cmd.seqList, Footprint.CmdWritesWithin,
    Footprint.BasicWritesWithin]
  refine
    ⟨bank_footprint_subset_emission regs
        ((bankRegisters regs).index_mem_footprint 7),
      bank_footprint_subset_emission regs
        ((bankRegisters regs).index_mem_footprint 7),
      physical_slot_mem_emission regs (by simp),
      initializeBank_writesWithin tm regs,
      copy_emission_writesWithin regs _ _
        (bank_footprint_subset_emission regs
          ((bankRegisters regs).index_mem_footprint 8)),
      cmdWritesWithin_mono
        (NeighborhoodProgram.bankRead_sourceWritesWithin
          (bankRegisters regs))
        (bank_footprint_subset_emission regs),
      bank_footprint_subset_emission regs
        ((bankRegisters regs).index_mem_footprint 7),
      bank_footprint_subset_emission regs
        ((bankRegisters regs).index_mem_footprint 11),
      copy_emission_writesWithin regs _ _
        (bank_footprint_subset_emission regs
          ((bankRegisters regs).index_mem_footprint 8)),
      cmdWritesWithin_mono
        (NeighborhoodProgram.bankReplace_sourceWritesWithin
          (bankRegisters regs))
        (bank_footprint_subset_emission regs),
      restoreRangeOne_writesWithin regs⟩

private theorem initializeBoundaryTape_writesWithin
    (tm : TM workTapeCount)
    (tape : TapeIndex workTapeCount)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (emissionFootprint regs)
      (initializeBoundaryTape tm tape regs) := by
  simp only [initializeBoundaryTape, Cmd.seqList,
    Footprint.CmdWritesWithin]
  exact
    ⟨pushBlankBlock_writesWithin tm regs,
      pushBlock_writesWithin tm .upper tape regs,
      pushBlock_writesWithin tm .lower tape regs,
      decodeHead_writesWithin tm tape regs,
      markHead_writesWithin tm 0 regs⟩

private theorem initializeRegularTape_writesWithin
    (tm : TM workTapeCount)
    (tape : TapeIndex workTapeCount)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (emissionFootprint regs)
      (initializeRegularTape tm tape regs) := by
  simp only [initializeRegularTape, Cmd.seqList,
    Footprint.CmdWritesWithin]
  exact
    ⟨pushBlock_writesWithin tm .upper tape regs,
      pushBlock_writesWithin tm .center tape regs,
      pushBlock_writesWithin tm .lower tape regs,
      decodeHead_writesWithin tm tape regs,
      markHead_writesWithin tm 1 regs⟩

private theorem initializeTape_writesWithin
    (tm : TM workTapeCount)
    (controller : SearchProgram.Registers)
    (tape : TapeIndex workTapeCount)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (footprint regs)
      (initializeTape tm controller tape regs) := by
  simp only [initializeTape, Cmd.seqList,
    Footprint.CmdWritesWithin]
  exact
    ⟨copy_writesWithin regs _ _
        (physical_slot_mem regs (by simp)),
      copy_writesWithin regs _ _
        (physical_slot_mem regs (by simp)),
      deriveTapeCenter_writesWithin
        workTapeCount controller tape regs,
      copy_writesWithin regs _ _
        (physical_slot_mem regs (by simp)),
      copy_writesWithin regs _ _
        (physical_slot_mem regs (by simp)),
      cmdWritesWithin_mono
        (initializeBoundaryTape_writesWithin tm tape regs)
        (emissionFootprint_subset regs),
      cmdWritesWithin_mono
        (initializeRegularTape_writesWithin tm tape regs)
        (emissionFootprint_subset regs)⟩

private theorem initializeTapes_writesWithin
    (tm : TM workTapeCount)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) :
    ∀ tapes,
      Footprint.CmdWritesWithin (footprint regs)
        (initializeTapes tm controller regs tapes) := by
  intro tapes
  induction tapes with
  | nil =>
      trivial
  | cons tape tapes ih =>
      exact
        ⟨initializeTape_writesWithin tm controller tape regs, ih⟩

private theorem readStateBit_writesWithin
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (state : tm.Q)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (emissionFootprint regs)
      (readStateBit tm order state regs) :=
  ⟨physical_slot_mem_emission regs (by simp),
    cmdWritesWithin_mono
      (AssignmentPayloadBit.read_writesWithin
        workTapeCount regs
        (childIndex workTapeCount
          (.chronological, TapeIndex.input workTapeCount)))
      (assignmentPayload_footprint_subset_emission regs)⟩

private theorem decodeStates_writesWithin
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (regs : NeighborhoodTrial.Registers controller) :
    ∀ sourceStates,
      Footprint.CmdWritesWithin (emissionFootprint regs)
        (decodeStates tm order regs sourceStates) := by
  intro sourceStates
  induction sourceStates with
  | nil =>
      exact physical_slot_mem_emission regs (by simp)
  | cons state sourceStates ih =>
      exact
        ⟨readStateBit_writesWithin tm order state regs,
          ih,
          physical_slot_mem_emission regs (by simp)⟩

private theorem initializeState_writesWithin
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (emissionFootprint regs)
      (initializeState tm order regs) :=
  ⟨decodeStates_writesWithin tm order regs (states tm order),
    pushDecoded_writesWithin tm regs⟩

theorem build_writesWithin_internal
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) :
  Footprint.CmdWritesWithin (footprint regs)
      (build tm order controller regs) :=
  ⟨initializeTapes_writesWithin tm controller regs
      (tapes workTapeCount),
    cmdWritesWithin_mono
      (initializeState_writesWithin tm order regs)
      (emissionFootprint_subset regs)⟩

theorem build_compiledWritesWithin_internal
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) :
    RAM.RegisterStore.DenseOverlay.FixedRegisters.Footprint.ProgramWritesWithin
      (build tm order controller regs).compile
      (footprint regs) :=
  Footprint.programWritesWithin_compile
    (build_writesWithin_internal tm order controller regs)

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

/-- Exact direct destinations of one decoded-digit push. -/
private def pushDecodedFootprint
    (regs : NeighborhoodTrial.Registers controller) : Finset ℕ :=
  let stack := (bankRegisters regs).mainStack
  {(bankRegisters regs).base,
    (bankRegisters regs).basePred,
    (bankRegisters regs).one,
    (bankRegisters regs).value,
    stack.quotient,
    stack.word}

private theorem pushDecoded_small_writesWithin
    (tm : TM workTapeCount)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (pushDecodedFootprint regs)
      (pushDecoded tm regs) := by
  simp [pushDecodedFootprint, pushDecoded, initializeBank, copy,
    NeighborhoodProgram.push, Cmd.basics, Cmd.seqList,
    Footprint.CmdWritesWithin, Footprint.BasicWritesWithin]

private theorem pushDecoded_runs
    (tm : TM workTapeCount)
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store) (word value : ℕ)
    (hword : store (packedWord regs) = word)
    (hvalue : store (decodedValue regs) = value) :
    ∃ final,
      Runs (pushDecoded tm regs) store final ∧
      final (packedWord regs) =
        PackedDigits.push
          (PackedLocalConfiguration.radix tm) value word ∧
      ∀ address, address ∉ pushDecodedFootprint regs →
        final address = store address := by
  obtain ⟨initialized, hinitializeRun, hinitializedWord,
      hinitializedBase, _hinitializedBasePred, _hinitializedOne,
      hinitializedOutside⟩ :=
    initializeBank_runs tm regs store word hword
  have hinitializedValue :
      initialized (decodedValue regs) = value := by
    rw [hinitializedOutside (decodedValue regs)]
    · exact hvalue
    · exact regs.injective.ne (by decide)
    · exact regs.injective.ne (by decide)
    · exact regs.injective.ne (by decide)
  obtain ⟨copied, hcopyRun, hcopiedValue, hcopiedOutside⟩ :=
    copy_runs (bankRegisters regs).value (decodedValue regs)
      initialized (regs.injective.ne (by decide))
  have hcopiedWord :
      copied (bankRegisters regs).word = word := by
    rw [hcopiedOutside (bankRegisters regs).word
      ((bankRegisters regs).index_ne (by decide))]
    exact hinitializedWord
  have hcopiedBase :
      copied (bankRegisters regs).base =
        PackedLocalConfiguration.radix tm := by
    rw [hcopiedOutside (bankRegisters regs).base
      ((bankRegisters regs).index_ne (by decide))]
    exact hinitializedBase
  have hcopiedPushedValue :
      copied (bankRegisters regs).value = value :=
    hcopiedValue.trans hinitializedValue
  obtain ⟨final, hpushRun, hfinalWord, _hquotient,
      _hbase, _hvalue⟩ :=
    NeighborhoodProgram.push_runs
      (bankRegisters regs).mainStack copied
      (PackedLocalConfiguration.radix tm) word value
      hcopiedWord hcopiedBase hcopiedPushedValue
  have hrun : Runs (pushDecoded tm regs) store final := by
    simpa [pushDecoded, Cmd.seqList] using
      Runs.seq hinitializeRun (Runs.seq hcopyRun hpushRun)
  refine ⟨final, hrun, hfinalWord, ?_⟩
  intro address haddress
  exact Footprint.runs_eq_outside
    (pushDecoded_small_writesWithin tm regs) hrun haddress

/-- Stable data needed by every streamed assignment-payload lookup. -/
private structure AssignmentContext
    (tm : TM workTapeCount)
    (blockLength offset code word : ℕ)
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store) : Prop where
  blockLength_eq :
    store (Layout.blockLength regs) = blockLength
  cursor_eq :
    store (cursor regs) = offset
  assignment_eq :
    store (CombineValue.rangeRegisters regs).remaining = code
  one_eq :
    store (CombineValue.rangeRegisters regs).one = 1
  word_eq :
    store (packedWord regs) = word
  chunkCount_eq :
    store (Layout.chunkCount regs) =
      PrimeGrouped.Logarithmic.chunkCount
        (NeighborhoodExecutableEvaluation.payloadWidth tm blockLength)
        (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount)
  chunkRadix_eq :
    store (Layout.chunkRadix regs) =
      2 ^
        PrimeGrouped.Logarithmic.chunkBits
          (NeighborhoodExecutableEvaluation.payloadWidth tm blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount)

private def assignmentContextSlot (slot : Fin 34) : Prop :=
  slot = 2 ∨ slot = 19 ∨ slot = 21 ∨ slot = 17 ∨
    slot = 32 ∨ slot = 7 ∨ slot = 8

private theorem assignmentContextSlot_ne_31 :
    ∀ slot, assignmentContextSlot slot → slot ≠ 31 := by
  intro slot hslot
  rcases hslot with h | h | h | h | h | h | h <;>
    subst slot <;> decide

private theorem assignmentContextSlot_ne_18 :
    ∀ slot, assignmentContextSlot slot → slot ≠ 18 := by
  intro slot hslot
  rcases hslot with h | h | h | h | h | h | h <;>
    subst slot <;> decide

private theorem assignmentContextSlot_ne_10 :
    ∀ slot, assignmentContextSlot slot → slot ≠ 10 := by
  intro slot hslot
  rcases hslot with h | h | h | h | h | h | h <;>
    subst slot <;> decide

private theorem assignmentContext_of_cursorWrite
    (tm : TM workTapeCount)
    (regs : NeighborhoodTrial.Registers controller)
    (blockLength oldOffset newOffset code word : ℕ)
    (initial final : Store)
    (hcontext :
      AssignmentContext tm blockLength oldOffset code word
        regs initial)
    (hcursor : final (cursor regs) = newOffset)
    (houtside :
      ∀ address, address ≠ cursor regs →
        final address = initial address) :
    AssignmentContext tm blockLength newOffset code word
      regs final := by
  have fixed (slot : Fin 34) (hslot : slot ≠ 19) :
      final (regs.index slot) = initial (regs.index slot) := by
    apply houtside
    simpa [cursor, CombineValue.rangeRegisters] using
      regs.injective.ne hslot
  exact
    { blockLength_eq := (fixed 2 (by decide)).trans
        hcontext.blockLength_eq
      cursor_eq := hcursor
      assignment_eq := by
        simpa [CombineValue.rangeRegisters] using
          (fixed 21 (by decide)).trans hcontext.assignment_eq
      one_eq := by
        simpa [CombineValue.rangeRegisters] using
          (fixed 17 (by decide)).trans hcontext.one_eq
      word_eq := by
        simpa [packedWord, bankRegisters,
          PackedLocalHeadScan.bankRegisters,
          PackedLocalHeadScan.bankMap] using
            (fixed 32 (by decide)).trans hcontext.word_eq
      chunkCount_eq := (fixed 7 (by decide)).trans
        hcontext.chunkCount_eq
      chunkRadix_eq := (fixed 8 (by decide)).trans
        hcontext.chunkRadix_eq }

private theorem assignmentContext_of_physicalWrite
    (tm : TM workTapeCount)
    (regs : NeighborhoodTrial.Registers controller)
    (blockLength offset code word : ℕ)
    (destinationSlot : Fin 34)
    (initial final : Store)
    (hcontext :
      AssignmentContext tm blockLength offset code word
        regs initial)
    (huntracked :
      ∀ slot, assignmentContextSlot slot →
        slot ≠ destinationSlot)
    (houtside :
      ∀ address, address ≠ regs.index destinationSlot →
        final address = initial address) :
    AssignmentContext tm blockLength offset code word
      regs final := by
  have fixed (slot : Fin 34)
      (hslot : assignmentContextSlot slot) :
      final (regs.index slot) = initial (regs.index slot) :=
    houtside (regs.index slot)
      (regs.injective.ne (huntracked slot hslot))
  exact
    { blockLength_eq := (fixed 2 (by
          simp [assignmentContextSlot])).trans
        hcontext.blockLength_eq
      cursor_eq := by
        simpa [cursor, CombineValue.rangeRegisters] using
          (fixed 19 (by simp [assignmentContextSlot])).trans
            hcontext.cursor_eq
      assignment_eq := by
        simpa [CombineValue.rangeRegisters] using
          (fixed 21 (by simp [assignmentContextSlot])).trans
            hcontext.assignment_eq
      one_eq := by
        simpa [CombineValue.rangeRegisters] using
          (fixed 17 (by simp [assignmentContextSlot])).trans
            hcontext.one_eq
      word_eq := by
        simpa [packedWord, bankRegisters,
          PackedLocalHeadScan.bankRegisters,
          PackedLocalHeadScan.bankMap] using
            (fixed 32 (by simp [assignmentContextSlot])).trans
              hcontext.word_eq
      chunkCount_eq := (fixed 7 (by
          simp [assignmentContextSlot])).trans
        hcontext.chunkCount_eq
      chunkRadix_eq := (fixed 8 (by
          simp [assignmentContextSlot])).trans
        hcontext.chunkRadix_eq }

private theorem packedWord_not_mem_payloadWrite
    (regs : NeighborhoodTrial.Registers controller) :
    packedWord regs ∉ AssignmentPayloadBit.writeFootprint regs := by
  simp [packedWord, bankRegisters,
    PackedLocalHeadScan.bankRegisters, PackedLocalHeadScan.bankMap,
    AssignmentPayloadBit.writeFootprint,
    AssignmentPayloadBit.recoveryFootprint,
    AssignmentPayloadBit.exponentStackRegisters,
    AssignmentPayloadBit.exponentStackMap,
    NeighborhoodProgram.StackRegisters.footprint,
    AssignmentBit.writeFootprint, AssignmentBit.digitRegisters,
    AssignmentBit.digitMap, CombineTerm.DigitRegisters.writeFootprint,
    AssignmentBit.digitIndex, AssignmentPayloadBit.recoveredChunkBits,
    regs.injective.eq_iff]
  decide

private theorem prepareCellPosition_runs
    (tm : TM workTapeCount)
    (symbol : Γ)
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store) (blockLength offset : ℕ)
    (hblock :
      store (Layout.blockLength regs) = blockLength)
    (hoffset : store (cursor regs) = offset) :
    ∃ final,
      Runs (prepareCellPosition tm symbol regs) store final ∧
      final (payloadPosition regs) =
        Fintype.card tm.Q + blockLength + 4 * offset +
          (NeighborhoodExecutableEvaluation.FiniteEncoding.gammaEquiv
            symbol).val ∧
      ∀ address,
        address ≠ payloadPosition regs →
        address ≠ (bankRegisters regs).value →
        final address = store address := by
  let ops : List Basic :=
    [.imm (payloadPosition regs) (Fintype.card tm.Q),
      .add (payloadPosition regs) (payloadPosition regs)
        (Layout.blockLength regs),
      .imm (bankRegisters regs).value 4,
      .mul (bankRegisters regs).value (cursor regs)
        (bankRegisters regs).value,
      .add (payloadPosition regs) (payloadPosition regs)
        (bankRegisters regs).value,
      .imm (bankRegisters regs).value
        (NeighborhoodExecutableEvaluation.FiniteEncoding.gammaEquiv
          symbol).val,
      .add (payloadPosition regs) (payloadPosition regs)
        (bankRegisters regs).value]
  let final := Basic.execList ops store
  refine ⟨final, ?_, ?_, ?_⟩
  · simpa [prepareCellPosition, ops] using basics_runs ops store
  · simp [final, ops, Basic.execList, Basic.exec, hblock,
      payloadPosition, AssignmentPayloadBit.payloadPosition,
      Layout.codecScratch, cursor, CombineValue.rangeRegisters,
      bankRegisters, PackedLocalHeadScan.bankRegisters,
      PackedLocalHeadScan.bankMap, regs.injective.eq_iff]
    change store (cursor regs) * 4 = 4 * offset
    rw [hoffset]
    omega
  · intro address hpayload hvalue
    simp [final, ops, Basic.execList, Basic.exec,
      Function.update_of_ne, hpayload, hvalue]

private def cellPosition
    (tm : TM workTapeCount)
    (blockLength offset : ℕ) (hoffset : offset < blockLength)
    (symbol : Γ) :
    Fin
      (NeighborhoodExecutableEvaluation.payloadWidth tm blockLength) :=
  ⟨Fintype.card tm.Q + blockLength + 4 * offset +
      (NeighborhoodExecutableEvaluation.FiniteEncoding.gammaEquiv
        symbol).val,
    by
      change
        Fintype.card tm.Q + blockLength + 4 * offset +
            (NeighborhoodExecutableEvaluation.FiniteEncoding.gammaEquiv
              symbol).val <
          ComputationGraph.CompactEncoding.width blockLength tm.Q
      rw [ComputationGraph.CompactEncoding.width_eq]
      have hsymbol :=
        (NeighborhoodExecutableEvaluation.FiniteEncoding.gammaEquiv
          symbol).isLt
      omega⟩

private theorem readCellBit_runs
    (tm : TM workTapeCount)
    (slot : Slot)
    (tape : TapeIndex workTapeCount)
    (symbol : Γ)
    (regs : NeighborhoodTrial.Registers controller)
    (blockLength offset code word : ℕ)
    (hoffset : offset < blockLength)
    (store : Store)
    (hcontext :
      AssignmentContext tm blockLength offset code word regs store) :
    ∃ final,
      Runs (readCellBit tm slot tape symbol regs) store final ∧
      final (decodedValue regs) =
        (AssignmentCodeSemantics.assignmentBits
          (NeighborhoodExecutableEvaluation.payloadWidth tm blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount)
          code
          (childIndex workTapeCount (.content slot, tape))
          (cellPosition tm blockLength offset hoffset symbol)).toNat ∧
      AssignmentContext tm blockLength offset code word regs final := by
  let position :
      Fin
        (NeighborhoodExecutableEvaluation.payloadWidth tm blockLength) :=
    cellPosition tm blockLength offset hoffset symbol
  obtain ⟨prepared, hprepareRun, hposition, hprepareOutside⟩ :=
    prepareCellPosition_runs tm symbol regs store blockLength offset
      hcontext.blockLength_eq hcontext.cursor_eq
  have hpreparedChunkCount :
      prepared (Layout.chunkCount regs) =
        PrimeGrouped.Logarithmic.chunkCount
          (NeighborhoodExecutableEvaluation.payloadWidth tm blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount) := by
    rw [hprepareOutside (Layout.chunkCount regs)
      (regs.injective.ne (by decide))
      (regs.injective.ne (by decide))]
    exact hcontext.chunkCount_eq
  have hpreparedChunkRadix :
      prepared (Layout.chunkRadix regs) =
        2 ^
          PrimeGrouped.Logarithmic.chunkBits
            (NeighborhoodExecutableEvaluation.payloadWidth tm blockLength)
            (NeighborhoodExecutableEvaluation.graphFanIn
              workTapeCount) := by
    rw [hprepareOutside (Layout.chunkRadix regs)
      (regs.injective.ne (by decide))
      (regs.injective.ne (by decide))]
    exact hcontext.chunkRadix_eq
  have hpreparedCode :
      prepared (CombineValue.rangeRegisters regs).remaining = code := by
    rw [hprepareOutside
      (CombineValue.rangeRegisters regs).remaining
      (regs.injective.ne (by decide))
      (regs.injective.ne (by decide))]
    exact hcontext.assignment_eq
  have hpreparedPosition :
      prepared (payloadPosition regs) = position.val := by
    simpa [position, cellPosition] using hposition
  obtain ⟨final, hreadRun, hpost⟩ :=
    AssignmentPayloadBit.read_runs
      workTapeCount
      (NeighborhoodExecutableEvaluation.payloadWidth tm blockLength)
      regs (childIndex workTapeCount (.content slot, tape))
      position prepared code hpreparedChunkCount hpreparedChunkRadix
      hpreparedCode hpreparedPosition
  refine ⟨final, ?_, hpost.value_eq, ?_⟩
  · exact Runs.seq hprepareRun hreadRun
  · refine
      { blockLength_eq := ?_
        cursor_eq := ?_
        assignment_eq := hpost.remaining_eq
        one_eq := ?_
        word_eq := ?_
        chunkCount_eq := ?_
        chunkRadix_eq := ?_ }
    · rw [hpost.abi.blockLength_eq]
      rw [hprepareOutside (Layout.blockLength regs)
        (regs.injective.ne (by decide))
        (regs.injective.ne (by decide))]
      exact hcontext.blockLength_eq
    · rw [hpost.term_eq]
      rw [hprepareOutside (cursor regs)
        (regs.injective.ne (by decide))
        (regs.injective.ne (by decide))]
      exact hcontext.cursor_eq
    · rw [hpost.one_eq]
      rw [hprepareOutside (CombineValue.rangeRegisters regs).one
        (regs.injective.ne (by decide))
        (regs.injective.ne (by decide))]
      exact hcontext.one_eq
    · rw [hpost.eq_outside (packedWord regs)
        (packedWord_not_mem_payloadWrite regs)]
      rw [hprepareOutside (packedWord regs)
        (regs.injective.ne (by decide))
        (regs.injective.ne (by decide))]
      exact hcontext.word_eq
    · rw [hpost.abi.chunkCount_eq]
      exact hpreparedChunkCount
    · rw [hpost.abi.chunkRadix_eq]
      exact hpreparedChunkRadix

private theorem setDecoded_runs
    (tm : TM workTapeCount)
    (regs : NeighborhoodTrial.Registers controller)
    (blockLength offset code word value : ℕ)
    (store : Store)
    (hcontext :
      AssignmentContext tm blockLength offset code word regs store) :
    ∃ final,
      Runs
        (.basic (.imm (decodedValue regs) value))
        store final ∧
      final (decodedValue regs) = value ∧
      AssignmentContext tm blockLength offset code word regs final := by
  let final := (Basic.imm (decodedValue regs) value).exec store
  refine ⟨final, Runs.basic _ _, ?_, ?_⟩
  · simp [final, Basic.exec]
  · refine
      { blockLength_eq := ?_
        cursor_eq := ?_
        assignment_eq := ?_
        one_eq := ?_
        word_eq := ?_
        chunkCount_eq := ?_
        chunkRadix_eq := ?_ }
    · simpa [final, Basic.exec, decodedValue,
        CombineTerm.packedValue, regs.injective.eq_iff] using
        hcontext.blockLength_eq
    · simpa [final, Basic.exec, decodedValue,
        CombineTerm.packedValue, cursor, CombineValue.rangeRegisters,
        regs.injective.eq_iff] using hcontext.cursor_eq
    · simpa [final, Basic.exec, decodedValue,
        CombineTerm.packedValue, CombineValue.rangeRegisters,
        regs.injective.eq_iff] using hcontext.assignment_eq
    · simpa [final, Basic.exec, decodedValue,
        CombineTerm.packedValue, CombineValue.rangeRegisters,
        regs.injective.eq_iff] using hcontext.one_eq
    · simpa [final, Basic.exec, decodedValue,
        CombineTerm.packedValue, packedWord, bankRegisters,
        PackedLocalHeadScan.bankRegisters, PackedLocalHeadScan.bankMap,
        regs.injective.eq_iff] using hcontext.word_eq
    · simpa [final, Basic.exec, decodedValue,
        CombineTerm.packedValue, regs.injective.eq_iff] using
        hcontext.chunkCount_eq
    · simpa [final, Basic.exec, decodedValue,
        CombineTerm.packedValue, regs.injective.eq_iff] using
        hcontext.chunkRadix_eq

private theorem setPayloadPosition_runs
    (tm : TM workTapeCount)
    (regs : NeighborhoodTrial.Registers controller)
    (blockLength offset code word value : ℕ)
    (store : Store)
    (hcontext :
      AssignmentContext tm blockLength offset code word regs store) :
    ∃ final,
      Runs
        (.basic (.imm (payloadPosition regs) value))
        store final ∧
      final (payloadPosition regs) = value ∧
      AssignmentContext tm blockLength offset code word regs final := by
  let final := (Basic.imm (payloadPosition regs) value).exec store
  have houtside :
      ∀ address, address ≠ payloadPosition regs →
        final address = store address := by
    intro address haddress
    simp [final, Basic.exec, Function.update_of_ne, haddress]
  refine ⟨final, Runs.basic _ _, by simp [final, Basic.exec], ?_⟩
  refine
    { blockLength_eq := ?_
      cursor_eq := ?_
      assignment_eq := ?_
      one_eq := ?_
      word_eq := ?_
      chunkCount_eq := ?_
      chunkRadix_eq := ?_ }
  · rw [houtside (Layout.blockLength regs)
      (regs.injective.ne (by decide))]
    exact hcontext.blockLength_eq
  · rw [houtside (cursor regs)
      (regs.injective.ne (by decide))]
    exact hcontext.cursor_eq
  · rw [houtside (CombineValue.rangeRegisters regs).remaining
      (regs.injective.ne (by decide))]
    exact hcontext.assignment_eq
  · rw [houtside (CombineValue.rangeRegisters regs).one
      (regs.injective.ne (by decide))]
    exact hcontext.one_eq
  · rw [houtside (packedWord regs)
      (regs.injective.ne (by decide))]
    exact hcontext.word_eq
  · rw [houtside (Layout.chunkCount regs)
      (regs.injective.ne (by decide))]
    exact hcontext.chunkCount_eq
  · rw [houtside (Layout.chunkRadix regs)
      (regs.injective.ne (by decide))]
    exact hcontext.chunkRadix_eq

private theorem payloadRead_runs
    (tm : TM workTapeCount)
    (regs : NeighborhoodTrial.Registers controller)
    (blockLength offset code word : ℕ)
    (child :
      Fin
        (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount))
    (position :
      Fin
        (NeighborhoodExecutableEvaluation.payloadWidth tm blockLength))
    (store : Store)
    (hcontext :
      AssignmentContext tm blockLength offset code word regs store)
    (hposition :
      store (payloadPosition regs) = position.val) :
    ∃ final,
      Runs (AssignmentPayloadBit.read workTapeCount regs child)
        store final ∧
      final (decodedValue regs) =
        (AssignmentCodeSemantics.assignmentBits
          (NeighborhoodExecutableEvaluation.payloadWidth tm blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount)
          code child position).toNat ∧
      final (payloadPosition regs) = position.val ∧
      AssignmentContext tm blockLength offset code word regs final := by
  obtain ⟨final, hrun, hpost⟩ :=
    AssignmentPayloadBit.read_runs
      workTapeCount
      (NeighborhoodExecutableEvaluation.payloadWidth tm blockLength)
      regs child position store code hcontext.chunkCount_eq
      hcontext.chunkRadix_eq hcontext.assignment_eq hposition
  refine ⟨final, hrun, hpost.value_eq, hpost.position_eq, ?_⟩
  refine
    { blockLength_eq :=
        hpost.abi.blockLength_eq.trans hcontext.blockLength_eq
      cursor_eq := hpost.term_eq.trans hcontext.cursor_eq
      assignment_eq := hpost.remaining_eq
      one_eq := hpost.one_eq.trans hcontext.one_eq
      word_eq := ?_
      chunkCount_eq :=
        hpost.abi.chunkCount_eq.trans hcontext.chunkCount_eq
      chunkRadix_eq :=
        hpost.abi.chunkRadix_eq.trans hcontext.chunkRadix_eq }
  exact
    (hpost.eq_outside (packedWord regs)
      (packedWord_not_mem_payloadWrite regs)).trans hcontext.word_eq

private def cellBits
    (tm : TM workTapeCount)
    (blockLength offset : ℕ) (hoffset : offset < blockLength)
    (code : ℕ) (slot : Slot) (tape : TapeIndex workTapeCount) :
    Γ → Bool :=
  fun symbol =>
    AssignmentCodeSemantics.assignmentBits
      (NeighborhoodExecutableEvaluation.payloadWidth tm blockLength)
      (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount)
      code
      (childIndex workTapeCount (.content slot, tape))
      (cellPosition tm blockLength offset hoffset symbol)

private theorem decodeGamma_cellBits
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (offset : ℕ) (hoffset : offset < blockLength)
    (code : ℕ) (slot : Slot) (tape : TapeIndex workTapeCount) :
    NeighborhoodExecutableEvaluation.decodeGamma
        (cellBits tm blockLength offset hoffset code slot tape) =
      (LocalAssignmentSemantics.assignmentInputs
        tm order blockLength hpositive code
        (.content slot, tape)).cells ⟨offset, hoffset⟩ := by
  unfold LocalAssignmentSemantics.assignmentInputs
    NeighborhoodExecutableEvaluation.decodeBits
  change
    NeighborhoodExecutableEvaluation.decodeGamma
        (cellBits tm blockLength offset hoffset code slot tape) =
      NeighborhoodExecutableEvaluation.decodeGamma
        (fun symbol =>
          AssignmentCodeSemantics.assignmentBits
            (NeighborhoodExecutableEvaluation.payloadWidth tm blockLength)
            (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount)
            code
            (childIndex workTapeCount (.content slot, tape))
            ((NeighborhoodExecutableEvaluation.FiniteEncoding.ofStateOrder
              order blockLength).coordinate
              (.inr (.inr (⟨offset, hoffset⟩, symbol)))))
  apply congrArg NeighborhoodExecutableEvaluation.decodeGamma
  funext symbol
  apply congrArg
    (AssignmentCodeSemantics.assignmentBits
      (NeighborhoodExecutableEvaluation.payloadWidth tm blockLength)
      (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount)
      code (childIndex workTapeCount (.content slot, tape)))
  apply Fin.ext
  simp [cellPosition,
    NeighborhoodExecutableEvaluation.FiniteEncoding.ofStateOrder,
    NeighborhoodExecutableEvaluation.FiniteEncoding.coordinateEquiv]
  omega

private theorem decodeCell_runs
    (tm : TM workTapeCount)
    (slot : Slot)
    (tape : TapeIndex workTapeCount)
    (regs : NeighborhoodTrial.Registers controller)
    (blockLength offset code word : ℕ)
    (hoffset : offset < blockLength)
    (store : Store)
    (hcontext :
      AssignmentContext tm blockLength offset code word regs store) :
    ∃ final,
      Runs (decodeCell tm slot tape regs) store final ∧
      final (decodedValue regs) =
        CompactValueCodeSemantics.gammaCode
          (NeighborhoodExecutableEvaluation.decodeGamma
            (cellBits tm blockLength offset hoffset code slot tape)) ∧
      AssignmentContext tm blockLength offset code word regs final := by
  let bits :=
    cellBits tm blockLength offset hoffset code slot tape
  obtain ⟨afterZero, hzeroRun, hzeroValueRaw, hzeroContext⟩ :=
    readCellBit_runs tm slot tape .zero regs blockLength offset
      code word hoffset store hcontext
  have hzeroValue :
      afterZero (decodedValue regs) = (bits .zero).toNat := by
    simpa [bits, cellBits] using hzeroValueRaw
  by_cases hzero : bits .zero = true
  · obtain ⟨final, hsetRun, hsetValue, hfinalContext⟩ :=
      setDecoded_runs tm regs blockLength offset code word
        (CompactValueCodeSemantics.gammaCode .zero)
        afterZero hzeroContext
    have htest : afterZero (decodedValue regs) ≠ 0 := by
      rw [hzeroValue, hzero]
      decide
    refine ⟨final, ?_, ?_, hfinalContext⟩
    · simpa [decodeCell] using
        Runs.seq hzeroRun (Runs.ifNonzero htest hsetRun)
    · simpa [NeighborhoodExecutableEvaluation.decodeGamma, bits,
        hzero] using hsetValue
  · have hzeroFalse : bits .zero = false :=
      Bool.eq_false_of_not_eq_true hzero
    have hzeroTest : afterZero (decodedValue regs) = 0 := by
      rw [hzeroValue, hzeroFalse]
      rfl
    obtain ⟨afterOne, honeRun, honeValueRaw, honeContext⟩ :=
      readCellBit_runs tm slot tape .one regs blockLength offset
        code word hoffset afterZero hzeroContext
    have honeValue :
        afterOne (decodedValue regs) = (bits .one).toNat := by
      simpa [bits, cellBits] using honeValueRaw
    by_cases hone : bits .one = true
    · obtain ⟨final, hsetRun, hsetValue, hfinalContext⟩ :=
        setDecoded_runs tm regs blockLength offset code word
          (CompactValueCodeSemantics.gammaCode .one)
          afterOne honeContext
      have honeTest : afterOne (decodedValue regs) ≠ 0 := by
        rw [honeValue, hone]
        decide
      have hzeroBranch :
          Runs
            (Cmd.seq
              (readCellBit tm slot tape .one regs)
              (.ifZero (decodedValue regs)
                (Cmd.seq
                  (readCellBit tm slot tape .blank regs)
                  (.ifZero (decodedValue regs)
                    (Cmd.seq
                      (readCellBit tm slot tape .start regs)
                      (.ifZero (decodedValue regs)
                        (.basic
                          (.imm (decodedValue regs)
                            (CompactValueCodeSemantics.gammaCode
                              .blank)))
                        (.basic
                          (.imm (decodedValue regs)
                            (CompactValueCodeSemantics.gammaCode
                              .start)))))
                    (.basic
                      (.imm (decodedValue regs)
                        (CompactValueCodeSemantics.gammaCode .blank)))))
                (.basic
                  (.imm (decodedValue regs)
                    (CompactValueCodeSemantics.gammaCode .one)))))
            afterZero final :=
        Runs.seq honeRun (Runs.ifNonzero honeTest hsetRun)
      refine ⟨final, ?_, ?_, hfinalContext⟩
      · simpa [decodeCell] using
          Runs.seq hzeroRun (Runs.ifZero hzeroTest hzeroBranch)
      · simpa [NeighborhoodExecutableEvaluation.decodeGamma, bits,
          hzeroFalse, hone] using hsetValue
    · have honeFalse : bits .one = false :=
        Bool.eq_false_of_not_eq_true hone
      have honeTest : afterOne (decodedValue regs) = 0 := by
        rw [honeValue, honeFalse]
        rfl
      obtain ⟨afterBlank, hblankRun, hblankValueRaw,
          hblankContext⟩ :=
        readCellBit_runs tm slot tape .blank regs blockLength offset
          code word hoffset afterOne honeContext
      have hblankValue :
          afterBlank (decodedValue regs) = (bits .blank).toNat := by
        simpa [bits, cellBits] using hblankValueRaw
      by_cases hblank : bits .blank = true
      · obtain ⟨final, hsetRun, hsetValue, hfinalContext⟩ :=
          setDecoded_runs tm regs blockLength offset code word
            (CompactValueCodeSemantics.gammaCode .blank)
            afterBlank hblankContext
        have hblankTest :
            afterBlank (decodedValue regs) ≠ 0 := by
          rw [hblankValue, hblank]
          decide
        have honeZeroBranch :
            Runs
              (Cmd.seq
                (readCellBit tm slot tape .blank regs)
                (.ifZero (decodedValue regs)
                  (Cmd.seq
                    (readCellBit tm slot tape .start regs)
                    (.ifZero (decodedValue regs)
                      (.basic
                        (.imm (decodedValue regs)
                          (CompactValueCodeSemantics.gammaCode .blank)))
                      (.basic
                        (.imm (decodedValue regs)
                          (CompactValueCodeSemantics.gammaCode .start)))))
                  (.basic
                    (.imm (decodedValue regs)
                      (CompactValueCodeSemantics.gammaCode .blank)))))
              afterOne final :=
          Runs.seq hblankRun
            (Runs.ifNonzero hblankTest hsetRun)
        have hzeroBranch :
            Runs
              (Cmd.seq
                (readCellBit tm slot tape .one regs)
                (.ifZero (decodedValue regs)
                  (Cmd.seq
                    (readCellBit tm slot tape .blank regs)
                    (.ifZero (decodedValue regs)
                      (Cmd.seq
                        (readCellBit tm slot tape .start regs)
                        (.ifZero (decodedValue regs)
                          (.basic
                            (.imm (decodedValue regs)
                              (CompactValueCodeSemantics.gammaCode .blank)))
                          (.basic
                            (.imm (decodedValue regs)
                              (CompactValueCodeSemantics.gammaCode .start)))))
                      (.basic
                        (.imm (decodedValue regs)
                          (CompactValueCodeSemantics.gammaCode .blank)))))
                  (.basic
                    (.imm (decodedValue regs)
                      (CompactValueCodeSemantics.gammaCode .one)))))
              afterZero final :=
          Runs.seq honeRun
            (Runs.ifZero honeTest honeZeroBranch)
        refine ⟨final, ?_, ?_, hfinalContext⟩
        · simpa [decodeCell] using
            Runs.seq hzeroRun
              (Runs.ifZero hzeroTest hzeroBranch)
        · simpa [NeighborhoodExecutableEvaluation.decodeGamma, bits,
            hzeroFalse, honeFalse, hblank] using hsetValue
      · have hblankFalse : bits .blank = false :=
          Bool.eq_false_of_not_eq_true hblank
        have hblankTest :
            afterBlank (decodedValue regs) = 0 := by
          rw [hblankValue, hblankFalse]
          rfl
        obtain ⟨afterStart, hstartRun, hstartValueRaw,
            hstartContext⟩ :=
          readCellBit_runs tm slot tape .start regs blockLength offset
            code word hoffset afterBlank hblankContext
        have hstartValue :
            afterStart (decodedValue regs) =
              (bits .start).toNat := by
          simpa [bits, cellBits] using hstartValueRaw
        by_cases hstart : bits .start = true
        · obtain ⟨final, hsetRun, hsetValue, hfinalContext⟩ :=
            setDecoded_runs tm regs blockLength offset code word
              (CompactValueCodeSemantics.gammaCode .start)
              afterStart hstartContext
          have hstartTest :
              afterStart (decodedValue regs) ≠ 0 := by
            rw [hstartValue, hstart]
            decide
          have hblankZeroBranch :
              Runs
                (Cmd.seq
                  (readCellBit tm slot tape .start regs)
                  (.ifZero (decodedValue regs)
                    (.basic
                      (.imm (decodedValue regs)
                        (CompactValueCodeSemantics.gammaCode .blank)))
                    (.basic
                      (.imm (decodedValue regs)
                        (CompactValueCodeSemantics.gammaCode .start)))))
                afterBlank final :=
            Runs.seq hstartRun
              (Runs.ifNonzero hstartTest hsetRun)
          have honeZeroBranch :
              Runs
                (Cmd.seq
                  (readCellBit tm slot tape .blank regs)
                  (.ifZero (decodedValue regs)
                    (Cmd.seq
                      (readCellBit tm slot tape .start regs)
                      (.ifZero (decodedValue regs)
                        (.basic
                          (.imm (decodedValue regs)
                            (CompactValueCodeSemantics.gammaCode .blank)))
                        (.basic
                          (.imm (decodedValue regs)
                            (CompactValueCodeSemantics.gammaCode .start)))))
                    (.basic
                      (.imm (decodedValue regs)
                        (CompactValueCodeSemantics.gammaCode .blank)))))
                afterOne final :=
            Runs.seq hblankRun
              (Runs.ifZero hblankTest hblankZeroBranch)
          have hzeroBranch :
              Runs
                (Cmd.seq
                  (readCellBit tm slot tape .one regs)
                  (.ifZero (decodedValue regs)
                    (Cmd.seq
                      (readCellBit tm slot tape .blank regs)
                      (.ifZero (decodedValue regs)
                        (Cmd.seq
                          (readCellBit tm slot tape .start regs)
                          (.ifZero (decodedValue regs)
                            (.basic
                              (.imm (decodedValue regs)
                                (CompactValueCodeSemantics.gammaCode
                                  .blank)))
                            (.basic
                              (.imm (decodedValue regs)
                                (CompactValueCodeSemantics.gammaCode
                                  .start)))))
                        (.basic
                          (.imm (decodedValue regs)
                            (CompactValueCodeSemantics.gammaCode .blank)))))
                    (.basic
                      (.imm (decodedValue regs)
                        (CompactValueCodeSemantics.gammaCode .one)))))
                afterZero final :=
            Runs.seq honeRun
              (Runs.ifZero honeTest honeZeroBranch)
          refine ⟨final, ?_, ?_, hfinalContext⟩
          · simpa [decodeCell] using
              Runs.seq hzeroRun
                (Runs.ifZero hzeroTest hzeroBranch)
          · simpa [NeighborhoodExecutableEvaluation.decodeGamma, bits,
              hzeroFalse, honeFalse, hblankFalse, hstart] using
                hsetValue
        · have hstartFalse : bits .start = false :=
            Bool.eq_false_of_not_eq_true hstart
          have hstartTest :
              afterStart (decodedValue regs) = 0 := by
            rw [hstartValue, hstartFalse]
            rfl
          obtain ⟨final, hsetRun, hsetValue, hfinalContext⟩ :=
            setDecoded_runs tm regs blockLength offset code word
              (CompactValueCodeSemantics.gammaCode .blank)
              afterStart hstartContext
          have hblankZeroBranch :
              Runs
                (Cmd.seq
                  (readCellBit tm slot tape .start regs)
                  (.ifZero (decodedValue regs)
                    (.basic
                      (.imm (decodedValue regs)
                        (CompactValueCodeSemantics.gammaCode .blank)))
                    (.basic
                      (.imm (decodedValue regs)
                        (CompactValueCodeSemantics.gammaCode .start)))))
                afterBlank final :=
            Runs.seq hstartRun (Runs.ifZero hstartTest hsetRun)
          have honeZeroBranch :
              Runs
                (Cmd.seq
                  (readCellBit tm slot tape .blank regs)
                  (.ifZero (decodedValue regs)
                    (Cmd.seq
                      (readCellBit tm slot tape .start regs)
                      (.ifZero (decodedValue regs)
                        (.basic
                          (.imm (decodedValue regs)
                            (CompactValueCodeSemantics.gammaCode .blank)))
                        (.basic
                          (.imm (decodedValue regs)
                            (CompactValueCodeSemantics.gammaCode .start)))))
                    (.basic
                      (.imm (decodedValue regs)
                        (CompactValueCodeSemantics.gammaCode .blank)))))
                afterOne final :=
            Runs.seq hblankRun
              (Runs.ifZero hblankTest hblankZeroBranch)
          have hzeroBranch :
              Runs
                (Cmd.seq
                  (readCellBit tm slot tape .one regs)
                  (.ifZero (decodedValue regs)
                    (Cmd.seq
                      (readCellBit tm slot tape .blank regs)
                      (.ifZero (decodedValue regs)
                        (Cmd.seq
                          (readCellBit tm slot tape .start regs)
                          (.ifZero (decodedValue regs)
                            (.basic
                              (.imm (decodedValue regs)
                                (CompactValueCodeSemantics.gammaCode
                                  .blank)))
                            (.basic
                              (.imm (decodedValue regs)
                                (CompactValueCodeSemantics.gammaCode
                                  .start)))))
                        (.basic
                          (.imm (decodedValue regs)
                            (CompactValueCodeSemantics.gammaCode .blank)))))
                    (.basic
                      (.imm (decodedValue regs)
                        (CompactValueCodeSemantics.gammaCode .one)))))
                afterZero final :=
            Runs.seq honeRun
              (Runs.ifZero honeTest honeZeroBranch)
          refine ⟨final, ?_, ?_, hfinalContext⟩
          · simpa [decodeCell] using
              Runs.seq hzeroRun
                (Runs.ifZero hzeroTest hzeroBranch)
          · simpa [NeighborhoodExecutableEvaluation.decodeGamma, bits,
              hzeroFalse, honeFalse, hblankFalse, hstartFalse] using
                hsetValue

private theorem pushDecoded_context_runs
    (tm : TM workTapeCount)
    (regs : NeighborhoodTrial.Registers controller)
    (blockLength offset code word value : ℕ)
    (store : Store)
    (hcontext :
      AssignmentContext tm blockLength offset code word regs store)
    (hvalue : store (decodedValue regs) = value) :
    ∃ final,
      Runs (pushDecoded tm regs) store final ∧
      AssignmentContext tm blockLength offset code
        (PackedDigits.push
          (PackedLocalConfiguration.radix tm) value word)
        regs final := by
  obtain ⟨final, hrun, hword, houtside⟩ :=
    pushDecoded_runs tm regs store word value hcontext.word_eq hvalue
  refine ⟨final, hrun, ?_⟩
  refine
    { blockLength_eq := ?_
      cursor_eq := ?_
      assignment_eq := ?_
      one_eq := ?_
      word_eq := hword
      chunkCount_eq := ?_
      chunkRadix_eq := ?_ }
  · rw [houtside (Layout.blockLength regs)]
    · exact hcontext.blockLength_eq
    · simp [pushDecodedFootprint, bankRegisters,
        PackedLocalHeadScan.bankRegisters, PackedLocalHeadScan.bankMap,
        NeighborhoodProgram.BankRegisters.mainStack,
        NeighborhoodProgram.BankRegisters.mainMap,
        regs.injective.eq_iff]
  · rw [houtside (cursor regs)]
    · exact hcontext.cursor_eq
    · simp [pushDecodedFootprint, cursor, CombineValue.rangeRegisters,
        bankRegisters, PackedLocalHeadScan.bankRegisters,
        PackedLocalHeadScan.bankMap,
        NeighborhoodProgram.BankRegisters.mainStack,
        NeighborhoodProgram.BankRegisters.mainMap,
        regs.injective.eq_iff]
  · rw [houtside (CombineValue.rangeRegisters regs).remaining]
    · exact hcontext.assignment_eq
    · simp [pushDecodedFootprint, CombineValue.rangeRegisters,
        bankRegisters, PackedLocalHeadScan.bankRegisters,
        PackedLocalHeadScan.bankMap,
        NeighborhoodProgram.BankRegisters.mainStack,
        NeighborhoodProgram.BankRegisters.mainMap,
        regs.injective.eq_iff]
  · rw [houtside (CombineValue.rangeRegisters regs).one]
    · exact hcontext.one_eq
    · simp [pushDecodedFootprint, CombineValue.rangeRegisters,
        bankRegisters, PackedLocalHeadScan.bankRegisters,
        PackedLocalHeadScan.bankMap,
        NeighborhoodProgram.BankRegisters.mainStack,
        NeighborhoodProgram.BankRegisters.mainMap,
        regs.injective.eq_iff]
  · rw [houtside (Layout.chunkCount regs)]
    · exact hcontext.chunkCount_eq
    · simp [pushDecodedFootprint, bankRegisters,
        PackedLocalHeadScan.bankRegisters, PackedLocalHeadScan.bankMap,
        NeighborhoodProgram.BankRegisters.mainStack,
        NeighborhoodProgram.BankRegisters.mainMap,
        regs.injective.eq_iff]
  · rw [houtside (Layout.chunkRadix regs)]
    · exact hcontext.chunkRadix_eq
    · simp [pushDecodedFootprint, bankRegisters,
        PackedLocalHeadScan.bankRegisters, PackedLocalHeadScan.bankMap,
        NeighborhoodProgram.BankRegisters.mainStack,
        NeighborhoodProgram.BankRegisters.mainMap,
        regs.injective.eq_iff]

private theorem pushCell_runs
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (slot : Slot)
    (tape : TapeIndex workTapeCount)
    (regs : NeighborhoodTrial.Registers controller)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (offset : ℕ) (hoffset : offset < blockLength)
    (code word : ℕ)
    (store : Store)
    (hcontext :
      AssignmentContext tm blockLength offset code word regs store) :
    let value :=
      CompactValueCodeSemantics.gammaCode
        ((LocalAssignmentSemantics.assignmentInputs
          tm order blockLength hpositive code
          (.content slot, tape)).cells ⟨offset, hoffset⟩)
    ∃ final,
      Runs (pushCell tm slot tape regs) store final ∧
      AssignmentContext tm blockLength offset code
        (PackedDigits.push
          (PackedLocalConfiguration.radix tm) value word)
        regs final := by
  dsimp only
  obtain ⟨decoded, hdecodeRun, hdecodeValue, hdecodeContext⟩ :=
    decodeCell_runs tm slot tape regs blockLength offset code word
      hoffset store hcontext
  have hdecodedSemantic :
      decoded (decodedValue regs) =
        CompactValueCodeSemantics.gammaCode
          ((LocalAssignmentSemantics.assignmentInputs
            tm order blockLength hpositive code
            (.content slot, tape)).cells ⟨offset, hoffset⟩) := by
    exact hdecodeValue.trans
      (congrArg CompactValueCodeSemantics.gammaCode
        (decodeGamma_cellBits tm order blockLength hpositive offset
          hoffset code slot tape))
  obtain ⟨final, hpushRun, hfinalContext⟩ :=
    pushDecoded_context_runs tm regs blockLength offset code word
      (CompactValueCodeSemantics.gammaCode
        ((LocalAssignmentSemantics.assignmentInputs
          tm order blockLength hpositive code
          (.content slot, tape)).cells ⟨offset, hoffset⟩))
      decoded hdecodeContext hdecodedSemantic
  refine ⟨final, ?_, hfinalContext⟩
  exact Runs.seq hdecodeRun hpushRun

private def blockDigit
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (code : ℕ) (slot : Slot) (tape : TapeIndex workTapeCount)
    (offset : ℕ) : ℕ :=
  if hoffset : offset < blockLength then
    CompactValueCodeSemantics.gammaCode
      ((LocalAssignmentSemantics.assignmentInputs
        tm order blockLength hpositive code
        (.content slot, tape)).cells ⟨offset, hoffset⟩)
  else
    CompactValueCodeSemantics.gammaCode .blank

private theorem decrementCursor_runs
    (tm : TM workTapeCount)
    (regs : NeighborhoodTrial.Registers controller)
    (blockLength offset code word : ℕ)
    (store : Store)
    (hcontext :
      AssignmentContext tm blockLength (offset + 1) code word regs
        store) :
    ∃ final,
      Runs
        (.basic
          (.sub (cursor regs) (cursor regs)
            (CombineValue.rangeRegisters regs).one))
        store final ∧
      AssignmentContext tm blockLength offset code word regs final ∧
      ∀ address, address ≠ cursor regs →
        final address = store address := by
  let final :=
    (Basic.sub (cursor regs) (cursor regs)
      (CombineValue.rangeRegisters regs).one).exec store
  have houtside :
      ∀ address, address ≠ cursor regs →
        final address = store address := by
    intro address haddress
    simp [final, Basic.exec, Function.update_of_ne, haddress]
  refine ⟨final, Runs.basic _ _, ?_, houtside⟩
  refine
    { blockLength_eq := ?_
      cursor_eq := ?_
      assignment_eq := ?_
      one_eq := ?_
      word_eq := ?_
      chunkCount_eq := ?_
      chunkRadix_eq := ?_ }
  · rw [houtside (Layout.blockLength regs)
      (regs.injective.ne (by decide))]
    exact hcontext.blockLength_eq
  · simp [final, Basic.exec, hcontext.cursor_eq, hcontext.one_eq]
  · rw [houtside (CombineValue.rangeRegisters regs).remaining
      (regs.injective.ne (by decide))]
    exact hcontext.assignment_eq
  · rw [houtside (CombineValue.rangeRegisters regs).one
      (regs.injective.ne (by decide))]
    exact hcontext.one_eq
  · rw [houtside (packedWord regs)
      (regs.injective.ne (by decide))]
    exact hcontext.word_eq
  · rw [houtside (Layout.chunkCount regs)
      (regs.injective.ne (by decide))]
    exact hcontext.chunkCount_eq
  · rw [houtside (Layout.chunkRadix regs)
      (regs.injective.ne (by decide))]
    exact hcontext.chunkRadix_eq

private theorem pushBlockBody_runs
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (slot : Slot)
    (tape : TapeIndex workTapeCount)
    (regs : NeighborhoodTrial.Registers controller)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (offset : ℕ) (hoffset : offset < blockLength)
    (code word : ℕ)
    (store : Store)
    (hcontext :
      AssignmentContext tm blockLength (offset + 1) code word regs
        store) :
    ∃ final,
      Runs (pushBlockBody tm slot tape regs) store final ∧
      AssignmentContext tm blockLength offset code
        (PackedDigits.push
          (PackedLocalConfiguration.radix tm)
          (blockDigit tm order blockLength hpositive code slot tape
            offset)
          word)
        regs final := by
  obtain ⟨decremented, hdecrementRun, hdecrementedContext,
      _hdecrementedOutside⟩ :=
    decrementCursor_runs tm regs blockLength offset code word store
      hcontext
  obtain ⟨final, hpushRun, hfinalContextRaw⟩ :=
    pushCell_runs tm order slot tape regs blockLength hpositive offset
      hoffset code word decremented hdecrementedContext
  have hfinalContext :
      AssignmentContext tm blockLength offset code
        (PackedDigits.push
          (PackedLocalConfiguration.radix tm)
          (blockDigit tm order blockLength hpositive code slot tape
            offset)
          word)
        regs final := by
    simpa [blockDigit, hoffset] using hfinalContextRaw
  exact
    ⟨final, Runs.seq hdecrementRun hpushRun, hfinalContext⟩

private theorem prependFrom_push_last
    (base : ℕ) (digits : ℕ → ℕ)
    (start count word : ℕ) :
    PackedDigits.prependFrom base digits start count
        (PackedDigits.push base (digits (start + count)) word) =
      PackedDigits.prependFrom base digits start (count + 1) word := by
  induction count generalizing start with
  | zero =>
      rfl
  | succ count ih =>
      simp only [PackedDigits.prependFrom]
      congr 1
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (start + 1)

private theorem word_eq_of_digits_drop
    (base count first second : ℕ)
    (hdigits :
      ∀ index, index < count →
        PackedDigits.digit base first index =
          PackedDigits.digit base second index)
    (hdrop :
      PackedDigits.drop base count first =
        PackedDigits.drop base count second) :
    first = second := by
  induction count generalizing first second with
  | zero =>
      simpa [PackedDigits.drop] using hdrop
  | succ count ih =>
      have hzero := hdigits 0 (by omega)
      have htailDigits :
          ∀ index, index < count →
            PackedDigits.digit base
                (PackedDigits.pop base first) index =
              PackedDigits.digit base
                (PackedDigits.pop base second) index := by
        intro index hindex
        rw [PackedDigits.digit_pop, PackedDigits.digit_pop]
        exact hdigits (index + 1) (by omega)
      have htailDrop :
          PackedDigits.drop base count
              (PackedDigits.pop base first) =
            PackedDigits.drop base count
              (PackedDigits.pop base second) := by
        simpa [PackedDigits.drop] using hdrop
      have htail := ih _ _ htailDigits htailDrop
      calc
        first =
            PackedDigits.push base
              (PackedDigits.digit base first 0)
              (PackedDigits.pop base first) :=
          (PackedDigits.push_digit_pop base first).symm
        _ =
            PackedDigits.push base
              (PackedDigits.digit base second 0)
              (PackedDigits.pop base second) := by
          rw [hzero, htail]
        _ = second :=
          PackedDigits.push_digit_pop base second

private theorem prependFrom_congr
    (base : ℕ) (first second : ℕ → ℕ)
    (firstStart secondStart count suffix : ℕ)
    (heq :
      ∀ offset, offset < count →
        first (firstStart + offset) =
          second (secondStart + offset)) :
    PackedDigits.prependFrom base first firstStart count suffix =
      PackedDigits.prependFrom base second secondStart count suffix := by
  induction count generalizing firstStart secondStart with
  | zero =>
      rfl
  | succ count ih =>
      simp only [PackedDigits.prependFrom]
      congr 1
      · simpa using heq 0 (by omega)
      · apply ih
        intro offset hoffset
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          heq (offset + 1) (by omega)

private theorem prependFrom_append
    (base : ℕ) (digits : ℕ → ℕ)
    (start first second suffix : ℕ) :
    PackedDigits.prependFrom base digits start first
        (PackedDigits.prependFrom base digits (start + first)
          second suffix) =
      PackedDigits.prependFrom base digits start (first + second)
        suffix := by
  induction first generalizing start with
  | zero =>
      simp [PackedDigits.prependFrom]
  | succ first ih =>
      rw [Nat.succ_add]
      simp only [PackedDigits.prependFrom]
      congr 1
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (start + 1)

private theorem threePrepend_eq
    (base blockLength suffix : ℕ)
    (first second third target : ℕ → ℕ)
    (hfirst :
      ∀ offset, offset < blockLength →
        first offset = target offset)
    (hsecond :
      ∀ offset, offset < blockLength →
        second offset = target (blockLength + offset))
    (hthird :
      ∀ offset, offset < blockLength →
        third offset = target (2 * blockLength + offset)) :
    PackedDigits.prependFrom base first 0 blockLength
        (PackedDigits.prependFrom base second 0 blockLength
          (PackedDigits.prependFrom base third 0 blockLength suffix)) =
      PackedDigits.prependFrom base target 0
        (3 * blockLength) suffix := by
  calc
    _ =
        PackedDigits.prependFrom base target 0 blockLength
          (PackedDigits.prependFrom base second 0 blockLength
            (PackedDigits.prependFrom base third 0 blockLength
              suffix)) := by
      apply prependFrom_congr
      intro offset hoffset
      simpa using hfirst offset hoffset
    _ =
        PackedDigits.prependFrom base target 0 blockLength
          (PackedDigits.prependFrom base target blockLength blockLength
            (PackedDigits.prependFrom base third 0 blockLength
              suffix)) := by
      congr 1
      apply prependFrom_congr
      intro offset hoffset
      simpa using hsecond offset hoffset
    _ =
        PackedDigits.prependFrom base target 0 blockLength
          (PackedDigits.prependFrom base target blockLength blockLength
            (PackedDigits.prependFrom base target
              (2 * blockLength) blockLength suffix)) := by
      congr 1
      congr 1
      apply prependFrom_congr
      intro offset hoffset
      simpa using hthird offset hoffset
    _ =
        PackedDigits.prependFrom base target 0
          (blockLength + blockLength)
          (PackedDigits.prependFrom base target
            (2 * blockLength) blockLength suffix) := by
      simpa [two_mul] using
        prependFrom_append base target 0 blockLength blockLength
          (PackedDigits.prependFrom base target
            (2 * blockLength) blockLength suffix)
    _ =
        PackedDigits.prependFrom base target 0
          (3 * blockLength) suffix := by
      convert
        prependFrom_append base target 0
          (blockLength + blockLength) blockLength suffix using 1 <;>
        ring_nf

private theorem pushBlockLoop_runs
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (slot : Slot)
    (tape : TapeIndex workTapeCount)
    (regs : NeighborhoodTrial.Registers controller)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (code : ℕ) :
    ∀ count word store,
      count ≤ blockLength →
      AssignmentContext tm blockLength count code word regs store →
      ∃ final,
        Runs
          (.whileNonzero (cursor regs)
            (pushBlockBody tm slot tape regs))
          store final ∧
        AssignmentContext tm blockLength 0 code
          (PackedDigits.prependFrom
            (PackedLocalConfiguration.radix tm)
            (blockDigit tm order blockLength hpositive code slot tape)
            0 count word)
          regs final := by
  intro count
  induction count with
  | zero =>
      intro word store _hcount hcontext
      refine ⟨store, Runs.whileZero hcontext.cursor_eq, ?_⟩
      simpa [PackedDigits.prependFrom] using hcontext
  | succ count ih =>
      intro word store hcount hcontext
      have htest : store (cursor regs) ≠ 0 := by
        rw [hcontext.cursor_eq]
        omega
      have hoffset : count < blockLength := by
        omega
      obtain ⟨afterBody, hbodyRun, hbodyContext⟩ :=
        pushBlockBody_runs tm order slot tape regs blockLength
          hpositive count hoffset code word store hcontext
      obtain ⟨final, hloopRun, hfinalContextRaw⟩ :=
        ih
          (PackedDigits.push
            (PackedLocalConfiguration.radix tm)
            (blockDigit tm order blockLength hpositive code slot tape
              count)
            word)
          afterBody (by omega) hbodyContext
      have hlast :=
        prependFrom_push_last
          (PackedLocalConfiguration.radix tm)
          (blockDigit tm order blockLength hpositive code slot tape)
          0 count word
      have hfinalContext :
          AssignmentContext tm blockLength 0 code
            (PackedDigits.prependFrom
              (PackedLocalConfiguration.radix tm)
              (blockDigit tm order blockLength hpositive code slot tape)
              0 (count + 1) word)
            regs final := by
        rw [← hlast]
        simpa using hfinalContextRaw
      exact
        ⟨final,
          Runs.whileNonzero htest hbodyRun hloopRun,
          hfinalContext⟩

private theorem copyCursor_runs
    (tm : TM workTapeCount)
    (regs : NeighborhoodTrial.Registers controller)
    (blockLength offset code word : ℕ)
    (store : Store)
    (hcontext :
      AssignmentContext tm blockLength offset code word regs store) :
    ∃ final,
      Runs
        (copy (cursor regs) (Layout.blockLength regs))
        store final ∧
      AssignmentContext tm blockLength blockLength code word regs final := by
  obtain ⟨final, hrun, hcursor, houtside⟩ :=
    copy_runs (cursor regs) (Layout.blockLength regs) store
      (regs.injective.ne (by decide))
  refine ⟨final, hrun, ?_⟩
  refine
    { blockLength_eq := ?_
      cursor_eq := hcursor.trans hcontext.blockLength_eq
      assignment_eq := ?_
      one_eq := ?_
      word_eq := ?_
      chunkCount_eq := ?_
      chunkRadix_eq := ?_ }
  · rw [houtside (Layout.blockLength regs)
      (regs.injective.ne (by decide))]
    exact hcontext.blockLength_eq
  · rw [houtside (CombineValue.rangeRegisters regs).remaining
      (regs.injective.ne (by decide))]
    exact hcontext.assignment_eq
  · rw [houtside (CombineValue.rangeRegisters regs).one
      (regs.injective.ne (by decide))]
    exact hcontext.one_eq
  · rw [houtside (packedWord regs)
      (regs.injective.ne (by decide))]
    exact hcontext.word_eq
  · rw [houtside (Layout.chunkCount regs)
      (regs.injective.ne (by decide))]
    exact hcontext.chunkCount_eq
  · rw [houtside (Layout.chunkRadix regs)
      (regs.injective.ne (by decide))]
    exact hcontext.chunkRadix_eq

private theorem pushBlock_runs
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (slot : Slot)
    (tape : TapeIndex workTapeCount)
    (regs : NeighborhoodTrial.Registers controller)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (offset code word : ℕ)
    (store : Store)
    (hcontext :
      AssignmentContext tm blockLength offset code word regs store) :
    ∃ final,
      Runs (pushBlock tm slot tape regs) store final ∧
      AssignmentContext tm blockLength 0 code
        (PackedDigits.prependFrom
          (PackedLocalConfiguration.radix tm)
          (blockDigit tm order blockLength hpositive code slot tape)
          0 blockLength word)
        regs final := by
  have honeRun :
      Runs
        (.basic
          (.imm (CombineValue.rangeRegisters regs).one 1))
        store store := by
    have heq :
        (Basic.imm
          (CombineValue.rangeRegisters regs).one 1).exec store =
            store := by
      funext address
      by_cases haddress :
          address = (CombineValue.rangeRegisters regs).one
      · subst address
        simp [Basic.exec, hcontext.one_eq]
      · simp [Basic.exec, Function.update_of_ne, haddress]
    simpa [heq] using
      Runs.basic
        (Basic.imm (CombineValue.rangeRegisters regs).one 1) store
  obtain ⟨positioned, hcopyRun, hpositionedContext⟩ :=
    copyCursor_runs tm regs blockLength offset code word store hcontext
  obtain ⟨final, hloopRun, hfinalContext⟩ :=
    pushBlockLoop_runs tm order slot tape regs blockLength hpositive
      code blockLength word positioned le_rfl hpositionedContext
  refine ⟨final, ?_, hfinalContext⟩
  simpa [pushBlock, Cmd.seqList] using
    Runs.seq honeRun (Runs.seq hcopyRun hloopRun)

private theorem pushBlankBody_runs
    (tm : TM workTapeCount)
    (regs : NeighborhoodTrial.Registers controller)
    (blockLength offset code word : ℕ)
    (store : Store)
    (hcontext :
      AssignmentContext tm blockLength (offset + 1) code word regs
        store) :
    ∃ final,
      Runs (pushBlankBody tm regs) store final ∧
      AssignmentContext tm blockLength offset code
        (PackedDigits.push
          (PackedLocalConfiguration.radix tm)
          (CompactValueCodeSemantics.gammaCode .blank)
          word)
        regs final := by
  obtain ⟨decremented, hdecrementRun, hdecrementedContext,
      _hdecrementedOutside⟩ :=
    decrementCursor_runs tm regs blockLength offset code word store
      hcontext
  obtain ⟨decoded, hsetRun, hdecodedValue, hdecodedContext⟩ :=
    setDecoded_runs tm regs blockLength offset code word
      (CompactValueCodeSemantics.gammaCode .blank)
      decremented hdecrementedContext
  obtain ⟨final, hpushRun, hfinalContext⟩ :=
    pushDecoded_context_runs tm regs blockLength offset code word
      (CompactValueCodeSemantics.gammaCode .blank)
      decoded hdecodedContext hdecodedValue
  refine ⟨final, ?_, hfinalContext⟩
  simpa [pushBlankBody, Cmd.seqList] using
    Runs.seq hdecrementRun (Runs.seq hsetRun hpushRun)

private theorem pushBlankLoop_runs
    (tm : TM workTapeCount)
    (regs : NeighborhoodTrial.Registers controller)
    (blockLength code : ℕ) :
    ∀ count word store,
      count ≤ blockLength →
      AssignmentContext tm blockLength count code word regs store →
      ∃ final,
        Runs
          (.whileNonzero (cursor regs) (pushBlankBody tm regs))
          store final ∧
        AssignmentContext tm blockLength 0 code
          (PackedDigits.prependFrom
            (PackedLocalConfiguration.radix tm)
            (fun _ => CompactValueCodeSemantics.gammaCode .blank)
            0 count word)
          regs final := by
  intro count
  induction count with
  | zero =>
      intro word store _hcount hcontext
      refine ⟨store, Runs.whileZero hcontext.cursor_eq, ?_⟩
      simpa [PackedDigits.prependFrom] using hcontext
  | succ count ih =>
      intro word store hcount hcontext
      have htest : store (cursor regs) ≠ 0 := by
        rw [hcontext.cursor_eq]
        omega
      obtain ⟨afterBody, hbodyRun, hbodyContext⟩ :=
        pushBlankBody_runs tm regs blockLength count code word store
          hcontext
      obtain ⟨final, hloopRun, hfinalContextRaw⟩ :=
        ih
          (PackedDigits.push
            (PackedLocalConfiguration.radix tm)
            (CompactValueCodeSemantics.gammaCode .blank)
            word)
          afterBody (by omega) hbodyContext
      have hlast :=
        prependFrom_push_last
          (PackedLocalConfiguration.radix tm)
          (fun _ => CompactValueCodeSemantics.gammaCode .blank)
          0 count word
      have hfinalContext :
          AssignmentContext tm blockLength 0 code
            (PackedDigits.prependFrom
              (PackedLocalConfiguration.radix tm)
              (fun _ =>
                CompactValueCodeSemantics.gammaCode .blank)
              0 (count + 1) word)
            regs final := by
        rw [← hlast]
        simpa using hfinalContextRaw
      exact
        ⟨final,
          Runs.whileNonzero htest hbodyRun hloopRun,
          hfinalContext⟩

private theorem pushBlankBlock_runs
    (tm : TM workTapeCount)
    (regs : NeighborhoodTrial.Registers controller)
    (blockLength offset code word : ℕ)
    (store : Store)
    (hcontext :
      AssignmentContext tm blockLength offset code word regs store) :
    ∃ final,
      Runs (pushBlankBlock tm regs) store final ∧
      AssignmentContext tm blockLength 0 code
        (PackedDigits.prependFrom
          (PackedLocalConfiguration.radix tm)
          (fun _ => CompactValueCodeSemantics.gammaCode .blank)
          0 blockLength word)
        regs final := by
  have honeRun :
      Runs
        (.basic
          (.imm (CombineValue.rangeRegisters regs).one 1))
        store store := by
    have heq :
        (Basic.imm
          (CombineValue.rangeRegisters regs).one 1).exec store =
            store := by
      funext address
      by_cases haddress :
          address = (CombineValue.rangeRegisters regs).one
      · subst address
        simp [Basic.exec, hcontext.one_eq]
      · simp [Basic.exec, Function.update_of_ne, haddress]
    simpa [heq] using
      Runs.basic
        (Basic.imm (CombineValue.rangeRegisters regs).one 1) store
  obtain ⟨positioned, hcopyRun, hpositionedContext⟩ :=
    copyCursor_runs tm regs blockLength offset code word store hcontext
  obtain ⟨final, hloopRun, hfinalContext⟩ :=
    pushBlankLoop_runs tm regs blockLength code blockLength word
      positioned le_rfl hpositionedContext
  refine ⟨final, ?_, hfinalContext⟩
  simpa [pushBlankBlock, Cmd.seqList] using
    Runs.seq honeRun (Runs.seq hcopyRun hloopRun)

private def headPosition
    (tm : TM workTapeCount)
    (blockLength : ℕ) (remainder : ℕ)
    (hremainder : remainder < blockLength) :
    Fin
      (NeighborhoodExecutableEvaluation.payloadWidth tm blockLength) :=
  ⟨Fintype.card tm.Q + remainder, by
    change
      Fintype.card tm.Q + remainder <
        ComputationGraph.CompactEncoding.width blockLength tm.Q
    rw [ComputationGraph.CompactEncoding.width_eq]
    omega⟩

private def headBits
    (tm : TM workTapeCount)
    (blockLength code : ℕ)
    (tape : TapeIndex workTapeCount)
    (remainder : ℕ) : Bool :=
  if hremainder : remainder < blockLength then
    AssignmentCodeSemantics.assignmentBits
      (NeighborhoodExecutableEvaluation.payloadWidth tm blockLength)
      (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount)
      code
      (childIndex workTapeCount (.chronological, tape))
      (headPosition tm blockLength remainder hremainder)
  else
    false

private theorem headBits_eq_bitsAt
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (blockLength code : ℕ) (tape : TapeIndex workTapeCount)
    (remainder : Fin blockLength) :
    headBits tm blockLength code tape remainder.val =
      NeighborhoodExecutableEvaluation.bitsAt
        (NeighborhoodExecutableEvaluation.FiniteEncoding.ofStateOrder
          order blockLength)
        (AssignmentCodeSemantics.assignmentBits
          (NeighborhoodExecutableEvaluation.payloadWidth tm blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount)
          code
          (childIndex workTapeCount (.chronological, tape)))
        (.inr (.inl remainder)) := by
  unfold headBits NeighborhoodExecutableEvaluation.bitsAt
  simp only [remainder.isLt, dite_true]
  apply congrArg
    (AssignmentCodeSemantics.assignmentBits
      (NeighborhoodExecutableEvaluation.payloadWidth tm blockLength)
      (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount)
      code (childIndex workTapeCount (.chronological, tape)))
  apply Fin.ext
  simp [headPosition,
    NeighborhoodExecutableEvaluation.FiniteEncoding.ofStateOrder,
    NeighborhoodExecutableEvaluation.FiniteEncoding.coordinateEquiv]

private theorem prepareHeadPosition_runs
    (tm : TM workTapeCount)
    (regs : NeighborhoodTrial.Registers controller)
    (blockLength start count code word : ℕ)
    (hstartCount : start + count = blockLength)
    (store : Store)
    (hcontext :
      AssignmentContext tm blockLength count code word regs store) :
    ∃ final,
      Runs (prepareHeadPosition tm regs) store final ∧
      final (payloadPosition regs) =
        Fintype.card tm.Q + start ∧
      AssignmentContext tm blockLength count code word regs final := by
  let ops : List Basic :=
    [.imm (payloadPosition regs) (Fintype.card tm.Q),
      .add (payloadPosition regs) (payloadPosition regs)
        (Layout.blockLength regs),
      .sub (payloadPosition regs) (payloadPosition regs)
        (cursor regs),
      .imm (bankRegisters regs).value 0]
  let final := Basic.execList ops store
  have houtside :
      ∀ address,
        address ≠ payloadPosition regs →
        address ≠ (bankRegisters regs).value →
        final address = store address := by
    intro address hpayload hvalue
    simp [final, ops, Basic.execList, Basic.exec,
      Function.update_of_ne, hpayload, hvalue]
  refine ⟨final, ?_, ?_, ?_⟩
  · simpa [prepareHeadPosition, ops] using basics_runs ops store
  · have hcursorPayload :
        cursor regs ≠ payloadPosition regs :=
      regs.injective.ne (by decide)
    simp [final, ops, Basic.execList, Basic.exec,
      hcontext.blockLength_eq, hcontext.cursor_eq,
      hcursorPayload,
      payloadPosition, AssignmentPayloadBit.payloadPosition,
      Layout.codecScratch, bankRegisters,
      PackedLocalHeadScan.bankRegisters,
      PackedLocalHeadScan.bankMap, regs.injective.eq_iff]
    omega
  · refine
      { blockLength_eq := ?_
        cursor_eq := ?_
        assignment_eq := ?_
        one_eq := ?_
        word_eq := ?_
        chunkCount_eq := ?_
        chunkRadix_eq := ?_ }
    · rw [houtside (Layout.blockLength regs)
        (regs.injective.ne (by decide))
        (regs.injective.ne (by decide))]
      exact hcontext.blockLength_eq
    · rw [houtside (cursor regs)
        (regs.injective.ne (by decide))
        (regs.injective.ne (by decide))]
      exact hcontext.cursor_eq
    · rw [houtside (CombineValue.rangeRegisters regs).remaining
        (regs.injective.ne (by decide))
        (regs.injective.ne (by decide))]
      exact hcontext.assignment_eq
    · rw [houtside (CombineValue.rangeRegisters regs).one
        (regs.injective.ne (by decide))
        (regs.injective.ne (by decide))]
      exact hcontext.one_eq
    · rw [houtside (packedWord regs)
        (regs.injective.ne (by decide))
        (regs.injective.ne (by decide))]
      exact hcontext.word_eq
    · rw [houtside (Layout.chunkCount regs)
        (regs.injective.ne (by decide))
        (regs.injective.ne (by decide))]
      exact hcontext.chunkCount_eq
    · rw [houtside (Layout.chunkRadix regs)
        (regs.injective.ne (by decide))
        (regs.injective.ne (by decide))]
      exact hcontext.chunkRadix_eq

private theorem readHeadBit_runs
    (tm : TM workTapeCount)
    (tape : TapeIndex workTapeCount)
    (regs : NeighborhoodTrial.Registers controller)
    (blockLength start count code word : ℕ)
    (hstart : start < blockLength)
    (hstartCount : start + count = blockLength)
    (store : Store)
    (hcontext :
      AssignmentContext tm blockLength count code word regs store) :
    ∃ positioned final,
      Runs (prepareHeadPosition tm regs) store positioned ∧
      Runs
        (AssignmentPayloadBit.read workTapeCount regs
          (childIndex workTapeCount (.chronological, tape)))
        positioned final ∧
      final (decodedValue regs) =
        (headBits tm blockLength code tape start).toNat ∧
      final (payloadPosition regs) =
        Fintype.card tm.Q + start ∧
      AssignmentContext tm blockLength count code word regs final := by
  obtain ⟨positioned, hpositionRun, hpositionValue,
      hpositionContext⟩ :=
    prepareHeadPosition_runs tm regs blockLength start count code word
      hstartCount store hcontext
  have hposition :
      positioned (payloadPosition regs) =
        (headPosition tm blockLength start hstart).val := by
    simpa [headPosition] using hpositionValue
  obtain ⟨final, hreadRun, hreadValueRaw, hfinalPosition,
      hfinalContext⟩ :=
    payloadRead_runs tm regs blockLength count code word
      (childIndex workTapeCount (.chronological, tape))
      (headPosition tm blockLength start hstart)
      positioned hpositionContext hposition
  refine ⟨positioned, final, hpositionRun, hreadRun, ?_, ?_,
    hfinalContext⟩
  · simpa [headBits, hstart] using hreadValueRaw
  · simpa [headPosition] using hfinalPosition

private def headSelection (bits : ℕ → Bool) :
    ℕ → ℕ → ℕ
  | _, 0 => 0
  | start, count + 1 =>
      if bits start then start + 1
      else headSelection bits (start + 1) count

private theorem headFalseBranch_runs
    (tm : TM workTapeCount)
    (regs : NeighborhoodTrial.Registers controller)
    (blockLength count code word : ℕ)
    (store : Store)
    (hcontext :
      AssignmentContext tm blockLength (count + 1) code word regs
        store) :
    ∃ final,
      Runs
        (Cmd.seq
          (.basic (.imm (payloadPosition regs) 0))
          (.basic
            (.sub (cursor regs) (cursor regs)
              (CombineValue.rangeRegisters regs).one)))
        store final ∧
      final (payloadPosition regs) = 0 ∧
      AssignmentContext tm blockLength count code word regs final := by
  obtain ⟨cleared, hclearRun, hclearValue, hclearContext⟩ :=
    setPayloadPosition_runs tm regs blockLength (count + 1) code word
      0 store hcontext
  obtain ⟨final, hdecrementRun, hfinalContext, houtside⟩ :=
    decrementCursor_runs tm regs blockLength count code word cleared
      hclearContext
  refine ⟨final, Runs.seq hclearRun hdecrementRun, ?_,
    hfinalContext⟩
  exact
    (houtside (payloadPosition regs)
      (regs.injective.ne (by decide))).trans hclearValue

private theorem headTrueBranch_runs
    (tm : TM workTapeCount)
    (regs : NeighborhoodTrial.Registers controller)
    (blockLength start count code word : ℕ)
    (store : Store)
    (hposition :
      store (payloadPosition regs) = Fintype.card tm.Q + start)
    (hcontext :
      AssignmentContext tm blockLength (count + 1) code word regs
        store) :
    ∃ final,
      Runs
        (Cmd.seqList
          [.basic
              (.imm (bankRegisters regs).value
                (Fintype.card tm.Q)),
            .basic
              (.sub (payloadPosition regs) (payloadPosition regs)
                (bankRegisters regs).value),
            .basic
              (.add (payloadPosition regs) (payloadPosition regs)
                (CombineValue.rangeRegisters regs).one),
            .basic (.imm (cursor regs) 0)])
        store final ∧
      final (payloadPosition regs) = start + 1 ∧
      AssignmentContext tm blockLength 0 code word regs final := by
  let ops : List Basic :=
    [.imm (bankRegisters regs).value (Fintype.card tm.Q),
      .sub (payloadPosition regs) (payloadPosition regs)
        (bankRegisters regs).value,
      .add (payloadPosition regs) (payloadPosition regs)
        (CombineValue.rangeRegisters regs).one,
      .imm (cursor regs) 0]
  let final := Basic.execList ops store
  have houtside :
      ∀ address,
        address ≠ (bankRegisters regs).value →
        address ≠ payloadPosition regs →
        address ≠ cursor regs →
        final address = store address := by
    intro address hvalue hpayload hcursor
    simp [final, ops, Basic.execList, Basic.exec,
      Function.update_of_ne, hvalue, hpayload, hcursor]
  refine ⟨final, ?_, ?_, ?_⟩
  · simpa [ops] using basics_runs ops store
  · simp [final, ops, Basic.execList, Basic.exec, hposition,
      payloadPosition,
      AssignmentPayloadBit.payloadPosition, Layout.codecScratch,
      cursor, CombineValue.rangeRegisters, bankRegisters,
      PackedLocalHeadScan.bankRegisters,
      PackedLocalHeadScan.bankMap, regs.injective.eq_iff]
    exact hcontext.one_eq
  · refine
      { blockLength_eq := ?_
        cursor_eq := ?_
        assignment_eq := ?_
        one_eq := ?_
        word_eq := ?_
        chunkCount_eq := ?_
        chunkRadix_eq := ?_ }
    · rw [houtside (Layout.blockLength regs)
        (regs.injective.ne (by decide))
        (regs.injective.ne (by decide))
        (regs.injective.ne (by decide))]
      exact hcontext.blockLength_eq
    · simp [final, ops, Basic.execList, Basic.exec]
    · rw [houtside (CombineValue.rangeRegisters regs).remaining
        (regs.injective.ne (by decide))
        (regs.injective.ne (by decide))
        (regs.injective.ne (by decide))]
      exact hcontext.assignment_eq
    · rw [houtside (CombineValue.rangeRegisters regs).one
        (regs.injective.ne (by decide))
        (regs.injective.ne (by decide))
        (regs.injective.ne (by decide))]
      exact hcontext.one_eq
    · rw [houtside (packedWord regs)
        (regs.injective.ne (by decide))
        (regs.injective.ne (by decide))
        (regs.injective.ne (by decide))]
      exact hcontext.word_eq
    · rw [houtside (Layout.chunkCount regs)
        (regs.injective.ne (by decide))
        (regs.injective.ne (by decide))
        (regs.injective.ne (by decide))]
      exact hcontext.chunkCount_eq
    · rw [houtside (Layout.chunkRadix regs)
        (regs.injective.ne (by decide))
        (regs.injective.ne (by decide))
        (regs.injective.ne (by decide))]
      exact hcontext.chunkRadix_eq

private theorem decodeHeadLoop_runs
    (tm : TM workTapeCount)
    (tape : TapeIndex workTapeCount)
    (regs : NeighborhoodTrial.Registers controller)
    (blockLength code : ℕ)
    (bits : ℕ → Bool)
    (hbits : bits = headBits tm blockLength code tape) :
    ∀ start count word store,
      start + count = blockLength →
      AssignmentContext tm blockLength count code word regs store →
      store (payloadPosition regs) = 0 →
      ∃ final,
        Runs
          (.whileNonzero (cursor regs)
            (decodeHeadBody tm tape regs))
          store final ∧
        final (payloadPosition regs) =
          headSelection bits start count ∧
        AssignmentContext tm blockLength 0 code word regs final := by
  intro start count
  induction count generalizing start with
  | zero =>
      intro word store _hstartCount hcontext hpayload
      refine ⟨store, Runs.whileZero hcontext.cursor_eq, ?_, ?_⟩
      · simpa [headSelection] using hpayload
      · simpa using hcontext
  | succ count ih =>
      intro word store hstartCount hcontext hpayload
      have hstart : start < blockLength := by omega
      have htest : store (cursor regs) ≠ 0 := by
        rw [hcontext.cursor_eq]
        omega
      obtain ⟨positioned, afterRead, hprepareRun, hreadRun,
          hreadValueRaw, hreadPosition, hreadContext⟩ :=
        readHeadBit_runs tm tape regs blockLength start (count + 1)
          code word hstart hstartCount store hcontext
      have hreadValue :
          afterRead (decodedValue regs) = (bits start).toNat := by
        simpa [hbits] using hreadValueRaw
      by_cases hbit : bits start = true
      · have hreadTest : afterRead (decodedValue regs) ≠ 0 := by
          rw [hreadValue, hbit]
          decide
        obtain ⟨afterBody, hbranchRun, hbodyPosition,
            hbodyContext⟩ :=
          headTrueBranch_runs tm regs blockLength start count code word
            afterRead hreadPosition hreadContext
        have hbodyRun :
            Runs (decodeHeadBody tm tape regs) store afterBody := by
          simpa [decodeHeadBody, Cmd.seqList] using
            Runs.seq hprepareRun
              (Runs.seq hreadRun
                (Runs.ifNonzero hreadTest hbranchRun))
        have hloopRun :
            Runs
              (.whileNonzero (cursor regs)
                (decodeHeadBody tm tape regs))
              afterBody afterBody :=
          Runs.whileZero hbodyContext.cursor_eq
        refine
          ⟨afterBody,
            Runs.whileNonzero htest hbodyRun hloopRun,
            ?_, hbodyContext⟩
        simpa [headSelection, hbit] using hbodyPosition
      · have hbitFalse : bits start = false :=
          Bool.eq_false_of_not_eq_true hbit
        have hreadTest : afterRead (decodedValue regs) = 0 := by
          rw [hreadValue, hbitFalse]
          rfl
        obtain ⟨afterBody, hbranchRun, hbodyPosition,
            hbodyContext⟩ :=
          headFalseBranch_runs tm regs blockLength count code word
            afterRead hreadContext
        have hbodyRun :
            Runs (decodeHeadBody tm tape regs) store afterBody := by
          simpa [decodeHeadBody, Cmd.seqList] using
            Runs.seq hprepareRun
              (Runs.seq hreadRun
                (Runs.ifZero hreadTest hbranchRun))
        obtain ⟨final, hloopRun, hfinalPosition,
            hfinalContext⟩ :=
          ih (start + 1) word afterBody (by omega) hbodyContext
            hbodyPosition
        refine
          ⟨final,
            Runs.whileNonzero htest hbodyRun hloopRun,
            ?_, hfinalContext⟩
        simpa [headSelection, hbitFalse] using hfinalPosition

private theorem headSelection_eq_find?
    (bits : ℕ → Bool) :
    ∀ start count,
      headSelection bits start count =
        match (List.range' start count).find? bits with
        | some index => index + 1
        | none => 0 := by
  intro start count
  induction count generalizing start with
  | zero =>
      rfl
  | succ count ih =>
      cases hbit : bits start <;>
        simp [headSelection, List.range'_succ, hbit, ih]

private theorem headSelection_firstTrueFin
    {count : ℕ} (hpositive : 0 < count)
    (bits : Fin count → Bool) :
    headSelection
          (fun index =>
            if h : index < count then bits ⟨index, h⟩ else false)
          0 count -
        1 =
      (NeighborhoodExecutableEvaluation.firstTrueFin
        ⟨0, hpositive⟩ bits).val := by
  rw [headSelection_eq_find?]
  rw [← List.range_eq_range']
  rw [← List.map_coe_finRange_eq_range]
  rw [List.find?_map]
  have hpredicate :
      ((fun index =>
        if h : index < count then bits ⟨index, h⟩ else false) ∘
        (fun index : Fin count => index.val)) = bits := by
    funext index
    simp only [Function.comp_apply, dif_pos index.isLt]
  rw [hpredicate]
  unfold NeighborhoodExecutableEvaluation.firstTrueFin
  generalize hfind :
    (List.finRange count).find? bits = found
  cases found <;> simp

private theorem headSelection_headBits
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (code : ℕ) (tape : TapeIndex workTapeCount) :
    headSelection (headBits tm blockLength code tape)
          0 blockLength -
        1 =
      (LocalAssignmentSemantics.assignmentInputs
        tm order blockLength hpositive code
        (.chronological, tape)).headRemainder.val := by
  let bits : Fin blockLength → Bool :=
    fun remainder =>
      NeighborhoodExecutableEvaluation.bitsAt
        (NeighborhoodExecutableEvaluation.FiniteEncoding.ofStateOrder
          order blockLength)
        (AssignmentCodeSemantics.assignmentBits
          (NeighborhoodExecutableEvaluation.payloadWidth tm blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount)
          code
          (childIndex workTapeCount (.chronological, tape)))
        (.inr (.inl remainder))
  have hheadBits :
      headBits tm blockLength code tape =
        fun remainder =>
          if h : remainder < blockLength then
            bits ⟨remainder, h⟩
          else
            false := by
    funext remainder
    by_cases hremainder : remainder < blockLength
    · simp only [hremainder, dite_true]
      simpa [bits] using
        headBits_eq_bitsAt tm order blockLength code tape
          ⟨remainder, hremainder⟩
    · simp [headBits, hremainder]
  rw [hheadBits]
  unfold LocalAssignmentSemantics.assignmentInputs
    NeighborhoodExecutableEvaluation.decodeBits
  exact headSelection_firstTrueFin hpositive bits

private theorem decodeHead_runs
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (tape : TapeIndex workTapeCount)
    (regs : NeighborhoodTrial.Registers controller)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (offset code word : ℕ)
    (store : Store)
    (hcontext :
      AssignmentContext tm blockLength offset code word regs store) :
    let head :=
      (LocalAssignmentSemantics.assignmentInputs
        tm order blockLength hpositive code
        (.chronological, tape)).headRemainder.val
    ∃ final,
      Runs (decodeHead tm tape regs) store final ∧
      final (cursor regs) = head ∧
      AssignmentContext tm blockLength head code word regs final := by
  dsimp only
  have honeRun :
      Runs
        (.basic
          (.imm (CombineValue.rangeRegisters regs).one 1))
        store store := by
    have heq :
        (Basic.imm
          (CombineValue.rangeRegisters regs).one 1).exec store =
            store := by
      funext address
      by_cases haddress :
          address = (CombineValue.rangeRegisters regs).one
      · subst address
        simp [Basic.exec, hcontext.one_eq]
      · simp [Basic.exec, Function.update_of_ne, haddress]
    simpa [heq] using
      Runs.basic
        (Basic.imm (CombineValue.rangeRegisters regs).one 1) store
  obtain ⟨copied, hcopyRun, hcopyContext⟩ :=
    copyCursor_runs tm regs blockLength offset code word store
      hcontext
  obtain ⟨positioned, hpositionRun, hpositionValue,
      hpositionContext⟩ :=
    setPayloadPosition_runs tm regs blockLength blockLength code word
      0 copied hcopyContext
  obtain ⟨looped, hloopRun, hloopPosition, hloopContext⟩ :=
    decodeHeadLoop_runs tm tape regs blockLength code
      (headBits tm blockLength code tape) rfl
      0 blockLength word positioned (by simp)
      hpositionContext hpositionValue
  have hselection :
      headSelection (headBits tm blockLength code tape)
            0 blockLength -
          1 =
        (LocalAssignmentSemantics.assignmentInputs
          tm order blockLength hpositive code
          (.chronological, tape)).headRemainder.val :=
    headSelection_headBits tm order blockLength hpositive code tape
  let final :=
    (Basic.sub (cursor regs) (payloadPosition regs)
      (CombineValue.rangeRegisters regs).one).exec looped
  have hfinalRun :
      Runs
        (.basic
          (.sub (cursor regs) (payloadPosition regs)
            (CombineValue.rangeRegisters regs).one))
        looped final :=
    Runs.basic _ _
  have houtside :
      ∀ address, address ≠ cursor regs →
        final address = looped address := by
    intro address haddress
    simp [final, Basic.exec, Function.update_of_ne, haddress]
  have hfinalCursor :
      final (cursor regs) =
        (LocalAssignmentSemantics.assignmentInputs
          tm order blockLength hpositive code
          (.chronological, tape)).headRemainder.val := by
    simp [final, Basic.exec, hloopPosition, hloopContext.one_eq,
      hselection]
  refine ⟨final, ?_, hfinalCursor, ?_⟩
  · simpa [decodeHead, Cmd.seqList] using
      Runs.seq honeRun
        (Runs.seq hcopyRun
          (Runs.seq hpositionRun
            (Runs.seq hloopRun hfinalRun)))
  · refine
      { blockLength_eq := ?_
        cursor_eq := hfinalCursor
        assignment_eq := ?_
        one_eq := ?_
        word_eq := ?_
        chunkCount_eq := ?_
        chunkRadix_eq := ?_ }
    · rw [houtside (Layout.blockLength regs)
        (regs.injective.ne (by decide))]
      exact hloopContext.blockLength_eq
    · rw [houtside (CombineValue.rangeRegisters regs).remaining
        (regs.injective.ne (by decide))]
      exact hloopContext.assignment_eq
    · rw [houtside (CombineValue.rangeRegisters regs).one
        (regs.injective.ne (by decide))]
      exact hloopContext.one_eq
    · rw [houtside (packedWord regs)
        (regs.injective.ne (by decide))]
      exact hloopContext.word_eq
    · rw [houtside (Layout.chunkCount regs)
        (regs.injective.ne (by decide))]
      exact hloopContext.chunkCount_eq
    · rw [houtside (Layout.chunkRadix regs)
        (regs.injective.ne (by decide))]
      exact hloopContext.chunkRadix_eq

private theorem markHead_runs
    (tm : TM workTapeCount)
    (regs : NeighborhoodTrial.Registers controller)
    (centerOffsetBlocks blockLength offset code word : ℕ)
    (store : Store)
    (hcontext :
      AssignmentContext tm blockLength offset code word regs store) :
    let index := offset + centerOffsetBlocks * blockLength
    let replacement :=
      PackedDigits.digit
          (PackedLocalConfiguration.radix tm) word index +
        4
    ∃ final,
      Runs (markHead tm centerOffsetBlocks regs) store final ∧
      AssignmentContext tm blockLength index code
        (NeighborhoodProgram.replaceAt
          (PackedLocalConfiguration.radix tm) word index replacement)
        regs final := by
  dsimp only
  let index := offset + centerOffsetBlocks * blockLength
  let replacement :=
    PackedDigits.digit
        (PackedLocalConfiguration.radix tm) word index +
      4
  let ops : List Basic :=
    [.imm (bankRegisters regs).value centerOffsetBlocks,
      .mul (bankRegisters regs).value
        (bankRegisters regs).value (Layout.blockLength regs),
      .add (cursor regs) (cursor regs)
        (bankRegisters regs).value]
  let centerSet :=
    (Basic.imm (bankRegisters regs).value
      centerOffsetBlocks).exec store
  let centerScaled :=
    (Basic.mul (bankRegisters regs).value
      (bankRegisters regs).value
      (Layout.blockLength regs)).exec centerSet
  let prepared := Basic.execList ops store
  have hcenterRun :
      Runs
        (.basic
          (.imm (bankRegisters regs).value centerOffsetBlocks))
        store centerSet :=
    Runs.basic _ _
  have hscaleRun :
      Runs
        (.basic
          (.mul (bankRegisters regs).value
            (bankRegisters regs).value
            (Layout.blockLength regs)))
        centerSet centerScaled :=
    Runs.basic _ _
  have hcursorRun :
      Runs
        (.basic
          (.add (cursor regs) (cursor regs)
            (bankRegisters regs).value))
        centerScaled prepared := by
    simpa [prepared, ops, Basic.execList, centerSet, centerScaled] using
      Runs.basic
        (Basic.add (cursor regs) (cursor regs)
          (bankRegisters regs).value)
        centerScaled
  have hprepareOutside :
      ∀ address,
        address ≠ (bankRegisters regs).value →
        address ≠ cursor regs →
        prepared address = store address := by
    intro address hvalue hcursor
    simp [prepared, ops, Basic.execList, Basic.exec,
      Function.update_of_ne, hvalue, hcursor]
  have hpreparedContext :
      AssignmentContext tm blockLength index code word regs prepared := by
    refine
      { blockLength_eq := ?_
        cursor_eq := ?_
        assignment_eq := ?_
        one_eq := ?_
        word_eq := ?_
        chunkCount_eq := ?_
        chunkRadix_eq := ?_ }
    · rw [hprepareOutside (Layout.blockLength regs)
        (regs.injective.ne (by decide))
        (regs.injective.ne (by decide))]
      exact hcontext.blockLength_eq
    · simp [prepared, ops, Basic.execList, Basic.exec, index,
        hcontext.blockLength_eq,
        cursor, CombineValue.rangeRegisters, bankRegisters,
        PackedLocalHeadScan.bankRegisters,
        PackedLocalHeadScan.bankMap, regs.injective.eq_iff]
      exact hcontext.cursor_eq
    · rw [hprepareOutside
        (CombineValue.rangeRegisters regs).remaining
        (regs.injective.ne (by decide))
        (regs.injective.ne (by decide))]
      exact hcontext.assignment_eq
    · rw [hprepareOutside
        (CombineValue.rangeRegisters regs).one
        (regs.injective.ne (by decide))
        (regs.injective.ne (by decide))]
      exact hcontext.one_eq
    · rw [hprepareOutside (packedWord regs)
        ((bankRegisters regs).index_ne (by decide))
        (regs.injective.ne (by decide))]
      exact hcontext.word_eq
    · rw [hprepareOutside (Layout.chunkCount regs)
        (regs.injective.ne (by decide))
        (regs.injective.ne (by decide))]
      exact hcontext.chunkCount_eq
    · rw [hprepareOutside (Layout.chunkRadix regs)
        (regs.injective.ne (by decide))
        (regs.injective.ne (by decide))]
      exact hcontext.chunkRadix_eq
  obtain ⟨initialized, hinitializeRun, hinitializedWord,
      hinitializedBase, hinitializedBasePred, hinitializedOne,
      hinitializedOutside⟩ :=
    initializeBank_runs tm regs prepared word
      hpreparedContext.word_eq
  have hinitializedCursor :
      initialized (cursor regs) = index := by
    rw [hinitializedOutside (cursor regs)]
    · exact hpreparedContext.cursor_eq
    all_goals
      exact regs.injective.ne (by decide)
  have hinitializedRemaining :
      initialized (CombineValue.rangeRegisters regs).remaining =
        code := by
    rw [hinitializedOutside
      (CombineValue.rangeRegisters regs).remaining]
    · exact hpreparedContext.assignment_eq
    all_goals
      exact regs.injective.ne (by decide)
  obtain ⟨indexed, hindexRun, hindexValue, hindexOutside⟩ :=
    copy_runs (bankRegisters regs).indexCount (cursor regs)
      initialized (regs.injective.ne (by decide))
  have hindexedWord :
      indexed (bankRegisters regs).word = word := by
    rw [hindexOutside (bankRegisters regs).word
      ((bankRegisters regs).index_ne (by decide))]
    exact hinitializedWord
  have hindexedBase :
      indexed (bankRegisters regs).base =
        PackedLocalConfiguration.radix tm := by
    rw [hindexOutside (bankRegisters regs).base
      ((bankRegisters regs).index_ne (by decide))]
    exact hinitializedBase
  have hindexedBasePred :
      indexed (bankRegisters regs).basePred =
        PackedLocalConfiguration.radix tm - 1 := by
    rw [hindexOutside (bankRegisters regs).basePred
      ((bankRegisters regs).index_ne (by decide))]
    exact hinitializedBasePred
  have hindexedOne :
      indexed (bankRegisters regs).one = 1 := by
    rw [hindexOutside (bankRegisters regs).one
      ((bankRegisters regs).index_ne (by decide))]
    exact hinitializedOne
  have hindexedIndex :
      indexed (bankRegisters regs).indexCount = index :=
    hindexValue.trans hinitializedCursor
  obtain ⟨read, hreadRun, hreadWord, _hreadBuffer,
      _hreadIndex, _hreadCompleted, hreadResult, hreadBase,
      hreadBasePred, hreadOne, _hreadReplacement⟩ :=
    NeighborhoodProgram.bankRead_runs (bankRegisters regs) indexed
      (PackedLocalConfiguration.radix tm) word index
      (by simp [PackedLocalConfiguration.radix]) hindexedWord
      hindexedBase hindexedBasePred hindexedOne hindexedIndex
  have hreadCursor :
      read (cursor regs) = index := by
    calc
      read (cursor regs) = indexed (cursor regs) := by
        exact Footprint.runs_eq_outside
          (NeighborhoodProgram.bankRead_sourceWritesWithin
            (bankRegisters regs))
          hreadRun
          (by
            simpa [cursor, CombineValue.rangeRegisters] using
              fixed_index_not_mem_bank regs 19 (by decide))
      _ = initialized (cursor regs) :=
        hindexOutside (cursor regs)
          (regs.injective.ne (by decide))
      _ = index := hinitializedCursor
  have hreadRemaining :
      read (CombineValue.rangeRegisters regs).remaining = code := by
    calc
      read (CombineValue.rangeRegisters regs).remaining =
          indexed (CombineValue.rangeRegisters regs).remaining := by
        exact Footprint.runs_eq_outside
          (NeighborhoodProgram.bankRead_sourceWritesWithin
            (bankRegisters regs))
          hreadRun
          (by
            simpa [CombineValue.rangeRegisters] using
              fixed_index_not_mem_bank regs 21 (by decide))
      _ = initialized
          (CombineValue.rangeRegisters regs).remaining :=
        hindexOutside
          (CombineValue.rangeRegisters regs).remaining
          (regs.injective.ne (by decide))
      _ = code := hinitializedRemaining
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
        replacement := by
    simp [replacementSet, valueSet, replacement, Basic.exec,
      bankRegisters, PackedLocalHeadScan.bankRegisters,
      PackedLocalHeadScan.bankMap, regs.injective.eq_iff]
    exact hreadResult
  have hreplacementWord :
      replacementSet (bankRegisters regs).word = word := by
    simp [replacementSet, valueSet, Basic.exec,
      bankRegisters, PackedLocalHeadScan.bankRegisters,
      PackedLocalHeadScan.bankMap, regs.injective.eq_iff]
    exact hreadWord
  have hreplacementBase :
      replacementSet (bankRegisters regs).base =
        PackedLocalConfiguration.radix tm := by
    simp [replacementSet, valueSet, Basic.exec,
      bankRegisters, PackedLocalHeadScan.bankRegisters,
      PackedLocalHeadScan.bankMap, regs.injective.eq_iff]
    exact hreadBase
  have hreplacementBasePred :
      replacementSet (bankRegisters regs).basePred =
        PackedLocalConfiguration.radix tm - 1 := by
    simp [replacementSet, valueSet, Basic.exec,
      bankRegisters, PackedLocalHeadScan.bankRegisters,
      PackedLocalHeadScan.bankMap, regs.injective.eq_iff]
    exact hreadBasePred
  have hreplacementOne :
      replacementSet (bankRegisters regs).one = 1 := by
    simp [replacementSet, valueSet, Basic.exec,
      bankRegisters, PackedLocalHeadScan.bankRegisters,
      PackedLocalHeadScan.bankMap, regs.injective.eq_iff]
    exact hreadOne
  have hreplacementCursor :
      replacementSet (cursor regs) = index := by
    simp [replacementSet, valueSet, Basic.exec, cursor,
      CombineValue.rangeRegisters, bankRegisters,
      PackedLocalHeadScan.bankRegisters,
      PackedLocalHeadScan.bankMap, regs.injective.eq_iff]
    exact hreadCursor
  have hreplacementRemaining :
      replacementSet
          (CombineValue.rangeRegisters regs).remaining =
        code := by
    simp [replacementSet, valueSet, Basic.exec,
      CombineValue.rangeRegisters, bankRegisters,
      PackedLocalHeadScan.bankRegisters,
      PackedLocalHeadScan.bankMap, regs.injective.eq_iff]
    exact hreadRemaining
  obtain ⟨replaceIndexed, hreplaceIndexRun, hreplaceIndexValue,
      hreplaceIndexOutside⟩ :=
    copy_runs (bankRegisters regs).indexCount (cursor regs)
      replacementSet (regs.injective.ne (by decide))
  have hreplaceIndexedWord :
      replaceIndexed (bankRegisters regs).word = word := by
    rw [hreplaceIndexOutside (bankRegisters regs).word
      ((bankRegisters regs).index_ne (by decide))]
    exact hreplacementWord
  have hreplaceIndexedBase :
      replaceIndexed (bankRegisters regs).base =
        PackedLocalConfiguration.radix tm := by
    rw [hreplaceIndexOutside (bankRegisters regs).base
      ((bankRegisters regs).index_ne (by decide))]
    exact hreplacementBase
  have hreplaceIndexedBasePred :
      replaceIndexed (bankRegisters regs).basePred =
        PackedLocalConfiguration.radix tm - 1 := by
    rw [hreplaceIndexOutside (bankRegisters regs).basePred
      ((bankRegisters regs).index_ne (by decide))]
    exact hreplacementBasePred
  have hreplaceIndexedOne :
      replaceIndexed (bankRegisters regs).one = 1 := by
    rw [hreplaceIndexOutside (bankRegisters regs).one
      ((bankRegisters regs).index_ne (by decide))]
    exact hreplacementOne
  have hreplaceIndexedReplacement :
      replaceIndexed (bankRegisters regs).replacement =
        replacement := by
    rw [hreplaceIndexOutside (bankRegisters regs).replacement
      ((bankRegisters regs).index_ne (by decide))]
    exact hreplacementValue
  have hreplaceIndexedIndex :
      replaceIndexed (bankRegisters regs).indexCount = index :=
    hreplaceIndexValue.trans hreplacementCursor
  have hreplaceIndexedCursor :
      replaceIndexed (cursor regs) = index := by
    rw [hreplaceIndexOutside (cursor regs)
      (regs.injective.ne (by decide))]
    exact hreplacementCursor
  have hreplaceIndexedRemaining :
      replaceIndexed
          (CombineValue.rangeRegisters regs).remaining =
        code := by
    rw [hreplaceIndexOutside
      (CombineValue.rangeRegisters regs).remaining
      (regs.injective.ne (by decide))]
    exact hreplacementRemaining
  obtain ⟨replaced, hreplaceRun, hreplaceWord, _hreplaceBuffer,
      _hreplaceIndex, _hreplaceCompleted, _hreplaceResult,
      _hreplaceBase, _hreplaceBasePred, _hreplaceOne,
      _hreplaceReplacement⟩ :=
    NeighborhoodProgram.bankReplace_runs
      (bankRegisters regs) replaceIndexed
      (PackedLocalConfiguration.radix tm) word index replacement
      (by simp [PackedLocalConfiguration.radix])
      hreplaceIndexedWord hreplaceIndexedBase
      hreplaceIndexedBasePred hreplaceIndexedOne
      hreplaceIndexedIndex hreplaceIndexedReplacement
  have hreplacedCursor :
      replaced (cursor regs) = index := by
    calc
      replaced (cursor regs) =
          replaceIndexed (cursor regs) := by
        exact Footprint.runs_eq_outside
          (NeighborhoodProgram.bankReplace_sourceWritesWithin
            (bankRegisters regs))
          hreplaceRun
          (by
            simpa [cursor, CombineValue.rangeRegisters] using
              fixed_index_not_mem_bank regs 19 (by decide))
      _ = index := hreplaceIndexedCursor
  have hreplacedRemaining :
      replaced (CombineValue.rangeRegisters regs).remaining =
        code := by
    calc
      replaced (CombineValue.rangeRegisters regs).remaining =
          replaceIndexed
            (CombineValue.rangeRegisters regs).remaining := by
        exact Footprint.runs_eq_outside
          (NeighborhoodProgram.bankReplace_sourceWritesWithin
            (bankRegisters regs))
          hreplaceRun
          (by
            simpa [CombineValue.rangeRegisters] using
              fixed_index_not_mem_bank regs 21 (by decide))
      _ = code := hreplaceIndexedRemaining
  let final :=
    (Basic.imm (CombineValue.rangeRegisters regs).one 1).exec
      replaced
  have hrestoreRun :
      Runs (restoreRangeOne regs) replaced final :=
    Runs.basic _ _
  have hfinalCursor :
      final (cursor regs) = index := by
    simpa [final, Basic.exec, cursor,
      CombineValue.rangeRegisters, regs.injective.eq_iff] using
      hreplacedCursor
  have hfinalRemaining :
      final (CombineValue.rangeRegisters regs).remaining =
        code := by
    simpa [final, Basic.exec, CombineValue.rangeRegisters,
      regs.injective.eq_iff] using hreplacedRemaining
  have hfinalWord :
      final (bankRegisters regs).word =
        NeighborhoodProgram.replaceAt
          (PackedLocalConfiguration.radix tm) word index
          replacement := by
    simpa [final, Basic.exec, CombineValue.rangeRegisters,
      bankRegisters, PackedLocalHeadScan.bankRegisters,
      PackedLocalHeadScan.bankMap, regs.injective.eq_iff] using
      hreplaceWord
  have hrun :
      Runs (markHead tm centerOffsetBlocks regs) store final := by
    simpa [markHead, Cmd.seqList, ops] using
      Runs.seq hcenterRun
        (Runs.seq hscaleRun
          (Runs.seq hcursorRun
            (Runs.seq hinitializeRun
              (Runs.seq hindexRun
                (Runs.seq hreadRun
                  (Runs.seq hvalueRun
                    (Runs.seq hreplacementRun
                      (Runs.seq hreplaceIndexRun
                        (Runs.seq hreplaceRun hrestoreRun)))))))))
  refine ⟨final, hrun, ?_⟩
  refine
    { blockLength_eq := ?_
      cursor_eq := hfinalCursor
      assignment_eq := hfinalRemaining
      one_eq := ?_
      word_eq := hfinalWord
      chunkCount_eq := ?_
      chunkRadix_eq := ?_ }
  · calc
      final (Layout.blockLength regs) =
          store (Layout.blockLength regs) := by
        exact Footprint.runs_eq_outside
          (markHead_writesWithin tm centerOffsetBlocks regs)
          hrun
          (not_mem_emissionFootprint regs
            (fixed_index_not_mem_footprint regs 2 (by decide)))
      _ = blockLength := hcontext.blockLength_eq
  · simp [final, Basic.exec]
  · calc
      final (Layout.chunkCount regs) =
          store (Layout.chunkCount regs) := by
        exact Footprint.runs_eq_outside
          (markHead_writesWithin tm centerOffsetBlocks regs)
          hrun
          (not_mem_emissionFootprint regs
            (fixed_index_not_mem_footprint regs 7 (by decide)))
      _ = _ := hcontext.chunkCount_eq
  · calc
      final (Layout.chunkRadix regs) =
          store (Layout.chunkRadix regs) := by
        exact Footprint.runs_eq_outside
          (markHead_writesWithin tm centerOffsetBlocks regs)
          hrun
          (not_mem_emissionFootprint regs
            (fixed_index_not_mem_footprint regs 8 (by decide)))
      _ = _ := hcontext.chunkRadix_eq

private theorem localStartCfg_cells
    (tm : TM workTapeCount) (blockLength : ℕ)
    (centers : TapeIndex workTapeCount → ℕ)
    (inputs :
      PredecessorIndex workTapeCount →
        NeighborhoodContent.Content blockLength tm.Q)
    (tape : TapeIndex workTapeCount) (position : ℕ) :
    (tapeAt
        (Guess.Consistency.localStartCfg
          tm blockLength centers inputs)
        tape).cells position =
      (NeighborhoodContent.tapeFromNeighborhood blockLength
        (centers tape)
        (centers tape * blockLength +
          (inputs (.chronological, tape)).headRemainder.val)
        (fun slot => (inputs (.content slot, tape)).cells)).cells
          position := by
  by_cases hinput : tape.val = 0
  · have htape :
        tape = TapeIndex.input workTapeCount :=
      Fin.ext hinput
    rw [htape]
    rfl
  · by_cases houtput : tape.val = workTapeCount + 1
    · have htape :
          tape = TapeIndex.output workTapeCount :=
        Fin.ext houtput
      rw [htape]
      simp [Guess.Consistency.localStartCfg,
        NeighborhoodContent.cfgFromNeighborhoods]
    · let index : Fin workTapeCount :=
        ⟨tape.val - 1, by omega⟩
      have htape : tape = TapeIndex.work index := by
        apply Fin.ext
        simp only [TapeIndex.work, index]
        omega
      rw [htape]
      simp [Guess.Consistency.localStartCfg,
        NeighborhoodContent.cfgFromNeighborhoods]

private theorem localStartCfg_cell_regular
    (tm : TM workTapeCount) (blockLength : ℕ)
    (hpositive : 0 < blockLength)
    (centers : TapeIndex workTapeCount → ℕ)
    (inputs :
      PredecessorIndex workTapeCount →
        NeighborhoodContent.Content blockLength tm.Q)
    (tape : TapeIndex workTapeCount)
    (hcenter : 0 < centers tape)
    (slot : Slot) (offset : Fin blockLength) :
    (tapeAt
      (Guess.Consistency.localStartCfg
        tm blockLength centers inputs)
      tape).cells
        (neighborBlock (centers tape) slot * blockLength +
          offset.val) =
      (inputs (.content slot, tape)).cells offset := by
  have hblock (block : ℕ) :
      blockIndex blockLength
          (block * blockLength + offset.val) =
        block := by
    unfold blockIndex
    rw [Nat.mul_comm block blockLength,
      Nat.mul_add_div hpositive,
      Nat.div_eq_of_lt offset.isLt, Nat.add_zero]
  have hmod (block : ℕ) :
      (block * blockLength + offset.val) % blockLength =
        offset.val := by
    rw [Nat.mul_comm block blockLength, Nat.mul_add_mod,
      Nat.mod_eq_of_lt offset.isLt]
  have hcenterNe :
      centers tape ≠ centers tape - 1 := by
    omega
  have hupperNe :
      centers tape + 1 ≠ centers tape - 1 := by
    omega
  rw [localStartCfg_cells]
  simp only [NeighborhoodContent.tapeFromNeighborhood,
    dif_pos hpositive]
  cases slot <;>
    simp [neighborBlock, hblock, hmod, NeighborhoodContains,
      matchingSlot, hcenterNe, hupperNe]

private theorem localStartCfg_cell_boundary_lower
    (tm : TM workTapeCount) (blockLength : ℕ)
    (hpositive : 0 < blockLength)
    (centers : TapeIndex workTapeCount → ℕ)
    (inputs :
      PredecessorIndex workTapeCount →
        NeighborhoodContent.Content blockLength tm.Q)
    (tape : TapeIndex workTapeCount)
    (hcenter : centers tape = 0)
    (offset : Fin blockLength) :
    (tapeAt
      (Guess.Consistency.localStartCfg
        tm blockLength centers inputs)
      tape).cells offset.val =
      (inputs (.content .lower, tape)).cells offset := by
  have hne : blockLength ≠ 0 := by omega
  rw [localStartCfg_cells]
  simp [NeighborhoodContent.tapeFromNeighborhood, hpositive, hcenter,
    blockIndex, NeighborhoodContains, matchingSlot, hne,
    Nat.div_eq_of_lt offset.isLt,
    Nat.mod_eq_of_lt offset.isLt]

private theorem localStartCfg_cell_boundary_upper
    (tm : TM workTapeCount) (blockLength : ℕ)
    (hpositive : 0 < blockLength)
    (centers : TapeIndex workTapeCount → ℕ)
    (inputs :
      PredecessorIndex workTapeCount →
        NeighborhoodContent.Content blockLength tm.Q)
    (tape : TapeIndex workTapeCount)
    (hcenter : centers tape = 0)
    (offset : Fin blockLength) :
    (tapeAt
      (Guess.Consistency.localStartCfg
        tm blockLength centers inputs)
      tape).cells (blockLength + offset.val) =
      (inputs (.content .upper, tape)).cells offset := by
  have hne : blockLength ≠ 0 := by omega
  have hdiv :
      (blockLength + offset.val) / blockLength = 1 := by
    rw [show
      blockLength + offset.val =
        blockLength * 1 + offset.val by omega,
      Nat.mul_add_div hpositive,
      Nat.div_eq_of_lt offset.isLt]
  have hmod :
      (blockLength + offset.val) % blockLength =
        offset.val := by
    rw [show
      blockLength + offset.val =
        blockLength * 1 + offset.val by omega,
      Nat.mul_add_mod, Nat.mod_eq_of_lt offset.isLt]
  rw [localStartCfg_cells]
  simp [NeighborhoodContent.tapeFromNeighborhood, hpositive, hcenter,
    blockIndex, hdiv, hmod, NeighborhoodContains, matchingSlot, hne]

private theorem localStartCfg_cell_boundary_blank
    (tm : TM workTapeCount) (blockLength : ℕ)
    (hpositive : 0 < blockLength)
    (centers : TapeIndex workTapeCount → ℕ)
    (inputs :
      PredecessorIndex workTapeCount →
        NeighborhoodContent.Content blockLength tm.Q)
    (tape : TapeIndex workTapeCount)
    (hcenter : centers tape = 0)
    (offset : Fin blockLength) :
    (tapeAt
      (Guess.Consistency.localStartCfg
        tm blockLength centers inputs)
      tape).cells (2 * blockLength + offset.val) =
      Γ.blank := by
  have hdiv :
      (2 * blockLength + offset.val) / blockLength = 2 := by
    rw [Nat.mul_comm 2 blockLength,
      Nat.mul_add_div hpositive,
      Nat.div_eq_of_lt offset.isLt, Nat.add_zero]
  have houtside :
      ¬NeighborhoodContains 0 2 := by
    simp [NeighborhoodContains]
  rw [localStartCfg_cells]
  simp only [NeighborhoodContent.tapeFromNeighborhood,
    dif_pos hpositive, hcenter, blockIndex, hdiv]
  rw [if_neg houtside]

private theorem gammaCode_lt_four (symbol : Γ) :
    CompactValueCodeSemantics.gammaCode symbol < 4 := by
  cases symbol <;> decide

private def localSymbolDigit
    (cfg : Cfg workTapeCount Q)
    (blockLength : ℕ)
    (centers : TapeIndex workTapeCount → ℕ)
    (tape : TapeIndex workTapeCount)
    (localPosition : ℕ) : ℕ :=
  CompactValueCodeSemantics.gammaCode
    ((tapeAt cfg tape).cells
      (PackedLocalConfiguration.absolutePosition
        blockLength (centers tape) localPosition))

private theorem blockDigit_regular_eq
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (code : ℕ)
    (centers : TapeIndex workTapeCount → ℕ)
    (tape : TapeIndex workTapeCount)
    (hcenter : 0 < centers tape)
    (slot : Slot) (offset : ℕ) (hoffset : offset < blockLength) :
    blockDigit tm order blockLength hpositive code slot tape offset =
      localSymbolDigit
        (Guess.Consistency.localStartCfg tm blockLength centers
          (LocalAssignmentSemantics.assignmentInputs
            tm order blockLength hpositive code))
        blockLength centers tape
        (slot.toFin.val * blockLength + offset) := by
  have hposition :
      PackedLocalConfiguration.absolutePosition blockLength
          (centers tape)
          (slot.toFin.val * blockLength + offset) =
        neighborBlock (centers tape) slot * blockLength + offset := by
    obtain ⟨previous, hcenterEq⟩ :=
      Nat.exists_eq_succ_of_ne_zero
        (by omega : centers tape ≠ 0)
    rw [hcenterEq]
    cases slot <;>
      simp [PackedLocalConfiguration.absolutePosition,
        PackedLocalConfiguration.windowStart, Slot.toFin,
        neighborBlock] <;>
      ring_nf
  unfold blockDigit
  rw [dif_pos hoffset]
  unfold localSymbolDigit
  rw [hposition]
  exact congrArg CompactValueCodeSemantics.gammaCode
    (localStartCfg_cell_regular
      tm blockLength hpositive centers
      (LocalAssignmentSemantics.assignmentInputs
        tm order blockLength hpositive code)
      tape hcenter slot ⟨offset, hoffset⟩).symm

private theorem blockDigit_boundary_lower_eq
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (code : ℕ)
    (centers : TapeIndex workTapeCount → ℕ)
    (tape : TapeIndex workTapeCount)
    (hcenter : centers tape = 0)
    (offset : ℕ) (hoffset : offset < blockLength) :
    blockDigit tm order blockLength hpositive code .lower tape offset =
      localSymbolDigit
        (Guess.Consistency.localStartCfg tm blockLength centers
          (LocalAssignmentSemantics.assignmentInputs
            tm order blockLength hpositive code))
        blockLength centers tape offset := by
  unfold blockDigit
  rw [dif_pos hoffset]
  unfold localSymbolDigit
  simp only [PackedLocalConfiguration.absolutePosition,
    PackedLocalConfiguration.windowStart, hcenter, Nat.zero_sub,
    Nat.zero_mul, Nat.zero_add]
  exact congrArg CompactValueCodeSemantics.gammaCode
    (localStartCfg_cell_boundary_lower
      tm blockLength hpositive centers
      (LocalAssignmentSemantics.assignmentInputs
        tm order blockLength hpositive code)
      tape hcenter ⟨offset, hoffset⟩).symm

private theorem blockDigit_boundary_upper_eq
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (code : ℕ)
    (centers : TapeIndex workTapeCount → ℕ)
    (tape : TapeIndex workTapeCount)
    (hcenter : centers tape = 0)
    (offset : ℕ) (hoffset : offset < blockLength) :
    blockDigit tm order blockLength hpositive code .upper tape offset =
      localSymbolDigit
        (Guess.Consistency.localStartCfg tm blockLength centers
          (LocalAssignmentSemantics.assignmentInputs
            tm order blockLength hpositive code))
        blockLength centers tape (blockLength + offset) := by
  unfold blockDigit
  rw [dif_pos hoffset]
  unfold localSymbolDigit
  simp only [PackedLocalConfiguration.absolutePosition,
    PackedLocalConfiguration.windowStart, hcenter, Nat.zero_sub,
    Nat.zero_mul, Nat.zero_add]
  exact congrArg CompactValueCodeSemantics.gammaCode
    (localStartCfg_cell_boundary_upper
      tm blockLength hpositive centers
      (LocalAssignmentSemantics.assignmentInputs
        tm order blockLength hpositive code)
      tape hcenter ⟨offset, hoffset⟩).symm

private theorem blankDigit_boundary_eq
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (code : ℕ)
    (centers : TapeIndex workTapeCount → ℕ)
    (tape : TapeIndex workTapeCount)
    (hcenter : centers tape = 0)
    (offset : ℕ) (hoffset : offset < blockLength) :
    CompactValueCodeSemantics.gammaCode .blank =
      localSymbolDigit
        (Guess.Consistency.localStartCfg tm blockLength centers
          (LocalAssignmentSemantics.assignmentInputs
            tm order blockLength hpositive code))
        blockLength centers tape (2 * blockLength + offset) := by
  unfold localSymbolDigit
  simp only [PackedLocalConfiguration.absolutePosition,
    PackedLocalConfiguration.windowStart, hcenter, Nat.zero_sub,
    Nat.zero_mul, Nat.zero_add]
  exact congrArg CompactValueCodeSemantics.gammaCode
    (localStartCfg_cell_boundary_blank
      tm blockLength hpositive centers
      (LocalAssignmentSemantics.assignmentInputs
        tm order blockLength hpositive code)
      tape hcenter ⟨offset, hoffset⟩).symm

private theorem regularBlocksWord_eq
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (code word : ℕ)
    (centers : TapeIndex workTapeCount → ℕ)
    (tape : TapeIndex workTapeCount)
    (hcenter : 0 < centers tape) :
    let base := PackedLocalConfiguration.radix tm
    let lower :=
      blockDigit tm order blockLength hpositive code .lower tape
    let center :=
      blockDigit tm order blockLength hpositive code .center tape
    let upper :=
      blockDigit tm order blockLength hpositive code .upper tape
    let symbols :=
      localSymbolDigit
        (Guess.Consistency.localStartCfg tm blockLength centers
          (LocalAssignmentSemantics.assignmentInputs
            tm order blockLength hpositive code))
        blockLength centers tape
    PackedDigits.prependFrom base lower 0 blockLength
        (PackedDigits.prependFrom base center 0 blockLength
          (PackedDigits.prependFrom base upper 0 blockLength word)) =
      PackedDigits.prependFrom base symbols 0
        (PackedLocalConfiguration.tapeSpan blockLength) word := by
  dsimp only
  apply threePrepend_eq
  · intro offset hoffset
    simpa [Slot.toFin] using
      blockDigit_regular_eq tm order blockLength hpositive code
        centers tape hcenter .lower offset hoffset
  · intro offset hoffset
    simpa [Slot.toFin] using
      blockDigit_regular_eq tm order blockLength hpositive code
        centers tape hcenter .center offset hoffset
  · intro offset hoffset
    simpa [Slot.toFin] using
      blockDigit_regular_eq tm order blockLength hpositive code
        centers tape hcenter .upper offset hoffset

private theorem boundaryBlocksWord_eq
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (code word : ℕ)
    (centers : TapeIndex workTapeCount → ℕ)
    (tape : TapeIndex workTapeCount)
    (hcenter : centers tape = 0) :
    let base := PackedLocalConfiguration.radix tm
    let lower :=
      blockDigit tm order blockLength hpositive code .lower tape
    let upper :=
      blockDigit tm order blockLength hpositive code .upper tape
    let symbols :=
      localSymbolDigit
        (Guess.Consistency.localStartCfg tm blockLength centers
          (LocalAssignmentSemantics.assignmentInputs
            tm order blockLength hpositive code))
        blockLength centers tape
    PackedDigits.prependFrom base lower 0 blockLength
        (PackedDigits.prependFrom base upper 0 blockLength
          (PackedDigits.prependFrom base
            (fun _ => CompactValueCodeSemantics.gammaCode .blank)
            0 blockLength word)) =
      PackedDigits.prependFrom base symbols 0
        (PackedLocalConfiguration.tapeSpan blockLength) word := by
  dsimp only
  apply threePrepend_eq
  · intro offset hoffset
    exact blockDigit_boundary_lower_eq
      tm order blockLength hpositive code centers tape hcenter
        offset hoffset
  · intro offset hoffset
    exact blockDigit_boundary_upper_eq
      tm order blockLength hpositive code centers tape hcenter
        offset hoffset
  · intro offset hoffset
    exact blankDigit_boundary_eq
      tm order blockLength hpositive code centers tape hcenter
        offset hoffset

private theorem markLocalWord_eq
    (tm : TM workTapeCount)
    (blockLength : ℕ)
    (centers : TapeIndex workTapeCount → ℕ)
    (cfg : Cfg workTapeCount tm.Q)
    (tape : TapeIndex workTapeCount)
    (headLocal suffix : ℕ)
    (hheadLocal :
      headLocal <
        PackedLocalConfiguration.tapeSpan blockLength)
    (hhead :
      (tapeAt cfg tape).head =
        PackedLocalConfiguration.absolutePosition
          blockLength (centers tape) headLocal) :
    let unmarked :=
      PackedDigits.prependFrom
        (PackedLocalConfiguration.radix tm)
        (localSymbolDigit cfg blockLength centers tape)
        0 (PackedLocalConfiguration.tapeSpan blockLength) suffix
    NeighborhoodProgram.replaceAt
        (PackedLocalConfiguration.radix tm) unmarked headLocal
        (PackedDigits.digit
            (PackedLocalConfiguration.radix tm)
            unmarked headLocal +
          4) =
      PackedDigits.prependFrom
        (PackedLocalConfiguration.radix tm)
        (PackedLocalConfiguration.cellDigit
          cfg blockLength centers tape)
        0 (PackedLocalConfiguration.tapeSpan blockLength) suffix := by
  dsimp only
  let base := PackedLocalConfiguration.radix tm
  let count := PackedLocalConfiguration.tapeSpan blockLength
  let symbols := localSymbolDigit cfg blockLength centers tape
  let cells :=
    PackedLocalConfiguration.cellDigit
      cfg blockLength centers tape
  let unmarked :=
    PackedDigits.prependFrom base symbols 0 count suffix
  let replacement :=
    PackedDigits.digit base unmarked headLocal + 4
  have hbase : 0 < base := by
    simp [base, PackedLocalConfiguration.radix]
  have hsymbols :
      ∀ index, symbols index < base := by
    intro index
    have hcode :=
      gammaCode_lt_four
        ((tapeAt cfg tape).cells
          (PackedLocalConfiguration.absolutePosition
            blockLength (centers tape) index))
    dsimp only [symbols, localSymbolDigit]
    have hbaseLarge : 16 ≤ base := by
      simp [base, PackedLocalConfiguration.radix]
    omega
  have hcells :
      ∀ index, cells index < base := by
    intro index
    exact
      PackedLocalConfiguration.cellDigit_lt_radix
        tm cfg blockLength centers tape index
  have hheadDigit :
      PackedDigits.digit base unmarked headLocal =
        symbols headLocal := by
    simpa [unmarked] using
      PackedDigits.prependFrom_digit hbase hsymbols
        0 count suffix headLocal hheadLocal
  have hreplacement :
      replacement < base := by
    dsimp only [replacement]
    rw [hheadDigit]
    have hsymbol := hsymbols headLocal
    have hsmall : symbols headLocal < 4 := by
      exact gammaCode_lt_four _
    have hbaseLarge : 16 ≤ base := by
      simp [base, PackedLocalConfiguration.radix]
    omega
  apply word_eq_of_digits_drop base count
  · intro index hindex
    by_cases heq : index = headLocal
    · subst index
      rw [NeighborhoodProgram.replaceAt_digit_eq
        hbase hreplacement]
      rw [PackedDigits.prependFrom_digit
        hbase hcells 0 count suffix headLocal hheadLocal]
      dsimp only [replacement]
      rw [hheadDigit]
      simp [cells, symbols, localSymbolDigit,
        PackedLocalConfiguration.cellDigit, hhead]
    · rw [NeighborhoodProgram.replaceAt_digit_ne
        hbase hreplacement heq]
      rw [PackedDigits.prependFrom_digit
        hbase hsymbols 0 count suffix index hindex]
      rw [PackedDigits.prependFrom_digit
        hbase hcells 0 count suffix index hindex]
      have hnotHead :
          (tapeAt cfg tape).head ≠
            PackedLocalConfiguration.absolutePosition
              blockLength (centers tape) index := by
        rw [hhead]
        intro habsolute
        apply heq
        unfold PackedLocalConfiguration.absolutePosition at habsolute
        omega
      simp [cells, symbols, localSymbolDigit,
        PackedLocalConfiguration.cellDigit, hnotHead]
  · calc
      PackedDigits.drop base count
          (NeighborhoodProgram.replaceAt
            base unmarked headLocal replacement) =
          PackedDigits.drop base count unmarked :=
        PackedLocalRepresentation.drop_replaceAt
          hbase hheadLocal hreplacement
      _ = suffix := by
        exact PackedDigits.drop_prependFrom
          hbase hsymbols 0 count suffix
      _ =
          PackedDigits.drop base count
            (PackedDigits.prependFrom base cells 0 count suffix) := by
        symm
        exact PackedDigits.drop_prependFrom
          hbase hcells 0 count suffix

private theorem cellSegment_eq_configuration
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (centers : TapeIndex workTapeCount → ℕ)
    (cfg : Cfg workTapeCount tm.Q)
    (tape : TapeIndex workTapeCount)
    (suffix : ℕ) :
    PackedDigits.prependFrom
        (PackedLocalConfiguration.radix tm)
        (PackedLocalConfiguration.cellDigit
          cfg blockLength centers tape)
        0 (PackedLocalConfiguration.tapeSpan blockLength) suffix =
      PackedDigits.prependFrom
        (PackedLocalConfiguration.radix tm)
        (PackedLocalConfiguration.configurationDigit
          tm order blockLength centers cfg)
        (PackedLocalConfiguration.cellIndex blockLength tape 0)
        (PackedLocalConfiguration.tapeSpan blockLength) suffix := by
  apply prependFrom_congr
  intro offset hoffset
  have hcell :=
    PackedLocalConfiguration.configurationDigit_cell
      tm order blockLength hpositive centers cfg tape offset hoffset
  simpa [PackedLocalConfiguration.cellIndex] using hcell.symm

private theorem initializeBoundaryTape_runs
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (tape : TapeIndex workTapeCount)
    (regs : NeighborhoodTrial.Registers controller)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (centers : TapeIndex workTapeCount → ℕ)
    (hcenter : centers tape = 0)
    (offset code word : ℕ)
    (store : Store)
    (hcontext :
      AssignmentContext tm blockLength offset code word regs store) :
    let inputs :=
      LocalAssignmentSemantics.assignmentInputs
        tm order blockLength hpositive code
    let cfg :=
      Guess.Consistency.localStartCfg
        tm blockLength centers inputs
    let head :=
      (inputs (.chronological, tape)).headRemainder.val
    let finalWord :=
      PackedDigits.prependFrom
        (PackedLocalConfiguration.radix tm)
        (PackedLocalConfiguration.configurationDigit
          tm order blockLength centers cfg)
        (PackedLocalConfiguration.cellIndex blockLength tape 0)
        (PackedLocalConfiguration.tapeSpan blockLength) word
    ∃ final,
      Runs (initializeBoundaryTape tm tape regs) store final ∧
      AssignmentContext tm blockLength head code finalWord regs final := by
  dsimp only
  let inputs :=
    LocalAssignmentSemantics.assignmentInputs
      tm order blockLength hpositive code
  let cfg :=
    Guess.Consistency.localStartCfg
      tm blockLength centers inputs
  let head :=
    (inputs (.chronological, tape)).headRemainder.val
  let blankWord :=
    PackedDigits.prependFrom
      (PackedLocalConfiguration.radix tm)
      (fun _ => CompactValueCodeSemantics.gammaCode .blank)
      0 blockLength word
  let upperWord :=
    PackedDigits.prependFrom
      (PackedLocalConfiguration.radix tm)
      (blockDigit tm order blockLength hpositive code .upper tape)
      0 blockLength blankWord
  let premark :=
    PackedDigits.prependFrom
      (PackedLocalConfiguration.radix tm)
      (blockDigit tm order blockLength hpositive code .lower tape)
      0 blockLength upperWord
  obtain ⟨afterBlank, hblankRun, hblankContextRaw⟩ :=
    pushBlankBlock_runs tm regs blockLength offset code word
      store hcontext
  have hblankContext :
      AssignmentContext tm blockLength 0 code blankWord regs
        afterBlank := by
    simpa [blankWord] using hblankContextRaw
  obtain ⟨afterUpper, hupperRun, hupperContextRaw⟩ :=
    pushBlock_runs tm order .upper tape regs blockLength hpositive
      0 code blankWord afterBlank hblankContext
  have hupperContext :
      AssignmentContext tm blockLength 0 code upperWord regs
        afterUpper := by
    simpa [upperWord] using hupperContextRaw
  obtain ⟨beforeHead, hlowerRun, hlowerContextRaw⟩ :=
    pushBlock_runs tm order .lower tape regs blockLength hpositive
      0 code upperWord afterUpper hupperContext
  have hlowerContext :
      AssignmentContext tm blockLength 0 code premark regs
        beforeHead := by
    simpa [premark] using hlowerContextRaw
  obtain ⟨decoded, hdecodeRun, _hdecodeValue,
      hdecodeContextRaw⟩ :=
    decodeHead_runs tm order tape regs blockLength hpositive
      0 code premark beforeHead hlowerContext
  have hdecodeContext :
      AssignmentContext tm blockLength head code premark regs
        decoded := by
    simpa [head, inputs] using hdecodeContextRaw
  obtain ⟨marked, hmarkRun, hmarkContextRaw⟩ :=
    markHead_runs tm regs 0 blockLength head code premark decoded
      hdecodeContext
  have hmarkContext :
      AssignmentContext tm blockLength head code
        (NeighborhoodProgram.replaceAt
          (PackedLocalConfiguration.radix tm) premark head
          (PackedDigits.digit
              (PackedLocalConfiguration.radix tm) premark head +
            4))
        regs marked := by
    simpa using hmarkContextRaw
  have hpremark :
      premark =
        PackedDigits.prependFrom
          (PackedLocalConfiguration.radix tm)
          (localSymbolDigit cfg blockLength centers tape)
          0 (PackedLocalConfiguration.tapeSpan blockLength) word := by
    simpa [premark, upperWord, blankWord, cfg, inputs] using
      boundaryBlocksWord_eq tm order blockLength hpositive code word
        centers tape hcenter
  have hheadLocal :
      head < PackedLocalConfiguration.tapeSpan blockLength := by
    have hremainder :=
      (inputs (.chronological, tape)).headRemainder.isLt
    simp only [head]
    simp [PackedLocalConfiguration.tapeSpan]
    omega
  have hheadEq :
      (tapeAt cfg tape).head =
        PackedLocalConfiguration.absolutePosition
          blockLength (centers tape) head := by
    have hsource :=
      PackedLocalConfiguration.localStartCfg_head
        tm blockLength centers inputs tape
    simpa [cfg, head, PackedLocalConfiguration.absolutePosition,
      PackedLocalConfiguration.windowStart, hcenter] using hsource
  have hmarkedLocal :
      NeighborhoodProgram.replaceAt
          (PackedLocalConfiguration.radix tm) premark head
          (PackedDigits.digit
              (PackedLocalConfiguration.radix tm) premark head +
            4) =
        PackedDigits.prependFrom
          (PackedLocalConfiguration.radix tm)
          (PackedLocalConfiguration.cellDigit
            cfg blockLength centers tape)
          0 (PackedLocalConfiguration.tapeSpan blockLength) word := by
    rw [hpremark]
    exact markLocalWord_eq tm blockLength centers cfg tape head word
      hheadLocal hheadEq
  have hsegment :=
    cellSegment_eq_configuration tm order blockLength hpositive
      centers cfg tape word
  have hfinalContext :
      AssignmentContext tm blockLength head code
        (PackedDigits.prependFrom
          (PackedLocalConfiguration.radix tm)
          (PackedLocalConfiguration.configurationDigit
            tm order blockLength centers cfg)
          (PackedLocalConfiguration.cellIndex blockLength tape 0)
          (PackedLocalConfiguration.tapeSpan blockLength) word)
        regs marked := by
    rw [← hsegment, ← hmarkedLocal]
    exact hmarkContext
  refine ⟨marked, ?_, hfinalContext⟩
  simpa [initializeBoundaryTape, Cmd.seqList] using
    Runs.seq hblankRun
      (Runs.seq hupperRun
        (Runs.seq hlowerRun
          (Runs.seq hdecodeRun hmarkRun)))

private theorem initializeRegularTape_runs
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (tape : TapeIndex workTapeCount)
    (regs : NeighborhoodTrial.Registers controller)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (centers : TapeIndex workTapeCount → ℕ)
    (hcenter : 0 < centers tape)
    (offset code word : ℕ)
    (store : Store)
    (hcontext :
      AssignmentContext tm blockLength offset code word regs store) :
    let inputs :=
      LocalAssignmentSemantics.assignmentInputs
        tm order blockLength hpositive code
    let cfg :=
      Guess.Consistency.localStartCfg
        tm blockLength centers inputs
    let head :=
      (inputs (.chronological, tape)).headRemainder.val
    let headLocal := blockLength + head
    let finalWord :=
      PackedDigits.prependFrom
        (PackedLocalConfiguration.radix tm)
        (PackedLocalConfiguration.configurationDigit
          tm order blockLength centers cfg)
        (PackedLocalConfiguration.cellIndex blockLength tape 0)
        (PackedLocalConfiguration.tapeSpan blockLength) word
    ∃ final,
      Runs (initializeRegularTape tm tape regs) store final ∧
      AssignmentContext tm blockLength headLocal code finalWord regs
        final := by
  dsimp only
  let inputs :=
    LocalAssignmentSemantics.assignmentInputs
      tm order blockLength hpositive code
  let cfg :=
    Guess.Consistency.localStartCfg
      tm blockLength centers inputs
  let head :=
    (inputs (.chronological, tape)).headRemainder.val
  let headLocal := blockLength + head
  let upperWord :=
    PackedDigits.prependFrom
      (PackedLocalConfiguration.radix tm)
      (blockDigit tm order blockLength hpositive code .upper tape)
      0 blockLength word
  let centerWord :=
    PackedDigits.prependFrom
      (PackedLocalConfiguration.radix tm)
      (blockDigit tm order blockLength hpositive code .center tape)
      0 blockLength upperWord
  let premark :=
    PackedDigits.prependFrom
      (PackedLocalConfiguration.radix tm)
      (blockDigit tm order blockLength hpositive code .lower tape)
      0 blockLength centerWord
  obtain ⟨afterUpper, hupperRun, hupperContextRaw⟩ :=
    pushBlock_runs tm order .upper tape regs blockLength hpositive
      offset code word store hcontext
  have hupperContext :
      AssignmentContext tm blockLength 0 code upperWord regs
        afterUpper := by
    simpa [upperWord] using hupperContextRaw
  obtain ⟨afterCenter, hcenterRun, hcenterContextRaw⟩ :=
    pushBlock_runs tm order .center tape regs blockLength hpositive
      0 code upperWord afterUpper hupperContext
  have hcenterContext :
      AssignmentContext tm blockLength 0 code centerWord regs
        afterCenter := by
    simpa [centerWord] using hcenterContextRaw
  obtain ⟨beforeHead, hlowerRun, hlowerContextRaw⟩ :=
    pushBlock_runs tm order .lower tape regs blockLength hpositive
      0 code centerWord afterCenter hcenterContext
  have hlowerContext :
      AssignmentContext tm blockLength 0 code premark regs
        beforeHead := by
    simpa [premark] using hlowerContextRaw
  obtain ⟨decoded, hdecodeRun, _hdecodeValue,
      hdecodeContextRaw⟩ :=
    decodeHead_runs tm order tape regs blockLength hpositive
      0 code premark beforeHead hlowerContext
  have hdecodeContext :
      AssignmentContext tm blockLength head code premark regs
        decoded := by
    simpa [head, inputs] using hdecodeContextRaw
  obtain ⟨marked, hmarkRun, hmarkContextRaw⟩ :=
    markHead_runs tm regs 1 blockLength head code premark decoded
      hdecodeContext
  have hmarkContext :
      AssignmentContext tm blockLength headLocal code
        (NeighborhoodProgram.replaceAt
          (PackedLocalConfiguration.radix tm) premark headLocal
          (PackedDigits.digit
              (PackedLocalConfiguration.radix tm) premark headLocal +
            4))
        regs marked := by
    simpa [headLocal, Nat.add_comm] using hmarkContextRaw
  have hpremark :
      premark =
        PackedDigits.prependFrom
          (PackedLocalConfiguration.radix tm)
          (localSymbolDigit cfg blockLength centers tape)
          0 (PackedLocalConfiguration.tapeSpan blockLength) word := by
    simpa [premark, centerWord, upperWord, cfg, inputs] using
      regularBlocksWord_eq tm order blockLength hpositive code word
        centers tape hcenter
  have hheadLocalBound :
      headLocal <
        PackedLocalConfiguration.tapeSpan blockLength := by
    have hremainder :=
      (inputs (.chronological, tape)).headRemainder.isLt
    simp only [headLocal, head]
    simp [PackedLocalConfiguration.tapeSpan]
    omega
  have hheadEq :
      (tapeAt cfg tape).head =
        PackedLocalConfiguration.absolutePosition
          blockLength (centers tape) headLocal := by
    have hsource :=
      PackedLocalConfiguration.localStartCfg_head
        tm blockLength centers inputs tape
    rw [hsource]
    unfold PackedLocalConfiguration.absolutePosition
      PackedLocalConfiguration.windowStart
    obtain ⟨previous, hcenterEq⟩ :=
      Nat.exists_eq_succ_of_ne_zero
        (by omega : centers tape ≠ 0)
    rw [hcenterEq]
    dsimp only [headLocal, head]
    simp only [Nat.succ_sub_one]
    simp only [Nat.succ_mul]
    ac_rfl
  have hmarkedLocal :
      NeighborhoodProgram.replaceAt
          (PackedLocalConfiguration.radix tm) premark headLocal
          (PackedDigits.digit
              (PackedLocalConfiguration.radix tm) premark headLocal +
            4) =
        PackedDigits.prependFrom
          (PackedLocalConfiguration.radix tm)
          (PackedLocalConfiguration.cellDigit
            cfg blockLength centers tape)
          0 (PackedLocalConfiguration.tapeSpan blockLength) word := by
    rw [hpremark]
    exact markLocalWord_eq tm blockLength centers cfg tape headLocal
      word hheadLocalBound hheadEq
  have hsegment :=
    cellSegment_eq_configuration tm order blockLength hpositive
      centers cfg tape word
  have hfinalContext :
      AssignmentContext tm blockLength headLocal code
        (PackedDigits.prependFrom
          (PackedLocalConfiguration.radix tm)
          (PackedLocalConfiguration.configurationDigit
            tm order blockLength centers cfg)
          (PackedLocalConfiguration.cellIndex blockLength tape 0)
          (PackedLocalConfiguration.tapeSpan blockLength) word)
        regs marked := by
    rw [← hsegment, ← hmarkedLocal]
    exact hmarkContext
  refine ⟨marked, ?_, hfinalContext⟩
  simpa [initializeRegularTape, Cmd.seqList] using
    Runs.seq hupperRun
      (Runs.seq hcenterRun
        (Runs.seq hlowerRun
          (Runs.seq hdecodeRun hmarkRun)))

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
    (Basic.imm
      (ControlDecode.nodeTape regs) selectedTape.val).exec decoded
  have hselectRun :
      Runs
        (.basic
          (.imm (ControlDecode.nodeTape regs) selectedTape.val))
        decoded selected :=
    Runs.basic _ _
  have hselectedTape :
      selected (ControlDecode.nodeTape regs) =
        selectedTape.val := by
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
  refine ⟨final, ?_, hcenterPost.center_eq,
    hcenterPost.guess_eq, ?_⟩
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
      (NeighborhoodGraph.Guess.Enumeration.candidateGuess code)
        |>.derivedCenter tape interval <;>
    rfl

private theorem assignmentContext_of_deriveOutside
    (tm : TM workTapeCount)
    (regs : NeighborhoodTrial.Registers controller)
    (blockLength offset code word : ℕ)
    (initial final : Store)
    (hcontext :
      AssignmentContext tm blockLength offset code word regs initial)
    (houtside :
      ∀ address,
        address ∉ ControlDecode.scratchFootprint regs →
        address ∉ CombineSafeCenter.footprint regs →
        final address = initial address) :
    AssignmentContext tm blockLength offset code word regs final := by
  have fixed
      (slot : Fin 34)
      (hcontrol :
        ∀ scratch, slot ≠ ControlDecode.scratchMap scratch)
      (hcenter :
        ∀ scratch, slot ≠ CombineSafeCenter.scratchMap scratch) :
      final (regs.index slot) = initial (regs.index slot) :=
    houtside (regs.index slot)
      (fixed_index_not_mem_control regs slot hcontrol)
      (fixed_index_not_mem_center regs slot hcenter)
  refine
    { blockLength_eq := ?_
      cursor_eq := ?_
      assignment_eq := ?_
      one_eq := ?_
      word_eq := ?_
      chunkCount_eq := ?_
      chunkRadix_eq := ?_ }
  · rw [show
      final (Layout.blockLength regs) =
        initial (Layout.blockLength regs) by
      simpa using fixed 2
        (by decide)
        (by decide)]
    exact hcontext.blockLength_eq
  · rw [show
      final (cursor regs) = initial (cursor regs) by
      simpa [cursor, CombineValue.rangeRegisters] using
        fixed 19
          (by decide)
          (by decide)]
    exact hcontext.cursor_eq
  · rw [show
      final (CombineValue.rangeRegisters regs).remaining =
        initial (CombineValue.rangeRegisters regs).remaining by
      simpa [CombineValue.rangeRegisters] using
        fixed 21
          (by decide)
          (by decide)]
    exact hcontext.assignment_eq
  · rw [show
      final (CombineValue.rangeRegisters regs).one =
        initial (CombineValue.rangeRegisters regs).one by
      simpa [CombineValue.rangeRegisters] using
        fixed 17
          (by decide)
          (by decide)]
    exact hcontext.one_eq
  · rw [show
      final (packedWord regs) = initial (packedWord regs) by
      simpa [packedWord, bankRegisters,
        PackedLocalHeadScan.bankRegisters,
        PackedLocalHeadScan.bankMap] using
        fixed 32
          (by decide)
          (by decide)]
    exact hcontext.word_eq
  · rw [show
      final (Layout.chunkCount regs) =
        initial (Layout.chunkCount regs) by
      simpa using fixed 7
        (by decide)
        (by decide)]
    exact hcontext.chunkCount_eq
  · rw [show
      final (Layout.chunkRadix regs) =
        initial (Layout.chunkRadix regs) by
      simpa using fixed 8
        (by decide)
        (by decide)]
    exact hcontext.chunkRadix_eq

private theorem initializeTape_runs
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
    (selectedTape : TapeIndex workTapeCount)
    (guessCode :
      Fin
        (3 ^
          NeighborhoodGraph.Guess.Enumeration.movementCount
            workTapeCount instanceData.horizon))
    (assignment offset word : ℕ)
    (store : Store)
    (hfits :
      ∀ digit ∈
          FrameCodec.nodeDigits
            (show
              NeighborhoodEvaluator.QueryNode
                workTapeCount instanceData.horizon
              from .graph (.computation nodeTape slot interval)),
        digit < Representation.digitBase instanceData)
    (hcomputation :
      CombineTerm.ComputationContext regs instanceData nodeTape slot
        interval logicalBank store)
    (hstoreGuess : store controller.guess = guessCode.val)
    (hguess :
      instanceData.guess =
        NeighborhoodGraph.Guess.Enumeration.candidateGuess guessCode)
    (hinterval : interval ≤ instanceData.horizon)
    (hassignment :
      AssignmentContext tm instanceData.blockLength offset assignment
        word regs store) :
    let centers :=
      NeighborhoodGraph.Guess.Consistency.guessedCenters
        instanceData.guess interval
    let inputs :=
      LocalAssignmentSemantics.assignmentInputs tm order
        instanceData.blockLength instanceData.positive assignment
    let cfg :=
      Guess.Consistency.localStartCfg
        tm instanceData.blockLength centers inputs
    let finalWord :=
      PackedDigits.prependFrom
        (PackedLocalConfiguration.radix tm)
        (PackedLocalConfiguration.configurationDigit tm order
          instanceData.blockLength centers cfg)
        (PackedLocalConfiguration.cellIndex
          instanceData.blockLength selectedTape 0)
        (PackedLocalConfiguration.tapeSpan instanceData.blockLength)
        word
    ∃ final finalOffset,
      Runs
        (initializeTape tm controller selectedTape regs)
        store final ∧
      AssignmentContext tm instanceData.blockLength finalOffset
        assignment finalWord regs final ∧
      final (CombineValue.rangeRegisters regs).accumulator =
        store (CombineValue.rangeRegisters regs).accumulator ∧
      final (CombineValue.rangeRegisters regs).count =
        store (CombineValue.rangeRegisters regs).count := by
  dsimp only
  let centers :=
    NeighborhoodGraph.Guess.Consistency.guessedCenters
      instanceData.guess interval
  let inputs :=
    LocalAssignmentSemantics.assignmentInputs tm order
      instanceData.blockLength instanceData.positive assignment
  let cfg :=
    Guess.Consistency.localStartCfg
      tm instanceData.blockLength centers inputs
  let finalWord :=
    PackedDigits.prependFrom
      (PackedLocalConfiguration.radix tm)
      (PackedLocalConfiguration.configurationDigit tm order
        instanceData.blockLength centers cfg)
      (PackedLocalConfiguration.cellIndex
        instanceData.blockLength selectedTape 0)
      (PackedLocalConfiguration.tapeSpan instanceData.blockLength)
      word
  obtain ⟨savedAccumulator, hsaveAccumulatorRun,
      hsaveAccumulatorValue, hsaveAccumulatorOutside⟩ :=
    copy_runs (cursor regs)
      (CombineValue.rangeRegisters regs).accumulator store
      (by
        simpa [cursor, CombineValue.rangeRegisters] using
          regs.injective.ne (by decide : (19 : Fin 34) ≠ 18))
  have hsaveAccumulatorContext :
      AssignmentContext tm instanceData.blockLength
        (store (CombineValue.rangeRegisters regs).accumulator)
        assignment word regs savedAccumulator :=
    assignmentContext_of_cursorWrite tm regs
      instanceData.blockLength offset
      (store (CombineValue.rangeRegisters regs).accumulator)
      assignment word store savedAccumulator hassignment
      hsaveAccumulatorValue hsaveAccumulatorOutside
  obtain ⟨savedCount, hsaveCountRun, hsaveCountValue,
      hsaveCountOutside⟩ :=
    copy_runs (payloadPosition regs)
      (CombineValue.rangeRegisters regs).count savedAccumulator
      (by
        simpa [payloadPosition, AssignmentPayloadBit.payloadPosition,
          Layout.codecScratch, CombineValue.rangeRegisters] using
            regs.injective.ne (by decide : (31 : Fin 34) ≠ 10))
  have hsaveCountContext :
      AssignmentContext tm instanceData.blockLength
        (store (CombineValue.rangeRegisters regs).accumulator)
        assignment word regs savedCount :=
    assignmentContext_of_physicalWrite tm regs
      instanceData.blockLength
      (store (CombineValue.rangeRegisters regs).accumulator)
      assignment word 31 savedAccumulator savedCount
      hsaveAccumulatorContext assignmentContextSlot_ne_31
      (by
        simpa [payloadPosition, AssignmentPayloadBit.payloadPosition,
          Layout.codecScratch] using hsaveCountOutside)
  have hsavesRun :
      Runs
        (.seq
          (copy (cursor regs)
            (CombineValue.rangeRegisters regs).accumulator)
          (copy (payloadPosition regs)
            (CombineValue.rangeRegisters regs).count))
        store savedCount :=
    Runs.seq hsaveAccumulatorRun hsaveCountRun
  have hsavesWrites :
      Footprint.CmdWritesWithin (footprint regs)
        (.seq
          (copy (cursor regs)
            (CombineValue.rangeRegisters regs).accumulator)
          (copy (payloadPosition regs)
            (CombineValue.rangeRegisters regs).count)) :=
    ⟨copy_writesWithin regs _ _
        (physical_slot_mem regs (by simp)),
      copy_writesWithin regs _ _
        (physical_slot_mem regs (by simp))⟩
  have hsavedComputation :
      CombineTerm.ComputationContext regs instanceData nodeTape slot
        interval logicalBank savedCount :=
    computationContext_of_runs regs instanceData nodeTape slot
      interval logicalBank hsavesWrites hsavesRun hcomputation
  have hsavedGuess :
      savedCount controller.guess = guessCode.val :=
    (controller_guess_eq_of_runs regs hsavesWrites
      hsavesRun).trans hstoreGuess
  obtain ⟨derived, hderiveRun, hcenterRaw, _hderivedGuess,
      hderiveOutside⟩ :=
    deriveTapeCenter_runs regs instanceData nodeTape slot interval
      logicalBank selectedTape guessCode savedCount hfits
      hsavedComputation hsavedGuess
  have hderivedAssignment :
      AssignmentContext tm instanceData.blockLength
        (store (CombineValue.rangeRegisters regs).accumulator)
        assignment word regs derived :=
    assignmentContext_of_deriveOutside tm regs
      instanceData.blockLength
      (store (CombineValue.rangeRegisters regs).accumulator)
      assignment word savedCount derived hsaveCountContext
      hderiveOutside
  obtain ⟨restoredAccumulator, hrestoreAccumulatorRun,
      hrestoreAccumulatorValue, hrestoreAccumulatorOutside⟩ :=
    copy_runs (CombineValue.rangeRegisters regs).accumulator
      (cursor regs) derived
      (by
        simpa [cursor, CombineValue.rangeRegisters] using
          regs.injective.ne (by decide : (18 : Fin 34) ≠ 19))
  have hrestoredAccumulatorContext :
      AssignmentContext tm instanceData.blockLength
        (store (CombineValue.rangeRegisters regs).accumulator)
        assignment word regs restoredAccumulator :=
    assignmentContext_of_physicalWrite tm regs
      instanceData.blockLength
      (store (CombineValue.rangeRegisters regs).accumulator)
      assignment word 18 derived restoredAccumulator
      hderivedAssignment assignmentContextSlot_ne_18
      (by
        simpa [CombineValue.rangeRegisters] using
          hrestoreAccumulatorOutside)
  have hrestoredAccumulatorEq :
      restoredAccumulator
          (CombineValue.rangeRegisters regs).accumulator =
        store (CombineValue.rangeRegisters regs).accumulator :=
    hrestoreAccumulatorValue.trans hderivedAssignment.cursor_eq
  have hderivedPayload :
      derived (payloadPosition regs) =
        store (CombineValue.rangeRegisters regs).count := by
    calc
      derived (payloadPosition regs) =
          savedCount (payloadPosition regs) := by
        apply hderiveOutside
        · simpa [payloadPosition,
            AssignmentPayloadBit.payloadPosition,
            Layout.codecScratch] using
              fixed_index_not_mem_control regs 31 (by decide)
        · simpa [payloadPosition,
            AssignmentPayloadBit.payloadPosition,
            Layout.codecScratch] using
              fixed_index_not_mem_center regs 31 (by decide)
      _ = savedAccumulator
          (CombineValue.rangeRegisters regs).count :=
        hsaveCountValue
      _ = store (CombineValue.rangeRegisters regs).count := by
        apply hsaveAccumulatorOutside
        simpa [cursor, CombineValue.rangeRegisters] using
          regs.injective.ne (by decide : (10 : Fin 34) ≠ 19)
  have hrestoredPayload :
      restoredAccumulator (payloadPosition regs) =
        store (CombineValue.rangeRegisters regs).count := by
    calc
      restoredAccumulator (payloadPosition regs) =
          derived (payloadPosition regs) := by
        apply hrestoreAccumulatorOutside
        simpa [payloadPosition,
          AssignmentPayloadBit.payloadPosition,
          Layout.codecScratch, CombineValue.rangeRegisters] using
            regs.injective.ne (by decide : (31 : Fin 34) ≠ 18)
      _ = _ := hderivedPayload
  obtain ⟨restored, hrestoreCountRun, hrestoreCountValue,
      hrestoreCountOutside⟩ :=
    copy_runs (CombineValue.rangeRegisters regs).count
      (payloadPosition regs) restoredAccumulator
      (by
        simpa [payloadPosition, AssignmentPayloadBit.payloadPosition,
          Layout.codecScratch, CombineValue.rangeRegisters] using
            regs.injective.ne (by decide : (10 : Fin 34) ≠ 31))
  have hrestoredContext :
      AssignmentContext tm instanceData.blockLength
        (store (CombineValue.rangeRegisters regs).accumulator)
        assignment word regs restored :=
    assignmentContext_of_physicalWrite tm regs
      instanceData.blockLength
      (store (CombineValue.rangeRegisters regs).accumulator)
      assignment word 10 restoredAccumulator restored
      hrestoredAccumulatorContext assignmentContextSlot_ne_10
      (by
        simpa [CombineValue.rangeRegisters] using
          hrestoreCountOutside)
  have hrestoredCountEq :
      restored (CombineValue.rangeRegisters regs).count =
        store (CombineValue.rangeRegisters regs).count :=
    hrestoreCountValue.trans hrestoredPayload
  have hrestoredAccumulatorEq :
      restored (CombineValue.rangeRegisters regs).accumulator =
        store (CombineValue.rangeRegisters regs).accumulator := by
    rw [hrestoreCountOutside
      (CombineValue.rangeRegisters regs).accumulator]
    · exact hrestoredAccumulatorEq
    · simpa [CombineValue.rangeRegisters] using
        regs.injective.ne (by decide : (18 : Fin 34) ≠ 10)
  have hcenterValue :
      restored (CombineSafeCenter.centerValue regs) =
        centers selectedTape := by
    calc
      restored (CombineSafeCenter.centerValue regs) =
          restoredAccumulator
            (CombineSafeCenter.centerValue regs) := by
        apply hrestoreCountOutside
        simpa [CombineSafeCenter.centerValue,
          CombineSafeCenter.centerMap,
          CombineValue.rangeRegisters] using
            regs.injective.ne (by decide : (1 : Fin 34) ≠ 10)
      _ = derived (CombineSafeCenter.centerValue regs) := by
        apply hrestoreAccumulatorOutside
        simpa [CombineSafeCenter.centerValue,
          CombineSafeCenter.centerMap,
          CombineValue.rangeRegisters] using
            regs.injective.ne (by decide : (1 : Fin 34) ≠ 18)
      _ = centers selectedTape :=
        hcenterRaw.trans
          (centerOutputValue_derivedCenter instanceData guessCode
            selectedTape interval hinterval hguess)
  by_cases hcenter : centers selectedTape = 0
  · have htest :
        restored (CombineSafeCenter.centerValue regs) = 0 := by
      rw [hcenterValue, hcenter]
    obtain ⟨final, hbranchRun, hfinalAssignmentRaw⟩ :=
      initializeBoundaryTape_runs tm order selectedTape regs
        instanceData.blockLength instanceData.positive centers
        hcenter
        (store (CombineValue.rangeRegisters regs).accumulator)
        assignment word restored hrestoredContext
    have hfinalAssignment :
        AssignmentContext tm instanceData.blockLength
          ((inputs (.chronological, selectedTape)).headRemainder.val)
          assignment finalWord regs final := by
      simpa [finalWord, cfg, inputs] using hfinalAssignmentRaw
    refine
      ⟨final,
        (inputs
          (.chronological, selectedTape)).headRemainder.val,
        ?_, hfinalAssignment, ?_, ?_⟩
    · simpa [initializeTape, Cmd.seqList] using
        Runs.seq hsaveAccumulatorRun
          (Runs.seq hsaveCountRun
            (Runs.seq hderiveRun
              (Runs.seq hrestoreAccumulatorRun
                (Runs.seq hrestoreCountRun
                  (Runs.ifZero htest hbranchRun)))))
    · calc
        final (CombineValue.rangeRegisters regs).accumulator =
            restored
              (CombineValue.rangeRegisters regs).accumulator := by
          exact Footprint.runs_eq_outside
            (initializeBoundaryTape_writesWithin
              tm selectedTape regs)
            hbranchRun (by simp [emissionFootprint])
        _ = _ := hrestoredAccumulatorEq
    · calc
        final (CombineValue.rangeRegisters regs).count =
            restored (CombineValue.rangeRegisters regs).count := by
          exact Footprint.runs_eq_outside
            (initializeBoundaryTape_writesWithin
              tm selectedTape regs)
            hbranchRun (by simp [emissionFootprint])
        _ = _ := hrestoredCountEq
  · have hcenterPositive : 0 < centers selectedTape :=
      Nat.pos_of_ne_zero hcenter
    have htest :
        restored (CombineSafeCenter.centerValue regs) ≠ 0 := by
      rw [hcenterValue]
      exact hcenter
    obtain ⟨final, hbranchRun, hfinalAssignmentRaw⟩ :=
      initializeRegularTape_runs tm order selectedTape regs
        instanceData.blockLength instanceData.positive centers
        hcenterPositive
        (store (CombineValue.rangeRegisters regs).accumulator)
        assignment word restored hrestoredContext
    have hfinalAssignment :
        AssignmentContext tm instanceData.blockLength
          (instanceData.blockLength +
            (inputs
              (.chronological,
                selectedTape)).headRemainder.val)
          assignment finalWord regs final := by
      simpa [finalWord, cfg, inputs] using hfinalAssignmentRaw
    refine
      ⟨final,
        instanceData.blockLength +
          (inputs
            (.chronological, selectedTape)).headRemainder.val,
        ?_, hfinalAssignment, ?_, ?_⟩
    · simpa [initializeTape, Cmd.seqList] using
        Runs.seq hsaveAccumulatorRun
          (Runs.seq hsaveCountRun
            (Runs.seq hderiveRun
              (Runs.seq hrestoreAccumulatorRun
                (Runs.seq hrestoreCountRun
                  (Runs.ifNonzero htest hbranchRun)))))
    · calc
        final (CombineValue.rangeRegisters regs).accumulator =
            restored
              (CombineValue.rangeRegisters regs).accumulator := by
          exact Footprint.runs_eq_outside
            (initializeRegularTape_writesWithin
              tm selectedTape regs)
            hbranchRun (by simp [emissionFootprint])
        _ = _ := hrestoredAccumulatorEq
    · calc
        final (CombineValue.rangeRegisters regs).count =
            restored (CombineValue.rangeRegisters regs).count := by
          exact Footprint.runs_eq_outside
            (initializeRegularTape_writesWithin
              tm selectedTape regs)
            hbranchRun (by simp [emissionFootprint])
        _ = _ := hrestoredCountEq

private def initializedTapesWord
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (blockLength : ℕ)
    (centers : TapeIndex workTapeCount → ℕ)
    (cfg : Cfg workTapeCount tm.Q)
    (values : List (TapeIndex workTapeCount))
    (word : ℕ) : ℕ :=
  values.foldl
    (fun current tape =>
      PackedDigits.prependFrom
        (PackedLocalConfiguration.radix tm)
        (PackedLocalConfiguration.configurationDigit
          tm order blockLength centers cfg)
        (PackedLocalConfiguration.cellIndex blockLength tape 0)
        (PackedLocalConfiguration.tapeSpan blockLength)
        current)
    word

private theorem reverseRangeSegments_eq
    (base span : ℕ) (digits : ℕ → ℕ) :
    ∀ count suffix,
      List.foldl
          (fun word tape =>
            PackedDigits.prependFrom base digits
              (1 + tape * span) span word)
          suffix (List.range count).reverse =
        PackedDigits.prependFrom base digits 1
          (count * span) suffix := by
  intro count
  induction count with
  | zero =>
      intro suffix
      simp [PackedDigits.prependFrom]
  | succ count ih =>
      intro suffix
      rw [List.range_succ, List.reverse_append]
      simp only [List.reverse_singleton, List.singleton_append,
        List.foldl_cons]
      rw [ih]
      convert
        prependFrom_append base digits 1
          (count * span) span suffix using 1
      all_goals
        ring_nf

private theorem initializedTapesWord_all_eq
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (blockLength : ℕ)
    (centers : TapeIndex workTapeCount → ℕ)
    (cfg : Cfg workTapeCount tm.Q)
    (word : ℕ) :
    initializedTapesWord tm order blockLength centers cfg
        (tapes workTapeCount) word =
      PackedDigits.prependFrom
        (PackedLocalConfiguration.radix tm)
        (PackedLocalConfiguration.configurationDigit
          tm order blockLength centers cfg)
        1
        ((workTapeCount + 2) *
          PackedLocalConfiguration.tapeSpan blockLength)
        word := by
  let step := fun current tape =>
    PackedDigits.prependFrom
      (PackedLocalConfiguration.radix tm)
      (PackedLocalConfiguration.configurationDigit
        tm order blockLength centers cfg)
      (1 + tape *
        PackedLocalConfiguration.tapeSpan blockLength)
      (PackedLocalConfiguration.tapeSpan blockLength)
      current
  have hmapFold :=
    List.foldl_map
      (f := fun tape : TapeIndex workTapeCount => tape.val)
      (g := step)
      (l := (List.finRange (workTapeCount + 2)).reverse)
      (init := word)
  calc
    initializedTapesWord tm order blockLength centers cfg
          (tapes workTapeCount) word =
        List.foldl step word
          (((List.finRange (workTapeCount + 2)).reverse).map
            fun tape => tape.val) := by
      simpa [initializedTapesWord, tapes,
        PackedLocalConfiguration.cellIndex] using hmapFold.symm
    _ =
        List.foldl step word
          (List.range (workTapeCount + 2)).reverse := by
      rw [List.map_reverse, List.map_coe_finRange_eq_range]
    _ = _ :=
      reverseRangeSegments_eq
        (PackedLocalConfiguration.radix tm)
        (PackedLocalConfiguration.tapeSpan blockLength)
        (PackedLocalConfiguration.configurationDigit
          tm order blockLength centers cfg)
        (workTapeCount + 2) word

private theorem initializeTapes_runs
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
    (guessCode :
      Fin
        (3 ^
          NeighborhoodGraph.Guess.Enumeration.movementCount
            workTapeCount instanceData.horizon))
    (assignment : ℕ)
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
        NeighborhoodGraph.Guess.Enumeration.candidateGuess guessCode)
    (hinterval : interval ≤ instanceData.horizon) :
    let centers :=
      NeighborhoodGraph.Guess.Consistency.guessedCenters
        instanceData.guess interval
    let inputs :=
      LocalAssignmentSemantics.assignmentInputs tm order
        instanceData.blockLength instanceData.positive assignment
    let cfg :=
      Guess.Consistency.localStartCfg
        tm instanceData.blockLength centers inputs
    ∀ values offset word store,
      CombineTerm.ComputationContext regs instanceData nodeTape slot
          interval logicalBank store →
      store controller.guess = guessCode.val →
      AssignmentContext tm instanceData.blockLength offset assignment
          word regs store →
      ∃ final finalOffset,
        Runs
          (initializeTapes tm controller regs values)
          store final ∧
        AssignmentContext tm instanceData.blockLength finalOffset
          assignment
          (initializedTapesWord tm order instanceData.blockLength
            centers cfg values word)
          regs final ∧
        final (CombineValue.rangeRegisters regs).accumulator =
          store (CombineValue.rangeRegisters regs).accumulator ∧
        final (CombineValue.rangeRegisters regs).count =
          store (CombineValue.rangeRegisters regs).count := by
  dsimp only
  let centers :=
    NeighborhoodGraph.Guess.Consistency.guessedCenters
      instanceData.guess interval
  let inputs :=
    LocalAssignmentSemantics.assignmentInputs tm order
      instanceData.blockLength instanceData.positive assignment
  let cfg :=
    Guess.Consistency.localStartCfg
      tm instanceData.blockLength centers inputs
  intro values
  induction values with
  | nil =>
      intro offset word store _hcomputation _hstoreGuess
        hassignment
      refine ⟨store, offset, Runs.skip _, ?_, rfl, rfl⟩
      simpa [initializedTapesWord] using hassignment
  | cons tape values ih =>
      intro offset word store hcomputation hstoreGuess
        hassignment
      obtain ⟨afterTape, nextOffset, htapeRun,
          htapeAssignment, htapeAccumulator, htapeCount⟩ :=
        initializeTape_runs order regs instanceData nodeTape slot
          interval logicalBank tape guessCode assignment offset word
          store hfits hcomputation hstoreGuess hguess hinterval
          hassignment
      have hnextComputation :
          CombineTerm.ComputationContext regs instanceData nodeTape
            slot interval logicalBank afterTape :=
        computationContext_of_runs regs instanceData nodeTape slot
          interval logicalBank
          (initializeTape_writesWithin tm controller tape regs)
          htapeRun hcomputation
      have hnextGuess :
          afterTape controller.guess = guessCode.val := by
        calc
          afterTape controller.guess = store controller.guess :=
            controller_guess_eq_of_runs regs
              (initializeTape_writesWithin
                tm controller tape regs)
              htapeRun
          _ = guessCode.val := hstoreGuess
      obtain ⟨final, finalOffset, htailRun,
          hfinalAssignmentRaw, htailAccumulator, htailCount⟩ :=
        ih nextOffset _ afterTape hnextComputation hnextGuess
          htapeAssignment
      have hfinalAssignment :
          AssignmentContext tm instanceData.blockLength finalOffset
            assignment
            (initializedTapesWord tm order
              instanceData.blockLength centers cfg
              (tape :: values) word)
            regs final := by
        simpa [initializedTapesWord, centers, inputs, cfg] using
          hfinalAssignmentRaw
      exact
        ⟨final, finalOffset,
          Runs.seq htapeRun htailRun, hfinalAssignment,
          htailAccumulator.trans htapeAccumulator,
          htailCount.trans htapeCount⟩

private def statePosition
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (blockLength : ℕ) (state : tm.Q) :
    Fin
      (NeighborhoodExecutableEvaluation.payloadWidth tm blockLength) :=
  ⟨CompactValueCodeSemantics.stateCode order state, by
    change
      (order.state state).val <
        ComputationGraph.CompactEncoding.width blockLength tm.Q
    rw [ComputationGraph.CompactEncoding.width_eq]
    have hstate := (order.state state).isLt
    omega⟩

private def stateBits
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (blockLength code : ℕ) (state : tm.Q) : Bool :=
  AssignmentCodeSemantics.assignmentBits
    (NeighborhoodExecutableEvaluation.payloadWidth tm blockLength)
    (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount)
    code
    (childIndex workTapeCount
      (.chronological, TapeIndex.input workTapeCount))
    (statePosition tm order blockLength state)

private theorem stateBits_eq_bitsAt
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (blockLength code : ℕ) (state : tm.Q) :
    stateBits tm order blockLength code state =
      NeighborhoodExecutableEvaluation.bitsAt
        (NeighborhoodExecutableEvaluation.FiniteEncoding.ofStateOrder
          order blockLength)
        (AssignmentCodeSemantics.assignmentBits
          (NeighborhoodExecutableEvaluation.payloadWidth tm blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount)
          code
          (childIndex workTapeCount
            (.chronological, TapeIndex.input workTapeCount)))
        (.inl state) := by
  unfold stateBits NeighborhoodExecutableEvaluation.bitsAt
  apply congrArg
    (AssignmentCodeSemantics.assignmentBits
      (NeighborhoodExecutableEvaluation.payloadWidth tm blockLength)
      (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount)
      code
      (childIndex workTapeCount
        (.chronological, TapeIndex.input workTapeCount)))
  apply Fin.ext
  simp [statePosition, CompactValueCodeSemantics.stateCode,
    NeighborhoodExecutableEvaluation.FiniteEncoding.ofStateOrder,
    NeighborhoodExecutableEvaluation.FiniteEncoding.coordinateEquiv]

private theorem readStateBit_runs
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (state : tm.Q)
    (regs : NeighborhoodTrial.Registers controller)
    (blockLength offset code word : ℕ)
    (store : Store)
    (hcontext :
      AssignmentContext tm blockLength offset code word regs store) :
    ∃ final,
      Runs (readStateBit tm order state regs) store final ∧
      final (decodedValue regs) =
        (stateBits tm order blockLength code state).toNat ∧
      AssignmentContext tm blockLength offset code word regs final := by
  obtain ⟨positioned, hpositionRun, hpositionValue,
      hpositionContext⟩ :=
    setPayloadPosition_runs tm regs blockLength offset code word
      (statePosition tm order blockLength state).val store hcontext
  obtain ⟨final, hreadRun, hreadValue, _hpayload,
      hfinalContext⟩ :=
    payloadRead_runs tm regs blockLength offset code word
      (childIndex workTapeCount
        (.chronological, TapeIndex.input workTapeCount))
      (statePosition tm order blockLength state)
      positioned hpositionContext hpositionValue
  refine ⟨final, ?_, ?_, hfinalContext⟩
  · exact Runs.seq hpositionRun hreadRun
  · simpa [stateBits] using hreadValue

private def decodedState
    (tm : TM workTapeCount)
    (bits : tm.Q → Bool) : List tm.Q → tm.Q
  | [] => tm.qstart
  | state :: sourceStates =>
      if bits state then state
      else decodedState tm bits sourceStates

private theorem decodeStates_runs
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (regs : NeighborhoodTrial.Registers controller)
    (blockLength offset code word : ℕ)
    (bits : tm.Q → Bool)
    (hbits :
      bits = stateBits tm order blockLength code) :
    ∀ sourceStates store,
      AssignmentContext tm blockLength offset code word regs store →
      ∃ final,
        Runs (decodeStates tm order regs sourceStates) store final ∧
        final (decodedValue regs) =
          CompactValueCodeSemantics.stateCode order
            (decodedState tm bits sourceStates) ∧
        AssignmentContext tm blockLength offset code word regs final := by
  intro sourceStates
  induction sourceStates with
  | nil =>
      intro store hcontext
      obtain ⟨final, hrun, hvalue, hfinalContext⟩ :=
        setDecoded_runs tm regs blockLength offset code word
          (CompactValueCodeSemantics.stateCode order tm.qstart)
          store hcontext
      refine ⟨final, ?_, ?_, hfinalContext⟩
      · simpa [decodeStates] using hrun
      · simpa [decodedState] using hvalue
  | cons state sourceStates ih =>
      intro store hcontext
      obtain ⟨afterRead, hreadRun, hreadValueRaw, hreadContext⟩ :=
        readStateBit_runs tm order state regs blockLength offset code
          word store hcontext
      have hreadValue :
          afterRead (decodedValue regs) = (bits state).toNat := by
        simpa [hbits] using hreadValueRaw
      by_cases hstate : bits state = true
      · obtain ⟨final, hsetRun, hsetValue, hfinalContext⟩ :=
          setDecoded_runs tm regs blockLength offset code word
            (CompactValueCodeSemantics.stateCode order state)
            afterRead hreadContext
        have htest : afterRead (decodedValue regs) ≠ 0 := by
          rw [hreadValue, hstate]
          decide
        refine ⟨final, ?_, ?_, hfinalContext⟩
        · simpa [decodeStates] using
            Runs.seq hreadRun (Runs.ifNonzero htest hsetRun)
        · simpa [decodedState, hstate] using hsetValue
      · have hstateFalse : bits state = false :=
          Bool.eq_false_of_not_eq_true hstate
        have htest : afterRead (decodedValue regs) = 0 := by
          rw [hreadValue, hstateFalse]
          rfl
        obtain ⟨final, htailRun, htailValue, hfinalContext⟩ :=
          ih afterRead hreadContext
        refine ⟨final, ?_, ?_, hfinalContext⟩
        · simpa [decodeStates] using
            Runs.seq hreadRun (Runs.ifZero htest htailRun)
        · simpa [decodedState, hstateFalse] using htailValue

private theorem decodedState_eq_find?
    (tm : TM workTapeCount)
    (bits : tm.Q → Bool) :
    ∀ sourceStates,
      decodedState tm bits sourceStates =
        (sourceStates.find? bits).getD tm.qstart := by
  intro sourceStates
  induction sourceStates with
  | nil =>
      rfl
  | cons state sourceStates ih =>
      simp only [decodedState, List.find?_cons]
      split <;> simp_all

private theorem find?_map_getD
    {α β : Type*} (transform : α → β) (predicate : β → Bool)
    (default : α) :
    ∀ (values : List α),
      ((values.map transform).find? predicate).getD
          (transform default) =
        transform
          ((values.find? fun value => predicate (transform value)).getD
            default) := by
  intro values
  induction values with
  | nil =>
      rfl
  | cons value values ih =>
      simp only [List.map_cons, List.find?_cons]
      split <;> simp_all

private theorem decodedState_states
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (code : ℕ) :
    decodedState tm (stateBits tm order blockLength code)
        (states tm order) =
      (LocalAssignmentSemantics.assignmentInputs
        tm order blockLength hpositive code
        (.chronological, TapeIndex.input workTapeCount)).state := by
  rw [decodedState_eq_find?]
  let predicate : tm.Q → Bool :=
    stateBits tm order blockLength code
  let indexed : Fin (Fintype.card tm.Q) → Bool :=
    fun index => predicate (order.state.symm index)
  have hindexed :
      indexed =
        fun index =>
          NeighborhoodExecutableEvaluation.bitsAt
            (NeighborhoodExecutableEvaluation.FiniteEncoding.ofStateOrder
              order blockLength)
            (AssignmentCodeSemantics.assignmentBits
              (NeighborhoodExecutableEvaluation.payloadWidth
                tm blockLength)
              (NeighborhoodExecutableEvaluation.graphFanIn
                workTapeCount)
              code
              (childIndex workTapeCount
                (.chronological, TapeIndex.input workTapeCount)))
            (.inl (order.state.symm index)) := by
    funext index
    exact stateBits_eq_bitsAt tm order blockLength code
      (order.state.symm index)
  unfold states LocalAssignmentSemantics.assignmentInputs
    NeighborhoodExecutableEvaluation.decodeBits
    NeighborhoodExecutableEvaluation.firstTrueFin
  change
    ((((List.finRange (Fintype.card tm.Q)).map order.state.symm).find?
        predicate).getD tm.qstart) =
      order.state.symm
        (((List.finRange (Fintype.card tm.Q)).find?
          (fun index =>
            NeighborhoodExecutableEvaluation.bitsAt
              (NeighborhoodExecutableEvaluation.FiniteEncoding.ofStateOrder
                order blockLength)
              (AssignmentCodeSemantics.assignmentBits
                (NeighborhoodExecutableEvaluation.payloadWidth
                  tm blockLength)
                (NeighborhoodExecutableEvaluation.graphFanIn
                  workTapeCount)
                code
                (childIndex workTapeCount
                  (.chronological,
                    TapeIndex.input workTapeCount)))
              (.inl (order.state.symm index)))).getD
            (order.state tm.qstart))
  calc
    (((List.finRange (Fintype.card tm.Q)).map order.state.symm).find?
          predicate).getD tm.qstart =
        (((List.finRange (Fintype.card tm.Q)).map
          order.state.symm).find? predicate).getD
          (order.state.symm (order.state tm.qstart)) := by
            exact congrArg
              (fun default =>
                (((List.finRange (Fintype.card tm.Q)).map
                  order.state.symm).find? predicate).getD default)
              (order.state.left_inv tm.qstart).symm
    _ = order.state.symm
          (((List.finRange (Fintype.card tm.Q)).find? indexed).getD
            (order.state tm.qstart)) := by
      exact find?_map_getD order.state.symm predicate
        (order.state tm.qstart) _
    _ = _ := by rw [hindexed]

private theorem initializeState_runs
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (regs : NeighborhoodTrial.Registers controller)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (offset code word : ℕ)
    (store : Store)
    (hcontext :
      AssignmentContext tm blockLength offset code word regs store) :
    let state :=
      (LocalAssignmentSemantics.assignmentInputs
        tm order blockLength hpositive code
        (.chronological, TapeIndex.input workTapeCount)).state
    ∃ final,
      Runs (initializeState tm order regs) store final ∧
      AssignmentContext tm blockLength offset code
        (PackedDigits.push
          (PackedLocalConfiguration.radix tm)
          (CompactValueCodeSemantics.stateCode order state)
          word)
        regs final := by
  dsimp only
  obtain ⟨decoded, hdecodeRun, hdecodeValueRaw, hdecodeContext⟩ :=
    decodeStates_runs tm order regs blockLength offset code word
      (stateBits tm order blockLength code) rfl
      (states tm order) store hcontext
  have hdecodeValue :
      decoded (decodedValue regs) =
        CompactValueCodeSemantics.stateCode order
          (LocalAssignmentSemantics.assignmentInputs
            tm order blockLength hpositive code
            (.chronological,
              TapeIndex.input workTapeCount)).state := by
    exact hdecodeValueRaw.trans
      (congrArg (CompactValueCodeSemantics.stateCode order)
        (decodedState_states tm order blockLength hpositive code))
  obtain ⟨final, hpushRun, hfinalContext⟩ :=
    pushDecoded_context_runs tm regs blockLength offset code word
      (CompactValueCodeSemantics.stateCode order
        (LocalAssignmentSemantics.assignmentInputs
          tm order blockLength hpositive code
          (.chronological, TapeIndex.input workTapeCount)).state)
      decoded hdecodeContext hdecodeValue
  exact ⟨final, Runs.seq hdecodeRun hpushRun, hfinalContext⟩

private theorem digitBase_eq_chunkPower
    {tm : TM workTapeCount}
    (instanceData : NeighborhoodProgram.ResidueInstance tm) :
    Representation.digitBase instanceData =
      2 ^
        PrimeGrouped.Logarithmic.chunkBits
          (NeighborhoodExecutableEvaluation.payloadWidth
            tm instanceData.blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn
            workTapeCount) := by
  unfold Representation.digitBase CandidateParameters.domainSize
  rw [Representation.payloadWidth_eq_booleanWidth instanceData]
  rfl

private theorem statePush_allTapes_eq_assignmentStartWord
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (guess : Guess.CenterGuess workTapeCount horizon)
    (interval : Fin horizon)
    (code suffix : ℕ) :
    let centers :=
      Guess.Consistency.guessedCenters guess interval.val
    let inputs :=
      LocalAssignmentSemantics.assignmentInputs
        tm order blockLength hpositive code
    let cfg :=
      Guess.Consistency.localStartCfg
        tm blockLength centers inputs
    PackedDigits.push
        (PackedLocalConfiguration.radix tm)
        (CompactValueCodeSemantics.stateCode order
          (inputs
            (.chronological,
              TapeIndex.input workTapeCount)).state)
        (PackedDigits.prependFrom
          (PackedLocalConfiguration.radix tm)
          (PackedLocalConfiguration.configurationDigit
            tm order blockLength centers cfg)
          1
          ((workTapeCount + 2) *
            PackedLocalConfiguration.tapeSpan blockLength)
          suffix) =
      PackedLocalConfiguration.assignmentStartWord
        tm order blockLength hpositive guess interval code suffix := by
  dsimp only
  unfold PackedLocalConfiguration.assignmentStartWord
    PackedLocalConfiguration.encodeAbove PackedDigits.prepend
    PackedLocalConfiguration.digitCount
  rw [show
      1 + (workTapeCount + 2) *
          PackedLocalConfiguration.tapeSpan blockLength =
        (workTapeCount + 2) *
            PackedLocalConfiguration.tapeSpan blockLength + 1 by
      omega]
  rw [PackedDigits.prependFrom]
  rfl

theorem build_runs_internal
    {tm : TM workTapeCount}
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (nodeTape : TapeIndex workTapeCount)
    (slot : NeighborhoodGraph.Slot)
    (interval : Fin instanceData.horizon)
    (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (guessCode :
      Fin
        (3 ^
          NeighborhoodGraph.Guess.Enumeration.movementCount
            workTapeCount instanceData.horizon))
    (assignment suffix : ℕ)
    (store : Store)
    (hfits :
      ∀ digit ∈
          FrameCodec.nodeDigits
            (show
              NeighborhoodEvaluator.QueryNode
                workTapeCount instanceData.horizon
              from .graph
                (.computation nodeTape slot interval.val)),
        digit < Representation.digitBase instanceData)
    (hcomputation :
      CombineTerm.ComputationContext regs instanceData nodeTape slot
        interval.val logicalBank store)
    (hstoreGuess :
      store controller.guess = guessCode.val)
    (hguess :
      instanceData.guess =
        NeighborhoodGraph.Guess.Enumeration.candidateGuess guessCode)
    (hassignment :
      store (CombineValue.rangeRegisters regs).remaining =
        assignment)
    (hword : store (packedWord regs) = suffix)
    (hone :
      store (CombineValue.rangeRegisters regs).one = 1) :
    ∃ final,
      Runs (build tm order controller regs) store final ∧
      Post tm order instanceData.blockLength instanceData.positive
        instanceData.guess interval assignment suffix regs
        store final := by
  let centers :=
    Guess.Consistency.guessedCenters
      instanceData.guess interval.val
  let inputs :=
    LocalAssignmentSemantics.assignmentInputs tm order
      instanceData.blockLength instanceData.positive assignment
  let cfg :=
    Guess.Consistency.localStartCfg
      tm instanceData.blockLength centers inputs
  let tapeWord :=
    PackedDigits.prependFrom
      (PackedLocalConfiguration.radix tm)
      (PackedLocalConfiguration.configurationDigit tm order
        instanceData.blockLength centers cfg)
      1
      ((workTapeCount + 2) *
        PackedLocalConfiguration.tapeSpan instanceData.blockLength)
      suffix
  have hinitial :
      AssignmentContext tm instanceData.blockLength
        (store (cursor regs)) assignment suffix regs store :=
    { blockLength_eq :=
        hcomputation.parameters.blockLength_eq
      cursor_eq := rfl
      assignment_eq := hassignment
      one_eq := hone
      word_eq := hword
      chunkCount_eq :=
        hcomputation.parameters.chunkCount_eq
      chunkRadix_eq :=
        hcomputation.parameters.digitBase_eq.trans
          (digitBase_eq_chunkPower instanceData) }
  have hinterval : interval.val ≤ instanceData.horizon := by
    omega
  obtain ⟨afterTapes, tapeOffset, htapesRun,
      htapesContextRaw, htapesAccumulator, htapesCount⟩ :=
    initializeTapes_runs order regs instanceData nodeTape slot
      interval.val logicalBank guessCode assignment hfits hguess
      hinterval (tapes workTapeCount) (store (cursor regs)) suffix
      store hcomputation hstoreGuess hinitial
  rw [initializedTapesWord_all_eq tm order
    instanceData.blockLength centers cfg suffix] at htapesContextRaw
  have htapesContext :
      AssignmentContext tm instanceData.blockLength tapeOffset
        assignment tapeWord regs afterTapes := by
    simpa [tapeWord, centers, inputs, cfg] using
      htapesContextRaw
  obtain ⟨final, hstateRun, hfinalContextRaw⟩ :=
    initializeState_runs tm order regs instanceData.blockLength
      instanceData.positive tapeOffset assignment tapeWord
      afterTapes htapesContext
  have hfinalContext :
      AssignmentContext tm instanceData.blockLength tapeOffset
        assignment
        (PackedLocalConfiguration.assignmentStartWord tm order
          instanceData.blockLength instanceData.positive
          instanceData.guess interval assignment suffix)
        regs final := by
    rw [← statePush_allTapes_eq_assignmentStartWord tm order
      instanceData.blockLength instanceData.positive
      instanceData.guess interval assignment suffix]
    simpa [tapeWord, centers, inputs, cfg] using
      hfinalContextRaw
  have hrun :
      Runs (build tm order controller regs) store final := by
    exact Runs.seq htapesRun hstateRun
  have hwrites :=
    build_writesWithin_internal tm order controller regs
  have hstateAccumulator :
      final (CombineValue.rangeRegisters regs).accumulator =
        afterTapes
          (CombineValue.rangeRegisters regs).accumulator :=
    Footprint.runs_eq_outside
      (initializeState_writesWithin tm order regs)
      hstateRun (by simp [emissionFootprint])
  have hstateCount :
      final (CombineValue.rangeRegisters regs).count =
        afterTapes (CombineValue.rangeRegisters regs).count :=
    Footprint.runs_eq_outside
      (initializeState_writesWithin tm order regs)
      hstateRun (by simp [emissionFootprint])
  refine ⟨final, hrun, ?_⟩
  exact
    { word_eq := hfinalContext.word_eq
      assignment_eq := hfinalContext.assignment_eq
      accumulator_eq :=
        hstateAccumulator.trans htapesAccumulator
      modulus_eq := by
        simpa [CombineValue.rangeRegisters] using
          Footprint.runs_eq_outside hwrites hrun
            (fixed_index_not_mem_footprint regs 24
              (by decide))
      modulusPred_eq := by
        simpa [CombineValue.rangeRegisters] using
          Footprint.runs_eq_outside hwrites hrun
            (fixed_index_not_mem_footprint regs 16
              (by decide))
      one_eq := hfinalContext.one_eq
      count_eq := hstateCount.trans htapesCount
      catalyticWord_eq := by
        simpa [NeighborhoodTrial.Registers.layout] using
          Footprint.runs_eq_outside hwrites hrun
            (fixed_index_not_mem_footprint regs 33
              (by decide))
      abi := preservesABI_of_runs regs hwrites hrun
      eq_outside := fun address haddress =>
        Footprint.runs_eq_outside hwrites hrun haddress }

end Internal
end PackedLocalInitialization
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
