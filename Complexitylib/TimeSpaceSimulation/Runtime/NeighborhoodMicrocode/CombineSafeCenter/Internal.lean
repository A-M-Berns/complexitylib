/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.CombineSafeCenter.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.ChildNode
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.CombineTerm

/-!
# Correctness internals for combine-safe center reconstruction
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace CombineSafeCenter
namespace Internal

open RAM Structured

variable {controller : SearchProgram.Registers}

private theorem basics_runs (ops : List Basic) (store : Store) :
    Runs (Cmd.basics ops) store (Basic.execList ops store) := by
  obtain ⟨cost, space, hexec⟩ :=
    RAM.Structured.Internal.exec_basics_exists ops store
  exact ⟨ops.length, cost, space, hexec⟩

private theorem copy_update_runs
    {destination source : ℕ} (store : Store)
    (hne : destination ≠ source) :
    Runs (CombineTerm.copy destination source) store
      (Function.update store destination (store source)) := by
  apply Runs.seq (Runs.basic (.imm destination 0) store)
  simpa [CombineTerm.copy, Basic.exec, Function.update_of_ne,
    hne, Ne.symm hne] using
    Runs.basic
      (.add destination source destination)
      (Basic.exec (.imm destination 0) store)

private theorem cmdWritesWithin_mono
    {small large : Finset ℕ} {cmd : Cmd}
    (hwrites : Footprint.CmdWritesWithin small cmd)
    (hsubset : small ⊆ large) :
    Footprint.CmdWritesWithin large cmd := by
  induction cmd with
  | skip =>
      trivial
  | basic op =>
      cases op <;>
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

private theorem scratch_index_mem
    (regs : NeighborhoodTrial.Registers controller)
    (slot : Fin 11) :
    regs.index (scratchMap slot) ∈ footprint regs :=
  Finset.mem_image.mpr ⟨slot, Finset.mem_univ _, rfl⟩

private theorem center_index_mem
    (regs : NeighborhoodTrial.Registers controller)
    (slot : Fin 5) :
    regs.index (centerMap slot) ∈ footprint regs := by
  fin_cases slot
  · simpa [centerMap, scratchMap] using
      scratch_index_mem regs (6 : Fin 11)
  · simpa [centerMap, scratchMap] using
      scratch_index_mem regs (7 : Fin 11)
  · simpa [centerMap, scratchMap] using
      scratch_index_mem regs (8 : Fin 11)
  · simpa [centerMap, scratchMap] using
      scratch_index_mem regs (9 : Fin 11)
  · simpa [centerMap, scratchMap] using
      scratch_index_mem regs (10 : Fin 11)

private theorem digit_index_mem
    (regs : NeighborhoodTrial.Registers controller)
    (slot : Fin 6) :
    regs.index (digitMap slot) ∈ footprint regs := by
  fin_cases slot
  · simpa [digitMap, scratchMap] using
      scratch_index_mem regs (0 : Fin 11)
  · simpa [digitMap, scratchMap] using
      scratch_index_mem regs (1 : Fin 11)
  · simpa [digitMap, scratchMap] using
      scratch_index_mem regs (2 : Fin 11)
  · simpa [digitMap, scratchMap] using
      scratch_index_mem regs (3 : Fin 11)
  · simpa [digitMap, scratchMap] using
      scratch_index_mem regs (4 : Fin 11)
  · simpa [digitMap, scratchMap] using
      scratch_index_mem regs (5 : Fin 11)

private theorem digit_writeFootprint_subset
    (regs : NeighborhoodTrial.Registers controller) :
    (digitRegisters regs).writeFootprint ⊆ footprint regs := by
  intro address haddress
  simp only [CombineTerm.DigitRegisters.writeFootprint,
    Finset.mem_insert, Finset.mem_singleton] at haddress
  rcases haddress with haddress | haddress | haddress |
      haddress | haddress
  all_goals
    subst address
  · exact digit_index_mem regs 0
  · exact digit_index_mem regs 1
  · exact digit_index_mem regs 2
  · exact digit_index_mem regs 3
  · exact digit_index_mem regs 5

private theorem copy_writesWithin
    (regs : NeighborhoodTrial.Registers controller)
    (destination source : ℕ)
    (hmem : destination ∈ footprint regs) :
    Footprint.CmdWritesWithin (footprint regs)
      (CombineTerm.copy destination source) := by
  apply cmdWritesWithin_mono (small := {destination})
  · simp [CombineTerm.copy, Footprint.CmdWritesWithin,
      Footprint.BasicWritesWithin]
  · simpa using hmem

private theorem advanceCenter_writesWithin
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (footprint regs)
      (advanceCenter regs) := by
  simp [advanceCenter, Cmd.basics, Cmd.seqList,
    Footprint.CmdWritesWithin, Footprint.BasicWritesWithin,
    center_index_mem]

private theorem invalidateCenter_writesWithin
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (footprint regs)
      (invalidateCenter regs) := by
  simp [invalidateCenter, Cmd.basics, Cmd.seqList,
    Footprint.CmdWritesWithin, Footprint.BasicWritesWithin,
    center_index_mem]

private theorem applySelectedMovement_writesWithin
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (footprint regs)
      (applySelectedMovement regs) := by
  simp only [applySelectedMovement, applyLeftMovement,
    applyNonleftMovement, Footprint.CmdWritesWithin]
  refine ⟨⟨invalidateCenter_writesWithin regs, ?_⟩, ?_⟩
  · exact ⟨center_index_mem regs 1,
      advanceCenter_writesWithin regs⟩
  · refine ⟨digit_index_mem regs 2,
      advanceCenter_writesWithin regs, ?_⟩
    exact ⟨center_index_mem regs 1,
      advanceCenter_writesWithin regs⟩

private theorem initializeCenter_writesWithin
    (workTapeCount : ℕ)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (footprint regs)
      (initializeCenter workTapeCount regs) := by
  simp only [initializeCenter, Cmd.seqList,
    Footprint.CmdWritesWithin]
  exact
    ⟨copy_writesWithin regs _ _ (center_index_mem regs 3),
      copy_writesWithin regs _ _ (center_index_mem regs 4),
      digit_index_mem regs 3,
      digit_index_mem regs 4,
      center_index_mem regs 1,
      center_index_mem regs 2,
      center_index_mem regs 0⟩

private theorem centerStep_writesWithin
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (footprint regs)
      (centerStep controller regs) := by
  simp only [centerStep, Cmd.seqList,
    Footprint.CmdWritesWithin]
  exact
    ⟨copy_writesWithin regs _ _ (digit_index_mem regs 5),
      copy_writesWithin regs _ _ (digit_index_mem regs 0),
      cmdWritesWithin_mono
        (CombineTerm.seekDigit_writesWithin (digitRegisters regs))
        (digit_writeFootprint_subset regs),
      applySelectedMovement_writesWithin regs⟩

theorem deriveCenter_writesWithin_internal
    (workTapeCount : ℕ)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (footprint regs)
      (deriveCenter workTapeCount controller regs) := by
  exact
    ⟨initializeCenter_writesWithin workTapeCount regs,
      centerStep_writesWithin controller regs⟩

theorem deriveCenter_compiledWritesWithin_internal
    (workTapeCount : ℕ)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) :
    RAM.RegisterStore.DenseOverlay.FixedRegisters.Footprint.ProgramWritesWithin
      (deriveCenter workTapeCount controller regs).compile
      (footprint regs) :=
  Footprint.programWritesWithin_compile
    (deriveCenter_writesWithin_internal
      workTapeCount controller regs)

theorem footprint_subset_combineScratch_internal
    (regs : NeighborhoodTrial.Registers controller) :
    footprint regs ⊆ CombineValue.combineScratchFootprint regs := by
  intro address haddress
  simp only [footprint, Finset.mem_image, Finset.mem_univ,
    true_and] at haddress
  obtain ⟨slot, rfl⟩ := haddress
  fin_cases slot
  all_goals
    simp [scratchMap, CombineValue.combineScratchFootprint,
      CombineValue.combineScratchMap]
  all_goals
    first
    | exact ⟨0, rfl⟩
    | exact ⟨2, rfl⟩
    | exact ⟨3, rfl⟩
    | exact ⟨5, rfl⟩
    | exact ⟨7, rfl⟩
    | exact ⟨15, rfl⟩
    | exact ⟨4, rfl⟩
    | exact ⟨1, rfl⟩
    | exact ⟨8, rfl⟩
    | exact ⟨12, rfl⟩
    | exact ⟨14, rfl⟩

private theorem fixed_index_not_mem
    (regs : NeighborhoodTrial.Registers controller)
    (slot : Fin 34)
    (hslot : ∀ scratch, slot ≠ scratchMap scratch) :
    regs.index slot ∉ footprint regs := by
  intro haddress
  simp only [footprint, Finset.mem_image, Finset.mem_univ,
    true_and] at haddress
  obtain ⟨scratch, heq⟩ := haddress
  exact hslot scratch (regs.injective heq.symm)

private theorem controller_guess_not_mem
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) :
    controller.guess ∉ footprint regs := by
  intro haddress
  simp only [footprint, Finset.mem_image, Finset.mem_univ,
    true_and] at haddress
  obtain ⟨slot, hslot⟩ := haddress
  exact regs.index_ne_controller (scratchMap slot) 2 hslot

theorem deriveCenter_preservesCombine_internal
    (workTapeCount : ℕ)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    {initial final : Store}
    (hrun :
      Runs (deriveCenter workTapeCount controller regs)
        initial final) :
    PreservesCombine regs initial final := by
  have preserve :
      ∀ slot : Fin 34,
        (∀ scratch, slot ≠ scratchMap scratch) →
        final (regs.index slot) = initial (regs.index slot) := by
    intro slot hslot
    exact Footprint.runs_eq_outside
      (deriveCenter_writesWithin_internal
        workTapeCount controller regs)
      hrun (fixed_index_not_mem regs slot hslot)
  have fixed
      (slot : Fin 34)
      (hslot : ∀ scratch, slot ≠ scratchMap scratch) :
      final (regs.index slot) = initial (regs.index slot) :=
    preserve slot hslot
  refine
    { accumulator_eq := ?_
      assignment_eq := ?_
      term_eq := ?_
      one_eq := ?_
      count_eq := ?_
      codecScratch_eq := ?_
      stack_eq := ?_
      bank_eq := ?_
      abi := ?_ }
  · simpa [CombineValue.rangeRegisters] using
      fixed 18 (by
        intro scratch
        fin_cases scratch <;> decide)
  · simpa [CombineValue.rangeRegisters] using
      fixed 21 (by
        intro scratch
        fin_cases scratch <;> decide)
  · simpa [CombineValue.rangeRegisters] using
      fixed 19 (by
        intro scratch
        fin_cases scratch <;> decide)
  · simpa [CombineValue.rangeRegisters] using
      fixed 17 (by
        intro scratch
        fin_cases scratch <;> decide)
  · simpa [CombineValue.rangeRegisters] using
      fixed 10 (by
        intro scratch
        fin_cases scratch <;> decide)
  · exact fixed 31 (by
      intro scratch
      fin_cases scratch <;> decide)
  · exact fixed 32 (by
      intro scratch
      fin_cases scratch <;> decide)
  · exact fixed 33 (by
      intro scratch
      fin_cases scratch <;> decide)
  · exact
      { fuel_eq := fixed 22 (by
          intro scratch
          fin_cases scratch <;> decide)
        nodeCode_eq := fixed 23 (by
          intro scratch
          fin_cases scratch <;> decide)
        scalar_eq := fixed 25 (by
          intro scratch
          fin_cases scratch <;> decide)
        out_eq := fixed 26 (by
          intro scratch
          fin_cases scratch <;> decide)
        phaseCode_eq := fixed 27 (by
          intro scratch
          fin_cases scratch <;> decide)
        active_eq := fixed 28 (by
          intro scratch
          fin_cases scratch <;> decide)
        blockLength_eq := fixed 2 (by
          intro scratch
          fin_cases scratch <;> decide)
        horizon_eq := fixed 3 (by
          intro scratch
          fin_cases scratch <;> decide)
        chunkCount_eq := fixed 7 (by
          intro scratch
          fin_cases scratch <;> decide)
        chunkRadix_eq := fixed 8 (by
          intro scratch
          fin_cases scratch <;> decide)
        frameRadix_eq := fixed 13 (by
          intro scratch
          fin_cases scratch <;> decide)
        bankRadix_eq := fixed 14 (by
          intro scratch
          fin_cases scratch <;> decide)
        bankDigitCount_eq := fixed 15 (by
          intro scratch
          fin_cases scratch <;> decide)
        modulusPred_eq := fixed 16 (by
          intro scratch
          fin_cases scratch <;> decide)
        modulus_eq := fixed 24 (by
          intro scratch
          fin_cases scratch <;> decide) }

private theorem digit_index_ne_center
    (regs : NeighborhoodTrial.Registers controller)
    (digit : Fin 6) (center : Fin 5) :
    regs.index (digitMap digit) ≠
      regs.index (centerMap center) := by
  apply regs.injective.ne
  fin_cases digit <;> fin_cases center <;>
    decide

private theorem center_not_mem_digitWriteFootprint
    (regs : NeighborhoodTrial.Registers controller)
    (slot : Fin 5) :
    regs.index (centerMap slot) ∉
      (digitRegisters regs).writeFootprint := by
  simp only [CombineTerm.DigitRegisters.writeFootprint,
    Finset.mem_insert, Finset.mem_singleton, not_or]
  exact
    ⟨(digit_index_ne_center regs 0 slot).symm,
      (digit_index_ne_center regs 1 slot).symm,
      (digit_index_ne_center regs 2 slot).symm,
      (digit_index_ne_center regs 3 slot).symm,
      (digit_index_ne_center regs 5 slot).symm⟩

private theorem guess_not_mem_digitWriteFootprint
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) :
    controller.guess ∉
      (digitRegisters regs).writeFootprint := by
  intro haddress
  simp only [CombineTerm.DigitRegisters.writeFootprint,
    Finset.mem_insert, Finset.mem_singleton] at haddress
  rcases haddress with haddress | haddress | haddress |
      haddress | haddress
  all_goals
    exact regs.index_ne_controller _ 2 haddress.symm

private theorem radixDigit_eq_movementDigitValue
    (word index : ℕ) :
    CombineTerm.radixDigit 3 word index =
      ChildNode.movementDigitValue word index := by
  rw [ChildNode.movementDigitValue_eq_digit]
  rfl

private theorem applySelectedMovement_runs
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store)
    (digit center remaining index stride : ℕ)
    (hdigit :
      store (digitRegisters regs).value = digit)
    (hone : store (digitRegisters regs).one = 1)
    (hdivisor : store (digitRegisters regs).divisor = 3)
    (hcenter : store (centerValue regs) = center)
    (hvalid : store (centerValid regs) = 1)
    (hremaining : store (centerRemaining regs) = remaining)
    (hindex : store (centerNextIndex regs) = index)
    (hstride : store (centerStride regs) = stride) :
    ∃ final,
      Runs (applySelectedMovement regs) store final ∧
      let result := ChildNode.applyMovementDigit digit center
      final (centerValid regs) =
          ChildNode.centerValidValue result ∧
        final (centerValue regs) =
          ChildNode.centerOutputValue result ∧
        final (centerRemaining regs) =
          ChildNode.centerRemainingValue remaining result ∧
        final (centerNextIndex regs) =
          ChildNode.centerNextIndexValue index stride result ∧
        final (digitRegisters regs).one = 1 ∧
        final (digitRegisters regs).divisor = 3 ∧
        final (centerStride regs) = stride := by
  by_cases hdigitZero : digit = 0
  · have hvalueZero :
        store (digitRegisters regs).value = 0 := by
      rw [hdigit, hdigitZero]
    by_cases hcenterZero : center = 0
    · have hstoredCenterZero :
          store (centerValue regs) = 0 := by
        rw [hcenter, hcenterZero]
      let final :=
        Basic.execList
          [.imm (centerValid regs) 0,
            .imm (centerRemaining regs) 0] store
      have hbranch :
          Runs (invalidateCenter regs) store final := by
        simpa [invalidateCenter] using
          basics_runs
            [.imm (centerValid regs) 0,
              .imm (centerRemaining regs) 0] store
      have hrun :
          Runs (applySelectedMovement regs) store final := by
        exact Runs.ifZero hvalueZero
          (Runs.ifZero hstoredCenterZero hbranch)
      refine ⟨final, hrun, ?_⟩
      simp [ChildNode.applyMovementDigit, hdigitZero,
        hcenterZero, ChildNode.centerValidValue,
        ChildNode.centerOutputValue,
        ChildNode.centerRemainingValue,
        ChildNode.centerNextIndexValue, final,
        Basic.execList, Basic.exec, hcenter, hindex,
        hstride, centerMap, digitRegisters, digitMap,
        regs.injective.eq_iff]
      exact ⟨hone, hdivisor⟩
    · let decreased :=
        (Basic.sub (centerValue regs) (centerValue regs)
          (digitRegisters regs).one).exec store
      let final :=
        Basic.execList
          [.add (centerNextIndex regs)
              (centerNextIndex regs) (centerStride regs),
            .sub (centerRemaining regs)
              (centerRemaining regs) (digitRegisters regs).one]
          decreased
      have hstoredCenterNonzero :
          store (centerValue regs) ≠ 0 := by
        rw [hcenter]
        exact hcenterZero
      have hbranch :
          Runs (applyLeftMovement regs) store final := by
        apply Runs.ifNonzero hstoredCenterNonzero
        apply Runs.seq
          (Runs.basic
            (.sub (centerValue regs) (centerValue regs)
              (digitRegisters regs).one) store)
        simpa [advanceCenter] using
          basics_runs
            [.add (centerNextIndex regs)
                (centerNextIndex regs) (centerStride regs),
              .sub (centerRemaining regs)
                (centerRemaining regs)
                (digitRegisters regs).one] decreased
      have hrun :
          Runs (applySelectedMovement regs) store final :=
        Runs.ifZero hvalueZero hbranch
      refine ⟨final, hrun, ?_⟩
      simp [ChildNode.applyMovementDigit, hdigitZero,
        hcenterZero, ChildNode.centerValidValue,
        ChildNode.centerOutputValue,
        ChildNode.centerRemainingValue,
        ChildNode.centerNextIndexValue, final, decreased,
        Basic.execList, Basic.exec, hcenter, hvalid,
        hremaining, hindex, hstride, centerMap,
        digitRegisters, digitMap, regs.injective.eq_iff]
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact congrArg (fun value => center - value) hone
      · exact congrArg (fun value => remaining - value) hone
      · exact hone
      · exact hdivisor
  · have hvalueNonzero :
        store (digitRegisters regs).value ≠ 0 := by
      rw [hdigit]
      exact hdigitZero
    let tested :=
      (Basic.sub (digitRegisters regs).test
        (digitRegisters regs).value
        (digitRegisters regs).one).exec store
    have htested :
        tested (digitRegisters regs).test = digit - 1 := by
      simp [tested, Basic.exec, hdigit, hone]
    by_cases hdigitOne : digit = 1
    · have htestedZero :
          tested (digitRegisters regs).test = 0 := by
        rw [htested, hdigitOne]
      let final :=
        Basic.execList
          [.add (centerNextIndex regs)
              (centerNextIndex regs) (centerStride regs),
            .sub (centerRemaining regs)
              (centerRemaining regs) (digitRegisters regs).one]
          tested
      have hadvance :
          Runs (advanceCenter regs) tested final := by
        simpa [advanceCenter] using
          basics_runs
            [.add (centerNextIndex regs)
                (centerNextIndex regs) (centerStride regs),
              .sub (centerRemaining regs)
                (centerRemaining regs)
                (digitRegisters regs).one] tested
      have hbranch :
          Runs (applyNonleftMovement regs) store final := by
        exact Runs.seq
          (Runs.basic
            (.sub (digitRegisters regs).test
              (digitRegisters regs).value
              (digitRegisters regs).one) store)
          (Runs.ifZero htestedZero hadvance)
      have hrun :
          Runs (applySelectedMovement regs) store final :=
        Runs.ifNonzero hvalueNonzero hbranch
      refine ⟨final, hrun, ?_⟩
      simp [ChildNode.applyMovementDigit, hdigitOne,
        ChildNode.centerValidValue,
        ChildNode.centerOutputValue,
        ChildNode.centerRemainingValue,
        ChildNode.centerNextIndexValue, final, tested,
        Basic.execList, Basic.exec, hcenter, hvalid,
        hremaining, hindex, hstride, centerMap,
        digitRegisters, digitMap, regs.injective.eq_iff]
      exact
        ⟨congrArg (fun value => remaining - value) hone,
          hone, hdivisor⟩
    · have htestedNonzero :
          tested (digitRegisters regs).test ≠ 0 := by
        rw [htested]
        omega
      let increased :=
        (Basic.add (centerValue regs) (centerValue regs)
          (digitRegisters regs).one).exec tested
      let final :=
        Basic.execList
          [.add (centerNextIndex regs)
              (centerNextIndex regs) (centerStride regs),
            .sub (centerRemaining regs)
              (centerRemaining regs) (digitRegisters regs).one]
          increased
      have hadvance :
          Runs (advanceCenter regs) increased final := by
        simpa [advanceCenter] using
          basics_runs
            [.add (centerNextIndex regs)
                (centerNextIndex regs) (centerStride regs),
              .sub (centerRemaining regs)
                (centerRemaining regs)
                (digitRegisters regs).one] increased
      have hright :
          Runs
            (Cmd.seq
              (.basic
                (.add (centerValue regs) (centerValue regs)
                  (digitRegisters regs).one))
              (advanceCenter regs))
            tested final :=
        Runs.seq
          (Runs.basic
            (.add (centerValue regs) (centerValue regs)
              (digitRegisters regs).one) tested)
          hadvance
      have hbranch :
          Runs (applyNonleftMovement regs) store final := by
        exact Runs.seq
          (Runs.basic
            (.sub (digitRegisters regs).test
              (digitRegisters regs).value
              (digitRegisters regs).one) store)
          (Runs.ifNonzero htestedNonzero hright)
      have hrun :
          Runs (applySelectedMovement regs) store final :=
        Runs.ifNonzero hvalueNonzero hbranch
      refine ⟨final, hrun, ?_⟩
      simp [ChildNode.applyMovementDigit, hdigitZero,
        hdigitOne, ChildNode.centerValidValue,
        ChildNode.centerOutputValue,
        ChildNode.centerRemainingValue,
        ChildNode.centerNextIndexValue, final, increased,
        tested, Basic.execList, Basic.exec, hcenter,
        hvalid, hremaining, hindex, hstride, centerMap,
        digitRegisters, digitMap, regs.injective.eq_iff]
      exact
        ⟨hone, congrArg (fun value => remaining - value) hone,
          hone, hdivisor⟩

private theorem initializeCenter_runs
    (workTapeCount : ℕ)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store) (word tape interval : ℕ)
    (hguess : store controller.guess = word)
    (htape : store (ControlDecode.nodeTape regs) = tape)
    (hinterval :
      store (ControlDecode.nodePayload1 regs) = interval) :
    ∃ final,
      Runs (initializeCenter workTapeCount regs) store final ∧
      final (centerValue regs) = 0 ∧
      final (centerValid regs) = 1 ∧
      final (centerRemaining regs) = interval ∧
      final (centerNextIndex regs) = tape ∧
      final (centerStride regs) = workTapeCount + 2 ∧
      final (digitRegisters regs).one = 1 ∧
      final (digitRegisters regs).divisor = 3 ∧
      final controller.guess = word := by
  let remainingStore :=
    Function.update store (centerRemaining regs)
      (store (ControlDecode.nodePayload1 regs))
  let indexed :=
    Function.update remainingStore (centerNextIndex regs)
      (remainingStore (ControlDecode.nodeTape regs))
  let oneStore :=
    (Basic.imm (digitRegisters regs).one 1).exec indexed
  let divisorStore :=
    (Basic.imm (digitRegisters regs).divisor 3).exec oneStore
  let centered :=
    (Basic.imm (centerValue regs) 0).exec divisorStore
  let validated :=
    (Basic.imm (centerValid regs) 1).exec centered
  let final :=
    (Basic.imm (centerStride regs) (workTapeCount + 2)).exec
      validated
  have hremainingRun :
      Runs
        (CombineTerm.copy
          (centerRemaining regs)
          (ControlDecode.nodePayload1 regs))
        store remainingStore := by
    exact copy_update_runs store
      (regs.injective.ne (by decide))
  have hindexedRun :
      Runs
        (CombineTerm.copy
          (centerNextIndex regs) (ControlDecode.nodeTape regs))
        remainingStore indexed := by
    exact copy_update_runs remainingStore
      (regs.injective.ne (by decide))
  have hrun :
      Runs (initializeCenter workTapeCount regs) store final := by
    simpa [initializeCenter, Cmd.seqList] using
      Runs.seq hremainingRun
        (Runs.seq hindexedRun
          (Runs.seq
            (Runs.basic
              (.imm (digitRegisters regs).one 1) indexed)
            (Runs.seq
              (Runs.basic
                (.imm (digitRegisters regs).divisor 3) oneStore)
              (Runs.seq
                (Runs.basic (.imm (centerValue regs) 0)
                  divisorStore)
                (Runs.seq
                  (Runs.basic (.imm (centerValid regs) 1)
                    centered)
                  (Runs.basic
                    (.imm (centerStride regs)
                      (workTapeCount + 2))
                    validated))))))
  refine ⟨final, hrun, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [final, validated, centered, divisorStore, oneStore,
      indexed, remainingStore, Basic.exec, centerMap,
      digitRegisters, digitMap, regs.injective.eq_iff]
  · simp [final, validated, centered, divisorStore, oneStore,
      indexed, remainingStore, Basic.exec, centerMap,
      digitRegisters, digitMap, regs.injective.eq_iff]
  · simp [final, validated, centered, divisorStore, oneStore,
      indexed, remainingStore, Basic.exec, centerMap,
      digitRegisters, digitMap, regs.injective.eq_iff,
      ControlDecode.nodePayload1, ControlDecode.third,
      hinterval]
  · simp [final, validated, centered, divisorStore, oneStore,
      indexed, remainingStore, Basic.exec, centerMap,
      digitRegisters, digitMap, regs.injective.eq_iff,
      ControlDecode.nodeTape, ControlDecode.first, htape]
  · simp [final, Basic.exec]
  · simp [final, validated, centered, divisorStore, oneStore,
      indexed, remainingStore, Basic.exec, centerMap,
      digitRegisters, digitMap, regs.injective.eq_iff]
  · simp [final, validated, centered, divisorStore, oneStore,
      indexed, remainingStore, Basic.exec, centerMap,
      digitRegisters, digitMap, regs.injective.eq_iff]
  · calc
      final controller.guess = store controller.guess :=
        Footprint.runs_eq_outside
          (initializeCenter_writesWithin workTapeCount regs)
          hrun (controller_guess_not_mem controller regs)
      _ = word := hguess

private theorem centerLoop_runs
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store)
    (word remaining index center stride : ℕ)
    (hguess : store controller.guess = word)
    (hremaining : store (centerRemaining regs) = remaining)
    (hindex : store (centerNextIndex regs) = index)
    (hcenter : store (centerValue regs) = center)
    (hvalid : store (centerValid regs) = 1)
    (hone : store (digitRegisters regs).one = 1)
    (hdivisor : store (digitRegisters regs).divisor = 3)
    (hstride : store (centerStride regs) = stride) :
    ∃ final,
      Runs
        (.whileNonzero (centerRemaining regs)
          (centerStep controller regs))
        store final ∧
      let result :=
        ChildNode.scanCenter word stride remaining index center
      final (centerValid regs) =
          ChildNode.centerValidValue result ∧
        final (centerValue regs) =
          ChildNode.centerOutputValue result ∧
        final (centerRemaining regs) = 0 ∧
        final (digitRegisters regs).one = 1 ∧
        final (digitRegisters regs).divisor = 3 ∧
        final (centerStride regs) = stride ∧
        final controller.guess = word := by
  induction remaining generalizing store index center with
  | zero =>
      refine ⟨store, Runs.whileZero hremaining, ?_⟩
      simp [ChildNode.scanCenter, hvalid, hcenter, hremaining,
        hstride, hguess, hone, hdivisor,
        ChildNode.centerValidValue,
        ChildNode.centerOutputValue]
  | succ remaining ih =>
      have hremainingNonzero :
          store (centerRemaining regs) ≠ 0 := by
        rw [hremaining]
        omega
      let cursorStore :=
        Function.update store (digitRegisters regs).cursor index
      have hcursorRun :
          Runs
            (CombineTerm.copy
              (digitRegisters regs).cursor
              (centerNextIndex regs))
            store cursorStore := by
        simpa [cursorStore, hindex] using
          copy_update_runs store
            (regs.injective.ne
              (by decide :
                digitMap 5 ≠ centerMap 4))
      let valueStore :=
        Function.update cursorStore
          (digitRegisters regs).value word
      have hvalueRun :
          Runs
            (CombineTerm.copy
              (digitRegisters regs).value controller.guess)
            cursorStore valueStore := by
        have hcursorGuess :
            cursorStore controller.guess = word := by
          rw [show cursorStore controller.guess =
              store controller.guess by
            simpa only [cursorStore] using
              (Function.update_of_ne
                (regs.index_ne_controller (digitMap 5) 2).symm
                index store)]
          exact hguess
        simpa [valueStore, hcursorGuess] using
          copy_update_runs cursorStore
            (regs.index_ne_controller (digitMap 0) 2)
      have hvalue :
          valueStore (digitRegisters regs).value = word := by
        simp [valueStore]
      have hcursor :
          valueStore (digitRegisters regs).cursor = index := by
        simp [valueStore, cursorStore, digitRegisters, digitMap,
          regs.injective.eq_iff]
      have hvalueDivisor :
          valueStore (digitRegisters regs).divisor = 3 := by
        rw [show valueStore (digitRegisters regs).divisor =
            cursorStore (digitRegisters regs).divisor by
          simpa only [valueStore] using
            (Function.update_of_ne
              (regs.injective.ne
                (by decide : digitMap 4 ≠ digitMap 0))
              word cursorStore)]
        rw [show cursorStore (digitRegisters regs).divisor =
            store (digitRegisters regs).divisor by
          simpa only [cursorStore] using
            (Function.update_of_ne
              (regs.injective.ne
                (by decide : digitMap 4 ≠ digitMap 5))
              index store)]
        exact hdivisor
      obtain ⟨looked, hlookupRun, hlookupPost⟩ :=
        CombineTerm.seekDigit_runs (digitRegisters regs)
          valueStore 3 word index (by omega) hvalue hcursor
          hvalueDivisor
      let selected := ChildNode.movementDigitValue word index
      have hlookedDigit :
          looked (digitRegisters regs).value = selected := by
        rw [hlookupPost.value_eq,
          radixDigit_eq_movementDigitValue]
      have hlookedCenter :
          looked (centerValue regs) = center := by
        rw [hlookupPost.eq_outside _
          (center_not_mem_digitWriteFootprint regs 1)]
        rw [show valueStore (centerValue regs) =
            cursorStore (centerValue regs) by
          simpa only [valueStore] using
            (Function.update_of_ne
              (digit_index_ne_center regs 0 1).symm
              word cursorStore)]
        rw [show cursorStore (centerValue regs) =
            store (centerValue regs) by
          simpa only [cursorStore] using
            (Function.update_of_ne
              (digit_index_ne_center regs 5 1).symm
              index store)]
        exact hcenter
      have hlookedValid :
          looked (centerValid regs) = 1 := by
        rw [hlookupPost.eq_outside _
          (center_not_mem_digitWriteFootprint regs 2)]
        rw [show valueStore (centerValid regs) =
            cursorStore (centerValid regs) by
          simpa only [valueStore] using
            (Function.update_of_ne
              (digit_index_ne_center regs 0 2).symm
              word cursorStore)]
        rw [show cursorStore (centerValid regs) =
            store (centerValid regs) by
          simpa only [cursorStore] using
            (Function.update_of_ne
              (digit_index_ne_center regs 5 2).symm
              index store)]
        exact hvalid
      have hlookedRemaining :
          looked (centerRemaining regs) = remaining + 1 := by
        rw [hlookupPost.eq_outside _
          (center_not_mem_digitWriteFootprint regs 3)]
        rw [show valueStore (centerRemaining regs) =
            cursorStore (centerRemaining regs) by
          simpa only [valueStore] using
            (Function.update_of_ne
              (digit_index_ne_center regs 0 3).symm
              word cursorStore)]
        rw [show cursorStore (centerRemaining regs) =
            store (centerRemaining regs) by
          simpa only [cursorStore] using
            (Function.update_of_ne
              (digit_index_ne_center regs 5 3).symm
              index store)]
        exact hremaining
      have hlookedIndex :
          looked (centerNextIndex regs) = index := by
        rw [hlookupPost.eq_outside _
          (center_not_mem_digitWriteFootprint regs 4)]
        rw [show valueStore (centerNextIndex regs) =
            cursorStore (centerNextIndex regs) by
          simpa only [valueStore] using
            (Function.update_of_ne
              (digit_index_ne_center regs 0 4).symm
              word cursorStore)]
        rw [show cursorStore (centerNextIndex regs) =
            store (centerNextIndex regs) by
          simpa only [cursorStore] using
            (Function.update_of_ne
              (digit_index_ne_center regs 5 4).symm
              index store)]
        exact hindex
      have hlookedStride :
          looked (centerStride regs) = stride := by
        rw [hlookupPost.eq_outside _
          (center_not_mem_digitWriteFootprint regs 0)]
        rw [show valueStore (centerStride regs) =
            cursorStore (centerStride regs) by
          simpa only [valueStore] using
            (Function.update_of_ne
              (digit_index_ne_center regs 0 0).symm
              word cursorStore)]
        rw [show cursorStore (centerStride regs) =
            store (centerStride regs) by
          simpa only [cursorStore] using
            (Function.update_of_ne
              (digit_index_ne_center regs 5 0).symm
              index store)]
        exact hstride
      obtain ⟨applied, happlyRun, happlyPost⟩ :=
        applySelectedMovement_runs regs looked selected center
          (remaining + 1) index stride hlookedDigit
          hlookupPost.one_eq hlookupPost.divisor_eq
          hlookedCenter hlookedValid hlookedRemaining
          hlookedIndex hlookedStride
      dsimp only at happlyPost
      rcases happlyPost with
        ⟨happliedValid, happpliedCenter, happpliedRemaining,
          happpliedIndex, happpliedOne, happpliedDivisor,
          happpliedStride⟩
      have hbody :
          Runs (centerStep controller regs) store applied := by
        simpa [centerStep, Cmd.seqList] using
          Runs.seq hcursorRun
            (Runs.seq hvalueRun
              (Runs.seq hlookupRun happlyRun))
      have hlookedGuess :
          looked controller.guess = word := by
        rw [hlookupPost.eq_outside _
          (guess_not_mem_digitWriteFootprint controller regs)]
        rw [show valueStore controller.guess =
            cursorStore controller.guess by
          simpa only [valueStore] using
            (Function.update_of_ne
              (regs.index_ne_controller (digitMap 0) 2).symm
              word cursorStore)]
        rw [show cursorStore controller.guess =
            store controller.guess by
          simpa only [cursorStore] using
            (Function.update_of_ne
              (regs.index_ne_controller (digitMap 5) 2).symm
              index store)]
        exact hguess
      have happliedGuess :
          applied controller.guess = word := by
        calc
          applied controller.guess = looked controller.guess :=
            Footprint.runs_eq_outside
              (applySelectedMovement_writesWithin regs)
              happlyRun
              (controller_guess_not_mem controller regs)
          _ = word := hlookedGuess
      generalize hmovement :
        ChildNode.applyMovementDigit selected center =
          movementResult
      cases movementResult with
      | none =>
          have happliedRemainingZero :
              applied (centerRemaining regs) = 0 := by
            rw [happpliedRemaining, hmovement]
            rfl
          have hloop :=
            Runs.whileZero
              (body := centerStep controller regs)
              happliedRemainingZero
          refine ⟨applied,
            Runs.whileNonzero hremainingNonzero hbody hloop,
            ?_, ?_, happliedRemainingZero, happpliedOne,
            happpliedDivisor, happpliedStride, happliedGuess⟩
          · simpa [ChildNode.scanCenter, selected, hmovement] using
              happliedValid
          · simpa [ChildNode.scanCenter, selected, hmovement] using
              happpliedCenter
      | some next =>
          have happliedValidOne :
              applied (centerValid regs) = 1 := by
            rw [happliedValid, hmovement]
            rfl
          have happliedCenterNext :
              applied (centerValue regs) = next := by
            rw [happpliedCenter, hmovement]
            rfl
          have happliedRemaining :
              applied (centerRemaining regs) = remaining := by
            rw [happpliedRemaining, hmovement]
            simp [ChildNode.centerRemainingValue]
          have happliedIndex :
              applied (centerNextIndex regs) =
                index + stride := by
            rw [happpliedIndex, hmovement]
            rfl
          obtain ⟨final, hloopRun, hfinalValid, hfinalCenter,
              hfinalRemaining, hfinalOne, hfinalDivisor,
              hfinalStride, hfinalGuess⟩ :=
            ih applied (index + stride) next happliedGuess
              happliedRemaining happliedIndex happliedCenterNext
              happliedValidOne happpliedOne happpliedDivisor
              happpliedStride
          refine ⟨final,
            Runs.whileNonzero hremainingNonzero hbody hloopRun,
            ?_, ?_, hfinalRemaining, hfinalOne, hfinalDivisor,
            hfinalStride, hfinalGuess⟩
          · simpa [ChildNode.scanCenter, selected, hmovement] using
              hfinalValid
          · simpa [ChildNode.scanCenter, selected, hmovement] using
              hfinalCenter

theorem deriveCenter_runs_internal
    (workTapeCount : ℕ)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store) (word tape interval : ℕ)
    (hguess : store controller.guess = word)
    (htape : store (ControlDecode.nodeTape regs) = tape)
    (hinterval :
      store (ControlDecode.nodePayload1 regs) = interval) :
    ∃ final,
      Runs (deriveCenter workTapeCount controller regs) store final ∧
      Post workTapeCount word tape interval
        controller regs store final := by
  obtain ⟨initialized, hinitializeRun, hinitializedCenter,
      hinitializedValid, hinitializedRemaining, hinitializedIndex,
      hinitializedStride, hinitializedOne, hinitializedDivisor,
      hinitializedGuess⟩ :=
    initializeCenter_runs workTapeCount controller regs store
      word tape interval hguess htape hinterval
  obtain ⟨final, hloopRun, hfinalValid, hfinalCenter,
      hfinalRemaining, hfinalOne, hfinalDivisor, hfinalStride,
      hfinalGuess⟩ :=
    centerLoop_runs controller regs initialized word interval tape 0
      (workTapeCount + 2) hinitializedGuess
      hinitializedRemaining hinitializedIndex hinitializedCenter
      hinitializedValid hinitializedOne hinitializedDivisor
      hinitializedStride
  have hrun :
      Runs (deriveCenter workTapeCount controller regs) store final :=
    Runs.seq hinitializeRun hloopRun
  refine ⟨final, hrun, ?_⟩
  refine
    { valid_eq := ?_
      center_eq := ?_
      remaining_eq := hfinalRemaining
      guess_eq := hfinalGuess
      eq_outside := ?_ }
  · simpa [ChildNode.derivedCenterValue] using hfinalValid
  · simpa [ChildNode.derivedCenterValue] using hfinalCenter
  · intro address haddress
    exact Footprint.runs_eq_outside
      (deriveCenter_writesWithin_internal
        workTapeCount controller regs)
      hrun haddress

end Internal
end CombineSafeCenter
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
