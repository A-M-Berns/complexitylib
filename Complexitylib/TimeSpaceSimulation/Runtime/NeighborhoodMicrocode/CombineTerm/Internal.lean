/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.Models.RandomAccessMachine.Structured.Footprint
import
  Complexitylib.Models.RandomAccessMachine.Structured.RuntimeArithmetic
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.CombineTerm.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.CombineValue
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.ControlDecode
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.FrameBounds
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.Representation
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodProgram
import
  Complexitylib.TreeEvaluation.CookMertz.PrimeField.Runtime

/-!
# Fixed-register assignment digits and combine-term composition -- proofs
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace CombineTerm
namespace Internal

open RAM Structured
open TreeEval CookMertz

variable {controller : SearchProgram.Registers}

theorem computationContext_transport_internal
    {tm : TM workTapeCount}
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (tape : TapeIndex workTapeCount)
    (slot : NeighborhoodGraph.Slot)
    (interval : ℕ)
    (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    {initial final : Store}
    (hcontext :
      ComputationContext regs instanceData tape slot interval
        logicalBank initial)
    (habi : ControlDecode.PreservesABI regs initial final)
    (hbank :
      final regs.layout.bank = initial regs.layout.bank) :
    ComputationContext regs instanceData tape slot interval
      logicalBank final := by
  exact
    { parameters :=
        { blockLength_eq :=
            habi.blockLength_eq.trans
              hcontext.parameters.blockLength_eq
          horizon_eq :=
            habi.horizon_eq.trans hcontext.parameters.horizon_eq
          digitBase_eq :=
            habi.chunkRadix_eq.trans
              hcontext.parameters.digitBase_eq
          bankBase_eq :=
            habi.bankRadix_eq.trans
              hcontext.parameters.bankBase_eq
          frameBase_eq :=
            habi.frameRadix_eq.trans
              hcontext.parameters.frameBase_eq
          chunkCount_eq :=
            habi.chunkCount_eq.trans
              hcontext.parameters.chunkCount_eq
          bankDigitCount_eq :=
            habi.bankDigitCount_eq.trans
              hcontext.parameters.bankDigitCount_eq
          modulus_eq :=
            habi.modulus_eq.trans hcontext.parameters.modulus_eq
          modulusPred_eq :=
            habi.modulusPred_eq.trans
              hcontext.parameters.modulusPred_eq }
      nodeCode_eq :=
        habi.nodeCode_eq.trans hcontext.nodeCode_eq
      bank := by
        rw [hbank]
        exact hcontext.bank }

theorem computationFrameContext_transport_internal
    {tm : TM workTapeCount}
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (tape : TapeIndex workTapeCount)
    (slot : NeighborhoodGraph.Slot)
    (interval : ℕ)
    (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    {initial final : Store}
    (hcontext :
      ComputationFrameContext regs instanceData frame tape slot interval
        logicalBank initial)
    (habi : ControlDecode.PreservesABI regs initial final)
    (hbank :
      final regs.layout.bank = initial regs.layout.bank) :
    ComputationFrameContext regs instanceData frame tape slot interval
      logicalBank final := by
  exact
    { computation :=
        computationContext_transport_internal
          regs instanceData tape slot interval logicalBank
          hcontext.computation habi hbank
      out_eq := habi.out_eq.trans hcontext.out_eq }

theorem computationContext_of_queryState_internal
    {tm : TM workTapeCount}
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (rest : List (NeighborhoodScheduler.Frame tm instanceData))
    (state : NeighborhoodScheduler.State tm instanceData)
    (store : Store)
    (tape : TapeIndex workTapeCount)
    (slot : NeighborhoodGraph.Slot)
    (interval : ℕ)
    (hstack : state.stack = frame :: rest)
    (hnode :
      frame.node =
        (show
          NeighborhoodEvaluator.QueryNode
            workTapeCount instanceData.horizon
          from .graph (.computation tape slot interval)))
    (hrep : Representation.QueryState regs instanceData state store) :
    ComputationContext regs instanceData tape slot interval
      state.registers store := by
  have hhead :=
    Representation.QueryState.head regs frame rest state store
      hstack hrep
  exact
    { parameters := hrep.parameters
      nodeCode_eq := by
        simpa [hnode] using hhead.1.node_eq
      bank := hrep.bank }

theorem computationContext_stableUnderDriverWrites_internal
    {tm : TM workTapeCount}
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (tape : TapeIndex workTapeCount)
    (slot : NeighborhoodGraph.Slot)
    (interval : ℕ)
    (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength) :
    CombineValue.StableUnderDriverWrites
      (CombineValue.rangeRegisters regs)
      (ComputationContext regs instanceData tape slot interval
        logicalBank) := by
  intro initial final hcontext houtside
  have hpreserved :
      ∀ target : Fin 34,
        target ≠ (18 : Fin 34) →
        target ≠ (5 : Fin 34) →
        target ≠ (21 : Fin 34) →
        target ≠ (17 : Fin 34) →
        final (regs.index target) = initial (regs.index target) := by
    intro target haccumulator htest hremaining hone
    apply houtside
    change
      regs.index target ∉
        {regs.index 18, regs.index 5, regs.index 21,
          regs.index 17}
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact
      ⟨fun heq => haccumulator (regs.injective heq),
        fun heq => htest (regs.injective heq),
        fun heq => hremaining (regs.injective heq),
        fun heq => hone (regs.injective heq)⟩
  exact
    { parameters :=
        { blockLength_eq :=
            (hpreserved (2 : Fin 34) (by decide) (by decide)
              (by decide) (by decide)).trans
              hcontext.parameters.blockLength_eq
          horizon_eq :=
            (hpreserved (3 : Fin 34) (by decide) (by decide)
              (by decide) (by decide)).trans
              hcontext.parameters.horizon_eq
          digitBase_eq :=
            (hpreserved (8 : Fin 34) (by decide) (by decide)
              (by decide) (by decide)).trans
              hcontext.parameters.digitBase_eq
          bankBase_eq :=
            (hpreserved (14 : Fin 34) (by decide) (by decide)
              (by decide) (by decide)).trans
              hcontext.parameters.bankBase_eq
          frameBase_eq :=
            (hpreserved (13 : Fin 34) (by decide) (by decide)
              (by decide) (by decide)).trans
              hcontext.parameters.frameBase_eq
          chunkCount_eq :=
            (hpreserved (7 : Fin 34) (by decide) (by decide)
              (by decide) (by decide)).trans
              hcontext.parameters.chunkCount_eq
          bankDigitCount_eq :=
            (hpreserved (15 : Fin 34) (by decide) (by decide)
              (by decide) (by decide)).trans
              hcontext.parameters.bankDigitCount_eq
          modulus_eq :=
            (hpreserved (24 : Fin 34) (by decide) (by decide)
              (by decide) (by decide)).trans
              hcontext.parameters.modulus_eq
          modulusPred_eq :=
            (hpreserved (16 : Fin 34) (by decide) (by decide)
              (by decide) (by decide)).trans
              hcontext.parameters.modulusPred_eq }
      nodeCode_eq :=
        (hpreserved (23 : Fin 34) (by decide) (by decide)
          (by decide) (by decide)).trans hcontext.nodeCode_eq
      bank := by
        change
          NeighborhoodProgram.RepresentsResidueBank
            tm instanceData.blockLength
            (Representation.fieldBase instanceData)
            (final (regs.index 33)) logicalBank
        rw [hpreserved (33 : Fin 34) (by decide) (by decide)
          (by decide) (by decide)]
        simpa [NeighborhoodTrial.Registers.layout] using hcontext.bank }

theorem computationFrameContext_stableUnderDriverWrites_internal
    {tm : TM workTapeCount}
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (tape : TapeIndex workTapeCount)
    (slot : NeighborhoodGraph.Slot)
    (interval : ℕ)
    (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength) :
    CombineValue.StableUnderDriverWrites
      (CombineValue.rangeRegisters regs)
      (ComputationFrameContext regs instanceData frame tape slot interval
        logicalBank) := by
  intro initial final hcontext houtside
  exact
    { computation :=
        computationContext_stableUnderDriverWrites_internal
          regs instanceData tape slot interval logicalBank
          hcontext.computation houtside
      out_eq :=
        (houtside (Layout.out regs) (by
          simp [CombineValue.RangeRegisters.driverWriteFootprint,
            CombineValue.rangeRegisters, Layout.out,
            regs.injective.eq_iff])).trans hcontext.out_eq }

theorem decodeComputationNode_runs_internal
    {tm : TM workTapeCount}
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (tape : TapeIndex workTapeCount)
    (slot : NeighborhoodGraph.Slot)
    (interval : ℕ)
    (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (store : Store)
    (hfits :
      ∀ digit ∈
          FrameCodec.nodeDigits
            (show
              NeighborhoodEvaluator.QueryNode
                workTapeCount instanceData.horizon
              from .graph (.computation tape slot interval)),
        digit < Representation.digitBase instanceData)
    (hcontext :
      ComputationContext regs instanceData tape slot interval
        logicalBank store) :
    ∃ final,
      Runs (ControlDecode.decodeNode regs) store final ∧
      DecodedComputationPost regs instanceData tape slot interval
        logicalBank final := by
  have hbase : 0 < Representation.digitBase instanceData := by
    unfold Representation.digitBase CandidateParameters.domainSize
    exact PrimeGrouped.Logarithmic.domainSize_pos _ _
  obtain ⟨final, hrun, _, hdecoded, habi⟩ :=
    ControlDecode.decodeNode_encodeNode_runs
      regs store (Representation.digitBase instanceData)
      (show
        NeighborhoodEvaluator.QueryNode
          workTapeCount instanceData.horizon
        from .graph (.computation tape slot interval))
      hbase hfits hcontext.nodeCode_eq
      hcontext.parameters.digitBase_eq
  have hbankOutside :
      regs.layout.bank ∉ ControlDecode.scratchFootprint regs := by
    simp only [ControlDecode.scratchFootprint, Finset.mem_image,
      Finset.mem_univ, true_and, not_exists]
    intro index heq
    have hindex := regs.injective heq
    change ControlDecode.scratchMap index = (33 : Fin 34) at hindex
    exact
      (show ∀ index : Fin 7,
          ControlDecode.scratchMap index ≠ (33 : Fin 34) by
        decide)
        index hindex
  have hbank :
      final regs.layout.bank = store regs.layout.bank :=
    RAM.Structured.Footprint.runs_eq_outside
      (ControlDecode.decodeNode_writesWithin regs) hrun hbankOutside
  refine ⟨final, hrun, ?_⟩
  exact
    { context :=
        computationContext_transport_internal
          regs instanceData tape slot interval logicalBank
          hcontext habi hbank
      decoded := hdecoded }

theorem radixQuotient_eq_div_pow_internal
    (radix word index : ℕ) :
    radixQuotient radix index word =
      word / radix ^ index := by
  induction index generalizing word with
  | zero =>
      simp [radixQuotient]
  | succ index ih =>
      simp only [radixQuotient]
      rw [ih, Nat.div_div_eq_div_mul]
      simp [pow_succ, Nat.mul_comm]

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

private theorem seekLoop_runs
    (regs : DigitRegisters) (store : Store)
    (radix word index : ℕ)
    (hradix : 0 < radix)
    (hvalue : store regs.value = word)
    (hcursor : store regs.cursor = index)
    (hdivisor : store regs.divisor = radix) :
    ∃ final,
      Runs
          (.whileNonzero regs.cursor (seekBody regs))
          store final ∧
        final regs.value = radixQuotient radix index word ∧
        final regs.cursor = 0 ∧
        final regs.divisor = radix := by
  induction index generalizing store word with
  | zero =>
      refine ⟨store, ?_, ?_, hcursor, hdivisor⟩
      · exact Runs.whileZero hcursor
      · simpa [radixQuotient] using hvalue
  | succ index ih =>
      have hnonzero : store regs.cursor ≠ 0 := by
        rw [hcursor]
        omega
      obtain ⟨afterDivision, hdivision, hdivisionPost⟩ :=
        ControlDecode.divRem_runs regs.division store radix word
          hradix hvalue hdivisor
      have hdivisionCursor :
          afterDivision regs.cursor = index + 1 := by
        rw [hdivisionPost.eq_outside regs.cursor]
        · exact hcursor
        · simp [ControlDecode.DivisionRegisters.writeFootprint,
            DigitRegisters.division, regs.injective.eq_iff]
      obtain
        ⟨afterCopy, hcopy, hcopyValue, hcopyOutside⟩ :=
        copy_runs regs.value regs.quotient afterDivision
          (regs.injective.ne (by decide))
      have hcopyCursor :
          afterCopy regs.cursor = index + 1 := by
        rw [hcopyOutside regs.cursor
          (regs.injective.ne (by decide))]
        exact hdivisionCursor
      have hcopyOne : afterCopy regs.one = 1 := by
        rw [hcopyOutside regs.one
          (regs.injective.ne (by decide))]
        exact hdivisionPost.one_eq
      have hcopyDivisor :
          afterCopy regs.divisor = radix := by
        rw [hcopyOutside regs.divisor
          (regs.injective.ne (by decide))]
        exact hdivisionPost.divisor_eq
      let afterDecrement :=
        (Basic.sub regs.cursor regs.cursor regs.one).exec afterCopy
      have hdecrementRun :
          Runs (.basic
            (.sub regs.cursor regs.cursor regs.one))
            afterCopy afterDecrement :=
        Runs.basic _ _
      have hdecrementValue :
          afterDecrement regs.value = word / radix := by
        have hpreserved :
            afterDecrement regs.value = afterCopy regs.value := by
          simp [afterDecrement, Basic.exec,
            regs.injective.eq_iff]
        exact hpreserved.trans
          (hcopyValue.trans hdivisionPost.quotient_eq)
      have hdecrementCursor :
          afterDecrement regs.cursor = index := by
        simp [afterDecrement, Basic.exec, hcopyCursor, hcopyOne]
      have hdecrementDivisor :
          afterDecrement regs.divisor = radix := by
        simp [afterDecrement, Basic.exec, regs.injective.eq_iff,
          hcopyDivisor]
      obtain ⟨final, hrest, hfinalValue, hfinalCursor,
          hfinalDivisor⟩ :=
        ih afterDecrement (word / radix) hdecrementValue
          hdecrementCursor hdecrementDivisor
      have hbody :
          Runs (seekBody regs) store afterDecrement := by
        simpa [seekBody, Cmd.seqList] using
          Runs.seq hdivision (Runs.seq hcopy hdecrementRun)
      refine ⟨final,
        Runs.whileNonzero hnonzero hbody hrest, ?_,
        hfinalCursor, hfinalDivisor⟩
      simpa [radixQuotient] using hfinalValue

private theorem cmdWritesWithin_mono
    {smaller larger : Finset ℕ}
    (hsubset : smaller ⊆ larger) :
    ∀ command,
      RAM.Structured.Footprint.CmdWritesWithin smaller command →
      RAM.Structured.Footprint.CmdWritesWithin larger command := by
  intro command hwrites
  induction command with
  | skip => trivial
  | basic op =>
      cases op <;>
        simp_all [RAM.Structured.Footprint.CmdWritesWithin,
          RAM.Structured.Footprint.BasicWritesWithin] <;>
        exact hsubset hwrites
  | seq first second firstIH secondIH =>
      exact ⟨firstIH hwrites.1, secondIH hwrites.2⟩
  | ifZero test onZero onNonzero zeroIH nonzeroIH =>
      exact ⟨zeroIH hwrites.1, nonzeroIH hwrites.2⟩
  | whileNonzero test body bodyIH =>
      exact bodyIH hwrites

private theorem division_writeFootprint_subset
    (regs : DigitRegisters) :
    regs.division.writeFootprint ⊆ regs.writeFootprint := by
  intro address haddress
  simp only [ControlDecode.DivisionRegisters.writeFootprint,
    Finset.mem_insert, Finset.mem_singleton] at haddress
  rcases haddress with haddress | haddress | haddress | haddress
  · change address = regs.value at haddress
    subst address
    simp [DigitRegisters.writeFootprint]
  · change address = regs.quotient at haddress
    subst address
    simp [DigitRegisters.writeFootprint]
  · change address = regs.test at haddress
    subst address
    simp [DigitRegisters.writeFootprint]
  · change address = regs.one at haddress
    subst address
    simp [DigitRegisters.writeFootprint]

theorem seekDigit_writesWithin_internal
    (regs : DigitRegisters) :
    RAM.Structured.Footprint.CmdWritesWithin
      regs.writeFootprint (seekDigit regs) := by
  have hdivision :=
    cmdWritesWithin_mono (division_writeFootprint_subset regs) _
      (ControlDecode.divRem_writesWithin regs.division)
  have hvalue : regs.value ∈ regs.writeFootprint := by
    simp [DigitRegisters.writeFootprint]
  have hcursor : regs.cursor ∈ regs.writeFootprint := by
    simp [DigitRegisters.writeFootprint]
  have hcopy :
      RAM.Structured.Footprint.CmdWritesWithin
        regs.writeFootprint (copy regs.value regs.quotient) := by
    simpa [copy, RAM.Structured.Footprint.CmdWritesWithin,
      RAM.Structured.Footprint.BasicWritesWithin] using
      And.intro hvalue hvalue
  have hdecrement :
      RAM.Structured.Footprint.CmdWritesWithin
        regs.writeFootprint
        (.basic (.sub regs.cursor regs.cursor regs.one)) := by
    simpa [RAM.Structured.Footprint.CmdWritesWithin,
      RAM.Structured.Footprint.BasicWritesWithin] using hcursor
  simp only [seekDigit, seekBody, Cmd.seqList,
    RAM.Structured.Footprint.CmdWritesWithin]
  exact ⟨⟨hdivision, hcopy, hdecrement⟩, hdivision⟩

theorem seekDigit_runs_internal
    (regs : DigitRegisters) (store : Store)
    (radix word index : ℕ)
    (hradix : 0 < radix)
    (hvalue : store regs.value = word)
    (hcursor : store regs.cursor = index)
    (hdivisor : store regs.divisor = radix) :
    ∃ final,
      Runs (seekDigit regs) store final ∧
      DigitPost regs radix word index store final := by
  obtain ⟨afterSeek, hseek, hseekValue, hseekCursor,
      hseekDivisor⟩ :=
    seekLoop_runs regs store radix word index hradix
      hvalue hcursor hdivisor
  obtain ⟨final, hdivision, hdivisionPost⟩ :=
    ControlDecode.divRem_runs regs.division afterSeek radix
      (radixQuotient radix index word) hradix hseekValue
      hseekDivisor
  have hrun : Runs (seekDigit regs) store final := by
    simpa [seekDigit] using Runs.seq hseek hdivision
  refine ⟨final, hrun, ?_⟩
  refine
    { value_eq := ?_
      cursor_eq := ?_
      divisor_eq := hdivisionPost.divisor_eq
      one_eq := hdivisionPost.one_eq
      eq_outside := ?_ }
  · have hdivisionValue :
        final regs.value =
          (radixQuotient radix index word) % radix := by
      exact hdivisionPost.value_eq
    rw [hdivisionValue,
      radixQuotient_eq_div_pow_internal]
    rfl
  · have hcursorOutside :
        regs.cursor ∉ regs.division.writeFootprint := by
      simp [ControlDecode.DivisionRegisters.writeFootprint,
        DigitRegisters.division, regs.injective.eq_iff]
    exact
      (hdivisionPost.eq_outside regs.cursor hcursorOutside).trans
        hseekCursor
  · intro address haddress
    exact RAM.Structured.Footprint.runs_eq_outside
      (seekDigit_writesWithin_internal regs) hrun haddress

private theorem combineScratch_mem
    (regs : NeighborhoodTrial.Registers controller)
    (slot : Fin 19) :
    regs.index (CombineValue.combineScratchMap slot) ∈
      CombineValue.combineScratchFootprint regs := by
  exact Finset.mem_image.mpr ⟨slot, Finset.mem_univ _, rfl⟩

private theorem assignmentDigit_writeFootprint_subset
    (regs : NeighborhoodTrial.Registers controller) :
    (assignmentDigitRegisters regs).writeFootprint ⊆
      CombineValue.combineScratchFootprint regs := by
  intro address haddress
  simp only [DigitRegisters.writeFootprint, Finset.mem_insert,
    Finset.mem_singleton] at haddress
  rcases haddress with haddress | haddress | haddress |
      haddress | haddress
  · subst address
    exact combineScratch_mem regs (11 : Fin 19)
  · subst address
    exact combineScratch_mem regs (12 : Fin 19)
  · subst address
    exact combineScratch_mem regs (2 : Fin 19)
  · subst address
    exact combineScratch_mem regs (9 : Fin 19)
  · subst address
    exact combineScratch_mem regs (14 : Fin 19)

theorem assignmentDigit_precise_writesWithin_internal
    (regs : NeighborhoodTrial.Registers controller) :
    RAM.Structured.Footprint.CmdWritesWithin
      (assignmentDigitRegisters regs).writeFootprint
      (assignmentDigit regs) := by
  let digit := assignmentDigitRegisters regs
  have hvalue : digit.value ∈ digit.writeFootprint := by
    simp [DigitRegisters.writeFootprint]
  have hcursor : digit.cursor ∈ digit.writeFootprint := by
    simp [DigitRegisters.writeFootprint]
  have hcopyValue :
      RAM.Structured.Footprint.CmdWritesWithin
        digit.writeFootprint
        (copy digit.value
          (CombineValue.rangeRegisters regs).remaining) := by
    simpa [copy, RAM.Structured.Footprint.CmdWritesWithin,
      RAM.Structured.Footprint.BasicWritesWithin] using
      And.intro hvalue hvalue
  have hcopyCursor :
      RAM.Structured.Footprint.CmdWritesWithin
        digit.writeFootprint
        (copy digit.cursor (assignmentDigitIndex regs)) := by
    simpa [copy, RAM.Structured.Footprint.CmdWritesWithin,
      RAM.Structured.Footprint.BasicWritesWithin] using
      And.intro hcursor hcursor
  simpa only [assignmentDigit, Cmd.seqList,
    RAM.Structured.Footprint.CmdWritesWithin] using
    And.intro hcopyValue
      (And.intro hcopyCursor
        (seekDigit_writesWithin_internal digit))

theorem assignmentDigit_writesWithin_internal
    (regs : NeighborhoodTrial.Registers controller) :
    RAM.Structured.Footprint.CmdWritesWithin
      (CombineValue.combineScratchFootprint regs)
      (assignmentDigit regs) := by
  exact cmdWritesWithin_mono
    (assignmentDigit_writeFootprint_subset regs) _
    (assignmentDigit_precise_writesWithin_internal regs)

theorem assignmentDigit_layout_writesWithin_internal
    (regs : NeighborhoodTrial.Registers controller) :
    RAM.Structured.Footprint.CmdWritesWithin
      regs.layout.footprint (assignmentDigit regs) :=
  cmdWritesWithin_mono
    (CombineValue.combineScratchFootprint_subset_layout regs) _
    (assignmentDigit_writesWithin_internal regs)

theorem assignmentDigit_runs_internal
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store) (radix code index : ℕ)
    (hradix : 0 < radix)
    (hcode :
      store (CombineValue.rangeRegisters regs).remaining = code)
    (hindex : store (assignmentDigitIndex regs) = index)
    (hradixValue : store (Layout.chunkRadix regs) = radix)
    (hone :
      store (CombineValue.rangeRegisters regs).one = 1) :
    ∃ final,
      Runs (assignmentDigit regs) store final ∧
      AssignmentDigitPost regs radix code index store final ∧
      ControlDecode.PreservesABI regs store final := by
  let digit := assignmentDigitRegisters regs
  let range := CombineValue.rangeRegisters regs
  obtain ⟨afterCode, hcopyCode, hcopyCodeValue,
      hcopyCodeOutside⟩ :=
    copy_runs digit.value range.remaining store
      (regs.injective.ne (by decide))
  have hafterCodeIndex :
      afterCode (assignmentDigitIndex regs) = index := by
    rw [hcopyCodeOutside (assignmentDigitIndex regs)
      (regs.injective.ne (by decide))]
    exact hindex
  obtain ⟨afterIndex, hcopyIndex, hcopyIndexValue,
      hcopyIndexOutside⟩ :=
    copy_runs digit.cursor (assignmentDigitIndex regs) afterCode
      (regs.injective.ne (by decide))
  have hafterIndexValue : afterIndex digit.value = code := by
    rw [hcopyIndexOutside digit.value
      (regs.injective.ne (by decide))]
    exact hcopyCodeValue.trans hcode
  have hafterIndexCursor :
      afterIndex digit.cursor = index :=
    hcopyIndexValue.trans hafterCodeIndex
  have hafterIndexDivisor :
      afterIndex digit.divisor = radix := by
    rw [hcopyIndexOutside digit.divisor
      (regs.injective.ne (by decide))]
    rw [hcopyCodeOutside digit.divisor
      (regs.injective.ne (by decide))]
    exact hradixValue
  obtain ⟨final, hseek, hseekPost⟩ :=
    seekDigit_runs_internal digit afterIndex radix code index
      hradix hafterIndexValue hafterIndexCursor
      hafterIndexDivisor
  have hrun : Runs (assignmentDigit regs) store final := by
    simpa [assignmentDigit, Cmd.seqList] using
      Runs.seq hcopyCode (Runs.seq hcopyIndex hseek)
  have hwrites :=
    assignmentDigit_precise_writesWithin_internal regs
  have houtside :
      ∀ address,
        address ∉ digit.writeFootprint →
        final address = store address := by
    intro address haddress
    exact RAM.Structured.Footprint.runs_eq_outside
      hwrites hrun haddress
  have haccumulatorOutside :
      range.accumulator ∉ digit.writeFootprint := by
    simp [DigitRegisters.writeFootprint, digit, range,
      assignmentDigitRegisters, CombineValue.rangeRegisters,
      regs.injective.eq_iff]
  have hremainingOutside :
      range.remaining ∉ digit.writeFootprint := by
    simp [DigitRegisters.writeFootprint, digit, range,
      assignmentDigitRegisters, CombineValue.rangeRegisters,
      regs.injective.eq_iff]
  have hmodulusOutside :
      range.modulus ∉ digit.writeFootprint := by
    simp [DigitRegisters.writeFootprint, digit, range,
      assignmentDigitRegisters, CombineValue.rangeRegisters,
      regs.injective.eq_iff]
  have hmodulusPredOutside :
      range.modulusPred ∉ digit.writeFootprint := by
    simp [DigitRegisters.writeFootprint, digit, range,
      assignmentDigitRegisters, CombineValue.rangeRegisters,
      regs.injective.eq_iff]
  have hcountOutside :
      range.count ∉ digit.writeFootprint := by
    simp [DigitRegisters.writeFootprint, digit, range,
      assignmentDigitRegisters, CombineValue.rangeRegisters,
      regs.injective.eq_iff]
  have hindexOutside :
      assignmentDigitIndex regs ∉ digit.writeFootprint := by
    simp [DigitRegisters.writeFootprint, digit,
      assignmentDigitRegisters, assignmentDigitIndex,
      regs.injective.eq_iff]
  refine ⟨final, hrun, ?_, ?_⟩
  · exact
      { term_eq := hseekPost.value_eq
        accumulator_eq :=
          houtside range.accumulator haccumulatorOutside
        remaining_eq :=
          (houtside range.remaining hremainingOutside).trans hcode
        modulus_eq :=
          houtside range.modulus hmodulusOutside
        modulusPred_eq :=
          houtside range.modulusPred hmodulusPredOutside
        one_eq := hseekPost.one_eq.trans hone.symm
        count_eq :=
          houtside range.count hcountOutside
        index_eq :=
          (houtside (assignmentDigitIndex regs) hindexOutside).trans
            hindex }
  · exact CombineValue.preservesABI_of_combineScratch regs
      (assignmentDigit_writesWithin_internal regs) hrun

theorem readResidueCoordinate_writesWithin_internal
    (regs : NeighborhoodTrial.Registers controller) :
    RAM.Structured.Footprint.CmdWritesWithin
      (coordinateReadFootprint regs)
      (readResidueCoordinate regs) := by
  let range := CombineValue.rangeRegisters regs
  let bank := coordinateBankRegisters regs
  have hsaved :
      savedRangeCount regs ∈ coordinateReadFootprint regs := by
    simp [coordinateReadFootprint]
  have hcount :
      range.count ∈ coordinateReadFootprint regs := by
    apply Finset.mem_union_right
    change
      range.count ∈
        {savedRangeCount regs, range.count}
    simp
  have hindex :
      bank.indexCount ∈ coordinateReadFootprint regs := by
    exact Finset.mem_union_left _
      (NeighborhoodProgram.BankRegisters.index_mem_footprint
        bank (8 : Fin 12))
  have hbasePred :
      bank.basePred ∈ coordinateReadFootprint regs := by
    exact Finset.mem_union_left _
      (NeighborhoodProgram.BankRegisters.index_mem_footprint
        bank (3 : Fin 12))
  have hsave :
      RAM.Structured.Footprint.CmdWritesWithin
        (coordinateReadFootprint regs)
        (copy (savedRangeCount regs) range.count) := by
    simpa [copy, RAM.Structured.Footprint.CmdWritesWithin,
      RAM.Structured.Footprint.BasicWritesWithin] using
      And.intro hsaved hsaved
  have hcopyIndex :
      RAM.Structured.Footprint.CmdWritesWithin
        (coordinateReadFootprint regs)
        (copy bank.indexCount (coordinateIndex regs)) := by
    simpa [copy, RAM.Structured.Footprint.CmdWritesWithin,
      RAM.Structured.Footprint.BasicWritesWithin] using
      And.intro hindex hindex
  have hpred :
      RAM.Structured.Footprint.CmdWritesWithin
        (coordinateReadFootprint regs)
        (.basic (.sub bank.basePred bank.base bank.one)) := by
    simpa [RAM.Structured.Footprint.CmdWritesWithin,
      RAM.Structured.Footprint.BasicWritesWithin] using hbasePred
  have hread :
      RAM.Structured.Footprint.CmdWritesWithin
        (coordinateReadFootprint regs)
        (NeighborhoodProgram.bankRead bank) :=
    cmdWritesWithin_mono (Finset.subset_union_left) _
      (NeighborhoodProgram.bankRead_sourceWritesWithin bank)
  have hrestore :
      RAM.Structured.Footprint.CmdWritesWithin
        (coordinateReadFootprint regs)
        (copy range.count (savedRangeCount regs)) := by
    simpa [copy, RAM.Structured.Footprint.CmdWritesWithin,
      RAM.Structured.Footprint.BasicWritesWithin] using
      And.intro hcount hcount
  simpa only [readResidueCoordinate, Cmd.seqList,
    RAM.Structured.Footprint.CmdWritesWithin] using
    And.intro hsave
      (And.intro hcopyIndex
        (And.intro hpred (And.intro hread hrestore)))

private theorem coordinateBank_outside
    (regs : NeighborhoodTrial.Registers controller)
    (target : Fin 34)
    (hmap :
      ∀ slot : Fin 12, coordinateBankMap slot ≠ target) :
    regs.index target ∉
      (coordinateBankRegisters regs).footprint := by
  intro hmem
  obtain ⟨slot, _, heq⟩ := Finset.mem_image.mp hmem
  have hindex := regs.injective heq
  change coordinateBankMap slot = target at hindex
  exact hmap slot hindex

private theorem coordinateRead_outside
    (regs : NeighborhoodTrial.Registers controller)
    (target : Fin 34)
    (hmap :
      ∀ slot : Fin 12, coordinateBankMap slot ≠ target)
    (hsaved : (31 : Fin 34) ≠ target)
    (hcount : (10 : Fin 34) ≠ target) :
    regs.index target ∉ coordinateReadFootprint regs := by
  intro hmem
  simp only [coordinateReadFootprint, Finset.mem_union,
    Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with hbank | hsavedEq | hcountEq
  · exact coordinateBank_outside regs target hmap hbank
  · exact hsaved (regs.injective hsavedEq.symm)
  · exact hcount (regs.injective hcountEq.symm)

theorem readResidueCoordinate_runs_internal
    {tm : TM workTapeCount}
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (tape : TapeIndex workTapeCount)
    (slot : NeighborhoodGraph.Slot)
    (interval : ℕ)
    (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (register :
      Fin
        (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount + 1))
    (chunk :
      Fin
        (PrimeGrouped.Logarithmic.chunkCount
          (NeighborhoodExecutableEvaluation.payloadWidth
            tm instanceData.blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount)))
    (store : Store)
    (hcontext :
      ComputationContext regs instanceData tape slot interval
        logicalBank store)
    (hcoordinate :
      store (coordinateIndex regs) =
        NeighborhoodProgram.residueBankIndex
          tm instanceData.blockLength register chunk)
    (hone :
      store (CombineValue.rangeRegisters regs).one = 1) :
    ∃ final,
      Runs (readResidueCoordinate regs) store final ∧
      ResidueCoordinatePost regs (logicalBank register chunk)
        (NeighborhoodProgram.residueBankIndex
          tm instanceData.blockLength register chunk)
        store final ∧
      ComputationContext regs instanceData tape slot interval
        logicalBank final := by
  let range := CombineValue.rangeRegisters regs
  let bank := coordinateBankRegisters regs
  let coordinate :=
    NeighborhoodProgram.residueBankIndex
      tm instanceData.blockLength register chunk
  let base := Representation.fieldBase instanceData
  have hbase : 0 < base := by
    unfold base Representation.fieldBase Representation.digitBase
      CandidateParameters.domainSize
    exact Nat.pow_pos
      (PrimeGrouped.Logarithmic.domainSize_pos _ _)
  obtain ⟨afterSave, hsave, hsaveValue, hsaveOutside⟩ :=
    copy_runs (savedRangeCount regs) range.count store
      (regs.injective.ne (by decide))
  have hafterSaveCoordinate :
      afterSave (coordinateIndex regs) = coordinate := by
    rw [hsaveOutside (coordinateIndex regs)
      (regs.injective.ne (by decide))]
    exact hcoordinate
  obtain ⟨afterIndex, hcopyIndex, hindexValue,
      hindexOutside⟩ :=
    copy_runs bank.indexCount (coordinateIndex regs) afterSave
      (regs.injective.ne (by decide))
  have hafterIndexIndex :
      afterIndex bank.indexCount = coordinate :=
    hindexValue.trans hafterSaveCoordinate
  have hafterIndexWord :
      afterIndex bank.word = store bank.word := by
    rw [hindexOutside bank.word (regs.injective.ne (by decide))]
    rw [hsaveOutside bank.word (regs.injective.ne (by decide))]
  have hafterIndexBase :
      afterIndex bank.base = base := by
    rw [hindexOutside bank.base (regs.injective.ne (by decide))]
    rw [hsaveOutside bank.base (regs.injective.ne (by decide))]
    exact hcontext.parameters.bankBase_eq
  have hafterIndexOne :
      afterIndex bank.one = 1 := by
    rw [hindexOutside bank.one (regs.injective.ne (by decide))]
    rw [hsaveOutside bank.one (regs.injective.ne (by decide))]
    exact hone
  let afterPred :=
    (Basic.sub bank.basePred bank.base bank.one).exec afterIndex
  have hpredRun :
      Runs (.basic (.sub bank.basePred bank.base bank.one))
        afterIndex afterPred :=
    Runs.basic _ _
  have hafterPredWord :
      afterPred bank.word = store bank.word := by
    simp [afterPred, Basic.exec, bank.injective.eq_iff,
      hafterIndexWord]
  have hafterPredBase :
      afterPred bank.base = base := by
    simp [afterPred, Basic.exec, bank.injective.eq_iff,
      hafterIndexBase]
  have hafterPredBasePred :
      afterPred bank.basePred = base - 1 := by
    simp [afterPred, Basic.exec, hafterIndexBase, hafterIndexOne]
  have hafterPredOne :
      afterPred bank.one = 1 := by
    simp [afterPred, Basic.exec, bank.injective.eq_iff,
      hafterIndexOne]
  have hafterPredIndex :
      afterPred bank.indexCount = coordinate := by
    simp [afterPred, Basic.exec, bank.injective.eq_iff,
      hafterIndexIndex]
  obtain
    ⟨afterRead, hread, hreadWord, _, _, _, hreadResult,
      hreadBase, _, hreadOne, hreadReplacement⟩ :=
    NeighborhoodProgram.bankRead_runs bank afterPred base
      (store bank.word) coordinate hbase hafterPredWord
      hafterPredBase hafterPredBasePred hafterPredOne
      hafterPredIndex
  have hsavedOutsideBank :
      savedRangeCount regs ∉ bank.footprint := by
    exact coordinateBank_outside regs (31 : Fin 34) (by decide)
  have hafterReadSaved :
      afterRead (savedRangeCount regs) =
        store range.count := by
    rw [RAM.Structured.Footprint.runs_eq_outside
      (NeighborhoodProgram.bankRead_sourceWritesWithin bank)
      hread hsavedOutsideBank]
    have hafterPredSaved :
        afterPred (savedRangeCount regs) =
          afterIndex (savedRangeCount regs) := by
      have hne :
          savedRangeCount regs ≠ bank.basePred :=
        regs.injective.ne (by decide)
      simp [afterPred, Basic.exec, Function.update_of_ne, hne]
    rw [hafterPredSaved]
    rw [hindexOutside (savedRangeCount regs)
      (regs.injective.ne (by decide))]
    exact hsaveValue
  obtain ⟨final, hrestore, hrestoreValue,
      hrestoreOutside⟩ :=
    copy_runs range.count (savedRangeCount regs) afterRead
      (regs.injective.ne (by decide))
  have hrun :
      Runs (readResidueCoordinate regs) store final := by
    simpa [readResidueCoordinate, Cmd.seqList] using
      Runs.seq hsave
        (Runs.seq hcopyIndex
          (Runs.seq hpredRun (Runs.seq hread hrestore)))
  have hfinalOutside :
      ∀ address, address ∉ coordinateReadFootprint regs →
        final address = store address := by
    intro address haddress
    exact RAM.Structured.Footprint.runs_eq_outside
      (readResidueCoordinate_writesWithin_internal regs)
      hrun haddress
  have hafterPredAccumulator :
      afterPred range.accumulator = store range.accumulator := by
    have hne : range.accumulator ≠ bank.basePred :=
      regs.injective.ne (by decide)
    rw [show afterPred range.accumulator =
        afterIndex range.accumulator by
      simp [afterPred, Basic.exec, Function.update_of_ne, hne]]
    rw [hindexOutside range.accumulator
      (regs.injective.ne (by decide))]
    rw [hsaveOutside range.accumulator
      (regs.injective.ne (by decide))]
  have hfinalAccumulator :
      final range.accumulator = store range.accumulator := by
    rw [hrestoreOutside range.accumulator
      (regs.injective.ne (by decide))]
    exact hreadReplacement.trans hafterPredAccumulator
  have hfinalBankBase :
      final (Layout.bankRadix regs) = base := by
    rw [hrestoreOutside (Layout.bankRadix regs)
      (regs.injective.ne (by decide))]
    exact hreadBase
  have hfinalContext :
      ComputationContext regs instanceData tape slot interval
        logicalBank final := by
    exact
      { parameters :=
          { blockLength_eq :=
              (hfinalOutside _ (coordinateRead_outside regs
                (2 : Fin 34) (by decide) (by decide)
                (by decide))).trans
                hcontext.parameters.blockLength_eq
            horizon_eq :=
              (hfinalOutside _ (coordinateRead_outside regs
                (3 : Fin 34) (by decide) (by decide)
                (by decide))).trans hcontext.parameters.horizon_eq
            digitBase_eq :=
              (hfinalOutside _ (coordinateRead_outside regs
                (8 : Fin 34) (by decide) (by decide)
                (by decide))).trans
                hcontext.parameters.digitBase_eq
            bankBase_eq := hfinalBankBase
            frameBase_eq :=
              (hfinalOutside _ (coordinateRead_outside regs
                (13 : Fin 34) (by decide) (by decide)
                (by decide))).trans
                hcontext.parameters.frameBase_eq
            chunkCount_eq :=
              (hfinalOutside _ (coordinateRead_outside regs
                (7 : Fin 34) (by decide) (by decide)
                (by decide))).trans
                hcontext.parameters.chunkCount_eq
            bankDigitCount_eq :=
              (hfinalOutside _ (coordinateRead_outside regs
                (15 : Fin 34) (by decide) (by decide)
                (by decide))).trans
                hcontext.parameters.bankDigitCount_eq
            modulus_eq :=
              (hfinalOutside _ (coordinateRead_outside regs
                (24 : Fin 34) (by decide) (by decide)
                (by decide))).trans hcontext.parameters.modulus_eq
            modulusPred_eq :=
              (hfinalOutside _ (coordinateRead_outside regs
                (16 : Fin 34) (by decide) (by decide)
                (by decide))).trans
                hcontext.parameters.modulusPred_eq }
        nodeCode_eq :=
          (hfinalOutside _ (coordinateRead_outside regs
            (23 : Fin 34) (by decide) (by decide)
            (by decide))).trans hcontext.nodeCode_eq
        bank := by
          change
            NeighborhoodProgram.RepresentsResidueBank
              tm instanceData.blockLength
              (Representation.fieldBase instanceData)
              (final bank.word) logicalBank
          rw [hrestoreOutside bank.word
            (regs.injective.ne (by decide))]
          rw [hreadWord]
          simpa [bank, coordinateBankRegisters,
            NeighborhoodTrial.Registers.layout] using hcontext.bank }
  refine ⟨final, hrun, ?_, hfinalContext⟩
  exact
    { result_eq := by
        rw [hrestoreOutside bank.result
          (regs.injective.ne (by decide))]
        exact hreadResult.trans (hcontext.bank register chunk)
      bank_eq := by
        rw [hrestoreOutside bank.word
          (regs.injective.ne (by decide))]
        exact hreadWord
      accumulator_eq := hfinalAccumulator
      remaining_eq :=
        hfinalOutside _ (coordinateRead_outside regs
          (21 : Fin 34) (by decide) (by decide) (by decide))
      modulus_eq :=
        hfinalOutside _ (coordinateRead_outside regs
          (24 : Fin 34) (by decide) (by decide) (by decide))
      modulusPred_eq :=
        hfinalOutside _ (coordinateRead_outside regs
          (16 : Fin 34) (by decide) (by decide) (by decide))
      one_eq := by
        rw [hrestoreOutside range.one
          (regs.injective.ne (by decide))]
        exact hreadOne.trans hone.symm
      count_eq := hrestoreValue.trans hafterReadSaved
      coordinate_eq :=
        (hfinalOutside _ (coordinateRead_outside regs
          (30 : Fin 34) (by decide) (by decide)
          (by decide))).trans hcoordinate }

theorem combineTerm_writesWithin_internal
    (regs : NeighborhoodTrial.Registers controller)
    (packedKernel basisKernel : Cmd)
    (hpacked :
      RAM.Structured.Footprint.CmdWritesWithin
        (CombineValue.combineScratchFootprint regs) packedKernel)
    (hbasis :
      RAM.Structured.Footprint.CmdWritesWithin
        (CombineValue.combineScratchFootprint regs) basisKernel) :
    RAM.Structured.Footprint.CmdWritesWithin
      (CombineValue.combineScratchFootprint regs)
      (combineTerm regs packedKernel basisKernel) := by
  have hterm := combineScratch_mem regs (11 : Fin 19)
  have htest := combineScratch_mem regs (3 : Fin 19)
  change (CombineValue.rangeRegisters regs).term ∈
    CombineValue.combineScratchFootprint regs at hterm
  change (CombineValue.rangeRegisters regs).test ∈
    CombineValue.combineScratchFootprint regs at htest
  simp_all [combineTerm, RuntimeArithmetic.mulMod,
    RuntimeArithmetic.reduce, RuntimeArithmetic.reduceBody,
    RuntimeArithmetic.reduceTestOp, termReduceRegisters,
    Cmd.seqList, RAM.Structured.Footprint.CmdWritesWithin,
    RAM.Structured.Footprint.BasicWritesWithin]

theorem combineTerm_layout_writesWithin_internal
    (regs : NeighborhoodTrial.Registers controller)
    (packedKernel basisKernel : Cmd)
    (hpacked :
      RAM.Structured.Footprint.CmdWritesWithin
        (CombineValue.combineScratchFootprint regs) packedKernel)
    (hbasis :
      RAM.Structured.Footprint.CmdWritesWithin
        (CombineValue.combineScratchFootprint regs) basisKernel) :
    RAM.Structured.Footprint.CmdWritesWithin
      regs.layout.footprint
      (combineTerm regs packedKernel basisKernel) :=
  cmdWritesWithin_mono
    (CombineValue.combineScratchFootprint_subset_layout regs) _
    (combineTerm_writesWithin_internal regs packedKernel basisKernel
      hpacked hbasis)

theorem combineTerm_preservesABI_internal
    (regs : NeighborhoodTrial.Registers controller)
    (packedKernel basisKernel : Cmd)
    (hpacked :
      RAM.Structured.Footprint.CmdWritesWithin
        (CombineValue.combineScratchFootprint regs) packedKernel)
    (hbasis :
      RAM.Structured.Footprint.CmdWritesWithin
        (CombineValue.combineScratchFootprint regs) basisKernel)
    {initial final : Store}
    (hrun :
      Runs (combineTerm regs packedKernel basisKernel)
        initial final) :
    ControlDecode.PreservesABI regs initial final :=
  CombineValue.preservesABI_of_combineScratch regs
    (combineTerm_writesWithin_internal regs packedKernel basisKernel
      hpacked hbasis)
    hrun

theorem combineTerm_specAt_internal
    (regs : NeighborhoodTrial.Registers controller)
    (packedKernel basisKernel : Cmd)
    (modulus : ℕ) (packed basis : ℕ → ℕ)
    (hmodulus : 0 < modulus)
    (hpacked :
      PackedKernelSpecAt regs packedKernel modulus packed)
    (hbasis :
      BasisKernelSpecAt regs basisKernel modulus basis) :
    CombineValue.TermKernelSpecAt
      (CombineValue.rangeRegisters regs)
      (combineTerm regs packedKernel basisKernel)
      modulus
      (fun index =>
        PrimeField.Runtime.mul modulus
          (packed index) (basis index)) := by
  intro store index hremaining hmodulusValue hmodulusPred hone
  obtain ⟨afterPacked, hpackedRun, hpackedPost⟩ :=
    hpacked store index hremaining hmodulusValue hmodulusPred hone
  have hpackedModulus :
      afterPacked (CombineValue.rangeRegisters regs).modulus =
        modulus :=
    hpackedPost.modulus_eq.trans hmodulusValue
  have hpackedModulusPred :
      afterPacked (CombineValue.rangeRegisters regs).modulusPred =
        modulus - 1 :=
    hpackedPost.modulusPred_eq.trans hmodulusPred
  have hpackedOne :
      afterPacked (CombineValue.rangeRegisters regs).one = 1 :=
    hpackedPost.one_eq.trans hone
  obtain ⟨afterBasis, hbasisRun, hbasisPost⟩ :=
    hbasis afterPacked index hpackedPost.remaining_eq
      hpackedModulus hpackedModulusPred hpackedOne
  have hfinalPacked :
      afterBasis (packedValue regs) = packed index :=
    hbasisPost.packed_eq.trans hpackedPost.packed_eq
  have hfinalBasis :
      afterBasis (basisValue regs) = basis index :=
    hbasisPost.basis_eq
  have hfinalAccumulator :
      afterBasis
          (CombineValue.rangeRegisters regs).accumulator =
        store (CombineValue.rangeRegisters regs).accumulator :=
    hbasisPost.accumulator_eq.trans hpackedPost.accumulator_eq
  have hfinalModulus :
      afterBasis (CombineValue.rangeRegisters regs).modulus =
        modulus :=
    hbasisPost.modulus_eq.trans hpackedModulus
  have hfinalModulusPred :
      afterBasis (CombineValue.rangeRegisters regs).modulusPred =
        modulus - 1 :=
    hbasisPost.modulusPred_eq.trans hpackedModulusPred
  have hfinalOne :
      afterBasis (CombineValue.rangeRegisters regs).one = 1 :=
    hbasisPost.one_eq.trans hpackedOne
  have hfinalCount :
      afterBasis (CombineValue.rangeRegisters regs).count =
        store (CombineValue.rangeRegisters regs).count :=
    hbasisPost.count_eq.trans hpackedPost.count_eq
  let termValue :=
    PrimeField.Runtime.mul modulus
      (packed index) (basis index)
  let final :=
    RuntimeArithmetic.reduceResultStore
      (termReduceRegisters regs) termValue afterBasis
  have hmul :
      Runs
          (RuntimeArithmetic.mulMod (termReduceRegisters regs)
            (packedValue regs) (basisValue regs))
          afterBasis final := by
    simpa [final, termValue, hfinalPacked, hfinalBasis,
      PrimeField.Runtime.mul, PrimeField.Runtime.mulInput,
      PrimeField.Runtime.normalize, Nat.mul_mod] using
      RuntimeArithmetic.mulMod_runs (termReduceRegisters regs)
        (packedValue regs) (basisValue regs) afterBasis
        modulus hmodulus hfinalModulus hfinalModulusPred
  have hrun :
      Runs (combineTerm regs packedKernel basisKernel)
        store final := by
    simpa [combineTerm, Cmd.seqList] using
      Runs.seq hpackedRun (Runs.seq hbasisRun hmul)
  refine ⟨final, hrun, ?_⟩
  exact
    { term_eq := by
        simp [final, termValue,
          RuntimeArithmetic.reduceResultStore,
          termReduceRegisters, CombineValue.rangeRegisters,
          regs.injective.eq_iff]
      accumulator_eq := by
        simpa [final, RuntimeArithmetic.reduceResultStore,
          termReduceRegisters, CombineValue.rangeRegisters,
          regs.injective.eq_iff] using
          hfinalAccumulator
      remaining_eq := by
        simpa [final, RuntimeArithmetic.reduceResultStore,
          termReduceRegisters, CombineValue.rangeRegisters,
          regs.injective.eq_iff] using
          hbasisPost.remaining_eq
      modulus_eq := by
        simpa [final, RuntimeArithmetic.reduceResultStore,
          termReduceRegisters, CombineValue.rangeRegisters,
          regs.injective.eq_iff] using
          hbasisPost.modulus_eq.trans hpackedPost.modulus_eq
      modulusPred_eq := by
        simpa [final, RuntimeArithmetic.reduceResultStore,
          termReduceRegisters, CombineValue.rangeRegisters,
          regs.injective.eq_iff] using
          hbasisPost.modulusPred_eq.trans
            hpackedPost.modulusPred_eq
      one_eq := by
        simpa [final, RuntimeArithmetic.reduceResultStore,
          termReduceRegisters, CombineValue.rangeRegisters,
          regs.injective.eq_iff] using
          hbasisPost.one_eq.trans hpackedPost.one_eq
      count_eq := by
        simpa [final, RuntimeArithmetic.reduceResultStore,
          termReduceRegisters, CombineValue.rangeRegisters,
          regs.injective.eq_iff] using
          hfinalCount }

theorem combineTerm_specAtAnyContext_internal
    (regs : NeighborhoodTrial.Registers controller)
    (packedKernel basisKernel : Cmd)
    (modulus : ℕ) (packed basis : ℕ → ℕ)
    (context : Store → Prop)
    (htransport :
      ∀ {initial final : Store},
        context initial →
        ControlDecode.PreservesABI regs initial final →
        final regs.layout.bank = initial regs.layout.bank →
        context final)
    (hmodulus : 0 < modulus)
    (hpacked :
      PackedKernelSpecAtContext regs packedKernel modulus packed
        context)
    (hbasis :
      BasisKernelSpecAtContext regs basisKernel modulus basis
        context) :
    CombineValue.TermKernelSpecAtContext
      (CombineValue.rangeRegisters regs)
      (combineTerm regs packedKernel basisKernel)
      modulus
      (fun index =>
        PrimeField.Runtime.mul modulus
          (packed index) (basis index))
      context := by
  intro store index hcontext hremaining hmodulusValue
    hmodulusPred hone
  obtain ⟨afterPacked, hpackedRun, hpackedPost,
      hpackedContext⟩ :=
    hpacked store index hcontext hremaining hmodulusValue
      hmodulusPred hone
  have hpackedModulus :
      afterPacked (CombineValue.rangeRegisters regs).modulus =
        modulus :=
    hpackedPost.modulus_eq.trans hmodulusValue
  have hpackedModulusPred :
      afterPacked (CombineValue.rangeRegisters regs).modulusPred =
        modulus - 1 :=
    hpackedPost.modulusPred_eq.trans hmodulusPred
  have hpackedOne :
      afterPacked (CombineValue.rangeRegisters regs).one = 1 :=
    hpackedPost.one_eq.trans hone
  obtain ⟨afterBasis, hbasisRun, hbasisPost,
      hbasisContext⟩ :=
    hbasis afterPacked index hpackedContext
      hpackedPost.remaining_eq hpackedModulus
      hpackedModulusPred hpackedOne
  have hfinalPacked :
      afterBasis (packedValue regs) = packed index :=
    hbasisPost.packed_eq.trans hpackedPost.packed_eq
  have hfinalBasis :
      afterBasis (basisValue regs) = basis index :=
    hbasisPost.basis_eq
  have hfinalAccumulator :
      afterBasis
          (CombineValue.rangeRegisters regs).accumulator =
        store (CombineValue.rangeRegisters regs).accumulator :=
    hbasisPost.accumulator_eq.trans hpackedPost.accumulator_eq
  have hfinalModulus :
      afterBasis (CombineValue.rangeRegisters regs).modulus =
        modulus :=
    hbasisPost.modulus_eq.trans hpackedModulus
  have hfinalModulusPred :
      afterBasis (CombineValue.rangeRegisters regs).modulusPred =
        modulus - 1 :=
    hbasisPost.modulusPred_eq.trans hpackedModulusPred
  have hfinalOne :
      afterBasis (CombineValue.rangeRegisters regs).one = 1 :=
    hbasisPost.one_eq.trans hpackedOne
  have hfinalCount :
      afterBasis (CombineValue.rangeRegisters regs).count =
        store (CombineValue.rangeRegisters regs).count :=
    hbasisPost.count_eq.trans hpackedPost.count_eq
  let termValue :=
    PrimeField.Runtime.mul modulus
      (packed index) (basis index)
  let final :=
    RuntimeArithmetic.reduceResultStore
      (termReduceRegisters regs) termValue afterBasis
  have hmul :
      Runs
          (RuntimeArithmetic.mulMod (termReduceRegisters regs)
            (packedValue regs) (basisValue regs))
          afterBasis final := by
    simpa [final, termValue, hfinalPacked, hfinalBasis,
      PrimeField.Runtime.mul, PrimeField.Runtime.mulInput,
      PrimeField.Runtime.normalize, Nat.mul_mod] using
      RuntimeArithmetic.mulMod_runs (termReduceRegisters regs)
        (packedValue regs) (basisValue regs) afterBasis
        modulus hmodulus hfinalModulus hfinalModulusPred
  have hrun :
      Runs (combineTerm regs packedKernel basisKernel)
        store final := by
    simpa [combineTerm, Cmd.seqList] using
      Runs.seq hpackedRun (Runs.seq hbasisRun hmul)
  have habi :
      ControlDecode.PreservesABI regs afterBasis final := by
    exact
      { fuel_eq := by
          simp [final, RuntimeArithmetic.reduceResultStore,
            termReduceRegisters, CombineValue.rangeRegisters,
            regs.injective.eq_iff]
        nodeCode_eq := by
          simp [final, RuntimeArithmetic.reduceResultStore,
            termReduceRegisters, CombineValue.rangeRegisters,
            regs.injective.eq_iff]
        scalar_eq := by
          simp [final, RuntimeArithmetic.reduceResultStore,
            termReduceRegisters, CombineValue.rangeRegisters,
            regs.injective.eq_iff]
        out_eq := by
          simp [final, RuntimeArithmetic.reduceResultStore,
            termReduceRegisters, CombineValue.rangeRegisters,
            regs.injective.eq_iff]
        phaseCode_eq := by
          simp [final, RuntimeArithmetic.reduceResultStore,
            termReduceRegisters, CombineValue.rangeRegisters,
            regs.injective.eq_iff]
        active_eq := by
          simp [final, RuntimeArithmetic.reduceResultStore,
            termReduceRegisters, CombineValue.rangeRegisters,
            regs.injective.eq_iff]
        blockLength_eq := by
          simp [final, RuntimeArithmetic.reduceResultStore,
            termReduceRegisters, CombineValue.rangeRegisters,
            regs.injective.eq_iff]
        horizon_eq := by
          simp [final, RuntimeArithmetic.reduceResultStore,
            termReduceRegisters, CombineValue.rangeRegisters,
            regs.injective.eq_iff]
        chunkCount_eq := by
          simp [final, RuntimeArithmetic.reduceResultStore,
            termReduceRegisters, CombineValue.rangeRegisters,
            regs.injective.eq_iff]
        chunkRadix_eq := by
          simp [final, RuntimeArithmetic.reduceResultStore,
            termReduceRegisters, CombineValue.rangeRegisters,
            regs.injective.eq_iff]
        frameRadix_eq := by
          simp [final, RuntimeArithmetic.reduceResultStore,
            termReduceRegisters, CombineValue.rangeRegisters,
            regs.injective.eq_iff]
        bankRadix_eq := by
          simp [final, RuntimeArithmetic.reduceResultStore,
            termReduceRegisters, CombineValue.rangeRegisters,
            regs.injective.eq_iff]
        bankDigitCount_eq := by
          simp [final, RuntimeArithmetic.reduceResultStore,
            termReduceRegisters, CombineValue.rangeRegisters,
            regs.injective.eq_iff]
        modulusPred_eq := by
          simp [final, RuntimeArithmetic.reduceResultStore,
            termReduceRegisters, CombineValue.rangeRegisters,
            regs.injective.eq_iff]
        modulus_eq := by
          simp [final, RuntimeArithmetic.reduceResultStore,
            termReduceRegisters, CombineValue.rangeRegisters,
            regs.injective.eq_iff] }
  have hbank :
      final regs.layout.bank = afterBasis regs.layout.bank := by
    simp [final, RuntimeArithmetic.reduceResultStore,
      termReduceRegisters, CombineValue.rangeRegisters,
      NeighborhoodTrial.Registers.layout, regs.injective.eq_iff]
  have hfinalContext : context final :=
    htransport hbasisContext habi hbank
  refine ⟨final, hrun, ?_, hfinalContext⟩
  exact
    { term_eq := by
        simp [final, termValue,
          RuntimeArithmetic.reduceResultStore,
          termReduceRegisters, CombineValue.rangeRegisters,
          regs.injective.eq_iff]
      accumulator_eq := by
        simpa [final, RuntimeArithmetic.reduceResultStore,
          termReduceRegisters, CombineValue.rangeRegisters,
          regs.injective.eq_iff] using
          hfinalAccumulator
      remaining_eq := by
        simpa [final, RuntimeArithmetic.reduceResultStore,
          termReduceRegisters, CombineValue.rangeRegisters,
          regs.injective.eq_iff] using
          hbasisPost.remaining_eq
      modulus_eq := by
        simpa [final, RuntimeArithmetic.reduceResultStore,
          termReduceRegisters, CombineValue.rangeRegisters,
          regs.injective.eq_iff] using
          hbasisPost.modulus_eq.trans hpackedPost.modulus_eq
      modulusPred_eq := by
        simpa [final, RuntimeArithmetic.reduceResultStore,
          termReduceRegisters, CombineValue.rangeRegisters,
          regs.injective.eq_iff] using
          hbasisPost.modulusPred_eq.trans
            hpackedPost.modulusPred_eq
      one_eq := by
        simpa [final, RuntimeArithmetic.reduceResultStore,
          termReduceRegisters, CombineValue.rangeRegisters,
          regs.injective.eq_iff] using
          hbasisPost.one_eq.trans hpackedPost.one_eq
      count_eq := by
        simpa [final, RuntimeArithmetic.reduceResultStore,
          termReduceRegisters, CombineValue.rangeRegisters,
          regs.injective.eq_iff] using
          hfinalCount }

theorem combineTerm_specAtContext_internal
    {tm : TM workTapeCount}
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (tape : TapeIndex workTapeCount)
    (slot : NeighborhoodGraph.Slot)
    (interval : ℕ)
    (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (packedKernel basisKernel : Cmd)
    (modulus : ℕ) (packed basis : ℕ → ℕ)
    (hmodulus : 0 < modulus)
    (hpacked :
      PackedKernelSpecAtContext regs packedKernel modulus packed
        (ComputationContext regs instanceData tape slot interval
          logicalBank))
    (hbasis :
      BasisKernelSpecAtContext regs basisKernel modulus basis
        (ComputationContext regs instanceData tape slot interval
          logicalBank)) :
    CombineValue.TermKernelSpecAtContext
      (CombineValue.rangeRegisters regs)
      (combineTerm regs packedKernel basisKernel)
      modulus
      (fun index =>
        PrimeField.Runtime.mul modulus
          (packed index) (basis index))
      (ComputationContext regs instanceData tape slot interval
        logicalBank) :=
  combineTerm_specAtAnyContext_internal
    regs packedKernel basisKernel modulus packed basis
    (ComputationContext regs instanceData tape slot interval logicalBank)
    (fun hcontext habi hbank =>
      computationContext_transport_internal
        regs instanceData tape slot interval logicalBank
        hcontext habi hbank)
    hmodulus hpacked hbasis

theorem assignmentTerm_eq_factors_internal
    (payloadWidth fanIn : ℕ)
    (combine :
      (Fin fanIn → Fin payloadWidth → Bool) →
        Fin payloadWidth → Bool)
    (args :
      Fin fanIn →
        Fin
          (PrimeGrouped.Logarithmic.chunkCount payloadWidth fanIn) →
          ℕ)
    (outputChunk :
      Fin
        (PrimeGrouped.Logarithmic.chunkCount payloadWidth fanIn))
    (code : ℕ) :
    CombineValue.assignmentTerm payloadWidth fanIn combine args
        outputChunk code =
      PrimeField.Runtime.mul
        (NeighborhoodExecutableEvaluation.Residue.fieldModulus
          payloadWidth fanIn)
        (packedAssignmentValue payloadWidth fanIn combine
          outputChunk code)
        (basisAssignmentValue payloadWidth fanIn args code) := by
  rfl

theorem combineTerm_assignmentSpecAt_internal
    (regs : NeighborhoodTrial.Registers controller)
    (packedKernel basisKernel : Cmd)
    (payloadWidth fanIn : ℕ)
    (combine :
      (Fin fanIn → Fin payloadWidth → Bool) →
        Fin payloadWidth → Bool)
    (args :
      Fin fanIn →
        Fin
          (PrimeGrouped.Logarithmic.chunkCount payloadWidth fanIn) →
          ℕ)
    (outputChunk :
      Fin
        (PrimeGrouped.Logarithmic.chunkCount payloadWidth fanIn))
    (hpacked :
      PackedKernelSpecAt regs packedKernel
        (NeighborhoodExecutableEvaluation.Residue.fieldModulus
          payloadWidth fanIn)
        (packedAssignmentValue payloadWidth fanIn combine outputChunk))
    (hbasis :
      BasisKernelSpecAt regs basisKernel
        (NeighborhoodExecutableEvaluation.Residue.fieldModulus
          payloadWidth fanIn)
        (basisAssignmentValue payloadWidth fanIn args)) :
    CombineValue.CombineTermKernelSpecAt
      (CombineValue.rangeRegisters regs)
      (combineTerm regs packedKernel basisKernel)
      payloadWidth fanIn combine args outputChunk := by
  have hfactorSpec :=
    combineTerm_specAt_internal regs packedKernel basisKernel
      (NeighborhoodExecutableEvaluation.Residue.fieldModulus
        payloadWidth fanIn)
      (packedAssignmentValue payloadWidth fanIn combine outputChunk)
      (basisAssignmentValue payloadWidth fanIn args)
      (CombineValue.fieldModulus_pos payloadWidth fanIn)
      hpacked hbasis
  intro store index hremaining hmodulus hmodulusPred hone
  obtain ⟨final, hrun, hpost⟩ :=
    hfactorSpec store index hremaining hmodulus
      hmodulusPred hone
  refine ⟨final, hrun, ?_⟩
  rw [assignmentTerm_eq_factors_internal
    payloadWidth fanIn combine args outputChunk index]
  exact hpost

theorem evaluateNode_combineTerm_runsAnyContext_internal
    (regs : NeighborhoodTrial.Registers controller)
    (packedKernel basisKernel : Cmd)
    (payloadWidth fanIn : ℕ)
    (combine :
      (Fin fanIn → Fin payloadWidth → Bool) →
        Fin payloadWidth → Bool)
    (args :
      Fin fanIn →
        Fin
          (PrimeGrouped.Logarithmic.chunkCount payloadWidth fanIn) →
          ℕ)
    (outputChunk :
      Fin
        (PrimeGrouped.Logarithmic.chunkCount payloadWidth fanIn))
    (context : Store → Prop)
    (htransport :
      ∀ {initial final : Store},
        context initial →
        ControlDecode.PreservesABI regs initial final →
        final regs.layout.bank = initial regs.layout.bank →
        context final)
    (hstable :
      CombineValue.StableUnderDriverWrites
        (CombineValue.rangeRegisters regs) context)
    (hpacked :
      PackedKernelSpecAtContext regs packedKernel
        (NeighborhoodExecutableEvaluation.Residue.fieldModulus
          payloadWidth fanIn)
        (packedAssignmentValue payloadWidth fanIn combine outputChunk)
        context)
    (hbasis :
      BasisKernelSpecAtContext regs basisKernel
        (NeighborhoodExecutableEvaluation.Residue.fieldModulus
          payloadWidth fanIn)
        (basisAssignmentValue payloadWidth fanIn args)
        context)
    (store : Store)
    (hcontext : context store)
    (hmodulusValue :
      store (CombineValue.rangeRegisters regs).modulus =
        NeighborhoodExecutableEvaluation.Residue.fieldModulus
          payloadWidth fanIn)
    (hmodulusPred :
      store (CombineValue.rangeRegisters regs).modulusPred =
        NeighborhoodExecutableEvaluation.Residue.fieldModulus
            payloadWidth fanIn -
          1)
    (hcount :
      store (CombineValue.rangeRegisters regs).count =
        CombineValue.assignmentCount payloadWidth fanIn) :
    ∃ final,
      Runs
          (CombineValue.rangeFold .add
            (CombineValue.rangeRegisters regs)
            (combineTerm regs packedKernel basisKernel))
          store final ∧
      final (CombineValue.rangeRegisters regs).accumulator =
        NeighborhoodExecutableEvaluation.Residue.evaluateNode
          payloadWidth fanIn combine args outputChunk ∧
      CombineValue.RangePost .add
        (CombineValue.rangeRegisters regs)
        (NeighborhoodExecutableEvaluation.Residue.fieldModulus
          payloadWidth fanIn)
        (CombineValue.assignmentCount payloadWidth fanIn)
        (CombineValue.assignmentTerm
          payloadWidth fanIn combine args outputChunk)
        store final ∧
      context final := by
  have hfactorSpec :=
    combineTerm_specAtAnyContext_internal
      regs packedKernel basisKernel
      (NeighborhoodExecutableEvaluation.Residue.fieldModulus
        payloadWidth fanIn)
      (packedAssignmentValue payloadWidth fanIn combine outputChunk)
      (basisAssignmentValue payloadWidth fanIn args)
      context htransport
      (CombineValue.fieldModulus_pos payloadWidth fanIn)
      hpacked hbasis
  have htermSpec :
      CombineValue.TermKernelSpecAtContext
        (CombineValue.rangeRegisters regs)
        (combineTerm regs packedKernel basisKernel)
        (NeighborhoodExecutableEvaluation.Residue.fieldModulus
          payloadWidth fanIn)
        (CombineValue.assignmentTerm
          payloadWidth fanIn combine args outputChunk)
        context := by
    intro current index hcurrentContext hremaining hmodulus
      hcurrentModulusPred hone
    obtain ⟨final, hrun, hpost, hfinalContext⟩ :=
      hfactorSpec current index hcurrentContext hremaining
        hmodulus hcurrentModulusPred hone
    refine ⟨final, hrun, ?_, hfinalContext⟩
    rw [assignmentTerm_eq_factors_internal
      payloadWidth fanIn combine args outputChunk index]
    exact hpost
  obtain ⟨final, hrun, hpost, hfinalContext⟩ :=
    CombineValue.rangeFold_runsAtContext .add
      (CombineValue.rangeRegisters regs)
      (combineTerm regs packedKernel basisKernel)
      (CombineValue.assignmentTerm
        payloadWidth fanIn combine args outputChunk)
      store
      (NeighborhoodExecutableEvaluation.Residue.fieldModulus
        payloadWidth fanIn)
      (CombineValue.assignmentCount payloadWidth fanIn)
      context hstable
      htermSpec
      (CombineValue.fieldModulus_pos payloadWidth fanIn)
      hmodulusValue hmodulusPred hcount hcontext
  refine ⟨final, hrun, ?_, hpost, hfinalContext⟩
  exact hpost.accumulator_eq.trans
    (CombineValue.evaluateNode_eq_assignmentRange
      payloadWidth fanIn combine args outputChunk).symm

theorem evaluateNode_combineTerm_runsContext_internal
    {tm : TM workTapeCount}
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (tape : TapeIndex workTapeCount)
    (slot : NeighborhoodGraph.Slot)
    (interval : ℕ)
    (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (packedKernel basisKernel : Cmd)
    (payloadWidth fanIn : ℕ)
    (combine :
      (Fin fanIn → Fin payloadWidth → Bool) →
        Fin payloadWidth → Bool)
    (args :
      Fin fanIn →
        Fin
          (PrimeGrouped.Logarithmic.chunkCount payloadWidth fanIn) →
          ℕ)
    (outputChunk :
      Fin
        (PrimeGrouped.Logarithmic.chunkCount payloadWidth fanIn))
    (hpacked :
      PackedKernelSpecAtContext regs packedKernel
        (NeighborhoodExecutableEvaluation.Residue.fieldModulus
          payloadWidth fanIn)
        (packedAssignmentValue payloadWidth fanIn combine outputChunk)
        (ComputationContext regs instanceData tape slot interval
          logicalBank))
    (hbasis :
      BasisKernelSpecAtContext regs basisKernel
        (NeighborhoodExecutableEvaluation.Residue.fieldModulus
          payloadWidth fanIn)
        (basisAssignmentValue payloadWidth fanIn args)
        (ComputationContext regs instanceData tape slot interval
          logicalBank))
    (store : Store)
    (hcontext :
      ComputationContext regs instanceData tape slot interval
        logicalBank store)
    (hmodulusValue :
      store (CombineValue.rangeRegisters regs).modulus =
        NeighborhoodExecutableEvaluation.Residue.fieldModulus
          payloadWidth fanIn)
    (hmodulusPred :
      store (CombineValue.rangeRegisters regs).modulusPred =
        NeighborhoodExecutableEvaluation.Residue.fieldModulus
            payloadWidth fanIn -
          1)
    (hcount :
      store (CombineValue.rangeRegisters regs).count =
        CombineValue.assignmentCount payloadWidth fanIn) :
    ∃ final,
      Runs
          (CombineValue.rangeFold .add
            (CombineValue.rangeRegisters regs)
            (combineTerm regs packedKernel basisKernel))
          store final ∧
      final (CombineValue.rangeRegisters regs).accumulator =
        NeighborhoodExecutableEvaluation.Residue.evaluateNode
          payloadWidth fanIn combine args outputChunk ∧
      CombineValue.RangePost .add
        (CombineValue.rangeRegisters regs)
        (NeighborhoodExecutableEvaluation.Residue.fieldModulus
          payloadWidth fanIn)
        (CombineValue.assignmentCount payloadWidth fanIn)
        (CombineValue.assignmentTerm
          payloadWidth fanIn combine args outputChunk)
        store final ∧
      ComputationContext regs instanceData tape slot interval
        logicalBank final :=
  evaluateNode_combineTerm_runsAnyContext_internal
    regs packedKernel basisKernel payloadWidth fanIn combine args outputChunk
    (ComputationContext regs instanceData tape slot interval logicalBank)
    (fun hcurrent habi hbank =>
      computationContext_transport_internal
        regs instanceData tape slot interval logicalBank
        hcurrent habi hbank)
    (computationContext_stableUnderDriverWrites_internal
      regs instanceData tape slot interval logicalBank)
    hpacked hbasis store hcontext hmodulusValue hmodulusPred hcount

theorem combineResidues_combineTerm_runsContext_internal
    {tm : TM workTapeCount}
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (tape : TapeIndex workTapeCount)
    (slot : NeighborhoodGraph.Slot)
    (interval : ℕ)
    (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (packedKernel basisKernel : Cmd)
    (outputChunk :
      Fin
        (PrimeGrouped.Logarithmic.chunkCount
          (NeighborhoodExecutableEvaluation.payloadWidth
            tm instanceData.blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount)))
    (hpacked :
      ComputationPackedKernelSpecAt regs instanceData frame tape slot
        interval logicalBank outputChunk packedKernel)
    (hbasis :
      ComputationBasisKernelSpecAt regs instanceData frame tape slot
        interval logicalBank basisKernel)
    (store : Store)
    (hcontext :
      ComputationFrameContext regs instanceData frame tape slot interval
        logicalBank store)
    (hcount :
      store (CombineValue.rangeRegisters regs).count =
        CombineValue.assignmentCount
          (NeighborhoodExecutableEvaluation.payloadWidth
            tm instanceData.blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn
            workTapeCount)) :
    ∃ final,
      Runs
          (CombineValue.rangeFold .add
            (CombineValue.rangeRegisters regs)
            (combineTerm regs packedKernel basisKernel))
          store final ∧
      final (CombineValue.rangeRegisters regs).accumulator =
        NeighborhoodExecutableEvaluation.combineResidues
          tm instanceData.x instanceData.blockLength
          instanceData.encoding instanceData.positive tape slot
          interval (computationArguments frame logicalBank)
          outputChunk ∧
      CombineValue.RangePost .add
        (CombineValue.rangeRegisters regs)
        (NeighborhoodExecutableEvaluation.Residue.fieldModulus
          (NeighborhoodExecutableEvaluation.payloadWidth
            tm instanceData.blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount))
        (CombineValue.assignmentCount
          (NeighborhoodExecutableEvaluation.payloadWidth
            tm instanceData.blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount))
        (CombineValue.assignmentTerm
          (NeighborhoodExecutableEvaluation.payloadWidth
            tm instanceData.blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount)
          (NeighborhoodExecutableEvaluation.booleanCombine
            tm instanceData.x instanceData.blockLength
            instanceData.encoding instanceData.positive tape slot
            interval)
          (computationArguments frame logicalBank)
          outputChunk)
        store final ∧
      ComputationFrameContext regs instanceData frame tape slot interval
        logicalBank final := by
  have hpackedSpec :
      PackedKernelSpecAtContext regs packedKernel
        (NeighborhoodExecutableEvaluation.Residue.fieldModulus
          (NeighborhoodExecutableEvaluation.payloadWidth
            tm instanceData.blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount))
        (packedAssignmentValue
          (NeighborhoodExecutableEvaluation.payloadWidth
            tm instanceData.blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount)
          (NeighborhoodExecutableEvaluation.booleanCombine
            tm instanceData.x instanceData.blockLength
            instanceData.encoding instanceData.positive tape slot
            interval)
          outputChunk)
        (ComputationFrameContext regs instanceData frame tape slot interval
          logicalBank) := by
    simpa [ComputationPackedKernelSpecAt,
      NeighborhoodScheduler.fieldModulus,
      NeighborhoodExecutableEvaluation.Residue.fieldModulus] using
      hpacked
  have hbasisSpec :
      BasisKernelSpecAtContext regs basisKernel
        (NeighborhoodExecutableEvaluation.Residue.fieldModulus
          (NeighborhoodExecutableEvaluation.payloadWidth
            tm instanceData.blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount))
        (basisAssignmentValue
          (NeighborhoodExecutableEvaluation.payloadWidth
            tm instanceData.blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount)
          (computationArguments frame logicalBank))
        (ComputationFrameContext regs instanceData frame tape slot interval
          logicalBank) := by
    simpa [ComputationBasisKernelSpecAt,
      NeighborhoodScheduler.fieldModulus,
      NeighborhoodExecutableEvaluation.Residue.fieldModulus] using
      hbasis
  have hmodulusValue :
      store (CombineValue.rangeRegisters regs).modulus =
        NeighborhoodExecutableEvaluation.Residue.fieldModulus
          (NeighborhoodExecutableEvaluation.payloadWidth
            tm instanceData.blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount) := by
    simpa [NeighborhoodScheduler.fieldModulus,
      NeighborhoodExecutableEvaluation.Residue.fieldModulus] using
      hcontext.computation.parameters.modulus_eq
  have hmodulusPred :
      store (CombineValue.rangeRegisters regs).modulusPred =
        NeighborhoodExecutableEvaluation.Residue.fieldModulus
            (NeighborhoodExecutableEvaluation.payloadWidth
              tm instanceData.blockLength)
            (NeighborhoodExecutableEvaluation.graphFanIn
              workTapeCount) -
          1 := by
    simpa [NeighborhoodScheduler.fieldModulus,
      NeighborhoodExecutableEvaluation.Residue.fieldModulus] using
      hcontext.computation.parameters.modulusPred_eq
  simpa only [NeighborhoodExecutableEvaluation.combineResidues] using
    evaluateNode_combineTerm_runsAnyContext_internal
      regs packedKernel basisKernel
      (NeighborhoodExecutableEvaluation.payloadWidth
        tm instanceData.blockLength)
      (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount)
      (NeighborhoodExecutableEvaluation.booleanCombine
        tm instanceData.x instanceData.blockLength
        instanceData.encoding instanceData.positive tape slot interval)
      (computationArguments frame logicalBank)
      outputChunk
      (ComputationFrameContext regs instanceData frame tape slot interval
        logicalBank)
      (fun hcurrent habi hbank =>
        computationFrameContext_transport_internal
          regs instanceData frame tape slot interval logicalBank
          hcurrent habi hbank)
      (computationFrameContext_stableUnderDriverWrites_internal
        regs instanceData frame tape slot interval logicalBank)
      hpackedSpec hbasisSpec store hcontext
      hmodulusValue hmodulusPred hcount

end Internal
end CombineTerm
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
