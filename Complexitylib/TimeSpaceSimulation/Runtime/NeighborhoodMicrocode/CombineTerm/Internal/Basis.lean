/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.CombineTerm.Internal
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.Dispatcher
import Complexitylib.TimeSpaceSimulation.Runtime.Arithmetic
import Complexitylib.TreeEvaluation.CookMertz.GroupedExtension.Evaluation
import Complexitylib.TreeEvaluation.CookMertz.PrimeGrouped.Logarithmic.Decoding

/-!
# Uniform tensor-basis microcode proofs

This internal layer proves the arithmetic, packed-bank, and nested-loop
correctness of the fixed-fan-in tensor-basis command.
-/

open Complexity Complexity.TimeSpaceSimulation TreeEval CookMertz

private theorem test_toBits_add (first second value : ℕ) :
    Nat.toBits (first + second) value =
      Nat.toBits first (value / 2 ^ second) ++ Nat.toBits second value := by
  induction first with
  | zero => simp [Nat.toBits]
  | succ first ih =>
      simp only [Nat.succ_add, Nat.toBits, ih, List.cons_append,
        List.cons.injEq]
      rw [Nat.div_div_eq_div_mul, pow_add, Nat.mul_comm]
      simp

private theorem test_fromBits_slice
    (pre chunk suffix value : ℕ) :
    Nat.fromBits
        (((Nat.toBits (pre + chunk + suffix) value).drop pre).take
          chunk) =
      value / 2 ^ suffix % 2 ^ chunk := by
  rw [show pre + chunk + suffix = pre + (chunk + suffix) by omega,
    test_toBits_add]
  have hdrop :
      (Nat.toBits pre (value / 2 ^ (chunk + suffix)) ++
          Nat.toBits (chunk + suffix) value).drop pre =
        Nat.toBits (chunk + suffix) value := by
    rw [List.drop_append_of_le_length (by simp [Nat.length_toBits])]
    simp [Nat.length_toBits]
  rw [hdrop]
  rw [test_toBits_add]
  have htake :
      (Nat.toBits chunk (value / 2 ^ suffix) ++
          Nat.toBits suffix value).take chunk =
        Nat.toBits chunk (value / 2 ^ suffix) := by
    rw [List.take_append_of_le_length (by simp [Nat.length_toBits])]
    simp [Nat.length_toBits]
  rw [htake, Nat.fromBits_toBits_mod]

private theorem test_chunk_bits_eq_slice
    (payloadWidth fanIn code : ℕ)
    (coordinate :
      Fin fanIn ×
        Fin
          (PrimeGrouped.Logarithmic.chunkCount payloadWidth fanIn)) :
    List.ofFn
        (GroupedExtension.Evaluation.chunkAssignmentOfCode
          finProdFinEquiv
          (PrimeGrouped.Logarithmic.chunkBits payloadWidth fanIn)
          code coordinate) =
      ((Nat.toBits
          ((fanIn *
              PrimeGrouped.Logarithmic.chunkCount payloadWidth fanIn) *
            PrimeGrouped.Logarithmic.chunkBits payloadWidth fanIn)
          code).drop
        (PrimeGrouped.Logarithmic.chunkBits payloadWidth fanIn *
          (finProdFinEquiv coordinate).val)).take
        (PrimeGrouped.Logarithmic.chunkBits payloadWidth fanIn) := by
  let count :=
    fanIn * PrimeGrouped.Logarithmic.chunkCount payloadWidth fanIn
  let bits := PrimeGrouped.Logarithmic.chunkBits payloadWidth fanIn
  let index := (finProdFinEquiv coordinate).val
  have hindex : index < count := (finProdFinEquiv coordinate).isLt
  have hfit : bits * (index + 1) ≤ count * bits := by
    simpa [Nat.succ_eq_add_one, Nat.mul_comm] using
      Nat.mul_le_mul_right bits (Nat.succ_le_iff.mpr hindex)
  simp only [Nat.mul_add] at hfit
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_take, List.length_drop,
      Nat.length_toBits]
    change bits = min bits (count * bits - bits * index)
    rw [min_eq_left]
    omega
  · intro offset hleft hright
    simp only [List.getElem_ofFn]
    rw [List.getElem_take, List.getElem_drop]
    simp [GroupedExtension.Evaluation.chunkAssignmentOfCode,
      BooleanExtension.Evaluation.assignmentOfCode,
      GroupedExtension.Evaluation.bitEncoding, finProdFinEquiv]
    congr 1
    omega

private theorem test_assignment_digit
    (payloadWidth fanIn code : ℕ)
    (coordinate :
      Fin fanIn ×
        Fin
          (PrimeGrouped.Logarithmic.chunkCount payloadWidth fanIn)) :
    PrimeGrouped.Logarithmic.chunkCodeNat
        (GroupedExtension.Evaluation.chunkAssignmentOfCode
          finProdFinEquiv
          (PrimeGrouped.Logarithmic.chunkBits payloadWidth fanIn)
          code coordinate) =
      Complexity.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.CombineTerm.radixDigit
        (PrimeGrouped.Logarithmic.domainSize payloadWidth fanIn)
        code
        (Runtime.NeighborhoodMicrocode.CombineTerm.basisCoordinateDigitIndex
          payloadWidth fanIn coordinate) := by
  let count :=
    fanIn * PrimeGrouped.Logarithmic.chunkCount payloadWidth fanIn
  let bits := PrimeGrouped.Logarithmic.chunkBits payloadWidth fanIn
  let index := (finProdFinEquiv coordinate).val
  have hindex : index < count := (finProdFinEquiv coordinate).isLt
  have hdecomp :
      count * bits =
        bits * index + bits + bits * (count - 1 - index) := by
    have hsplit : index + 1 + (count - (index + 1)) = count :=
      Nat.add_sub_of_le (Nat.succ_le_iff.mpr hindex)
    have htail :
        count - (index + 1) = count - 1 - index := by
      omega
    calc
      count * bits =
          (index + 1 + (count - (index + 1))) * bits := by
            rw [hsplit]
      _ = bits * index + bits + bits * (count - 1 - index) := by
        rw [htail]
        ring
  rw [PrimeGrouped.Logarithmic.chunkCodeNat,
    test_chunk_bits_eq_slice]
  change
    Nat.fromBits
        (((Nat.toBits (count * bits) code).drop (bits * index)).take
          bits) =
      _
  rw [hdecomp, test_fromBits_slice]
  simp [Complexity.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.CombineTerm.radixDigit,
    Runtime.NeighborhoodMicrocode.CombineTerm.basisCoordinateDigitIndex,
    PrimeGrouped.Logarithmic.domainSize, count, bits, index, pow_mul]

private theorem test_chunk_code_of_code
    (bits code : ℕ) (hcode : code < 2 ^ bits) :
    PrimeGrouped.Logarithmic.chunkCodeNat
        (GroupedExtension.Evaluation.chunkOfCode bits code) =
      code := by
  simpa [PrimeGrouped.Logarithmic.chunkCodeNat,
    GroupedExtension.Evaluation.codeOfChunk,
    BooleanExtension.Evaluation.codeOfAssignment] using
    GroupedExtension.Evaluation.codeOfChunk_chunkOfCode hcode

private theorem test_domain_le_modulus (payloadWidth fanIn : ℕ) :
    PrimeGrouped.Logarithmic.domainSize payloadWidth fanIn ≤
      NeighborhoodExecutableEvaluation.Residue.fieldModulus
        payloadWidth fanIn := by
  have hzero :
      PrimeGrouped.Logarithmic.chunkCodeNat
          (GroupedExtension.Evaluation.chunkOfCode
            (PrimeGrouped.Logarithmic.chunkBits payloadWidth fanIn)
            (PrimeGrouped.Logarithmic.domainSize payloadWidth fanIn - 1)) =
        PrimeGrouped.Logarithmic.domainSize payloadWidth fanIn - 1 := by
    apply test_chunk_code_of_code
    exact Nat.sub_lt
      (PrimeGrouped.Logarithmic.domainSize_pos payloadWidth fanIn)
      (by omega)
  have hlt :=
    PrimeGrouped.Logarithmic.Decoding.chunkCodeNat_lt_searchModulus
      payloadWidth fanIn
      (GroupedExtension.Evaluation.chunkOfCode
        (PrimeGrouped.Logarithmic.chunkBits payloadWidth fanIn)
        (PrimeGrouped.Logarithmic.domainSize payloadWidth fanIn - 1))
  rw [hzero] at hlt
  simpa [NeighborhoodExecutableEvaluation.Residue.fieldModulus] using
    (Nat.le_of_pred_lt hlt)

private theorem test_numeric_factor_eq
    (payloadWidth fanIn point other : ℕ)
    (selected :
      GroupedExtension.Chunk
        (PrimeGrouped.Logarithmic.chunkBits payloadWidth fanIn))
    (hother :
      other <
        PrimeGrouped.Logarithmic.domainSize payloadWidth fanIn) :
    Complexity.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.CombineTerm.numericLagrangeFactor
        (NeighborhoodExecutableEvaluation.Residue.fieldModulus
          payloadWidth fanIn)
        (PrimeGrouped.Logarithmic.chunkCodeNat selected)
        other point =
      NeighborhoodExecutableEvaluation.Residue.lagrangeFactor
        payloadWidth fanIn selected
        (GroupedExtension.Evaluation.chunkOfCode
          (PrimeGrouped.Logarithmic.chunkBits payloadWidth fanIn)
          other)
        point := by
  unfold NeighborhoodExecutableEvaluation.Residue.lagrangeFactor
  have hotherCode :
    PrimeGrouped.Logarithmic.chunkCodeNat
        (GroupedExtension.Evaluation.chunkOfCode
          (PrimeGrouped.Logarithmic.chunkBits payloadWidth fanIn)
          other) =
      other :=
    test_chunk_code_of_code _ _ hother
  by_cases hselected :
      selected =
        GroupedExtension.Evaluation.chunkOfCode
          (PrimeGrouped.Logarithmic.chunkBits payloadWidth fanIn)
          other
  · subst selected
    simp [Runtime.NeighborhoodMicrocode.CombineTerm.numericLagrangeFactor,
      hotherCode]
  · have hcodeNe :
        PrimeGrouped.Logarithmic.chunkCodeNat selected ≠ other := by
      intro heq
      apply hselected
      apply PrimeGrouped.Logarithmic.chunkCodeNat_injective
      exact heq.trans hotherCode.symm
    simp [Runtime.NeighborhoodMicrocode.CombineTerm.numericLagrangeFactor,
      hselected, hcodeNe, hotherCode]

namespace Complexity.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.CombineTerm

open RAM Structured

variable {controller : SearchProgram.Registers}

private theorem test_cmdWritesWithin_mono
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

theorem copy_runs_internal
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

private theorem test_numeric_sub
    {modulus first second : ℕ}
    (hfirst : first < modulus) (hsecond : second < modulus) :
    (first + modulus - second) % modulus =
      PrimeField.Runtime.sub modulus first second := by
  simp only [PrimeField.Runtime.sub, PrimeField.Runtime.subInput,
    PrimeField.Runtime.normalize, Nat.mod_eq_of_lt hfirst,
    Nat.mod_eq_of_lt hsecond]

private def test_basisTermFootprint
    (regs : NeighborhoodTrial.Registers controller) : Finset ℕ :=
  {regs.index 4, regs.index 9, regs.index 11, regs.index 20,
    regs.index 29}

private theorem test_basisLagrangeTerm_writesWithin
    (regs : NeighborhoodTrial.Registers controller) :
    RAM.Structured.Footprint.CmdWritesWithin
      (test_basisTermFootprint regs) (basisLagrangeTerm regs) := by
  simp [test_basisTermFootprint, basisLagrangeTerm,
    basisNontrivialFactor, copy, Runtime.inverseMod,
    RuntimeArithmetic.subMod, RuntimeArithmetic.mulMod,
    RuntimeArithmetic.powMod, RuntimeArithmetic.powModBody,
    RuntimeArithmetic.reduce, RuntimeArithmetic.reduceBody,
    RuntimeArithmetic.reduceTestOp,
    basisChunkRangeRegisters, basisDenominatorRegisters,
    basisNumeratorRegisters, basisInverseRegisters,
    basisFactorRegisters, RuntimeArithmetic.PowRegisters.reduceRegisters,
    CombineValue.RangeRegisters.term,
    RuntimeArithmetic.PowRegisters.accumulator,
    RuntimeArithmetic.PowRegisters.test,
    RuntimeArithmetic.PowRegisters.base,
    RuntimeArithmetic.PowRegisters.exponent,
    Cmd.seqList, RAM.Structured.Footprint.CmdWritesWithin,
    RAM.Structured.Footprint.BasicWritesWithin]

private def test_machineLagrangeFactor
    (modulus selected other point : ℕ) : ℕ :=
  if selected = other then
    PrimeField.Runtime.normalize modulus 1
  else
    PrimeField.Runtime.mul modulus
      (PrimeField.Runtime.inverse modulus
        ((selected + modulus - other) % modulus))
      ((point % modulus + modulus - other) % modulus)

private theorem test_machineLagrangeFactor_eq
    {modulus selected other point : ℕ}
    (hselected : selected < modulus) (hother : other < modulus) :
    test_machineLagrangeFactor modulus selected other point =
      numericLagrangeFactor modulus selected other point := by
  unfold test_machineLagrangeFactor numericLagrangeFactor
  by_cases heq : selected = other
  · simp [heq]
  · simp only [heq, ↓reduceIte]
    rw [test_numeric_sub hselected hother]
    have hnumerator :
        (point % modulus + modulus - other) % modulus =
          PrimeField.Runtime.sub modulus point other := by
      simp [PrimeField.Runtime.sub, PrimeField.Runtime.subInput,
        PrimeField.Runtime.normalize, Nat.mod_eq_of_lt hother]
    rw [hnumerator]

private theorem test_basisLagrangeTerm_runs
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store) (modulus selected other point : ℕ)
    (hprime : modulus.Prime)
    (hmodulus :
      store (basisChunkRangeRegisters regs).modulus = modulus)
    (hmodulusPred :
      store (basisChunkRangeRegisters regs).modulusPred =
        modulus - 1)
    (hone :
      store (basisChunkRangeRegisters regs).one = 1)
    (hselected :
      store (CombineValue.rangeRegisters regs).term = selected)
    (hother :
      store (basisChunkRangeRegisters regs).remaining = other)
    (hpoint :
      store (coordinateBankRegisters regs).result = point) :
    ∃ final,
      Runs (basisLagrangeTerm regs) store final ∧
      CombineValue.TermPost (basisChunkRangeRegisters regs)
        (test_machineLagrangeFactor modulus selected other point)
        other store final := by
  let inner := basisChunkRangeRegisters regs
  let selectedCell := (CombineValue.rangeRegisters regs).term
  have hselectedStore : store selectedCell = selected := by
    simpa [selectedCell] using hselected
  have hotherStore : store inner.remaining = other := by
    simpa [inner] using hother
  have hpointStore :
      store (coordinateBankRegisters regs).result = point :=
    hpoint
  have hmodulusStore : store inner.modulus = modulus := by
    simpa [inner] using hmodulus
  have hmodulusPredStore :
      store inner.modulusPred = modulus - 1 := by
    simpa [inner] using hmodulusPred
  have honeStore : store inner.one = 1 := by
    simpa [inner] using hone
  have hselectedAddress : store (regs.index 19) = selected := by
    simpa [CombineValue.rangeRegisters] using hselected
  have hotherAddress : store (regs.index 0) = other := by
    simpa [basisChunkRangeRegisters] using hother
  let firstCopyZero := (Basic.imm (regs.index 4) 0).exec store
  let firstCopy :=
    (Basic.add (regs.index 4) selectedCell (regs.index 4)).exec
      firstCopyZero
  let firstDifference :=
    (Basic.sub (regs.index 4) (regs.index 4) inner.remaining).exec
      firstCopy
  let secondCopyZero := (Basic.imm (regs.index 29) 0).exec
    firstDifference
  let secondCopy :=
    (Basic.add (regs.index 29) inner.remaining (regs.index 29)).exec
      secondCopyZero
  let secondDifference :=
    (Basic.sub (regs.index 29) (regs.index 29) selectedCell).exec
      secondCopy
  let compared :=
    (Basic.add (regs.index 4) (regs.index 4) (regs.index 29)).exec
      secondDifference
  have hprefix :
      Runs
          (Cmd.seqList
            [copy (regs.index 4) selectedCell,
              .basic (.sub (regs.index 4) (regs.index 4)
                inner.remaining),
              copy (regs.index 29) inner.remaining,
              .basic (.sub (regs.index 29) (regs.index 29)
                selectedCell),
              .basic (.add (regs.index 4) (regs.index 4)
                (regs.index 29))])
          store compared := by
    exact
      Runs.seq
        (Runs.seq (Runs.basic _ _) (Runs.basic _ _))
        (Runs.seq (Runs.basic _ _)
          (Runs.seq
            (Runs.seq (Runs.basic _ _) (Runs.basic _ _))
            (Runs.seq (Runs.basic _ _) (Runs.basic _ _))))
  have hcomparedTest :
      compared (regs.index 4) =
        (selected - other) + (other - selected) := by
    simp [compared, secondDifference, secondCopy, secondCopyZero,
      firstDifference, firstCopy, firstCopyZero, Basic.exec,
      selectedCell, inner, basisChunkRangeRegisters,
      CombineValue.rangeRegisters, regs.injective.eq_iff]
    change
      store (regs.index 19) - store (regs.index 0) +
          (store (regs.index 0) - store (regs.index 19)) =
        selected - other + (other - selected)
    rw [hselectedAddress, hotherAddress]
  have hcomparedSelected :
      compared selectedCell = selected := by
    simp [compared, secondDifference, secondCopy, secondCopyZero,
      firstDifference, firstCopy, firstCopyZero, Basic.exec,
      selectedCell, inner, basisChunkRangeRegisters,
      CombineValue.rangeRegisters, regs.injective.eq_iff]
    exact hselected
  have hcomparedOther :
      compared inner.remaining = other := by
    simp [compared, secondDifference, secondCopy, secondCopyZero,
      firstDifference, firstCopy, firstCopyZero, Basic.exec,
      selectedCell, inner, basisChunkRangeRegisters,
      CombineValue.rangeRegisters, regs.injective.eq_iff]
    exact hother
  have hcomparedPoint :
      compared (coordinateBankRegisters regs).result = point := by
    simp [compared, secondDifference, secondCopy, secondCopyZero,
      firstDifference, firstCopy, firstCopyZero, Basic.exec,
      selectedCell, inner, basisChunkRangeRegisters,
      CombineValue.rangeRegisters, coordinateBankRegisters,
      coordinateBankMap, regs.injective.eq_iff]
    exact hpoint
  have hcomparedModulus :
      compared inner.modulus = modulus := by
    simp [compared, secondDifference, secondCopy, secondCopyZero,
      firstDifference, firstCopy, firstCopyZero, Basic.exec,
      selectedCell, inner, basisChunkRangeRegisters,
      CombineValue.rangeRegisters, regs.injective.eq_iff]
    exact hmodulus
  have hcomparedModulusPred :
      compared inner.modulusPred = modulus - 1 := by
    simp [compared, secondDifference, secondCopy, secondCopyZero,
      firstDifference, firstCopy, firstCopyZero, Basic.exec,
      selectedCell, inner, basisChunkRangeRegisters,
      CombineValue.rangeRegisters, regs.injective.eq_iff]
    exact hmodulusPred
  have hcomparedOne :
      compared inner.one = 1 := by
    simp [compared, secondDifference, secondCopy, secondCopyZero,
      firstDifference, firstCopy, firstCopyZero, Basic.exec,
      selectedCell, inner, basisChunkRangeRegisters,
      CombineValue.rangeRegisters, regs.injective.eq_iff]
    exact hone
  have hcomparedPointAddress :
      compared (regs.index 12) = point := by
    simpa [coordinateBankRegisters, coordinateBankMap] using
      hcomparedPoint
  have hcomparedOtherAddress :
      compared (regs.index 0) = other := by
    simpa [inner, basisChunkRangeRegisters] using hcomparedOther
  have hcomparedModulusAddress :
      compared (regs.index 24) = modulus := by
    simpa [inner, basisChunkRangeRegisters] using hcomparedModulus
  have hcomparedPredAddress :
      compared (regs.index 16) = modulus - 1 := by
    simpa [inner, basisChunkRangeRegisters] using
      hcomparedModulusPred
  have hcomparedOneAddress :
      compared (regs.index 17) = 1 := by
    simpa [inner, basisChunkRangeRegisters] using hcomparedOne
  by_cases heq : selected = other
  · have htestZero : compared (regs.index 4) = 0 := by
      rw [hcomparedTest, heq]
      simp
    let final := (Basic.imm inner.term 1).exec compared
    have hbranch :
        Runs
          (.ifZero (regs.index 4)
            (.basic (.imm inner.term 1))
            (basisNontrivialFactor regs))
          compared final :=
      Runs.ifZero htestZero (Runs.basic _ _)
    have hfull :
        Runs (basisLagrangeTerm regs) store final := by
      simpa [basisLagrangeTerm, inner] using
        Runs.seq hprefix hbranch
    refine ⟨final, ?_, ?_⟩
    · exact hfull
    · exact
        { term_eq := by
            simp [final, Basic.exec, inner,
              test_machineLagrangeFactor, heq,
              PrimeField.Runtime.normalize,
              Nat.mod_eq_of_lt hprime.one_lt]
          accumulator_eq :=
            RAM.Structured.Footprint.runs_eq_outside
              (test_basisLagrangeTerm_writesWithin regs) hfull
              (by
                simp [test_basisTermFootprint,
                  basisChunkRangeRegisters, regs.injective.eq_iff])
          remaining_eq :=
            (RAM.Structured.Footprint.runs_eq_outside
              (test_basisLagrangeTerm_writesWithin regs) hfull
              (by
                simp [test_basisTermFootprint,
                  basisChunkRangeRegisters, regs.injective.eq_iff])).trans
              hotherStore
          modulus_eq :=
            RAM.Structured.Footprint.runs_eq_outside
              (test_basisLagrangeTerm_writesWithin regs) hfull
              (by
                simp [test_basisTermFootprint,
                  basisChunkRangeRegisters, regs.injective.eq_iff])
          modulusPred_eq :=
            RAM.Structured.Footprint.runs_eq_outside
              (test_basisLagrangeTerm_writesWithin regs) hfull
              (by
                simp [test_basisTermFootprint,
                  basisChunkRangeRegisters, regs.injective.eq_iff])
          one_eq :=
            RAM.Structured.Footprint.runs_eq_outside
              (test_basisLagrangeTerm_writesWithin regs) hfull
              (by
                simp [test_basisTermFootprint,
                  basisChunkRangeRegisters, regs.injective.eq_iff])
          count_eq :=
            RAM.Structured.Footprint.runs_eq_outside
              (test_basisLagrangeTerm_writesWithin regs) hfull
              (by
                simp [test_basisTermFootprint,
                  basisChunkRangeRegisters, regs.injective.eq_iff]) }
  · have htestNonzero : compared (regs.index 4) ≠ 0 := by
      rw [hcomparedTest]
      omega
    have hdenominatorRun :=
      RuntimeArithmetic.subMod_runs
        (basisDenominatorRegisters regs)
        selectedCell inner.remaining compared modulus hprime.pos
        (regs.injective.ne (by decide))
        (by simpa [inner, basisChunkRangeRegisters] using
          hcomparedModulus)
        (by simpa [inner, basisChunkRangeRegisters] using
          hcomparedModulusPred)
    let denominator := (selected + modulus - other) % modulus
    let afterDenominator :=
      RuntimeArithmetic.reduceResultStore
        (basisDenominatorRegisters regs) denominator compared
    have hdenominatorEq :
        (compared selectedCell + modulus -
            compared inner.remaining) %
            modulus =
          denominator := by
      rw [hcomparedSelected, hcomparedOther]
    rw [hdenominatorEq] at hdenominatorRun
    change
      Runs
        (RuntimeArithmetic.subMod (basisDenominatorRegisters regs)
          selectedCell inner.remaining)
        compared afterDenominator at hdenominatorRun
    have hafterDenominatorModulus :
        afterDenominator (basisInverseRegisters regs).modulus =
          modulus := by
      change afterDenominator (regs.index 24) = modulus
      simp [afterDenominator, RuntimeArithmetic.reduceResultStore,
        basisDenominatorRegisters,
        Function.update, regs.injective.eq_iff,
        hcomparedModulusAddress]
    have hafterDenominatorPred :
        afterDenominator (basisInverseRegisters regs).modulusPred =
          modulus - 1 := by
      change afterDenominator (regs.index 16) = modulus - 1
      simp [afterDenominator, RuntimeArithmetic.reduceResultStore,
        basisDenominatorRegisters,
        Function.update, regs.injective.eq_iff,
        hcomparedPredAddress]
    have hafterDenominatorBase :
        afterDenominator (basisInverseRegisters regs).base =
          denominator := by
      change afterDenominator (regs.index 9) = denominator
      simp [afterDenominator, RuntimeArithmetic.reduceResultStore,
        basisDenominatorRegisters,
        Function.update, regs.injective.eq_iff]
    have hafterDenominatorOne :
        afterDenominator (basisInverseRegisters regs).one = 1 := by
      change afterDenominator (regs.index 17) = 1
      simp [afterDenominator, RuntimeArithmetic.reduceResultStore,
        basisDenominatorRegisters,
        Function.update, regs.injective.eq_iff,
        hcomparedOneAddress]
    have hdenominatorLt : denominator < modulus :=
      Nat.mod_lt _ hprime.pos
    let afterInverse :=
      RuntimeArithmetic.powModResultStore
        (basisInverseRegisters regs)
        (PrimeField.Runtime.inverse modulus denominator)
        afterDenominator
    have hinverseRun :
        Runs (Runtime.inverseMod (basisInverseRegisters regs))
          afterDenominator afterInverse := by
      exact Runtime.inverseMod_runs
        (basisInverseRegisters regs) afterDenominator modulus
        denominator hprime hafterDenominatorModulus
        hafterDenominatorPred hafterDenominatorBase
        hafterDenominatorOne hdenominatorLt
    obtain ⟨afterPointCopy, hpointCopy, hpointCopyValue,
        hpointCopyOutside⟩ :=
    copy_runs_internal (basisNumeratorRegisters regs).value
        (coordinateBankRegisters regs).result afterInverse
        (regs.injective.ne (by decide))
    have hafterInversePoint :
        afterInverse (coordinateBankRegisters regs).result = point := by
      change afterInverse (regs.index 12) = point
      simp [afterInverse, RuntimeArithmetic.powModResultStore,
        basisInverseRegisters, Function.update, regs.injective.eq_iff,
        afterDenominator, RuntimeArithmetic.reduceResultStore,
        basisDenominatorRegisters, hcomparedPointAddress]
    have hpointCopyEq :
        afterPointCopy (basisNumeratorRegisters regs).value = point :=
      hpointCopyValue.trans hafterInversePoint
    have hpointCopyModulus :
        afterPointCopy (basisNumeratorRegisters regs).modulus =
          modulus := by
      change afterPointCopy (regs.index 24) = modulus
      rw [hpointCopyOutside (regs.index 24)
        (regs.injective.ne (by decide))]
      simp [afterInverse, RuntimeArithmetic.powModResultStore,
        basisInverseRegisters,
        Function.update, regs.injective.eq_iff,
        afterDenominator, RuntimeArithmetic.reduceResultStore,
        basisDenominatorRegisters, hcomparedModulusAddress]
    have hpointCopyPred :
        afterPointCopy (basisNumeratorRegisters regs).modulusPred =
          modulus - 1 := by
      change afterPointCopy (regs.index 16) = modulus - 1
      rw [hpointCopyOutside (regs.index 16)
        (regs.injective.ne (by decide))]
      simp [afterInverse, RuntimeArithmetic.powModResultStore,
        basisInverseRegisters,
        Function.update, regs.injective.eq_iff,
        afterDenominator, RuntimeArithmetic.reduceResultStore,
        basisDenominatorRegisters, hcomparedPredAddress]
    have hpointCopyOther :
        afterPointCopy (regs.index 0) = other := by
      rw [hpointCopyOutside (regs.index 0)
        (regs.injective.ne (by decide))]
      simp [afterInverse, RuntimeArithmetic.powModResultStore,
        basisInverseRegisters, Function.update, regs.injective.eq_iff,
        afterDenominator, RuntimeArithmetic.reduceResultStore,
        basisDenominatorRegisters, hcomparedOtherAddress]
    have hpointCopyModulusAddress :
        afterPointCopy (regs.index 24) = modulus := by
      simpa [basisNumeratorRegisters] using hpointCopyModulus
    have hpointCopyPredAddress :
        afterPointCopy (regs.index 16) = modulus - 1 := by
      simpa [basisNumeratorRegisters] using hpointCopyPred
    let afterPointReduce :=
      RuntimeArithmetic.reduceResultStore
        (basisNumeratorRegisters regs) (point % modulus)
        afterPointCopy
    have hpointReduce :
        Runs (RuntimeArithmetic.reduce (basisNumeratorRegisters regs))
          afterPointCopy afterPointReduce := by
      exact RuntimeArithmetic.reduce_runs
        (basisNumeratorRegisters regs) afterPointCopy modulus point
        hprime.pos hpointCopyEq hpointCopyModulus hpointCopyPred
    have hafterPointOther :
        afterPointReduce inner.remaining = other := by
      change afterPointReduce (regs.index 0) = other
      simp [afterPointReduce, RuntimeArithmetic.reduceResultStore,
        basisNumeratorRegisters,
        Function.update, regs.injective.eq_iff, hpointCopyOther]
    have hafterPointModulus :
        afterPointReduce (basisNumeratorRegisters regs).modulus =
          modulus := by
      change afterPointReduce (regs.index 24) = modulus
      simp [afterPointReduce, RuntimeArithmetic.reduceResultStore,
        basisNumeratorRegisters, Function.update,
        regs.injective.eq_iff, hpointCopyModulusAddress]
    have hafterPointPred :
        afterPointReduce (basisNumeratorRegisters regs).modulusPred =
          modulus - 1 := by
      change afterPointReduce (regs.index 16) = modulus - 1
      simp [afterPointReduce, RuntimeArithmetic.reduceResultStore,
        basisNumeratorRegisters, Function.update,
        regs.injective.eq_iff, hpointCopyPredAddress]
    have hnumeratorRun :=
      RuntimeArithmetic.subMod_runs
        (basisNumeratorRegisters regs)
        (basisNumeratorRegisters regs).value inner.remaining
        afterPointReduce modulus hprime.pos
        (regs.injective.ne (by decide))
        hafterPointModulus hafterPointPred
    let numerator := (point % modulus + modulus - other) % modulus
    have hnumeratorEq :
        (afterPointReduce (basisNumeratorRegisters regs).value +
            modulus - afterPointReduce inner.remaining) %
            modulus =
          numerator := by
      have hvalue :
          afterPointReduce (basisNumeratorRegisters regs).value =
            point % modulus := by
        change afterPointReduce (regs.index 11) = point % modulus
        simp [afterPointReduce,
          RuntimeArithmetic.reduceResultStore,
          basisNumeratorRegisters, Function.update,
          regs.injective.eq_iff]
      rw [hvalue, hafterPointOther]
    rw [hnumeratorEq] at hnumeratorRun
    let afterNumerator :=
      RuntimeArithmetic.reduceResultStore
        (basisNumeratorRegisters regs) numerator afterPointReduce
    change
      Runs
        (RuntimeArithmetic.subMod (basisNumeratorRegisters regs)
          (basisNumeratorRegisters regs).value inner.remaining)
        afterPointReduce afterNumerator at hnumeratorRun
    let inverseValue := PrimeField.Runtime.inverse modulus denominator
    have hafterNumeratorInverse :
        afterNumerator (basisInverseRegisters regs).accumulator =
          inverseValue := by
      change afterNumerator (regs.index 20) = inverseValue
      simp [afterNumerator, RuntimeArithmetic.reduceResultStore,
        basisNumeratorRegisters, afterPointReduce,
        RuntimeArithmetic.reduceResultStore,
        regs.injective.eq_iff]
      rw [hpointCopyOutside (regs.index 20)
        (regs.injective.ne (by decide))]
      simp [inverseValue, afterInverse,
        RuntimeArithmetic.powModResultStore,
        basisInverseRegisters, Function.update,
        regs.injective.eq_iff]
    have hafterNumeratorNumerator :
        afterNumerator (basisNumeratorRegisters regs).value =
          numerator := by
      change afterNumerator (regs.index 11) = numerator
      simp [afterNumerator, RuntimeArithmetic.reduceResultStore,
        basisNumeratorRegisters, Function.update,
        regs.injective.eq_iff]
    have hafterNumeratorModulus :
        afterNumerator (basisFactorRegisters regs).modulus =
          modulus := by
      change afterNumerator (regs.index 24) = modulus
      simp [afterNumerator, RuntimeArithmetic.reduceResultStore,
        basisNumeratorRegisters, afterPointReduce,
        RuntimeArithmetic.reduceResultStore, Function.update,
        regs.injective.eq_iff, hpointCopyModulusAddress]
    have hafterNumeratorPred :
        afterNumerator (basisFactorRegisters regs).modulusPred =
          modulus - 1 := by
      change afterNumerator (regs.index 16) = modulus - 1
      simp [afterNumerator, RuntimeArithmetic.reduceResultStore,
        basisNumeratorRegisters, afterPointReduce,
        RuntimeArithmetic.reduceResultStore, Function.update,
        regs.injective.eq_iff, hpointCopyPredAddress]
    have hfactorRun :=
      RuntimeArithmetic.mulMod_runs (basisFactorRegisters regs)
        (basisInverseRegisters regs).accumulator
        (basisNumeratorRegisters regs).value afterNumerator modulus
        hprime.pos hafterNumeratorModulus hafterNumeratorPred
    let factor :=
      PrimeField.Runtime.mul modulus inverseValue numerator
    have hfactorEq :
        (afterNumerator (basisInverseRegisters regs).accumulator *
            afterNumerator (basisNumeratorRegisters regs).value) %
            modulus =
          factor := by
      rw [hafterNumeratorInverse, hafterNumeratorNumerator]
      simp [factor, PrimeField.Runtime.mul,
        PrimeField.Runtime.mulInput, PrimeField.Runtime.normalize]
    rw [hfactorEq] at hfactorRun
    let final :=
      RuntimeArithmetic.reduceResultStore
        (basisFactorRegisters regs) factor afterNumerator
    change
      Runs
        (RuntimeArithmetic.mulMod (basisFactorRegisters regs)
          (basisInverseRegisters regs).accumulator
          (basisNumeratorRegisters regs).value)
        afterNumerator final at hfactorRun
    have hnontrivial :
        Runs (basisNontrivialFactor regs) compared final := by
      simpa [basisNontrivialFactor, Cmd.seqList] using
        Runs.seq hdenominatorRun
          (Runs.seq hinverseRun
            (Runs.seq hpointCopy
              (Runs.seq hpointReduce
                (Runs.seq hnumeratorRun hfactorRun))))
    have hbranch :
        Runs
          (.ifZero (regs.index 4)
            (.basic (.imm inner.term 1))
            (basisNontrivialFactor regs))
          compared final :=
      Runs.ifNonzero htestNonzero hnontrivial
    have hfull :
        Runs (basisLagrangeTerm regs) store final := by
      simpa [basisLagrangeTerm, inner] using
        Runs.seq hprefix hbranch
    refine ⟨final, ?_, ?_⟩
    · exact hfull
    · exact
        { term_eq := by
            change final (regs.index 20) =
              test_machineLagrangeFactor modulus selected other point
            simp [final, RuntimeArithmetic.reduceResultStore,
              basisFactorRegisters, factor, inverseValue,
              denominator, numerator, test_machineLagrangeFactor,
              heq,
              PrimeField.Runtime.mul,
              PrimeField.Runtime.mulInput,
              PrimeField.Runtime.normalize,
              Nat.mod_eq_of_lt
                (PrimeField.Runtime.inverse_lt hprime.pos),
              Nat.mod_eq_of_lt
                (Nat.mod_lt _ hprime.pos),
              Function.update, regs.injective.eq_iff]
          accumulator_eq :=
            RAM.Structured.Footprint.runs_eq_outside
              (test_basisLagrangeTerm_writesWithin regs) hfull
              (by
                simp [test_basisTermFootprint,
                  basisChunkRangeRegisters, regs.injective.eq_iff])
          remaining_eq :=
            (RAM.Structured.Footprint.runs_eq_outside
              (test_basisLagrangeTerm_writesWithin regs) hfull
              (by
                simp [test_basisTermFootprint,
                  basisChunkRangeRegisters, regs.injective.eq_iff])).trans
              hotherStore
          modulus_eq :=
            RAM.Structured.Footprint.runs_eq_outside
              (test_basisLagrangeTerm_writesWithin regs) hfull
              (by
                simp [test_basisTermFootprint,
                  basisChunkRangeRegisters, regs.injective.eq_iff])
          modulusPred_eq :=
            RAM.Structured.Footprint.runs_eq_outside
              (test_basisLagrangeTerm_writesWithin regs) hfull
              (by
                simp [test_basisTermFootprint,
                  basisChunkRangeRegisters, regs.injective.eq_iff])
          one_eq :=
            RAM.Structured.Footprint.runs_eq_outside
              (test_basisLagrangeTerm_writesWithin regs) hfull
              (by
                simp [test_basisTermFootprint,
                  basisChunkRangeRegisters, regs.injective.eq_iff])
          count_eq :=
            RAM.Structured.Footprint.runs_eq_outside
              (test_basisLagrangeTerm_writesWithin regs) hfull
              (by
                simp [test_basisTermFootprint,
                  basisChunkRangeRegisters, regs.injective.eq_iff]) }

private theorem test_fold_range_congr
    (op : CombineValue.FoldOp) (modulus : ℕ)
    (first second : ℕ → ℕ) (count : ℕ)
    (heq : ∀ index, index < count → first index = second index) :
    CombineValue.FoldOp.range op modulus first count =
      CombineValue.FoldOp.range op modulus second count := by
  suffices
      ∀ accumulator,
        CombineValue.FoldOp.fold op modulus first count accumulator =
          CombineValue.FoldOp.fold op modulus second count accumulator by
    exact this _
  induction count with
  | zero =>
      intro accumulator
      rfl
  | succ count ih =>
      intro accumulator
      simp only [CombineValue.FoldOp.fold]
      rw [heq count (by omega)]
      apply ih
      intro index hindex
      exact heq index (by omega)

theorem chunkRange_eq_internal
    (payloadWidth fanIn point : ℕ)
    (selected :
      GroupedExtension.Chunk
        (PrimeGrouped.Logarithmic.chunkBits payloadWidth fanIn)) :
    CombineValue.FoldOp.range .mul
        (NeighborhoodExecutableEvaluation.Residue.fieldModulus
          payloadWidth fanIn)
        (fun other =>
          test_machineLagrangeFactor
            (NeighborhoodExecutableEvaluation.Residue.fieldModulus
              payloadWidth fanIn)
            (PrimeGrouped.Logarithmic.chunkCodeNat selected)
            other point)
        (PrimeGrouped.Logarithmic.domainSize payloadWidth fanIn) =
      NeighborhoodExecutableEvaluation.Residue.chunkBasisValue
        payloadWidth fanIn selected point := by
  let modulus :=
    NeighborhoodExecutableEvaluation.Residue.fieldModulus
      payloadWidth fanIn
  let count := PrimeGrouped.Logarithmic.domainSize payloadWidth fanIn
  have hcountLe : count ≤ modulus :=
    test_domain_le_modulus payloadWidth fanIn
  have hselectedLt :
      PrimeGrouped.Logarithmic.chunkCodeNat selected < modulus := by
    exact
      PrimeGrouped.Logarithmic.Decoding.chunkCodeNat_lt_searchModulus
        payloadWidth fanIn selected
  calc
    CombineValue.FoldOp.range .mul modulus
        (fun other =>
          test_machineLagrangeFactor modulus
            (PrimeGrouped.Logarithmic.chunkCodeNat selected)
            other point)
        count =
      CombineValue.FoldOp.range .mul modulus
        (fun other =>
          numericLagrangeFactor modulus
            (PrimeGrouped.Logarithmic.chunkCodeNat selected)
            other point)
        count := by
          apply test_fold_range_congr
          intro other hother
          exact test_machineLagrangeFactor_eq hselectedLt
            (lt_of_lt_of_le hother hcountLe)
    _ =
      CombineValue.FoldOp.range .mul modulus
        (fun other =>
          NeighborhoodExecutableEvaluation.Residue.lagrangeFactor
            payloadWidth fanIn selected
            (GroupedExtension.Evaluation.chunkOfCode
              (PrimeGrouped.Logarithmic.chunkBits payloadWidth fanIn)
              other)
            point)
        count := by
          apply test_fold_range_congr
          intro other hother
          exact test_numeric_factor_eq payloadWidth fanIn point
            other selected hother
    _ =
      NeighborhoodExecutableEvaluation.Residue.productRange modulus
        (fun other =>
          NeighborhoodExecutableEvaluation.Residue.lagrangeFactor
            payloadWidth fanIn selected
            (GroupedExtension.Evaluation.chunkOfCode
              (PrimeGrouped.Logarithmic.chunkBits payloadWidth fanIn)
              other)
            point)
        count :=
      CombineValue.fold_mul_eq_productRange modulus _ count
    _ =
      NeighborhoodExecutableEvaluation.Residue.chunkBasisValue
        payloadWidth fanIn selected point := rfl

theorem basisChunkRange_runs_internal
    (regs : NeighborhoodTrial.Registers controller)
    (payloadWidth fanIn : ℕ)
    (selected :
      GroupedExtension.Chunk
        (PrimeGrouped.Logarithmic.chunkBits payloadWidth fanIn))
    (point : ℕ) (store : Store)
    (hmodulus :
      store (basisChunkRangeRegisters regs).modulus =
        NeighborhoodExecutableEvaluation.Residue.fieldModulus
          payloadWidth fanIn)
    (hmodulusPred :
      store (basisChunkRangeRegisters regs).modulusPred =
        NeighborhoodExecutableEvaluation.Residue.fieldModulus
            payloadWidth fanIn -
          1)
    (hcount :
      store (basisChunkRangeRegisters regs).count =
        PrimeGrouped.Logarithmic.domainSize payloadWidth fanIn)
    (hselected :
      store (CombineValue.rangeRegisters regs).term =
        PrimeGrouped.Logarithmic.chunkCodeNat selected)
    (hpoint :
      store (coordinateBankRegisters regs).result = point) :
    ∃ final,
      Runs
          (CombineValue.rangeFold .mul
            (basisChunkRangeRegisters regs)
            (basisLagrangeTerm regs))
          store final ∧
      CombineValue.RangePost .mul
        (basisChunkRangeRegisters regs)
        (NeighborhoodExecutableEvaluation.Residue.fieldModulus
          payloadWidth fanIn)
        (PrimeGrouped.Logarithmic.domainSize payloadWidth fanIn)
        (fun other =>
          test_machineLagrangeFactor
            (NeighborhoodExecutableEvaluation.Residue.fieldModulus
              payloadWidth fanIn)
            (PrimeGrouped.Logarithmic.chunkCodeNat selected)
            other point)
        store final ∧
      final (CombineValue.rangeRegisters regs).term =
          PrimeGrouped.Logarithmic.chunkCodeNat selected ∧
      final (coordinateBankRegisters regs).result = point := by
  let inner := basisChunkRangeRegisters regs
  let modulus :=
    NeighborhoodExecutableEvaluation.Residue.fieldModulus
      payloadWidth fanIn
  let context : Store → Prop :=
    fun current =>
      current (CombineValue.rangeRegisters regs).term =
          PrimeGrouped.Logarithmic.chunkCodeNat selected ∧
        current (coordinateBankRegisters regs).result = point
  have hstable :
      CombineValue.StableUnderDriverWrites inner context := by
    intro initial final hcontext houtside
    exact
      ⟨(houtside (CombineValue.rangeRegisters regs).term
          (by
            simp [inner, CombineValue.RangeRegisters.driverWriteFootprint,
              basisChunkRangeRegisters, CombineValue.rangeRegisters,
              regs.injective.eq_iff])).trans hcontext.1,
        (houtside (coordinateBankRegisters regs).result
          (by
            simp [inner, CombineValue.RangeRegisters.driverWriteFootprint,
              basisChunkRangeRegisters, coordinateBankRegisters,
              coordinateBankMap, regs.injective.eq_iff])).trans
          hcontext.2⟩
  have hterm :
      CombineValue.TermKernelSpecAtContext inner
        (basisLagrangeTerm regs) modulus
        (fun other =>
          test_machineLagrangeFactor modulus
            (PrimeGrouped.Logarithmic.chunkCodeNat selected)
            other point)
        context := by
    intro current other hcontext hremaining hcurrentModulus
      hcurrentPred hone
    obtain ⟨final, hrun, hpost⟩ :=
      test_basisLagrangeTerm_runs regs current modulus
        (PrimeGrouped.Logarithmic.chunkCodeNat selected)
        other point
        (PrimeField.Search.searchModulus_prime _)
        hcurrentModulus hcurrentPred hone hcontext.1
        hremaining hcontext.2
    refine ⟨final, hrun, hpost, ?_⟩
    have htermPreserved :
        final (CombineValue.rangeRegisters regs).term =
          current (CombineValue.rangeRegisters regs).term :=
      RAM.Structured.Footprint.runs_eq_outside
        (test_basisLagrangeTerm_writesWithin regs) hrun
        (by
          simp [test_basisTermFootprint,
            CombineValue.rangeRegisters, regs.injective.eq_iff])
    have hpointPreserved :
        final (coordinateBankRegisters regs).result =
          current (coordinateBankRegisters regs).result :=
      RAM.Structured.Footprint.runs_eq_outside
        (test_basisLagrangeTerm_writesWithin regs) hrun
        (by
          simp [test_basisTermFootprint,
            coordinateBankRegisters, coordinateBankMap,
            regs.injective.eq_iff])
    exact
      ⟨htermPreserved.trans hcontext.1,
        hpointPreserved.trans hcontext.2⟩
  obtain ⟨final, hrun, hpost, hfinalContext⟩ :=
    CombineValue.rangeFold_runsAtContext .mul inner
      (basisLagrangeTerm regs)
      (fun other =>
        test_machineLagrangeFactor modulus
          (PrimeGrouped.Logarithmic.chunkCodeNat selected)
          other point)
      store modulus
      (PrimeGrouped.Logarithmic.domainSize payloadWidth fanIn)
      context hstable hterm
      (CombineValue.fieldModulus_pos payloadWidth fanIn)
      (by simpa [inner, modulus] using hmodulus)
      (by simpa [inner, modulus] using hmodulusPred)
      (by simpa [inner] using hcount)
      ⟨hselected, hpoint⟩
  exact ⟨final, hrun, hpost, hfinalContext⟩

private theorem test_combineScratch_mem
    (regs : NeighborhoodTrial.Registers controller) (slot : Fin 19) :
    regs.index (CombineValue.combineScratchMap slot) ∈
      CombineValue.combineScratchFootprint regs :=
  Finset.mem_image.mpr ⟨slot, Finset.mem_univ _, rfl⟩

private theorem test_readResidueCoordinate_combine_writesWithin
    (regs : NeighborhoodTrial.Registers controller) :
    RAM.Structured.Footprint.CmdWritesWithin
      (CombineValue.combineScratchFootprint regs)
      (readResidueCoordinate regs) := by
  have h0 := test_combineScratch_mem regs (0 : Fin 19)
  change regs.index 0 ∈ CombineValue.combineScratchFootprint regs at h0
  have h1 := test_combineScratch_mem regs (1 : Fin 19)
  change regs.index 1 ∈ CombineValue.combineScratchFootprint regs at h1
  have h4 := test_combineScratch_mem regs (2 : Fin 19)
  change regs.index 4 ∈ CombineValue.combineScratchFootprint regs at h4
  have h5 := test_combineScratch_mem regs (3 : Fin 19)
  change regs.index 5 ∈ CombineValue.combineScratchFootprint regs at h5
  have h9 := test_combineScratch_mem regs (5 : Fin 19)
  change regs.index 9 ∈ CombineValue.combineScratchFootprint regs at h9
  have h10 := test_combineScratch_mem regs (6 : Fin 19)
  change regs.index 10 ∈ CombineValue.combineScratchFootprint regs at h10
  have h11 := test_combineScratch_mem regs (7 : Fin 19)
  change regs.index 11 ∈ CombineValue.combineScratchFootprint regs at h11
  have h12 := test_combineScratch_mem regs (8 : Fin 19)
  change regs.index 12 ∈ CombineValue.combineScratchFootprint regs at h12
  have h17 := test_combineScratch_mem regs (9 : Fin 19)
  change regs.index 17 ∈ CombineValue.combineScratchFootprint regs at h17
  have h31 := test_combineScratch_mem regs (16 : Fin 19)
  change regs.index 31 ∈ CombineValue.combineScratchFootprint regs at h31
  have h33 := test_combineScratch_mem regs (18 : Fin 19)
  change regs.index 33 ∈ CombineValue.combineScratchFootprint regs at h33
  simp [readResidueCoordinate, copy, NeighborhoodProgram.bankRead,
    NeighborhoodProgram.bankSeek, NeighborhoodProgram.bankRestore,
    NeighborhoodProgram.bankRestoreBody,
    NeighborhoodProgram.bankForward,
    NeighborhoodProgram.bankForwardBody,
    NeighborhoodProgram.peek, NeighborhoodProgram.pop,
    NeighborhoodProgram.popBody, NeighborhoodProgram.popTestOp,
    NeighborhoodProgram.push,
    RuntimeArithmetic.reduce, RuntimeArithmetic.reduceBody,
    RuntimeArithmetic.reduceTestOp,
    NeighborhoodProgram.BankRegisters.word,
    NeighborhoodProgram.BankRegisters.buffer,
    NeighborhoodProgram.BankRegisters.basePred,
    NeighborhoodProgram.BankRegisters.quotient,
    NeighborhoodProgram.BankRegisters.test,
    NeighborhoodProgram.BankRegisters.value,
    NeighborhoodProgram.BankRegisters.indexCount,
    NeighborhoodProgram.BankRegisters.completed,
    NeighborhoodProgram.BankRegisters.result,
    NeighborhoodProgram.StackRegisters.word,
    NeighborhoodProgram.StackRegisters.quotient,
    NeighborhoodProgram.StackRegisters.test,
    NeighborhoodProgram.StackRegisters.value,
    NeighborhoodProgram.StackRegisters.reduceRegisters,
    coordinateBankRegisters, coordinateBankMap,
    savedRangeCount, coordinateIndex,
    CombineValue.rangeRegisters,
    CombineValue.combineScratchFootprint,
    CombineValue.combineScratchMap,
    Cmd.seqList, RAM.Structured.Footprint.CmdWritesWithin,
    RAM.Structured.Footprint.BasicWritesWithin] at *
  aesop

theorem basisChunkRange_writesWithin_internal
    (regs : NeighborhoodTrial.Registers controller) :
    RAM.Structured.Footprint.CmdWritesWithin
      (CombineValue.combineScratchFootprint regs)
      (CombineValue.rangeFold .mul
        (basisChunkRangeRegisters regs)
        (basisLagrangeTerm regs)) := by
  have h0 := test_combineScratch_mem regs (0 : Fin 19)
  change regs.index 0 ∈ CombineValue.combineScratchFootprint regs at h0
  have h4 := test_combineScratch_mem regs (2 : Fin 19)
  change regs.index 4 ∈ CombineValue.combineScratchFootprint regs at h4
  have h5 := test_combineScratch_mem regs (3 : Fin 19)
  change regs.index 5 ∈ CombineValue.combineScratchFootprint regs at h5
  have h9 := test_combineScratch_mem regs (5 : Fin 19)
  change regs.index 9 ∈ CombineValue.combineScratchFootprint regs at h9
  have h11 := test_combineScratch_mem regs (7 : Fin 19)
  change regs.index 11 ∈ CombineValue.combineScratchFootprint regs at h11
  have h17 := test_combineScratch_mem regs (9 : Fin 19)
  change regs.index 17 ∈ CombineValue.combineScratchFootprint regs at h17
  have h20 := test_combineScratch_mem regs (12 : Fin 19)
  change regs.index 20 ∈ CombineValue.combineScratchFootprint regs at h20
  have h29 := test_combineScratch_mem regs (14 : Fin 19)
  change regs.index 29 ∈ CombineValue.combineScratchFootprint regs at h29
  have h31 := test_combineScratch_mem regs (16 : Fin 19)
  change regs.index 31 ∈ CombineValue.combineScratchFootprint regs at h31
  have hterm :
      RAM.Structured.Footprint.CmdWritesWithin
        (CombineValue.combineScratchFootprint regs)
        (basisLagrangeTerm regs) := by
    exact
      test_cmdWritesWithin_mono
        (show test_basisTermFootprint regs ⊆
            CombineValue.combineScratchFootprint regs by
          intro address haddress
          simp only [test_basisTermFootprint, Finset.mem_insert,
            Finset.mem_singleton] at haddress
          rcases haddress with haddress | haddress | haddress |
              haddress | haddress <;>
            subst address <;> assumption)
        _ (test_basisLagrangeTerm_writesWithin regs)
  simp [CombineValue.rangeFold, CombineValue.initializeFold,
    CombineValue.rangeFoldFrom, CombineValue.foldBody,
    CombineValue.foldCommand, CombineValue.copy,
    RuntimeArithmetic.mulMod, RuntimeArithmetic.reduce,
    RuntimeArithmetic.reduceBody, RuntimeArithmetic.reduceTestOp,
    CombineValue.RangeRegisters.reduceRegisters,
    CombineValue.RangeRegisters.one,
    CombineValue.RangeRegisters.remaining,
    CombineValue.RangeRegisters.accumulator,
    CombineValue.RangeRegisters.test,
    basisChunkRangeRegisters,
    Cmd.seqList, RAM.Structured.Footprint.CmdWritesWithin,
    RAM.Structured.Footprint.BasicWritesWithin]
  exact
    ⟨⟨h17, h0, h31, h5, h31, h5⟩,
      h0, hterm, h31, h5, h31, h5⟩

def basisChunkFootprint
    (regs : NeighborhoodTrial.Registers controller) : Finset ℕ :=
  {regs.index 0, regs.index 4, regs.index 5, regs.index 9,
    regs.index 11, regs.index 17, regs.index 20, regs.index 29,
    regs.index 31}

theorem basisChunkRange_precise_writesWithin_internal
    (regs : NeighborhoodTrial.Registers controller) :
    RAM.Structured.Footprint.CmdWritesWithin
      (basisChunkFootprint regs)
      (CombineValue.rangeFold .mul
        (basisChunkRangeRegisters regs)
        (basisLagrangeTerm regs)) := by
  have h0 : regs.index 0 ∈ basisChunkFootprint regs := by
    simp [basisChunkFootprint]
  have h5 : regs.index 5 ∈ basisChunkFootprint regs := by
    simp [basisChunkFootprint]
  have h17 : regs.index 17 ∈ basisChunkFootprint regs := by
    simp [basisChunkFootprint]
  have h31 : regs.index 31 ∈ basisChunkFootprint regs := by
    simp [basisChunkFootprint]
  have hterm :
      RAM.Structured.Footprint.CmdWritesWithin
        (basisChunkFootprint regs)
        (basisLagrangeTerm regs) := by
    exact
      test_cmdWritesWithin_mono
        (show test_basisTermFootprint regs ⊆
            basisChunkFootprint regs by
          intro address haddress
          simp only [test_basisTermFootprint, Finset.mem_insert,
            Finset.mem_singleton] at haddress
          rcases haddress with haddress | haddress | haddress |
              haddress | haddress <;>
            subst address <;> simp [basisChunkFootprint])
        _ (test_basisLagrangeTerm_writesWithin regs)
  simp [CombineValue.rangeFold, CombineValue.initializeFold,
    CombineValue.rangeFoldFrom, CombineValue.foldBody,
    CombineValue.foldCommand, CombineValue.copy,
    RuntimeArithmetic.mulMod, RuntimeArithmetic.reduce,
    RuntimeArithmetic.reduceBody, RuntimeArithmetic.reduceTestOp,
    CombineValue.RangeRegisters.reduceRegisters,
    CombineValue.RangeRegisters.one,
    CombineValue.RangeRegisters.remaining,
    CombineValue.RangeRegisters.accumulator,
    CombineValue.RangeRegisters.test,
    basisChunkRangeRegisters,
    Cmd.seqList, RAM.Structured.Footprint.CmdWritesWithin,
    RAM.Structured.Footprint.BasicWritesWithin]
  exact
    ⟨⟨h17, h0, h31, h5, h31, h5⟩,
      h0, hterm, h31, h5, h31, h5⟩

theorem basisAccumulatorMul_writesWithin_internal
    (regs : NeighborhoodTrial.Registers controller) :
    RAM.Structured.Footprint.CmdWritesWithin
      (CombineValue.combineScratchFootprint regs)
      (RuntimeArithmetic.mulMod (basisAccumulatorRegisters regs)
        (basisChunkRangeRegisters regs).accumulator
        (basisValue regs)) := by
  have h4 := test_combineScratch_mem regs (2 : Fin 19)
  change regs.index 4 ∈ CombineValue.combineScratchFootprint regs at h4
  have h32 := test_combineScratch_mem regs (17 : Fin 19)
  change regs.index 32 ∈ CombineValue.combineScratchFootprint regs at h32
  simp [RuntimeArithmetic.mulMod, RuntimeArithmetic.reduce,
    RuntimeArithmetic.reduceBody, RuntimeArithmetic.reduceTestOp,
    basisAccumulatorRegisters, basisValue,
    RAM.Structured.Footprint.CmdWritesWithin,
    RAM.Structured.Footprint.BasicWritesWithin]
  exact ⟨h32, h4, h32, h4⟩

def basisAccumulatorFootprint
    (regs : NeighborhoodTrial.Registers controller) : Finset ℕ :=
  {regs.index 4, basisValue regs}

theorem basisAccumulatorMul_precise_writesWithin_internal
    (regs : NeighborhoodTrial.Registers controller) :
    RAM.Structured.Footprint.CmdWritesWithin
      (basisAccumulatorFootprint regs)
      (RuntimeArithmetic.mulMod (basisAccumulatorRegisters regs)
        (basisChunkRangeRegisters regs).accumulator
        (basisValue regs)) := by
  have h4 : regs.index 4 ∈ basisAccumulatorFootprint regs := by
    simp [basisAccumulatorFootprint]
  have h32 : basisValue regs ∈
      basisAccumulatorFootprint regs := by
    simp [basisAccumulatorFootprint]
  simp [RuntimeArithmetic.mulMod, RuntimeArithmetic.reduce,
    RuntimeArithmetic.reduceBody, RuntimeArithmetic.reduceTestOp,
    basisAccumulatorRegisters,
    RAM.Structured.Footprint.CmdWritesWithin,
    RAM.Structured.Footprint.BasicWritesWithin]
  exact ⟨h32, h4, h32, h4⟩

theorem productRange_lt_internal
    {modulus : ℕ} (hmodulus : 0 < modulus)
    (term : ℕ → ℕ) (count : ℕ) :
    NeighborhoodExecutableEvaluation.Residue.productRange
        modulus term count <
      modulus := by
  suffices
      ∀ accumulator, accumulator < modulus →
        NeighborhoodExecutableEvaluation.Residue.foldProduct
            modulus term count accumulator <
          modulus by
    exact this _ (PrimeField.Runtime.normalize_lt hmodulus)
  induction count with
  | zero =>
      intro accumulator haccumulator
      exact haccumulator
  | succ count ih =>
      intro accumulator _
      exact ih _ (PrimeField.Runtime.mul_lt hmodulus)

private theorem test_context_transport
    {tm : TM workTapeCount}
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (tape : TapeIndex workTapeCount)
    (slot : NeighborhoodGraph.Slot)
    (interval : ℕ)
    (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    {command : Cmd} {initial final : Store}
    (hcontext :
      ComputationContext regs instanceData tape slot interval
        logicalBank initial)
    (hwrites :
      RAM.Structured.Footprint.CmdWritesWithin
        (CombineValue.combineScratchFootprint regs) command)
    (hrun : Runs command initial final)
    (hbank :
      final regs.layout.bank = initial regs.layout.bank) :
    ComputationContext regs instanceData tape slot interval
      logicalBank final := by
  exact
    Internal.computationContext_transport_internal
      regs instanceData tape slot interval logicalBank hcontext
      (CombineValue.preservesABI_of_combineScratch regs hwrites hrun)
      hbank

theorem frameContext_transport_combineScratch_internal
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
    {command : Cmd} {initial final : Store}
    (hcontext :
      ComputationFrameContext regs instanceData frame tape slot interval
        logicalBank initial)
    (hwrites :
      RAM.Structured.Footprint.CmdWritesWithin
        (CombineValue.combineScratchFootprint regs) command)
    (hrun : Runs command initial final)
    (hbank :
      final regs.layout.bank = initial regs.layout.bank) :
    ComputationFrameContext regs instanceData frame tape slot interval
      logicalBank final := by
  exact
    Internal.computationFrameContext_transport_internal
      regs instanceData frame tape slot interval logicalBank hcontext
      (CombineValue.preservesABI_of_combineScratch regs hwrites hrun)
      hbank

/-
set_option maxHeartbeats 0 in
theorem test_basisCoordinate_runs
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
    (coordinate :
      Fin (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount) ×
        Fin
          (PrimeGrouped.Logarithmic.chunkCount
            (NeighborhoodExecutableEvaluation.payloadWidth
              tm instanceData.blockLength)
            (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount)))
    (store : Store) (code accumulator : ℕ)
    (hcontext :
      ComputationContext regs instanceData tape slot interval
        logicalBank store)
    (hremaining :
      store (CombineValue.rangeRegisters regs).remaining = code)
    (_hmodulus :
      store (CombineValue.rangeRegisters regs).modulus =
        NeighborhoodScheduler.fieldModulus instanceData)
    (_hmodulusPred :
      store (CombineValue.rangeRegisters regs).modulusPred =
        NeighborhoodScheduler.fieldModulus instanceData - 1)
    (hone :
      store (CombineValue.rangeRegisters regs).one = 1)
    (haccumulator : store (basisValue regs) = accumulator) :
    ∃ final,
      Runs
          (basisCoordinateCommand regs
            (NeighborhoodExecutableEvaluation.payloadWidth
              tm instanceData.blockLength)
            (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount)
            (NeighborhoodProgram.residueBankIndex
              tm instanceData.blockLength
              (frame.childTarget coordinate.1) coordinate.2)
            coordinate)
          store final ∧
      BasisPost regs
        (PrimeField.Runtime.mul
          (NeighborhoodScheduler.fieldModulus instanceData)
          (NeighborhoodExecutableEvaluation.Residue.chunkBasisValue
            (NeighborhoodExecutableEvaluation.payloadWidth
              tm instanceData.blockLength)
            (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount)
            (GroupedExtension.Evaluation.chunkAssignmentOfCode
              finProdFinEquiv
              (PrimeGrouped.Logarithmic.chunkBits
                (NeighborhoodExecutableEvaluation.payloadWidth
                  tm instanceData.blockLength)
                (NeighborhoodExecutableEvaluation.graphFanIn
                  workTapeCount))
              code coordinate)
            (computationArguments frame logicalBank coordinate.1
              coordinate.2))
          accumulator)
        code store final ∧
      ComputationContext regs instanceData tape slot interval
        logicalBank final := by
  let payloadWidth :=
    NeighborhoodExecutableEvaluation.payloadWidth
      tm instanceData.blockLength
  let fanIn :=
    NeighborhoodExecutableEvaluation.graphFanIn workTapeCount
  let modulus := NeighborhoodScheduler.fieldModulus instanceData
  let radix :=
    PrimeGrouped.Logarithmic.domainSize payloadWidth fanIn
  let inner := basisChunkRangeRegisters regs
  let digitIndex :=
    basisCoordinateDigitIndex payloadWidth fanIn coordinate
  let bankCoordinate :=
    NeighborhoodProgram.residueBankIndex
      tm instanceData.blockLength
      (frame.childTarget coordinate.1) coordinate.2
  let selected :=
    GroupedExtension.Evaluation.chunkAssignmentOfCode
      finProdFinEquiv
      (PrimeGrouped.Logarithmic.chunkBits payloadWidth fanIn)
      code coordinate
  let point :=
    computationArguments frame logicalBank coordinate.1 coordinate.2
  have hmodulusPos : 0 < modulus := by
    simpa [modulus, NeighborhoodScheduler.fieldModulus] using
      CombineValue.fieldModulus_pos payloadWidth fanIn
  have hradixPos : 0 < radix := by
    exact PrimeGrouped.Logarithmic.domainSize_pos payloadWidth fanIn
  have hradixEq :
      Representation.digitBase instanceData = radix := by
    unfold Representation.digitBase CandidateParameters.domainSize
    rw [← Representation.payloadWidth_eq_booleanWidth instanceData]
    rfl
  have hradixValue :
      store (Layout.chunkRadix regs) = radix :=
    hcontext.parameters.digitBase_eq.trans hradixEq
  have h30 := test_combineScratch_mem regs (15 : Fin 19)
  change assignmentDigitIndex regs ∈
    CombineValue.combineScratchFootprint regs at h30
  have hdigitIndexWrites :
      RAM.Structured.Footprint.CmdWritesWithin
        (CombineValue.combineScratchFootprint regs)
        (.basic (.imm (assignmentDigitIndex regs) digitIndex)) := by
    simpa [RAM.Structured.Footprint.CmdWritesWithin,
      RAM.Structured.Footprint.BasicWritesWithin] using h30
  let afterDigitIndex :=
    (Basic.imm (assignmentDigitIndex regs) digitIndex).exec store
  have hdigitIndexRun :
      Runs (.basic (.imm (assignmentDigitIndex regs) digitIndex))
        store afterDigitIndex :=
    Runs.basic _ _
  have hafterDigitIndex :
      afterDigitIndex (assignmentDigitIndex regs) = digitIndex := by
    simp [afterDigitIndex, Basic.exec]
  have hafterDigitRemaining :
      afterDigitIndex
          (CombineValue.rangeRegisters regs).remaining =
        code := by
    rw [show afterDigitIndex
        (CombineValue.rangeRegisters regs).remaining =
          store (CombineValue.rangeRegisters regs).remaining by
      simp [afterDigitIndex, Basic.exec, assignmentDigitIndex,
        CombineValue.rangeRegisters, regs.injective.eq_iff]]
    exact hremaining
  have hafterDigitRadix :
      afterDigitIndex (Layout.chunkRadix regs) = radix := by
    simp [afterDigitIndex, Basic.exec, assignmentDigitIndex,
      Layout.chunkRadix, NeighborhoodTrial.Registers.layout,
      regs.injective.eq_iff, hradixValue]
  have hafterDigitOne :
      afterDigitIndex (CombineValue.rangeRegisters regs).one = 1 := by
    rw [show afterDigitIndex
        (CombineValue.rangeRegisters regs).one =
          store (CombineValue.rangeRegisters regs).one by
      simp [afterDigitIndex, Basic.exec, assignmentDigitIndex,
        CombineValue.rangeRegisters, regs.injective.eq_iff]]
    exact hone
  have hafterDigitBank :
      afterDigitIndex regs.layout.bank = store regs.layout.bank := by
    change afterDigitIndex (regs.index 33) = store (regs.index 33)
    simp [afterDigitIndex, Basic.exec, assignmentDigitIndex,
      regs.injective.eq_iff]
  have hafterDigitContext :
      ComputationContext regs instanceData tape slot interval
        logicalBank afterDigitIndex :=
    test_context_transport regs instanceData tape slot interval
      logicalBank hcontext hdigitIndexWrites hdigitIndexRun
      hafterDigitBank
  obtain
    ⟨afterAssignment, hassignment, hassignmentPost, _⟩ :=
      assignmentDigit_runs regs afterDigitIndex radix code digitIndex
        hradixPos hafterDigitRemaining hafterDigitIndex
        hafterDigitRadix hafterDigitOne
  have hassignmentBank :
      afterAssignment regs.layout.bank =
        afterDigitIndex regs.layout.bank := by
    apply RAM.Structured.Footprint.runs_eq_outside
      (assignmentDigit_precise_writesWithin regs) hassignment
    change regs.index 33 ∉
      (assignmentDigitRegisters regs).writeFootprint
    simp [DigitRegisters.writeFootprint, assignmentDigitRegisters,
      regs.injective.eq_iff]
  have hassignmentContext :
      ComputationContext regs instanceData tape slot interval
        logicalBank afterAssignment :=
    test_context_transport regs instanceData tape slot interval
      logicalBank hafterDigitContext
      (assignmentDigit_writesWithin regs) hassignment hassignmentBank
  have hassignmentBasis :
      afterAssignment (basisValue regs) =
        afterDigitIndex (basisValue regs) := by
    apply RAM.Structured.Footprint.runs_eq_outside
      (assignmentDigit_precise_writesWithin regs) hassignment
    change regs.index 32 ∉
      (assignmentDigitRegisters regs).writeFootprint
    simp [DigitRegisters.writeFootprint, assignmentDigitRegisters,
      regs.injective.eq_iff]
  let afterCoordinate :=
    (Basic.imm (coordinateIndex regs) bankCoordinate).exec
      afterAssignment
  have hcoordinateRun :
      Runs (.basic (.imm (coordinateIndex regs) bankCoordinate))
        afterAssignment afterCoordinate :=
    Runs.basic _ _
  have hcoordinateWrites :
      RAM.Structured.Footprint.CmdWritesWithin
        (CombineValue.combineScratchFootprint regs)
        (.basic (.imm (coordinateIndex regs) bankCoordinate)) := by
    simpa [coordinateIndex,
      RAM.Structured.Footprint.CmdWritesWithin,
      RAM.Structured.Footprint.BasicWritesWithin] using h30
  have hcoordinateValue :
      afterCoordinate (coordinateIndex regs) = bankCoordinate := by
    simp [afterCoordinate, Basic.exec]
  have hcoordinateOne :
      afterCoordinate (CombineValue.rangeRegisters regs).one = 1 := by
    rw [show afterCoordinate
        (CombineValue.rangeRegisters regs).one =
          afterAssignment (CombineValue.rangeRegisters regs).one by
      simp [afterCoordinate, Basic.exec, coordinateIndex,
        CombineValue.rangeRegisters, regs.injective.eq_iff]]
    exact hassignmentPost.one_eq.trans hafterDigitOne
  have hcoordinateBank :
      afterCoordinate regs.layout.bank =
        afterAssignment regs.layout.bank := by
    change afterCoordinate (regs.index 33) =
      afterAssignment (regs.index 33)
    simp [afterCoordinate, Basic.exec, coordinateIndex,
      regs.injective.eq_iff]
  have hcoordinateContext :
      ComputationContext regs instanceData tape slot interval
        logicalBank afterCoordinate :=
    test_context_transport regs instanceData tape slot interval
      logicalBank hassignmentContext hcoordinateWrites
      hcoordinateRun hcoordinateBank
  obtain ⟨afterRead, hread, hreadPost, hreadContext⟩ :=
    readResidueCoordinate_runs regs instanceData tape slot interval
      logicalBank (frame.childTarget coordinate.1) coordinate.2
      afterCoordinate hcoordinateContext hcoordinateValue
      hcoordinateOne
  have hreadTerm :
      afterRead (CombineValue.rangeRegisters regs).term =
        afterCoordinate (CombineValue.rangeRegisters regs).term := by
    apply RAM.Structured.Footprint.runs_eq_outside
      (readResidueCoordinate_writesWithin regs) hread
    simp [coordinateReadFootprint,
      NeighborhoodProgram.BankRegisters.footprint,
      coordinateBankRegisters, coordinateBankMap,
      CombineValue.rangeRegisters, savedRangeCount,
      regs.injective.eq_iff]
    decide
  have hreadBasis :
      afterRead (basisValue regs) =
        afterCoordinate (basisValue regs) := by
    apply RAM.Structured.Footprint.runs_eq_outside
      (readResidueCoordinate_writesWithin regs) hread
    simp [coordinateReadFootprint,
      NeighborhoodProgram.BankRegisters.footprint,
      coordinateBankRegisters, coordinateBankMap,
      CombineValue.rangeRegisters, savedRangeCount, basisValue,
      regs.injective.eq_iff]
    decide
  have h1 := test_combineScratch_mem regs (1 : Fin 19)
  change inner.count ∈
    CombineValue.combineScratchFootprint regs at h1
  have hcountWrites :
      RAM.Structured.Footprint.CmdWritesWithin
        (CombineValue.combineScratchFootprint regs)
        (.basic (.imm inner.count radix)) := by
    simpa [RAM.Structured.Footprint.CmdWritesWithin,
      RAM.Structured.Footprint.BasicWritesWithin] using h1
  let afterCount := (Basic.imm inner.count radix).exec afterRead
  have hcountRun :
      Runs (.basic (.imm inner.count radix)) afterRead afterCount :=
    Runs.basic _ _
  have hcountValue : afterCount inner.count = radix := by
    simp [afterCount, Basic.exec]
  have hcountBank :
      afterCount regs.layout.bank = afterRead regs.layout.bank := by
    change afterCount (regs.index 33) = afterRead (regs.index 33)
    simp [afterCount, Basic.exec, inner, basisChunkRangeRegisters,
      regs.injective.eq_iff]
  have hcountContext :
      ComputationContext regs instanceData tape slot interval
        logicalBank afterCount :=
    test_context_transport regs instanceData tape slot interval
      logicalBank hreadContext hcountWrites hcountRun hcountBank
  have hcountModulus :
      afterCount inner.modulus = modulus := by
    simpa [inner, basisChunkRangeRegisters, modulus,
      CombineValue.rangeRegisters] using
      hcountContext.parameters.modulus_eq
  have hcountModulusPred :
      afterCount inner.modulusPred = modulus - 1 := by
    simpa [inner, basisChunkRangeRegisters, modulus,
      CombineValue.rangeRegisters] using
      hcountContext.parameters.modulusPred_eq
  have hcountSelected :
      afterCount (CombineValue.rangeRegisters regs).term =
        PrimeGrouped.Logarithmic.chunkCodeNat selected := by
    rw [show afterCount (CombineValue.rangeRegisters regs).term =
        afterRead (CombineValue.rangeRegisters regs).term by
      simp [afterCount, Basic.exec, inner, basisChunkRangeRegisters,
        CombineValue.rangeRegisters, regs.injective.eq_iff]]
    rw [hreadTerm]
    rw [show afterCoordinate
        (CombineValue.rangeRegisters regs).term =
          afterAssignment
            (CombineValue.rangeRegisters regs).term by
      simp [afterCoordinate, Basic.exec, coordinateIndex,
        CombineValue.rangeRegisters, regs.injective.eq_iff]]
    rw [hassignmentPost.term_eq]
    exact
      (test_assignment_digit payloadWidth fanIn code coordinate).symm
  have hcountPoint :
      afterCount (coordinateBankRegisters regs).result = point := by
    rw [show afterCount (coordinateBankRegisters regs).result =
        afterRead (coordinateBankRegisters regs).result by
      simp [afterCount, Basic.exec, inner, basisChunkRangeRegisters,
        coordinateBankRegisters, coordinateBankMap,
        regs.injective.eq_iff]]
    exact hreadPost.result_eq
  obtain ⟨afterRange, hrange, hrangePost, hselectedRange,
      hpointRange⟩ :=
    test_basisChunkRange_runs regs payloadWidth fanIn selected point
      afterCount hcountModulus hcountModulusPred hcountValue
      hcountSelected hcountPoint
  have hrangeBank :
      afterRange regs.layout.bank = afterCount regs.layout.bank := by
    apply RAM.Structured.Footprint.runs_eq_outside
      (test_basisChunkRange_precise_writesWithin regs) hrange
    change regs.index 33 ∉ test_basisChunkFootprint regs
    simp [test_basisChunkFootprint, regs.injective.eq_iff]
  have hrangeContext :
      ComputationContext regs instanceData tape slot interval
        logicalBank afterRange :=
    test_context_transport regs instanceData tape slot interval
      logicalBank hcountContext
      (test_basisChunkRange_writesWithin regs) hrange hrangeBank
  have hrangeOutside :
      ∀ address, address ∉ test_basisChunkFootprint regs →
        afterRange address = afterCount address := by
    intro address haddress
    exact RAM.Structured.Footprint.runs_eq_outside
      (test_basisChunkRange_precise_writesWithin regs) hrange
      haddress
  have hassignmentPacked :
      afterAssignment (packedValue regs) =
        afterDigitIndex (packedValue regs) := by
    apply RAM.Structured.Footprint.runs_eq_outside
      (assignmentDigit_precise_writesWithin regs) hassignment
    change regs.index 6 ∉
      (assignmentDigitRegisters regs).writeFootprint
    simp [DigitRegisters.writeFootprint, assignmentDigitRegisters,
      regs.injective.eq_iff]
  have hreadPacked :
      afterRead (packedValue regs) =
        afterCoordinate (packedValue regs) := by
    apply RAM.Structured.Footprint.runs_eq_outside
      (readResidueCoordinate_writesWithin regs) hread
    simp [coordinateReadFootprint,
      NeighborhoodProgram.BankRegisters.footprint,
      coordinateBankRegisters, coordinateBankMap,
      CombineValue.rangeRegisters, savedRangeCount, packedValue,
      regs.injective.eq_iff]
    decide
  have hcountPacked :
      afterCount (packedValue regs) = store (packedValue regs) := by
    calc
      afterCount (packedValue regs) =
          afterRead (packedValue regs) := by
        simp [afterCount, Basic.exec, inner,
          basisChunkRangeRegisters, packedValue,
          regs.injective.eq_iff]
      _ = afterCoordinate (packedValue regs) := hreadPacked
      _ = afterAssignment (packedValue regs) := by
        simp [afterCoordinate, Basic.exec, coordinateIndex,
          packedValue, regs.injective.eq_iff]
      _ = afterDigitIndex (packedValue regs) :=
        hassignmentPacked
      _ = store (packedValue regs) := by
        simp [afterDigitIndex, Basic.exec, assignmentDigitIndex,
          packedValue, regs.injective.eq_iff]
  have hcountAccumulator :
      afterCount (CombineValue.rangeRegisters regs).accumulator =
        store (CombineValue.rangeRegisters regs).accumulator := by
    calc
      afterCount (CombineValue.rangeRegisters regs).accumulator =
          afterRead
            (CombineValue.rangeRegisters regs).accumulator := by
        simp [afterCount, Basic.exec, inner,
          basisChunkRangeRegisters, CombineValue.rangeRegisters,
          regs.injective.eq_iff]
      _ = afterCoordinate
          (CombineValue.rangeRegisters regs).accumulator :=
        hreadPost.accumulator_eq
      _ = afterAssignment
          (CombineValue.rangeRegisters regs).accumulator := by
        simp [afterCoordinate, Basic.exec, coordinateIndex,
          CombineValue.rangeRegisters, regs.injective.eq_iff]
      _ = afterDigitIndex
          (CombineValue.rangeRegisters regs).accumulator :=
        hassignmentPost.accumulator_eq
      _ = store
          (CombineValue.rangeRegisters regs).accumulator := by
        simp [afterDigitIndex, Basic.exec, assignmentDigitIndex,
          CombineValue.rangeRegisters, regs.injective.eq_iff]
  have hcountRemaining :
      afterCount (CombineValue.rangeRegisters regs).remaining =
        code := by
    calc
      afterCount (CombineValue.rangeRegisters regs).remaining =
          afterRead (CombineValue.rangeRegisters regs).remaining := by
        simp [afterCount, Basic.exec, inner,
          basisChunkRangeRegisters, CombineValue.rangeRegisters,
          regs.injective.eq_iff]
      _ = afterCoordinate
          (CombineValue.rangeRegisters regs).remaining :=
        hreadPost.remaining_eq
      _ = afterAssignment
          (CombineValue.rangeRegisters regs).remaining := by
        simp [afterCoordinate, Basic.exec, coordinateIndex,
          CombineValue.rangeRegisters, regs.injective.eq_iff]
      _ = code := hassignmentPost.remaining_eq
  have hcountOuterCount :
      afterCount (CombineValue.rangeRegisters regs).count =
        store (CombineValue.rangeRegisters regs).count := by
    calc
      afterCount (CombineValue.rangeRegisters regs).count =
          afterRead (CombineValue.rangeRegisters regs).count := by
        simp [afterCount, Basic.exec, inner,
          basisChunkRangeRegisters, CombineValue.rangeRegisters,
          regs.injective.eq_iff]
      _ = afterCoordinate
          (CombineValue.rangeRegisters regs).count :=
        hreadPost.count_eq
      _ = afterAssignment
          (CombineValue.rangeRegisters regs).count := by
        simp [afterCoordinate, Basic.exec, coordinateIndex,
          CombineValue.rangeRegisters, regs.injective.eq_iff]
      _ = afterDigitIndex
          (CombineValue.rangeRegisters regs).count :=
        hassignmentPost.count_eq
      _ = store (CombineValue.rangeRegisters regs).count := by
        simp [afterDigitIndex, Basic.exec, assignmentDigitIndex,
          CombineValue.rangeRegisters, regs.injective.eq_iff]
  have hcountBasis :
      afterCount (basisValue regs) = accumulator := by
    calc
      afterCount (basisValue regs) = afterRead (basisValue regs) := by
        simp [afterCount, Basic.exec, inner,
          basisChunkRangeRegisters, basisValue,
          regs.injective.eq_iff]
      _ = afterCoordinate (basisValue regs) := hreadBasis
      _ = afterAssignment (basisValue regs) := by
        simp [afterCoordinate, Basic.exec, coordinateIndex,
          basisValue, regs.injective.eq_iff]
      _ = afterDigitIndex (basisValue regs) := hassignmentBasis
      _ = store (basisValue regs) := by
        simp [afterDigitIndex, Basic.exec, assignmentDigitIndex,
          basisValue, regs.injective.eq_iff]
      _ = accumulator := haccumulator
  have hrangeBasis :
      afterRange (basisValue regs) = accumulator := by
    rw [hrangeOutside (basisValue regs)
      (by
        simp [test_basisChunkFootprint, basisValue,
          regs.injective.eq_iff])]
    exact hcountBasis
  have hrangePacked :
      afterRange (packedValue regs) = store (packedValue regs) := by
    rw [hrangeOutside (packedValue regs)
      (by
        simp [test_basisChunkFootprint, packedValue,
          regs.injective.eq_iff])]
    exact hcountPacked
  have hrangeAccumulator :
      afterRange
          (CombineValue.rangeRegisters regs).accumulator =
        store (CombineValue.rangeRegisters regs).accumulator := by
    rw [hrangeOutside
      (CombineValue.rangeRegisters regs).accumulator
      (by
        simp [test_basisChunkFootprint,
          CombineValue.rangeRegisters, regs.injective.eq_iff])]
    exact hcountAccumulator
  have hrangeRemaining :
      afterRange (CombineValue.rangeRegisters regs).remaining =
        code := by
    rw [hrangeOutside (CombineValue.rangeRegisters regs).remaining
      (by
        simp [test_basisChunkFootprint,
          CombineValue.rangeRegisters, regs.injective.eq_iff])]
    exact hcountRemaining
  have hrangeOuterCount :
      afterRange (CombineValue.rangeRegisters regs).count =
        store (CombineValue.rangeRegisters regs).count := by
    rw [hrangeOutside (CombineValue.rangeRegisters regs).count
      (by
        simp [test_basisChunkFootprint,
          CombineValue.rangeRegisters, regs.injective.eq_iff])]
    exact hcountOuterCount
  have hchunkValue :
      afterRange inner.accumulator =
        NeighborhoodExecutableEvaluation.Residue.chunkBasisValue
          payloadWidth fanIn selected point :=
    hrangePost.accumulator_eq.trans
      (test_chunk_range_eq payloadWidth fanIn point selected)
  have hchunkLt :
      NeighborhoodExecutableEvaluation.Residue.chunkBasisValue
          payloadWidth fanIn selected point <
        modulus := by
    unfold NeighborhoodExecutableEvaluation.Residue.chunkBasisValue
    simpa [modulus, NeighborhoodScheduler.fieldModulus] using
      test_productRange_lt
        (modulus := modulus) hmodulusPos
        (fun code =>
          NeighborhoodExecutableEvaluation.Residue.lagrangeFactor
            payloadWidth fanIn selected
            (GroupedExtension.Evaluation.chunkOfCode
              (PrimeGrouped.Logarithmic.chunkBits payloadWidth fanIn)
              code)
            point)
        radix
  have hmulModulus :
      afterRange (basisAccumulatorRegisters regs).modulus =
        modulus := by
    simpa [basisAccumulatorRegisters, inner, modulus,
      NeighborhoodScheduler.fieldModulus] using
      hrangePost.modulus_eq
  have hmulModulusPred :
      afterRange (basisAccumulatorRegisters regs).modulusPred =
        modulus - 1 := by
    simpa [basisAccumulatorRegisters, inner, modulus,
      NeighborhoodScheduler.fieldModulus] using
      hrangePost.modulusPred_eq
  let product :=
    PrimeField.Runtime.mul modulus
      (NeighborhoodExecutableEvaluation.Residue.chunkBasisValue
        payloadWidth fanIn selected point)
      accumulator
  have hproductEq :
      (afterRange inner.accumulator *
          afterRange (basisValue regs)) %
          modulus =
        product := by
    rw [hchunkValue, hrangeBasis]
    simp [product, PrimeField.Runtime.mul,
      PrimeField.Runtime.mulInput, PrimeField.Runtime.normalize,
      Nat.mod_eq_of_lt hchunkLt]
  have hmul :=
    RuntimeArithmetic.mulMod_runs (basisAccumulatorRegisters regs)
      inner.accumulator (basisValue regs) afterRange modulus
      hmodulusPos hmulModulus hmulModulusPred
  rw [hproductEq] at hmul
  let final :=
    RuntimeArithmetic.reduceResultStore
      (basisAccumulatorRegisters regs) product afterRange
  change
    Runs
      (RuntimeArithmetic.mulMod (basisAccumulatorRegisters regs)
        inner.accumulator (basisValue regs))
      afterRange final at hmul
  have hmulOutside :
      ∀ address, address ∉ test_basisAccumulatorFootprint regs →
        final address = afterRange address := by
    intro address haddress
    exact RAM.Structured.Footprint.runs_eq_outside
      (test_basisAccumulatorMul_precise_writesWithin regs) hmul
      haddress
  have hmulBank :
      final regs.layout.bank = afterRange regs.layout.bank := by
    apply hmulOutside
    change regs.index 33 ∉ test_basisAccumulatorFootprint regs
    simp [test_basisAccumulatorFootprint, basisValue,
      regs.injective.eq_iff]
  have hfinalContext :
      ComputationContext regs instanceData tape slot interval
        logicalBank final :=
    test_context_transport regs instanceData tape slot interval
      logicalBank hrangeContext
      (test_basisAccumulatorMul_writesWithin regs) hmul hmulBank
  have hrun :
      Runs
          (basisCoordinateCommand regs payloadWidth fanIn
            bankCoordinate coordinate)
          store final := by
    have hprepare :
        Runs
          (basisCoordinatePrepare regs payloadWidth fanIn
            bankCoordinate coordinate)
          store afterCount := by
      simpa [basisCoordinatePrepare, Cmd.seqList, inner, digitIndex,
        bankCoordinate, radix] using
        Runs.seq hdigitIndexRun
          (Runs.seq hassignment
            (Runs.seq hcoordinateRun
              (Runs.seq hread hcountRun)))
    simpa [basisCoordinateCommand, inner] using
      Runs.seq hprepare (Runs.seq hrange hmul)
  refine ⟨final, ?_, ?_, hfinalContext⟩
  · simpa [payloadWidth, fanIn, bankCoordinate] using hrun
  · exact
      { basis_eq := by
          change final (basisAccumulatorRegisters regs).value = _
          rw [show final (basisAccumulatorRegisters regs).value =
              product by
            simp [final, RuntimeArithmetic.reduceResultStore,
              (basisAccumulatorRegisters regs).value_ne_test]]
        packed_eq :=
          (hmulOutside (packedValue regs)
            (by
              simp [test_basisAccumulatorFootprint, packedValue,
                basisValue, regs.injective.eq_iff])).trans
            hrangePacked
        accumulator_eq :=
          (hmulOutside
            (CombineValue.rangeRegisters regs).accumulator
            (by
              simp [test_basisAccumulatorFootprint,
                CombineValue.rangeRegisters, basisValue,
                regs.injective.eq_iff])).trans
            hrangeAccumulator
        remaining_eq :=
          (hmulOutside
            (CombineValue.rangeRegisters regs).remaining
            (by
              simp [test_basisAccumulatorFootprint,
                CombineValue.rangeRegisters, basisValue,
                regs.injective.eq_iff])).trans
            hrangeRemaining
        modulus_eq :=
          (hmulOutside
            (CombineValue.rangeRegisters regs).modulus
            (by
              simp [test_basisAccumulatorFootprint,
                CombineValue.rangeRegisters, basisValue,
                regs.injective.eq_iff])).trans
            (by
              simpa [inner, basisChunkRangeRegisters,
                CombineValue.rangeRegisters, modulus] using
                hrangePost.modulus_eq.trans hmodulus.symm)
        modulusPred_eq :=
          (hmulOutside
            (CombineValue.rangeRegisters regs).modulusPred
            (by
              simp [test_basisAccumulatorFootprint,
                CombineValue.rangeRegisters, basisValue,
                regs.injective.eq_iff])).trans
            (by
              simpa [inner, basisChunkRangeRegisters,
                CombineValue.rangeRegisters, modulus] using
                hrangePost.modulusPred_eq.trans hmodulusPred.symm)
        one_eq :=
          (hmulOutside
            (CombineValue.rangeRegisters regs).one
            (by
              simp [test_basisAccumulatorFootprint,
                CombineValue.rangeRegisters, basisValue,
                regs.injective.eq_iff])).trans
            (by
              simpa [inner, basisChunkRangeRegisters,
                CombineValue.rangeRegisters] using
                hrangePost.one_eq.trans hone.symm)
        count_eq :=
          (hmulOutside
            (CombineValue.rangeRegisters regs).count
            (by
              simp [test_basisAccumulatorFootprint,
                CombineValue.rangeRegisters, basisValue,
                regs.injective.eq_iff])).trans
            hrangeOuterCount }

/-
private theorem test_foldrMul_lt
    {modulus : ℕ} (hmodulus : 0 < modulus)
    (values : List ℕ) (accumulator : ℕ)
    (haccumulator : accumulator < modulus) :
    values.foldr (PrimeField.Runtime.mul modulus) accumulator <
      modulus := by
  induction values with
  | nil => exact haccumulator
  | cons value values ih =>
      simp only [List.foldr]
      exact PrimeField.Runtime.mul_lt hmodulus

theorem test_basisCoordinateFold_runs
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
    (coordinates :
      List
        (Fin
            (NeighborhoodExecutableEvaluation.graphFanIn
              workTapeCount) ×
          Fin
            (PrimeGrouped.Logarithmic.chunkCount
              (NeighborhoodExecutableEvaluation.payloadWidth
                tm instanceData.blockLength)
              (NeighborhoodExecutableEvaluation.graphFanIn
                workTapeCount))))
    (store : Store) (code accumulator : ℕ)
    (hcontext :
      ComputationContext regs instanceData tape slot interval
        logicalBank store)
    (hremaining :
      store (CombineValue.rangeRegisters regs).remaining = code)
    (hmodulus :
      store (CombineValue.rangeRegisters regs).modulus =
        NeighborhoodScheduler.fieldModulus instanceData)
    (hmodulusPred :
      store (CombineValue.rangeRegisters regs).modulusPred =
        NeighborhoodScheduler.fieldModulus instanceData - 1)
    (hone :
      store (CombineValue.rangeRegisters regs).one = 1)
    (haccumulator : store (basisValue regs) = accumulator) :
    ∃ final,
      Runs
          (basisCoordinateFold regs
            (NeighborhoodExecutableEvaluation.payloadWidth
              tm instanceData.blockLength)
            (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount)
            (fun coordinate =>
              NeighborhoodProgram.residueBankIndex
                tm instanceData.blockLength
                (frame.childTarget coordinate.1) coordinate.2)
            coordinates)
          store final ∧
      BasisPost regs
        ((coordinates.map fun coordinate =>
          NeighborhoodExecutableEvaluation.Residue.chunkBasisValue
            (NeighborhoodExecutableEvaluation.payloadWidth
              tm instanceData.blockLength)
            (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount)
            (GroupedExtension.Evaluation.chunkAssignmentOfCode
              finProdFinEquiv
              (PrimeGrouped.Logarithmic.chunkBits
                (NeighborhoodExecutableEvaluation.payloadWidth
                  tm instanceData.blockLength)
                (NeighborhoodExecutableEvaluation.graphFanIn
                  workTapeCount))
              code coordinate)
            (computationArguments frame logicalBank coordinate.1
              coordinate.2)).foldr
          (PrimeField.Runtime.mul
            (NeighborhoodScheduler.fieldModulus instanceData))
          accumulator)
        code store final ∧
      ComputationContext regs instanceData tape slot interval
        logicalBank final := by
  induction coordinates generalizing store accumulator with
  | nil =>
      refine ⟨store, ?_, ?_, hcontext⟩
      · simpa [basisCoordinateFold] using Runs.skip store
      · exact
          { basis_eq := by simpa using haccumulator
            packed_eq := rfl
            accumulator_eq := rfl
            remaining_eq := hremaining
            modulus_eq := rfl
            modulusPred_eq := rfl
            one_eq := rfl
            count_eq := rfl }
  | cons coordinate coordinates ih =>
      let modulus := NeighborhoodScheduler.fieldModulus instanceData
      let values :=
        coordinates.map fun current =>
          NeighborhoodExecutableEvaluation.Residue.chunkBasisValue
            (NeighborhoodExecutableEvaluation.payloadWidth
              tm instanceData.blockLength)
            (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount)
            (GroupedExtension.Evaluation.chunkAssignmentOfCode
              finProdFinEquiv
              (PrimeGrouped.Logarithmic.chunkBits
                (NeighborhoodExecutableEvaluation.payloadWidth
                  tm instanceData.blockLength)
                (NeighborhoodExecutableEvaluation.graphFanIn
                  workTapeCount))
              code current)
            (computationArguments frame logicalBank current.1
              current.2)
      let tailValue :=
        values.foldr (PrimeField.Runtime.mul modulus) accumulator
      obtain ⟨afterTail, htailRun, htailPost, htailContext⟩ :=
        ih store accumulator hcontext hremaining hmodulus
          hmodulusPred hone haccumulator
      obtain ⟨final, hcoordinateRun, hcoordinatePost,
          hfinalContext⟩ :=
        test_basisCoordinate_runs regs instanceData frame tape slot
          interval logicalBank coordinate afterTail code tailValue
          htailContext htailPost.remaining_eq
          (htailPost.modulus_eq.trans hmodulus)
          (htailPost.modulusPred_eq.trans hmodulusPred)
          (htailPost.one_eq.trans hone)
          (by
            simpa [tailValue, values, modulus] using
              htailPost.basis_eq)
      refine ⟨final, ?_, ?_, hfinalContext⟩
      · simpa [basisCoordinateFold] using
          Runs.seq htailRun hcoordinateRun
      · exact
          { basis_eq := by
              simpa [tailValue, values, modulus] using
                hcoordinatePost.basis_eq
            packed_eq :=
              hcoordinatePost.packed_eq.trans htailPost.packed_eq
            accumulator_eq :=
              hcoordinatePost.accumulator_eq.trans
                htailPost.accumulator_eq
            remaining_eq := hcoordinatePost.remaining_eq
            modulus_eq :=
              hcoordinatePost.modulus_eq.trans htailPost.modulus_eq
            modulusPred_eq :=
              hcoordinatePost.modulusPred_eq.trans
                htailPost.modulusPred_eq
            one_eq :=
              hcoordinatePost.one_eq.trans htailPost.one_eq
            count_eq :=
              hcoordinatePost.count_eq.trans htailPost.count_eq }
-/
-/

private theorem runtimeDigitIndex_eq
    (payloadWidth fanIn : ℕ)
    (child : Fin fanIn)
    (chunk :
      Fin
        (PrimeGrouped.Logarithmic.chunkCount payloadWidth fanIn)) :
    reverseChildRank fanIn child *
          PrimeGrouped.Logarithmic.chunkCount payloadWidth fanIn +
        (PrimeGrouped.Logarithmic.chunkCount payloadWidth fanIn -
          1 - chunk.val) =
      basisCoordinateDigitIndex payloadWidth fanIn (child, chunk) := by
  unfold reverseChildRank basisCoordinateDigitIndex
  let k := PrimeGrouped.Logarithmic.chunkCount payloadWidth fanIn
  let c := child.val
  let d := chunk.val
  change
    (fanIn - 1 - c) * k + (k - 1 - d) =
      fanIn * k - 1 - (d + k * c)
  have hc : c < fanIn := child.isLt
  have hd : d < k := chunk.isLt
  have hfan :
      fanIn = (fanIn - 1 - c) + 1 + c := by
    omega
  have hmul :
      fanIn * k = (fanIn - 1 - c) * k + k + c * k := by
    calc
      fanIn * k =
          ((fanIn - 1 - c) + 1 + c) * k :=
        congrArg (fun value => value * k) hfan
      _ = _ := by ring
  have hcomm : c * k = k * c := Nat.mul_comm c k
  omega

private def assignmentIndexFootprint
    (regs : NeighborhoodTrial.Registers controller) : Finset ℕ :=
  {coordinateIndex regs, regs.index 29}

private theorem prepareAssignmentDigitIndex_writesWithin
    (regs : NeighborhoodTrial.Registers controller)
    (reverseRank : ℕ) :
    RAM.Structured.Footprint.CmdWritesWithin
      (assignmentIndexFootprint regs)
      (prepareAssignmentDigitIndex regs reverseRank) := by
  simp [assignmentIndexFootprint, prepareAssignmentDigitIndex, copy,
    Cmd.seqList, RAM.Structured.Footprint.CmdWritesWithin,
    RAM.Structured.Footprint.BasicWritesWithin]

private theorem assignmentIndexFootprint_subset
    (regs : NeighborhoodTrial.Registers controller) :
    assignmentIndexFootprint regs ⊆
      CombineValue.combineScratchFootprint regs := by
  intro address haddress
  simp only [assignmentIndexFootprint, Finset.mem_insert,
    Finset.mem_singleton] at haddress
  rcases haddress with rfl | rfl
  · exact test_combineScratch_mem regs (15 : Fin 19)
  · exact test_combineScratch_mem regs (14 : Fin 19)

private theorem prepareAssignmentDigitIndex_runs
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store) (reverseRank chunkCount chunk : ℕ)
    (hchunkCount :
      store (Layout.chunkCount regs) = chunkCount)
    (hone :
      store (CombineValue.rangeRegisters regs).one = 1)
    (hchunk :
      store (basisChunkCursor regs) = chunk) :
    ∃ final,
      Runs (prepareAssignmentDigitIndex regs reverseRank) store final ∧
      final (coordinateIndex regs) =
        reverseRank * chunkCount + (chunkCount - 1 - chunk) ∧
      ∀ address, address ∉ assignmentIndexFootprint regs →
        final address = store address := by
  let afterRank :=
    (Basic.imm (coordinateIndex regs) reverseRank).exec store
  let afterProduct :=
    (Basic.mul (coordinateIndex regs) (coordinateIndex regs)
      (Layout.chunkCount regs)).exec afterRank
  obtain ⟨afterCount, hcopy, hcopyValue, hcopyOutside⟩ :=
    copy_runs_internal (regs.index 29) (Layout.chunkCount regs)
      afterProduct (regs.injective.ne (by decide))
  let afterPred :=
    (Basic.sub (regs.index 29) (regs.index 29)
      (CombineValue.rangeRegisters regs).one).exec afterCount
  let afterOffset :=
    (Basic.sub (regs.index 29) (regs.index 29)
      (basisChunkCursor regs)).exec afterPred
  let final :=
    (Basic.add (coordinateIndex regs) (coordinateIndex regs)
      (regs.index 29)).exec afterOffset
  have honeAddress : store (regs.index 17) = 1 := by
    simpa [CombineValue.rangeRegisters] using hone
  have hchunkAddress : store (regs.index 1) = chunk := by
    simpa [basisChunkCursor, basisChunkRangeRegisters] using hchunk
  have hrun :
      Runs (prepareAssignmentDigitIndex regs reverseRank)
        store final := by
    simpa [prepareAssignmentDigitIndex, Cmd.seqList, afterRank,
      afterProduct, afterPred, afterOffset, final] using
      Runs.seq (Runs.basic _ _)
        (Runs.seq (Runs.basic _ _)
          (Runs.seq hcopy
            (Runs.seq (Runs.basic _ _)
              (Runs.seq (Runs.basic _ _) (Runs.basic _ _)))))
  refine ⟨final, hrun, ?_, ?_⟩
  · simp [final, afterOffset, afterPred, Basic.exec,
      hcopyValue, hcopyOutside, afterProduct, afterRank,
      hchunkCount, honeAddress, hchunkAddress, coordinateIndex,
      basisChunkCursor, basisChunkRangeRegisters,
      CombineValue.rangeRegisters, CombineValue.RangeRegisters.one,
      CombineValue.RangeRegisters.count, Layout.chunkCount,
      regs.injective.eq_iff]
  · intro address haddress
    exact
      RAM.Structured.Footprint.runs_eq_outside
        (prepareAssignmentDigitIndex_writesWithin regs reverseRank)
        hrun haddress

private def bankCoordinateFootprint
    (regs : NeighborhoodTrial.Registers controller) : Finset ℕ :=
  {coordinateIndex regs, regs.index 29,
    (CombineValue.rangeRegisters regs).test}

private theorem prepareBankCoordinate_writesWithin
    (regs : NeighborhoodTrial.Registers controller)
    {fanIn : ℕ} (child : Fin fanIn) :
    RAM.Structured.Footprint.CmdWritesWithin
      (bankCoordinateFootprint regs)
      (prepareBankCoordinate regs child) := by
  simp [bankCoordinateFootprint, prepareBankCoordinate,
    Cmd.seqList, RAM.Structured.Footprint.CmdWritesWithin,
    RAM.Structured.Footprint.BasicWritesWithin]

private theorem bankCoordinateFootprint_subset
    (regs : NeighborhoodTrial.Registers controller) :
    bankCoordinateFootprint regs ⊆
      CombineValue.combineScratchFootprint regs := by
  intro address haddress
  simp only [bankCoordinateFootprint, Finset.mem_insert,
    Finset.mem_singleton] at haddress
  rcases haddress with rfl | rfl | rfl
  · exact test_combineScratch_mem regs (15 : Fin 19)
  · exact test_combineScratch_mem regs (14 : Fin 19)
  · exact test_combineScratch_mem regs (3 : Fin 19)

private theorem prepareBankCoordinate_runs
    (regs : NeighborhoodTrial.Registers controller)
    {fanIn : ℕ} (child : Fin fanIn)
    (store : Store) (out chunkCount chunk : ℕ)
    (hout : store (Layout.out regs) = out)
    (hchunkCount :
      store (Layout.chunkCount regs) = chunkCount)
    (hchunk :
      store (basisChunkCursor regs) = chunk) :
    ∃ final,
      Runs (prepareBankCoordinate regs child) store final ∧
      final (coordinateIndex regs) =
        (if child.val < out then child.val else child.val + 1) *
            chunkCount +
          chunk ∧
      ∀ address, address ∉ bankCoordinateFootprint regs →
        final address = store address := by
  let afterChild :=
    (Basic.imm (regs.index 29) child.val).exec store
  let afterTest :=
    (Basic.sub (CombineValue.rangeRegisters regs).test
      (Layout.out regs) (regs.index 29)).exec afterChild
  have hchunkAddress : store (regs.index 1) = chunk := by
    simpa [basisChunkCursor, basisChunkRangeRegisters] using hchunk
  by_cases hchild : child.val < out
  · have htest :
        afterTest (CombineValue.rangeRegisters regs).test ≠ 0 := by
      simp [afterTest, afterChild, Basic.exec,
        CombineValue.rangeRegisters, CombineValue.RangeRegisters.test,
        Layout.out, regs.injective.eq_iff, hout]
      omega
    let afterTarget :=
      (Basic.imm (coordinateIndex regs) child.val).exec afterTest
    let afterProduct :=
      (Basic.mul (coordinateIndex regs) (coordinateIndex regs)
        (Layout.chunkCount regs)).exec afterTarget
    let final :=
      (Basic.add (coordinateIndex regs) (coordinateIndex regs)
        (basisChunkCursor regs)).exec afterProduct
    have hrun :
        Runs (prepareBankCoordinate regs child) store final := by
      simpa [prepareBankCoordinate, Cmd.seqList, afterChild,
        afterTest, afterTarget, afterProduct, final] using
        Runs.seq (Runs.basic _ _)
          (Runs.seq (Runs.basic _ _)
            (Runs.seq (Runs.ifNonzero htest (Runs.basic _ _))
              (Runs.seq (Runs.basic _ _) (Runs.basic _ _))))
    refine ⟨final, hrun, ?_, ?_⟩
    · simp [final, afterProduct, afterTarget, afterTest,
        afterChild, Basic.exec, hchild, hchunkCount, hchunkAddress,
        coordinateIndex, basisChunkCursor,
        basisChunkRangeRegisters,
        CombineValue.rangeRegisters,
        CombineValue.RangeRegisters.count,
        Layout.chunkCount, regs.injective.eq_iff]
    · intro address haddress
      exact
        RAM.Structured.Footprint.runs_eq_outside
          (prepareBankCoordinate_writesWithin regs child)
          hrun haddress
  · have htest :
        afterTest (CombineValue.rangeRegisters regs).test = 0 := by
      simp [afterTest, afterChild, Basic.exec,
        CombineValue.rangeRegisters, CombineValue.RangeRegisters.test,
        Layout.out, regs.injective.eq_iff, hout]
      omega
    let afterTarget :=
      (Basic.imm (coordinateIndex regs) (child.val + 1)).exec
        afterTest
    let afterProduct :=
      (Basic.mul (coordinateIndex regs) (coordinateIndex regs)
        (Layout.chunkCount regs)).exec afterTarget
    let final :=
      (Basic.add (coordinateIndex regs) (coordinateIndex regs)
        (basisChunkCursor regs)).exec afterProduct
    have hrun :
        Runs (prepareBankCoordinate regs child) store final := by
      simpa [prepareBankCoordinate, Cmd.seqList, afterChild,
        afterTest, afterTarget, afterProduct, final] using
        Runs.seq (Runs.basic _ _)
          (Runs.seq (Runs.basic _ _)
            (Runs.seq (Runs.ifZero htest (Runs.basic _ _))
              (Runs.seq (Runs.basic _ _) (Runs.basic _ _))))
    refine ⟨final, hrun, ?_, ?_⟩
    · simp [final, afterProduct, afterTarget, afterTest,
        afterChild, Basic.exec, hchild, hchunkCount, hchunkAddress,
        coordinateIndex, basisChunkCursor,
        basisChunkRangeRegisters,
        CombineValue.rangeRegisters,
        CombineValue.RangeRegisters.count,
        Layout.chunkCount, regs.injective.eq_iff]
    · intro address haddress
      exact
        RAM.Structured.Footprint.runs_eq_outside
          (prepareBankCoordinate_writesWithin regs child)
          hrun haddress

structure BasisPreparePost
    {tm : TM workTapeCount}
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (tape : TapeIndex workTapeCount)
    (slot : NeighborhoodGraph.Slot)
    (interval code accumulator : ℕ)
    (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (child :
      Fin (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount))
    (chunk :
      Fin
        (PrimeGrouped.Logarithmic.chunkCount
          (NeighborhoodExecutableEvaluation.payloadWidth
            tm instanceData.blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount)))
    (initial final : Store) : Prop where
  context :
    ComputationFrameContext regs instanceData frame tape slot interval
      logicalBank final
  selected_eq :
    final (CombineValue.rangeRegisters regs).term =
      PrimeGrouped.Logarithmic.chunkCodeNat
        (GroupedExtension.Evaluation.chunkAssignmentOfCode
          finProdFinEquiv
          (PrimeGrouped.Logarithmic.chunkBits
            (NeighborhoodExecutableEvaluation.payloadWidth
              tm instanceData.blockLength)
            (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount))
          code (child, chunk))
  point_eq :
    final (coordinateBankRegisters regs).result =
      computationArguments frame logicalBank child chunk
  coordinate_eq :
    final (coordinateIndex regs) = chunk.val
  innerCount_eq :
    final (basisChunkRangeRegisters regs).count =
      PrimeGrouped.Logarithmic.domainSize
        (NeighborhoodExecutableEvaluation.payloadWidth
          tm instanceData.blockLength)
        (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount)
  basis_eq : final (basisValue regs) = accumulator
  packed_eq :
    final (packedValue regs) = initial (packedValue regs)
  accumulator_eq :
    final (CombineValue.rangeRegisters regs).accumulator =
      initial (CombineValue.rangeRegisters regs).accumulator
  remaining_eq :
    final (CombineValue.rangeRegisters regs).remaining = code
  modulus_eq :
    final (CombineValue.rangeRegisters regs).modulus =
      initial (CombineValue.rangeRegisters regs).modulus
  modulusPred_eq :
    final (CombineValue.rangeRegisters regs).modulusPred =
      initial (CombineValue.rangeRegisters regs).modulusPred
  one_eq :
    final (CombineValue.rangeRegisters regs).one =
      initial (CombineValue.rangeRegisters regs).one
  count_eq :
    final (CombineValue.rangeRegisters regs).count =
      initial (CombineValue.rangeRegisters regs).count

theorem basisChunkPrepare_runs_internal
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
    (child :
      Fin (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount))
    (chunk :
      Fin
        (PrimeGrouped.Logarithmic.chunkCount
          (NeighborhoodExecutableEvaluation.payloadWidth
            tm instanceData.blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount)))
    (store : Store) (code accumulator : ℕ)
    (hcontext :
      ComputationFrameContext regs instanceData frame tape slot interval
        logicalBank store)
    (hremaining :
      store (CombineValue.rangeRegisters regs).remaining = code)
    (_hmodulus :
      store (CombineValue.rangeRegisters regs).modulus =
        NeighborhoodScheduler.fieldModulus instanceData)
    (_hmodulusPred :
      store (CombineValue.rangeRegisters regs).modulusPred =
        NeighborhoodScheduler.fieldModulus instanceData - 1)
    (hone :
      store (CombineValue.rangeRegisters regs).one = 1)
    (haccumulator : store (basisValue regs) = accumulator)
    (hcursor :
      store (basisChunkCursor regs) = chunk.val + 1) :
    ∃ final,
      Runs (basisChunkPrepare regs child) store final ∧
      BasisPreparePost regs instanceData frame tape slot interval
        code accumulator logicalBank child chunk store final := by
  let payloadWidth :=
    NeighborhoodExecutableEvaluation.payloadWidth
      tm instanceData.blockLength
  let fanIn :=
    NeighborhoodExecutableEvaluation.graphFanIn workTapeCount
  let modulus := NeighborhoodScheduler.fieldModulus instanceData
  let radix :=
    PrimeGrouped.Logarithmic.domainSize payloadWidth fanIn
  let digitIndex :=
    basisCoordinateDigitIndex payloadWidth fanIn (child, chunk)
  let bankCoordinate :=
    NeighborhoodProgram.residueBankIndex
      tm instanceData.blockLength (frame.childTarget child) chunk
  let selected :=
    GroupedExtension.Evaluation.chunkAssignmentOfCode
      finProdFinEquiv
      (PrimeGrouped.Logarithmic.chunkBits payloadWidth fanIn)
      code (child, chunk)
  let point := computationArguments frame logicalBank child chunk
  have hradixPos : 0 < radix :=
    PrimeGrouped.Logarithmic.domainSize_pos payloadWidth fanIn
  have hradixEq :
      Representation.digitBase instanceData = radix := by
    unfold Representation.digitBase CandidateParameters.domainSize
    rw [← Representation.payloadWidth_eq_booleanWidth instanceData]
    rfl
  have hradixValue :
      store (Layout.chunkRadix regs) = radix :=
    hcontext.computation.parameters.digitBase_eq.trans hradixEq
  have hchunkCount :
      store (Layout.chunkCount regs) =
        PrimeGrouped.Logarithmic.chunkCount payloadWidth fanIn := by
    simpa [payloadWidth, fanIn] using
      hcontext.computation.parameters.chunkCount_eq
  let afterDecrement :=
    (Basic.sub (basisChunkCursor regs) (basisChunkCursor regs)
      (CombineValue.rangeRegisters regs).one).exec store
  have hdecrementRun :
      Runs
        (.basic (.sub (basisChunkCursor regs) (basisChunkCursor regs)
          (CombineValue.rangeRegisters regs).one))
        store afterDecrement :=
    Runs.basic _ _
  have hdecrementCursor :
      afterDecrement (basisChunkCursor regs) = chunk.val := by
    simp [afterDecrement, Basic.exec, hcursor, hone]
  have hdecrementWrites :
      RAM.Structured.Footprint.CmdWritesWithin
        (CombineValue.combineScratchFootprint regs)
        (.basic (.sub (basisChunkCursor regs) (basisChunkCursor regs)
          (CombineValue.rangeRegisters regs).one)) := by
    have h1 := test_combineScratch_mem regs (1 : Fin 19)
    change basisChunkCursor regs ∈
      CombineValue.combineScratchFootprint regs at h1
    simpa [RAM.Structured.Footprint.CmdWritesWithin,
      RAM.Structured.Footprint.BasicWritesWithin] using h1
  have hdecrementBank :
      afterDecrement regs.layout.bank = store regs.layout.bank := by
    change afterDecrement (regs.index 33) = store (regs.index 33)
    simp [afterDecrement, Basic.exec, basisChunkCursor,
      basisChunkRangeRegisters, regs.injective.eq_iff]
  have hdecrementContext :
      ComputationFrameContext regs instanceData frame tape slot interval
        logicalBank afterDecrement :=
    frameContext_transport_combineScratch_internal
      regs instanceData frame tape slot interval
      logicalBank hcontext hdecrementWrites hdecrementRun hdecrementBank
  have hdecrementRemaining :
      afterDecrement (CombineValue.rangeRegisters regs).remaining =
        code := by
    simpa [afterDecrement, Basic.exec, basisChunkCursor,
      basisChunkRangeRegisters, CombineValue.rangeRegisters,
      regs.injective.eq_iff] using hremaining
  have hdecrementRadix :
      afterDecrement (Layout.chunkRadix regs) = radix := by
    simpa [afterDecrement, Basic.exec, basisChunkCursor,
      basisChunkRangeRegisters, Layout.chunkRadix,
      regs.injective.eq_iff] using hradixValue
  have hdecrementOne :
      afterDecrement (CombineValue.rangeRegisters regs).one = 1 := by
    simpa [afterDecrement, Basic.exec, basisChunkCursor,
      basisChunkRangeRegisters, CombineValue.rangeRegisters,
      regs.injective.eq_iff] using hone
  obtain ⟨afterDigitIndex, hdigitIndexRun, hdigitIndexValue,
      hdigitIndexOutside⟩ :=
    prepareAssignmentDigitIndex_runs regs afterDecrement
      (reverseChildRank fanIn child)
      (PrimeGrouped.Logarithmic.chunkCount payloadWidth fanIn)
      chunk.val
      (by simpa [payloadWidth, fanIn] using
        hdecrementContext.computation.parameters.chunkCount_eq)
      hdecrementOne hdecrementCursor
  have hdigitIndexExact :
      afterDigitIndex (assignmentDigitIndex regs) = digitIndex := by
    rw [hdigitIndexValue]
    exact runtimeDigitIndex_eq payloadWidth fanIn child chunk
  have hdigitIndexBank :
      afterDigitIndex regs.layout.bank =
        afterDecrement regs.layout.bank := by
    apply hdigitIndexOutside
    change regs.index 33 ∉ assignmentIndexFootprint regs
    simp [assignmentIndexFootprint, coordinateIndex,
      regs.injective.eq_iff]
  have hdigitIndexContext :
      ComputationFrameContext regs instanceData frame tape slot interval
        logicalBank afterDigitIndex :=
    frameContext_transport_combineScratch_internal
      regs instanceData frame tape slot interval
      logicalBank hdecrementContext
      (test_cmdWritesWithin_mono
        (assignmentIndexFootprint_subset regs) _
        (prepareAssignmentDigitIndex_writesWithin regs
          (reverseChildRank fanIn child)))
      hdigitIndexRun hdigitIndexBank
  have hdigitIndexRemaining :
      afterDigitIndex (CombineValue.rangeRegisters regs).remaining =
        code := by
    rw [hdigitIndexOutside]
    · exact hdecrementRemaining
    · simp [assignmentIndexFootprint,
        CombineValue.rangeRegisters, coordinateIndex,
        regs.injective.eq_iff]
  have hdigitIndexRadix :
      afterDigitIndex (Layout.chunkRadix regs) = radix := by
    rw [hdigitIndexOutside]
    · exact hdecrementRadix
    · simp [assignmentIndexFootprint, Layout.chunkRadix,
        coordinateIndex, regs.injective.eq_iff]
  have hdigitIndexOne :
      afterDigitIndex (CombineValue.rangeRegisters regs).one = 1 := by
    rw [hdigitIndexOutside]
    · exact hdecrementOne
    · simp [assignmentIndexFootprint,
        CombineValue.rangeRegisters, coordinateIndex,
        regs.injective.eq_iff]
  obtain ⟨afterAssignment, hassignmentRun, hassignmentPost,
      hassignmentABI⟩ :=
    Internal.assignmentDigit_runs_internal regs afterDigitIndex radix
      code digitIndex hradixPos hdigitIndexRemaining hdigitIndexExact
      hdigitIndexRadix hdigitIndexOne
  have hassignmentBank :
      afterAssignment regs.layout.bank =
        afterDigitIndex regs.layout.bank := by
    apply RAM.Structured.Footprint.runs_eq_outside
      (Internal.assignmentDigit_precise_writesWithin_internal regs)
      hassignmentRun
    change regs.index 33 ∉
      (assignmentDigitRegisters regs).writeFootprint
    simp [DigitRegisters.writeFootprint, assignmentDigitRegisters,
      regs.injective.eq_iff]
  have hassignmentContext :
      ComputationFrameContext regs instanceData frame tape slot interval
        logicalBank afterAssignment :=
    Internal.computationFrameContext_transport_internal
      regs instanceData frame tape slot interval logicalBank
      hdigitIndexContext hassignmentABI hassignmentBank
  have hdigitIndexCursor :
      afterDigitIndex (basisChunkCursor regs) = chunk.val := by
    rw [hdigitIndexOutside]
    · exact hdecrementCursor
    · simp [assignmentIndexFootprint, basisChunkCursor,
        basisChunkRangeRegisters, coordinateIndex,
        regs.injective.eq_iff]
  have hassignmentCursor :
      afterAssignment (basisChunkCursor regs) = chunk.val := by
    rw [RAM.Structured.Footprint.runs_eq_outside
      (Internal.assignmentDigit_precise_writesWithin_internal regs)
      hassignmentRun]
    · exact hdigitIndexCursor
    · change regs.index 1 ∉
        (assignmentDigitRegisters regs).writeFootprint
      simp [DigitRegisters.writeFootprint, assignmentDigitRegisters,
        regs.injective.eq_iff]
  obtain ⟨afterBankIndex, hbankIndexRun, hbankIndexValue,
      hbankIndexOutside⟩ :=
    prepareBankCoordinate_runs regs child afterAssignment
      frame.out.val
      (PrimeGrouped.Logarithmic.chunkCount payloadWidth fanIn)
      chunk.val hassignmentContext.out_eq
      (by simpa [payloadWidth, fanIn] using
        hassignmentContext.computation.parameters.chunkCount_eq)
      hassignmentCursor
  have hbankIndexExact :
      afterBankIndex (coordinateIndex regs) = bankCoordinate := by
    rw [hbankIndexValue]
    unfold bankCoordinate NeighborhoodProgram.residueBankIndex
    rw [Dispatcher.childTargetValue_eq_succAbove frame.out child]
    rfl
  have hbankIndexBank :
      afterBankIndex regs.layout.bank =
        afterAssignment regs.layout.bank := by
    apply hbankIndexOutside
    change regs.index 33 ∉ bankCoordinateFootprint regs
    simp [bankCoordinateFootprint, coordinateIndex,
      CombineValue.rangeRegisters, regs.injective.eq_iff]
  have hbankIndexContext :
      ComputationFrameContext regs instanceData frame tape slot interval
        logicalBank afterBankIndex :=
    frameContext_transport_combineScratch_internal
      regs instanceData frame tape slot interval
      logicalBank hassignmentContext
      (test_cmdWritesWithin_mono
        (bankCoordinateFootprint_subset regs) _
        (prepareBankCoordinate_writesWithin regs child))
      hbankIndexRun hbankIndexBank
  have hbankIndexCursor :
      afterBankIndex (basisChunkCursor regs) = chunk.val := by
    rw [hbankIndexOutside]
    · exact hassignmentCursor
    · simp [bankCoordinateFootprint, basisChunkCursor,
        basisChunkRangeRegisters, coordinateIndex,
        CombineValue.rangeRegisters, regs.injective.eq_iff]
  have hbankIndexOne :
      afterBankIndex (CombineValue.rangeRegisters regs).one = 1 := by
    rw [hbankIndexOutside]
    · exact hassignmentPost.one_eq.trans hdigitIndexOne
    · simp [bankCoordinateFootprint,
        CombineValue.rangeRegisters, coordinateIndex,
        regs.injective.eq_iff]
  obtain ⟨afterSave, hsaveRun, hsaveValue, hsaveOutside⟩ :=
    copy_runs_internal (regs.index 29) (basisChunkCursor regs)
      afterBankIndex (regs.injective.ne (by decide))
  have hsaveCursor :
      afterSave (regs.index 29) = chunk.val :=
    hsaveValue.trans hbankIndexCursor
  have hsaveCoordinate :
      afterSave (coordinateIndex regs) = bankCoordinate := by
    rw [hsaveOutside (coordinateIndex regs)
      (regs.injective.ne (by decide))]
    exact hbankIndexExact
  have hsaveOne :
      afterSave (CombineValue.rangeRegisters regs).one = 1 := by
    rw [hsaveOutside (CombineValue.rangeRegisters regs).one
      (regs.injective.ne (by decide))]
    exact hbankIndexOne
  have hsaveBank :
      afterSave regs.layout.bank = afterBankIndex regs.layout.bank := by
    change afterSave (regs.index 33) = afterBankIndex (regs.index 33)
    exact hsaveOutside _ (regs.injective.ne (by decide))
  have hsaveWrites :
      RAM.Structured.Footprint.CmdWritesWithin
        (CombineValue.combineScratchFootprint regs)
        (copy (regs.index 29) (basisChunkCursor regs)) := by
    have h29 := test_combineScratch_mem regs (14 : Fin 19)
    change regs.index 29 ∈
      CombineValue.combineScratchFootprint regs at h29
    simpa [copy, RAM.Structured.Footprint.CmdWritesWithin,
      RAM.Structured.Footprint.BasicWritesWithin] using
      And.intro h29 h29
  have hsaveContext :
      ComputationFrameContext regs instanceData frame tape slot interval
        logicalBank afterSave :=
    frameContext_transport_combineScratch_internal
      regs instanceData frame tape slot interval
      logicalBank hbankIndexContext hsaveWrites hsaveRun hsaveBank
  obtain ⟨afterRead, hreadRun, hreadPost, hreadContext⟩ :=
    Internal.readResidueCoordinate_runs_internal regs instanceData tape
      slot interval logicalBank (frame.childTarget child) chunk
      afterSave hsaveContext.computation hsaveCoordinate hsaveOne
  have hreadOut :
      afterRead (Layout.out regs) = afterSave (Layout.out regs) := by
    apply RAM.Structured.Footprint.runs_eq_outside
      (Internal.readResidueCoordinate_writesWithin_internal regs)
      hreadRun
    simp [coordinateReadFootprint,
      NeighborhoodProgram.BankRegisters.footprint,
      coordinateBankRegisters, coordinateBankMap,
      CombineValue.rangeRegisters, savedRangeCount,
      Layout.out, regs.injective.eq_iff]
    decide
  have hreadFrameContext :
      ComputationFrameContext regs instanceData frame tape slot interval
        logicalBank afterRead :=
    { computation := hreadContext
      out_eq := hreadOut.trans hsaveContext.out_eq }
  have hreadCursorSave :
      afterRead (regs.index 29) = chunk.val := by
    rw [RAM.Structured.Footprint.runs_eq_outside
      (Internal.readResidueCoordinate_writesWithin_internal regs)
      hreadRun]
    · exact hsaveCursor
    · simp [coordinateReadFootprint,
        NeighborhoodProgram.BankRegisters.footprint,
        coordinateBankRegisters, coordinateBankMap,
        CombineValue.rangeRegisters, savedRangeCount,
        regs.injective.eq_iff]
      decide
  obtain ⟨afterRestore, hrestoreRun, hrestoreValue,
      hrestoreOutside⟩ :=
    copy_runs_internal (coordinateIndex regs) (regs.index 29) afterRead
      (regs.injective.ne (by decide))
  have hrestoreCoordinate :
      afterRestore (coordinateIndex regs) = chunk.val :=
    hrestoreValue.trans hreadCursorSave
  have hrestoreBank :
      afterRestore regs.layout.bank = afterRead regs.layout.bank := by
    change afterRestore (regs.index 33) = afterRead (regs.index 33)
    exact hrestoreOutside _ (regs.injective.ne (by decide))
  have hrestoreWrites :
      RAM.Structured.Footprint.CmdWritesWithin
        (CombineValue.combineScratchFootprint regs)
        (copy (coordinateIndex regs) (regs.index 29)) := by
    have h30 := test_combineScratch_mem regs (15 : Fin 19)
    change coordinateIndex regs ∈
      CombineValue.combineScratchFootprint regs at h30
    simpa [copy, RAM.Structured.Footprint.CmdWritesWithin,
      RAM.Structured.Footprint.BasicWritesWithin] using
      And.intro h30 h30
  have hrestoreContext :
      ComputationFrameContext regs instanceData frame tape slot interval
        logicalBank afterRestore :=
    frameContext_transport_combineScratch_internal
      regs instanceData frame tape slot interval
      logicalBank hreadFrameContext hrestoreWrites hrestoreRun
      hrestoreBank
  have hrestoreRadix :
      afterRestore (Layout.chunkRadix regs) = radix := by
    rw [hrestoreOutside (Layout.chunkRadix regs)
      (regs.injective.ne (by decide))]
    exact hreadContext.parameters.digitBase_eq.trans hradixEq
  obtain ⟨afterCount, hcountRun, hcountValue, hcountOutside⟩ :=
    copy_runs_internal (basisChunkRangeRegisters regs).count
      (Layout.chunkRadix regs) afterRestore
      (regs.injective.ne (by decide))
  have hcountExact :
      afterCount (basisChunkRangeRegisters regs).count = radix :=
    hcountValue.trans hrestoreRadix
  have hcountBank :
      afterCount regs.layout.bank = afterRestore regs.layout.bank := by
    change afterCount (regs.index 33) = afterRestore (regs.index 33)
    exact hcountOutside _ (regs.injective.ne (by decide))
  have hcountWrites :
      RAM.Structured.Footprint.CmdWritesWithin
        (CombineValue.combineScratchFootprint regs)
        (copy (basisChunkRangeRegisters regs).count
          (Layout.chunkRadix regs)) := by
    have h1 := test_combineScratch_mem regs (1 : Fin 19)
    change (basisChunkRangeRegisters regs).count ∈
      CombineValue.combineScratchFootprint regs at h1
    simpa [copy, RAM.Structured.Footprint.CmdWritesWithin,
      RAM.Structured.Footprint.BasicWritesWithin] using
      And.intro h1 h1
  have hcountContext :
      ComputationFrameContext regs instanceData frame tape slot interval
        logicalBank afterCount :=
    frameContext_transport_combineScratch_internal
      regs instanceData frame tape slot interval
      logicalBank hrestoreContext hcountWrites hcountRun hcountBank
  have hreadTerm :
      afterRead (CombineValue.rangeRegisters regs).term =
        afterSave (CombineValue.rangeRegisters regs).term := by
    apply RAM.Structured.Footprint.runs_eq_outside
      (Internal.readResidueCoordinate_writesWithin_internal regs)
      hreadRun
    simp [coordinateReadFootprint,
      NeighborhoodProgram.BankRegisters.footprint,
      coordinateBankRegisters, coordinateBankMap,
      CombineValue.rangeRegisters, savedRangeCount,
      regs.injective.eq_iff]
    decide
  have hcountSelected :
      afterCount (CombineValue.rangeRegisters regs).term =
        PrimeGrouped.Logarithmic.chunkCodeNat selected := by
    calc
      afterCount (CombineValue.rangeRegisters regs).term =
          afterRestore (CombineValue.rangeRegisters regs).term := by
        rw [hcountOutside]
        simp [basisChunkRangeRegisters,
          CombineValue.rangeRegisters, regs.injective.eq_iff]
      _ = afterRead (CombineValue.rangeRegisters regs).term := by
        rw [hrestoreOutside]
        simp [coordinateIndex, CombineValue.rangeRegisters,
          regs.injective.eq_iff]
      _ = afterSave (CombineValue.rangeRegisters regs).term :=
        hreadTerm
      _ = afterBankIndex
          (CombineValue.rangeRegisters regs).term := by
        rw [hsaveOutside]
        simp [CombineValue.rangeRegisters, regs.injective.eq_iff]
      _ = afterAssignment
          (CombineValue.rangeRegisters regs).term := by
        rw [hbankIndexOutside]
        simp [bankCoordinateFootprint, coordinateIndex,
          CombineValue.rangeRegisters, regs.injective.eq_iff]
      _ = radixDigit radix code digitIndex :=
        hassignmentPost.term_eq
      _ = PrimeGrouped.Logarithmic.chunkCodeNat selected := by
        symm
        exact test_assignment_digit payloadWidth fanIn code (child, chunk)
  have hcountPoint :
      afterCount (coordinateBankRegisters regs).result = point := by
    calc
      afterCount (coordinateBankRegisters regs).result =
          afterRestore (coordinateBankRegisters regs).result := by
        rw [hcountOutside]
        simp [basisChunkRangeRegisters, coordinateBankRegisters,
          coordinateBankMap, regs.injective.eq_iff]
      _ = afterRead (coordinateBankRegisters regs).result := by
        rw [hrestoreOutside]
        simp [coordinateIndex, coordinateBankRegisters,
          coordinateBankMap, regs.injective.eq_iff]
      _ = point := by
        simpa [point, computationArguments] using hreadPost.result_eq
  have hcountCoordinate :
      afterCount (coordinateIndex regs) = chunk.val := by
    rw [hcountOutside]
    · exact hrestoreCoordinate
    · simp [basisChunkRangeRegisters, coordinateIndex,
        regs.injective.eq_iff]
  have hrun :
      Runs (basisChunkPrepare regs child) store afterCount := by
    simpa [basisChunkPrepare, Cmd.seqList] using
      Runs.seq hdecrementRun
        (Runs.seq hdigitIndexRun
          (Runs.seq hassignmentRun
            (Runs.seq hbankIndexRun
              (Runs.seq hsaveRun
                (Runs.seq hreadRun
                  (Runs.seq hrestoreRun hcountRun))))))
  have hreadBasis :
      afterRead (basisValue regs) = afterSave (basisValue regs) := by
    apply RAM.Structured.Footprint.runs_eq_outside
      (Internal.readResidueCoordinate_writesWithin_internal regs)
      hreadRun
    simp [coordinateReadFootprint,
      NeighborhoodProgram.BankRegisters.footprint,
      coordinateBankRegisters, coordinateBankMap,
      CombineValue.rangeRegisters, savedRangeCount, basisValue,
      regs.injective.eq_iff]
    decide
  have hassignmentBasis :
      afterAssignment (basisValue regs) =
        afterDigitIndex (basisValue regs) := by
    apply RAM.Structured.Footprint.runs_eq_outside
      (Internal.assignmentDigit_precise_writesWithin_internal regs)
      hassignmentRun
    change regs.index 32 ∉
      (assignmentDigitRegisters regs).writeFootprint
    simp [DigitRegisters.writeFootprint, assignmentDigitRegisters,
      regs.injective.eq_iff]
  have hcountBasis :
      afterCount (basisValue regs) = accumulator := by
    calc
      afterCount (basisValue regs) = afterRestore (basisValue regs) := by
        rw [hcountOutside]
        simp [basisChunkRangeRegisters, basisValue,
          regs.injective.eq_iff]
      _ = afterRead (basisValue regs) := by
        rw [hrestoreOutside]
        simp [coordinateIndex, basisValue, regs.injective.eq_iff]
      _ = afterSave (basisValue regs) := hreadBasis
      _ = afterBankIndex (basisValue regs) := by
        rw [hsaveOutside]
        simp [basisValue, regs.injective.eq_iff]
      _ = afterAssignment (basisValue regs) := by
        rw [hbankIndexOutside]
        simp [bankCoordinateFootprint, coordinateIndex,
          CombineValue.rangeRegisters, basisValue,
          regs.injective.eq_iff]
      _ = afterDigitIndex (basisValue regs) := hassignmentBasis
      _ = afterDecrement (basisValue regs) := by
        rw [hdigitIndexOutside]
        simp [assignmentIndexFootprint, coordinateIndex,
          basisValue, regs.injective.eq_iff]
      _ = store (basisValue regs) := by
        simp [afterDecrement, Basic.exec, basisChunkCursor,
          basisChunkRangeRegisters, basisValue,
          regs.injective.eq_iff]
      _ = accumulator := haccumulator
  have hreadPacked :
      afterRead (packedValue regs) = afterSave (packedValue regs) := by
    apply RAM.Structured.Footprint.runs_eq_outside
      (Internal.readResidueCoordinate_writesWithin_internal regs)
      hreadRun
    simp [coordinateReadFootprint,
      NeighborhoodProgram.BankRegisters.footprint,
      coordinateBankRegisters, coordinateBankMap,
      CombineValue.rangeRegisters, savedRangeCount, packedValue,
      regs.injective.eq_iff]
    decide
  have hassignmentPacked :
      afterAssignment (packedValue regs) =
        afterDigitIndex (packedValue regs) := by
    apply RAM.Structured.Footprint.runs_eq_outside
      (Internal.assignmentDigit_precise_writesWithin_internal regs)
      hassignmentRun
    change regs.index 6 ∉
      (assignmentDigitRegisters regs).writeFootprint
    simp [DigitRegisters.writeFootprint, assignmentDigitRegisters,
      regs.injective.eq_iff]
  have hcountPacked :
      afterCount (packedValue regs) = store (packedValue regs) := by
    calc
      afterCount (packedValue regs) =
          afterRestore (packedValue regs) := by
        rw [hcountOutside]
        simp [basisChunkRangeRegisters, packedValue,
          regs.injective.eq_iff]
      _ = afterRead (packedValue regs) := by
        rw [hrestoreOutside]
        simp [coordinateIndex, packedValue, regs.injective.eq_iff]
      _ = afterSave (packedValue regs) := hreadPacked
      _ = afterBankIndex (packedValue regs) := by
        rw [hsaveOutside]
        simp [packedValue, regs.injective.eq_iff]
      _ = afterAssignment (packedValue regs) := by
        rw [hbankIndexOutside]
        simp [bankCoordinateFootprint, coordinateIndex,
          CombineValue.rangeRegisters, packedValue,
          regs.injective.eq_iff]
      _ = afterDigitIndex (packedValue regs) := hassignmentPacked
      _ = afterDecrement (packedValue regs) := by
        rw [hdigitIndexOutside]
        simp [assignmentIndexFootprint, coordinateIndex,
          packedValue, regs.injective.eq_iff]
      _ = store (packedValue regs) := by
        simp [afterDecrement, Basic.exec, basisChunkCursor,
          basisChunkRangeRegisters, packedValue,
          regs.injective.eq_iff]
  have hcountAccumulator :
      afterCount (CombineValue.rangeRegisters regs).accumulator =
        store (CombineValue.rangeRegisters regs).accumulator := by
    calc
      afterCount (CombineValue.rangeRegisters regs).accumulator =
          afterRestore
            (CombineValue.rangeRegisters regs).accumulator := by
        rw [hcountOutside]
        simp [basisChunkRangeRegisters,
          CombineValue.rangeRegisters, regs.injective.eq_iff]
      _ = afterRead
          (CombineValue.rangeRegisters regs).accumulator := by
        rw [hrestoreOutside]
        simp [coordinateIndex, CombineValue.rangeRegisters,
          regs.injective.eq_iff]
      _ = afterSave
          (CombineValue.rangeRegisters regs).accumulator :=
        hreadPost.accumulator_eq
      _ = afterBankIndex
          (CombineValue.rangeRegisters regs).accumulator := by
        rw [hsaveOutside]
        simp [CombineValue.rangeRegisters, regs.injective.eq_iff]
      _ = afterAssignment
          (CombineValue.rangeRegisters regs).accumulator := by
        rw [hbankIndexOutside]
        simp [bankCoordinateFootprint, coordinateIndex,
          CombineValue.rangeRegisters, regs.injective.eq_iff]
      _ = afterDigitIndex
          (CombineValue.rangeRegisters regs).accumulator :=
        hassignmentPost.accumulator_eq
      _ = afterDecrement
          (CombineValue.rangeRegisters regs).accumulator := by
        rw [hdigitIndexOutside]
        simp [assignmentIndexFootprint, coordinateIndex,
          CombineValue.rangeRegisters, regs.injective.eq_iff]
      _ = store
          (CombineValue.rangeRegisters regs).accumulator := by
        simp [afterDecrement, Basic.exec, basisChunkCursor,
          basisChunkRangeRegisters, CombineValue.rangeRegisters,
          regs.injective.eq_iff]
  have hcountRemaining :
      afterCount (CombineValue.rangeRegisters regs).remaining =
        code := by
    calc
      afterCount (CombineValue.rangeRegisters regs).remaining =
          afterRestore
            (CombineValue.rangeRegisters regs).remaining := by
        rw [hcountOutside]
        simp [basisChunkRangeRegisters,
          CombineValue.rangeRegisters, regs.injective.eq_iff]
      _ = afterRead
          (CombineValue.rangeRegisters regs).remaining := by
        rw [hrestoreOutside]
        simp [coordinateIndex, CombineValue.rangeRegisters,
          regs.injective.eq_iff]
      _ = afterSave
          (CombineValue.rangeRegisters regs).remaining :=
        hreadPost.remaining_eq
      _ = afterBankIndex
          (CombineValue.rangeRegisters regs).remaining := by
        rw [hsaveOutside]
        simp [CombineValue.rangeRegisters, regs.injective.eq_iff]
      _ = afterAssignment
          (CombineValue.rangeRegisters regs).remaining := by
        rw [hbankIndexOutside]
        simp [bankCoordinateFootprint, coordinateIndex,
          CombineValue.rangeRegisters, regs.injective.eq_iff]
      _ = code := hassignmentPost.remaining_eq
  have hcountModulus :
      afterCount (CombineValue.rangeRegisters regs).modulus =
        store (CombineValue.rangeRegisters regs).modulus := by
    calc
      afterCount (CombineValue.rangeRegisters regs).modulus =
          afterRestore
            (CombineValue.rangeRegisters regs).modulus := by
        rw [hcountOutside]
        simp [basisChunkRangeRegisters,
          CombineValue.rangeRegisters, regs.injective.eq_iff]
      _ = afterRead
          (CombineValue.rangeRegisters regs).modulus := by
        rw [hrestoreOutside]
        simp [coordinateIndex, CombineValue.rangeRegisters,
          regs.injective.eq_iff]
      _ = afterSave
          (CombineValue.rangeRegisters regs).modulus :=
        hreadPost.modulus_eq
      _ = afterBankIndex
          (CombineValue.rangeRegisters regs).modulus := by
        rw [hsaveOutside]
        simp [CombineValue.rangeRegisters, regs.injective.eq_iff]
      _ = afterAssignment
          (CombineValue.rangeRegisters regs).modulus := by
        rw [hbankIndexOutside]
        simp [bankCoordinateFootprint, coordinateIndex,
          CombineValue.rangeRegisters, regs.injective.eq_iff]
      _ = afterDigitIndex
          (CombineValue.rangeRegisters regs).modulus :=
        hassignmentPost.modulus_eq
      _ = afterDecrement
          (CombineValue.rangeRegisters regs).modulus := by
        rw [hdigitIndexOutside]
        simp [assignmentIndexFootprint, coordinateIndex,
          CombineValue.rangeRegisters, regs.injective.eq_iff]
      _ = store (CombineValue.rangeRegisters regs).modulus := by
        simp [afterDecrement, Basic.exec, basisChunkCursor,
          basisChunkRangeRegisters, CombineValue.rangeRegisters,
          regs.injective.eq_iff]
  have hcountModulusPred :
      afterCount (CombineValue.rangeRegisters regs).modulusPred =
        store (CombineValue.rangeRegisters regs).modulusPred := by
    calc
      afterCount (CombineValue.rangeRegisters regs).modulusPred =
          afterRestore
            (CombineValue.rangeRegisters regs).modulusPred := by
        rw [hcountOutside]
        simp [basisChunkRangeRegisters,
          CombineValue.rangeRegisters, regs.injective.eq_iff]
      _ = afterRead
          (CombineValue.rangeRegisters regs).modulusPred := by
        rw [hrestoreOutside]
        simp [coordinateIndex, CombineValue.rangeRegisters,
          regs.injective.eq_iff]
      _ = afterSave
          (CombineValue.rangeRegisters regs).modulusPred :=
        hreadPost.modulusPred_eq
      _ = afterBankIndex
          (CombineValue.rangeRegisters regs).modulusPred := by
        rw [hsaveOutside]
        simp [CombineValue.rangeRegisters, regs.injective.eq_iff]
      _ = afterAssignment
          (CombineValue.rangeRegisters regs).modulusPred := by
        rw [hbankIndexOutside]
        simp [bankCoordinateFootprint, coordinateIndex,
          CombineValue.rangeRegisters, regs.injective.eq_iff]
      _ = afterDigitIndex
          (CombineValue.rangeRegisters regs).modulusPred :=
        hassignmentPost.modulusPred_eq
      _ = afterDecrement
          (CombineValue.rangeRegisters regs).modulusPred := by
        rw [hdigitIndexOutside]
        simp [assignmentIndexFootprint, coordinateIndex,
          CombineValue.rangeRegisters, regs.injective.eq_iff]
      _ = store
          (CombineValue.rangeRegisters regs).modulusPred := by
        simp [afterDecrement, Basic.exec, basisChunkCursor,
          basisChunkRangeRegisters, CombineValue.rangeRegisters,
          regs.injective.eq_iff]
  have hcountOne :
      afterCount (CombineValue.rangeRegisters regs).one =
        store (CombineValue.rangeRegisters regs).one := by
    calc
      afterCount (CombineValue.rangeRegisters regs).one =
          afterRestore (CombineValue.rangeRegisters regs).one := by
        rw [hcountOutside]
        simp [basisChunkRangeRegisters,
          CombineValue.rangeRegisters, regs.injective.eq_iff]
      _ = afterRead (CombineValue.rangeRegisters regs).one := by
        rw [hrestoreOutside]
        simp [coordinateIndex, CombineValue.rangeRegisters,
          regs.injective.eq_iff]
      _ = afterSave (CombineValue.rangeRegisters regs).one :=
        hreadPost.one_eq
      _ = afterBankIndex (CombineValue.rangeRegisters regs).one := by
        rw [hsaveOutside]
        simp [CombineValue.rangeRegisters, regs.injective.eq_iff]
      _ = afterAssignment (CombineValue.rangeRegisters regs).one := by
        rw [hbankIndexOutside]
        simp [bankCoordinateFootprint, coordinateIndex,
          CombineValue.rangeRegisters, regs.injective.eq_iff]
      _ = afterDigitIndex (CombineValue.rangeRegisters regs).one :=
        hassignmentPost.one_eq
      _ = afterDecrement (CombineValue.rangeRegisters regs).one := by
        rw [hdigitIndexOutside]
        simp [assignmentIndexFootprint, coordinateIndex,
          CombineValue.rangeRegisters, regs.injective.eq_iff]
      _ = store (CombineValue.rangeRegisters regs).one := by
        simp [afterDecrement, Basic.exec, basisChunkCursor,
          basisChunkRangeRegisters, CombineValue.rangeRegisters,
          regs.injective.eq_iff]
  have hcountOuterCount :
      afterCount (CombineValue.rangeRegisters regs).count =
        store (CombineValue.rangeRegisters regs).count := by
    calc
      afterCount (CombineValue.rangeRegisters regs).count =
          afterRestore (CombineValue.rangeRegisters regs).count := by
        rw [hcountOutside]
        simp [basisChunkRangeRegisters,
          CombineValue.rangeRegisters, regs.injective.eq_iff]
      _ = afterRead (CombineValue.rangeRegisters regs).count := by
        rw [hrestoreOutside]
        simp [coordinateIndex, CombineValue.rangeRegisters,
          regs.injective.eq_iff]
      _ = afterSave (CombineValue.rangeRegisters regs).count :=
        hreadPost.count_eq
      _ = afterBankIndex (CombineValue.rangeRegisters regs).count := by
        rw [hsaveOutside]
        simp [CombineValue.rangeRegisters, regs.injective.eq_iff]
      _ = afterAssignment
          (CombineValue.rangeRegisters regs).count := by
        rw [hbankIndexOutside]
        simp [bankCoordinateFootprint, coordinateIndex,
          CombineValue.rangeRegisters, regs.injective.eq_iff]
      _ = afterDigitIndex
          (CombineValue.rangeRegisters regs).count :=
        hassignmentPost.count_eq
      _ = afterDecrement
          (CombineValue.rangeRegisters regs).count := by
        rw [hdigitIndexOutside]
        simp [assignmentIndexFootprint, coordinateIndex,
          CombineValue.rangeRegisters, regs.injective.eq_iff]
      _ = store (CombineValue.rangeRegisters regs).count := by
        simp [afterDecrement, Basic.exec, basisChunkCursor,
          basisChunkRangeRegisters, CombineValue.rangeRegisters,
          regs.injective.eq_iff]
  refine ⟨afterCount, hrun, ?_⟩
  exact
    { context := hcountContext
      selected_eq := by
        simpa [selected, payloadWidth, fanIn] using hcountSelected
      point_eq := by
        simpa [point] using hcountPoint
      coordinate_eq := hcountCoordinate
      innerCount_eq := by
        simpa [radix, payloadWidth, fanIn] using hcountExact
      basis_eq := hcountBasis
      packed_eq := hcountPacked
      accumulator_eq := hcountAccumulator
      remaining_eq := hcountRemaining
      modulus_eq := hcountModulus
      modulusPred_eq := hcountModulusPred
      one_eq := hcountOne
      count_eq := hcountOuterCount }

set_option maxHeartbeats 0 in
private theorem basisChunkBody_runs
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
    (child :
      Fin (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount))
    (chunk :
      Fin
        (PrimeGrouped.Logarithmic.chunkCount
          (NeighborhoodExecutableEvaluation.payloadWidth
            tm instanceData.blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount)))
    (store : Store) (code accumulator : ℕ)
    (hcontext :
      ComputationFrameContext regs instanceData frame tape slot interval
        logicalBank store)
    (hremaining :
      store (CombineValue.rangeRegisters regs).remaining = code)
    (hmodulus :
      store (CombineValue.rangeRegisters regs).modulus =
        NeighborhoodScheduler.fieldModulus instanceData)
    (hmodulusPred :
      store (CombineValue.rangeRegisters regs).modulusPred =
        NeighborhoodScheduler.fieldModulus instanceData - 1)
    (hone :
      store (CombineValue.rangeRegisters regs).one = 1)
    (haccumulator : store (basisValue regs) = accumulator)
    (hcursor :
      store (basisChunkCursor regs) = chunk.val + 1) :
    ∃ final,
      Runs (basisChunkBody regs child) store final ∧
      BasisPost regs
        (PrimeField.Runtime.mul
          (NeighborhoodScheduler.fieldModulus instanceData)
          (NeighborhoodExecutableEvaluation.Residue.chunkBasisValue
            (NeighborhoodExecutableEvaluation.payloadWidth
              tm instanceData.blockLength)
            (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount)
            (GroupedExtension.Evaluation.chunkAssignmentOfCode
              finProdFinEquiv
              (PrimeGrouped.Logarithmic.chunkBits
                (NeighborhoodExecutableEvaluation.payloadWidth
                  tm instanceData.blockLength)
                (NeighborhoodExecutableEvaluation.graphFanIn
                  workTapeCount))
              code (child, chunk))
            (computationArguments frame logicalBank child chunk))
          accumulator)
        code store final ∧
      ComputationFrameContext regs instanceData frame tape slot interval
        logicalBank final ∧
      final (basisChunkCursor regs) = chunk.val := by
  let payloadWidth :=
    NeighborhoodExecutableEvaluation.payloadWidth
      tm instanceData.blockLength
  let fanIn :=
    NeighborhoodExecutableEvaluation.graphFanIn workTapeCount
  let modulus := NeighborhoodScheduler.fieldModulus instanceData
  let radix :=
    PrimeGrouped.Logarithmic.domainSize payloadWidth fanIn
  let inner := basisChunkRangeRegisters regs
  let selected :=
    GroupedExtension.Evaluation.chunkAssignmentOfCode
      finProdFinEquiv
      (PrimeGrouped.Logarithmic.chunkBits payloadWidth fanIn)
      code (child, chunk)
  let point := computationArguments frame logicalBank child chunk
  obtain ⟨afterPrepare, hprepareRun, hpreparePost⟩ :=
    basisChunkPrepare_runs_internal regs instanceData frame tape slot interval
      logicalBank child chunk store code accumulator hcontext
      hremaining hmodulus hmodulusPred hone haccumulator hcursor
  have hprepareModulus :
      afterPrepare inner.modulus = modulus := by
    simpa [inner, basisChunkRangeRegisters, modulus,
      CombineValue.rangeRegisters] using
      hpreparePost.modulus_eq.trans hmodulus
  have hprepareModulusPred :
      afterPrepare inner.modulusPred = modulus - 1 := by
    simpa [inner, basisChunkRangeRegisters, modulus,
      CombineValue.rangeRegisters] using
      hpreparePost.modulusPred_eq.trans hmodulusPred
  have hprepareCount :
      afterPrepare inner.count = radix := by
    simpa [inner, radix, payloadWidth, fanIn] using
      hpreparePost.innerCount_eq
  have hprepareSelected :
      afterPrepare (CombineValue.rangeRegisters regs).term =
        PrimeGrouped.Logarithmic.chunkCodeNat selected := by
    simpa [selected, payloadWidth, fanIn] using
      hpreparePost.selected_eq
  have hpreparePoint :
      afterPrepare (coordinateBankRegisters regs).result = point := by
    simpa [point] using hpreparePost.point_eq
  obtain ⟨afterRange, hrangeRun, hrangePost, _hselectedRange,
      _hpointRange⟩ :=
    basisChunkRange_runs_internal regs payloadWidth fanIn selected point
      afterPrepare hprepareModulus hprepareModulusPred hprepareCount
      hprepareSelected hpreparePoint
  have hrangeBank :
      afterRange regs.layout.bank =
        afterPrepare regs.layout.bank := by
    apply RAM.Structured.Footprint.runs_eq_outside
      (basisChunkRange_precise_writesWithin_internal regs) hrangeRun
    change regs.index 33 ∉ basisChunkFootprint regs
    simp [basisChunkFootprint, regs.injective.eq_iff]
  have hrangeContext :
      ComputationFrameContext regs instanceData frame tape slot interval
        logicalBank afterRange :=
    frameContext_transport_combineScratch_internal
      regs instanceData frame tape slot interval
      logicalBank hpreparePost.context
      (basisChunkRange_writesWithin_internal regs) hrangeRun hrangeBank
  have hrangeOutside :
      ∀ address, address ∉ basisChunkFootprint regs →
        afterRange address = afterPrepare address := by
    intro address haddress
    exact RAM.Structured.Footprint.runs_eq_outside
      (basisChunkRange_precise_writesWithin_internal regs) hrangeRun
      haddress
  have hrangeBasis :
      afterRange (basisValue regs) = accumulator := by
    rw [hrangeOutside (basisValue regs)
      (by
        simp [basisChunkFootprint, basisValue,
          regs.injective.eq_iff])]
    exact hpreparePost.basis_eq
  have hrangeCoordinate :
      afterRange (coordinateIndex regs) = chunk.val := by
    rw [hrangeOutside (coordinateIndex regs)
      (by
        simp [basisChunkFootprint, coordinateIndex,
          regs.injective.eq_iff])]
    exact hpreparePost.coordinate_eq
  have hchunkValue :
      afterRange inner.accumulator =
        NeighborhoodExecutableEvaluation.Residue.chunkBasisValue
          payloadWidth fanIn selected point :=
    hrangePost.accumulator_eq.trans
      (chunkRange_eq_internal payloadWidth fanIn point selected)
  have hmodulusPos : 0 < modulus := by
    simpa [modulus, NeighborhoodScheduler.fieldModulus] using
      CombineValue.fieldModulus_pos payloadWidth fanIn
  have hchunkLt :
      NeighborhoodExecutableEvaluation.Residue.chunkBasisValue
          payloadWidth fanIn selected point <
        modulus := by
    unfold NeighborhoodExecutableEvaluation.Residue.chunkBasisValue
    simpa [modulus, NeighborhoodScheduler.fieldModulus] using
      productRange_lt_internal
        (modulus := modulus) hmodulusPos
        (fun current =>
          NeighborhoodExecutableEvaluation.Residue.lagrangeFactor
            payloadWidth fanIn selected
            (GroupedExtension.Evaluation.chunkOfCode
              (PrimeGrouped.Logarithmic.chunkBits payloadWidth fanIn)
              current)
            point)
        radix
  have hmulModulus :
      afterRange (basisAccumulatorRegisters regs).modulus =
        modulus := by
    simpa [basisAccumulatorRegisters, inner, modulus,
      NeighborhoodScheduler.fieldModulus] using
      hrangePost.modulus_eq
  have hmulModulusPred :
      afterRange (basisAccumulatorRegisters regs).modulusPred =
        modulus - 1 := by
    simpa [basisAccumulatorRegisters, inner, modulus,
      NeighborhoodScheduler.fieldModulus] using
      hrangePost.modulusPred_eq
  let product :=
    PrimeField.Runtime.mul modulus
      (NeighborhoodExecutableEvaluation.Residue.chunkBasisValue
        payloadWidth fanIn selected point)
      accumulator
  have hproductEq :
      (afterRange inner.accumulator *
          afterRange (basisValue regs)) %
          modulus =
        product := by
    rw [hchunkValue, hrangeBasis]
    simp [product, PrimeField.Runtime.mul,
      PrimeField.Runtime.mulInput, PrimeField.Runtime.normalize,
      Nat.mod_eq_of_lt hchunkLt]
  have hmul :=
    RuntimeArithmetic.mulMod_runs (basisAccumulatorRegisters regs)
      inner.accumulator (basisValue regs) afterRange modulus
      hmodulusPos hmulModulus hmulModulusPred
  rw [hproductEq] at hmul
  let afterMul :=
    RuntimeArithmetic.reduceResultStore
      (basisAccumulatorRegisters regs) product afterRange
  change
    Runs
      (RuntimeArithmetic.mulMod (basisAccumulatorRegisters regs)
        inner.accumulator (basisValue regs))
      afterRange afterMul at hmul
  have hmulOutside :
      ∀ address, address ∉ basisAccumulatorFootprint regs →
        afterMul address = afterRange address := by
    intro address haddress
    exact RAM.Structured.Footprint.runs_eq_outside
      (basisAccumulatorMul_precise_writesWithin_internal regs) hmul
      haddress
  have hmulBank :
      afterMul regs.layout.bank = afterRange regs.layout.bank := by
    apply hmulOutside
    change regs.index 33 ∉ basisAccumulatorFootprint regs
    simp [basisAccumulatorFootprint, basisValue,
      regs.injective.eq_iff]
  have hmulContext :
      ComputationFrameContext regs instanceData frame tape slot interval
        logicalBank afterMul :=
    frameContext_transport_combineScratch_internal
      regs instanceData frame tape slot interval logicalBank
      hrangeContext (basisAccumulatorMul_writesWithin_internal regs)
      hmul hmulBank
  have hmulCoordinate :
      afterMul (coordinateIndex regs) = chunk.val := by
    rw [hmulOutside (coordinateIndex regs)
      (by
        simp [basisAccumulatorFootprint, coordinateIndex, basisValue,
          regs.injective.eq_iff])]
    exact hrangeCoordinate
  obtain ⟨final, hrestoreRun, hrestoreValue, hrestoreOutside⟩ :=
    copy_runs_internal (basisChunkCursor regs) (coordinateIndex regs)
      afterMul (regs.injective.ne (by decide))
  have hcursorMem :
      basisChunkCursor regs ∈
        CombineValue.combineScratchFootprint regs := by
    exact Finset.mem_image.mpr
      ⟨(1 : Fin 19), Finset.mem_univ _, rfl⟩
  have hrestoreWrites :
      RAM.Structured.Footprint.CmdWritesWithin
        (CombineValue.combineScratchFootprint regs)
        (copy (basisChunkCursor regs) (coordinateIndex regs)) := by
    simpa [copy,
      RAM.Structured.Footprint.CmdWritesWithin,
      RAM.Structured.Footprint.BasicWritesWithin] using
      And.intro hcursorMem hcursorMem
  have hrestoreBank :
      final regs.layout.bank = afterMul regs.layout.bank := by
    apply hrestoreOutside
    change regs.index 33 ≠ basisChunkCursor regs
    simp [basisChunkCursor, basisChunkRangeRegisters,
      regs.injective.eq_iff]
  have hfinalContext :
      ComputationFrameContext regs instanceData frame tape slot interval
        logicalBank final :=
    frameContext_transport_combineScratch_internal
      regs instanceData frame tape slot interval logicalBank
      hmulContext hrestoreWrites hrestoreRun hrestoreBank
  have hrun :
      Runs (basisChunkBody regs child) store final := by
    apply Runs.seq
    · change Runs (basisChunkCore regs child) store afterMul
      apply Runs.seq
      · change
          Runs (basisChunkRangeStage regs child) store afterRange
        exact Runs.seq hprepareRun hrangeRun
      · exact hmul
    · exact hrestoreRun
  refine ⟨final, hrun, ?_, hfinalContext, ?_⟩
  · exact
      { basis_eq := by
          rw [hrestoreOutside (basisValue regs)
            (by
              simp [basisChunkCursor, basisChunkRangeRegisters,
                basisValue, regs.injective.eq_iff])]
          change afterMul (basisAccumulatorRegisters regs).value = _
          rw [show afterMul (basisAccumulatorRegisters regs).value =
              product by
            simp [afterMul, RuntimeArithmetic.reduceResultStore,
              (basisAccumulatorRegisters regs).value_ne_test]]
        packed_eq := by
          rw [hrestoreOutside (packedValue regs)
            (by
              simp [basisChunkCursor, basisChunkRangeRegisters,
                packedValue, regs.injective.eq_iff])]
          rw [hmulOutside (packedValue regs)
            (by
              simp [basisAccumulatorFootprint, packedValue, basisValue,
                regs.injective.eq_iff])]
          rw [hrangeOutside (packedValue regs)
            (by
              simp [basisChunkFootprint, packedValue,
                regs.injective.eq_iff])]
          exact hpreparePost.packed_eq
        accumulator_eq := by
          rw [hrestoreOutside
            (CombineValue.rangeRegisters regs).accumulator
            (by
              simp [basisChunkCursor, basisChunkRangeRegisters,
                CombineValue.rangeRegisters, regs.injective.eq_iff])]
          rw [hmulOutside
            (CombineValue.rangeRegisters regs).accumulator
            (by
              simp [basisAccumulatorFootprint,
                CombineValue.rangeRegisters, basisValue,
                regs.injective.eq_iff])]
          rw [hrangeOutside
            (CombineValue.rangeRegisters regs).accumulator
            (by
              simp [basisChunkFootprint,
                CombineValue.rangeRegisters, regs.injective.eq_iff])]
          exact hpreparePost.accumulator_eq
        remaining_eq := by
          rw [hrestoreOutside
            (CombineValue.rangeRegisters regs).remaining
            (by
              simp [basisChunkCursor, basisChunkRangeRegisters,
                CombineValue.rangeRegisters, regs.injective.eq_iff])]
          rw [hmulOutside
            (CombineValue.rangeRegisters regs).remaining
            (by
              simp [basisAccumulatorFootprint,
                CombineValue.rangeRegisters, basisValue,
                regs.injective.eq_iff])]
          rw [hrangeOutside
            (CombineValue.rangeRegisters regs).remaining
            (by
              simp [basisChunkFootprint,
                CombineValue.rangeRegisters, regs.injective.eq_iff])]
          exact hpreparePost.remaining_eq
        modulus_eq := by
          rw [hrestoreOutside
            (CombineValue.rangeRegisters regs).modulus
            (by
              simp [basisChunkCursor, basisChunkRangeRegisters,
                CombineValue.rangeRegisters, regs.injective.eq_iff])]
          rw [hmulOutside
            (CombineValue.rangeRegisters regs).modulus
            (by
              simp [basisAccumulatorFootprint,
                CombineValue.rangeRegisters, basisValue,
                regs.injective.eq_iff])]
          simpa [inner, basisChunkRangeRegisters,
            CombineValue.rangeRegisters, modulus] using
            hrangePost.modulus_eq.trans hmodulus.symm
        modulusPred_eq := by
          rw [hrestoreOutside
            (CombineValue.rangeRegisters regs).modulusPred
            (by
              simp [basisChunkCursor, basisChunkRangeRegisters,
                CombineValue.rangeRegisters, regs.injective.eq_iff])]
          rw [hmulOutside
            (CombineValue.rangeRegisters regs).modulusPred
            (by
              simp [basisAccumulatorFootprint,
                CombineValue.rangeRegisters, basisValue,
                regs.injective.eq_iff])]
          simpa [inner, basisChunkRangeRegisters,
            CombineValue.rangeRegisters, modulus] using
            hrangePost.modulusPred_eq.trans hmodulusPred.symm
        one_eq := by
          rw [hrestoreOutside
            (CombineValue.rangeRegisters regs).one
            (by
              simp [basisChunkCursor, basisChunkRangeRegisters,
                CombineValue.rangeRegisters, regs.injective.eq_iff])]
          rw [hmulOutside
            (CombineValue.rangeRegisters regs).one
            (by
              simp [basisAccumulatorFootprint,
                CombineValue.rangeRegisters, basisValue,
                regs.injective.eq_iff])]
          simpa [inner, basisChunkRangeRegisters,
            CombineValue.rangeRegisters] using
            hrangePost.one_eq.trans hone.symm
        count_eq := by
          rw [hrestoreOutside
            (CombineValue.rangeRegisters regs).count
            (by
              simp [basisChunkCursor, basisChunkRangeRegisters,
                CombineValue.rangeRegisters, regs.injective.eq_iff])]
          rw [hmulOutside
            (CombineValue.rangeRegisters regs).count
            (by
              simp [basisAccumulatorFootprint,
                CombineValue.rangeRegisters, basisValue,
                regs.injective.eq_iff])]
          rw [hrangeOutside
            (CombineValue.rangeRegisters regs).count
            (by
              simp [basisChunkFootprint,
                CombineValue.rangeRegisters, regs.injective.eq_iff])]
          exact hpreparePost.count_eq }
  · exact hrestoreValue.trans hmulCoordinate

private def chunkFactorNat {fanIn chunkCount : ℕ}
    (hcount : 0 < chunkCount)
    (factor : Fin fanIn → Fin chunkCount → ℕ)
    (child : Fin fanIn) (chunk : ℕ) : ℕ :=
  factor child
    ⟨chunk % chunkCount, Nat.mod_lt chunk hcount⟩

private def basisChildrenFold {fanIn chunkCount : ℕ}
    (modulus : ℕ) (hcount : 0 < chunkCount)
    (factor : Fin fanIn → Fin chunkCount → ℕ) :
    List (Fin fanIn) → ℕ → ℕ
  | [], accumulator => accumulator
  | child :: children, accumulator =>
      NeighborhoodExecutableEvaluation.Residue.foldProduct modulus
        (chunkFactorNat hcount factor child) chunkCount
        (basisChildrenFold modulus hcount factor children accumulator)

private theorem runtimeMul_eq (modulus first second : ℕ) :
    PrimeField.Runtime.mul modulus first second =
      first * second % modulus := by
  simp [PrimeField.Runtime.mul, PrimeField.Runtime.mulInput,
    PrimeField.Runtime.normalize, Nat.mul_mod]

private theorem foldProduct_lt
    (modulus : ℕ) (term : ℕ → ℕ) (count accumulator : ℕ)
    (hmodulus : 0 < modulus) (haccumulator : accumulator < modulus) :
    NeighborhoodExecutableEvaluation.Residue.foldProduct
        modulus term count accumulator <
      modulus := by
  induction count generalizing accumulator with
  | zero => exact haccumulator
  | succ count ih =>
      rw [NeighborhoodExecutableEvaluation.Residue.foldProduct]
      exact ih _ (PrimeField.Runtime.mul_lt hmodulus)

private theorem foldProduct_eq_prod_mod
    (modulus : ℕ) (term : ℕ → ℕ) (count accumulator : ℕ)
    (hmodulus : 0 < modulus) (haccumulator : accumulator < modulus) :
    NeighborhoodExecutableEvaluation.Residue.foldProduct
        modulus term count accumulator =
      ((List.range count).map term).prod * accumulator %
        modulus := by
  induction count generalizing accumulator with
  | zero =>
      simp [NeighborhoodExecutableEvaluation.Residue.foldProduct,
        Nat.mod_eq_of_lt haccumulator]
  | succ count ih =>
      rw [NeighborhoodExecutableEvaluation.Residue.foldProduct]
      rw [ih _ (PrimeField.Runtime.mul_lt hmodulus)]
      rw [List.range_succ, List.map_append, List.prod_append]
      simp only [List.map_singleton, List.prod_singleton]
      rw [runtimeMul_eq, Nat.mul_mod_mod, Nat.mul_assoc]

private theorem basisChildrenFold_lt {fanIn chunkCount : ℕ}
    (modulus : ℕ) (hcount : 0 < chunkCount)
    (factor : Fin fanIn → Fin chunkCount → ℕ)
    (children : List (Fin fanIn)) (accumulator : ℕ)
    (hmodulus : 0 < modulus) (haccumulator : accumulator < modulus) :
    basisChildrenFold modulus hcount factor children accumulator <
      modulus := by
  induction children with
  | nil => exact haccumulator
  | cons child children ih =>
      unfold basisChildrenFold
      exact foldProduct_lt modulus _ chunkCount _ hmodulus ih

private theorem chunkFactorNat_fin {fanIn chunkCount : ℕ}
    (hcount : 0 < chunkCount)
    (factor : Fin fanIn → Fin chunkCount → ℕ)
    (child : Fin fanIn) (chunk : Fin chunkCount) :
    chunkFactorNat hcount factor child chunk.val =
      factor child chunk := by
  simp [chunkFactorNat, Nat.mod_eq_of_lt chunk.isLt]

private theorem range_chunkFactorNat_prod {fanIn chunkCount : ℕ}
    (hcount : 0 < chunkCount)
    (factor : Fin fanIn → Fin chunkCount → ℕ)
    (child : Fin fanIn) :
    ((List.range chunkCount).map
        (chunkFactorNat hcount factor child)).prod =
      ∏ chunk : Fin chunkCount, factor child chunk := by
  rw [← List.prod_toFinset _ List.nodup_range]
  simp only [List.toFinset_range]
  rw [← Fin.prod_univ_eq_prod_range
    (chunkFactorNat hcount factor child) chunkCount]
  apply Finset.prod_congr rfl
  intro chunk _
  rw [chunkFactorNat_fin]

private theorem basisChildrenFold_eq_prod {fanIn chunkCount : ℕ}
    (modulus : ℕ) (hcount : 0 < chunkCount)
    (factor : Fin fanIn → Fin chunkCount → ℕ)
    (children : List (Fin fanIn)) (accumulator : ℕ)
    (hmodulus : 0 < modulus) (haccumulator : accumulator < modulus) :
    basisChildrenFold modulus hcount factor children accumulator =
      (children.map fun child =>
        ∏ chunk : Fin chunkCount, factor child chunk).prod *
        accumulator % modulus := by
  induction children generalizing accumulator with
  | nil =>
      simp [basisChildrenFold, Nat.mod_eq_of_lt haccumulator]
  | cons child children ih =>
      rw [basisChildrenFold]
      rw [foldProduct_eq_prod_mod _ _ _ _ hmodulus
        (basisChildrenFold_lt modulus hcount factor children
          accumulator hmodulus haccumulator)]
      rw [range_chunkFactorNat_prod, ih accumulator haccumulator]
      simp only [List.map_cons, List.prod_cons]
      rw [Nat.mul_mod_mod, Nat.mul_assoc]

private theorem productList_eq_prod_mod
    (modulus : ℕ) (values : List ℕ) :
    NeighborhoodExecutableEvaluation.Residue.productList
        modulus values =
      values.prod % modulus := by
  induction values with
  | nil =>
      simp [NeighborhoodExecutableEvaluation.Residue.productList,
        PrimeField.Runtime.normalize]
  | cons value values ih =>
      rw [NeighborhoodExecutableEvaluation.Residue.productList, ih]
      rw [runtimeMul_eq, Nat.mul_mod_mod]
      rfl

private theorem basisChildrenFold_eq_productList
    {fanIn chunkCount : ℕ}
    (modulus : ℕ) (hcount : 0 < chunkCount)
    (factor : Fin fanIn → Fin chunkCount → ℕ)
    (hmodulus : 0 < modulus) :
    basisChildrenFold modulus hcount factor
        (List.finRange fanIn)
        (PrimeField.Runtime.normalize modulus 1) =
      NeighborhoodExecutableEvaluation.Residue.productList modulus
        ((BooleanExtension.Evaluation.coordinates
          (finProdFinEquiv :
            Fin fanIn × Fin chunkCount ≃
              Fin (fanIn * chunkCount))).map
          fun coordinate => factor coordinate.1 coordinate.2) := by
  rw [basisChildrenFold_eq_prod _ _ _ _ _ hmodulus
    (PrimeField.Runtime.normalize_lt hmodulus),
    productList_eq_prod_mod]
  have hchildren :
      ((List.finRange fanIn).map fun child =>
        ∏ chunk : Fin chunkCount, factor child chunk).prod =
      ∏ child : Fin fanIn, ∏ chunk : Fin chunkCount,
        factor child chunk := by
    rw [← List.prod_toFinset _
      (List.nodup_finRange fanIn)]
    simp
  have hcoordinates :
      (((BooleanExtension.Evaluation.coordinates
        (finProdFinEquiv :
          Fin fanIn × Fin chunkCount ≃
            Fin (fanIn * chunkCount))).map
        fun coordinate => factor coordinate.1 coordinate.2).prod) =
      ∏ coordinate : Fin fanIn × Fin chunkCount,
        factor coordinate.1 coordinate.2 := by
    rw [← List.prod_toFinset _
      (BooleanExtension.Evaluation.coordinates_nodup
        (finProdFinEquiv :
          Fin fanIn × Fin chunkCount ≃
            Fin (fanIn * chunkCount)))]
    rw [BooleanExtension.Evaluation.coordinates_toFinset]
  rw [hchildren, hcoordinates, Fintype.prod_prod_type]
  simp [PrimeField.Runtime.normalize]

private def computationBasisFactor
    {tm : TM workTapeCount}
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (code : ℕ)
    (child :
      Fin
        (NeighborhoodExecutableEvaluation.graphFanIn
          workTapeCount))
    (chunk :
      Fin
        (PrimeGrouped.Logarithmic.chunkCount
          (NeighborhoodExecutableEvaluation.payloadWidth
            tm instanceData.blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn
            workTapeCount))) : ℕ :=
  NeighborhoodExecutableEvaluation.Residue.chunkBasisValue
    (NeighborhoodExecutableEvaluation.payloadWidth
      tm instanceData.blockLength)
    (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount)
    (GroupedExtension.Evaluation.chunkAssignmentOfCode
      finProdFinEquiv
      (PrimeGrouped.Logarithmic.chunkBits
        (NeighborhoodExecutableEvaluation.payloadWidth
          tm instanceData.blockLength)
        (NeighborhoodExecutableEvaluation.graphFanIn
          workTapeCount))
      code (child, chunk))
    (computationArguments frame logicalBank child chunk)

set_option maxHeartbeats 0 in
private theorem basisChildLoop_runs
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
    (child :
      Fin
        (NeighborhoodExecutableEvaluation.graphFanIn
          workTapeCount))
    (hchunkCount :
      0 <
        PrimeGrouped.Logarithmic.chunkCount
          (NeighborhoodExecutableEvaluation.payloadWidth
            tm instanceData.blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn
            workTapeCount))
    (remaining : ℕ)
    (hremainingBound :
      remaining ≤
        PrimeGrouped.Logarithmic.chunkCount
          (NeighborhoodExecutableEvaluation.payloadWidth
            tm instanceData.blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn
            workTapeCount))
    (store : Store) (code accumulator : ℕ)
    (hcontext :
      ComputationFrameContext regs instanceData frame tape slot interval
        logicalBank store)
    (hremaining :
      store (CombineValue.rangeRegisters regs).remaining = code)
    (hmodulus :
      store (CombineValue.rangeRegisters regs).modulus =
        NeighborhoodScheduler.fieldModulus instanceData)
    (hmodulusPred :
      store (CombineValue.rangeRegisters regs).modulusPred =
        NeighborhoodScheduler.fieldModulus instanceData - 1)
    (hone :
      store (CombineValue.rangeRegisters regs).one = 1)
    (haccumulator : store (basisValue regs) = accumulator)
    (hcursor :
      store (basisChunkCursor regs) = remaining) :
    ∃ final,
      Runs
          (.whileNonzero (basisChunkCursor regs)
            (basisChunkBody regs child))
          store final ∧
      BasisPost regs
        (NeighborhoodExecutableEvaluation.Residue.foldProduct
          (NeighborhoodScheduler.fieldModulus instanceData)
          (chunkFactorNat hchunkCount
            (computationBasisFactor instanceData frame logicalBank
              code)
            child)
          remaining accumulator)
        code store final ∧
      ComputationFrameContext regs instanceData frame tape slot interval
        logicalBank final ∧
      final (basisChunkCursor regs) = 0 := by
  induction remaining generalizing store accumulator with
  | zero =>
      refine ⟨store, Runs.whileZero hcursor, ?_, hcontext, hcursor⟩
      exact
        { basis_eq := by
            simpa [
              NeighborhoodExecutableEvaluation.Residue.foldProduct]
              using haccumulator
          packed_eq := rfl
          accumulator_eq := rfl
          remaining_eq := hremaining
          modulus_eq := rfl
          modulusPred_eq := rfl
          one_eq := rfl
          count_eq := rfl }
  | succ remaining ih =>
      have hchunkLt :
          remaining <
            PrimeGrouped.Logarithmic.chunkCount
              (NeighborhoodExecutableEvaluation.payloadWidth
                tm instanceData.blockLength)
              (NeighborhoodExecutableEvaluation.graphFanIn
                workTapeCount) := by
        omega
      let chunk :
          Fin
            (PrimeGrouped.Logarithmic.chunkCount
              (NeighborhoodExecutableEvaluation.payloadWidth
                tm instanceData.blockLength)
              (NeighborhoodExecutableEvaluation.graphFanIn
                workTapeCount)) :=
        ⟨remaining, hchunkLt⟩
      let nextAccumulator :=
        PrimeField.Runtime.mul
          (NeighborhoodScheduler.fieldModulus instanceData)
          (computationBasisFactor instanceData frame logicalBank
            code child chunk)
          accumulator
      obtain ⟨afterBody, hbodyRun, hbodyPost, hbodyContext,
          hbodyCursor⟩ :=
        basisChunkBody_runs regs instanceData frame tape slot interval
          logicalBank child chunk store code accumulator hcontext
          hremaining hmodulus hmodulusPred hone haccumulator
          (by simpa [chunk] using hcursor)
      have hbodyBasis :
          afterBody (basisValue regs) = nextAccumulator := by
        simpa [nextAccumulator, computationBasisFactor] using
          hbodyPost.basis_eq
      obtain ⟨final, hloopRun, hloopPost, hfinalContext,
          hfinalCursor⟩ :=
        ih (by omega) afterBody nextAccumulator hbodyContext
          hbodyPost.remaining_eq
          (hbodyPost.modulus_eq.trans hmodulus)
          (hbodyPost.modulusPred_eq.trans hmodulusPred)
          (hbodyPost.one_eq.trans hone)
          hbodyBasis hbodyCursor
      have hnonzero :
          store (basisChunkCursor regs) ≠ 0 := by
        rw [hcursor]
        omega
      have hfactor :
          chunkFactorNat hchunkCount
              (computationBasisFactor instanceData frame logicalBank
                code)
              child remaining =
            computationBasisFactor instanceData frame logicalBank
              code child chunk := by
        unfold chunkFactorNat
        congr 2
        exact Nat.mod_eq_of_lt hchunkLt
      refine
        ⟨final, Runs.whileNonzero hnonzero hbodyRun hloopRun,
          ?_, hfinalContext, hfinalCursor⟩
      exact
        { basis_eq := by
            rw [
              NeighborhoodExecutableEvaluation.Residue.foldProduct,
              hfactor]
            simpa [nextAccumulator] using hloopPost.basis_eq
          packed_eq :=
            hloopPost.packed_eq.trans hbodyPost.packed_eq
          accumulator_eq :=
            hloopPost.accumulator_eq.trans
              hbodyPost.accumulator_eq
          remaining_eq := hloopPost.remaining_eq
          modulus_eq :=
            hloopPost.modulus_eq.trans hbodyPost.modulus_eq
          modulusPred_eq :=
            hloopPost.modulusPred_eq.trans
              hbodyPost.modulusPred_eq
          one_eq :=
            hloopPost.one_eq.trans hbodyPost.one_eq
          count_eq :=
            hloopPost.count_eq.trans hbodyPost.count_eq }

private theorem semanticChunkCount_pos
    {tm : TM workTapeCount}
    (instanceData : NeighborhoodProgram.ResidueInstance tm) :
    0 <
      PrimeGrouped.Logarithmic.chunkCount
        (NeighborhoodExecutableEvaluation.payloadWidth
          tm instanceData.blockLength)
        (NeighborhoodExecutableEvaluation.graphFanIn
          workTapeCount) := by
  apply
    GroupedExtension.LogarithmicParameters.chunkCount_pos
  change
    0 <
      ComputationGraph.CompactEncoding.width
        instanceData.blockLength tm.Q
  rw [ComputationGraph.CompactEncoding.width_eq]
  have hcard : 0 < Fintype.card tm.Q :=
    Fintype.card_pos_iff.mpr ⟨tm.qstart⟩
  omega

set_option maxHeartbeats 0 in
private theorem basisChildCommand_runs
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
    (child :
      Fin
        (NeighborhoodExecutableEvaluation.graphFanIn
          workTapeCount))
    (store : Store) (code accumulator : ℕ)
    (hcontext :
      ComputationFrameContext regs instanceData frame tape slot interval
        logicalBank store)
    (hremaining :
      store (CombineValue.rangeRegisters regs).remaining = code)
    (hmodulus :
      store (CombineValue.rangeRegisters regs).modulus =
        NeighborhoodScheduler.fieldModulus instanceData)
    (hmodulusPred :
      store (CombineValue.rangeRegisters regs).modulusPred =
        NeighborhoodScheduler.fieldModulus instanceData - 1)
    (hone :
      store (CombineValue.rangeRegisters regs).one = 1)
    (haccumulator : store (basisValue regs) = accumulator) :
    ∃ final,
      Runs (basisChildCommand regs child) store final ∧
      BasisPost regs
        (NeighborhoodExecutableEvaluation.Residue.foldProduct
          (NeighborhoodScheduler.fieldModulus instanceData)
          (chunkFactorNat (semanticChunkCount_pos instanceData)
            (computationBasisFactor instanceData frame logicalBank
              code)
            child)
          (PrimeGrouped.Logarithmic.chunkCount
            (NeighborhoodExecutableEvaluation.payloadWidth
              tm instanceData.blockLength)
            (NeighborhoodExecutableEvaluation.graphFanIn
              workTapeCount))
          accumulator)
        code store final ∧
      ComputationFrameContext regs instanceData frame tape slot interval
        logicalBank final := by
  let chunkCount :=
    PrimeGrouped.Logarithmic.chunkCount
      (NeighborhoodExecutableEvaluation.payloadWidth
        tm instanceData.blockLength)
      (NeighborhoodExecutableEvaluation.graphFanIn
        workTapeCount)
  obtain ⟨afterCopy, hcopyRun, hcopyValue, hcopyOutside⟩ :=
    copy_runs_internal (basisChunkCursor regs)
      (Layout.chunkCount regs) store
      (regs.injective.ne (by decide))
  have hcopyCursor :
      afterCopy (basisChunkCursor regs) = chunkCount :=
    hcopyValue.trans
      hcontext.computation.parameters.chunkCount_eq
  have hcursorMem :
      basisChunkCursor regs ∈
        CombineValue.combineScratchFootprint regs :=
    Finset.mem_image.mpr
      ⟨(1 : Fin 19), Finset.mem_univ _, rfl⟩
  have hcopyWrites :
      RAM.Structured.Footprint.CmdWritesWithin
        (CombineValue.combineScratchFootprint regs)
        (copy (basisChunkCursor regs)
          (Layout.chunkCount regs)) := by
    simpa [copy,
      RAM.Structured.Footprint.CmdWritesWithin,
      RAM.Structured.Footprint.BasicWritesWithin] using
      And.intro hcursorMem hcursorMem
  have hcopyBank :
      afterCopy regs.layout.bank = store regs.layout.bank := by
    apply hcopyOutside
    change regs.index 33 ≠ basisChunkCursor regs
    simp [basisChunkCursor, basisChunkRangeRegisters,
      regs.injective.eq_iff]
  have hcopyContext :
      ComputationFrameContext regs instanceData frame tape slot interval
        logicalBank afterCopy :=
    frameContext_transport_combineScratch_internal
      regs instanceData frame tape slot interval logicalBank
      hcontext hcopyWrites hcopyRun hcopyBank
  have hcopyBasis :
      afterCopy (basisValue regs) = accumulator := by
    rw [hcopyOutside (basisValue regs)
      (by
        simp [basisChunkCursor, basisChunkRangeRegisters,
          basisValue, regs.injective.eq_iff])]
    exact haccumulator
  have hcopyRemaining :
      afterCopy (CombineValue.rangeRegisters regs).remaining =
        code := by
    rw [hcopyOutside
      (CombineValue.rangeRegisters regs).remaining
      (by
        simp [basisChunkCursor, basisChunkRangeRegisters,
          CombineValue.rangeRegisters, regs.injective.eq_iff])]
    exact hremaining
  have hcopyModulus :
      afterCopy (CombineValue.rangeRegisters regs).modulus =
        NeighborhoodScheduler.fieldModulus instanceData := by
    rw [hcopyOutside
      (CombineValue.rangeRegisters regs).modulus
      (by
        simp [basisChunkCursor, basisChunkRangeRegisters,
          CombineValue.rangeRegisters, regs.injective.eq_iff])]
    exact hmodulus
  have hcopyModulusPred :
      afterCopy (CombineValue.rangeRegisters regs).modulusPred =
        NeighborhoodScheduler.fieldModulus instanceData - 1 := by
    rw [hcopyOutside
      (CombineValue.rangeRegisters regs).modulusPred
      (by
        simp [basisChunkCursor, basisChunkRangeRegisters,
          CombineValue.rangeRegisters, regs.injective.eq_iff])]
    exact hmodulusPred
  have hcopyOne :
      afterCopy (CombineValue.rangeRegisters regs).one = 1 := by
    rw [hcopyOutside
      (CombineValue.rangeRegisters regs).one
      (by
        simp [basisChunkCursor, basisChunkRangeRegisters,
          CombineValue.rangeRegisters, regs.injective.eq_iff])]
    exact hone
  obtain ⟨final, hloopRun, hloopPost, hfinalContext, _⟩ :=
    basisChildLoop_runs regs instanceData frame tape slot interval
      logicalBank child (semanticChunkCount_pos instanceData)
      chunkCount (by simp [chunkCount]) afterCopy code accumulator
      hcopyContext hcopyRemaining hcopyModulus hcopyModulusPred
      hcopyOne hcopyBasis hcopyCursor
  refine ⟨final, Runs.seq hcopyRun hloopRun, ?_, hfinalContext⟩
  exact
    { basis_eq := by
        simpa [chunkCount] using hloopPost.basis_eq
      packed_eq := by
        rw [hloopPost.packed_eq]
        exact hcopyOutside _ (by
          simp [basisChunkCursor, basisChunkRangeRegisters,
            packedValue, regs.injective.eq_iff])
      accumulator_eq := by
        rw [hloopPost.accumulator_eq]
        exact hcopyOutside _ (by
          simp [basisChunkCursor, basisChunkRangeRegisters,
            CombineValue.rangeRegisters, regs.injective.eq_iff])
      remaining_eq := hloopPost.remaining_eq
      modulus_eq := by
        rw [hloopPost.modulus_eq]
        exact hcopyOutside _ (by
          simp [basisChunkCursor, basisChunkRangeRegisters,
            CombineValue.rangeRegisters, regs.injective.eq_iff])
      modulusPred_eq := by
        rw [hloopPost.modulusPred_eq]
        exact hcopyOutside _ (by
          simp [basisChunkCursor, basisChunkRangeRegisters,
            CombineValue.rangeRegisters, regs.injective.eq_iff])
      one_eq := by
        rw [hloopPost.one_eq]
        exact hcopyOutside _ (by
          simp [basisChunkCursor, basisChunkRangeRegisters,
            CombineValue.rangeRegisters, regs.injective.eq_iff])
      count_eq := by
        rw [hloopPost.count_eq]
        exact hcopyOutside _ (by
          simp [basisChunkCursor, basisChunkRangeRegisters,
            CombineValue.rangeRegisters, regs.injective.eq_iff]) }

set_option maxHeartbeats 0 in
private theorem basisChildFold_runs
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
    (children :
      List
        (Fin
          (NeighborhoodExecutableEvaluation.graphFanIn
            workTapeCount)))
    (store : Store) (code accumulator : ℕ)
    (hcontext :
      ComputationFrameContext regs instanceData frame tape slot interval
        logicalBank store)
    (hremaining :
      store (CombineValue.rangeRegisters regs).remaining = code)
    (hmodulus :
      store (CombineValue.rangeRegisters regs).modulus =
        NeighborhoodScheduler.fieldModulus instanceData)
    (hmodulusPred :
      store (CombineValue.rangeRegisters regs).modulusPred =
        NeighborhoodScheduler.fieldModulus instanceData - 1)
    (hone :
      store (CombineValue.rangeRegisters regs).one = 1)
    (haccumulator : store (basisValue regs) = accumulator) :
    ∃ final,
      Runs (basisChildFold regs children) store final ∧
      BasisPost regs
        (basisChildrenFold
          (NeighborhoodScheduler.fieldModulus instanceData)
          (semanticChunkCount_pos instanceData)
          (computationBasisFactor instanceData frame logicalBank
            code)
          children accumulator)
        code store final ∧
      ComputationFrameContext regs instanceData frame tape slot interval
        logicalBank final := by
  induction children generalizing store accumulator with
  | nil =>
      refine ⟨store, ?_, ?_, hcontext⟩
      · simpa [basisChildFold] using Runs.skip store
      · exact
          { basis_eq := by
              simpa [basisChildrenFold] using haccumulator
            packed_eq := rfl
            accumulator_eq := rfl
            remaining_eq := hremaining
            modulus_eq := rfl
            modulusPred_eq := rfl
            one_eq := rfl
            count_eq := rfl }
  | cons child children ih =>
      let tailValue :=
        basisChildrenFold
          (NeighborhoodScheduler.fieldModulus instanceData)
          (semanticChunkCount_pos instanceData)
          (computationBasisFactor instanceData frame logicalBank
            code)
          children accumulator
      obtain ⟨afterTail, htailRun, htailPost, htailContext⟩ :=
        ih store accumulator hcontext hremaining hmodulus
          hmodulusPred hone haccumulator
      have htailBasis :
          afterTail (basisValue regs) = tailValue := by
        simpa [tailValue] using htailPost.basis_eq
      obtain ⟨final, hchildRun, hchildPost, hfinalContext⟩ :=
        basisChildCommand_runs regs instanceData frame tape slot interval
          logicalBank child afterTail code tailValue htailContext
          htailPost.remaining_eq
          (htailPost.modulus_eq.trans hmodulus)
          (htailPost.modulusPred_eq.trans hmodulusPred)
          (htailPost.one_eq.trans hone) htailBasis
      refine
        ⟨final, ?_, ?_, hfinalContext⟩
      · simpa [basisChildFold] using
          Runs.seq htailRun hchildRun
      · exact
          { basis_eq := by
              simpa [basisChildrenFold, tailValue] using
                hchildPost.basis_eq
            packed_eq :=
              hchildPost.packed_eq.trans htailPost.packed_eq
            accumulator_eq :=
              hchildPost.accumulator_eq.trans
                htailPost.accumulator_eq
            remaining_eq := hchildPost.remaining_eq
            modulus_eq :=
              hchildPost.modulus_eq.trans htailPost.modulus_eq
            modulusPred_eq :=
              hchildPost.modulusPred_eq.trans
                htailPost.modulusPred_eq
            one_eq :=
              hchildPost.one_eq.trans htailPost.one_eq
            count_eq :=
              hchildPost.count_eq.trans htailPost.count_eq }

set_option maxHeartbeats 0 in
theorem computationBasisKernel_spec_internal
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
    ComputationBasisKernelSpecAt regs instanceData frame tape slot
      interval logicalBank
      (computationBasisKernel workTapeCount regs) := by
  intro store code hcontext hremaining hmodulus hmodulusPred hone
  let payloadWidth :=
    NeighborhoodExecutableEvaluation.payloadWidth
      tm instanceData.blockLength
  let fanIn :=
    NeighborhoodExecutableEvaluation.graphFanIn workTapeCount
  let modulus := NeighborhoodScheduler.fieldModulus instanceData
  let afterImm :=
    (Basic.imm (basisValue regs) 1).exec store
  have himmRun :
      Runs (.basic (.imm (basisValue regs) 1))
        store afterImm :=
    Runs.basic _ _
  have himmValue :
      afterImm (basisValue regs) = 1 := by
    simp [afterImm, Basic.exec]
  have himmModulus :
      afterImm (basisAccumulatorRegisters regs).modulus =
        modulus := by
    simpa [afterImm, Basic.exec, basisAccumulatorRegisters,
      basisValue, modulus, regs.injective.eq_iff] using hmodulus
  have himmModulusPred :
      afterImm (basisAccumulatorRegisters regs).modulusPred =
        modulus - 1 := by
    simpa [afterImm, Basic.exec, basisAccumulatorRegisters,
      basisValue, modulus, regs.injective.eq_iff] using
      hmodulusPred
  have hmodulusPos : 0 < modulus := by
    simpa [modulus, NeighborhoodScheduler.fieldModulus] using
      CombineValue.fieldModulus_pos payloadWidth fanIn
  let initialBasis :=
    PrimeField.Runtime.normalize modulus 1
  let afterReduce :=
    RuntimeArithmetic.reduceResultStore
      (basisAccumulatorRegisters regs) initialBasis afterImm
  have hreduceRun :
      Runs
          (RuntimeArithmetic.reduce
            (basisAccumulatorRegisters regs))
          afterImm afterReduce := by
    simpa [afterReduce, initialBasis,
      PrimeField.Runtime.normalize] using
      RuntimeArithmetic.reduce_runs
        (basisAccumulatorRegisters regs) afterImm modulus 1
        hmodulusPos himmValue himmModulus himmModulusPred
  have hbasisMem :
      basisValue regs ∈
        CombineValue.combineScratchFootprint regs :=
    test_combineScratch_mem regs (17 : Fin 19)
  have htestMem :
      regs.index 4 ∈
        CombineValue.combineScratchFootprint regs :=
    test_combineScratch_mem regs (2 : Fin 19)
  have hsetupWrites :
      RAM.Structured.Footprint.CmdWritesWithin
        (CombineValue.combineScratchFootprint regs)
        (Cmd.seq
          (.basic (.imm (basisValue regs) 1))
          (RuntimeArithmetic.reduce
            (basisAccumulatorRegisters regs))) := by
    simp [RuntimeArithmetic.reduce,
      RuntimeArithmetic.reduceBody,
      RuntimeArithmetic.reduceTestOp,
      basisAccumulatorRegisters,
      RAM.Structured.Footprint.CmdWritesWithin,
      RAM.Structured.Footprint.BasicWritesWithin]
    exact ⟨hbasisMem, htestMem, hbasisMem, htestMem⟩
  have hsetupRun :
      Runs
          (Cmd.seq
            (.basic (.imm (basisValue regs) 1))
            (RuntimeArithmetic.reduce
              (basisAccumulatorRegisters regs)))
          store afterReduce :=
    Runs.seq himmRun hreduceRun
  have hsetupPreciseWrites :
      RAM.Structured.Footprint.CmdWritesWithin
        (basisAccumulatorFootprint regs)
        (Cmd.seq
          (.basic (.imm (basisValue regs) 1))
          (RuntimeArithmetic.reduce
            (basisAccumulatorRegisters regs))) := by
    simp [basisAccumulatorFootprint,
      RuntimeArithmetic.reduce,
      RuntimeArithmetic.reduceBody,
      RuntimeArithmetic.reduceTestOp,
      basisAccumulatorRegisters,
      RAM.Structured.Footprint.CmdWritesWithin,
      RAM.Structured.Footprint.BasicWritesWithin]
  have hsetupBank :
      afterReduce regs.layout.bank = store regs.layout.bank := by
    apply RAM.Structured.Footprint.runs_eq_outside
      hsetupPreciseWrites hsetupRun
    change regs.index 33 ∉ basisAccumulatorFootprint regs
    simp [basisAccumulatorFootprint, basisValue,
      regs.injective.eq_iff]
  have hsetupContext :
      ComputationFrameContext regs instanceData frame tape slot interval
        logicalBank afterReduce :=
    frameContext_transport_combineScratch_internal
      regs instanceData frame tape slot interval logicalBank
      hcontext hsetupWrites hsetupRun hsetupBank
  have hsetupBasis :
      afterReduce (basisValue regs) = initialBasis := by
    change
      (Function.update
        (Function.update afterImm (basisValue regs) initialBasis)
        (regs.index 4) 0) (basisValue regs) =
        initialBasis
    rw [Function.update_of_ne
      (regs.injective.ne (by decide))]
    exact Function.update_self _ _ _
  have hsetupRemaining :
      afterReduce (CombineValue.rangeRegisters regs).remaining =
        code := by
    simpa [afterReduce, RuntimeArithmetic.reduceResultStore,
      afterImm, Basic.exec, basisAccumulatorRegisters,
      basisValue, CombineValue.rangeRegisters,
      regs.injective.eq_iff] using hremaining
  have hsetupModulus :
      afterReduce (CombineValue.rangeRegisters regs).modulus =
        modulus := by
    simpa [afterReduce, RuntimeArithmetic.reduceResultStore,
      afterImm, Basic.exec, basisAccumulatorRegisters,
      basisValue, CombineValue.rangeRegisters, modulus,
      regs.injective.eq_iff] using hmodulus
  have hsetupModulusPred :
      afterReduce (CombineValue.rangeRegisters regs).modulusPred =
        modulus - 1 := by
    simpa [afterReduce, RuntimeArithmetic.reduceResultStore,
      afterImm, Basic.exec, basisAccumulatorRegisters,
      basisValue, CombineValue.rangeRegisters, modulus,
      regs.injective.eq_iff] using hmodulusPred
  have hsetupOne :
      afterReduce (CombineValue.rangeRegisters regs).one = 1 := by
    simpa [afterReduce, RuntimeArithmetic.reduceResultStore,
      afterImm, Basic.exec, basisAccumulatorRegisters,
      basisValue, CombineValue.rangeRegisters,
      regs.injective.eq_iff] using hone
  obtain ⟨final, hfoldRun, hfoldPost, hfinalContext⟩ :=
    basisChildFold_runs regs instanceData frame tape slot interval
      logicalBank
      (List.finRange
        (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount))
      afterReduce code initialBasis hsetupContext hsetupRemaining
      hsetupModulus hsetupModulusPred hsetupOne hsetupBasis
  have hsemantic :
      basisChildrenFold modulus
          (semanticChunkCount_pos instanceData)
          (computationBasisFactor instanceData frame logicalBank
            code)
          (List.finRange fanIn) initialBasis =
        basisAssignmentValue payloadWidth fanIn
          (computationArguments frame logicalBank) code := by
    simpa [payloadWidth, fanIn, modulus, initialBasis,
      basisAssignmentValue, computationBasisFactor,
      NeighborhoodExecutableEvaluation.Residue.basisValue,
      NeighborhoodScheduler.fieldModulus] using
      basisChildrenFold_eq_productList modulus
        (semanticChunkCount_pos instanceData)
        (computationBasisFactor instanceData frame logicalBank code)
        hmodulusPos
  refine ⟨final, ?_, ?_, hfinalContext⟩
  · simpa [computationBasisKernel, basisKernel] using
      Runs.seq hsetupRun hfoldRun
  · exact
      { basis_eq := by
          calc
            final (basisValue regs) =
                basisChildrenFold
                  (NeighborhoodScheduler.fieldModulus instanceData)
                  (semanticChunkCount_pos instanceData)
                  (computationBasisFactor instanceData frame
                    logicalBank code)
                  (List.finRange
                    (NeighborhoodExecutableEvaluation.graphFanIn
                      workTapeCount))
                  initialBasis :=
              hfoldPost.basis_eq
            _ =
                basisAssignmentValue
                  (NeighborhoodExecutableEvaluation.payloadWidth
                    tm instanceData.blockLength)
                  (NeighborhoodExecutableEvaluation.graphFanIn
                    workTapeCount)
                  (computationArguments frame logicalBank) code := by
              simpa [payloadWidth, fanIn, modulus] using hsemantic
        packed_eq := by
          rw [hfoldPost.packed_eq]
          simp [afterReduce, RuntimeArithmetic.reduceResultStore,
            afterImm, Basic.exec, basisAccumulatorRegisters,
            basisValue, packedValue, regs.injective.eq_iff]
        accumulator_eq := by
          rw [hfoldPost.accumulator_eq]
          simp [afterReduce, RuntimeArithmetic.reduceResultStore,
            afterImm, Basic.exec, basisAccumulatorRegisters,
            basisValue, CombineValue.rangeRegisters,
            regs.injective.eq_iff]
        remaining_eq := hfoldPost.remaining_eq
        modulus_eq := by
          rw [hfoldPost.modulus_eq]
          simp [afterReduce, RuntimeArithmetic.reduceResultStore,
            afterImm, Basic.exec, basisAccumulatorRegisters,
            basisValue, CombineValue.rangeRegisters,
            regs.injective.eq_iff]
        modulusPred_eq := by
          rw [hfoldPost.modulusPred_eq]
          simp [afterReduce, RuntimeArithmetic.reduceResultStore,
            afterImm, Basic.exec, basisAccumulatorRegisters,
            basisValue, CombineValue.rangeRegisters,
            regs.injective.eq_iff]
        one_eq := by
          rw [hfoldPost.one_eq]
          simp [afterReduce, RuntimeArithmetic.reduceResultStore,
            afterImm, Basic.exec, basisAccumulatorRegisters,
            basisValue, CombineValue.rangeRegisters,
            regs.injective.eq_iff]
        count_eq := by
          rw [hfoldPost.count_eq]
          simp [afterReduce, RuntimeArithmetic.reduceResultStore,
            afterImm, Basic.exec, basisAccumulatorRegisters,
            basisValue, CombineValue.rangeRegisters,
            regs.injective.eq_iff] }

private theorem copy_combine_writesWithin
    (regs : NeighborhoodTrial.Registers controller)
    (destination source : ℕ)
    (hdestination :
      destination ∈
        CombineValue.combineScratchFootprint regs) :
    RAM.Structured.Footprint.CmdWritesWithin
      (CombineValue.combineScratchFootprint regs)
      (copy destination source) := by
  simpa [copy,
    RAM.Structured.Footprint.CmdWritesWithin,
    RAM.Structured.Footprint.BasicWritesWithin] using
    And.intro hdestination hdestination

private theorem basisChunkPrepare_writesWithin
    (regs : NeighborhoodTrial.Registers controller)
    {fanIn : ℕ} (child : Fin fanIn) :
    RAM.Structured.Footprint.CmdWritesWithin
      (CombineValue.combineScratchFootprint regs)
      (basisChunkPrepare regs child) := by
  have hcursor :
      basisChunkCursor regs ∈
        CombineValue.combineScratchFootprint regs :=
    test_combineScratch_mem regs (1 : Fin 19)
  have h29 :
      regs.index 29 ∈
        CombineValue.combineScratchFootprint regs :=
    test_combineScratch_mem regs (14 : Fin 19)
  have h30 :
      coordinateIndex regs ∈
        CombineValue.combineScratchFootprint regs :=
    test_combineScratch_mem regs (15 : Fin 19)
  have hdecrement :
      RAM.Structured.Footprint.CmdWritesWithin
        (CombineValue.combineScratchFootprint regs)
        (.basic
          (.sub (basisChunkCursor regs)
            (basisChunkCursor regs)
            (CombineValue.rangeRegisters regs).one)) := by
    simpa [RAM.Structured.Footprint.CmdWritesWithin,
      RAM.Structured.Footprint.BasicWritesWithin] using hcursor
  have hindex :
      RAM.Structured.Footprint.CmdWritesWithin
        (CombineValue.combineScratchFootprint regs)
        (prepareAssignmentDigitIndex regs
          (reverseChildRank fanIn child)) :=
    test_cmdWritesWithin_mono
      (assignmentIndexFootprint_subset regs) _
      (prepareAssignmentDigitIndex_writesWithin regs
        (reverseChildRank fanIn child))
  have hbankCoordinate :
      RAM.Structured.Footprint.CmdWritesWithin
        (CombineValue.combineScratchFootprint regs)
        (prepareBankCoordinate regs child) :=
    test_cmdWritesWithin_mono
      (bankCoordinateFootprint_subset regs) _
      (prepareBankCoordinate_writesWithin regs child)
  have hcopy29 :=
    copy_combine_writesWithin regs (regs.index 29)
      (basisChunkCursor regs) h29
  have hcopy30 :=
    copy_combine_writesWithin regs (coordinateIndex regs)
      (regs.index 29) h30
  have hcopyCursor :=
    copy_combine_writesWithin regs (basisChunkCursor regs)
      (Layout.chunkRadix regs) hcursor
  simpa only [basisChunkPrepare, Cmd.seqList,
    RAM.Structured.Footprint.CmdWritesWithin] using
    And.intro hdecrement
      (And.intro hindex
        (And.intro
          (Internal.assignmentDigit_writesWithin_internal regs)
          (And.intro hbankCoordinate
            (And.intro hcopy29
              (And.intro
                (test_readResidueCoordinate_combine_writesWithin regs)
                (And.intro hcopy30 hcopyCursor))))))

private theorem basisChunkBody_writesWithin
    (regs : NeighborhoodTrial.Registers controller)
    {fanIn : ℕ} (child : Fin fanIn) :
    RAM.Structured.Footprint.CmdWritesWithin
      (CombineValue.combineScratchFootprint regs)
      (basisChunkBody regs child) := by
  have hcursor :
      basisChunkCursor regs ∈
        CombineValue.combineScratchFootprint regs :=
    test_combineScratch_mem regs (1 : Fin 19)
  have hrestore :=
    copy_combine_writesWithin regs (basisChunkCursor regs)
      (coordinateIndex regs) hcursor
  simpa [basisChunkBody, basisChunkCore, basisChunkRangeStage] using
    And.intro
      (And.intro
        (And.intro
          (basisChunkPrepare_writesWithin regs child)
          (basisChunkRange_writesWithin_internal regs))
        (basisAccumulatorMul_writesWithin_internal regs))
      hrestore

private theorem basisChildCommand_writesWithin
    (regs : NeighborhoodTrial.Registers controller)
    {fanIn : ℕ} (child : Fin fanIn) :
    RAM.Structured.Footprint.CmdWritesWithin
      (CombineValue.combineScratchFootprint regs)
      (basisChildCommand regs child) := by
  have hcursor :
      basisChunkCursor regs ∈
        CombineValue.combineScratchFootprint regs :=
    test_combineScratch_mem regs (1 : Fin 19)
  have hinitialize :=
    copy_combine_writesWithin regs (basisChunkCursor regs)
      (Layout.chunkCount regs) hcursor
  simpa [basisChildCommand] using
    And.intro hinitialize
      (basisChunkBody_writesWithin regs child)

private theorem basisChildFold_writesWithin
    (regs : NeighborhoodTrial.Registers controller)
    {fanIn : ℕ} (children : List (Fin fanIn)) :
    RAM.Structured.Footprint.CmdWritesWithin
      (CombineValue.combineScratchFootprint regs)
      (basisChildFold regs children) := by
  induction children with
  | nil => simp [basisChildFold,
      RAM.Structured.Footprint.CmdWritesWithin]
  | cons child children ih =>
      simpa [basisChildFold] using
        And.intro ih
          (basisChildCommand_writesWithin regs child)

theorem computationBasisKernel_writesWithin_internal
    (workTapeCount : ℕ)
    (regs : NeighborhoodTrial.Registers controller) :
    RAM.Structured.Footprint.CmdWritesWithin
      (CombineValue.combineScratchFootprint regs)
      (computationBasisKernel workTapeCount regs) := by
  have hbasis :
      basisValue regs ∈
        CombineValue.combineScratchFootprint regs :=
    test_combineScratch_mem regs (17 : Fin 19)
  have htest :
      regs.index 4 ∈
        CombineValue.combineScratchFootprint regs :=
    test_combineScratch_mem regs (2 : Fin 19)
  have hinitialize :
      RAM.Structured.Footprint.CmdWritesWithin
        (CombineValue.combineScratchFootprint regs)
        (.basic (.imm (basisValue regs) 1)) := by
    simpa [RAM.Structured.Footprint.CmdWritesWithin,
      RAM.Structured.Footprint.BasicWritesWithin] using hbasis
  have hreduce :
      RAM.Structured.Footprint.CmdWritesWithin
        (CombineValue.combineScratchFootprint regs)
        (RuntimeArithmetic.reduce
          (basisAccumulatorRegisters regs)) := by
    simp [RuntimeArithmetic.reduce,
      RuntimeArithmetic.reduceBody,
      RuntimeArithmetic.reduceTestOp,
      basisAccumulatorRegisters,
      RAM.Structured.Footprint.CmdWritesWithin,
      RAM.Structured.Footprint.BasicWritesWithin]
    exact ⟨htest, hbasis, htest⟩
  simpa [computationBasisKernel, basisKernel] using
    And.intro (And.intro hinitialize hreduce)
      (basisChildFold_writesWithin regs
        (List.finRange
          (NeighborhoodExecutableEvaluation.graphFanIn
            workTapeCount)))

end Complexity.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.CombineTerm
