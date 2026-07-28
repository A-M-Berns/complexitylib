/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.CombineTerm.Internal.Basis

/-!
# One dynamic tensor-basis chunk

This internal layer composes dynamic coordinate preparation, the inner
Lagrange range, modular multiplication, and cursor restoration for one
uniform tensor-basis loop iteration.
-/

open Complexity Complexity.TimeSpaceSimulation TreeEval CookMertz

namespace Complexity.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.CombineTerm

open RAM Structured

variable {controller : SearchProgram.Registers}

set_option maxHeartbeats 0 in
theorem basisChunkBody_runs_internal
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
    basisChunkPrepare_runs_internal regs instanceData frame tape slot
      interval logicalBank child chunk store code accumulator hcontext
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
      regs instanceData frame tape slot interval logicalBank
      hpreparePost.context
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

end Complexity.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.CombineTerm
