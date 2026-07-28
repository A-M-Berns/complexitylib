/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.CombineTerm.Internal.Basis

/-!
# Dynamic tensor-basis chunk range

This internal layer composes uniform chunk preparation with the inner
Lagrange range while retaining the frame and outer-fold invariants.
-/

open Complexity Complexity.TimeSpaceSimulation TreeEval CookMertz

namespace Complexity.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.CombineTerm

open RAM Structured

variable {controller : SearchProgram.Registers}

/-- State exposed by the range stage of one dynamic tensor-basis chunk. -/
structure BasisChunkRangePost
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
    (final : Store) : Prop where
  context :
    ComputationFrameContext regs instanceData frame tape slot interval
      logicalBank final
  chunkValue_eq :
    final (basisChunkRangeRegisters regs).accumulator =
      NeighborhoodExecutableEvaluation.Residue.chunkBasisValue
        (NeighborhoodExecutableEvaluation.payloadWidth
          tm instanceData.blockLength)
        (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount)
        (GroupedExtension.Evaluation.chunkAssignmentOfCode
          finProdFinEquiv
          (PrimeGrouped.Logarithmic.chunkBits
            (NeighborhoodExecutableEvaluation.payloadWidth
              tm instanceData.blockLength)
            (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount))
          code (child, chunk))
        (computationArguments frame logicalBank child chunk)
  basis_eq : final (basisValue regs) = accumulator
  coordinate_eq : final (coordinateIndex regs) = chunk.val
  mulModulus_eq :
    final (basisAccumulatorRegisters regs).modulus =
      NeighborhoodScheduler.fieldModulus instanceData
  mulModulusPred_eq :
    final (basisAccumulatorRegisters regs).modulusPred =
      NeighborhoodScheduler.fieldModulus instanceData - 1

set_option maxHeartbeats 0 in
theorem basisChunkRangeStage_runs_internal
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
      Runs (basisChunkRangeStage regs child) store final ∧
      BasisChunkRangePost regs instanceData frame tape slot interval
        code accumulator logicalBank child chunk final := by
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
  obtain ⟨final, hrangeRun, hrangePost, _hselectedRange,
      _hpointRange⟩ :=
    basisChunkRange_runs_internal regs payloadWidth fanIn selected point
      afterPrepare hprepareModulus hprepareModulusPred hprepareCount
      hprepareSelected hpreparePoint
  have hrangeBank :
      final regs.layout.bank = afterPrepare regs.layout.bank := by
    apply RAM.Structured.Footprint.runs_eq_outside
      (basisChunkRange_precise_writesWithin_internal regs) hrangeRun
    change regs.index 33 ∉ basisChunkFootprint regs
    simp [basisChunkFootprint, regs.injective.eq_iff]
  have hfinalContext :
      ComputationFrameContext regs instanceData frame tape slot interval
        logicalBank final :=
    frameContext_transport_combineScratch_internal
      regs instanceData frame tape slot interval logicalBank
      hpreparePost.context
      (basisChunkRange_writesWithin_internal regs) hrangeRun hrangeBank
  have houtside :
      ∀ address, address ∉ basisChunkFootprint regs →
        final address = afterPrepare address := by
    intro address haddress
    exact RAM.Structured.Footprint.runs_eq_outside
      (basisChunkRange_precise_writesWithin_internal regs) hrangeRun
      haddress
  have hrun :
      Runs (basisChunkRangeStage regs child) store final := by
    exact Runs.seq hprepareRun hrangeRun
  refine ⟨final, hrun, ?_⟩
  exact
    { context := hfinalContext
      chunkValue_eq := by
        exact hrangePost.accumulator_eq.trans
          (chunkRange_eq_internal payloadWidth fanIn point selected)
      basis_eq := by
        rw [houtside (basisValue regs)
          (by
            simp [basisChunkFootprint, basisValue,
              regs.injective.eq_iff])]
        exact hpreparePost.basis_eq
      coordinate_eq := by
        rw [houtside (coordinateIndex regs)
          (by
            simp [basisChunkFootprint, coordinateIndex,
              regs.injective.eq_iff])]
        exact hpreparePost.coordinate_eq
      mulModulus_eq := by
        simpa [basisAccumulatorRegisters, inner, modulus,
          NeighborhoodScheduler.fieldModulus] using
          hrangePost.modulus_eq
      mulModulusPred_eq := by
        simpa [basisAccumulatorRegisters, inner, modulus,
          NeighborhoodScheduler.fieldModulus] using
          hrangePost.modulusPred_eq }

end Complexity.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.CombineTerm
