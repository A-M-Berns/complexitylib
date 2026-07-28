import ScratchBasis

open Complexity Complexity.TimeSpaceSimulation TreeEval CookMertz

namespace Complexity.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.CombineTerm

open RAM Structured

variable {controller : SearchProgram.Registers}

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

end Complexity.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.CombineTerm
