/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.ParameterRepresentation.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.Representation
import Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodTrial

/-!
# Parameter-program representation bridge -- proofs
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace ParameterRepresentation
namespace Internal

open RAM Structured

variable {controller : SearchProgram.Registers}

theorem parameters_of_post_internal
    {tm : TM workTapeCount}
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (initial final : Store)
    (hpost :
      CandidateParameters.Post tm.Q workTapeCount
        instanceData.candidateTime regs.parameters initial final) :
    Representation.Parameters regs instanceData final := by
  refine
    { blockLength_eq :=
        NeighborhoodTrial.parametersPost_blockLength_eq
          regs instanceData hpost
      horizon_eq :=
        NeighborhoodTrial.parametersPost_horizon_eq
          regs instanceData hpost
      digitBase_eq := ?_
      bankBase_eq := ?_
      frameBase_eq := ?_
      chunkCount_eq := ?_
      bankDigitCount_eq := ?_
      modulus_eq :=
        NeighborhoodTrial.parametersPost_modulus_eq
          regs instanceData hpost
      modulusPred_eq :=
        NeighborhoodTrial.parametersPost_modulusPred_eq
          regs instanceData hpost }
  · change
      final regs.parameters.domainSize =
        Representation.digitBase instanceData
    rw [hpost.domainSize_eq]
    rfl
  · change
      final regs.parameters.bankRadix =
        Representation.fieldBase instanceData
    rw [hpost.bankRadix_eq,
      ← Representation.fieldBase_eq_bankRadix instanceData]
  · change
      final regs.parameters.frameRadix =
        Representation.frameBase instanceData
    rw [hpost.frameRadix_eq]
    rfl
  · change
      final regs.parameters.chunkCount =
        TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
          (NeighborhoodExecutableEvaluation.payloadWidth
            tm instanceData.blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount)
    rw [hpost.chunkCount_eq,
      Representation.payloadWidth_eq_booleanWidth instanceData]
    rfl
  · change
      final regs.parameters.bankDigitCount =
        (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount + 1) *
          TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
            (NeighborhoodExecutableEvaluation.payloadWidth
              tm instanceData.blockLength)
            (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount)
    rw [hpost.bankDigitCount_eq,
      ← Representation.bankCoordinateCount_eq instanceData]

theorem parameterProgram_runs_internal
    {tm : TM workTapeCount}
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (initial : Store)
    (hframe :
      SearchProgram.InputFrame
        controller regs.footprint instanceData.x initial)
    (hcandidate :
      initial controller.candidate = instanceData.candidateTime) :
    ∃ final,
      Runs (regs.parameterProgram tm.Q workTapeCount) initial final ∧
      Representation.Parameters regs instanceData final ∧
      SearchProgram.InputFrame
        controller regs.footprint instanceData.x final := by
  obtain ⟨final, hrun, hpost, hframeFinal⟩ :=
    NeighborhoodTrial.Registers.parameterProgram_runs_preserving_inputFrame
      tm.Q workTapeCount regs instanceData.x initial
      instanceData.candidateTime hframe hcandidate
  exact
    ⟨final, hrun,
      parameters_of_post_internal
        regs instanceData initial final hpost,
      hframeFinal⟩

end Internal
end ParameterRepresentation
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
