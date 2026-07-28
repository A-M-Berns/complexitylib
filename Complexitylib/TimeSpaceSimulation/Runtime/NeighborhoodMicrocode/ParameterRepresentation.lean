/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.ParameterRepresentation.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.ParameterRepresentation.Internal

/-!
# Parameter-program representation bridge
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace ParameterRepresentation

open RAM Structured

variable {controller : SearchProgram.Registers}

/-- The exact canonical parameter-program postcondition supplies every
retained parameter required by the packed scheduler representation. -/
theorem Parameters.of_post
    {tm : TM workTapeCount}
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (initial final : Store)
    (hpost :
      CandidateParameters.Post tm.Q workTapeCount
        instanceData.candidateTime regs.parameters initial final) :
    Representation.Parameters regs instanceData final :=
  Internal.parameters_of_post_internal
    regs instanceData initial final hpost

/-- Candidate-parameter setup establishes the scheduler parameter
representation while retaining the cached public-input frame. -/
theorem parameterProgram_runs
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
        controller regs.footprint instanceData.x final :=
  Internal.parameterProgram_runs_internal
    controller regs instanceData initial hframe hcandidate

end ParameterRepresentation
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
