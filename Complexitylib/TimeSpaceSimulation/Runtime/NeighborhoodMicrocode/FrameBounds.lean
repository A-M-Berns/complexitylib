/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.FrameBounds.Internal

/-!
# Codec consequences of scheduler frame bounds

Reachable scheduler frames fit the exact two-digit field and twenty-four-digit
continuation codecs computed by the runtime candidate-parameter pass.
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace FrameBounds

/-- A bounded scheduler scalar fits in the frame codec's two radix digits. -/
theorem frameBound_scalar_lt
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (hframe :
      NeighborhoodScheduler.FrameBounds.FrameBound frame) :
    frame.scalar <
      CandidateParameters.domainSize
        tm.Q workTapeCount instanceData.candidateTime ^
          FrameCodec.scalarDigitCount :=
  Internal.frameBound_scalar_lt_internal frame hframe

/-- Both decoded residue cursors fit the phase codec's two-digit scalar
allocation; this is the first one. -/
theorem frameBound_phaseResidue_lt
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (hframe :
      NeighborhoodScheduler.FrameBounds.FrameBound frame) :
    (ControlDecode.expectedPhaseValues frame.phase).residue <
      CandidateParameters.domainSize
          tm.Q workTapeCount instanceData.candidateTime ^
        FrameCodec.scalarDigitCount :=
  Internal.frameBound_phaseResidue_lt_internal frame hframe

/-- Both decoded residue cursors fit the phase codec's two-digit scalar
allocation; this is the remaining-residue counter. -/
theorem frameBound_phaseResiduesLeft_lt
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (hframe :
      NeighborhoodScheduler.FrameBounds.FrameBound frame) :
    (ControlDecode.expectedPhaseValues frame.phase).residuesLeft <
      CandidateParameters.domainSize
          tm.Q workTapeCount instanceData.candidateTime ^
        FrameCodec.scalarDigitCount :=
  Internal.frameBound_phaseResiduesLeft_lt_internal frame hframe

/-- Every reachable scheduler frame has only valid chunk-radix digits. -/
theorem frameBound_frameFits
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (hframe :
      NeighborhoodScheduler.FrameBounds.FrameBound frame) :
    FrameCodec.FrameFits
      (CandidateParameters.domainSize
        tm.Q workTapeCount instanceData.candidateTime)
      frame :=
  Internal.frameBound_frameFits_internal frame hframe

/-- Every node-code digit of a reachable scheduler frame fits the runtime
chunk radix. -/
theorem frameBound_nodeDigits_fit
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (hframe :
      NeighborhoodScheduler.FrameBounds.FrameBound frame) :
    ∀ digit ∈ FrameCodec.nodeDigits frame.node,
      digit <
        CandidateParameters.domainSize
          tm.Q workTapeCount instanceData.candidateTime :=
  Internal.frameBound_nodeDigits_fit_internal frame hframe

/-- Every phase-code digit of a reachable scheduler frame fits the runtime
chunk radix. -/
theorem frameBound_phaseDigits_fit
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (hframe :
      NeighborhoodScheduler.FrameBounds.FrameBound frame) :
    ∀ digit ∈
        FrameCodec.phaseDigits
          (CandidateParameters.domainSize
            tm.Q workTapeCount instanceData.candidateTime)
          frame.phase,
      digit <
        CandidateParameters.domainSize
          tm.Q workTapeCount instanceData.candidateTime :=
  Internal.frameBound_phaseDigits_fit_internal frame hframe

/-- Shifting a reachable frame code by one still fits below the runtime
continuation-frame radix. -/
theorem frameBound_shiftedCode_lt_frameRadix
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (hframe :
      NeighborhoodScheduler.FrameBounds.FrameBound frame) :
    FrameCodec.encodeFrame
          (CandidateParameters.domainSize
            tm.Q workTapeCount instanceData.candidateTime)
          frame +
        1 <
      CandidateParameters.frameRadix
        tm.Q workTapeCount instanceData.candidateTime :=
  Internal.frameBound_shiftedCode_lt_frameRadix_internal frame hframe

end FrameBounds
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
