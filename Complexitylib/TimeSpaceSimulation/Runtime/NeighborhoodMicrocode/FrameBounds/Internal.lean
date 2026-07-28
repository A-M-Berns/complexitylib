/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.CandidateParameters.RadixBounds
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.ControlDecode.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.FrameCodec
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodScheduler.FrameBounds
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodTrial

/-!
# Codec consequences of scheduler frame bounds -- proofs
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace FrameBounds
namespace Internal

open NeighborhoodGraph
open NeighborhoodExecutableEvaluation

theorem frameBound_scalar_lt_internal
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (hframe :
      NeighborhoodScheduler.FrameBounds.FrameBound frame) :
    frame.scalar <
      CandidateParameters.domainSize
        tm.Q workTapeCount instanceData.candidateTime ^
          FrameCodec.scalarDigitCount := by
  have hscalar := hframe.2.2.1
  rw [NeighborhoodTrial.fieldModulus_eq_canonicalModulus] at hscalar
  have hmodulus :=
    CandidateParameters.RadixBounds.canonicalModulus_lt_bankRadix
      tm.Q workTapeCount instanceData.candidateTime
  rw [CandidateParameters.RadixBounds.bankRadix_eq_domainSize_sq]
    at hmodulus
  simpa [FrameCodec.scalarDigitCount] using
    (hscalar.trans hmodulus)

private theorem fieldModulus_lt_scalarRadix
    {tm : TM workTapeCount}
    (instanceData : NeighborhoodProgram.ResidueInstance tm) :
    NeighborhoodScheduler.fieldModulus instanceData <
      CandidateParameters.domainSize
          tm.Q workTapeCount instanceData.candidateTime ^
        FrameCodec.scalarDigitCount := by
  rw [NeighborhoodTrial.fieldModulus_eq_canonicalModulus]
  have hmodulus :=
    CandidateParameters.RadixBounds.canonicalModulus_lt_bankRadix
      tm.Q workTapeCount instanceData.candidateTime
  rw [CandidateParameters.RadixBounds.bankRadix_eq_domainSize_sq]
    at hmodulus
  simpa [FrameCodec.scalarDigitCount] using hmodulus

theorem frameBound_phaseResidue_lt_internal
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (hframe :
      NeighborhoodScheduler.FrameBounds.FrameBound frame) :
    (ControlDecode.expectedPhaseValues frame.phase).residue <
      CandidateParameters.domainSize
          tm.Q workTapeCount instanceData.candidateTime ^
        FrameCodec.scalarDigitCount := by
  let base :=
    CandidateParameters.domainSize
      tm.Q workTapeCount instanceData.candidateTime
  change
    (ControlDecode.expectedPhaseValues frame.phase).residue <
      base ^ FrameCodec.scalarDigitCount
  have hbase : 0 < base := by
    have :=
      CandidateParameters.RadixBounds.one_lt_domainSize
        tm.Q workTapeCount instanceData.candidateTime
    omega
  have hmodulus :
      NeighborhoodScheduler.fieldModulus instanceData <
        base ^ FrameCodec.scalarDigitCount :=
    fieldModulus_lt_scalarRadix instanceData
  have hphase := hframe.2.2.2
  cases hphaseEq : frame.phase with
  | enter =>
      simp [ControlDecode.expectedPhaseValues]
      positivity
  | prepare residue residuesLeft child =>
      simp only [hphaseEq,
        NeighborhoodScheduler.FrameBounds.PhaseBound] at hphase
      simp only [ControlDecode.expectedPhaseValues]
      omega
  | combine residue residuesLeft =>
      simp only [hphaseEq,
        NeighborhoodScheduler.FrameBounds.PhaseBound] at hphase
      simp only [ControlDecode.expectedPhaseValues]
      omega
  | cleanupCall residue residuesLeft child =>
      simp only [hphaseEq,
        NeighborhoodScheduler.FrameBounds.PhaseBound] at hphase
      simp only [ControlDecode.expectedPhaseValues]
      omega
  | cleanupScale residue residuesLeft child next =>
      simp only [hphaseEq,
        NeighborhoodScheduler.FrameBounds.PhaseBound] at hphase
      simp only [ControlDecode.expectedPhaseValues]
      omega

theorem frameBound_phaseResiduesLeft_lt_internal
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (hframe :
      NeighborhoodScheduler.FrameBounds.FrameBound frame) :
    (ControlDecode.expectedPhaseValues frame.phase).residuesLeft <
      CandidateParameters.domainSize
          tm.Q workTapeCount instanceData.candidateTime ^
        FrameCodec.scalarDigitCount := by
  let base :=
    CandidateParameters.domainSize
      tm.Q workTapeCount instanceData.candidateTime
  change
    (ControlDecode.expectedPhaseValues frame.phase).residuesLeft <
      base ^ FrameCodec.scalarDigitCount
  have hbase : 0 < base := by
    have :=
      CandidateParameters.RadixBounds.one_lt_domainSize
        tm.Q workTapeCount instanceData.candidateTime
    omega
  have hmodulus :
      NeighborhoodScheduler.fieldModulus instanceData <
        base ^ FrameCodec.scalarDigitCount :=
    fieldModulus_lt_scalarRadix instanceData
  have hphase := hframe.2.2.2
  cases hphaseEq : frame.phase with
  | enter =>
      simp [ControlDecode.expectedPhaseValues]
      positivity
  | prepare residue residuesLeft child =>
      simp only [hphaseEq,
        NeighborhoodScheduler.FrameBounds.PhaseBound] at hphase
      simp only [ControlDecode.expectedPhaseValues]
      omega
  | combine residue residuesLeft =>
      simp only [hphaseEq,
        NeighborhoodScheduler.FrameBounds.PhaseBound] at hphase
      simp only [ControlDecode.expectedPhaseValues]
      omega
  | cleanupCall residue residuesLeft child =>
      simp only [hphaseEq,
        NeighborhoodScheduler.FrameBounds.PhaseBound] at hphase
      simp only [ControlDecode.expectedPhaseValues]
      omega
  | cleanupScale residue residuesLeft child next =>
      simp only [hphaseEq,
        NeighborhoodScheduler.FrameBounds.PhaseBound] at hphase
      simp only [ControlDecode.expectedPhaseValues]
      omega

private theorem scalarDigits_fit
    {base : ℕ} (hbase : 0 < base) (value : ℕ) :
    ∀ digit ∈ FrameCodec.scalarDigits base value,
      digit < base := by
  intro digit hdigit
  simp only [FrameCodec.scalarDigits, List.mem_cons,
    List.mem_nil_iff, or_false] at hdigit
  rcases hdigit with rfl | rfl
  · exact Nat.mod_lt _ hbase
  · exact Nat.mod_lt _ hbase

private theorem nodeDigits_fit
    {base horizon : ℕ}
    (hbase : 4 < base)
    (htape : workTapeCount + 2 < base)
    (hhorizon : horizon < base)
    (node :
      NeighborhoodEvaluator.QueryNode workTapeCount horizon)
    (hnode :
      NeighborhoodScheduler.FrameBounds.QueryBound horizon node) :
    ∀ digit ∈ FrameCodec.nodeDigits node,
      digit < base := by
  intro digit hdigit
  cases node with
  | failure =>
      simp [FrameCodec.nodeDigits] at hdigit
      omega
  | graph node =>
      cases node with
      | source tape block =>
          simp only
            [NeighborhoodScheduler.FrameBounds.QueryBound] at hnode
          simp only [FrameCodec.nodeDigits, List.mem_cons,
            List.mem_nil_iff, or_false] at hdigit
          rcases hdigit with rfl | rfl | rfl | rfl
          · omega
          · exact tape.isLt.trans htape
          · exact hnode.trans_lt (max_lt hhorizon (by omega))
          · omega
      | computation tape slot interval =>
          simp only
            [NeighborhoodScheduler.FrameBounds.QueryBound] at hnode
          simp only [FrameCodec.nodeDigits, List.mem_cons,
            List.mem_nil_iff, or_false] at hdigit
          rcases hdigit with rfl | rfl | rfl | rfl
          · omega
          · exact tape.isLt.trans htape
          · exact slot.toFin.isLt.trans (by omega)
          · exact hnode.trans hhorizon

private theorem phaseDigits_fit
    {base modulus : ℕ}
    (hbase : 4 < base)
    (hfanIn :
      graphFanIn workTapeCount < base)
    (phase : NeighborhoodScheduler.Phase workTapeCount)
    (hphase :
      NeighborhoodScheduler.FrameBounds.PhaseBound
        modulus (graphFanIn workTapeCount) phase) :
    ∀ digit ∈ FrameCodec.phaseDigits base phase,
      digit < base := by
  intro digit hdigit
  have hbasePos : 0 < base := by omega
  cases phase with
  | enter =>
      simp [FrameCodec.phaseDigits] at hdigit
      omega
  | prepare residue residuesLeft childIndex =>
      simp only
        [NeighborhoodScheduler.FrameBounds.PhaseBound] at hphase
      simp only [FrameCodec.phaseDigits, List.mem_append,
        List.mem_cons, List.mem_nil_iff, or_false] at hdigit
      rcases hdigit with
        ((rfl | hresidue) | hresiduesLeft) | rfl | rfl
      · omega
      · exact
          scalarDigits_fit hbasePos residue digit hresidue
      · exact
          scalarDigits_fit hbasePos residuesLeft digit hresiduesLeft
      · omega
      · omega
  | combine residue residuesLeft =>
      simp only [FrameCodec.phaseDigits, List.mem_append,
        List.mem_cons, List.mem_nil_iff, or_false] at hdigit
      rcases hdigit with
        ((rfl | hresidue) | hresiduesLeft) | rfl | rfl
      · omega
      · exact
          scalarDigits_fit hbasePos residue digit hresidue
      · exact
          scalarDigits_fit hbasePos residuesLeft digit hresiduesLeft
      · omega
      · omega
  | cleanupCall residue residuesLeft childIndex =>
      simp only
        [NeighborhoodScheduler.FrameBounds.PhaseBound] at hphase
      simp only [FrameCodec.phaseDigits, List.mem_append,
        List.mem_cons, List.mem_nil_iff, or_false] at hdigit
      rcases hdigit with
        ((rfl | hresidue) | hresiduesLeft) | rfl | rfl
      · omega
      · exact
          scalarDigits_fit hbasePos residue digit hresidue
      · exact
          scalarDigits_fit hbasePos residuesLeft digit hresiduesLeft
      · omega
      · omega
  | cleanupScale residue residuesLeft child nextChildIndex =>
      simp only
        [NeighborhoodScheduler.FrameBounds.PhaseBound] at hphase
      simp only [FrameCodec.phaseDigits, List.mem_append,
        List.mem_cons, List.mem_nil_iff, or_false] at hdigit
      rcases hdigit with
        ((rfl | hresidue) | hresiduesLeft) | rfl | rfl
      · omega
      · exact
          scalarDigits_fit hbasePos residue digit hresidue
      · exact
          scalarDigits_fit hbasePos residuesLeft digit hresiduesLeft
      · exact child.isLt.trans hfanIn
      · omega

theorem frameBound_frameFits_internal
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (hframe :
      NeighborhoodScheduler.FrameBounds.FrameBound frame) :
    FrameCodec.FrameFits
      (CandidateParameters.domainSize
        tm.Q workTapeCount instanceData.candidateTime)
      frame := by
  let base :=
    CandidateParameters.domainSize
      tm.Q workTapeCount instanceData.candidateTime
  have hbase : 4 < base := by
    have hfanIn :=
      CandidateParameters.RadixBounds.fanIn_lt_domainSize
        tm.Q workTapeCount instanceData.candidateTime
    unfold CandidateParameters.fanIn
      WorkspaceAccounting.fanIn at hfanIn
    omega
  have hfanIn : graphFanIn workTapeCount < base := by
    simpa [graphFanIn, NeighborhoodEvaluator.fanIn,
      CandidateParameters.fanIn, WorkspaceAccounting.fanIn] using
      CandidateParameters.RadixBounds.fanIn_lt_domainSize
        tm.Q workTapeCount instanceData.candidateTime
  have htape : workTapeCount + 2 < base := by
    unfold graphFanIn NeighborhoodEvaluator.fanIn at hfanIn
    omega
  have hhorizon : instanceData.horizon < base := by
    have hhorizon' :=
      CandidateParameters.RadixBounds.horizon_lt_domainSize
        tm.Q workTapeCount instanceData.candidateTime
    rw [instanceData.horizon_eq]
    exact hhorizon'
  rcases hframe with
    ⟨hfuel, hnode, _hscalar, hphase⟩
  intro digit hdigit
  unfold FrameCodec.frameDigits at hdigit
  simp only [List.mem_cons, List.mem_append] at hdigit
  change digit < base
  rcases hdigit with
    rfl | hnodeDigit | hscalarDigit | rfl | hphaseDigit | hreserved
  · exact hfuel.trans_lt hhorizon
  · exact
      nodeDigits_fit hbase htape hhorizon
        frame.node hnode digit hnodeDigit
  · exact
      scalarDigits_fit (by omega) frame.scalar digit hscalarDigit
  · have hout := frame.out.isLt
    omega
  · exact
      phaseDigits_fit hbase hfanIn
        frame.phase hphase digit hphaseDigit
  · simp only [List.mem_replicate] at hreserved
    omega

theorem frameBound_nodeDigits_fit_internal
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (hframe :
      NeighborhoodScheduler.FrameBounds.FrameBound frame) :
    ∀ digit ∈ FrameCodec.nodeDigits frame.node,
      digit <
        CandidateParameters.domainSize
          tm.Q workTapeCount instanceData.candidateTime := by
  intro digit hdigit
  apply frameBound_frameFits_internal frame hframe
  simp [FrameCodec.frameDigits, hdigit]

theorem frameBound_phaseDigits_fit_internal
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
          tm.Q workTapeCount instanceData.candidateTime := by
  intro digit hdigit
  apply frameBound_frameFits_internal frame hframe
  simp [FrameCodec.frameDigits, hdigit]

theorem frameBound_shiftedCode_lt_frameRadix_internal
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
        tm.Q workTapeCount instanceData.candidateTime := by
  have hbase :=
    CandidateParameters.RadixBounds.one_lt_domainSize
      tm.Q workTapeCount instanceData.candidateTime
  have hfits :=
    frameBound_frameFits_internal frame hframe
  have hcode :=
    FrameCodec.encodeFrame_succ_lt_pow frame hbase hfits
  rw [CandidateParameters.RadixBounds.frameRadix_eq_domainSize_pow]
  simpa [FrameCodec.frameDigitCount] using hcode

end Internal
end FrameBounds
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
