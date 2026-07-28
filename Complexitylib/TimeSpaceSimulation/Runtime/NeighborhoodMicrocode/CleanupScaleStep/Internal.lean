/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.CleanupScaleStep.Defs

/-!
# Concrete cleanup-scale scheduler step -- proofs
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace CleanupScaleStep
namespace Internal

open RAM Structured

variable {controller : SearchProgram.Registers}

theorem step_writesWithin_internal
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin regs.layout.footprint (step regs) := by
  constructor
  · change regs.index (17 : Fin 34) ∈ regs.layout.footprint
    exact Layout.index_mem_layout_footprint regs 17
  · exact Dispatcher.cleanupScale_writesWithin regs

theorem step_runs_internal
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (rest : List (NeighborhoodScheduler.Frame tm instanceData))
    (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store)
    (residue residuesLeft nextChild : ℕ)
    (child :
      Fin (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount))
    (hquery :
      Representation.QueryState regs instanceData
        { stack := frame :: rest
          registers := logicalBank }
        store)
    (hphase :
      frame.phase =
        .cleanupScale residue residuesLeft child nextChild)
    (hdecodedResidue :
      store (Dispatcher.decodedResidue regs) = residue)
    (hdecodedLeft :
      store (Dispatcher.decodedResiduesLeft regs) = residuesLeft)
    (hdecodedChild :
      store (Dispatcher.decodedChild regs) = child.val)
    (hdecodedNext :
      store (Dispatcher.decodedNextChild regs) = nextChild) :
    ∃ final,
      Runs (step regs) store final ∧
      Representation.QueryState regs instanceData
        { stack :=
            resumedParent frame residue residuesLeft nextChild :: rest
          registers :=
            scaledBank frame residue child logicalBank }
        final := by
  let initialized :=
    Basic.exec
      (.imm (Dispatcher.cleanupInverseRegisters regs).one 1)
      store
  have hinitialize :
      Runs
        (.basic
          (.imm (Dispatcher.cleanupInverseRegisters regs).one 1))
        store initialized :=
    Runs.basic _ _
  have hinitializedOne :
      initialized
          (Dispatcher.cleanupInverseRegisters regs).one =
        1 := by
    simp [initialized, Basic.exec]
  have hinitializedPhysical
      (slot : Fin 34) (hne : slot ≠ 17) :
      initialized (regs.index slot) = store (regs.index slot) := by
    simp [initialized, Basic.exec,
      Dispatcher.cleanupInverseRegisters,
      Dispatcher.cleanupInverseMap, regs.injective.eq_iff, hne]
  have hinitializedRetained :
      ∀ slot,
        initialized
            (regs.index (Dispatcher.cleanupRetainedMap slot)) =
          store
            (regs.index (Dispatcher.cleanupRetainedMap slot)) := by
    intro slot
    fin_cases slot <;>
      apply hinitializedPhysical <;> decide
  have hbankInitialized :
      initialized regs.layout.bank = store regs.layout.bank := by
    simpa [NeighborhoodTrial.Registers.layout,
      NeighborhoodProgram.Layout.bank] using
      hinitializedPhysical (33 : Fin 34) (by decide)
  have hframeBound :
      NeighborhoodScheduler.FrameBounds.FrameBound frame :=
    hquery.bounds frame (by simp)
  have hdigitBase :
      0 < Representation.digitBase instanceData := by
    unfold Representation.digitBase CandidateParameters.domainSize
    exact
      TreeEval.CookMertz.PrimeGrouped.Logarithmic.domainSize_pos _ _
  have hbankBase :
      0 < Representation.fieldBase instanceData :=
    pow_pos hdigitBase _
  have hprime :
      (NeighborhoodExecutableEvaluation.modulus
        tm instanceData.blockLength).Prime := by
    unfold NeighborhoodExecutableEvaluation.modulus
    exact
      TreeEval.CookMertz.PrimeField.Search.searchModulus_prime _
  have hmodulusBase :
      NeighborhoodExecutableEvaluation.modulus
          tm instanceData.blockLength ≤
        Representation.fieldBase instanceData := by
    have hlt :=
      CandidateParameters.RadixBounds.canonicalModulus_lt_bankRadix
        tm.Q workTapeCount instanceData.candidateTime
    rw [← NeighborhoodTrial.fieldModulus_eq_canonicalModulus
      instanceData] at hlt
    rw [CandidateParameters.RadixBounds.bankRadix_eq_domainSize_sq]
      at hlt
    simpa [NeighborhoodScheduler.fieldModulus,
      Representation.fieldBase, Representation.digitBase] using
      Nat.le_of_lt hlt
  have hresidueLt :
      residue <
        NeighborhoodExecutableEvaluation.modulus
          tm instanceData.blockLength := by
    have hphaseBound := hframeBound.2.2.2
    simp only [hphase,
      NeighborhoodScheduler.FrameBounds.PhaseBound] at hphaseBound
    unfold NeighborhoodScheduler.fieldModulus at hphaseBound
    omega
  have hresidueDigits :
      residue <
        Representation.digitBase instanceData ^
          FrameCodec.scalarDigitCount := by
    simpa [hphase, ControlDecode.expectedPhaseValues] using
      FrameBounds.frameBound_phaseResidue_lt frame hframeBound
  have hleftDigits :
      residuesLeft <
        Representation.digitBase instanceData ^
          FrameCodec.scalarDigitCount := by
    simpa [hphase, ControlDecode.expectedPhaseValues] using
      FrameBounds.frameBound_phaseResiduesLeft_lt frame hframeBound
  have hactive :
      Representation.ActiveFrame regs frame store :=
    hquery.stack.1
  have hword :
      initialized
          (Layout.residueScaleRegisters regs).bank.bank.word =
        initialized regs.layout.bank := by
    rfl
  have hrep :
      NeighborhoodProgram.RepresentsResidueBank
        tm instanceData.blockLength
        (Representation.fieldBase instanceData)
        (initialized regs.layout.bank) logicalBank := by
    rw [hbankInitialized]
    exact hquery.bank
  have hwordLt :
      initialized regs.layout.bank <
        Representation.fieldBase instanceData ^
          ((NeighborhoodExecutableEvaluation.graphFanIn
              workTapeCount + 1) *
            TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
              (NeighborhoodExecutableEvaluation.payloadWidth
                tm instanceData.blockLength)
              (NeighborhoodExecutableEvaluation.graphFanIn
                workTapeCount)) := by
    rw [hbankInitialized]
    exact hquery.bank_lt
  have hbaseValue :
      initialized
          (Layout.residueScaleRegisters regs).bank.bank.base =
        Representation.fieldBase instanceData := by
    calc
      initialized
          (Layout.residueScaleRegisters regs).bank.bank.base =
          store
            (Layout.residueScaleRegisters regs).bank.bank.base := by
        exact hinitializedPhysical (14 : Fin 34) (by decide)
      _ = Representation.fieldBase instanceData :=
        hquery.parameters.bankBase_eq
  have hmodulusValue :
      initialized
          (Layout.residueScaleRegisters regs).bank.modulus =
        NeighborhoodExecutableEvaluation.modulus
          tm instanceData.blockLength := by
    calc
      initialized
          (Layout.residueScaleRegisters regs).bank.modulus =
          store
            (Layout.residueScaleRegisters regs).bank.modulus := by
        exact hinitializedPhysical (24 : Fin 34) (by decide)
      _ = _ := hquery.parameters.modulus_eq
  have hmodulusPred :
      initialized
          (Layout.residueScaleRegisters regs).bank.modulusPred =
        NeighborhoodExecutableEvaluation.modulus
            tm instanceData.blockLength - 1 := by
    calc
      initialized
          (Layout.residueScaleRegisters regs).bank.modulusPred =
          store
            (Layout.residueScaleRegisters regs).bank.modulusPred := by
        exact hinitializedPhysical (16 : Fin 34) (by decide)
      _ = _ := hquery.parameters.modulusPred_eq
  have hscalar :
      initialized (Layout.scalar regs) = frame.scalar := by
    rw [hinitializedPhysical (25 : Fin 34) (by decide)]
    exact hactive.scalar_eq
  have hout :
      initialized (Layout.out regs) = frame.out.val := by
    rw [hinitializedPhysical (26 : Fin 34) (by decide)]
    exact hactive.out_eq
  have hchunkCount :
      initialized (Layout.chunkCount regs) =
        TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
          (NeighborhoodExecutableEvaluation.payloadWidth
            tm instanceData.blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn
            workTapeCount) := by
    rw [hinitializedPhysical (7 : Fin 34) (by decide)]
    exact hquery.parameters.chunkCount_eq
  have hchunkRadix :
      initialized (Layout.chunkRadix regs) =
        Representation.digitBase instanceData := by
    rw [hinitializedPhysical (8 : Fin 34) (by decide)]
    exact hquery.parameters.digitBase_eq
  have hbankRadix :
      initialized (Layout.bankRadix regs) =
        Representation.digitBase instanceData ^
          FrameCodec.scalarDigitCount := by
    rw [hinitializedPhysical (14 : Fin 34) (by decide)]
    simpa [Representation.fieldBase] using
      hquery.parameters.bankBase_eq
  have hdecodedResidueInitialized :
      initialized (Dispatcher.decodedResidue regs) = residue := by
    rw [hinitializedPhysical (9 : Fin 34) (by decide)]
    exact hdecodedResidue
  have hdecodedLeftInitialized :
      initialized (Dispatcher.decodedResiduesLeft regs) =
        residuesLeft := by
    rw [hinitializedPhysical (10 : Fin 34) (by decide)]
    exact hdecodedLeft
  have hdecodedChildInitialized :
      initialized (Dispatcher.decodedChild regs) = child.val := by
    rw [hinitializedPhysical (11 : Fin 34) (by decide)]
    exact hdecodedChild
  have hdecodedNextInitialized :
      initialized (Dispatcher.decodedNextChild regs) = nextChild := by
    rw [hinitializedPhysical (12 : Fin 34) (by decide)]
    exact hdecodedNext
  obtain ⟨final, finalWord, hcleanup, hpost⟩ :=
    Dispatcher.cleanupScale_runs
      tm instanceData.blockLength frame.scalar residue residuesLeft
      nextChild (Representation.digitBase instanceData)
      (Representation.fieldBase instanceData)
      (initialized regs.layout.bank) logicalBank frame.out child
      regs initialized hprime hdigitBase hbankBase hmodulusBase
      hresidueLt hresidueDigits hleftDigits hword hrep hwordLt
      hbaseValue hmodulusValue hmodulusPred hinitializedOne
      hscalar hout hchunkCount hchunkRadix hbankRadix
      hdecodedResidueInitialized hdecodedLeftInitialized
      hdecodedChildInitialized hdecodedNextInitialized
  have hretained :
      ∀ slot,
        final (regs.index (Dispatcher.cleanupRetainedMap slot)) =
          store (regs.index (Dispatcher.cleanupRetainedMap slot)) := by
    intro slot
    exact (hpost.retained_eq slot).trans
      (hinitializedRetained slot)
  have hparametersFinal :
      Representation.Parameters regs instanceData final := by
    exact
      { blockLength_eq := by
          calc
            final (Layout.blockLength regs) =
                store (Layout.blockLength regs) := by
              simpa [Dispatcher.cleanupRetainedMap,
                Layout.blockLength] using hretained 0
            _ = instanceData.blockLength :=
              hquery.parameters.blockLength_eq
        horizon_eq := by
          calc
            final (Layout.horizon regs) =
                store (Layout.horizon regs) := by
              simpa [Dispatcher.cleanupRetainedMap,
                Layout.horizon] using hretained 1
            _ = instanceData.horizon :=
              hquery.parameters.horizon_eq
        digitBase_eq := by
          calc
            final (Layout.chunkRadix regs) =
                store (Layout.chunkRadix regs) := by
              simpa [Dispatcher.cleanupRetainedMap,
                Layout.chunkRadix] using hretained 3
            _ = Representation.digitBase instanceData :=
              hquery.parameters.digitBase_eq
        bankBase_eq := hpost.base_eq
        frameBase_eq := by
          calc
            final (Layout.frameRadix regs) =
                store (Layout.frameRadix regs) := by
              simpa [Dispatcher.cleanupRetainedMap,
                Layout.frameRadix] using hretained 4
            _ = Representation.frameBase instanceData :=
              hquery.parameters.frameBase_eq
        chunkCount_eq := by
          calc
            final (Layout.chunkCount regs) =
                store (Layout.chunkCount regs) := by
              simpa [Dispatcher.cleanupRetainedMap,
                Layout.chunkCount] using hretained 2
            _ = _ := hquery.parameters.chunkCount_eq
        bankDigitCount_eq := by
          calc
            final (Layout.bankDigitCount regs) =
                store (Layout.bankDigitCount regs) := by
              simpa [Dispatcher.cleanupRetainedMap,
                Layout.bankDigitCount] using hretained 5
            _ = _ := hquery.parameters.bankDigitCount_eq
        modulus_eq := hpost.modulus_eq
        modulusPred_eq := hpost.modulusPred_eq }
  have hactiveFinal :
      Representation.ActiveFrame regs
        (resumedParent frame residue residuesLeft nextChild) final := by
    exact
      { fuel_eq := by
          calc
            final (Layout.fuel regs) =
                store (Layout.fuel regs) := by
              simpa [Dispatcher.cleanupRetainedMap,
                Layout.fuel] using hretained 6
            _ = frame.fuel := hactive.fuel_eq
        node_eq := by
          calc
            final (Layout.nodeCode regs) =
                store (Layout.nodeCode regs) := by
              simpa [Dispatcher.cleanupRetainedMap,
                Layout.nodeCode] using hretained 7
            _ = FrameCodec.encodeNode
                (Representation.digitBase instanceData)
                (resumedParent frame residue residuesLeft
                  nextChild).node := by
              simpa [resumedParent] using hactive.node_eq
        scalar_eq := by
          simpa [resumedParent] using hpost.scalar_eq
        out_eq := by
          simpa [resumedParent] using hpost.out_eq
        phase_eq := by
          simpa [resumedParent] using hpost.phaseCode_eq
        active_eq := by
          calc
            final (Layout.active regs) =
                store (Layout.active regs) := by
              simpa [Dispatcher.cleanupRetainedMap,
                Layout.active] using hretained 8
            _ = 1 := hactive.active_eq }
  have htailFinal :
      FrameTransfer.RepresentsStack regs
        (Representation.digitBase instanceData)
        (Representation.frameBase instanceData) rest final := by
    have htailStore := hquery.stack.2
    unfold FrameTransfer.RepresentsStack at htailStore ⊢
    calc
      final (Layout.frameStackRegisters regs).word =
          store (Layout.frameStackRegisters regs).word := by
        simpa [Dispatcher.cleanupRetainedMap,
          Layout.frameStackRegisters, Layout.frameStackMap] using
          hretained 9
      _ = FrameTransfer.encodeStack
          (Representation.digitBase instanceData)
          (Representation.frameBase instanceData) rest :=
        htailStore
  have hstackFinal :
      Representation.Stack regs
        (resumedParent frame residue residuesLeft nextChild :: rest)
        final :=
    ⟨hactiveFinal, htailFinal⟩
  have hbankFinal :
      NeighborhoodProgram.RepresentsResidueBank
        tm instanceData.blockLength
        (Representation.fieldBase instanceData)
        (final regs.layout.bank)
        (scaledBank frame residue child logicalBank) := by
    change
      NeighborhoodProgram.RepresentsResidueBank
        tm instanceData.blockLength
        (Representation.fieldBase instanceData)
        (final
          (Layout.residueScaleRegisters regs).bank.bank.word)
        (scaledBank frame residue child logicalBank)
    rw [hpost.word_eq]
    simpa [scaledBank, NeighborhoodScheduler.Frame.childTarget,
      NeighborhoodScheduler.fieldModulus] using hpost.represents
  have hbankLtFinal :
      final regs.layout.bank <
        Representation.fieldBase instanceData ^
          ((NeighborhoodExecutableEvaluation.graphFanIn
              workTapeCount + 1) *
            TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
              (NeighborhoodExecutableEvaluation.payloadWidth
                tm instanceData.blockLength)
              (NeighborhoodExecutableEvaluation.graphFanIn
                workTapeCount)) := by
    change
      final
          (Layout.residueScaleRegisters regs).bank.bank.word <
        Representation.fieldBase instanceData ^
          ((NeighborhoodExecutableEvaluation.graphFanIn
              workTapeCount + 1) *
            TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
              (NeighborhoodExecutableEvaluation.payloadWidth
                tm instanceData.blockLength)
              (NeighborhoodExecutableEvaluation.graphFanIn
                workTapeCount))
    rw [hpost.word_eq]
    exact hpost.word_lt
  have hresumedBound :
      NeighborhoodScheduler.FrameBounds.FrameBound
        (resumedParent frame residue residuesLeft nextChild) := by
    simpa [resumedParent, hphase,
      NeighborhoodScheduler.FrameBounds.FrameBound,
      NeighborhoodScheduler.FrameBounds.PhaseBound] using hframeBound
  have hboundsFinal :
      NeighborhoodScheduler.FrameBounds.StateBound
        { stack :=
            resumedParent frame residue residuesLeft nextChild :: rest
          registers :=
            scaledBank frame residue child logicalBank } := by
    intro candidate hcandidate
    simp only [List.mem_cons] at hcandidate
    rcases hcandidate with rfl | hcandidate
    · exact hresumedBound
    · exact hquery.bounds candidate (by simp [hcandidate])
  refine ⟨final, ?_, ?_⟩
  · simpa [step] using Runs.seq hinitialize hcleanup
  · exact
      { parameters := hparametersFinal
        stack := hstackFinal
        bank := hbankFinal
        bank_lt := hbankLtFinal
        bounds := hboundsFinal }

theorem step_next_runs_internal
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (rest : List (NeighborhoodScheduler.Frame tm instanceData))
    (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store)
    (residue residuesLeft nextChild : ℕ)
    (child :
      Fin (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount))
    (hquery :
      Representation.QueryState regs instanceData
        { stack := frame :: rest
          registers := logicalBank }
        store)
    (hphase :
      frame.phase =
        .cleanupScale residue residuesLeft child nextChild)
    (hdecodedResidue :
      store (Dispatcher.decodedResidue regs) = residue)
    (hdecodedLeft :
      store (Dispatcher.decodedResiduesLeft regs) = residuesLeft)
    (hdecodedChild :
      store (Dispatcher.decodedChild regs) = child.val)
    (hdecodedNext :
      store (Dispatcher.decodedNextChild regs) = nextChild) :
    ∃ final,
      Runs (step regs) store final ∧
      Representation.QueryState regs instanceData
        (NeighborhoodScheduler.State.next
          { stack := frame :: rest
            registers := logicalBank })
        final := by
  obtain ⟨final, hrun, hfinal⟩ :=
    step_runs_internal
      frame rest logicalBank regs store residue residuesLeft nextChild
      child hquery hphase hdecodedResidue hdecodedLeft hdecodedChild
      hdecodedNext
  refine ⟨final, hrun, ?_⟩
  simpa [NeighborhoodScheduler.State.next, hphase,
    resumedParent, scaledBank] using hfinal

end Internal
end CleanupScaleStep
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
