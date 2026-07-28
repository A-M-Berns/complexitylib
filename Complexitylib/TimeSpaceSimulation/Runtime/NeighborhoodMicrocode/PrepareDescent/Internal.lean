/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.ChildReady
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.Descent
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.ParentPhase
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.PrepareDescent.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.PrepareScale

/-!
# Concrete prepare-child descent -- proofs
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace PrepareDescent
namespace Internal

open RAM Structured

variable {controller : SearchProgram.Registers}

private theorem cmdWritesWithin_mono
    {small large : Finset ℕ} {command : Cmd}
    (hwrites : Footprint.CmdWritesWithin small command)
    (hsubset : small ⊆ large) :
    Footprint.CmdWritesWithin large command := by
  induction command with
  | skip =>
      trivial
  | basic op =>
      cases op <;>
        simp only [Footprint.CmdWritesWithin,
          Footprint.BasicWritesWithin] at hwrites ⊢
      all_goals exact hsubset hwrites
  | seq first second ihFirst ihSecond =>
      exact ⟨ihFirst hwrites.1, ihSecond hwrites.2⟩
  | ifZero test onZero onNonzero ihZero ihNonzero =>
      exact ⟨ihZero hwrites.1, ihNonzero hwrites.2⟩
  | whileNonzero test body ih =>
      exact ih hwrites

theorem descendChildCore_writesWithin_internal
    (workTapeCount : ℕ)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin regs.layout.footprint
      (descendChildCore workTapeCount controller regs) := by
  simp only [descendChildCore, Cmd.seqList, Footprint.CmdWritesWithin]
  exact
    ⟨cmdWritesWithin_mono
        (PrepareScale.scaleChildTarget_writesWithin regs)
        (PrepareScale.writeFootprint_subset_layout regs),
      ControlDecode.decodePhase_layout_writesWithin regs,
      ParentPhase.suspendPrepare_writesWithin regs,
      cmdWritesWithin_mono
        (ChildReady.prepare_writesWithin
          workTapeCount controller regs)
        (ChildReady.writeFootprint_subset_layout regs),
      cmdWritesWithin_mono
        (FrameInstall.installPrepareChild_writesWithin regs)
        (FrameInstall.writeFootprint_subset_layout regs)⟩

theorem descendChild_writesWithin_internal
    (workTapeCount : ℕ)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin regs.layout.footprint
      (descendChild workTapeCount controller regs) := by
  constructor
  · change regs.index (17 : Fin 34) ∈ regs.layout.footprint
    exact Layout.index_mem_layout_footprint regs 17
  · exact
      descendChildCore_writesWithin_internal
        workTapeCount controller regs

private theorem guess_not_mem_layout
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) :
    controller.guess ∉ regs.layout.footprint := by
  intro hguess
  exact
    Finset.disjoint_left.mp
      (NeighborhoodTrial.Registers.layout_disjoint_controller regs)
      hguess (controller.index_mem_footprint (2 : Fin 17))

private theorem physical_not_mem_residueScale
    (regs : NeighborhoodTrial.Registers controller)
    (slot : Fin 34)
    (hslot : ∀ index, Layout.residueScaleMap index ≠ slot) :
    regs.index slot ∉
      (Layout.residueScaleRegisters regs).footprint := by
  simp only [NeighborhoodProgram.ResidueScaleRegisters.footprint,
    Layout.residueScaleRegisters, Finset.mem_image,
    Finset.mem_univ, true_and, not_exists]
  intro index
  rw [regs.injective.eq_iff]
  exact hslot index

private theorem physical_not_mem_scaleWrite
    (regs : NeighborhoodTrial.Registers controller)
    (slot : Fin 34)
    (hscale : ∀ index, Layout.residueScaleMap index ≠ slot)
    (hscratch : slot ≠ 31)
    (hframe : slot ≠ 29)
    (hscalar : slot ≠ 25)
    (hout : slot ≠ 26) :
    regs.index slot ∉ PrepareScale.writeFootprint regs := by
  simp only [PrepareScale.writeFootprint, Finset.mem_union,
    Finset.mem_insert, Finset.mem_singleton, not_or]
  exact
    ⟨physical_not_mem_residueScale regs slot hscale,
      regs.injective.ne hscratch,
      regs.injective.ne hframe,
      regs.injective.ne hscalar,
      regs.injective.ne hout⟩

private theorem physical_not_mem_decodeScratch
    (regs : NeighborhoodTrial.Registers controller)
    (slot : Fin 34)
    (hslot : ∀ index, ControlDecode.scratchMap index ≠ slot) :
    regs.index slot ∉ ControlDecode.scratchFootprint regs := by
  simp only [ControlDecode.scratchFootprint, Finset.mem_image,
    Finset.mem_univ, true_and, not_exists]
  intro index
  rw [regs.injective.eq_iff]
  exact hslot index

theorem descendChildCore_computation_runs_internal
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (code :
      Fin
        (3 ^
          NeighborhoodGraph.Guess.Enumeration.movementCount
            workTapeCount instanceData.horizon))
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (rest : List (NeighborhoodScheduler.Frame tm instanceData))
    (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store)
    (parentTape tape : TapeIndex workTapeCount)
    (parentSlot : NeighborhoodGraph.Slot)
    (kind : NeighborhoodGraph.PredecessorKind)
    (interval residue residuesLeft : ℕ)
    (child :
      Fin (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount))
    (hselected :
      child =
        NeighborhoodGraph.predecessorIndexEquiv
          workTapeCount (kind, tape))
    (hinterval : interval < instanceData.horizon)
    (hquery :
      Representation.QueryState regs instanceData
        { stack := frame :: rest
          registers := logicalBank }
        store)
    (hphase :
      frame.phase =
        .prepare residue residuesLeft child.val)
    (hnode :
      frame.node =
        .graph (.computation parentTape parentSlot interval))
    (hdecodedResidue :
      store (Dispatcher.decodedResidue regs) = residue)
    (hdecodedChild :
      store (Dispatcher.decodedChild regs) = child.val)
    (hone :
      store (Dispatcher.cleanupInverseRegisters regs).one = 1)
    (hstoreGuess : store controller.guess = code.val)
    (hguess :
      instanceData.guess =
        NeighborhoodGraph.Guess.Enumeration.candidateGuess code) :
    ∃ final,
      Runs
        (descendChildCore workTapeCount controller regs)
        store final ∧
      Representation.QueryState regs instanceData
        { stack :=
            frame.prepareChild child ::
              advancedParent frame residue residuesLeft child ::
              rest
          registers :=
            NeighborhoodExecutableEvaluation.Residue.scaleAt
              tm instanceData.blockLength residue logicalBank
              (frame.childTarget child) }
        final := by
  have hframeBound :
      NeighborhoodScheduler.FrameBounds.FrameBound frame :=
    hquery.bounds frame (by simp)
  have hdigitBase :
      0 < Representation.digitBase instanceData := by
    unfold Representation.digitBase CandidateParameters.domainSize
    exact
      TreeEval.CookMertz.PrimeGrouped.Logarithmic.domainSize_pos _ _
  have hfieldBase :
      0 < Representation.fieldBase instanceData := by
    exact Nat.pow_pos hdigitBase
  have hmodulus :
      0 <
        NeighborhoodExecutableEvaluation.modulus
          tm instanceData.blockLength := by
    change 0 < NeighborhoodScheduler.fieldModulus instanceData
    have hone :=
      NeighborhoodScheduler.FrameBounds.fieldModulus_one_lt
        instanceData
    omega
  have hmodulusBase :
      NeighborhoodExecutableEvaluation.modulus
          tm instanceData.blockLength ≤
        Representation.fieldBase instanceData := by
    change
      NeighborhoodScheduler.fieldModulus instanceData ≤
        Representation.fieldBase instanceData
    rw [NeighborhoodTrial.fieldModulus_eq_canonicalModulus,
      Representation.fieldBase_eq_bankRadix]
    exact Nat.le_of_lt
      (CandidateParameters.RadixBounds.canonicalModulus_lt_bankRadix
        tm.Q workTapeCount instanceData.candidateTime)
  have hresidue :
      residue <
        Representation.digitBase instanceData ^
          FrameCodec.scalarDigitCount := by
    simpa [hphase, ControlDecode.expectedPhaseValues] using
      FrameBounds.frameBound_phaseResidue_lt frame hframeBound
  have hleft :
      residuesLeft <
        Representation.digitBase instanceData ^
          FrameCodec.scalarDigitCount := by
    simpa [hphase, ControlDecode.expectedPhaseValues] using
      FrameBounds.frameBound_phaseResiduesLeft_lt frame hframeBound
  have hadvancedBound :
      NeighborhoodScheduler.FrameBounds.FrameBound
        (advancedParent frame residue residuesLeft child) := by
    simpa only [advancedParent] using
      ParentPhase.frameBound_advancePrepare
        frame residue residuesLeft child hphase hframeBound
  have hword :
      store
          (Layout.residueScaleRegisters regs).bank.bank.word =
        store regs.layout.bank := by
    rfl
  have hbaseValue :
      store
          (Layout.residueScaleRegisters regs).bank.bank.base =
        Representation.fieldBase instanceData := by
    simpa [Layout.residueScaleRegisters, Layout.residueScaleMap,
      NeighborhoodProgram.ResidueScaleRegisters.bank,
      NeighborhoodProgram.ResidueScaleRegisters.bankSlot,
      NeighborhoodProgram.ResidueBankRegisters.bank,
      NeighborhoodProgram.ResidueBankRegisters.bankSlot] using
        hquery.parameters.bankBase_eq
  have hmodulusValue :
      store (Layout.residueScaleRegisters regs).bank.modulus =
        NeighborhoodExecutableEvaluation.modulus
          tm instanceData.blockLength := by
    simpa [Layout.residueScaleRegisters, Layout.residueScaleMap,
      NeighborhoodProgram.ResidueScaleRegisters.bank,
      NeighborhoodProgram.ResidueScaleRegisters.bankSlot,
      NeighborhoodProgram.ResidueBankRegisters.modulus,
      NeighborhoodScheduler.fieldModulus] using
        hquery.parameters.modulus_eq
  have hmodulusPred :
      store (Layout.residueScaleRegisters regs).bank.modulusPred =
        NeighborhoodExecutableEvaluation.modulus
            tm instanceData.blockLength -
          1 := by
    simpa [Layout.residueScaleRegisters, Layout.residueScaleMap,
      NeighborhoodProgram.ResidueScaleRegisters.bank,
      NeighborhoodProgram.ResidueScaleRegisters.bankSlot,
      NeighborhoodProgram.ResidueBankRegisters.modulusPred,
      NeighborhoodScheduler.fieldModulus] using
        hquery.parameters.modulusPred_eq
  obtain ⟨scaled, scaledWord, hscaleRun, hscalePost⟩ :=
    PrepareScale.scaleChildTarget_runs
      tm instanceData.blockLength frame.scalar residue
      (Representation.fieldBase instanceData)
      (store regs.layout.bank) logicalBank frame.out child regs store
      hfieldBase hmodulus hmodulusBase hword hquery.bank
      hquery.bank_lt hbaseValue hmodulusValue hmodulusPred hone
      hquery.stack.1.scalar_eq hquery.stack.1.out_eq
      hquery.parameters.chunkCount_eq hdecodedResidue hdecodedChild
  have hscaledRetained :
      ∀ slot : Fin 11,
        scaled
            (regs.index
              (![2, 3, 7, 8, 13, 15, 22, 23, 27, 28, 32] slot)) =
          store
            (regs.index
              (![2, 3, 7, 8, 13, 15, 22, 23, 27, 28, 32] slot)) := by
    intro slot
    apply hscalePost.eq_outside
    apply physical_not_mem_scaleWrite
    · intro index
      fin_cases slot <;> fin_cases index <;> decide
    · fin_cases slot <;> decide
    · fin_cases slot <;> decide
    · fin_cases slot <;> decide
    · fin_cases slot <;> decide
  have hactiveScaled :
      Representation.ActiveFrame regs frame scaled :=
    { fuel_eq :=
        (hscaledRetained (6 : Fin 11)).trans
          hquery.stack.1.fuel_eq
      node_eq :=
        (hscaledRetained (7 : Fin 11)).trans
          hquery.stack.1.node_eq
      scalar_eq := hscalePost.scalar_eq
      out_eq := hscalePost.out_eq
      phase_eq :=
        (hscaledRetained (8 : Fin 11)).trans
          hquery.stack.1.phase_eq
      active_eq :=
        (hscaledRetained (9 : Fin 11)).trans
          hquery.stack.1.active_eq }
  have hparametersScaled :
      Representation.Parameters regs instanceData scaled :=
    { blockLength_eq :=
        (hscaledRetained (0 : Fin 11)).trans
          hquery.parameters.blockLength_eq
      horizon_eq :=
        (hscaledRetained (1 : Fin 11)).trans
          hquery.parameters.horizon_eq
      digitBase_eq :=
        (hscaledRetained (3 : Fin 11)).trans
          hquery.parameters.digitBase_eq
      bankBase_eq := by
        simpa [Layout.residueScaleRegisters, Layout.residueScaleMap,
          NeighborhoodProgram.ResidueScaleRegisters.bank,
          NeighborhoodProgram.ResidueScaleRegisters.bankSlot,
          NeighborhoodProgram.ResidueBankRegisters.bank,
          NeighborhoodProgram.ResidueBankRegisters.bankSlot] using
            hscalePost.base_eq
      frameBase_eq :=
        (hscaledRetained (4 : Fin 11)).trans
          hquery.parameters.frameBase_eq
      chunkCount_eq :=
        (hscaledRetained (2 : Fin 11)).trans
          hquery.parameters.chunkCount_eq
      bankDigitCount_eq :=
        (hscaledRetained (5 : Fin 11)).trans
          hquery.parameters.bankDigitCount_eq
      modulus_eq := by
        simpa [Layout.residueScaleRegisters, Layout.residueScaleMap,
          NeighborhoodProgram.ResidueScaleRegisters.bank,
          NeighborhoodProgram.ResidueScaleRegisters.bankSlot,
          NeighborhoodProgram.ResidueBankRegisters.modulus,
          NeighborhoodScheduler.fieldModulus] using
            hscalePost.modulus_eq
      modulusPred_eq := by
        simpa [Layout.residueScaleRegisters, Layout.residueScaleMap,
          NeighborhoodProgram.ResidueScaleRegisters.bank,
          NeighborhoodProgram.ResidueScaleRegisters.bankSlot,
          NeighborhoodProgram.ResidueBankRegisters.modulusPred,
          NeighborhoodScheduler.fieldModulus] using
            hscalePost.modulusPred_eq }
  have hstackScaled :
      Representation.Stack regs (frame :: rest) scaled := by
    refine ⟨hactiveScaled, ?_⟩
    unfold FrameTransfer.RepresentsStack
    change scaled (regs.index 32) = _
    exact
      (hscaledRetained (10 : Fin 11)).trans hquery.stack.2
  have hbankScaled :
      NeighborhoodProgram.RepresentsResidueBank
        tm instanceData.blockLength
        (Representation.fieldBase instanceData)
        (scaled regs.layout.bank)
        (NeighborhoodExecutableEvaluation.Residue.scaleAt
          tm instanceData.blockLength residue logicalBank
          (frame.childTarget child)) := by
    change
      NeighborhoodProgram.RepresentsResidueBank
        tm instanceData.blockLength
        (Representation.fieldBase instanceData)
        (scaled
          (Layout.residueScaleRegisters regs).bank.bank.word)
        _
    rw [hscalePost.word_eq]
    simpa [NeighborhoodScheduler.Frame.childTarget] using
      hscalePost.represents
  have hguessScaled : scaled controller.guess = code.val := by
    calc
      scaled controller.guess = store controller.guess :=
        hscalePost.eq_outside _ (by
          intro hmember
          exact
            guess_not_mem_layout controller regs
              (PrepareScale.writeFootprint_subset_layout regs hmember))
      _ = code.val := hstoreGuess
  obtain ⟨decoded, hdecodeRun, hdecodedPost,
      hactiveDecoded, hparametersDecoded⟩ :=
    Representation.ActiveFrame.decodePhase_runs
      regs frame scaled hactiveScaled hparametersScaled hframeBound
  have hdecodeStackWord :
      decoded (regs.index 32) = scaled (regs.index 32) :=
    Footprint.runs_eq_outside
      (ControlDecode.decodePhase_writesWithin regs)
      hdecodeRun
      (physical_not_mem_decodeScratch regs 32 (by
        intro index
        fin_cases index <;> decide))
  have hdecodeBankWord :
      decoded regs.layout.bank = scaled regs.layout.bank := by
    change decoded (regs.index 33) = scaled (regs.index 33)
    exact
      Footprint.runs_eq_outside
        (ControlDecode.decodePhase_writesWithin regs)
        hdecodeRun
        (physical_not_mem_decodeScratch regs 33 (by
          intro index
          fin_cases index <;> decide))
  have hstackDecoded :
      Representation.Stack regs (frame :: rest) decoded := by
    refine ⟨hactiveDecoded, ?_⟩
    unfold FrameTransfer.RepresentsStack
    change decoded (regs.index 32) = _
    exact hdecodeStackWord.trans hstackScaled.2
  have hbankDecoded :
      NeighborhoodProgram.RepresentsResidueBank
        tm instanceData.blockLength
        (Representation.fieldBase instanceData)
        (decoded regs.layout.bank)
        (NeighborhoodExecutableEvaluation.Residue.scaleAt
          tm instanceData.blockLength residue logicalBank
          (frame.childTarget child)) := by
    rw [hdecodeBankWord]
    exact hbankScaled
  have hguessDecoded : decoded controller.guess = code.val := by
    calc
      decoded controller.guess = scaled controller.guess :=
        Footprint.runs_eq_outside
          (ControlDecode.decodePhase_layout_writesWithin regs)
          hdecodeRun (guess_not_mem_layout controller regs)
      _ = code.val := hguessScaled
  have hdecodedResidue' :
      decoded (Dispatcher.decodedResidue regs) = residue := by
    simpa [hphase, ControlDecode.expectedPhaseValues] using
      hdecodedPost.residue_eq
  have hdecodedLeft' :
      decoded (Dispatcher.decodedResiduesLeft regs) =
        residuesLeft := by
    simpa [hphase, ControlDecode.expectedPhaseValues] using
      hdecodedPost.residuesLeft_eq
  have hdecodedChild' :
      decoded (Dispatcher.decodedChild regs) = child.val := by
    simpa [hphase, ControlDecode.expectedPhaseValues] using
      hdecodedPost.child_eq
  have hdecodedNext' :
      decoded (Dispatcher.decodedNextChild regs) = 0 := by
    simpa [hphase, ControlDecode.expectedPhaseValues] using
      hdecodedPost.next_eq
  obtain ⟨suspended, hsuspend, hsuspendedStack,
      hparametersSuspended, hbankSuspended, hsavedChild,
      hactiveSuspended⟩ :=
    ParentPhase.suspendPrepare_runs
      regs frame rest decoded residue residuesLeft child hstackDecoded
      hparametersDecoded hdigitBase hresidue hleft hdecodedResidue'
      hdecodedLeft' hdecodedChild' hdecodedNext' hadvancedBound
  have hguessSuspended :
      suspended controller.guess = code.val := by
    calc
      suspended controller.guess = decoded controller.guess :=
        Footprint.runs_eq_outside
          (ParentPhase.suspendPrepare_writesWithin regs)
          hsuspend (guess_not_mem_layout controller regs)
      _ = code.val := hguessDecoded
  have hsavedSelected :
      suspended (ChildNode.savedChildIndex regs) =
        (NeighborhoodGraph.predecessorIndexEquiv
          workTapeCount (kind, tape)).val := by
    rw [← hselected]
    exact hsavedChild
  have hadvancedNode :
      (advancedParent frame residue residuesLeft child).node =
        .graph (.computation parentTape parentSlot interval) := by
    simpa only [advancedParent] using hnode
  obtain ⟨ready, hreadyRun, hready⟩ :=
    ChildReady.prepare_frameChild_runs
      code (advancedParent frame residue residuesLeft child)
      controller regs suspended parentTape tape parentSlot kind interval
      hinterval hactiveSuspended hparametersSuspended
      hadvancedBound hsavedSelected hguessSuspended hguess
      hadvancedNode
  have hparametersReady :
      Representation.Parameters regs instanceData ready :=
    ChildReady.Parameters.of_readyPost
      regs suspended ready hparametersSuspended hready
  have hsuspendedReady :
      FrameTransfer.RepresentsStack regs
        (Representation.digitBase instanceData)
        (Representation.frameBase instanceData)
        (advancedParent frame residue residuesLeft child :: rest)
        ready := by
    unfold FrameTransfer.RepresentsStack at hsuspendedStack ⊢
    rw [ChildReady.ReadyPost.stackWord_eq regs hready]
    exact hsuspendedStack
  have hbankAtSuspended :
      NeighborhoodProgram.RepresentsResidueBank
        tm instanceData.blockLength
        (Representation.fieldBase instanceData)
        (suspended regs.layout.bank)
        (NeighborhoodExecutableEvaluation.Residue.scaleAt
          tm instanceData.blockLength residue logicalBank
          (frame.childTarget child)) := by
    rw [hbankSuspended]
    exact hbankDecoded
  have hbankReady :
      NeighborhoodProgram.RepresentsResidueBank
        tm instanceData.blockLength
        (Representation.fieldBase instanceData)
        (ready regs.layout.bank)
        (NeighborhoodExecutableEvaluation.Residue.scaleAt
          tm instanceData.blockLength residue logicalBank
          (frame.childTarget child)) := by
    rw [ChildReady.ReadyPost.bank_eq regs hready]
    exact hbankAtSuspended
  have hbankLtReady :
      ready regs.layout.bank <
        Representation.fieldBase instanceData ^
          ((NeighborhoodExecutableEvaluation.graphFanIn
              workTapeCount + 1) *
            TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
              (NeighborhoodExecutableEvaluation.payloadWidth
                tm instanceData.blockLength)
              (NeighborhoodExecutableEvaluation.graphFanIn
                workTapeCount)) := by
    rw [ChildReady.ReadyPost.bank_eq regs hready, hbankSuspended,
      hdecodeBankWord]
    change
      scaled
          (Layout.residueScaleRegisters regs).bank.bank.word <
        _
    rw [hscalePost.word_eq]
    exact hscalePost.word_lt
  have hfuelReady :
      ready (Layout.fuel regs) = frame.fuel := by
    calc
      ready (Layout.fuel regs) =
          suspended (Layout.fuel regs) :=
        hready.fuel_eq
      _ = (advancedParent frame residue residuesLeft child).fuel :=
        hactiveSuspended.fuel_eq
      _ = frame.fuel := rfl
  have hnodeReady :
      ready (Layout.nodeCode regs) =
        FrameCodec.encodeNode
          (Representation.digitBase instanceData)
          (frame.childNode child) := by
    calc
      ready (Layout.nodeCode regs) =
          FrameCodec.encodeNode
            (suspended (Layout.chunkRadix regs))
            ((advancedParent frame residue residuesLeft child).childNode
              (NeighborhoodGraph.predecessorIndexEquiv
                workTapeCount (kind, tape))) :=
        hready.nodeCode_eq
      _ = FrameCodec.encodeNode
          (Representation.digitBase instanceData)
          ((advancedParent frame residue residuesLeft child).childNode
            (NeighborhoodGraph.predecessorIndexEquiv
              workTapeCount (kind, tape))) := by
        rw [hparametersSuspended.digitBase_eq]
      _ = FrameCodec.encodeNode
          (Representation.digitBase instanceData)
          (frame.childNode child) := by
        rw [← hselected]
        rfl
  have houtReady :
      ready (Layout.out regs) = (frame.childTarget child).val := by
    calc
      ready (Layout.out regs) =
          ((advancedParent frame residue residuesLeft child).childTarget
            (NeighborhoodGraph.predecessorIndexEquiv
              workTapeCount (kind, tape))).val :=
        hready.out_eq
      _ = (frame.childTarget child).val := by
        rw [← hselected]
        rfl
  have hparentFields :
      (advancedParent frame residue residuesLeft child).fuel =
          frame.fuel ∧
      (advancedParent frame residue residuesLeft child).node =
          frame.node ∧
      (advancedParent frame residue residuesLeft child).scalar =
          frame.scalar ∧
      (advancedParent frame residue residuesLeft child).out =
          frame.out := by
    simp [advancedParent]
  have hrestBounds :
      ∀ candidate ∈ rest,
        NeighborhoodScheduler.FrameBounds.FrameBound candidate := by
    intro candidate hcandidate
    exact hquery.bounds candidate (by simp [hcandidate])
  obtain ⟨final, hfinish, hfinal⟩ :=
    Descent.finishPrepare_runs
      regs frame
      (advancedParent frame residue residuesLeft child)
      rest child
      (NeighborhoodExecutableEvaluation.Residue.scaleAt
        tm instanceData.blockLength residue logicalBank
        (frame.childTarget child))
      ready hparentFields hsuspendedReady hparametersReady
      hbankReady hbankLtReady hfuelReady hnodeReady houtReady
      hframeBound hadvancedBound hrestBounds
  refine ⟨final, ?_, hfinal⟩
  simpa [descendChildCore, Cmd.seqList] using
    Runs.seq hscaleRun
      (Runs.seq hdecodeRun
        (Runs.seq hsuspend (Runs.seq hreadyRun hfinish)))

theorem descendChild_computation_runs_internal
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (code :
      Fin
        (3 ^
          NeighborhoodGraph.Guess.Enumeration.movementCount
            workTapeCount instanceData.horizon))
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (rest : List (NeighborhoodScheduler.Frame tm instanceData))
    (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store)
    (parentTape tape : TapeIndex workTapeCount)
    (parentSlot : NeighborhoodGraph.Slot)
    (kind : NeighborhoodGraph.PredecessorKind)
    (interval residue residuesLeft : ℕ)
    (child :
      Fin (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount))
    (hselected :
      child =
        NeighborhoodGraph.predecessorIndexEquiv
          workTapeCount (kind, tape))
    (hinterval : interval < instanceData.horizon)
    (hquery :
      Representation.QueryState regs instanceData
        { stack := frame :: rest
          registers := logicalBank }
        store)
    (hphase :
      frame.phase =
        .prepare residue residuesLeft child.val)
    (hnode :
      frame.node =
        .graph (.computation parentTape parentSlot interval))
    (hdecodedResidue :
      store (Dispatcher.decodedResidue regs) = residue)
    (hdecodedChild :
      store (Dispatcher.decodedChild regs) = child.val)
    (hstoreGuess : store controller.guess = code.val)
    (hguess :
      instanceData.guess =
        NeighborhoodGraph.Guess.Enumeration.candidateGuess code) :
    ∃ final,
      Runs
        (descendChild workTapeCount controller regs)
        store final ∧
      Representation.QueryState regs instanceData
        { stack :=
            frame.prepareChild child ::
              advancedParent frame residue residuesLeft child ::
              rest
          registers :=
            NeighborhoodExecutableEvaluation.Residue.scaleAt
              tm instanceData.blockLength residue logicalBank
              (frame.childTarget child) }
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
  have hactiveInitialized :
      Representation.ActiveFrame regs frame initialized :=
    { fuel_eq := by
        rw [hinitializedPhysical (22 : Fin 34) (by decide)]
        exact hquery.stack.1.fuel_eq
      node_eq := by
        rw [hinitializedPhysical (23 : Fin 34) (by decide)]
        exact hquery.stack.1.node_eq
      scalar_eq := by
        rw [hinitializedPhysical (25 : Fin 34) (by decide)]
        exact hquery.stack.1.scalar_eq
      out_eq := by
        rw [hinitializedPhysical (26 : Fin 34) (by decide)]
        exact hquery.stack.1.out_eq
      phase_eq := by
        rw [hinitializedPhysical (27 : Fin 34) (by decide)]
        exact hquery.stack.1.phase_eq
      active_eq := by
        rw [hinitializedPhysical (28 : Fin 34) (by decide)]
        exact hquery.stack.1.active_eq }
  have htailInitialized :
      FrameTransfer.RepresentsStack regs
        (Representation.digitBase instanceData)
        (Representation.frameBase instanceData) rest initialized := by
    unfold FrameTransfer.RepresentsStack
    change initialized (regs.index 32) = _
    rw [hinitializedPhysical (32 : Fin 34) (by decide)]
    exact hquery.stack.2
  have hparametersInitialized :
      Representation.Parameters regs instanceData initialized :=
    { blockLength_eq := by
        rw [hinitializedPhysical (2 : Fin 34) (by decide)]
        exact hquery.parameters.blockLength_eq
      horizon_eq := by
        rw [hinitializedPhysical (3 : Fin 34) (by decide)]
        exact hquery.parameters.horizon_eq
      digitBase_eq := by
        rw [hinitializedPhysical (8 : Fin 34) (by decide)]
        exact hquery.parameters.digitBase_eq
      bankBase_eq := by
        rw [hinitializedPhysical (14 : Fin 34) (by decide)]
        exact hquery.parameters.bankBase_eq
      frameBase_eq := by
        rw [hinitializedPhysical (13 : Fin 34) (by decide)]
        exact hquery.parameters.frameBase_eq
      chunkCount_eq := by
        rw [hinitializedPhysical (7 : Fin 34) (by decide)]
        exact hquery.parameters.chunkCount_eq
      bankDigitCount_eq := by
        rw [hinitializedPhysical (15 : Fin 34) (by decide)]
        exact hquery.parameters.bankDigitCount_eq
      modulus_eq := by
        rw [hinitializedPhysical (24 : Fin 34) (by decide)]
        exact hquery.parameters.modulus_eq
      modulusPred_eq := by
        rw [hinitializedPhysical (16 : Fin 34) (by decide)]
        exact hquery.parameters.modulusPred_eq }
  have hbankInitialized :
      initialized regs.layout.bank = store regs.layout.bank := by
    change initialized (regs.index 33) = store (regs.index 33)
    exact hinitializedPhysical (33 : Fin 34) (by decide)
  have hqueryInitialized :
      Representation.QueryState regs instanceData
        { stack := frame :: rest
          registers := logicalBank }
        initialized :=
    { parameters := hparametersInitialized
      stack := ⟨hactiveInitialized, htailInitialized⟩
      bank := by
        rw [hbankInitialized]
        exact hquery.bank
      bank_lt := by
        rw [hbankInitialized]
        exact hquery.bank_lt
      bounds := hquery.bounds }
  have hdecodedResidueInitialized :
      initialized (Dispatcher.decodedResidue regs) = residue := by
    rw [hinitializedPhysical (9 : Fin 34) (by decide)]
    exact hdecodedResidue
  have hdecodedChildInitialized :
      initialized (Dispatcher.decodedChild regs) = child.val := by
    rw [hinitializedPhysical (11 : Fin 34) (by decide)]
    exact hdecodedChild
  have hguessInitialized :
      initialized controller.guess = code.val := by
    change
      Function.update store (regs.index 17) 1 controller.guess =
        code.val
    rw [Function.update_of_ne
      (regs.index_ne_controller (17 : Fin 34) (2 : Fin 17)).symm]
    exact hstoreGuess
  obtain ⟨final, hcore, hfinal⟩ :=
    descendChildCore_computation_runs_internal
      code frame rest logicalBank controller regs initialized
      parentTape tape parentSlot kind interval residue residuesLeft
      child hselected hinterval hqueryInitialized hphase hnode
      hdecodedResidueInitialized hdecodedChildInitialized
      hinitializedOne hguessInitialized hguess
  refine ⟨final, ?_, hfinal⟩
  simpa [descendChild] using Runs.seq hinitialize hcore

end Internal
end PrepareDescent
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
