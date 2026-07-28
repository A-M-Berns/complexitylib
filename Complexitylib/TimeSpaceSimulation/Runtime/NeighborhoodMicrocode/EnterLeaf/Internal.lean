/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.EnterLeaf.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.FrameBounds
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.Representation
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.ResidueBankOps
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.SourceValue
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodTrial
import
  Complexitylib.Models.RandomAccessMachine.Structured.Footprint

/-!
# Entry transitions for failure and source leaves -- proofs
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace EnterLeaf
namespace Internal

open RAM Structured
open TreeEval CookMertz
open NeighborhoodExecutableEvaluation

variable {controller : SearchProgram.Registers}

private theorem cmdWritesWithin_mono
    {small large : Finset ℕ} (hsub : small ⊆ large)
    {cmd : Cmd}
    (hwrites : Footprint.CmdWritesWithin small cmd) :
    Footprint.CmdWritesWithin large cmd := by
  induction cmd with
  | skip =>
      trivial
  | basic op =>
      cases op <;>
        simp only [Footprint.CmdWritesWithin,
          Footprint.BasicWritesWithin] at hwrites ⊢
      all_goals exact hsub hwrites
  | seq first second firstIH secondIH =>
      exact ⟨firstIH hwrites.1, secondIH hwrites.2⟩
  | ifZero test onZero onNonzero zeroIH nonzeroIH =>
      exact ⟨zeroIH hwrites.1, nonzeroIH hwrites.2⟩
  | whileNonzero test body bodyIH =>
      exact bodyIH hwrites

private theorem basics_runs (ops : List Basic) (store : Store) :
    Runs (Cmd.basics ops) store (Basic.execList ops store) := by
  obtain ⟨cost, space, hexec⟩ :=
    RAM.Structured.Internal.exec_basics_exists ops store
  exact ⟨ops.length, cost, space, hexec⟩

private def copyResultStore
    (destination source : ℕ) (store : Store) : Store :=
  Function.update store destination (store source)

private theorem copy_runs
    (destination source : ℕ) (store : Store)
    (hne : destination ≠ source) :
    Runs (copy destination source) store
      (copyResultStore destination source store) := by
  let cleared := (Basic.imm destination 0).exec store
  have hfirst : Runs (.basic (.imm destination 0)) store cleared :=
    Runs.basic _ _
  have hsecond :
      Runs (.basic (.add destination source destination))
        cleared (copyResultStore destination source store) := by
    have hsource : cleared source = store source := by
      simp [cleared, Basic.exec, hne.symm]
    have hdestination : cleared destination = 0 := by
      simp [cleared, Basic.exec]
    simpa [copyResultStore, cleared, Basic.exec, hsource,
      hdestination, hne.symm] using
      Runs.basic (Basic.add destination source destination) cleared
  exact Runs.seq hfirst hsecond

private theorem index_not_mem_mapped
    (regs : NeighborhoodTrial.Registers controller)
    (map : Fin count → Fin 34) (target : Fin 34)
    (hne : ∀ slot, map slot ≠ target) :
    regs.index target ∉
      Finset.univ.image (fun slot => regs.index (map slot)) := by
  simp only [Finset.mem_image, Finset.mem_univ, true_and,
    not_exists]
  intro slot heq
  exact hne slot (regs.injective heq)

private theorem source_index_not_mem
    (regs : NeighborhoodTrial.Registers controller)
    (target : Fin 34)
    (hne : ∀ slot, SourceValue.writeMap slot ≠ target) :
    regs.index target ∉ SourceValue.writeFootprint regs :=
  index_not_mem_mapped regs SourceValue.writeMap target hne

private theorem decode_index_not_mem
    (regs : NeighborhoodTrial.Registers controller)
    (target : Fin 34)
    (hne : ∀ slot, ControlDecode.scratchMap slot ≠ target) :
    regs.index target ∉ ControlDecode.scratchFootprint regs :=
  index_not_mem_mapped regs ControlDecode.scratchMap target hne

private theorem scale_index_not_mem
    (regs : NeighborhoodTrial.Registers controller)
    (target : Fin 34)
    (hne : ∀ slot, Layout.residueScaleMap slot ≠ target) :
    regs.index target ∉
      (Layout.residueScaleRegisters regs).footprint :=
  index_not_mem_mapped regs Layout.residueScaleMap target hne

private theorem sourceFootprint_preservesABI
    (regs : NeighborhoodTrial.Registers controller)
    {command : Cmd} {initial final : Store}
    (hwrites :
      Footprint.CmdWritesWithin
        (SourceValue.writeFootprint regs) command)
    (hrun : Runs command initial final) :
    ControlDecode.PreservesABI regs initial final := by
  let outside (target : Fin 34)
      (hne : ∀ slot, SourceValue.writeMap slot ≠ target) :
      final (regs.index target) = initial (regs.index target) :=
    Footprint.runs_eq_outside hwrites hrun
      (source_index_not_mem regs target hne)
  exact
    { fuel_eq := outside 22 (by intro slot; fin_cases slot <;> decide)
      nodeCode_eq :=
        outside 23 (by intro slot; fin_cases slot <;> decide)
      scalar_eq :=
        outside 25 (by intro slot; fin_cases slot <;> decide)
      out_eq := outside 26 (by intro slot; fin_cases slot <;> decide)
      phaseCode_eq :=
        outside 27 (by intro slot; fin_cases slot <;> decide)
      active_eq :=
        outside 28 (by intro slot; fin_cases slot <;> decide)
      blockLength_eq :=
        outside 2 (by intro slot; fin_cases slot <;> decide)
      horizon_eq :=
        outside 3 (by intro slot; fin_cases slot <;> decide)
      chunkCount_eq :=
        outside 7 (by intro slot; fin_cases slot <;> decide)
      chunkRadix_eq :=
        outside 8 (by intro slot; fin_cases slot <;> decide)
      frameRadix_eq :=
        outside 13 (by intro slot; fin_cases slot <;> decide)
      bankRadix_eq :=
        outside 14 (by intro slot; fin_cases slot <;> decide)
      bankDigitCount_eq :=
        outside 15 (by intro slot; fin_cases slot <;> decide)
      modulusPred_eq :=
        outside 16 (by intro slot; fin_cases slot <;> decide)
      modulus_eq :=
        outside 24 (by intro slot; fin_cases slot <;> decide) }

private theorem preservesABI_trans
    (regs : NeighborhoodTrial.Registers controller)
    {first second third : Store}
    (hfirst : ControlDecode.PreservesABI regs first second)
    (hsecond : ControlDecode.PreservesABI regs second third) :
    ControlDecode.PreservesABI regs first third :=
  { fuel_eq := hsecond.fuel_eq.trans hfirst.fuel_eq
    nodeCode_eq := hsecond.nodeCode_eq.trans hfirst.nodeCode_eq
    scalar_eq := hsecond.scalar_eq.trans hfirst.scalar_eq
    out_eq := hsecond.out_eq.trans hfirst.out_eq
    phaseCode_eq := hsecond.phaseCode_eq.trans hfirst.phaseCode_eq
    active_eq := hsecond.active_eq.trans hfirst.active_eq
    blockLength_eq :=
      hsecond.blockLength_eq.trans hfirst.blockLength_eq
    horizon_eq := hsecond.horizon_eq.trans hfirst.horizon_eq
    chunkCount_eq :=
      hsecond.chunkCount_eq.trans hfirst.chunkCount_eq
    chunkRadix_eq :=
      hsecond.chunkRadix_eq.trans hfirst.chunkRadix_eq
    frameRadix_eq :=
      hsecond.frameRadix_eq.trans hfirst.frameRadix_eq
    bankRadix_eq :=
      hsecond.bankRadix_eq.trans hfirst.bankRadix_eq
    bankDigitCount_eq :=
      hsecond.bankDigitCount_eq.trans hfirst.bankDigitCount_eq
    modulusPred_eq :=
      hsecond.modulusPred_eq.trans hfirst.modulusPred_eq
    modulus_eq := hsecond.modulus_eq.trans hfirst.modulus_eq }

private theorem controller_eq_of_layout_run
    (regs : NeighborhoodTrial.Registers controller)
    (slot : Fin 17) {command : Cmd} {initial final : Store}
    (hwrites :
      Footprint.CmdWritesWithin regs.layout.footprint command)
    (hrun : Runs command initial final) :
    final (controller.index slot) = initial (controller.index slot) := by
  apply Footprint.runs_eq_outside hwrites hrun
  exact fun hmem =>
    Finset.disjoint_left.mp
      (NeighborhoodTrial.Registers.layout_disjoint_controller regs)
      hmem (controller.index_mem_footprint slot)

private theorem inputFrame_of_layout_run
    (regs : NeighborhoodTrial.Registers controller)
    (input : List Bool) {command : Cmd} {initial final : Store}
    (hwrites :
      Footprint.CmdWritesWithin regs.layout.footprint command)
    (hrun : Runs command initial final)
    (hframe :
      SearchProgram.InputFrame
        controller regs.footprint input initial) :
    SearchProgram.InputFrame controller regs.footprint input final := by
  constructor
  · exact
      (controller_eq_of_layout_run regs (16 : Fin 17)
        hwrites hrun).trans hframe.1
  · intro address hlimit
    calc
      final address = initial address := by
        apply Footprint.runs_eq_outside hwrites hrun
        intro hmember
        have hall :
            address ∈ controller.footprint ∪ regs.footprint := by
          apply Finset.mem_union_right
          exact Finset.mem_union_left _ hmember
        have hle :
            address ≤
              SearchProgram.footprintLimit
                controller regs.footprint :=
          Finset.le_sup (f := fun value : ℕ => value) hall
        omega
      _ = RAM.initRegs input address := hframe.2 address hlimit

theorem addScaledPrefix_zero_internal
    (tm : TM workTapeCount) (blockLength scalar : ℕ)
    (original : Residue.Registers tm blockLength)
    (out : Fin (graphFanIn workTapeCount + 1))
    (value : ResidueValue tm blockLength) :
    addScaledPrefix tm blockLength scalar original out value 0 =
      original := by
  funext register chunk
  simp [addScaledPrefix]

theorem addScaledPrefix_succ_internal
    (tm : TM workTapeCount) (blockLength scalar processed : ℕ)
    (original : Residue.Registers tm blockLength)
    (out : Fin (graphFanIn workTapeCount + 1))
    (value : ResidueValue tm blockLength)
    (hprocessed :
      processed <
        TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
          (payloadWidth tm blockLength)
          (graphFanIn workTapeCount)) :
    NeighborhoodProgram.updateResidueCoordinate
        tm blockLength
        (addScaledPrefix tm blockLength scalar original out value
          processed)
        out ⟨processed, hprocessed⟩
        (NeighborhoodProgram.ResidueBankOp.add.apply
          (modulus tm blockLength)
          (original out ⟨processed, hprocessed⟩)
          ((value ⟨processed, hprocessed⟩ * scalar) %
            modulus tm blockLength)) =
      addScaledPrefix tm blockLength scalar original out value
        (processed + 1) := by
  funext register chunk
  by_cases hr : register = out
  · subst register
    by_cases hc : chunk = ⟨processed, hprocessed⟩
    · subst chunk
      simp [NeighborhoodProgram.updateResidueCoordinate,
        addScaledPrefix]
    · have hv : chunk.val ≠ processed := by
        intro heq
        exact hc (Fin.ext heq)
      by_cases hlt : chunk.val < processed
      · have hlt' : chunk.val < processed + 1 := by omega
        simp [NeighborhoodProgram.updateResidueCoordinate,
          addScaledPrefix, hc, hlt, hlt']
      · have hlt' : ¬chunk.val < processed + 1 := by omega
        simp [NeighborhoodProgram.updateResidueCoordinate,
          addScaledPrefix, hc, hlt, hlt']
  · simp [NeighborhoodProgram.updateResidueCoordinate,
      addScaledPrefix, hr]

theorem addScaledPrefix_full_internal
    (tm : TM workTapeCount)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (scalar : ℕ)
    (original : Residue.Registers tm instanceData.blockLength)
    (out : Fin (graphFanIn workTapeCount + 1))
    (value : ResidueValue tm instanceData.blockLength) :
    addScaledPrefix tm instanceData.blockLength scalar original out value
        (TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
          (payloadWidth tm instanceData.blockLength)
          (graphFanIn workTapeCount)) =
      NeighborhoodScheduler.addScaledAt
        instanceData original out scalar value := by
  funext register chunk
  by_cases hr : register = out
  · subst register
    simp only [addScaledPrefix, true_and, chunk.isLt, if_true,
      NeighborhoodScheduler.addScaledAt, Residue.addAt,
      Function.update_self]
    simp [NeighborhoodProgram.ResidueBankOp.apply,
      Residue.addValue, Residue.scaleValue,
      PrimeField.Runtime.add, PrimeField.Runtime.addInput,
      PrimeField.Runtime.mul, PrimeField.Runtime.mulInput,
      PrimeField.Runtime.normalize, Nat.mul_comm, Nat.add_mod,
      Nat.mul_mod]
  · simp [addScaledPrefix, NeighborhoodScheduler.addScaledAt,
      Residue.addAt, hr]

private theorem initialize_writesWithin
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin regs.layout.footprint
      (initializeLeaf regs) := by
  simp [initializeLeaf, copy, Cmd.seqList,
    Footprint.CmdWritesWithin, Footprint.BasicWritesWithin,
    Layout.index_mem_layout_footprint]

private theorem advanceChunk_writesWithin
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin regs.layout.footprint
      (advanceChunk regs) := by
  simp [advanceChunk, Footprint.CmdWritesWithin,
    Footprint.BasicWritesWithin,
    Layout.index_mem_layout_footprint]

private theorem restore_writesWithin
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin regs.layout.footprint
      (restore regs) := by
  simp [restore, copy, Footprint.CmdWritesWithin,
    Footprint.BasicWritesWithin,
    Layout.index_mem_layout_footprint]

theorem failure_writesWithin_internal
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin regs.layout.footprint
      (failure regs) := by
  have hprovider :
      Footprint.CmdWritesWithin regs.layout.footprint
        (SourceValue.failureChunk regs) :=
    cmdWritesWithin_mono
      (SourceValue.writeFootprint_subset_layout regs)
      (SourceValue.failureChunk_writesWithin regs)
  simp only [failure, enterWith, chunkBody, Cmd.seqList,
    Footprint.CmdWritesWithin]
  exact
    ⟨initialize_writesWithin regs,
      ⟨hprovider,
        ⟨ResidueBankOps.addScaledActiveChunk_writesWithin regs,
          advanceChunk_writesWithin regs⟩⟩,
      restore_writesWithin regs,
      FrameTransfer.popParent_writesWithin regs⟩

theorem source_writesWithin_internal
    (tm : TM workTapeCount)
    (order : FiniteEncoding.StateOrder tm)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin regs.layout.footprint
      (source tm order regs) := by
  have hsource :
      Footprint.CmdWritesWithin regs.layout.footprint
        (SourceValue.sourceChunk tm order regs) :=
    cmdWritesWithin_mono
      (SourceValue.writeFootprint_subset_layout regs)
      (SourceValue.sourceChunk_writesWithin tm order regs)
  simp only [source, sourceProvider, enterWith, chunkBody,
    Cmd.seqList, Footprint.CmdWritesWithin]
  exact
    ⟨initialize_writesWithin regs,
      ⟨⟨ControlDecode.decodeNode_layout_writesWithin regs, hsource⟩,
        ⟨ResidueBankOps.addScaledActiveChunk_writesWithin regs,
          advanceChunk_writesWithin regs⟩⟩,
      restore_writesWithin regs,
      FrameTransfer.popParent_writesWithin regs⟩

private theorem failureProvider_writesWithin
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin regs.layout.footprint
      (SourceValue.failureChunk regs) :=
  cmdWritesWithin_mono
    (SourceValue.writeFootprint_subset_layout regs)
    (SourceValue.failureChunk_writesWithin regs)

private theorem sourceProvider_writesWithin
    (tm : TM workTapeCount)
    (order : FiniteEncoding.StateOrder tm)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin regs.layout.footprint
      (sourceProvider tm order regs) := by
  refine ⟨ControlDecode.decodeNode_layout_writesWithin regs, ?_⟩
  exact cmdWritesWithin_mono
    (SourceValue.writeFootprint_subset_layout regs)
    (SourceValue.sourceChunk_writesWithin tm order regs)

private theorem digitBase_eq_chunkPower
    {tm : TM workTapeCount}
    (instanceData : NeighborhoodProgram.ResidueInstance tm) :
    Representation.digitBase instanceData =
      2 ^
        PrimeGrouped.Logarithmic.chunkBits
          (payloadWidth tm instanceData.blockLength)
          (graphFanIn workTapeCount) := by
  unfold Representation.digitBase CandidateParameters.domainSize
  rw [Representation.payloadWidth_eq_booleanWidth instanceData]
  rfl

theorem failureProvider_spec_internal
    (tm : TM workTapeCount)
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (node :
      NeighborhoodEvaluator.QueryNode
        workTapeCount instanceData.horizon) :
    ProviderSpec regs instanceData node instanceData.x
      (SourceValue.failureChunk regs)
      (Residue.failureValue tm instanceData.blockLength) := by
  intro chunk initial _hnode hcursor _hparameters hframe
    hinputLength hone
  obtain ⟨final, hrun, hpost⟩ :=
    SourceValue.failureChunk_runs tm instanceData.blockLength chunk
      regs instanceData.x initial hframe
  have habi :
      ControlDecode.PreservesABI regs initial final :=
    sourceFootprint_preservesABI regs
      (SourceValue.failureChunk_writesWithin regs) hrun
  have hstack :
      final regs.layout.stack = initial regs.layout.stack := by
    apply Footprint.runs_eq_outside
      (SourceValue.failureChunk_writesWithin regs) hrun
    exact source_index_not_mem regs 32
      (by intro slot; fin_cases slot <;> decide)
  have hinputLength' :
      final controller.inputLength =
        initial controller.inputLength :=
    controller_eq_of_layout_run regs (0 : Fin 17)
      (failureProvider_writesWithin regs) hrun
  have hone' :
      final controller.one = initial controller.one :=
    controller_eq_of_layout_run regs
      (SearchProgram.Registers.primeSlot (6 : Fin 8))
      (failureProvider_writesWithin regs) hrun
  refine ⟨final, hrun, ?_⟩
  exact
    { operand_eq := hpost.operand_eq
      inputFrame := hpost.inputFrame
      abi := habi
      cursor_eq := hpost.cursor_eq
      stack_eq := hstack
      bank_eq := by simpa using hpost.bankWord_eq
      inputLength_eq := hinputLength'
      one_eq := hone' }

theorem sourceChunk_invariantRuns_of_frameBound_internal
    (tm : TM workTapeCount)
    (order : FiniteEncoding.StateOrder tm)
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (tape : TapeIndex workTapeCount) (block : ℕ)
    (hnode : frame.node = .graph (.source tape block))
    (hbound :
      NeighborhoodScheduler.FrameBounds.FrameBound frame)
    (chunk :
      Fin
        (PrimeGrouped.Logarithmic.chunkCount
          (payloadWidth tm instanceData.blockLength)
          (graphFanIn workTapeCount)))
    (allowed : Finset ℕ) (initial : Store)
    (htape :
      initial (ControlDecode.nodeTape regs) = tape.val)
    (hblock :
      initial (ControlDecode.nodePayload0 regs) = block)
    (hblockLength :
      initial (Layout.blockLength regs) = instanceData.blockLength)
    (hradix :
      initial (Layout.chunkRadix regs) =
        2 ^
          PrimeGrouped.Logarithmic.chunkBits
            (payloadWidth tm instanceData.blockLength)
            (graphFanIn workTapeCount))
    (hcursor :
      initial (Layout.codecScratch regs) = chunk.val)
    (hinputLength :
      initial controller.inputLength = instanceData.x.length)
    (hvalues :
      NeighborhoodProgram.ValuesWithin allowed
        (SourceValue.sourceTransientValueBound
          tm instanceData.candidateTime)
        initial)
    (hwriteSubset :
      SourceValue.writeFootprint regs ⊆ allowed)
    (haddressCapacity :
      2 ^ SearchProgram.footprintLimit controller regs.footprint ≤
        SourceValue.sourceTransientValueBound
          tm instanceData.candidateTime)
    (hframe :
      SearchProgram.InputFrame
        controller regs.footprint instanceData.x initial) :
    ∃ final steps,
      InvariantRuns
        (NeighborhoodProgram.ValuesWithin allowed
          (SourceValue.sourceTransientValueBound
            tm instanceData.candidateTime))
        (SourceValue.sourceChunk tm order regs) initial final steps ∧
      SourceValue.SourceChunkPost regs instanceData.x
        (Residue.sourceValue tm instanceData.x
          instanceData.blockLength
          (FiniteEncoding.ofStateOrder order instanceData.blockLength)
          instanceData.positive tape block chunk)
        initial final := by
  have hcanonical :
      instanceData.blockLength =
        NeighborhoodGraph.WorkspaceAccounting.blockLength
          instanceData.candidateTime := by
    simpa [NeighborhoodEvaluator.candidateBlockLength,
      NeighborhoodGraph.WorkspaceAccounting.blockLength] using
      instanceData.blockLength_eq
  have hblockBound :
      block ≤
        max
          (NeighborhoodGraph.WorkspaceAccounting.horizon
            instanceData.candidateTime)
          1 := by
    have hqueryBound :
        NeighborhoodScheduler.FrameBounds.QueryBound
          instanceData.horizon frame.node :=
      hbound.2.1
    rw [hnode] at hqueryBound
    simpa [NeighborhoodScheduler.FrameBounds.QueryBound,
      instanceData.horizon_eq] using hqueryBound
  simpa using
    SourceValue.sourceChunk_invariantRuns tm order regs
      instanceData.x instanceData.candidateTime
      instanceData.blockLength hcanonical instanceData.inputLength_le
      tape block hblockBound chunk allowed initial htape hblock
      hblockLength hradix hcursor hinputLength hvalues hwriteSubset
      haddressCapacity hframe

theorem sourceProvider_spec_internal
    (tm : TM workTapeCount)
    (order : FiniteEncoding.StateOrder tm)
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (tape : TapeIndex workTapeCount) (block : ℕ)
    (hencoding :
      instanceData.encoding =
        FiniteEncoding.ofStateOrder order instanceData.blockLength)
    (hfits :
      ∀ digit ∈
          FrameCodec.nodeDigits
            (show
              NeighborhoodEvaluator.QueryNode
                workTapeCount instanceData.horizon
              from .graph (.source tape block)),
        digit < Representation.digitBase instanceData) :
    ProviderSpec regs instanceData (.graph (.source tape block))
      instanceData.x (sourceProvider tm order regs)
      (Residue.sourceValue tm instanceData.x
        instanceData.blockLength instanceData.encoding
        instanceData.positive tape block) := by
  intro chunk initial hnode hcursor hparameters hframe
    hinputLength hone
  have hdigitBase :
      0 < Representation.digitBase instanceData := by
    unfold Representation.digitBase CandidateParameters.domainSize
    exact PrimeGrouped.Logarithmic.domainSize_pos _ _
  obtain ⟨decoded, hdecode, _hnodePost, hdecoded,
      hdecodeABI⟩ :=
    ControlDecode.decodeNode_encodeNode_runs regs initial
      (Representation.digitBase instanceData)
      (show
        NeighborhoodEvaluator.QueryNode
          workTapeCount instanceData.horizon
        from .graph (.source tape block))
      hdigitBase hfits hnode hparameters.digitBase_eq
  have hdecodeCursor :
      decoded (Layout.codecScratch regs) =
        initial (Layout.codecScratch regs) := by
    apply Footprint.runs_eq_outside
      (ControlDecode.decodeNode_writesWithin regs) hdecode
    exact decode_index_not_mem regs 31
      (by intro slot; fin_cases slot <;> decide)
  have hdecodeStack :
      decoded regs.layout.stack = initial regs.layout.stack := by
    apply Footprint.runs_eq_outside
      (ControlDecode.decodeNode_writesWithin regs) hdecode
    exact decode_index_not_mem regs 32
      (by intro slot; fin_cases slot <;> decide)
  have hdecodeBank :
      decoded regs.layout.bank = initial regs.layout.bank := by
    apply Footprint.runs_eq_outside
      (ControlDecode.decodeNode_writesWithin regs) hdecode
    exact decode_index_not_mem regs 33
      (by intro slot; fin_cases slot <;> decide)
  have hdecodeFrame :
      SearchProgram.InputFrame
        controller regs.footprint instanceData.x decoded :=
    inputFrame_of_layout_run regs instanceData.x
      (ControlDecode.decodeNode_layout_writesWithin regs)
      hdecode hframe
  have hdecodeInputLength :
      decoded controller.inputLength =
        instanceData.x.length := by
    rw [controller_eq_of_layout_run regs (0 : Fin 17)
      (ControlDecode.decodeNode_layout_writesWithin regs) hdecode]
    exact hinputLength
  have htape :
      decoded (ControlDecode.nodeTape regs) = tape.val := by
    simpa [ControlDecode.expectedNodeValues] using hdecoded.tape_eq
  have hblock :
      decoded (ControlDecode.nodePayload0 regs) = block := by
    simpa [ControlDecode.expectedNodeValues] using
      hdecoded.payload0_eq
  have hblockLength :
      decoded (Layout.blockLength regs) =
        instanceData.blockLength := by
    rw [hdecodeABI.blockLength_eq]
    exact hparameters.blockLength_eq
  have hradix :
      decoded (Layout.chunkRadix regs) =
        2 ^
          PrimeGrouped.Logarithmic.chunkBits
            (payloadWidth tm instanceData.blockLength)
            (graphFanIn workTapeCount) := by
    rw [hdecodeABI.chunkRadix_eq,
      hparameters.digitBase_eq,
      digitBase_eq_chunkPower instanceData]
  have hcursorDecoded :
      decoded (Layout.codecScratch regs) = chunk.val := by
    rw [hdecodeCursor]
    exact hcursor
  obtain ⟨final, hsource, hsourcePost⟩ :=
    SourceValue.sourceChunk_runs tm order regs instanceData.x
      instanceData.blockLength instanceData.positive tape block
      chunk decoded htape hblock hblockLength hradix
      hcursorDecoded hdecodeInputLength hdecodeFrame
  have hsourceABI :
      ControlDecode.PreservesABI regs decoded final :=
    sourceFootprint_preservesABI regs
      (SourceValue.sourceChunk_writesWithin tm order regs) hsource
  have hsourceStack :
      final regs.layout.stack = decoded regs.layout.stack := by
    apply Footprint.runs_eq_outside
      (SourceValue.sourceChunk_writesWithin tm order regs) hsource
    exact source_index_not_mem regs 32
      (by intro slot; fin_cases slot <;> decide)
  have hsourceInputLength :
      final controller.inputLength =
        decoded controller.inputLength :=
    controller_eq_of_layout_run regs (0 : Fin 17)
      (cmdWritesWithin_mono
        (SourceValue.writeFootprint_subset_layout regs)
        (SourceValue.sourceChunk_writesWithin tm order regs))
      hsource
  have hsourceOne :
      final controller.one = decoded controller.one :=
    controller_eq_of_layout_run regs
      (SearchProgram.Registers.primeSlot (6 : Fin 8))
      (cmdWritesWithin_mono
        (SourceValue.writeFootprint_subset_layout regs)
        (SourceValue.sourceChunk_writesWithin tm order regs))
      hsource
  refine ⟨final, Runs.seq hdecode hsource, ?_⟩
  exact
    { operand_eq := by
        rw [hencoding]
        exact hsourcePost.operand_eq
      inputFrame := hsourcePost.inputFrame
      abi := preservesABI_trans regs hdecodeABI hsourceABI
      cursor_eq :=
        hsourcePost.cursor_eq.trans hdecodeCursor
      stack_eq := hsourceStack.trans hdecodeStack
      bank_eq := by
        simpa using hsourcePost.bankWord_eq.trans hdecodeBank
      inputLength_eq :=
        hsourceInputLength.trans
          (controller_eq_of_layout_run regs (0 : Fin 17)
            (ControlDecode.decodeNode_layout_writesWithin regs)
            hdecode)
      one_eq :=
        hsourceOne.trans
          (controller_eq_of_layout_run regs
            (SearchProgram.Registers.primeSlot (6 : Fin 8))
            (ControlDecode.decodeNode_layout_writesWithin regs)
            hdecode) }

theorem initialize_runs_internal
    {tm : TM workTapeCount}
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (rest : List (NeighborhoodScheduler.Frame tm instanceData))
    (input : List Bool)
    (value : ResidueValue tm instanceData.blockLength)
    (logicalBank : Residue.Registers tm instanceData.blockLength)
    (store : Store)
    (hquery :
      Representation.QueryState regs instanceData
        { stack := frame :: rest
          registers := logicalBank }
        store)
    (hframe :
      SearchProgram.InputFrame
        controller regs.footprint input store)
    (hinputLength : store controller.inputLength = input.length)
    (hone : store controller.one = 1) :
    ∃ final,
      Runs (initializeLeaf regs) store final ∧
      LoopState regs instanceData frame rest input value logicalBank
        0
        (PrimeGrouped.Logarithmic.chunkCount
          (payloadWidth tm instanceData.blockLength)
          (graphFanIn workTapeCount))
        final := by
  let saved :=
    copyResultStore (Layout.phaseCode regs) (Layout.fuel regs) store
  let loaded :=
    copyResultStore (Layout.fuel regs) (Layout.chunkCount regs) saved
  let final :=
    (Basic.imm (Layout.codecScratch regs) 0).exec loaded
  have hsave :
      Runs (copy (Layout.phaseCode regs) (Layout.fuel regs))
        store saved := by
    apply copy_runs
    exact regs.injective.ne (by decide : (27 : Fin 34) ≠ 22)
  have hload :
      Runs (copy (Layout.fuel regs) (Layout.chunkCount regs))
        saved loaded := by
    apply copy_runs
    exact regs.injective.ne (by decide : (22 : Fin 34) ≠ 7)
  have hclear :
      Runs (.basic (.imm (Layout.codecScratch regs) 0))
        loaded final :=
    Runs.basic _ _
  have hrun : Runs (initializeLeaf regs) store final := by
    simpa [initializeLeaf, Cmd.seqList] using
      Runs.seq hsave (Runs.seq hload hclear)
  have hphysical
      (slot : Fin 34)
      (hphase : slot ≠ 27) (hfuel : slot ≠ 22)
      (hcursor : slot ≠ 31) :
      final (regs.index slot) = store (regs.index slot) := by
    simp [final, loaded, saved, copyResultStore, Basic.exec,
      regs.injective.eq_iff, hphase, hfuel, hcursor]
  have hparameters :
      Representation.Parameters regs instanceData final :=
    { blockLength_eq := by
        rw [hphysical 2 (by decide) (by decide) (by decide)]
        exact hquery.parameters.blockLength_eq
      horizon_eq := by
        rw [hphysical 3 (by decide) (by decide) (by decide)]
        exact hquery.parameters.horizon_eq
      digitBase_eq := by
        rw [hphysical 8 (by decide) (by decide) (by decide)]
        exact hquery.parameters.digitBase_eq
      bankBase_eq := by
        rw [hphysical 14 (by decide) (by decide) (by decide)]
        exact hquery.parameters.bankBase_eq
      frameBase_eq := by
        rw [hphysical 13 (by decide) (by decide) (by decide)]
        exact hquery.parameters.frameBase_eq
      chunkCount_eq := by
        rw [hphysical 7 (by decide) (by decide) (by decide)]
        exact hquery.parameters.chunkCount_eq
      bankDigitCount_eq := by
        rw [hphysical 15 (by decide) (by decide) (by decide)]
        exact hquery.parameters.bankDigitCount_eq
      modulus_eq := by
        rw [hphysical 24 (by decide) (by decide) (by decide)]
        exact hquery.parameters.modulus_eq
      modulusPred_eq := by
        rw [hphysical 16 (by decide) (by decide) (by decide)]
        exact hquery.parameters.modulusPred_eq }
  refine ⟨final, hrun, ?_⟩
  exact
    { balance := by simp
      remaining_eq := by
        simp [final, loaded, saved, copyResultStore, Basic.exec,
          regs.injective.eq_iff]
        exact hquery.parameters.chunkCount_eq
      cursor_eq := by simp [final, Basic.exec]
      savedFuel_eq := by
        simp [final, loaded, saved, copyResultStore, Basic.exec,
          regs.injective.eq_iff]
        exact hquery.stack.1.fuel_eq
      node_eq := by
        rw [hphysical 23 (by decide) (by decide) (by decide)]
        exact hquery.stack.1.node_eq
      scalar_eq := by
        rw [hphysical 25 (by decide) (by decide) (by decide)]
        exact hquery.stack.1.scalar_eq
      out_eq := by
        rw [hphysical 26 (by decide) (by decide) (by decide)]
        exact hquery.stack.1.out_eq
      active_eq := by
        rw [hphysical 28 (by decide) (by decide) (by decide)]
        exact hquery.stack.1.active_eq
      parameters := hparameters
      suspended := by
        change
          final (regs.index 32) =
            FrameTransfer.encodeStack
              (Representation.digitBase instanceData)
              (Representation.frameBase instanceData) rest
        rw [hphysical 32 (by decide) (by decide) (by decide)]
        exact hquery.stack.2
      bank := by
        rw [addScaledPrefix_zero_internal]
        change
          NeighborhoodProgram.RepresentsResidueBank
            tm instanceData.blockLength
            (Representation.fieldBase instanceData)
            (final (regs.index 33)) logicalBank
        rw [hphysical 33 (by decide) (by decide) (by decide)]
        exact hquery.bank
      bank_lt := by
        change
          final (regs.index 33) <
            Representation.fieldBase instanceData ^
              ((graphFanIn workTapeCount + 1) *
                PrimeGrouped.Logarithmic.chunkCount
                  (payloadWidth tm instanceData.blockLength)
                  (graphFanIn workTapeCount))
        rw [hphysical 33 (by decide) (by decide) (by decide)]
        exact hquery.bank_lt
      inputFrame :=
        inputFrame_of_layout_run regs input
          (initialize_writesWithin regs) hrun hframe
      inputLength_eq := by
        rw [controller_eq_of_layout_run regs (0 : Fin 17)
          (initialize_writesWithin regs) hrun]
        exact hinputLength
      one_eq := by
        change
          final
              (controller.index
                (SearchProgram.Registers.primeSlot (6 : Fin 8))) =
            1
        rw [controller_eq_of_layout_run regs
          (SearchProgram.Registers.primeSlot (6 : Fin 8))
          (initialize_writesWithin regs) hrun]
        exact hone }

private theorem addScaled_preservesABI
    (regs : NeighborhoodTrial.Registers controller)
    {initial final : Store} {base modulus : ℕ}
    (hrun :
      Runs (ResidueBankOps.addScaledActiveChunk regs)
        initial final)
    (hbaseInitial :
      initial
          (Layout.residueScaleRegisters regs).bank.bank.base =
        base)
    (hmodulusInitial :
      initial (Layout.residueScaleRegisters regs).bank.modulus =
        modulus)
    (hmodulusPredInitial :
      initial (Layout.residueScaleRegisters regs).bank.modulusPred =
        modulus - 1)
    (hbaseFinal :
      final
          (Layout.residueScaleRegisters regs).bank.bank.base =
        base)
    (hmodulusFinal :
      final (Layout.residueScaleRegisters regs).bank.modulus =
        modulus)
    (hmodulusPredFinal :
      final (Layout.residueScaleRegisters regs).bank.modulusPred =
        modulus - 1) :
    ControlDecode.PreservesABI regs initial final := by
  let outside (target : Fin 34)
      (hne : ∀ slot, Layout.residueScaleMap slot ≠ target) :
      final (regs.index target) = initial (regs.index target) :=
    Footprint.runs_eq_outside
      (ResidueBankOps.addScaledActiveChunk_scaleWritesWithin regs)
      hrun (scale_index_not_mem regs target hne)
  exact
    { fuel_eq := outside 22 (by intro slot; fin_cases slot <;> decide)
      nodeCode_eq :=
        outside 23 (by intro slot; fin_cases slot <;> decide)
      scalar_eq :=
        outside 25 (by intro slot; fin_cases slot <;> decide)
      out_eq := outside 26 (by intro slot; fin_cases slot <;> decide)
      phaseCode_eq :=
        outside 27 (by intro slot; fin_cases slot <;> decide)
      active_eq :=
        outside 28 (by intro slot; fin_cases slot <;> decide)
      blockLength_eq :=
        outside 2 (by intro slot; fin_cases slot <;> decide)
      horizon_eq :=
        outside 3 (by intro slot; fin_cases slot <;> decide)
      chunkCount_eq :=
        outside 7 (by intro slot; fin_cases slot <;> decide)
      chunkRadix_eq :=
        outside 8 (by intro slot; fin_cases slot <;> decide)
      frameRadix_eq :=
        outside 13 (by intro slot; fin_cases slot <;> decide)
      bankRadix_eq := hbaseFinal.trans hbaseInitial.symm
      bankDigitCount_eq :=
        outside 15 (by intro slot; fin_cases slot <;> decide)
      modulusPred_eq :=
        hmodulusPredFinal.trans hmodulusPredInitial.symm
      modulus_eq := hmodulusFinal.trans hmodulusInitial.symm }

theorem chunkBody_runs_internal
    {tm : TM workTapeCount}
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (rest : List (NeighborhoodScheduler.Frame tm instanceData))
    (input : List Bool)
    (provider : Cmd)
    (value : ResidueValue tm instanceData.blockLength)
    (logicalBank : Residue.Registers tm instanceData.blockLength)
    (processed remaining : ℕ) (store : Store)
    (hprovider :
      ProviderSpec regs instanceData frame.node input provider value)
    (hstate :
      LoopState regs instanceData frame rest input value logicalBank
        processed (remaining + 1) store) :
    ∃ final,
      Runs (chunkBody regs provider) store final ∧
      LoopState regs instanceData frame rest input value logicalBank
        (processed + 1) remaining final := by
  have hprocessed :
      processed <
        PrimeGrouped.Logarithmic.chunkCount
          (payloadWidth tm instanceData.blockLength)
          (graphFanIn workTapeCount) := by
    have hbalance := hstate.balance
    omega
  let chunk :
      Fin
        (PrimeGrouped.Logarithmic.chunkCount
          (payloadWidth tm instanceData.blockLength)
          (graphFanIn workTapeCount)) :=
    ⟨processed, hprocessed⟩
  obtain ⟨provided, hprovide, hprovidePost⟩ :=
    hprovider chunk store hstate.node_eq hstate.cursor_eq
      hstate.parameters hstate.inputFrame hstate.inputLength_eq
      hstate.one_eq
  have hprovidedParameters :
      Representation.Parameters regs instanceData provided :=
    Representation.Parameters.of_preservesABI regs store provided
      hstate.parameters hprovidePost.abi
  have hprovidedStack :
      FrameTransfer.RepresentsStack regs
        (Representation.digitBase instanceData)
        (Representation.frameBase instanceData) rest provided := by
    calc
      provided regs.layout.stack = store regs.layout.stack :=
        hprovidePost.stack_eq
      _ = FrameTransfer.encodeStack
          (Representation.digitBase instanceData)
          (Representation.frameBase instanceData) rest :=
        hstate.suspended
  have hprovidedBank :
      NeighborhoodProgram.RepresentsResidueBank
        tm instanceData.blockLength
        (Representation.fieldBase instanceData)
        (provided regs.layout.bank)
        (addScaledPrefix tm instanceData.blockLength frame.scalar
          logicalBank frame.out value processed) := by
    rw [hprovidePost.bank_eq]
    exact hstate.bank
  have hprovidedBankLt :
      provided regs.layout.bank <
        Representation.fieldBase instanceData ^
          ((graphFanIn workTapeCount + 1) *
            PrimeGrouped.Logarithmic.chunkCount
              (payloadWidth tm instanceData.blockLength)
              (graphFanIn workTapeCount)) := by
    rw [hprovidePost.bank_eq]
    exact hstate.bank_lt
  have hdigitBase :
      0 < Representation.digitBase instanceData := by
    unfold Representation.digitBase CandidateParameters.domainSize
    exact PrimeGrouped.Logarithmic.domainSize_pos _ _
  have hfieldBase :
      0 < Representation.fieldBase instanceData :=
    pow_pos hdigitBase _
  have hmodulus :
      0 < modulus tm instanceData.blockLength := by
    change 0 < NeighborhoodScheduler.fieldModulus instanceData
    have hone :=
      NeighborhoodScheduler.FrameBounds.fieldModulus_one_lt
        instanceData
    omega
  have hmodulusBase :
      modulus tm instanceData.blockLength ≤
        Representation.fieldBase instanceData := by
    change
      NeighborhoodScheduler.fieldModulus instanceData ≤
        Representation.fieldBase instanceData
    rw [NeighborhoodTrial.fieldModulus_eq_canonicalModulus,
      Representation.fieldBase_eq_bankRadix]
    exact Nat.le_of_lt
      (CandidateParameters.RadixBounds.canonicalModulus_lt_bankRadix
        tm.Q workTapeCount instanceData.candidateTime)
  have hvalue :
      provided
          (Layout.residueScaleRegisters regs).bank.operand =
        value chunk := by
    simpa [chunk] using hprovidePost.operand_eq
  have hscalar :
      provided (Layout.scalar regs) = frame.scalar := by
    rw [hprovidePost.abi.scalar_eq]
    exact hstate.scalar_eq
  have hout :
      provided (Layout.out regs) = frame.out.val := by
    rw [hprovidePost.abi.out_eq]
    exact hstate.out_eq
  have hcursor :
      provided (Layout.codecScratch regs) = chunk.val := by
    rw [hprovidePost.cursor_eq]
    exact hstate.cursor_eq
  have hbaseValue :
      provided
          (Layout.residueScaleRegisters regs).bank.bank.base =
        Representation.fieldBase instanceData :=
    hprovidedParameters.bankBase_eq
  have hmodulusValue :
      provided (Layout.residueScaleRegisters regs).bank.modulus =
        modulus tm instanceData.blockLength :=
    hprovidedParameters.modulus_eq
  have hmodulusPred :
      provided (Layout.residueScaleRegisters regs).bank.modulusPred =
        modulus tm instanceData.blockLength - 1 :=
    hprovidedParameters.modulusPred_eq
  obtain ⟨updated, hupdate, hupdatedBank, hupdatedWord,
      hupdatedBase, hupdatedModulus, hupdatedModulusPred⟩ :=
    ResidueBankOps.addScaledActiveChunk_runs tm
      instanceData.blockLength frame.scalar
      (Representation.fieldBase instanceData)
      (provided regs.layout.bank) (value chunk)
      (addScaledPrefix tm instanceData.blockLength frame.scalar
        logicalBank frame.out value processed)
      frame.out chunk regs provided hfieldBase hmodulus
      hmodulusBase rfl hprovidedBank hbaseValue hmodulusValue
      hmodulusPred hvalue hscalar hout
      hprovidedParameters.chunkCount_eq hcursor
  have hupdateABI :
      ControlDecode.PreservesABI regs provided updated :=
    addScaled_preservesABI regs hupdate hbaseValue hmodulusValue
      hmodulusPred hupdatedBase hupdatedModulus
      hupdatedModulusPred
  have hupdatedParameters :
      Representation.Parameters regs instanceData updated :=
    Representation.Parameters.of_preservesABI regs provided updated
      hprovidedParameters hupdateABI
  have hupdatedStack :
      FrameTransfer.RepresentsStack regs
        (Representation.digitBase instanceData)
        (Representation.frameBase instanceData) rest updated := by
    calc
      updated regs.layout.stack = provided regs.layout.stack := by
        exact Footprint.runs_eq_outside
          (ResidueBankOps.addScaledActiveChunk_scaleWritesWithin regs)
          hupdate
          (scale_index_not_mem regs 32
            (by intro slot; fin_cases slot <;> decide))
      _ = FrameTransfer.encodeStack
          (Representation.digitBase instanceData)
          (Representation.frameBase instanceData) rest :=
        hprovidedStack
  have hcurrent :
      addScaledPrefix tm instanceData.blockLength frame.scalar
          logicalBank frame.out value processed frame.out chunk =
        logicalBank frame.out chunk := by
    simp [addScaledPrefix, chunk]
  rw [hcurrent] at hupdatedBank
  have hupdatedBank' :
      NeighborhoodProgram.RepresentsResidueBank
        tm instanceData.blockLength
        (Representation.fieldBase instanceData)
        (updated regs.layout.bank)
        (addScaledPrefix tm instanceData.blockLength frame.scalar
          logicalBank frame.out value (processed + 1)) := by
    rw [← addScaledPrefix_succ_internal tm
      instanceData.blockLength frame.scalar processed logicalBank
      frame.out value hprocessed]
    exact hupdatedBank
  have hupdatedBankLt :
      updated regs.layout.bank <
        Representation.fieldBase instanceData ^
          ((graphFanIn workTapeCount + 1) *
            PrimeGrouped.Logarithmic.chunkCount
              (payloadWidth tm instanceData.blockLength)
              (graphFanIn workTapeCount)) := by
    change
      updated
          (Layout.residueScaleRegisters regs).bank.bank.word <
        Representation.fieldBase instanceData ^
          ((graphFanIn workTapeCount + 1) *
            PrimeGrouped.Logarithmic.chunkCount
              (payloadWidth tm instanceData.blockLength)
              (graphFanIn workTapeCount))
    rw [hupdatedWord]
    have hbound :=
      NeighborhoodProgram.bankUpdateAt_word_lt_pow
        (op := NeighborhoodProgram.ResidueBankOp.add)
        (operand :=
          (value chunk * frame.scalar) %
            modulus tm instanceData.blockLength)
      hfieldBase hprovidedBankLt
      (NeighborhoodProgram.residueBankIndex_lt
        tm instanceData.blockLength frame.out chunk)
      hmodulus hmodulusBase
    rw [hprovidedBank frame.out chunk] at hbound
    exact hbound
  have hupdatedCursor :
      updated (Layout.codecScratch regs) = processed := by
    rw [Footprint.runs_eq_outside
      (ResidueBankOps.addScaledActiveChunk_scaleWritesWithin regs)
      hupdate
      (scale_index_not_mem regs 31
        (by intro slot; fin_cases slot <;> decide))]
    rw [hprovidePost.cursor_eq]
    exact hstate.cursor_eq
  have hupdatedFuel :
      updated (Layout.fuel regs) = remaining + 1 := by
    rw [hupdateABI.fuel_eq, hprovidePost.abi.fuel_eq]
    exact hstate.remaining_eq
  have hupdatedOne : updated controller.one = 1 := by
    calc
      updated controller.one = provided controller.one :=
        controller_eq_of_layout_run regs
          (SearchProgram.Registers.primeSlot (6 : Fin 8))
          (ResidueBankOps.addScaledActiveChunk_writesWithin regs)
          hupdate
      _ = store controller.one := hprovidePost.one_eq
      _ = 1 := hstate.one_eq
  let cursorAdvanced :=
    (Basic.add (Layout.codecScratch regs)
      (Layout.codecScratch regs) controller.one).exec updated
  let final :=
    (Basic.sub (Layout.fuel regs)
      (Layout.fuel regs) controller.one).exec cursorAdvanced
  have hadvance :
      Runs (advanceChunk regs) updated final := by
    simpa [advanceChunk, cursorAdvanced, final] using
      Runs.seq
        (Runs.basic
          (Basic.add (Layout.codecScratch regs)
            (Layout.codecScratch regs) controller.one) updated)
        (Runs.basic
          (Basic.sub (Layout.fuel regs)
            (Layout.fuel regs) controller.one) cursorAdvanced)
  have hcursorAdvancedCursor :
      cursorAdvanced (Layout.codecScratch regs) =
        updated (Layout.codecScratch regs) + updated controller.one := by
    simp [cursorAdvanced, Basic.exec]
  have hcursorAdvancedFuel :
      cursorAdvanced (Layout.fuel regs) =
        updated (Layout.fuel regs) := by
    simp [cursorAdvanced, Basic.exec,
      regs.injective.eq_iff]
  have hcursorAdvancedOne :
      cursorAdvanced controller.one = updated controller.one := by
    have hne :
        controller.one ≠ Layout.codecScratch regs := by
      exact
        (regs.index_ne_controller 31
          (SearchProgram.Registers.primeSlot (6 : Fin 8))).symm
    simp [cursorAdvanced, Basic.exec, hne]
  have hphysical
      (slot : Fin 34) (hfuel : slot ≠ 22)
      (hcursorSlot : slot ≠ 31) :
      final (regs.index slot) = updated (regs.index slot) := by
    simp [final, cursorAdvanced, Basic.exec,
      regs.injective.eq_iff, hfuel, hcursorSlot]
  have hparameters :
      Representation.Parameters regs instanceData final :=
    { blockLength_eq := by
        rw [hphysical 2 (by decide) (by decide)]
        exact hupdatedParameters.blockLength_eq
      horizon_eq := by
        rw [hphysical 3 (by decide) (by decide)]
        exact hupdatedParameters.horizon_eq
      digitBase_eq := by
        rw [hphysical 8 (by decide) (by decide)]
        exact hupdatedParameters.digitBase_eq
      bankBase_eq := by
        rw [hphysical 14 (by decide) (by decide)]
        exact hupdatedParameters.bankBase_eq
      frameBase_eq := by
        rw [hphysical 13 (by decide) (by decide)]
        exact hupdatedParameters.frameBase_eq
      chunkCount_eq := by
        rw [hphysical 7 (by decide) (by decide)]
        exact hupdatedParameters.chunkCount_eq
      bankDigitCount_eq := by
        rw [hphysical 15 (by decide) (by decide)]
        exact hupdatedParameters.bankDigitCount_eq
      modulus_eq := by
        rw [hphysical 24 (by decide) (by decide)]
        exact hupdatedParameters.modulus_eq
      modulusPred_eq := by
        rw [hphysical 16 (by decide) (by decide)]
        exact hupdatedParameters.modulusPred_eq }
  refine ⟨final, ?_, ?_⟩
  · exact Runs.seq hprovide (Runs.seq hupdate hadvance)
  · exact
      { balance := by
          have hbalance := hstate.balance
          omega
        remaining_eq := by
          simp only [final, Basic.exec, Function.update_self]
          rw [hcursorAdvancedFuel, hcursorAdvancedOne,
            hupdatedFuel, hupdatedOne]
          omega
        cursor_eq := by
          rw [show
            final (Layout.codecScratch regs) =
              cursorAdvanced (Layout.codecScratch regs) by
                simp [final, Basic.exec, regs.injective.eq_iff]]
          rw [hcursorAdvancedCursor, hupdatedCursor, hupdatedOne]
        savedFuel_eq := by
          rw [hphysical 27 (by decide) (by decide),
            hupdateABI.phaseCode_eq,
            hprovidePost.abi.phaseCode_eq]
          exact hstate.savedFuel_eq
        node_eq := by
          rw [hphysical 23 (by decide) (by decide),
            hupdateABI.nodeCode_eq,
            hprovidePost.abi.nodeCode_eq]
          exact hstate.node_eq
        scalar_eq := by
          rw [hphysical 25 (by decide) (by decide),
            hupdateABI.scalar_eq, hprovidePost.abi.scalar_eq]
          exact hstate.scalar_eq
        out_eq := by
          rw [hphysical 26 (by decide) (by decide),
            hupdateABI.out_eq, hprovidePost.abi.out_eq]
          exact hstate.out_eq
        active_eq := by
          rw [hphysical 28 (by decide) (by decide),
            hupdateABI.active_eq, hprovidePost.abi.active_eq]
          exact hstate.active_eq
        parameters := hparameters
        suspended := by
          change
            final (regs.index 32) =
              FrameTransfer.encodeStack
                (Representation.digitBase instanceData)
                (Representation.frameBase instanceData) rest
          rw [hphysical 32 (by decide) (by decide)]
          exact hupdatedStack
        bank := by
          change
            NeighborhoodProgram.RepresentsResidueBank
              tm instanceData.blockLength
              (Representation.fieldBase instanceData)
              (final (regs.index 33))
              (addScaledPrefix tm instanceData.blockLength
                frame.scalar logicalBank frame.out value
                (processed + 1))
          rw [hphysical 33 (by decide) (by decide)]
          exact hupdatedBank'
        bank_lt := by
          change
            final (regs.index 33) <
              Representation.fieldBase instanceData ^
                ((graphFanIn workTapeCount + 1) *
                  PrimeGrouped.Logarithmic.chunkCount
                    (payloadWidth tm instanceData.blockLength)
                    (graphFanIn workTapeCount))
          rw [hphysical 33 (by decide) (by decide)]
          exact hupdatedBankLt
        inputFrame :=
          inputFrame_of_layout_run regs input
            (advanceChunk_writesWithin regs) hadvance
            (inputFrame_of_layout_run regs input
              (ResidueBankOps.addScaledActiveChunk_writesWithin regs)
              hupdate hprovidePost.inputFrame)
        inputLength_eq := by
          rw [controller_eq_of_layout_run regs (0 : Fin 17)
            (advanceChunk_writesWithin regs) hadvance,
            controller_eq_of_layout_run regs (0 : Fin 17)
              (ResidueBankOps.addScaledActiveChunk_writesWithin regs)
              hupdate, hprovidePost.inputLength_eq]
          exact hstate.inputLength_eq
        one_eq := by
          calc
            final controller.one = updated controller.one :=
              controller_eq_of_layout_run regs
                (SearchProgram.Registers.primeSlot (6 : Fin 8))
                (advanceChunk_writesWithin regs) hadvance
            _ = provided controller.one :=
              controller_eq_of_layout_run regs
                (SearchProgram.Registers.primeSlot (6 : Fin 8))
                (ResidueBankOps.addScaledActiveChunk_writesWithin regs)
                hupdate
            _ = store controller.one := hprovidePost.one_eq
            _ = 1 := hstate.one_eq }

theorem loop_runs_internal
    {tm : TM workTapeCount}
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (rest : List (NeighborhoodScheduler.Frame tm instanceData))
    (input : List Bool)
    (provider : Cmd)
    (value : ResidueValue tm instanceData.blockLength)
    (logicalBank : Residue.Registers tm instanceData.blockLength)
    (hprovider :
      ProviderSpec regs instanceData frame.node input provider value)
    (processed remaining : ℕ) (store : Store)
    (hstate :
      LoopState regs instanceData frame rest input value logicalBank
        processed remaining store) :
    ∃ final,
      Runs
        (.whileNonzero (Layout.fuel regs)
          (chunkBody regs provider))
        store final ∧
      LoopState regs instanceData frame rest input value logicalBank
        (processed + remaining) 0 final := by
  induction remaining generalizing processed store with
  | zero =>
      refine ⟨store, ?_, ?_⟩
      · exact Runs.whileZero hstate.remaining_eq
      · simpa using hstate
  | succ remaining ih =>
      have htest : store (Layout.fuel regs) ≠ 0 := by
        rw [hstate.remaining_eq]
        omega
      obtain ⟨afterBody, hbody, hbodyState⟩ :=
        chunkBody_runs_internal regs instanceData frame rest input
          provider value logicalBank processed remaining store
          hprovider hstate
      obtain ⟨final, hloop, hfinalState⟩ :=
        ih (processed + 1) afterBody hbodyState
      refine ⟨final, Runs.whileNonzero htest hbody hloop, ?_⟩
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        hfinalState

theorem restore_runs_internal
    {tm : TM workTapeCount}
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (rest : List (NeighborhoodScheduler.Frame tm instanceData))
    (input : List Bool)
    (value : ResidueValue tm instanceData.blockLength)
    (logicalBank : Residue.Registers tm instanceData.blockLength)
    (store : Store)
    (hphase : frame.phase = .enter)
    (hstate :
      LoopState regs instanceData frame rest input value logicalBank
        (PrimeGrouped.Logarithmic.chunkCount
          (payloadWidth tm instanceData.blockLength)
          (graphFanIn workTapeCount))
        0 store) :
    ∃ final,
      Runs (restore regs) store final ∧
      Representation.Stack regs (frame :: rest) final ∧
      Representation.Parameters regs instanceData final ∧
      NeighborhoodProgram.RepresentsResidueBank
        tm instanceData.blockLength
        (Representation.fieldBase instanceData)
        (final regs.layout.bank)
        (NeighborhoodScheduler.addScaledAt
          instanceData logicalBank frame.out frame.scalar value) ∧
      final regs.layout.bank <
        Representation.fieldBase instanceData ^
          ((graphFanIn workTapeCount + 1) *
            PrimeGrouped.Logarithmic.chunkCount
              (payloadWidth tm instanceData.blockLength)
              (graphFanIn workTapeCount)) ∧
      SearchProgram.InputFrame
        controller regs.footprint input final ∧
      final controller.inputLength = input.length ∧
      final controller.one = 1 := by
  let loaded :=
    copyResultStore (Layout.fuel regs) (Layout.phaseCode regs) store
  let final :=
    (Basic.imm (Layout.phaseCode regs) 0).exec loaded
  have hload :
      Runs (copy (Layout.fuel regs) (Layout.phaseCode regs))
        store loaded := by
    apply copy_runs
    exact regs.injective.ne (by decide : (22 : Fin 34) ≠ 27)
  have hclear :
      Runs (.basic (.imm (Layout.phaseCode regs) 0))
        loaded final :=
    Runs.basic _ _
  have hrun : Runs (restore regs) store final := by
    simpa [restore] using Runs.seq hload hclear
  have hphysical
      (slot : Fin 34)
      (hfuel : slot ≠ 22) (hphaseSlot : slot ≠ 27) :
      final (regs.index slot) = store (regs.index slot) := by
    simp [final, loaded, copyResultStore, Basic.exec,
      regs.injective.eq_iff, hfuel, hphaseSlot]
  have hparameters :
      Representation.Parameters regs instanceData final :=
    { blockLength_eq := by
        rw [hphysical 2 (by decide) (by decide)]
        exact hstate.parameters.blockLength_eq
      horizon_eq := by
        rw [hphysical 3 (by decide) (by decide)]
        exact hstate.parameters.horizon_eq
      digitBase_eq := by
        rw [hphysical 8 (by decide) (by decide)]
        exact hstate.parameters.digitBase_eq
      bankBase_eq := by
        rw [hphysical 14 (by decide) (by decide)]
        exact hstate.parameters.bankBase_eq
      frameBase_eq := by
        rw [hphysical 13 (by decide) (by decide)]
        exact hstate.parameters.frameBase_eq
      chunkCount_eq := by
        rw [hphysical 7 (by decide) (by decide)]
        exact hstate.parameters.chunkCount_eq
      bankDigitCount_eq := by
        rw [hphysical 15 (by decide) (by decide)]
        exact hstate.parameters.bankDigitCount_eq
      modulus_eq := by
        rw [hphysical 24 (by decide) (by decide)]
        exact hstate.parameters.modulus_eq
      modulusPred_eq := by
        rw [hphysical 16 (by decide) (by decide)]
        exact hstate.parameters.modulusPred_eq }
  have hactive :
      Representation.ActiveFrame regs frame final :=
    { fuel_eq := by
        simp [final, loaded, copyResultStore, Basic.exec,
          regs.injective.eq_iff]
        exact hstate.savedFuel_eq
      node_eq := by
        rw [hphysical 23 (by decide) (by decide)]
        exact hstate.node_eq
      scalar_eq := by
        rw [hphysical 25 (by decide) (by decide)]
        exact hstate.scalar_eq
      out_eq := by
        rw [hphysical 26 (by decide) (by decide)]
        exact hstate.out_eq
      phase_eq := by
        simp [final, Basic.exec, hphase, FrameCodec.encodePhase,
          FrameCodec.phaseDigits, FrameCodec.encodeList,
          PackedDigits.push]
      active_eq := by
        rw [hphysical 28 (by decide) (by decide)]
        exact hstate.active_eq }
  have hstack :
      Representation.Stack regs (frame :: rest) final := by
    refine ⟨hactive, ?_⟩
    change
      final (regs.index 32) =
        FrameTransfer.encodeStack
          (Representation.digitBase instanceData)
          (Representation.frameBase instanceData) rest
    rw [hphysical 32 (by decide) (by decide)]
    exact hstate.suspended
  have hbank :
      NeighborhoodProgram.RepresentsResidueBank
        tm instanceData.blockLength
        (Representation.fieldBase instanceData)
        (final regs.layout.bank)
        (NeighborhoodScheduler.addScaledAt
          instanceData logicalBank frame.out frame.scalar value) := by
    change
      NeighborhoodProgram.RepresentsResidueBank
        tm instanceData.blockLength
        (Representation.fieldBase instanceData)
        (final (regs.index 33))
        (NeighborhoodScheduler.addScaledAt
          instanceData logicalBank frame.out frame.scalar value)
    rw [hphysical 33 (by decide) (by decide)]
    rw [← addScaledPrefix_full_internal tm instanceData
      frame.scalar logicalBank frame.out value]
    exact hstate.bank
  refine ⟨final, hrun, hstack, hparameters, hbank, ?_, ?_, ?_, ?_⟩
  · change
      final (regs.index 33) <
        Representation.fieldBase instanceData ^
          ((graphFanIn workTapeCount + 1) *
            PrimeGrouped.Logarithmic.chunkCount
              (payloadWidth tm instanceData.blockLength)
              (graphFanIn workTapeCount))
    rw [hphysical 33 (by decide) (by decide)]
    exact hstate.bank_lt
  · exact inputFrame_of_layout_run regs input
      (restore_writesWithin regs) hrun hstate.inputFrame
  · rw [controller_eq_of_layout_run regs (0 : Fin 17)
      (restore_writesWithin regs) hrun]
    exact hstate.inputLength_eq
  · calc
      final controller.one = store controller.one :=
        controller_eq_of_layout_run regs
          (SearchProgram.Registers.primeSlot (6 : Fin 8))
          (restore_writesWithin regs) hrun
      _ = 1 := hstate.one_eq

theorem enterWith_runs_internal
    {tm : TM workTapeCount}
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (rest : List (NeighborhoodScheduler.Frame tm instanceData))
    (input : List Bool)
    (provider : Cmd)
    (value : ResidueValue tm instanceData.blockLength)
    (logicalBank : Residue.Registers tm instanceData.blockLength)
    (store : Store)
    (hphase : frame.phase = .enter)
    (hprovider :
      ProviderSpec regs instanceData frame.node input provider value)
    (hquery :
      Representation.QueryState regs instanceData
        { stack := frame :: rest
          registers := logicalBank }
        store)
    (hframe :
      SearchProgram.InputFrame
        controller regs.footprint input store)
    (hinputLength : store controller.inputLength = input.length)
    (hone : store controller.one = 1) :
    ∃ final,
      Runs (enterWith regs provider) store final ∧
      Representation.QueryState regs instanceData
        { stack := rest
          registers :=
            NeighborhoodScheduler.addScaledAt
              instanceData logicalBank frame.out frame.scalar value }
        final ∧
      SearchProgram.InputFrame
        controller regs.footprint input final ∧
      final controller.inputLength = input.length ∧
      final controller.one = 1 := by
  obtain ⟨initialized, hinitialize, hinitializedState⟩ :=
    initialize_runs_internal regs instanceData frame rest input value
      logicalBank store hquery hframe hinputLength hone
  obtain ⟨looped, hloop, hloopedState⟩ :=
    loop_runs_internal regs instanceData frame rest input provider
      value logicalBank hprovider 0
      (PrimeGrouped.Logarithmic.chunkCount
        (payloadWidth tm instanceData.blockLength)
        (graphFanIn workTapeCount))
      initialized hinitializedState
  have hloopedState' :
      LoopState regs instanceData frame rest input value logicalBank
        (PrimeGrouped.Logarithmic.chunkCount
          (payloadWidth tm instanceData.blockLength)
          (graphFanIn workTapeCount))
        0 looped := by
    simpa using hloopedState
  obtain ⟨restored, hrestore, hrestoredStack,
      hrestoredParameters, hrestoredBank, hrestoredBankLt,
      hrestoredFrame, hrestoredInputLength, hrestoredOne⟩ :=
    restore_runs_internal regs instanceData frame rest input value
      logicalBank looped hphase hloopedState'
  have hbounds :
      ∀ current ∈ rest,
        NeighborhoodScheduler.FrameBounds.FrameBound current := by
    intro current hcurrent
    exact hquery.bounds current (by simp [hcurrent])
  obtain ⟨final, hpop, hfinalStack, hfinalParameters,
      hfinalBankEq⟩ :=
    Representation.Stack.popParent_runs regs frame rest restored
      hrestoredStack hrestoredParameters hbounds
  have hfinalFrame :
      SearchProgram.InputFrame
        controller regs.footprint input final :=
    inputFrame_of_layout_run regs input
      (FrameTransfer.popParent_writesWithin regs) hpop
      hrestoredFrame
  have hfinalInputLength :
      final controller.inputLength = input.length := by
    calc
      final controller.inputLength =
          restored controller.inputLength :=
        controller_eq_of_layout_run regs (0 : Fin 17)
          (FrameTransfer.popParent_writesWithin regs) hpop
      _ = input.length := hrestoredInputLength
  have hfinalOne : final controller.one = 1 := by
    calc
      final controller.one = restored controller.one :=
        controller_eq_of_layout_run regs
          (SearchProgram.Registers.primeSlot (6 : Fin 8))
          (FrameTransfer.popParent_writesWithin regs) hpop
      _ = 1 := hrestoredOne
  refine ⟨final, ?_, ?_, hfinalFrame, hfinalInputLength,
    hfinalOne⟩
  · simpa [enterWith, Cmd.seqList] using
      Runs.seq hinitialize
        (Runs.seq hloop (Runs.seq hrestore hpop))
  · exact
      { parameters := hfinalParameters
        stack := hfinalStack
        bank := by
          rw [hfinalBankEq]
          exact hrestoredBank
        bank_lt := by
          rw [hfinalBankEq]
          exact hrestoredBankLt
        bounds := hbounds }

theorem failureValue_runs_internal
    {tm : TM workTapeCount}
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (rest : List (NeighborhoodScheduler.Frame tm instanceData))
    (logicalBank : Residue.Registers tm instanceData.blockLength)
    (store : Store)
    (hphase : frame.phase = .enter)
    (hquery :
      Representation.QueryState regs instanceData
        { stack := frame :: rest
          registers := logicalBank }
        store)
    (hframe :
      SearchProgram.InputFrame
        controller regs.footprint instanceData.x store)
    (hinputLength :
      store controller.inputLength = instanceData.x.length)
    (hone : store controller.one = 1) :
    ∃ final,
      Runs (failure regs) store final ∧
      Representation.QueryState regs instanceData
        { stack := rest
          registers :=
            NeighborhoodScheduler.addScaledAt
              instanceData logicalBank frame.out frame.scalar
                (Residue.failureValue tm instanceData.blockLength) }
        final ∧
      SearchProgram.InputFrame
        controller regs.footprint instanceData.x final ∧
      final controller.inputLength = instanceData.x.length ∧
      final controller.one = 1 := by
  have hprovider :
      ProviderSpec regs instanceData frame.node instanceData.x
        (SourceValue.failureChunk regs)
        (Residue.failureValue tm instanceData.blockLength) :=
    failureProvider_spec_internal tm regs instanceData frame.node
  obtain ⟨final, hrun, hfinal, hfinalFrame,
      hfinalInputLength, hfinalOne⟩ :=
    enterWith_runs_internal regs instanceData frame rest
      instanceData.x (SourceValue.failureChunk regs)
      (Residue.failureValue tm instanceData.blockLength)
      logicalBank store hphase hprovider hquery hframe
      hinputLength hone
  refine ⟨final, ?_, ?_, hfinalFrame, hfinalInputLength,
    hfinalOne⟩
  · simpa [failure] using hrun
  · exact hfinal

theorem failure_runs_internal
    {tm : TM workTapeCount}
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (rest : List (NeighborhoodScheduler.Frame tm instanceData))
    (logicalBank : Residue.Registers tm instanceData.blockLength)
    (store : Store)
    (hnode : frame.node = .failure)
    (hphase : frame.phase = .enter)
    (hquery :
      Representation.QueryState regs instanceData
        { stack := frame :: rest
          registers := logicalBank }
        store)
    (hframe :
      SearchProgram.InputFrame
        controller regs.footprint instanceData.x store)
    (hinputLength :
      store controller.inputLength = instanceData.x.length)
    (hone : store controller.one = 1) :
    ∃ final,
      Runs (failure regs) store final ∧
      Representation.QueryState regs instanceData
        (NeighborhoodScheduler.State.next
          { stack := frame :: rest
            registers := logicalBank })
        final ∧
      SearchProgram.InputFrame
        controller regs.footprint instanceData.x final ∧
      final controller.inputLength = instanceData.x.length ∧
      final controller.one = 1 := by
  obtain ⟨final, hrun, hfinal, hfinalFrame,
      hfinalInputLength, hfinalOne⟩ :=
    failureValue_runs_internal regs instanceData frame rest
      logicalBank store hphase hquery hframe hinputLength hone
  refine ⟨final, hrun, ?_, hfinalFrame, hfinalInputLength,
    hfinalOne⟩
  simpa [NeighborhoodScheduler.State.next, hphase, hnode] using
    hfinal

theorem source_runs_internal
    {tm : TM workTapeCount}
    (order : FiniteEncoding.StateOrder tm)
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (rest : List (NeighborhoodScheduler.Frame tm instanceData))
    (logicalBank : Residue.Registers tm instanceData.blockLength)
    (tape : TapeIndex workTapeCount) (block : ℕ)
    (store : Store)
    (hnode : frame.node = .graph (.source tape block))
    (hphase : frame.phase = .enter)
    (hencoding :
      instanceData.encoding =
        FiniteEncoding.ofStateOrder order instanceData.blockLength)
    (hquery :
      Representation.QueryState regs instanceData
        { stack := frame :: rest
          registers := logicalBank }
        store)
    (hframe :
      SearchProgram.InputFrame
        controller regs.footprint instanceData.x store)
    (hinputLength :
      store controller.inputLength = instanceData.x.length)
    (hone : store controller.one = 1) :
    ∃ final,
      Runs (source tm order regs) store final ∧
      Representation.QueryState regs instanceData
        (NeighborhoodScheduler.State.next
          { stack := frame :: rest
            registers := logicalBank })
        final ∧
      SearchProgram.InputFrame
        controller regs.footprint instanceData.x final ∧
      final controller.inputLength = instanceData.x.length ∧
      final controller.one = 1 := by
  have hframeBound :
      NeighborhoodScheduler.FrameBounds.FrameBound frame :=
    hquery.bounds frame (by simp)
  have hfits :
      ∀ digit ∈
          FrameCodec.nodeDigits
            (show
              NeighborhoodEvaluator.QueryNode
                workTapeCount instanceData.horizon
              from .graph (.source tape block)),
        digit < Representation.digitBase instanceData := by
    simpa [hnode] using
      FrameBounds.frameBound_nodeDigits_fit frame hframeBound
  have hprovider :
      ProviderSpec regs instanceData frame.node instanceData.x
        (sourceProvider tm order regs)
        (Residue.sourceValue tm instanceData.x
          instanceData.blockLength instanceData.encoding
          instanceData.positive tape block) := by
    rw [hnode]
    exact sourceProvider_spec_internal tm order regs instanceData
      tape block hencoding hfits
  obtain ⟨final, hrun, hfinal, hfinalFrame,
      hfinalInputLength, hfinalOne⟩ :=
    enterWith_runs_internal regs instanceData frame rest
      instanceData.x (sourceProvider tm order regs)
      (Residue.sourceValue tm instanceData.x
        instanceData.blockLength instanceData.encoding
        instanceData.positive tape block)
      logicalBank store hphase hprovider hquery hframe
      hinputLength hone
  refine ⟨final, ?_, ?_, hfinalFrame, hfinalInputLength,
    hfinalOne⟩
  · simpa [source] using hrun
  · simpa [NeighborhoodScheduler.State.next, hphase, hnode] using
      hfinal

end Internal
end EnterLeaf
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
