/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.ChildNode
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.ProviderRootInit.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.QueryInitialization
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodScheduler.FrameBounds

/-!
# Uniform initialization of local-consistency provider queries -- proofs
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace ProviderRootInitialization
namespace Internal

open RAM Structured
open NeighborhoodExecutableEvaluation

variable {controller : SearchProgram.Registers}

private theorem basics_runs
    (operations : List Basic) (store : Store) :
    Runs (Cmd.basics operations) store
      (Basic.execList operations store) := by
  obtain ⟨cost, space, hexec⟩ :=
    RAM.Structured.Internal.exec_basics_exists operations store
  exact ⟨operations.length, cost, space, hexec⟩

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

theorem buildProviderRoot_writesWithin_internal
    (workTapeCount : ℕ)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (rootFootprint regs)
      (buildProviderRoot workTapeCount controller regs) := by
  have htag :
      ControlDecode.tag regs ∈ rootFootprint regs := by
    apply Finset.mem_union_left
    apply Finset.mem_union_left
    apply Finset.mem_union_left
    apply Finset.mem_union_left
    apply Finset.mem_union_left
    apply Finset.mem_union_right
    exact
      Finset.mem_image.mpr
        ⟨(0 : Fin 5), Finset.mem_univ _, by
          simp [ControlDecode.tag, ChildNode.centerMap]⟩
  have htape :
      ControlDecode.nodeTape regs ∈ rootFootprint regs := by
    apply Finset.mem_union_left
    apply Finset.mem_union_left
    apply Finset.mem_union_right
    simp
  have hpayload0 :
      ControlDecode.nodePayload0 regs ∈ rootFootprint regs := by
    apply Finset.mem_union_left
    apply Finset.mem_union_left
    apply Finset.mem_union_left
    apply Finset.mem_union_left
    apply Finset.mem_union_left
    apply Finset.mem_union_right
    exact
      Finset.mem_image.mpr
        ⟨(1 : Fin 5), Finset.mem_univ _, by
          simp [ControlDecode.nodePayload0, ControlDecode.second,
            ChildNode.centerMap]⟩
  have hpayload1 :
      ControlDecode.nodePayload1 regs ∈ rootFootprint regs := by
    apply Finset.mem_union_left
    apply Finset.mem_union_left
    apply Finset.mem_union_left
    apply Finset.mem_union_left
    apply Finset.mem_union_right
    simp
  have hchild :
      ChildNode.savedChildIndex regs ∈ rootFootprint regs := by
    apply Finset.mem_union_right
    simp
  constructor
  · simp only [providerFields, Cmd.basics]
    exact
      ⟨htag, htape, hpayload0, hpayload1, hpayload1,
        hchild, hchild⟩
  · exact cmdWritesWithin_mono
      (ChildNode.regenerateChild_writesWithin
        workTapeCount controller regs)
      (Finset.subset_union_left)

theorem rootFootprint_subset_layout_internal
    (regs : NeighborhoodTrial.Registers controller) :
    rootFootprint regs ⊆ regs.layout.footprint := by
  intro address haddress
  rw [rootFootprint, Finset.mem_union] at haddress
  rcases haddress with hprior | hsaved
  · exact ChildNode.priorAssemblyFootprint_subset_layout regs hprior
  · have hsaved' :
        address = ChildNode.savedChildIndex regs := by
      simpa using hsaved
    subst address
    exact Layout.index_mem_layout_footprint regs (31 : Fin 34)

theorem initializeProviderQuery_writesWithin_internal
    (workTapeCount : ℕ)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin regs.layout.footprint
      (initializeProviderQuery workTapeCount controller regs) := by
  exact
    ⟨cmdWritesWithin_mono
        (buildProviderRoot_writesWithin_internal
          workTapeCount controller regs)
        (rootFootprint_subset_layout_internal regs),
      QueryInitialization.initialize_writesWithin workTapeCount regs⟩

private theorem parameters_of_buildProviderRoot_run
    {tm : TM workTapeCount}
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (initial final : Store)
    (hparameters :
      Representation.Parameters regs instanceData initial)
    (hrun :
      Runs (buildProviderRoot workTapeCount controller regs)
        initial final) :
    Representation.Parameters regs instanceData final := by
  have hphysical (slot : Fin 34)
      (hslot :
        regs.index slot ∉ rootFootprint regs) :
      final (regs.index slot) = initial (regs.index slot) :=
    Footprint.runs_eq_outside
      (buildProviderRoot_writesWithin_internal
        workTapeCount controller regs)
      hrun hslot
  have h2 :
      regs.index 2 ∉ rootFootprint regs := by
    simp [rootFootprint, ChildNode.priorAssemblyFootprint,
      ChildNode.priorFootprint, ChildNode.centerFootprint,
      ChildNode.movementFootprint, ChildNode.nodeEncodingFootprint,
      ChildNode.movementMap, ChildNode.centerMap, ChildNode.priorMap,
      ChildNode.savedChildIndex, Layout.codecScratch,
      ControlDecode.nodeTape, ControlDecode.nodePayload1,
      ControlDecode.first, ControlDecode.third, regs.injective.eq_iff];
      decide
  have h3 :
      regs.index 3 ∉ rootFootprint regs := by
    simp [rootFootprint, ChildNode.priorAssemblyFootprint,
      ChildNode.priorFootprint, ChildNode.centerFootprint,
      ChildNode.movementFootprint, ChildNode.nodeEncodingFootprint,
      ChildNode.movementMap, ChildNode.centerMap, ChildNode.priorMap,
      ChildNode.savedChildIndex, Layout.codecScratch,
      ControlDecode.nodeTape, ControlDecode.nodePayload1,
      ControlDecode.first, ControlDecode.third, regs.injective.eq_iff];
      decide
  have h7 :
      regs.index 7 ∉ rootFootprint regs := by
    simp [rootFootprint, ChildNode.priorAssemblyFootprint,
      ChildNode.priorFootprint, ChildNode.centerFootprint,
      ChildNode.movementFootprint, ChildNode.nodeEncodingFootprint,
      ChildNode.movementMap, ChildNode.centerMap, ChildNode.priorMap,
      ChildNode.savedChildIndex, Layout.codecScratch,
      ControlDecode.nodeTape, ControlDecode.nodePayload1,
      ControlDecode.first, ControlDecode.third, regs.injective.eq_iff];
      decide
  have h8 :
      regs.index 8 ∉ rootFootprint regs := by
    simp [rootFootprint, ChildNode.priorAssemblyFootprint,
      ChildNode.priorFootprint, ChildNode.centerFootprint,
      ChildNode.movementFootprint, ChildNode.nodeEncodingFootprint,
      ChildNode.movementMap, ChildNode.centerMap, ChildNode.priorMap,
      ChildNode.savedChildIndex, Layout.codecScratch,
      ControlDecode.nodeTape, ControlDecode.nodePayload1,
      ControlDecode.first, ControlDecode.third, regs.injective.eq_iff];
      decide
  have h13 :
      regs.index 13 ∉ rootFootprint regs := by
    simp [rootFootprint, ChildNode.priorAssemblyFootprint,
      ChildNode.priorFootprint, ChildNode.centerFootprint,
      ChildNode.movementFootprint, ChildNode.nodeEncodingFootprint,
      ChildNode.movementMap, ChildNode.centerMap, ChildNode.priorMap,
      ChildNode.savedChildIndex, Layout.codecScratch,
      ControlDecode.nodeTape, ControlDecode.nodePayload1,
      ControlDecode.first, ControlDecode.third, regs.injective.eq_iff];
      decide
  have h14 :
      regs.index 14 ∉ rootFootprint regs := by
    simp [rootFootprint, ChildNode.priorAssemblyFootprint,
      ChildNode.priorFootprint, ChildNode.centerFootprint,
      ChildNode.movementFootprint, ChildNode.nodeEncodingFootprint,
      ChildNode.movementMap, ChildNode.centerMap, ChildNode.priorMap,
      ChildNode.savedChildIndex, Layout.codecScratch,
      ControlDecode.nodeTape, ControlDecode.nodePayload1,
      ControlDecode.first, ControlDecode.third, regs.injective.eq_iff];
      decide
  have h15 :
      regs.index 15 ∉ rootFootprint regs := by
    simp [rootFootprint, ChildNode.priorAssemblyFootprint,
      ChildNode.priorFootprint, ChildNode.centerFootprint,
      ChildNode.movementFootprint, ChildNode.nodeEncodingFootprint,
      ChildNode.movementMap, ChildNode.centerMap, ChildNode.priorMap,
      ChildNode.savedChildIndex, Layout.codecScratch,
      ControlDecode.nodeTape, ControlDecode.nodePayload1,
      ControlDecode.first, ControlDecode.third, regs.injective.eq_iff];
      decide
  have h16 :
      regs.index 16 ∉ rootFootprint regs := by
    simp [rootFootprint, ChildNode.priorAssemblyFootprint,
      ChildNode.priorFootprint, ChildNode.centerFootprint,
      ChildNode.movementFootprint, ChildNode.nodeEncodingFootprint,
      ChildNode.movementMap, ChildNode.centerMap, ChildNode.priorMap,
      ChildNode.savedChildIndex, Layout.codecScratch,
      ControlDecode.nodeTape, ControlDecode.nodePayload1,
      ControlDecode.first, ControlDecode.third, regs.injective.eq_iff];
      decide
  have h24 :
      regs.index 24 ∉ rootFootprint regs := by
    simp [rootFootprint, ChildNode.priorAssemblyFootprint,
      ChildNode.priorFootprint, ChildNode.centerFootprint,
      ChildNode.movementFootprint, ChildNode.nodeEncodingFootprint,
      ChildNode.movementMap, ChildNode.centerMap, ChildNode.priorMap,
      ChildNode.savedChildIndex, Layout.codecScratch,
      ControlDecode.nodeTape, ControlDecode.nodePayload1,
      ControlDecode.first, ControlDecode.third, regs.injective.eq_iff];
      decide
  refine
    { blockLength_eq := ?_
      horizon_eq := ?_
      digitBase_eq := ?_
      bankBase_eq := ?_
      frameBase_eq := ?_
      chunkCount_eq := ?_
      bankDigitCount_eq := ?_
      modulus_eq := ?_
      modulusPred_eq := ?_ }
  · exact (hphysical 2 h2).trans hparameters.blockLength_eq
  · exact (hphysical 3 h3).trans hparameters.horizon_eq
  · exact (hphysical 8 h8).trans hparameters.digitBase_eq
  · exact (hphysical 14 h14).trans hparameters.bankBase_eq
  · exact (hphysical 13 h13).trans hparameters.frameBase_eq
  · exact (hphysical 7 h7).trans hparameters.chunkCount_eq
  · exact (hphysical 15 h15).trans hparameters.bankDigitCount_eq
  · exact (hphysical 24 h24).trans hparameters.modulus_eq
  · exact (hphysical 16 h16).trans hparameters.modulusPred_eq

theorem buildProviderRoot_runs_internal
    {tm : TM workTapeCount}
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (code :
      Fin
        (3 ^
          NeighborhoodGraph.Guess.Enumeration.movementCount
            workTapeCount instanceData.horizon))
    (interval : Fin instanceData.horizon)
    (child : Fin (graphFanIn workTapeCount))
    (store : Store)
    (hguess :
      instanceData.guess =
        NeighborhoodGraph.Guess.Enumeration.candidateGuess code)
    (hstoreGuess : store controller.guess = code.val)
    (hstoreInterval : store controller.success = interval.val)
    (hstoreChild : store controller.verdict = child.val)
    (hparameters :
      Representation.Parameters regs instanceData store) :
    ∃ final,
      Runs
        (buildProviderRoot workTapeCount controller regs)
        store final ∧
      Representation.Parameters regs instanceData final ∧
      final (Layout.nodeCode regs) =
        FrameCodec.encodeNode
          (Representation.digitBase instanceData)
          (providerRoot instanceData interval child) := by
  let operations : List Basic :=
    [.imm (ControlDecode.tag regs) 2,
      .imm (ControlDecode.nodeTape regs) 0,
      .imm (ControlDecode.nodePayload0 regs)
        NeighborhoodGraph.Slot.center.toFin.val,
      .imm (ControlDecode.nodePayload1 regs) 0,
      .add (ControlDecode.nodePayload1 regs)
        controller.success (ControlDecode.nodePayload1 regs),
      .imm (ChildNode.savedChildIndex regs) 0,
      .add (ChildNode.savedChildIndex regs)
        controller.verdict (ChildNode.savedChildIndex regs)]
  let prepared := Basic.execList operations store
  have hprepare :
      Runs (providerFields controller regs) store prepared := by
    simpa [providerFields, operations] using
      basics_runs operations store
  let parent :
      NeighborhoodEvaluator.QueryNode
        workTapeCount instanceData.horizon :=
    .graph
      (.computation
        (TapeIndex.input workTapeCount)
        .center interval.val)
  let frame : NeighborhoodScheduler.Frame tm instanceData :=
    { fuel := instanceData.horizon
      node := parent
      scalar := 1
      out := Fin.last (graphFanIn workTapeCount)
      phase := .enter }
  let kind :=
    ((NeighborhoodGraph.predecessorIndexEquiv workTapeCount).symm child).1
  let tape :=
    ((NeighborhoodGraph.predecessorIndexEquiv workTapeCount).symm child).2
  have hworkspaceController
      (workspaceSlot : Fin 34) (controllerSlot : Fin 17) :
      regs.index workspaceSlot ≠ controller.index controllerSlot :=
    regs.index_ne_controller workspaceSlot controllerSlot
  have hcontrollerWorkspace
      (controllerSlot : Fin 17) (workspaceSlot : Fin 34) :
      controller.index controllerSlot ≠ regs.index workspaceSlot :=
    (hworkspaceController workspaceSlot controllerSlot).symm
  have hdecoded :
      ControlDecode.EncodedNodePost regs frame.node prepared := by
    constructor <;>
      simp [prepared, operations, Basic.execList, Basic.exec, frame,
        parent, ControlDecode.expectedNodeValues, ControlDecode.tag,
        ControlDecode.nodeTape, ControlDecode.nodePayload0,
        ControlDecode.nodePayload1, ControlDecode.first,
        ControlDecode.second, ControlDecode.third,
        ChildNode.savedChildIndex, Layout.codecScratch,
        TapeIndex.input, SearchProgram.Registers.success,
        SearchProgram.Registers.verdict, regs.injective.eq_iff,
        hcontrollerWorkspace,
        hstoreInterval, hstoreChild]
  have hchild :
      prepared (ChildNode.savedChildIndex regs) =
        (NeighborhoodGraph.predecessorIndexEquiv
          workTapeCount (kind, tape)).val := by
    have hinverse :
        NeighborhoodGraph.predecessorIndexEquiv
            workTapeCount (kind, tape) =
          child := by
      change
        (NeighborhoodGraph.predecessorIndexEquiv workTapeCount)
            ((NeighborhoodGraph.predecessorIndexEquiv
              workTapeCount).symm child) =
          child
      exact
        (NeighborhoodGraph.predecessorIndexEquiv workTapeCount).apply_symm_apply
          child
    rw [hinverse]
    simp [prepared, operations, Basic.execList, Basic.exec,
      ChildNode.savedChildIndex, Layout.codecScratch,
      SearchProgram.Registers.success, SearchProgram.Registers.verdict,
      hcontrollerWorkspace, hstoreChild]
  obtain ⟨final, hregenerate, hnode, _hdigit, _houtside⟩ :=
    ChildNode.regenerateChild_frameChild_runs
      code frame controller regs prepared
      (TapeIndex.input workTapeCount) tape .center kind interval.val
      interval.isLt hdecoded hchild
      (by
        simpa [prepared, operations, Basic.execList, Basic.exec,
          SearchProgram.Registers.guess,
          SearchProgram.Registers.success, SearchProgram.Registers.verdict,
          hworkspaceController, hcontrollerWorkspace] using hstoreGuess)
      hguess rfl
  have hrun :
      Runs
        (buildProviderRoot workTapeCount controller regs)
        store final := by
    simpa [buildProviderRoot] using
      Runs.seq hprepare hregenerate
  refine
    ⟨final, hrun,
      parameters_of_buildProviderRoot_run
        controller regs instanceData store final hparameters hrun,
      ?_⟩
  have hbase :
      prepared (Layout.chunkRadix regs) =
        store (Layout.chunkRadix regs) := by
    simp [prepared, operations, Basic.execList, Basic.exec,
      Layout.chunkRadix, SearchProgram.Registers.success,
      SearchProgram.Registers.verdict, regs.injective.eq_iff,
      hcontrollerWorkspace]
  rw [hnode, hbase, hparameters.digitBase_eq]
  have hinverse :
      NeighborhoodGraph.predecessorIndexEquiv
          workTapeCount (kind, tape) =
        child := by
    change
      (NeighborhoodGraph.predecessorIndexEquiv workTapeCount)
          ((NeighborhoodGraph.predecessorIndexEquiv
            workTapeCount).symm child) =
        child
    exact
      (NeighborhoodGraph.predecessorIndexEquiv workTapeCount).apply_symm_apply
        child
  simp [NeighborhoodScheduler.Frame.childNode, frame, parent,
    providerRoot, hinverse]

theorem initializeProviderQuery_runs_internal
    {tm : TM workTapeCount}
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (code :
      Fin
        (3 ^
          NeighborhoodGraph.Guess.Enumeration.movementCount
            workTapeCount instanceData.horizon))
    (interval : Fin instanceData.horizon)
    (child : Fin (graphFanIn workTapeCount))
    (store : Store)
    (hguess :
      instanceData.guess =
        NeighborhoodGraph.Guess.Enumeration.candidateGuess code)
    (hstoreGuess : store controller.guess = code.val)
    (hstoreInterval : store controller.success = interval.val)
    (hstoreChild : store controller.verdict = child.val)
    (hparameters :
      Representation.Parameters regs instanceData store) :
    ∃ final,
      Runs
        (initializeProviderQuery workTapeCount controller regs)
        store final ∧
      Representation.QueryState regs instanceData
        (NeighborhoodScheduler.Decision.queryInitial
          (providerRoot instanceData interval child))
        final := by
  obtain ⟨rooted, hroot, hrootParameters, hrootCode⟩ :=
    buildProviderRoot_runs_internal
      controller regs instanceData code interval child store
      hguess hstoreGuess hstoreInterval hstoreChild hparameters
  obtain ⟨final, hinitialize, hquery⟩ :=
    QueryInitialization.initialize_runs
      regs instanceData (providerRoot instanceData interval child)
      rooted hrootParameters hrootCode
      (NeighborhoodScheduler.FrameBounds.queryBound_childAt
        instanceData
        (.graph
          (.computation
            (TapeIndex.input workTapeCount)
            .center interval.val))
        child)
  have hmodulus :
      1 < NeighborhoodScheduler.fieldModulus instanceData :=
    NeighborhoodScheduler.FrameBounds.fieldModulus_one_lt instanceData
  have hnormalize :
      TreeEval.CookMertz.PrimeField.Runtime.normalize
        (NeighborhoodScheduler.fieldModulus instanceData) 1 = 1 := by
    simp [TreeEval.CookMertz.PrimeField.Runtime.normalize,
      Nat.mod_eq_of_lt hmodulus]
  have hzero :
      NeighborhoodScheduler.Decision.zeroRegisters =
        ResidueBankOps.zeroRegisters tm instanceData.blockLength := by
    funext register chunk
    simp [NeighborhoodScheduler.Decision.zeroRegisters,
      ResidueBankOps.zeroRegisters,
      NeighborhoodExecutableEvaluation.Residue.zeroValue,
      TreeEval.CookMertz.PrimeField.Runtime.normalize]
  exact
    ⟨final, by
      simpa [initializeProviderQuery] using
        Runs.seq hroot hinitialize,
      by
        simpa [NeighborhoodScheduler.Decision.queryInitial,
          hnormalize, hzero] using hquery⟩

theorem initializeProviderQuery_runs_preserving_abi_internal
    {tm : TM workTapeCount}
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (code :
      Fin
        (3 ^
          NeighborhoodGraph.Guess.Enumeration.movementCount
            workTapeCount instanceData.horizon))
    (interval : Fin instanceData.horizon)
    (child : Fin (graphFanIn workTapeCount))
    (store : Store)
    (hguess :
      instanceData.guess =
        NeighborhoodGraph.Guess.Enumeration.candidateGuess code)
    (hstoreGuess : store controller.guess = code.val)
    (hstoreInterval : store controller.success = interval.val)
    (hstoreChild : store controller.verdict = child.val)
    (hparameters :
      Representation.Parameters regs instanceData store)
    (hframe :
      SearchProgram.InputFrame
        controller regs.footprint instanceData.x store)
    (hinputLength :
      store controller.inputLength = instanceData.x.length)
    (hone : store controller.one = 1) :
    ∃ final,
      Runs
        (initializeProviderQuery workTapeCount controller regs)
        store final ∧
      Representation.QueryState regs instanceData
        (NeighborhoodScheduler.Decision.queryInitial
          (providerRoot instanceData interval child))
        final ∧
      SearchProgram.InputFrame
        controller regs.footprint instanceData.x final ∧
      final controller.inputLength = instanceData.x.length ∧
      final controller.one = 1 ∧
      final controller.guess = code.val ∧
      final controller.success = interval.val ∧
      final controller.verdict = child.val := by
  obtain ⟨final, hrun, hquery⟩ :=
    initializeProviderQuery_runs_internal
      controller regs instanceData code interval child store
      hguess hstoreGuess hstoreInterval hstoreChild hparameters
  have hwritesLayout :=
    initializeProviderQuery_writesWithin_internal
      workTapeCount controller regs
  have hwritesTrial :
      Footprint.CmdWritesWithin regs.footprint
        (initializeProviderQuery workTapeCount controller regs) :=
    cmdWritesWithin_mono hwritesLayout
      (fun address haddress => Finset.mem_union_left _ haddress)
  have hframeFinal :=
    NeighborhoodTrial.Registers.runs_preserves_inputFrame
      regs hwritesTrial hrun hframe
  have hcontroller (slot : Fin 17) :
      final (controller.index slot) =
        store (controller.index slot) := by
    apply Footprint.runs_eq_outside hwritesLayout hrun
    exact fun hlayout =>
      Finset.disjoint_left.mp
        (NeighborhoodTrial.Registers.layout_disjoint_controller regs)
        hlayout (controller.index_mem_footprint slot)
  exact
    ⟨final, hrun, hquery, hframeFinal,
      (hcontroller 0).trans hinputLength,
      (hcontroller 14).trans hone,
      (hcontroller 2).trans hstoreGuess,
      (hcontroller 3).trans hstoreInterval,
      (hcontroller 4).trans hstoreChild⟩

end Internal
end ProviderRootInitialization
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
