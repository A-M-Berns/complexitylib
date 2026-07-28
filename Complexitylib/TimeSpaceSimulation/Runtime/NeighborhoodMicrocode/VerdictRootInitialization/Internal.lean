/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.ChildNode
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.QueryReinitialization
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.VerdictRootInitialization.Defs

/-!
# Uniform initialization of the verdict-consistency root -- proofs
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace VerdictRootInitialization
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

private theorem copy_update_runs
    {destination source : ℕ} (store : Store)
    (hne : destination ≠ source) :
    Runs (ControlDecode.copy destination source) store
      (Function.update store destination (store source)) := by
  apply Runs.seq (Runs.basic (.imm destination 0) store)
  simpa [Basic.exec, Function.update_of_ne, hne, Ne.symm hne] using
    Runs.basic
      (.add destination source destination)
      (Basic.exec (.imm destination 0) store)

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

private theorem centerFootprint_subset_prior
    (regs : NeighborhoodTrial.Registers controller) :
    ChildNode.centerFootprint regs ⊆ ChildNode.priorFootprint regs := by
  intro address haddress
  exact Finset.mem_union_left _
    (Finset.mem_union_left _ haddress)

private theorem prior_index_mem
    (regs : NeighborhoodTrial.Registers controller)
    (slot : Fin 5) :
    regs.index (ChildNode.priorMap slot) ∈
      ChildNode.priorFootprint regs := by
  apply Finset.mem_union_right
  exact Finset.mem_image.mpr ⟨slot, Finset.mem_univ _, rfl⟩

private theorem nodePayload1_mem_prior
    (regs : NeighborhoodTrial.Registers controller) :
    ControlDecode.nodePayload1 regs ∈
      ChildNode.priorFootprint regs := by
  apply Finset.mem_union_left
  exact Finset.mem_union_right _ (Finset.mem_singleton_self _)

private theorem copy_writesWithin_prior
    (regs : NeighborhoodTrial.Registers controller)
    (destination source : ℕ)
    (hmem : destination ∈ ChildNode.priorFootprint regs) :
    Footprint.CmdWritesWithin (ChildNode.priorFootprint regs)
      (ControlDecode.copy destination source) := by
  simpa [ControlDecode.copy, Footprint.CmdWritesWithin,
    Footprint.BasicWritesWithin] using And.intro hmem hmem

private theorem prior_index_not_mem_center
    (regs : NeighborhoodTrial.Registers controller)
    (slot : Fin 5) :
    regs.index (ChildNode.priorMap slot) ∉
      ChildNode.centerFootprint regs := by
  simp only [ChildNode.centerFootprint, Finset.mem_union,
    ChildNode.movementFootprint, Finset.mem_image,
    Finset.mem_univ, true_and, not_or, not_exists]
  constructor
  · intro movementSlot heq
    have hslot := regs.injective heq
    fin_cases slot <;> fin_cases movementSlot <;>
      simp [ChildNode.priorMap, ChildNode.movementMap] at hslot
  · intro centerSlot heq
    have hslot := regs.injective heq
    fin_cases slot <;> fin_cases centerSlot <;>
      simp [ChildNode.priorMap, ChildNode.centerMap] at hslot

private theorem priorFootprint_subset_assembly
    (regs : NeighborhoodTrial.Registers controller) :
    ChildNode.priorFootprint regs ⊆
      ChildNode.priorAssemblyFootprint regs :=
  fun _ haddress =>
    Finset.mem_union_left _
      (Finset.mem_union_left _ haddress)

theorem exactPriorSearchBody_writesWithin_internal
    (workTapeCount : ℕ)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (ChildNode.priorFootprint regs)
      (exactPriorSearchBody workTapeCount controller regs) := by
  simp only [exactPriorSearchBody, Cmd.seqList,
    Footprint.CmdWritesWithin]
  exact
    ⟨prior_index_mem regs 1,
      copy_writesWithin_prior regs _ _
        (nodePayload1_mem_prior regs),
      cmdWritesWithin_mono
        (ChildNode.deriveCenter_writesWithin
          workTapeCount controller regs)
        (centerFootprint_subset_prior regs),
      ⟨trivial,
        ChildNode.recordPriorIfContains_writesWithin regs⟩⟩

theorem scanExactPrior_writesWithin_internal
    (workTapeCount : ℕ)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (ChildNode.priorFootprint regs)
      (scanExactPrior workTapeCount controller regs) := by
  have hone :
      (ChildNode.movementDivision regs).one ∈
        ChildNode.priorFootprint regs :=
    centerFootprint_subset_prior regs
      (Finset.mem_union_left _
        (Finset.mem_image.mpr
          ⟨(3 : Fin 6), Finset.mem_univ _, rfl⟩))
  simp only [scanExactPrior, Cmd.basics,
    Footprint.CmdWritesWithin]
  exact
    ⟨⟨hone, prior_index_mem regs 2, prior_index_mem regs 3,
        prior_index_mem regs 4⟩,
      ⟨copy_writesWithin_prior regs _ _
          (prior_index_mem regs 1),
        exactPriorSearchBody_writesWithin_internal
          workTapeCount controller regs⟩⟩

theorem initializeVerdictFields_writesWithin_internal
    (workTapeCount : ℕ)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin
      (ChildNode.priorAssemblyFootprint regs)
      (initializeVerdictFields workTapeCount controller regs) := by
  have hnodeTape :
      ControlDecode.nodeTape regs ∈
        ChildNode.priorAssemblyFootprint regs := by
    simp [ChildNode.priorAssemblyFootprint]
  have hrequested :
      ChildNode.requestedBlock regs ∈
        ChildNode.priorAssemblyFootprint regs :=
    priorFootprint_subset_assembly regs (prior_index_mem regs 0)
  have htest :
      (ChildNode.movementDivision regs).test ∈
        ChildNode.priorAssemblyFootprint regs := by
    apply priorFootprint_subset_assembly regs
    apply centerFootprint_subset_prior regs
    apply Finset.mem_union_left
    exact Finset.mem_image.mpr
      ⟨(2 : Fin 6), Finset.mem_univ _, rfl⟩
  have hpayload :
      ControlDecode.nodePayload1 regs ∈
        ChildNode.priorAssemblyFootprint regs :=
    priorFootprint_subset_assembly regs
      (nodePayload1_mem_prior regs)
  simp only [initializeVerdictFields, Cmd.seqList,
    Footprint.CmdWritesWithin, ControlDecode.copy,
    Footprint.BasicWritesWithin]
  exact
    ⟨hnodeTape, hrequested, htest, ⟨hrequested, trivial⟩,
      hpayload, hpayload⟩

theorem installExactPrior_writesWithin_internal
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin
      (ChildNode.priorAssemblyFootprint regs)
      (installExactPrior regs) := by
  have hvalid :
      ChildNode.centerValid regs ∈
        ChildNode.priorAssemblyFootprint regs := by
    apply priorFootprint_subset_assembly regs
    apply centerFootprint_subset_prior regs
    exact Finset.mem_union_right _
      (Finset.mem_image.mpr
        ⟨(2 : Fin 5), Finset.mem_univ _, rfl⟩)
  exact ⟨hvalid, ChildNode.installPrior_writesWithin regs⟩

theorem buildVerdictRoot_writesWithin_internal
    (workTapeCount : ℕ)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin
      (ChildNode.priorAssemblyFootprint regs)
      (buildVerdictRoot workTapeCount controller regs) := by
  simp only [buildVerdictRoot, Cmd.seqList,
    Footprint.CmdWritesWithin]
  exact
    ⟨initializeVerdictFields_writesWithin_internal
        workTapeCount controller regs,
      cmdWritesWithin_mono
        (scanExactPrior_writesWithin_internal
          workTapeCount controller regs)
        (priorFootprint_subset_assembly regs),
      installExactPrior_writesWithin_internal regs⟩

theorem reinitializeVerdictQuery_writesWithin_internal
    (workTapeCount : ℕ)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin regs.layout.footprint
      (reinitializeVerdictQuery workTapeCount controller regs) := by
  exact
    ⟨cmdWritesWithin_mono
        (buildVerdictRoot_writesWithin_internal
          workTapeCount controller regs)
        (ChildNode.priorAssemblyFootprint_subset_layout regs),
      QueryReinitialization.reinitialize_writesWithin
        workTapeCount regs (verdictOut workTapeCount)⟩

private theorem retained_not_mem_priorAssembly
    (regs : NeighborhoodTrial.Registers controller) :
    Layout.blockLength regs ∉ ChildNode.priorAssemblyFootprint regs ∧
    Layout.horizon regs ∉ ChildNode.priorAssemblyFootprint regs ∧
    Layout.chunkRadix regs ∉ ChildNode.priorAssemblyFootprint regs ∧
    Layout.bankRadix regs ∉ ChildNode.priorAssemblyFootprint regs ∧
    Layout.frameRadix regs ∉ ChildNode.priorAssemblyFootprint regs ∧
    Layout.chunkCount regs ∉ ChildNode.priorAssemblyFootprint regs ∧
    Layout.bankDigitCount regs ∉ ChildNode.priorAssemblyFootprint regs ∧
    Layout.modulus regs ∉ ChildNode.priorAssemblyFootprint regs ∧
    Layout.modulusPred regs ∉ ChildNode.priorAssemblyFootprint regs ∧
    regs.layout.bank ∉ ChildNode.priorAssemblyFootprint regs := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    simp [ChildNode.priorAssemblyFootprint,
      ChildNode.priorFootprint, ChildNode.centerFootprint,
      ChildNode.movementFootprint, ChildNode.movementMap,
      ChildNode.centerMap, ChildNode.priorMap,
      ChildNode.nodeEncodingFootprint, Layout.blockLength,
      Layout.horizon, Layout.chunkRadix, Layout.bankRadix,
      Layout.frameRadix, Layout.chunkCount, Layout.bankDigitCount,
      Layout.modulus, Layout.modulusPred, Layout.nodeCode,
      Layout.codecDigit, NeighborhoodTrial.Registers.layout,
      regs.injective.eq_iff]
    decide

private theorem parameters_of_priorAssembly_run
    {tm : TM workTapeCount}
    {command : Cmd}
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (initial final : Store)
    (hparameters :
      Representation.Parameters regs instanceData initial)
    (hwrites :
      Footprint.CmdWritesWithin
        (ChildNode.priorAssemblyFootprint regs) command)
    (hrun : Runs command initial final) :
    Representation.Parameters regs instanceData final := by
  rcases retained_not_mem_priorAssembly regs with
    ⟨hblock, hhorizon, hdigitBase, hbankBase, hframeBase,
      hchunkCount, hbankCount, hmodulus, hmodulusPred, _⟩
  have hpreserved (address : ℕ)
      (haddress :
        address ∉ ChildNode.priorAssemblyFootprint regs) :
      final address = initial address :=
    Footprint.runs_eq_outside hwrites hrun haddress
  exact
    { blockLength_eq :=
        (hpreserved _ hblock).trans hparameters.blockLength_eq
      horizon_eq :=
        (hpreserved _ hhorizon).trans hparameters.horizon_eq
      digitBase_eq :=
        (hpreserved _ hdigitBase).trans hparameters.digitBase_eq
      bankBase_eq :=
        (hpreserved _ hbankBase).trans hparameters.bankBase_eq
      frameBase_eq :=
        (hpreserved _ hframeBase).trans hparameters.frameBase_eq
      chunkCount_eq :=
        (hpreserved _ hchunkCount).trans hparameters.chunkCount_eq
      bankDigitCount_eq :=
        (hpreserved _ hbankCount).trans
          hparameters.bankDigitCount_eq
      modulus_eq :=
        (hpreserved _ hmodulus).trans hparameters.modulus_eq
      modulusPred_eq :=
        (hpreserved _ hmodulusPred).trans
          hparameters.modulusPred_eq }

private theorem bank_of_priorAssembly_run
    {command : Cmd}
    (regs : NeighborhoodTrial.Registers controller)
    (initial final : Store)
    (hwrites :
      Footprint.CmdWritesWithin
        (ChildNode.priorAssemblyFootprint regs) command)
    (hrun : Runs command initial final) :
    final regs.layout.bank = initial regs.layout.bank :=
  Footprint.runs_eq_outside hwrites hrun
    (retained_not_mem_priorAssembly regs).2.2.2.2.2.2.2.2.2

theorem exactPriorSearchValue_contains_internal
    (workTapeCount word tape requested count interval center : ℕ)
    (hresult :
      exactPriorSearchValue workTapeCount word tape requested count =
        some (interval, center)) :
    NeighborhoodGraph.NeighborhoodContains center requested := by
  induction count with
  | zero =>
      simp [exactPriorSearchValue] at hresult
  | succ count ih =>
      generalize hcenter :
          ChildNode.derivedCenterValue
            workTapeCount word tape count = result
      cases result with
      | none =>
          exact ih (by
            simpa [exactPriorSearchValue, hcenter] using hresult)
      | some candidateCenter =>
          by_cases hcontains :
              NeighborhoodGraph.NeighborhoodContains
                candidateCenter requested
          · have heq :
                some (count, candidateCenter) =
                  some (interval, center) := by
              simpa [exactPriorSearchValue, hcenter, hcontains] using
                hresult
            have hpairs :
                (count, candidateCenter) =
                  (interval, center) :=
              Option.some.inj heq
            cases hpairs
            exact hcontains
          · exact ih (by
              simpa [exactPriorSearchValue, hcenter, hcontains] using
                hresult)

private def ExactPriorMatch
    (workTapeCount word tape requested interval : ℕ) : Prop :=
  ∃ center,
    ChildNode.derivedCenterValue
        workTapeCount word tape interval = some center ∧
      NeighborhoodGraph.NeighborhoodContains center requested

private theorem exactPriorSearchValue_none_no_match
    (workTapeCount word tape requested count : ℕ)
    (hsearch :
      exactPriorSearchValue
        workTapeCount word tape requested count = none) :
    ∀ interval, interval < count →
      ¬ExactPriorMatch
        workTapeCount word tape requested interval := by
  induction count with
  | zero =>
      intro interval hinterval
      omega
  | succ count ih =>
      generalize hcenter :
        ChildNode.derivedCenterValue
          workTapeCount word tape count = result
      cases result with
      | none =>
          have hrecursive :
              exactPriorSearchValue
                workTapeCount word tape requested count = none := by
            simpa [exactPriorSearchValue, hcenter] using hsearch
          intro interval hinterval hmatch
          by_cases hlt : interval < count
          · exact ih hrecursive interval hlt hmatch
          · have heq : interval = count := by
              omega
            subst interval
            rcases hmatch with ⟨center, hotherCenter, hcontains⟩
            rw [hcenter] at hotherCenter
            simp at hotherCenter
      | some center =>
          by_cases hcontains :
              NeighborhoodGraph.NeighborhoodContains center requested
          · simp [exactPriorSearchValue, hcenter, hcontains] at hsearch
          · have hrecursive :
                exactPriorSearchValue
                  workTapeCount word tape requested count = none := by
              simpa [exactPriorSearchValue, hcenter, hcontains] using
                hsearch
            intro interval hinterval hmatch
            by_cases hlt : interval < count
            · exact ih hrecursive interval hlt hmatch
            · have heq : interval = count := by
                omega
              subst interval
              rcases hmatch with
                ⟨otherCenter, hotherCenter, hotherContains⟩
              rw [hcenter] at hotherCenter
              simp only [Option.some.injEq] at hotherCenter
              subst otherCenter
              exact hcontains hotherContains

private theorem exactPriorSearchValue_some_maximal
    (workTapeCount word tape requested count interval center : ℕ)
    (hsearch :
      exactPriorSearchValue
          workTapeCount word tape requested count =
        some (interval, center)) :
    interval < count ∧
      ChildNode.derivedCenterValue
          workTapeCount word tape interval = some center ∧
      NeighborhoodGraph.NeighborhoodContains center requested ∧
      ∀ later, interval < later → later < count →
        ¬ExactPriorMatch
          workTapeCount word tape requested later := by
  induction count with
  | zero =>
      simp [exactPriorSearchValue] at hsearch
  | succ count ih =>
      generalize hcurrent :
        ChildNode.derivedCenterValue
          workTapeCount word tape count = result
      cases result with
      | none =>
          have hrecursive :
              exactPriorSearchValue
                  workTapeCount word tape requested count =
                some (interval, center) := by
            simpa [exactPriorSearchValue, hcurrent] using hsearch
          rcases ih hrecursive with
            ⟨hinterval, hcenter, hcontains, hmaximal⟩
          refine ⟨by omega, hcenter, hcontains, ?_⟩
          intro later hlater hbound hlaterMatch
          by_cases hlt : later < count
          · exact hmaximal later hlater hlt hlaterMatch
          · have heq : later = count := by
              omega
            subst later
            rcases hlaterMatch with
              ⟨otherCenter, hotherCenter, hotherContains⟩
            rw [hcurrent] at hotherCenter
            simp at hotherCenter
      | some current =>
          by_cases hcontains :
              NeighborhoodGraph.NeighborhoodContains current requested
          · have hpairs :
                count = interval ∧ current = center := by
              simpa [exactPriorSearchValue, hcurrent, hcontains] using
                hsearch
            rcases hpairs with ⟨rfl, rfl⟩
            refine ⟨by omega, hcurrent, hcontains, ?_⟩
            intro later hlater hbound
            omega
          · have hrecursive :
                exactPriorSearchValue
                    workTapeCount word tape requested count =
                  some (interval, center) := by
              simpa [exactPriorSearchValue, hcurrent, hcontains] using
                hsearch
            rcases ih hrecursive with
              ⟨hinterval, hcenter, hmatch, hmaximal⟩
            refine ⟨by omega, hcenter, hmatch, ?_⟩
            intro later hlater hbound hlaterMatch
            by_cases hlt : later < count
            · exact hmaximal later hlater hlt hlaterMatch
            · have heq : later = count := by
                omega
              subst later
              rcases hlaterMatch with
                ⟨otherCenter, hotherCenter, hotherContains⟩
              rw [hcurrent] at hotherCenter
              simp only [Option.some.injEq] at hotherCenter
              subst otherCenter
              exact hcontains hotherContains

private theorem mem_candidateGuess_priorIntervals_iff
    (code :
      Fin
        (3 ^
          NeighborhoodGraph.Guess.Enumeration.movementCount
            workTapeCount horizon))
    (tape : TapeIndex workTapeCount)
    (requested count : ℕ) (hcount : count ≤ horizon)
    (previous : Fin count) :
    previous ∈
        NeighborhoodGraph.Guess.CenterGuess.priorIntervals
          (NeighborhoodGraph.Guess.Enumeration.candidateGuess code)
          tape requested count ↔
      ExactPriorMatch
        workTapeCount code.val tape.val requested previous.val := by
  have hderived :=
    ChildNode.derivedCenterValue_candidateGuess
      code tape previous.val (by omega)
  simp only
    [NeighborhoodGraph.Guess.CenterGuess.priorIntervals,
      Finset.mem_filter, Finset.mem_univ, true_and]
  rw [← hderived]
  generalize hcenter :
    ChildNode.derivedCenterValue
      workTapeCount code.val tape.val previous.val = result
  cases result with
  | none =>
      simp [ExactPriorMatch, hcenter]
  | some center =>
      simp [ExactPriorMatch, hcenter]

private theorem candidateGuess_previousInterval_eq_none
    (code :
      Fin
        (3 ^
          NeighborhoodGraph.Guess.Enumeration.movementCount
            workTapeCount horizon))
    (tape : TapeIndex workTapeCount)
    (requested count : ℕ) (hcount : count ≤ horizon)
    (hnoMatch :
      ∀ interval, interval < count →
        ¬ExactPriorMatch
          workTapeCount code.val tape.val requested interval) :
    NeighborhoodGraph.Guess.CenterGuess.previousInterval
        (NeighborhoodGraph.Guess.Enumeration.candidateGuess code)
        tape requested count =
      none := by
  have hempty :
      ¬(NeighborhoodGraph.Guess.CenterGuess.priorIntervals
          (NeighborhoodGraph.Guess.Enumeration.candidateGuess code)
          tape requested count).Nonempty := by
    intro hnonempty
    rcases hnonempty with ⟨previous, hprevious⟩
    exact hnoMatch previous.val previous.isLt
      ((mem_candidateGuess_priorIntervals_iff
        code tape requested count hcount previous).1 hprevious)
  simp [NeighborhoodGraph.Guess.CenterGuess.previousInterval,
    hempty]

private theorem candidateGuess_previousInterval_eq_some
    (code :
      Fin
        (3 ^
          NeighborhoodGraph.Guess.Enumeration.movementCount
            workTapeCount horizon))
    (tape : TapeIndex workTapeCount)
    (requested count interval center : ℕ)
    (hcount : count ≤ horizon)
    (hinterval : interval < count)
    (hcenter :
      ChildNode.derivedCenterValue
        workTapeCount code.val tape.val interval = some center)
    (hcontains :
      NeighborhoodGraph.NeighborhoodContains center requested)
    (hmaximal :
      ∀ later, interval < later → later < count →
        ¬ExactPriorMatch
          workTapeCount code.val tape.val requested later) :
    NeighborhoodGraph.Guess.CenterGuess.previousInterval
        (NeighborhoodGraph.Guess.Enumeration.candidateGuess code)
        tape requested count =
      some ⟨interval, hinterval⟩ := by
  let previous : Fin count := ⟨interval, hinterval⟩
  have hpreviousMatch :
      ExactPriorMatch
        workTapeCount code.val tape.val requested previous.val :=
    ⟨center, hcenter, hcontains⟩
  have hpreviousMem :
      previous ∈
        NeighborhoodGraph.Guess.CenterGuess.priorIntervals
          (NeighborhoodGraph.Guess.Enumeration.candidateGuess code)
          tape requested count :=
    (mem_candidateGuess_priorIntervals_iff
      code tape requested count hcount previous).2 hpreviousMatch
  have hnonempty :
      (NeighborhoodGraph.Guess.CenterGuess.priorIntervals
          (NeighborhoodGraph.Guess.Enumeration.candidateGuess code)
          tape requested count).Nonempty :=
    ⟨previous, hpreviousMem⟩
  rw [NeighborhoodGraph.Guess.CenterGuess.previousInterval,
    dif_pos hnonempty]
  congr 1
  apply Fin.ext
  apply Nat.le_antisymm
  · by_contra hle
    change
      ¬((NeighborhoodGraph.Guess.CenterGuess.priorIntervals
          (NeighborhoodGraph.Guess.Enumeration.candidateGuess code)
          tape requested count).max' hnonempty).val ≤ interval at hle
    have hlt :
        interval <
          (NeighborhoodGraph.Guess.CenterGuess.priorIntervals
            (NeighborhoodGraph.Guess.Enumeration.candidateGuess code)
            tape requested count).max' hnonempty := by
      omega
    have hmaxMem :=
      Finset.max'_mem
        (NeighborhoodGraph.Guess.CenterGuess.priorIntervals
          (NeighborhoodGraph.Guess.Enumeration.candidateGuess code)
          tape requested count) hnonempty
    have hmaxMatch :=
      (mem_candidateGuess_priorIntervals_iff
        code tape requested count hcount _).1 hmaxMem
    exact hmaximal _ hlt (Fin.isLt _) hmaxMatch
  · exact Finset.le_max' _ previous hpreviousMem

theorem exactPriorQueryValue_candidateGuess_internal
    (code :
      Fin
        (3 ^
          NeighborhoodGraph.Guess.Enumeration.movementCount
            workTapeCount horizon))
    (tape : TapeIndex workTapeCount)
    (requested : ℕ) :
    ChildNode.priorQueryValue
        (horizon := horizon) tape requested
        (some
          (exactPriorSearchValue
            workTapeCount code.val tape.val requested horizon)) =
      NeighborhoodEvaluator.latestBlockRoot
        (NeighborhoodGraph.Guess.Enumeration.candidateGuess code)
        tape requested := by
  generalize hsearch :
    exactPriorSearchValue
      workTapeCount code.val tape.val requested horizon = result
  cases result with
  | none =>
      have hnoMatch :=
        exactPriorSearchValue_none_no_match
          workTapeCount code.val tape.val requested horizon hsearch
      have hprevious :=
        candidateGuess_previousInterval_eq_none
          code tape requested horizon (Nat.le_refl _) hnoMatch
      simp [ChildNode.priorQueryValue,
        NeighborhoodEvaluator.latestBlockRoot, hprevious]
  | some result =>
      rcases result with ⟨interval, center⟩
      rcases exactPriorSearchValue_some_maximal
          workTapeCount code.val tape.val requested horizon
          interval center hsearch with
        ⟨hinterval, hcenter, hcontains, hmaximal⟩
      have hprevious :=
        candidateGuess_previousInterval_eq_some
          code tape requested horizon interval center
          (Nat.le_refl _) hinterval hcenter hcontains hmaximal
      have hderived :=
        ChildNode.derivedCenterValue_candidateGuess
          code tape interval (by omega)
      rw [hcenter] at hderived
      simp [ChildNode.priorQueryValue,
        NeighborhoodEvaluator.latestBlockRoot, hprevious, ← hderived]

theorem initializeVerdictFields_runs_internal
    {tm : TM workTapeCount}
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (store : Store)
    (hparameters :
      Representation.Parameters regs instanceData store)
    (hone : store controller.one = 1) :
    ∃ final,
      Runs
        (initializeVerdictFields workTapeCount controller regs)
        store final ∧
      final (ControlDecode.nodeTape regs) =
        (TapeIndex.output workTapeCount).val ∧
      final (ChildNode.requestedBlock regs) =
        blockIndex instanceData.blockLength 1 ∧
      final (ControlDecode.nodePayload1 regs) =
        instanceData.horizon ∧
      final controller.one = 1 ∧
      final controller.guess = store controller.guess := by
  let taped :=
    Basic.exec
      (.imm (ControlDecode.nodeTape regs)
        (TapeIndex.output workTapeCount).val) store
  let requested :=
    Basic.exec (.imm (ChildNode.requestedBlock regs) 0) taped
  let tested :=
    Basic.exec
      (.sub (ChildNode.movementDivision regs).test
        (Layout.blockLength regs) controller.one) requested
  have htaped :
      Runs
        (.basic
          (.imm (ControlDecode.nodeTape regs)
            (TapeIndex.output workTapeCount).val))
        store taped :=
    Runs.basic _ _
  have hrequested :
      Runs
        (.basic (.imm (ChildNode.requestedBlock regs) 0))
        taped requested :=
    Runs.basic _ _
  have htested :
      Runs
        (.basic
          (.sub (ChildNode.movementDivision regs).test
            (Layout.blockLength regs) controller.one))
        requested tested :=
    Runs.basic _ _
  have htestedValue :
      tested (ChildNode.movementDivision regs).test =
        instanceData.blockLength - 1 := by
    have hone' : store (controller.index 14) = 1 := by
      simpa [SearchProgram.Registers.one,
        SearchProgram.Registers.primeRegisters,
        SearchProgram.Registers.primeSlot,
        PrimeSearch.Registers.one] using hone
    have h9one :
        controller.index 14 ≠ regs.index 9 :=
      (regs.index_ne_controller 9 14).symm
    have hrequestedOne :
        controller.index 14 ≠
          regs.index (ChildNode.priorMap 0) :=
      (regs.index_ne_controller (ChildNode.priorMap 0) 14).symm
    simp [tested, requested, taped, Basic.exec,
      Layout.blockLength, ChildNode.movementDivision,
      ChildNode.movementMap, ChildNode.priorMap,
      ControlDecode.nodeTape, ControlDecode.first,
      SearchProgram.Registers.one,
      SearchProgram.Registers.primeRegisters,
      SearchProgram.Registers.primeSlot,
      PrimeSearch.Registers.one,
      regs.injective.eq_iff,
      Function.update_of_ne, h9one, hrequestedOne,
      hparameters.blockLength_eq, hone']
  by_cases hlength : instanceData.blockLength = 1
  · let selected :=
      Basic.exec
        (.imm (ChildNode.requestedBlock regs) 1) tested
    have htestZero :
        tested (ChildNode.movementDivision regs).test = 0 := by
      rw [htestedValue, hlength]
    have hselect :
        Runs
          (.ifZero (ChildNode.movementDivision regs).test
            (.basic (.imm (ChildNode.requestedBlock regs) 1))
            .skip)
          tested selected :=
      Runs.ifZero htestZero (Runs.basic _ _)
    let final :=
      Function.update selected
        (ControlDecode.nodePayload1 regs)
        (selected (Layout.horizon regs))
    have hcopy :
        Runs
          (ControlDecode.copy
            (ControlDecode.nodePayload1 regs)
            (Layout.horizon regs))
          selected final :=
      copy_update_runs selected
        (regs.injective.ne (by decide : (11 : Fin 34) ≠ 3))
    have hrun :
        Runs
          (initializeVerdictFields workTapeCount controller regs)
          store final := by
      simpa [initializeVerdictFields, Cmd.seqList] using
        Runs.seq htaped
          (Runs.seq hrequested
            (Runs.seq htested (Runs.seq hselect hcopy)))
    have hwrites :
        Footprint.CmdWritesWithin regs.footprint
          (initializeVerdictFields workTapeCount controller regs) :=
      cmdWritesWithin_mono
        (initializeVerdictFields_writesWithin_internal
          workTapeCount controller regs)
        (fun _ haddress =>
          Finset.mem_union_left _
            (ChildNode.priorAssemblyFootprint_subset_layout
              regs haddress))
    have honeFinal :
        final controller.one = store controller.one := by
      simpa [SearchProgram.Registers.one,
        SearchProgram.Registers.primeRegisters,
        SearchProgram.Registers.primeSlot] using
          NeighborhoodTrial.Registers.runs_preserves_controller_index
            regs hwrites hrun (14 : Fin 17)
            (by decide) (by decide) (by decide)
    have hguessFinal :
        final controller.guess = store controller.guess :=
      NeighborhoodTrial.Registers.runs_preserves_controller_index
        regs hwrites hrun (2 : Fin 17)
        (by decide) (by decide) (by decide)
    refine
      ⟨final, hrun, ?_, ?_, ?_, honeFinal.trans hone,
        hguessFinal⟩
    · simp [final, selected, tested, requested, taped,
        Basic.exec, Function.update_of_ne,
        ControlDecode.nodeTape, ControlDecode.nodePayload1,
        ControlDecode.first, ControlDecode.third,
        ChildNode.priorMap, ChildNode.movementDivision,
        ChildNode.movementMap, regs.injective.eq_iff]
    · simp [final, selected, Basic.exec, ChildNode.priorMap,
        ControlDecode.nodePayload1, ControlDecode.third,
        regs.injective.eq_iff, blockIndex, hlength]
    · simp [final, selected, tested, requested, taped,
        Basic.exec, Layout.horizon,
        ControlDecode.nodePayload1, ControlDecode.third,
        ChildNode.priorMap, ChildNode.movementDivision,
        ChildNode.movementMap, regs.injective.eq_iff,
        hparameters.horizon_eq]
  · have htestNonzero :
        tested (ChildNode.movementDivision regs).test ≠ 0 := by
      have hpositive := instanceData.positive
      rw [htestedValue]
      omega
    have hselect :
        Runs
          (.ifZero (ChildNode.movementDivision regs).test
            (.basic (.imm (ChildNode.requestedBlock regs) 1))
            .skip)
          tested tested :=
      Runs.ifNonzero htestNonzero (Runs.skip tested)
    let final :=
      Function.update tested
        (ControlDecode.nodePayload1 regs)
        (tested (Layout.horizon regs))
    have hcopy :
        Runs
          (ControlDecode.copy
            (ControlDecode.nodePayload1 regs)
            (Layout.horizon regs))
          tested final :=
      copy_update_runs tested
        (regs.injective.ne (by decide : (11 : Fin 34) ≠ 3))
    have hrun :
        Runs
          (initializeVerdictFields workTapeCount controller regs)
          store final := by
      simpa [initializeVerdictFields, Cmd.seqList] using
        Runs.seq htaped
          (Runs.seq hrequested
            (Runs.seq htested (Runs.seq hselect hcopy)))
    have hwrites :
        Footprint.CmdWritesWithin regs.footprint
          (initializeVerdictFields workTapeCount controller regs) :=
      cmdWritesWithin_mono
        (initializeVerdictFields_writesWithin_internal
          workTapeCount controller regs)
        (fun _ haddress =>
          Finset.mem_union_left _
            (ChildNode.priorAssemblyFootprint_subset_layout
              regs haddress))
    have honeFinal :
        final controller.one = store controller.one := by
      simpa [SearchProgram.Registers.one,
        SearchProgram.Registers.primeRegisters,
        SearchProgram.Registers.primeSlot] using
          NeighborhoodTrial.Registers.runs_preserves_controller_index
            regs hwrites hrun (14 : Fin 17)
            (by decide) (by decide) (by decide)
    have hguessFinal :
        final controller.guess = store controller.guess :=
      NeighborhoodTrial.Registers.runs_preserves_controller_index
        regs hwrites hrun (2 : Fin 17)
        (by decide) (by decide) (by decide)
    have hblock :
        blockIndex instanceData.blockLength 1 = 0 := by
      have hpositive := instanceData.positive
      unfold blockIndex
      exact Nat.div_eq_of_lt (by omega)
    refine
      ⟨final, hrun, ?_, ?_, ?_, honeFinal.trans hone,
        hguessFinal⟩
    · simp [final, tested, requested, taped,
        Basic.exec, Function.update_of_ne,
        ControlDecode.nodeTape, ControlDecode.nodePayload1,
        ControlDecode.first, ControlDecode.third,
        ChildNode.priorMap, ChildNode.movementDivision,
        ChildNode.movementMap, regs.injective.eq_iff]
    · simp [final, tested, requested, taped, Basic.exec,
        ChildNode.priorMap, ControlDecode.nodePayload1,
        ControlDecode.third, ChildNode.movementDivision,
        ChildNode.movementMap, regs.injective.eq_iff, hblock]
    · simp [final, tested, requested, taped,
        Basic.exec, Layout.horizon,
        ControlDecode.nodePayload1, ControlDecode.third,
        ChildNode.priorMap, ChildNode.movementDivision,
        ChildNode.movementMap, regs.injective.eq_iff,
        hparameters.horizon_eq]

theorem installExactPrior_runs_internal
    {horizon : ℕ}
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store)
    (tape : TapeIndex workTapeCount)
    (requested : ℕ)
    (result : Option (ℕ × ℕ))
    (hfound :
      store (ChildNode.priorFound regs) =
        ChildNode.priorFoundValue (some result))
    (hinterval :
      store (ChildNode.priorInterval regs) =
        ChildNode.priorIntervalValue (some result))
    (hcenter :
      store (ChildNode.priorCenter regs) =
        ChildNode.priorCenterValue (some result))
    (htape :
      store (ControlDecode.nodeTape regs) = tape.val)
    (hrequested :
      store (ChildNode.requestedBlock regs) = requested)
    (hone :
      store (ChildNode.movementDivision regs).one = 1)
    (hcontains :
      ∀ interval center, result = some (interval, center) →
        NeighborhoodGraph.NeighborhoodContains center requested) :
    ∃ final,
      Runs (installExactPrior regs) store final ∧
      ChildNode.InstallPriorPost
        tape requested (some result) regs store final := by
  let validStore :=
    Basic.exec (.imm (ChildNode.centerValid regs) 1) store
  have hvalidRun :
      Runs
        (.basic (.imm (ChildNode.centerValid regs) 1))
        store validStore :=
    Runs.basic _ _
  have hvalid :
      validStore (ChildNode.centerValid regs) =
        ChildNode.priorValidValue (some result) := by
    simp [validStore, Basic.exec, ChildNode.priorValidValue]
  have hfound' :
      validStore (ChildNode.priorFound regs) =
        ChildNode.priorFoundValue (some result) := by
    simpa [validStore, Basic.exec, Function.update_of_ne,
      ChildNode.centerMap, ChildNode.priorMap,
      regs.injective.eq_iff] using hfound
  have hinterval' :
      validStore (ChildNode.priorInterval regs) =
        ChildNode.priorIntervalValue (some result) := by
    simpa [validStore, Basic.exec, Function.update_of_ne,
      ChildNode.centerMap, ChildNode.priorMap,
      regs.injective.eq_iff] using hinterval
  have hcenter' :
      validStore (ChildNode.priorCenter regs) =
        ChildNode.priorCenterValue (some result) := by
    simpa [validStore, Basic.exec, Function.update_of_ne,
      ChildNode.centerMap, ChildNode.priorMap,
      regs.injective.eq_iff] using hcenter
  have htape' :
      validStore (ControlDecode.nodeTape regs) = tape.val := by
    simpa [validStore, Basic.exec, Function.update_of_ne,
      ChildNode.centerMap, ControlDecode.nodeTape,
      ControlDecode.first, regs.injective.eq_iff] using htape
  have hrequested' :
      validStore (ChildNode.requestedBlock regs) = requested := by
    simpa [validStore, Basic.exec, Function.update_of_ne,
      ChildNode.centerMap, ChildNode.priorMap,
      regs.injective.eq_iff] using hrequested
  have hone' :
      validStore (ChildNode.movementDivision regs).one = 1 := by
    simpa [validStore, Basic.exec, Function.update_of_ne,
      ChildNode.centerMap, ChildNode.movementDivision,
      ChildNode.movementMap, regs.injective.eq_iff] using hone
  obtain ⟨final, hinstall, hpost⟩ :=
    ChildNode.installPrior_runs
      (horizon := horizon)
      regs validStore tape requested (some result)
      hvalid hfound' hinterval' hcenter' htape' hrequested'
      hone' (by
        intro interval center heq
        exact hcontains interval center (Option.some.inj heq))
  have hrun :
      Runs (installExactPrior regs) store final := by
    simpa [installExactPrior] using
      Runs.seq hvalidRun hinstall
  refine ⟨final, hrun, ?_⟩
  exact
    { nodeCode_eq := by
        intro horizon
        rw [hpost.nodeCode_eq (horizon := horizon)]
        simp [validStore, Basic.exec, Function.update_of_ne,
          ChildNode.centerMap, Layout.chunkRadix,
          regs.injective.eq_iff]
      codecDigit_eq := hpost.codecDigit_eq
      eq_outside := fun address haddress =>
        Footprint.runs_eq_outside
          (installExactPrior_writesWithin_internal regs)
          hrun haddress }

private theorem exactPriorLoop_runs
    (workTapeCount : ℕ)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store)
    (word tape requested count : ℕ)
    (hguess : store controller.guess = word)
    (htape : store (ControlDecode.nodeTape regs) = tape)
    (hrequested :
      store (ChildNode.requestedBlock regs) = requested)
    (hcountdown : store (ChildNode.priorCountdown regs) = count)
    (hfound : store (ChildNode.priorFound regs) = 0)
    (hinterval : store (ChildNode.priorInterval regs) = 0)
    (hpriorCenter : store (ChildNode.priorCenter regs) = 0)
    (hone : store (ChildNode.movementDivision regs).one = 1) :
    ∃ final,
      Runs
        (.whileNonzero (ChildNode.priorCountdown regs)
          (exactPriorSearchBody workTapeCount controller regs))
        store final ∧
      final (ChildNode.priorFound regs) =
        ChildNode.priorFoundValue
          (some
            (exactPriorSearchValue
              workTapeCount word tape requested count)) ∧
      final (ChildNode.priorInterval regs) =
        ChildNode.priorIntervalValue
          (some
            (exactPriorSearchValue
              workTapeCount word tape requested count)) ∧
      final (ChildNode.priorCenter regs) =
        ChildNode.priorCenterValue
          (some
            (exactPriorSearchValue
              workTapeCount word tape requested count)) ∧
      final (ChildNode.priorCountdown regs) = 0 ∧
      final (ChildNode.movementDivision regs).one = 1 ∧
      final (ControlDecode.nodeTape regs) = tape ∧
      final (ChildNode.requestedBlock regs) = requested ∧
      final controller.guess = word := by
  induction count generalizing store with
  | zero =>
      refine ⟨store, Runs.whileZero hcountdown, ?_⟩
      simp [exactPriorSearchValue, ChildNode.priorFoundValue,
        ChildNode.priorIntervalValue, ChildNode.priorCenterValue,
        hfound, hinterval, hpriorCenter, hcountdown, hone,
        htape, hrequested, hguess]
  | succ count ih =>
      have hcountdownNonzero :
          store (ChildNode.priorCountdown regs) ≠ 0 := by
        rw [hcountdown]
        omega
      let decremented :=
        (Basic.sub (ChildNode.priorCountdown regs)
          (ChildNode.priorCountdown regs)
          (ChildNode.movementDivision regs).one).exec store
      have hdecrementRun :
          Runs
            (.basic
              (.sub (ChildNode.priorCountdown regs)
                (ChildNode.priorCountdown regs)
                (ChildNode.movementDivision regs).one))
            store decremented :=
        Runs.basic _ _
      have hdecrementedCount :
          decremented (ChildNode.priorCountdown regs) = count := by
        simp [decremented, Basic.exec, hcountdown]
        change store (regs.index 17) = 1 at hone
        change count + 1 - store (regs.index 17) = count
        rw [hone]
        omega
      have hdecrementedOutside
          (address : ℕ)
          (hne : address ≠ ChildNode.priorCountdown regs) :
          decremented address = store address := by
        simp [decremented, Basic.exec,
          Function.update_of_ne, hne]
      let prepared :=
        Function.update decremented
          (ControlDecode.nodePayload1 regs)
          (decremented (ChildNode.priorCountdown regs))
      have hcopyRun :
          Runs
            (ControlDecode.copy
              (ControlDecode.nodePayload1 regs)
              (ChildNode.priorCountdown regs))
            decremented prepared := by
        exact copy_update_runs decremented
          (regs.injective.ne
            (by decide :
              (11 : Fin 34) ≠ ChildNode.priorMap 1))
      have hpreparedOutside
          (address : ℕ)
          (hnode :
            address ≠ ControlDecode.nodePayload1 regs)
          (hcount :
            address ≠ ChildNode.priorCountdown regs) :
          prepared address = store address := by
        rw [show prepared address = decremented address by
          simp [prepared, Function.update_of_ne, hnode]]
        exact hdecrementedOutside address hcount
      have hpreparedCount :
          prepared (ChildNode.priorCountdown regs) = count := by
        rw [show
          prepared (ChildNode.priorCountdown regs) =
              decremented (ChildNode.priorCountdown regs) by
          simp [prepared, regs.injective.eq_iff,
            ControlDecode.nodePayload1, ChildNode.priorMap]]
        exact hdecrementedCount
      have hpreparedCandidate :
          prepared (ControlDecode.nodePayload1 regs) = count := by
        simp [prepared, hdecrementedCount]
      have hpreparedGuess :
          prepared controller.guess = word := by
        rw [hpreparedOutside _
          (regs.index_ne_controller 11 2).symm
          (regs.index_ne_controller
            (ChildNode.priorMap 1) 2).symm]
        exact hguess
      have hpreparedTape :
          prepared (ControlDecode.nodeTape regs) = tape := by
        rw [hpreparedOutside _
          (regs.injective.ne (by decide))
          (regs.injective.ne (by decide))]
        exact htape
      have hpreparedRequested :
          prepared (ChildNode.requestedBlock regs) = requested := by
        rw [hpreparedOutside _
          (regs.injective.ne (by decide))
          (regs.injective.ne (by decide))]
        exact hrequested
      have hpreparedFound :
          prepared (ChildNode.priorFound regs) = 0 := by
        rw [hpreparedOutside _
          (regs.injective.ne (by decide))
          (regs.injective.ne (by decide))]
        exact hfound
      have hpreparedInterval :
          prepared (ChildNode.priorInterval regs) = 0 := by
        rw [hpreparedOutside _
          (regs.injective.ne (by decide))
          (regs.injective.ne (by decide))]
        exact hinterval
      have hpreparedPriorCenter :
          prepared (ChildNode.priorCenter regs) = 0 := by
        rw [hpreparedOutside _
          (regs.injective.ne (by decide))
          (regs.injective.ne (by decide))]
        exact hpriorCenter
      obtain ⟨centered, hderiveRun, hderivePost⟩ :=
        ChildNode.deriveCenter_runs
          workTapeCount controller regs prepared
          word tape count hpreparedGuess hpreparedTape
          hpreparedCandidate
      have hcenteredCount :
          centered (ChildNode.priorCountdown regs) = count := by
        rw [hderivePost.eq_outside _
          (prior_index_not_mem_center regs 1)]
        exact hpreparedCount
      have hcenteredFound :
          centered (ChildNode.priorFound regs) = 0 := by
        rw [hderivePost.eq_outside _
          (prior_index_not_mem_center regs 2)]
        exact hpreparedFound
      have hcenteredInterval :
          centered (ChildNode.priorInterval regs) = 0 := by
        rw [hderivePost.eq_outside _
          (prior_index_not_mem_center regs 3)]
        exact hpreparedInterval
      have hcenteredPriorCenter :
          centered (ChildNode.priorCenter regs) = 0 := by
        rw [hderivePost.eq_outside _
          (prior_index_not_mem_center regs 4)]
        exact hpreparedPriorCenter
      have hcenteredRequested :
          centered (ChildNode.requestedBlock regs) = requested := by
        rw [hderivePost.eq_outside _
          (prior_index_not_mem_center regs 0)]
        exact hpreparedRequested
      generalize hresult :
          ChildNode.derivedCenterValue
            workTapeCount word tape count = result
      cases result with
      | none =>
          have hcenteredInvalid :
              centered (ChildNode.centerValid regs) = 0 := by
            simpa [hresult, ChildNode.centerValidValue] using
              hderivePost.valid_eq
          have hbody :
              Runs
                (exactPriorSearchBody
                  workTapeCount controller regs)
                store centered := by
            simpa [exactPriorSearchBody, Cmd.seqList] using
              Runs.seq hdecrementRun
                (Runs.seq hcopyRun
                  (Runs.seq hderiveRun
                    (Runs.ifZero hcenteredInvalid
                      (Runs.skip centered))))
          obtain
              ⟨final, hloop, hfinalFound, hfinalInterval,
                hfinalCenter, hfinalCount, hfinalOne,
                hfinalTape, hfinalRequested, hfinalGuess⟩ :=
            ih centered hderivePost.guess_eq hderivePost.tape_eq
              hcenteredRequested hcenteredCount hcenteredFound
              hcenteredInterval hcenteredPriorCenter
              hderivePost.one_eq
          refine
            ⟨final,
              Runs.whileNonzero hcountdownNonzero hbody hloop,
              ?_⟩
          simpa [exactPriorSearchValue, hresult] using
            And.intro hfinalFound
              (And.intro hfinalInterval
                (And.intro hfinalCenter
                  (And.intro hfinalCount
                    (And.intro hfinalOne
                      (And.intro hfinalTape
                        (And.intro hfinalRequested
                          hfinalGuess))))))
      | some center =>
          have hcenteredValid :
              centered (ChildNode.centerValid regs) = 1 := by
            simpa [hresult, ChildNode.centerValidValue] using
              hderivePost.valid_eq
          have hcenteredCenter :
              centered (ChildNode.centerValue regs) = center := by
            simpa [hresult, ChildNode.centerOutputValue] using
              hderivePost.center_eq
          obtain ⟨checked, hcheckRun, hcheckPost⟩ :=
            ChildNode.recordPriorIfContains_runs
              controller regs centered center requested count count
              word tape hcenteredCenter hcenteredRequested
              hderivePost.interval_eq hcenteredCount
              hcenteredFound hcenteredInterval
              hcenteredPriorCenter hcenteredValid
              hderivePost.one_eq hderivePost.tape_eq
              hderivePost.guess_eq
          have hbody :
              Runs
                (exactPriorSearchBody
                  workTapeCount controller regs)
                store checked := by
            simpa [exactPriorSearchBody, Cmd.seqList] using
              Runs.seq hdecrementRun
                (Runs.seq hcopyRun
                  (Runs.seq hderiveRun
                    (Runs.ifNonzero (by
                      rw [hcenteredValid]
                      omega) hcheckRun)))
          by_cases hcontains :
              NeighborhoodGraph.NeighborhoodContains center requested
          · have hcheckedCount :
                checked (ChildNode.priorCountdown regs) = 0 := by
              rw [hcheckPost.countdown_eq]
              simp [hcontains]
            have hloop :
                Runs
                  (.whileNonzero (ChildNode.priorCountdown regs)
                    (exactPriorSearchBody
                      workTapeCount controller regs))
                  checked checked :=
              Runs.whileZero hcheckedCount
            refine
              ⟨checked,
                Runs.whileNonzero hcountdownNonzero hbody hloop,
                ?_⟩
            simp [exactPriorSearchValue, hresult, hcontains,
              ChildNode.priorFoundValue,
              ChildNode.priorIntervalValue,
              ChildNode.priorCenterValue,
              hcheckPost.found_eq, hcheckPost.interval_eq,
              hcheckPost.priorCenter_eq,
              hcheckPost.countdown_eq, hcheckPost.one_eq,
              hcheckPost.tape_eq, hcheckPost.requested_eq,
              hcheckPost.guess_eq]
          · have hcheckedCount :
                checked (ChildNode.priorCountdown regs) = count := by
              rw [hcheckPost.countdown_eq]
              simp [hcontains]
            have hcheckedFound :
                checked (ChildNode.priorFound regs) = 0 := by
              rw [hcheckPost.found_eq]
              simp [hcontains]
            have hcheckedInterval :
                checked (ChildNode.priorInterval regs) = 0 := by
              rw [hcheckPost.interval_eq]
              simp [hcontains]
            have hcheckedPriorCenter :
                checked (ChildNode.priorCenter regs) = 0 := by
              rw [hcheckPost.priorCenter_eq]
              simp [hcontains]
            obtain
                ⟨final, hloop, hfinalFound, hfinalInterval,
                  hfinalCenter, hfinalCount, hfinalOne,
                  hfinalTape, hfinalRequested, hfinalGuess⟩ :=
              ih checked hcheckPost.guess_eq hcheckPost.tape_eq
                hcheckPost.requested_eq hcheckedCount
                hcheckedFound hcheckedInterval
                hcheckedPriorCenter hcheckPost.one_eq
            refine
              ⟨final,
                Runs.whileNonzero hcountdownNonzero hbody hloop,
                ?_⟩
            simpa [exactPriorSearchValue, hresult, hcontains] using
              And.intro hfinalFound
                (And.intro hfinalInterval
                  (And.intro hfinalCenter
                    (And.intro hfinalCount
                      (And.intro hfinalOne
                        (And.intro hfinalTape
                          (And.intro hfinalRequested
                            hfinalGuess))))))

theorem scanExactPrior_runs_internal
    (workTapeCount : ℕ)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store) (word tape requested interval : ℕ)
    (hguess : store controller.guess = word)
    (htape : store (ControlDecode.nodeTape regs) = tape)
    (hrequested :
      store (ChildNode.requestedBlock regs) = requested)
    (hinterval :
      store (ControlDecode.nodePayload1 regs) = interval) :
    ∃ final,
      Runs (scanExactPrior workTapeCount controller regs) store final ∧
      ScanExactPriorPost workTapeCount word tape requested interval
        controller regs store final := by
  let operations : List Basic :=
    [.imm (ChildNode.movementDivision regs).one 1,
      .imm (ChildNode.priorFound regs) 0,
      .imm (ChildNode.priorInterval regs) 0,
      .imm (ChildNode.priorCenter regs) 0]
  let initialized := Basic.execList operations store
  have hinitializeRun :
      Runs (Cmd.basics operations) store initialized :=
    basics_runs operations store
  let counted :=
    Function.update initialized (ChildNode.priorCountdown regs)
      (initialized (ControlDecode.nodePayload1 regs))
  have hcopyRun :
      Runs
        (ControlDecode.copy
          (ChildNode.priorCountdown regs)
          (ControlDecode.nodePayload1 regs))
        initialized counted := by
    exact copy_update_runs initialized
      (regs.injective.ne
        (by decide :
          ChildNode.priorMap 1 ≠ (11 : Fin 34)))
  have hcountedCount :
      counted (ChildNode.priorCountdown regs) = interval := by
    simp [counted, initialized, operations, Basic.execList,
      Basic.exec, ChildNode.movementDivision,
      ChildNode.movementMap, ChildNode.priorMap,
      ControlDecode.nodePayload1, regs.injective.eq_iff,
      hinterval]
  have hcountedFound :
      counted (ChildNode.priorFound regs) = 0 := by
    simp [counted, initialized, operations, Basic.execList,
      Basic.exec, ChildNode.movementDivision,
      ChildNode.movementMap, ChildNode.priorMap,
      regs.injective.eq_iff]
  have hcountedInterval :
      counted (ChildNode.priorInterval regs) = 0 := by
    simp [counted, initialized, operations, Basic.execList,
      Basic.exec, ChildNode.movementDivision,
      ChildNode.movementMap, ChildNode.priorMap,
      regs.injective.eq_iff]
  have hcountedPriorCenter :
      counted (ChildNode.priorCenter regs) = 0 := by
    simp [counted, initialized, operations, Basic.execList,
      Basic.exec, ChildNode.movementDivision,
      ChildNode.movementMap, ChildNode.priorMap,
      regs.injective.eq_iff]
  have hcountedOne :
      counted (ChildNode.movementDivision regs).one = 1 := by
    simp [counted, initialized, operations, Basic.execList,
      Basic.exec, ChildNode.movementDivision,
      ChildNode.movementMap, ChildNode.priorMap,
      regs.injective.eq_iff]
  have hcountedTape :
      counted (ControlDecode.nodeTape regs) = tape := by
    simp [counted, initialized, operations, Basic.execList,
      Basic.exec, ChildNode.movementDivision,
      ChildNode.movementMap, ChildNode.priorMap,
      ControlDecode.nodeTape, ControlDecode.first,
      regs.injective.eq_iff, htape]
  have hcountedRequested :
      counted (ChildNode.requestedBlock regs) = requested := by
    simp [counted, initialized, operations, Basic.execList,
      Basic.exec, ChildNode.movementDivision,
      ChildNode.movementMap, ChildNode.priorMap,
      regs.injective.eq_iff, hrequested]
  have hinitializedGuess :
      initialized controller.guess = word := by
    simp [initialized, operations, Basic.execList, Basic.exec,
      ChildNode.movementDivision, ChildNode.movementMap,
      ControlDecode.DivisionRegisters.one,
      Function.update_of_ne,
      (regs.index_ne_controller (17 : Fin 34) 2).symm,
      (regs.index_ne_controller
        (ChildNode.priorMap 2) 2).symm,
      (regs.index_ne_controller
        (ChildNode.priorMap 3) 2).symm,
      (regs.index_ne_controller
        (ChildNode.priorMap 4) 2).symm]
    exact hguess
  have hcountedGuess :
      counted controller.guess = word := by
    simp [counted, Function.update_of_ne,
      (regs.index_ne_controller
        (ChildNode.priorMap 1) 2).symm,
      hinitializedGuess]
  obtain
      ⟨final, hloopRun, hfinalFound, hfinalInterval,
        hfinalCenter, hfinalCount, hfinalOne, hfinalTape,
        hfinalRequested, hfinalGuess⟩ :=
    exactPriorLoop_runs workTapeCount controller regs counted
      word tape requested interval hcountedGuess hcountedTape
      hcountedRequested hcountedCount hcountedFound
      hcountedInterval hcountedPriorCenter hcountedOne
  have hrun :
      Runs (scanExactPrior workTapeCount controller regs)
        store final := by
    simpa [scanExactPrior, operations] using
      Runs.seq hinitializeRun (Runs.seq hcopyRun hloopRun)
  refine ⟨final, hrun, ?_⟩
  exact
    { found_eq := hfinalFound
      interval_eq := hfinalInterval
      center_eq := hfinalCenter
      countdown_eq := hfinalCount
      one_eq := hfinalOne
      tape_eq := hfinalTape
      requested_eq := hfinalRequested
      guess_eq := hfinalGuess
      eq_outside := fun address haddress =>
        Footprint.runs_eq_outside
          (scanExactPrior_writesWithin_internal
            workTapeCount controller regs)
          hrun haddress }

theorem buildVerdictRoot_runs_internal
    {tm : TM workTapeCount}
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (code :
      Fin
        (3 ^
          NeighborhoodGraph.Guess.Enumeration.movementCount
            workTapeCount instanceData.horizon))
    (store : Store)
    (hparameters :
      Representation.Parameters regs instanceData store)
    (hone : store controller.one = 1)
    (hstoreGuess : store controller.guess = code.val)
    (hguess :
      instanceData.guess =
        NeighborhoodGraph.Guess.Enumeration.candidateGuess code) :
    ∃ final,
      Runs
        (buildVerdictRoot workTapeCount controller regs)
        store final ∧
      Representation.Parameters regs instanceData final ∧
      final (Layout.nodeCode regs) =
        FrameCodec.encodeNode
          (Representation.digitBase instanceData)
          (NeighborhoodEvaluator.verdictRoot
            instanceData.guess instanceData.blockLength) ∧
      final controller.one = 1 ∧
      final controller.guess = code.val ∧
      ∀ address,
        address ∉ ChildNode.priorAssemblyFootprint regs →
          final address = store address := by
  obtain
      ⟨fields, hfieldsRun, hfieldsTape, hfieldsRequested,
        hfieldsInterval, hfieldsOne, hfieldsGuessStore⟩ :=
    initializeVerdictFields_runs_internal
      controller regs instanceData store hparameters hone
  have hfieldsGuess : fields controller.guess = code.val :=
    hfieldsGuessStore.trans hstoreGuess
  have hfieldsParameters :
      Representation.Parameters regs instanceData fields :=
    parameters_of_priorAssembly_run
      regs instanceData store fields hparameters
      (initializeVerdictFields_writesWithin_internal
        workTapeCount controller regs)
      hfieldsRun
  obtain ⟨scanned, hscanRun, hscanPost⟩ :=
    scanExactPrior_runs_internal
      workTapeCount controller regs fields code.val
      (TapeIndex.output workTapeCount).val
      (blockIndex instanceData.blockLength 1)
      instanceData.horizon hfieldsGuess hfieldsTape
      hfieldsRequested hfieldsInterval
  have hscannedParameters :
      Representation.Parameters regs instanceData scanned :=
    parameters_of_priorAssembly_run
      regs instanceData fields scanned hfieldsParameters
      (cmdWritesWithin_mono
        (scanExactPrior_writesWithin_internal
          workTapeCount controller regs)
        (priorFootprint_subset_assembly regs))
      hscanRun
  let result :=
    exactPriorSearchValue
      workTapeCount code.val
      (TapeIndex.output workTapeCount).val
      (blockIndex instanceData.blockLength 1)
      instanceData.horizon
  obtain ⟨final, hinstallRun, hinstallPost⟩ :=
    installExactPrior_runs_internal
      (horizon := instanceData.horizon)
      regs scanned (TapeIndex.output workTapeCount)
      (blockIndex instanceData.blockLength 1) result
      hscanPost.found_eq hscanPost.interval_eq
      hscanPost.center_eq hscanPost.tape_eq
      hscanPost.requested_eq hscanPost.one_eq
      (by
        intro interval center heq
        exact exactPriorSearchValue_contains_internal
          workTapeCount code.val
          (TapeIndex.output workTapeCount).val
          (blockIndex instanceData.blockLength 1)
          instanceData.horizon interval center heq)
  have hrun :
      Runs
        (buildVerdictRoot workTapeCount controller regs)
        store final := by
    simpa [buildVerdictRoot, Cmd.seqList] using
      Runs.seq hfieldsRun (Runs.seq hscanRun hinstallRun)
  have hfinalParameters :
      Representation.Parameters regs instanceData final :=
    parameters_of_priorAssembly_run
      regs instanceData store final hparameters
      (buildVerdictRoot_writesWithin_internal
        workTapeCount controller regs)
      hrun
  have hwrites :
      Footprint.CmdWritesWithin regs.footprint
        (buildVerdictRoot workTapeCount controller regs) :=
    cmdWritesWithin_mono
      (buildVerdictRoot_writesWithin_internal
        workTapeCount controller regs)
      (fun _ haddress =>
        Finset.mem_union_left _
          (ChildNode.priorAssemblyFootprint_subset_layout
            regs haddress))
  have honeFinal :
      final controller.one = store controller.one := by
    simpa [SearchProgram.Registers.one,
      SearchProgram.Registers.primeRegisters,
      SearchProgram.Registers.primeSlot] using
        NeighborhoodTrial.Registers.runs_preserves_controller_index
          regs hwrites hrun (14 : Fin 17)
          (by decide) (by decide) (by decide)
  have hguessFinal :
      final controller.guess = store controller.guess :=
    NeighborhoodTrial.Registers.runs_preserves_controller_index
      regs hwrites hrun (2 : Fin 17)
      (by decide) (by decide) (by decide)
  refine
    ⟨final, hrun, hfinalParameters, ?_,
      honeFinal.trans hone, hguessFinal.trans hstoreGuess, ?_⟩
  · calc
      final (Layout.nodeCode regs) =
          FrameCodec.encodeNode
            (scanned (Layout.chunkRadix regs))
            (ChildNode.priorQueryValue
              (horizon := instanceData.horizon)
              (TapeIndex.output workTapeCount)
              (blockIndex instanceData.blockLength 1)
              (some result)) :=
        hinstallPost.nodeCode_eq
          (horizon := instanceData.horizon)
      _ =
          FrameCodec.encodeNode
            (Representation.digitBase instanceData)
            (NeighborhoodEvaluator.latestBlockRoot
              (NeighborhoodGraph.Guess.Enumeration.candidateGuess code)
              (TapeIndex.output workTapeCount)
              (blockIndex instanceData.blockLength 1)) := by
        rw [hscannedParameters.digitBase_eq]
        congr 1
        simpa [result] using
          exactPriorQueryValue_candidateGuess_internal
            code (TapeIndex.output workTapeCount)
            (blockIndex instanceData.blockLength 1)
      _ =
          FrameCodec.encodeNode
            (Representation.digitBase instanceData)
            (NeighborhoodEvaluator.verdictRoot
              instanceData.guess instanceData.blockLength) := by
        rw [hguess]
        rfl
  · intro address haddress
    exact Footprint.runs_eq_outside
      (buildVerdictRoot_writesWithin_internal
        workTapeCount controller regs)
      hrun haddress

theorem reinitializeVerdictQuery_runs_internal
    {tm : TM workTapeCount}
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (state : NeighborhoodScheduler.State tm instanceData)
    (code :
      Fin
        (3 ^
          NeighborhoodGraph.Guess.Enumeration.movementCount
            workTapeCount instanceData.horizon))
    (store : Store)
    (hquery :
      Representation.QueryState regs instanceData state store)
    (hone : store controller.one = 1)
    (hstoreGuess : store controller.guess = code.val)
    (hguess :
      instanceData.guess =
        NeighborhoodGraph.Guess.Enumeration.candidateGuess code) :
    ∃ final,
      Runs
        (reinitializeVerdictQuery workTapeCount controller regs)
        store final ∧
      Representation.QueryState regs instanceData
        (NeighborhoodScheduler.State.initial
          instanceData.horizon
          (NeighborhoodEvaluator.verdictRoot
            instanceData.guess instanceData.blockLength)
          1 (verdictOut workTapeCount) state.registers)
        final ∧
      final controller.one = 1 := by
  obtain
      ⟨rooted, hrootRun, hrootParameters, hrootCode,
        _hrootOne, _hrootGuess, hrootOutside⟩ :=
    buildVerdictRoot_runs_internal
      controller regs instanceData code store
      hquery.parameters hone hstoreGuess hguess
  have hrootBankEq :
      rooted regs.layout.bank = store regs.layout.bank :=
    hrootOutside regs.layout.bank
      (retained_not_mem_priorAssembly regs).2.2.2.2.2.2.2.2.2
  have hrootBank :
      NeighborhoodProgram.RepresentsResidueBank
        tm instanceData.blockLength
        (Representation.fieldBase instanceData)
        (rooted regs.layout.bank) state.registers := by
    rw [hrootBankEq]
    exact hquery.bank
  have hrootBankLt :
      rooted regs.layout.bank <
        Representation.fieldBase instanceData ^
          ((graphFanIn workTapeCount + 1) *
            TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
              (payloadWidth tm instanceData.blockLength)
              (graphFanIn workTapeCount)) := by
    rw [hrootBankEq]
    exact hquery.bank_lt
  obtain ⟨final, hreinitializeRun, hqueryFinal⟩ :=
    QueryReinitialization.reinitialize_from_bank_runs
      regs instanceData state.registers
      (NeighborhoodEvaluator.verdictRoot
        instanceData.guess instanceData.blockLength)
      (verdictOut workTapeCount) rooted
      hrootParameters hrootBank hrootBankLt hrootCode
      (NeighborhoodScheduler.FrameBounds.queryBound_verdictRoot
        instanceData)
  have hrun :
      Runs
        (reinitializeVerdictQuery workTapeCount controller regs)
        store final := by
    simpa [reinitializeVerdictQuery] using
      Runs.seq hrootRun hreinitializeRun
  have hwrites :
      Footprint.CmdWritesWithin regs.footprint
        (reinitializeVerdictQuery workTapeCount controller regs) :=
    cmdWritesWithin_mono
      (reinitializeVerdictQuery_writesWithin_internal
        workTapeCount controller regs)
      (fun _ haddress => Finset.mem_union_left _ haddress)
  have honeFinal :
      final controller.one = store controller.one := by
    simpa [SearchProgram.Registers.one,
      SearchProgram.Registers.primeRegisters,
      SearchProgram.Registers.primeSlot] using
        NeighborhoodTrial.Registers.runs_preserves_controller_index
          regs hwrites hrun (14 : Fin 17)
          (by decide) (by decide) (by decide)
  exact
    ⟨final, hrun, hqueryFinal, honeFinal.trans hone⟩

theorem reinitializeVerdictQuery_runs_preserving_abi_internal
    {tm : TM workTapeCount}
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (state : NeighborhoodScheduler.State tm instanceData)
    (code :
      Fin
        (3 ^
          NeighborhoodGraph.Guess.Enumeration.movementCount
            workTapeCount instanceData.horizon))
    (store : Store)
    (hquery :
      Representation.QueryState regs instanceData state store)
    (hone : store controller.one = 1)
    (hstoreGuess : store controller.guess = code.val)
    (hguess :
      instanceData.guess =
        NeighborhoodGraph.Guess.Enumeration.candidateGuess code)
    (hframe :
      SearchProgram.InputFrame
        controller regs.footprint instanceData.x store)
    (hinputLength :
      store controller.inputLength = instanceData.x.length) :
    ∃ final,
      Runs
        (reinitializeVerdictQuery workTapeCount controller regs)
        store final ∧
      Representation.QueryState regs instanceData
        (NeighborhoodScheduler.State.initial
          instanceData.horizon
          (NeighborhoodEvaluator.verdictRoot
            instanceData.guess instanceData.blockLength)
          1 (verdictOut workTapeCount) state.registers)
        final ∧
      SearchProgram.InputFrame
        controller regs.footprint instanceData.x final ∧
      final controller.inputLength = instanceData.x.length ∧
      final controller.one = 1 ∧
      final controller.guess = code.val := by
  obtain ⟨final, hrun, hqueryFinal, honeFinal⟩ :=
    reinitializeVerdictQuery_runs_internal
      controller regs instanceData state code store hquery
      hone hstoreGuess hguess
  have hwrites :
      Footprint.CmdWritesWithin regs.footprint
        (reinitializeVerdictQuery workTapeCount controller regs) :=
    cmdWritesWithin_mono
      (reinitializeVerdictQuery_writesWithin_internal
        workTapeCount controller regs)
      (fun _ haddress => Finset.mem_union_left _ haddress)
  have hinputLengthFinal :
      final controller.inputLength =
        store controller.inputLength :=
    NeighborhoodTrial.Registers.runs_preserves_controller_index
      regs hwrites hrun (0 : Fin 17)
      (by decide) (by decide) (by decide)
  have hguessFinal :
      final controller.guess = store controller.guess :=
    NeighborhoodTrial.Registers.runs_preserves_controller_index
      regs hwrites hrun (2 : Fin 17)
      (by decide) (by decide) (by decide)
  exact
    ⟨final, hrun, hqueryFinal,
      NeighborhoodTrial.Registers.runs_preserves_inputFrame
        regs hwrites hrun hframe,
      hinputLengthFinal.trans hinputLength,
      honeFinal,
      hguessFinal.trans hstoreGuess⟩

end Internal
end VerdictRootInitialization
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
