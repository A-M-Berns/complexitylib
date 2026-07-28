/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.CertifiedSearch
import Complexitylib.TimeSpaceSimulation.CertifiedSearch.Asymptotics
import Complexitylib.TimeSpaceSimulation.CertifiedTrial
import
  Complexitylib.TimeSpaceSimulation.NeighborhoodGraph.DecisionRecovery
import
  Complexitylib.TimeSpaceSimulation.NeighborhoodGraph.Guess.Consistency
import
  Complexitylib.TimeSpaceSimulation.NeighborhoodGraph.Guess.Enumeration
import
  Complexitylib.TimeSpaceSimulation.Runtime.CertifiedOutcome.Defs
import Complexitylib.TimeSpaceSimulation.Runtime.SearchEnvelope

/-!
# Per-guess certified-search outcome — proof internals
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace Runtime

namespace CertifiedOutcome

open NeighborhoodGraph
open NeighborhoodGraph.Guess

namespace Internal

theorem guessCount_bitlen_le_guessBits_internal
    (workTapeCount candidate : ℕ) :
    RAM.bitlen (guessCount workTapeCount candidate) ≤
      WorkspaceAccounting.guessBits workTapeCount candidate := by
  let movementCount :=
    Enumeration.movementCount workTapeCount (horizon candidate)
  have hpow :
      3 ^ movementCount < 2 ^ (2 * movementCount + 1) := by
    calc
      3 ^ movementCount ≤ 4 ^ movementCount :=
        pow_le_pow_left₀ (by omega) (by omega) movementCount
      _ = 2 ^ (2 * movementCount) := by
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
      _ < 2 ^ (2 * movementCount + 1) := by
        rw [pow_succ]
        have hpositive : 0 < 2 ^ (2 * movementCount) := by
          positivity
        omega
  rw [RAM.bitlen, Nat.size_le]
  simpa [guessCount, Search.guessCount, movementCount,
    Enumeration.movementCount, WorkspaceAccounting.guessBits,
    mul_assoc] using
    hpow

theorem actualGuessCode_lt_internal
    (tm : TM workTapeCount) (input : List Bool)
    (candidate : ℕ) :
    actualGuessCode tm input candidate <
      guessCount workTapeCount candidate := by
  change
    (Enumeration.encodeMovementCode
      (actualCenterGuess tm input
        (blockLength candidate) (horizon candidate))).val <
      Search.guessCount workTapeCount (horizon candidate)
  simp [Search.guessCount]

theorem decodedGuess_actual_internal
    (tm : TM workTapeCount) (input : List Bool)
    (candidate : ℕ)
    (hcode :
      actualGuessCode tm input candidate <
        guessCount workTapeCount candidate) :
    decodedGuess workTapeCount candidate
        (actualGuessCode tm input candidate) hcode =
      actualCenterGuess tm input
        (blockLength candidate) (horizon candidate) := by
  let actual :=
    actualCenterGuess tm input
      (blockLength candidate) (horizon candidate)
  have hfin :
      Fin.cast
          (by simp [guessCount, Search.guessCount])
          (⟨actualGuessCode tm input candidate, hcode⟩ :
            Fin (guessCount workTapeCount candidate)) =
        Enumeration.encodeMovementCode actual := by
    apply Fin.ext
    rfl
  rw [decodedGuess, hfin]
  exact Enumeration.actualCenterGuess_enumerated
    tm input (blockLength candidate) (horizon candidate)

private theorem halted_frozen_eq_decider
    (tm : TM workTapeCount) (input : List Bool)
    (time : ℕ) (cfg : Cfg workTapeCount tm.Q)
    (haltTime : ℕ)
    (hreach : tm.reachesIn haltTime (tm.initCfg input) cfg)
    (hhalt : tm.halted cfg)
    (hfrozen :
      tm.halted (tm.configurationAt input time)) :
    tm.configurationAt input time = cfg := by
  obtain ⟨frozenTime, hfrozenReach⟩ :=
    tm.reaches_to_reachesIn
      (tm.configurationAt_reaches input time)
  have hfrozenLe :
      frozenTime ≤ haltTime :=
    tm.reachesIn_le_halt hfrozenReach hreach hhalt
  have hhaltLe :
      haltTime ≤ frozenTime :=
    tm.reachesIn_le_halt hreach hfrozenReach hfrozen
  have hfirst :
      tm.configurationAt input frozenTime =
        tm.configurationAt input time :=
    tm.configurationAt_of_reachesIn
      hfrozenReach hfrozen (le_refl frozenTime)
  have hsecond :
      tm.configurationAt input frozenTime = cfg :=
    tm.configurationAt_of_reachesIn
      hreach hhalt (by omega)
  exact hfirst.symm.trans hsecond

private theorem snapshot_decode_sound
    (tm : TM workTapeCount) (L : Language)
    (actualTime : ℕ → ℕ)
    (hdecides : tm.DecidesInTime L actualTime)
    (input : List Bool) (candidate : ℕ)
    {answer : Bool}
    (hstate :
      (DecisionRecovery.decisionSnapshot tm input
        (blockLength candidate)
        (WorkspaceAccounting.blockLength_pos candidate)
        (horizon candidate)).state = tm.qhalt)
    (hdecode :
      CertifiedTrial.decodeVerdict
        (DecisionRecovery.decisionSnapshot tm input
          (blockLength candidate)
          (WorkspaceAccounting.blockLength_pos candidate)
          (horizon candidate)).verdict =
        some answer) :
    (answer = true → input ∈ L) ∧
      (answer = false → input ∉ L) := by
  have hfrozen :
      tm.halted
        (tm.configurationAt input
          (timeBlockStart
            (blockLength candidate) (horizon candidate))) := by
    simpa [TM.halted, Cfg.isHalted,
      DecisionRecovery.decisionSnapshot_state
        tm input (blockLength candidate)
          (horizon candidate)
          (WorkspaceAccounting.blockLength_pos candidate)] using
      hstate
  obtain ⟨cfg, haltTime, _htime, hreach, hhalt,
      hmember, hnotMember⟩ :=
    hdecides input
  have hcfg :
      tm.configurationAt input
          (timeBlockStart
            (blockLength candidate) (horizon candidate)) =
        cfg :=
    halted_frozen_eq_decider tm input
      (timeBlockStart
        (blockLength candidate) (horizon candidate))
      cfg haltTime hreach hhalt hfrozen
  have hverdict :
      (DecisionRecovery.decisionSnapshot tm input
        (blockLength candidate)
        (WorkspaceAccounting.blockLength_pos candidate)
        (horizon candidate)).verdict =
          cfg.output.cells 1 := by
    rw [DecisionRecovery.decisionSnapshot_verdict, hcfg]
  constructor
  · intro hanswer
    subst answer
    have hone :=
      (CertifiedTrial.decodeVerdict_eq_some_true_iff _).1
        hdecode
    by_contra hnot
    have hzero := hnotMember hnot
    rw [hverdict, hzero] at hone
    simp at hone
  · intro hanswer
    subst answer
    have hzero :=
      (CertifiedTrial.decodeVerdict_eq_some_false_iff _).1
        hdecode
    intro hmem
    have hone := hmember hmem
    rw [hverdict, hone] at hzero
    simp at hzero

theorem outcome_sound_internal
    (tm : TM workTapeCount) (L : Language)
    (actualTime : ℕ → ℕ)
    (hdecides : tm.DecidesInTime L actualTime)
    (family : CertifiedSearch.EngineFamily tm)
    (input : List Bool) (candidate prime code : ℕ)
    {answer : Bool}
    (hrun :
      outcome tm family input candidate prime code =
        some answer) :
    (answer = true → input ∈ L) ∧
      (answer = false → input ∉ L) := by
  unfold outcome at hrun
  split at hrun
  · rename_i hcode
    let engine := family.engine input candidate
    let guess :=
      decodedGuess workTapeCount candidate code hcode
    change
      (match Consistency.passes tm input
          (blockLength candidate)
          (EvaluatedProvider.provider engine.node) guess with
      | false => none
      | true =>
          match engine.snapshot guess with
          | none => none
          | some snapshot =>
              if snapshot.state = tm.qhalt then
                CertifiedTrial.decodeVerdict snapshot.verdict
              else
                none) = some answer at hrun
    cases hpasses :
        Consistency.passes tm input (blockLength candidate)
          (EvaluatedProvider.provider engine.node) guess with
    | false =>
        simp [hpasses] at hrun
    | true =>
        have hexact := family.exact input candidate
        have hprovider :
            Consistency.IsExactProvider tm input
              (blockLength candidate)
              (WorkspaceAccounting.blockLength_pos candidate)
              (EvaluatedProvider.provider engine.node) :=
          hexact.1.isExactProvider
        have hvalid :
            guess.IsValidFor
              (actualCenterTrajectory tm input
                (blockLength candidate)) :=
          Consistency.passes_implies_valid tm input
            (blockLength candidate) (horizon candidate)
            (WorkspaceAccounting.blockLength_pos candidate)
            (EvaluatedProvider.provider engine.node)
            hprovider guess hpasses
        have hsnapshot := hexact.2 guess hvalid
        rw [hpasses, hsnapshot] at hrun
        change
          (if
              (DecisionRecovery.decisionSnapshot tm input
                (blockLength candidate)
                (WorkspaceAccounting.blockLength_pos candidate)
                (horizon candidate)).state = tm.qhalt then
            CertifiedTrial.decodeVerdict
              (DecisionRecovery.decisionSnapshot tm input
                (blockLength candidate)
                (WorkspaceAccounting.blockLength_pos candidate)
                (horizon candidate)).verdict
          else none) = some answer at hrun
        by_cases hstate :
            (DecisionRecovery.decisionSnapshot tm input
              (blockLength candidate)
              (WorkspaceAccounting.blockLength_pos candidate)
              (horizon candidate)).state = tm.qhalt
        · rw [if_pos hstate] at hrun
          exact snapshot_decode_sound tm L actualTime hdecides
            input candidate hstate hrun
        · rw [if_neg hstate] at hrun
          contradiction
  · simp at hrun

theorem actualGuessCode_returns_internal
    (tm : TM workTapeCount) (L : Language)
    (actualTime : ℕ → ℕ)
    (hdecides : tm.DecidesInTime L actualTime)
    (family : CertifiedSearch.EngineFamily tm)
    (input : List Bool) (candidate prime : ℕ)
    (hcover : actualTime input.length ≤ candidate) :
    ∃ answer,
      outcome tm family input candidate prime
          (actualGuessCode tm input candidate) =
        some answer ∧
      (answer = true → input ∈ L) ∧
      (answer = false → input ∉ L) := by
  let engine := family.engine input candidate
  let actual :=
    actualCenterGuess tm input
      (blockLength candidate) (horizon candidate)
  have hpositive :
      0 < blockLength candidate :=
    WorkspaceAccounting.blockLength_pos candidate
  have hexact := family.exact input candidate
  have hprovider :
      Consistency.IsExactProvider tm input
        (blockLength candidate) hpositive
        (EvaluatedProvider.provider engine.node) :=
    hexact.1.isExactProvider
  have hpasses :
      Consistency.passes tm input (blockLength candidate)
        (EvaluatedProvider.provider engine.node) actual = true :=
    Consistency.actualCenterGuess_passes tm input
      (blockLength candidate) (horizon candidate) hpositive
      (EvaluatedProvider.provider engine.node) hprovider
  have hvalid :
      actual.IsValidFor
        (actualCenterTrajectory tm input
          (blockLength candidate)) :=
    actualCenterGuess_isValidFor tm input
      (blockLength candidate) (horizon candidate) hpositive
  have hsnapshot := hexact.2 actual hvalid
  obtain ⟨cfg, haltTime, htime, hreach, hhalt,
      hmember, hnotMember⟩ :=
    hdecides input
  have hhorizon :
      candidate ≤
        timeBlockStart
          (blockLength candidate) (horizon candidate) := by
    exact CertifiedSearch.candidate_le_horizon_start candidate
  have hcovered :
      haltTime ≤
        timeBlockStart
          (blockLength candidate) (horizon candidate) :=
    htime.trans (hcover.trans hhorizon)
  have hsnapshotValue :=
    DecisionRecovery.decisionSnapshot_eq_of_reachesIn
      tm input (blockLength candidate) (horizon candidate)
      haltTime hpositive cfg hreach hhalt hcovered
  have hsnapshotValue' :
      DecisionRecovery.decisionSnapshot tm input
          (WorkspaceAccounting.blockLength candidate)
          (WorkspaceAccounting.blockLength_pos candidate)
          (WorkspaceAccounting.horizon candidate) =
        { state := cfg.state, verdict := cfg.output.cells 1 } := by
    simpa [blockLength, horizon] using hsnapshotValue
  have hcode :
      actualGuessCode tm input candidate <
        guessCount workTapeCount candidate :=
    actualGuessCode_lt_internal tm input candidate
  have hdecoded :
      decodedGuess workTapeCount candidate
          (actualGuessCode tm input candidate) hcode =
        actual :=
    decodedGuess_actual_internal tm input candidate hcode
  unfold outcome
  rw [dif_pos hcode]
  dsimp only
  rw [hdecoded, hpasses, hsnapshot, hsnapshotValue']
  simp only [hhalt, if_true]
  by_cases hx : input ∈ L
  · refine ⟨true, ?_, by simp [hx]⟩
    rw [hmember hx]
    simp [CertifiedTrial.decodeVerdict]
  · refine ⟨false, ?_, by simp [hx]⟩
    rw [hnotMember hx]
    simp [CertifiedTrial.decodeVerdict]

theorem candidateReturnsAt_complete_internal
    (tm : TM workTapeCount) (L : Language)
    (actualTime : ℕ → ℕ)
    (hdecides : tm.DecidesInTime L actualTime)
    (family : CertifiedSearch.EngineFamily tm)
    (input : List Bool) (candidate prime : ℕ)
    (hcover : actualTime input.length ≤ candidate) :
    ∃ answer,
      CandidateReturnsAt tm family input candidate prime answer ∧
      (answer = true → input ∈ L) ∧
      (answer = false → input ∉ L) := by
  obtain ⟨answer, hrun, htrue, hfalse⟩ :=
    actualGuessCode_returns_internal tm L actualTime hdecides
      family input candidate prime hcover
  exact ⟨answer,
    ⟨actualGuessCode tm input candidate,
      actualGuessCode_lt_internal tm input candidate, hrun⟩,
    htrue, hfalse⟩

theorem kernel_outcome_sound_internal
    (tm : TM workTapeCount) (L : Language)
    (actualTime : ℕ → ℕ)
    (hdecides : tm.DecidesInTime L actualTime)
    (family : CertifiedSearch.EngineFamily tm)
    (kernel : SearchProgram.TrialKernel regs)
    (hrefines : KernelRefines kernel tm family)
    (input : List Bool) (candidate prime code : ℕ)
    {answer : Bool}
    (hrun :
      kernel.outcome input candidate prime code = some answer) :
    (answer = true → input ∈ L) ∧
      (answer = false → input ∉ L) := by
  apply outcome_sound_internal tm L actualTime hdecides
    family input candidate prime code
  rw [← hrefines.outcome_eq input candidate prime code]
  exact hrun

theorem kernel_candidateReturns_complete_internal
    (tm : TM workTapeCount) (L : Language)
    (actualTime : ℕ → ℕ)
    (hdecides : tm.DecidesInTime L actualTime)
    (family : CertifiedSearch.EngineFamily tm)
    (kernel : SearchProgram.TrialKernel regs)
    (hrefines : KernelRefines kernel tm family)
    (input : List Bool) (candidate : ℕ)
    (hcover : actualTime input.length ≤ candidate) :
    ∃ answer,
      SearchProgram.CandidateReturns
        kernel input candidate answer ∧
      (answer = true → input ∈ L) ∧
      (answer = false → input ∉ L) := by
  obtain ⟨answer, ⟨code, hcode, houtcome⟩,
      htrue, hfalse⟩ :=
    candidateReturnsAt_complete_internal
      tm L actualTime hdecides family input candidate
        (SearchProgram.firstPrimeAtOrAbove candidate) hcover
  refine ⟨answer, ⟨code, ?_, ?_⟩, htrue, hfalse⟩
  · rw [hrefines.guessCount_eq candidate]
    exact hcode
  · rw [hrefines.outcome_eq input candidate
      (SearchProgram.firstPrimeAtOrAbove candidate) code]
    exact houtcome

theorem kernel_eventuallySucceeds_internal
    (tm : TM workTapeCount) (L : Language)
    (actualTime : ℕ → ℕ)
    (hdecides : tm.DecidesInTime L actualTime)
    (family : CertifiedSearch.EngineFamily tm)
    (kernel : SearchProgram.TrialKernel regs)
    (hrefines : KernelRefines kernel tm family)
    (input : List Bool) :
    SearchProgram.EventuallySucceeds kernel input := by
  let candidate := max input.length (actualTime input.length)
  obtain ⟨answer, hreturns, _htrue, _hfalse⟩ :=
    kernel_candidateReturns_complete_internal
      tm L actualTime hdecides family kernel hrefines
      input candidate (by
        dsimp only [candidate]
        exact le_max_right _ _)
  exact ⟨candidate, answer, le_max_left _ _, hreturns⟩

theorem kernel_guessCount_bitlen_le_trialEnvelope_internal
    (tm : TM workTapeCount)
    (family : CertifiedSearch.EngineFamily tm)
    (kernel : SearchProgram.TrialKernel regs)
    (hrefines : KernelRefines kernel tm family)
    {candidate target : ℕ}
    (hcandidate : candidate ≤ target) :
    RAM.bitlen (kernel.guessCount candidate) ≤
      WorkspaceAccounting.trialEnvelopeBits
        tm.Q workTapeCount target := by
  rw [hrefines.guessCount_eq candidate]
  calc
    RAM.bitlen (guessCount workTapeCount candidate) ≤
        WorkspaceAccounting.guessBits workTapeCount candidate :=
      guessCount_bitlen_le_guessBits_internal
        workTapeCount candidate
    _ ≤ WorkspaceAccounting.totalBits
        tm.Q workTapeCount candidate := by
      unfold WorkspaceAccounting.totalBits
      omega
    _ ≤ WorkspaceAccounting.trialEnvelopeBits
        tm.Q workTapeCount target :=
      WorkspaceAccounting.totalBits_le_trialEnvelope
        tm.Q workTapeCount hcandidate

theorem kernel_prefixEnvelope_internal
    (tm : TM workTapeCount)
    (family : CertifiedSearch.EngineFamily tm)
    (regs : SearchProgram.Registers)
    (kernel : SearchProgram.TrialKernel regs)
    (hrefines : KernelRefines kernel tm family)
    (input : List Bool) (target : ℕ)
    (htarget : input.length ≤ target)
    (hkernelPrefix :
      ∀ candidate,
        input.length ≤ candidate →
        candidate ≤ target →
        ∀ prime guess,
          guess < kernel.guessCount candidate →
          kernel.prefixValueBits input candidate prime guess ≤
            controllerValueBits tm regs kernel target) :
    SearchProgram.PrefixEnvelope regs kernel input target
      (controllerValueBits tm regs kernel target) := by
  apply SearchEnvelope.prefixEnvelopeOfBounds
  · calc
      RAM.bitlen input.length ≤ RAM.bitlen target := by
        simpa [RAM.bitlen] using Nat.size_le_size htarget
      _ ≤ WorkspaceAccounting.trialEnvelopeBits
          tm.Q workTapeCount target :=
        WorkspaceAccounting.size_le_trialEnvelope
          tm.Q workTapeCount target
      _ ≤ NeighborhoodProgram.fixedRegisterCount *
            WorkspaceAccounting.trialEnvelopeBits
              tm.Q workTapeCount target + 2 := by
        simp only [NeighborhoodProgram.fixedRegisterCount]
        omega
      _ ≤ controllerValueBits tm regs kernel target :=
        le_max_right _ _
  · exact (le_max_left _ _).trans (le_max_left _ _)
  · calc
      RAM.bitlen target + 2 ≤
          WorkspaceAccounting.trialEnvelopeBits
              tm.Q workTapeCount target + 2 :=
        Nat.add_le_add_right
          (WorkspaceAccounting.size_le_trialEnvelope
            tm.Q workTapeCount target) 2
      _ ≤ NeighborhoodProgram.fixedRegisterCount *
            WorkspaceAccounting.trialEnvelopeBits
              tm.Q workTapeCount target + 2 := by
        simp only [NeighborhoodProgram.fixedRegisterCount]
        omega
      _ ≤ controllerValueBits tm regs kernel target := by
        exact le_max_right _ _
  · intro candidate _hlower hupper
    calc
      RAM.bitlen (kernel.guessCount candidate) ≤
          WorkspaceAccounting.trialEnvelopeBits
            tm.Q workTapeCount target :=
        kernel_guessCount_bitlen_le_trialEnvelope_internal
          tm family kernel hrefines hupper
      _ ≤ NeighborhoodProgram.fixedRegisterCount *
            WorkspaceAccounting.trialEnvelopeBits
              tm.Q workTapeCount target + 2 := by
        simp only [NeighborhoodProgram.fixedRegisterCount]
        omega
      _ ≤ controllerValueBits tm regs kernel target :=
        le_max_right _ _
  · exact hkernelPrefix

private theorem constant_isBigO_sqrtLog_internal
    (constant : ℕ) {T : ℕ → ℕ}
    (hT : ∀ n, n ≤ T n) :
    (fun _ : ℕ => constant) =O
      ComplexityBridge.sqrtLogSpace T := by
  have hconstantRounded :
      (fun _ : ℕ => constant) =O
        ComplexityBridge.roundedSqrtLogSpace T := by
    have hle :
        ∀ n,
          constant ≤
            constant *
              ComplexityBridge.roundedSqrtLogSpace T n := by
      intro n
      have hpositive :
          1 ≤ ComplexityBridge.roundedSqrtLogSpace T n := by
        exact WorkspaceAccounting.blockLength_pos (T n)
      simpa using Nat.mul_le_mul_left constant hpositive
    exact
      (BigO.of_le hle).trans
        (BigO.const_mul_left constant
          (BigO.refl
            (ComplexityBridge.roundedSqrtLogSpace T)))
  exact hconstantRounded.trans
    (ComplexityBridge.roundedSqrtLogSpace_isBigO hT)

theorem controllerValueBits_max_actualTime_isBigO_internal
    (tm : TM workTapeCount)
    (regs : SearchProgram.Registers)
    (kernel : SearchProgram.TrialKernel regs)
    {actualTime T : ℕ → ℕ}
    (htime : actualTime =O T)
    (hT : ∀ n, n ≤ T n) :
    (fun n =>
      controllerValueBits tm regs kernel
        (max n (actualTime n))) =O
      ComplexityBridge.sqrtLogSpace T := by
  let static := controllerStaticBits regs kernel
  let envelope := fun n =>
    WorkspaceAccounting.trialEnvelopeBits
      tm.Q workTapeCount (max n (actualTime n))
  have hstatic :
      (fun _ : ℕ => static) =O
        ComplexityBridge.sqrtLogSpace T :=
    constant_isBigO_sqrtLog_internal static hT
  have henvelope :
      envelope =O ComplexityBridge.sqrtLogSpace T := by
    simpa [envelope] using
      (CertifiedSearch.Asymptotics.trialEnvelopeBits_max_actualTime_isBigO
          tm.Q workTapeCount htime hT)
  have hscaledEnvelope :
      (fun n =>
        NeighborhoodProgram.fixedRegisterCount * envelope n) =O
        ComplexityBridge.sqrtLogSpace T :=
    BigO.const_mul_left
      NeighborhoodProgram.fixedRegisterCount henvelope
  have htwo :
      (fun _ : ℕ => 2) =O
        ComplexityBridge.sqrtLogSpace T :=
    constant_isBigO_sqrtLog_internal 2 hT
  have henvelopePlus :
      (fun n =>
        NeighborhoodProgram.fixedRegisterCount * envelope n + 2) =O
        ComplexityBridge.sqrtLogSpace T :=
    BigO.add hscaledEnvelope htwo
  simpa [controllerValueBits, static, envelope] using
    BigO.max_same hstatic henvelopePlus

theorem controllerTraceBits_max_actualTime_isBigO_internal
    (tm : TM workTapeCount)
    (regs : SearchProgram.Registers)
    (kernel : SearchProgram.TrialKernel regs)
    {actualTime T : ℕ → ℕ}
    (htime : actualTime =O T)
    (hT : ∀ n, n ≤ T n) :
    (fun n =>
      controllerValueBits tm regs kernel
          (max n (actualTime n)) + 1) =O
      ComplexityBridge.sqrtLogSpace T :=
  BigO.add
    (controllerValueBits_max_actualTime_isBigO_internal
      tm regs kernel htime hT)
    (constant_isBigO_sqrtLog_internal 1 hT)

theorem controller_codeSize_bitlen_le_internal
    (tm : TM workTapeCount)
    (regs : SearchProgram.Registers)
    (kernel : SearchProgram.TrialKernel regs)
    (target : ℕ) :
    RAM.bitlen (SearchProgram.program regs kernel).codeSize ≤
      controllerValueBits tm regs kernel target := by
  exact (le_max_left _ _).trans
    ((le_max_right _ _).trans (le_max_left _ _))

theorem controller_footprintCard_bitlen_le_internal
    (tm : TM workTapeCount)
    (regs : SearchProgram.Registers)
    (kernel : SearchProgram.TrialKernel regs)
    (target : ℕ) :
    RAM.bitlen (regs.footprint ∪ kernel.footprint).card ≤
      controllerValueBits tm regs kernel target := by
  exact (le_max_right _ _).trans
    ((le_max_right _ _).trans (le_max_left _ _))

private theorem bitlen_le_self_internal (value : ℕ) :
    RAM.bitlen value ≤ value := by
  rw [RAM.bitlen, Nat.size_le]
  exact Nat.lt_pow_self (by decide)

theorem controller_address_bitlen_le_internal
    (tm : TM workTapeCount)
    (regs : SearchProgram.Registers)
    (kernel : SearchProgram.TrialKernel regs)
    (target : ℕ)
    {address : ℕ}
    (haddress :
      address ∈ regs.footprint ∪ kernel.footprint) :
    RAM.bitlen address ≤
      controllerValueBits tm regs kernel target := by
  calc
    RAM.bitlen address ≤ address :=
      bitlen_le_self_internal address
    _ ≤ SearchProgram.footprintLimit regs kernel.footprint :=
      Finset.le_sup (f := fun value : ℕ => value) haddress
    _ ≤ controllerStaticBits regs kernel :=
      le_max_left _ _
    _ ≤ controllerValueBits tm regs kernel target :=
      le_max_left _ _

end Internal

end CertifiedOutcome

end Runtime

end TimeSpaceSimulation

end Complexity
