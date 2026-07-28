/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Mathlib.Tactic.FinCases
import Complexitylib.Models.RandomAccessMachine.Structured.Footprint
import Complexitylib.Models.RandomAccessMachine.Structured.Invariant
import
  Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.DenseOverlay.Footprint
import Complexitylib.TimeSpaceSimulation.Runtime.SearchProgram.Defs

/-!
# First-order Williams outer search controller — proof internals
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace Runtime

namespace SearchProgram

open RAM Structured

namespace Internal

theorem trialKernel_runs_internal
    (kernel : TrialKernel regs) (input : List Bool) (store : Store)
    (hframe : InputFrame regs kernel.footprint input store)
    (hinput : store regs.inputLength = input.length)
    (hone : store regs.one = 1)
    (hguess :
      store regs.guess <
        kernel.guessCount (store regs.candidate)) :
    ∃ final,
      Runs kernel.command store final ∧
      TrialPost regs kernel.footprint kernel.guessCount
        kernel.outcome input store final := by
  obtain ⟨final, steps, hrun, hpost⟩ :=
    kernel.prefixInvariantRuns input store hframe hinput hone hguess
  exact ⟨final, RAM.Structured.InvariantRuns.toRuns hrun, hpost⟩

private theorem exec_preserves_outside
    {allowed : Finset ℕ} {cmd : Cmd} {initial final : Store}
    {steps cost space : ℕ}
    (hwrites : RAM.Structured.Footprint.CmdWritesWithin allowed cmd)
    (hexec : Exec cmd initial final steps cost space)
    {index : ℕ} (hindex : index ∉ allowed) :
    final index = initial index := by
  induction hexec with
  | skip => rfl
  | basic op store =>
      cases op <;>
        simp only [RAM.Structured.Footprint.CmdWritesWithin,
          RAM.Structured.Footprint.BasicWritesWithin] at hwrites
      all_goals
        simp only [Basic.exec]
        rw [Function.update_of_ne]
        exact fun heq => hindex (heq ▸ hwrites)
  | seq hfirst hsecond firstIH secondIH =>
      exact (secondIH hwrites.2).trans (firstIH hwrites.1)
  | ifZero htest hbranch ih =>
      exact ih hwrites.1
  | ifNonzero htest hbranch ih =>
      exact ih hwrites.2
  | whileZero htest =>
      rfl
  | whileNonzero htest hbody hloop bodyIH loopIH =>
      exact (loopIH hwrites).trans (bodyIH hwrites)

private theorem runs_preserves_outside
    {allowed : Finset ℕ} {cmd : Cmd} {initial final : Store}
    (hwrites : RAM.Structured.Footprint.CmdWritesWithin allowed cmd)
    (hrun : Runs cmd initial final)
    {index : ℕ} (hindex : index ∉ allowed) :
    final index = initial index := by
  obtain ⟨steps, cost, space, hexec⟩ := hrun
  exact exec_preserves_outside hwrites hexec hindex

private def primeFootprint (regs : Registers) : Finset ℕ :=
  Finset.univ.image regs.primeRegisters.index

private theorem outer_not_mem_primeFootprint
    (regs : Registers) (slot : Fin 17) (hslot : slot.val < 8) :
    regs.index slot ∉ primeFootprint regs := by
  simp only [primeFootprint, Finset.mem_image, Finset.mem_univ, true_and]
  rintro ⟨upper, heq⟩
  have hslots := regs.injective heq
  have hvals := congrArg Fin.val hslots
  simp only [Registers.primeSlot] at hvals
  omega

private theorem upper_ne_outer
    (regs : Registers) (upper : Fin 8) (outer : Fin 17)
    (houter : outer.val < 8) :
    regs.primeRegisters.index upper ≠ regs.index outer := by
  exact fun heq =>
    outer_not_mem_primeFootprint regs outer houter
      (Finset.mem_image.mpr ⟨upper, Finset.mem_univ _, heq⟩)

private theorem primeSearch_writesWithin (regs : Registers) :
    RAM.Structured.Footprint.CmdWritesWithin (primeFootprint regs)
      (RAM.Structured.PrimeSearch.search regs.primeRegisters) := by
  simp [PrimeSearch.search, PrimeSearch.primality,
    PrimeSearch.primalitySetupOps, PrimeSearch.refreshSearchTest,
    PrimeSearch.searchBody, PrimeSearch.trialSetupOps,
    PrimeSearch.trialLoop, PrimeSearch.trialBody,
    PrimeSearch.decrementDivisor,
    RuntimeArithmetic.reduce, RuntimeArithmetic.reduceBody,
    RuntimeArithmetic.reduceTestOp,
    Cmd.basics, Cmd.seqList,
    RAM.Structured.Footprint.CmdWritesWithin,
    RAM.Structured.Footprint.BasicWritesWithin,
    primeFootprint, Registers.primeRegisters,
    PrimeSearch.Registers.reduceRegisters]

private theorem primeSearch_preserves_outer
    (regs : Registers) {initial final : Store}
    (hrun :
      Runs (RAM.Structured.PrimeSearch.search regs.primeRegisters)
        initial final)
    (slot : Fin 17) (hslot : slot.val < 8) :
    final (regs.index slot) = initial (regs.index slot) :=
  runs_preserves_outside (primeSearch_writesWithin regs) hrun
    (outer_not_mem_primeFootprint regs slot hslot)

private theorem prefixCache_not_mem_primeFootprint
    (regs : Registers) :
    regs.prefixCache ∉ primeFootprint regs := by
  simp only [primeFootprint, Finset.mem_image, Finset.mem_univ, true_and]
  rintro ⟨upper, heq⟩
  have hslots := regs.injective heq
  have hvals := congrArg Fin.val hslots
  simp only [Registers.primeSlot] at hvals
  omega

private theorem primeSearch_preserves_inputFrame
    (regs : Registers) (kernel : TrialKernel regs)
    (input : List Bool) {initial final : Store}
    (hframe : InputFrame regs kernel.footprint input initial)
    (hrun :
      Runs (RAM.Structured.PrimeSearch.search regs.primeRegisters)
        initial final) :
    InputFrame regs kernel.footprint input final := by
  constructor
  · exact (runs_preserves_outside
      (primeSearch_writesWithin regs) hrun
      (prefixCache_not_mem_primeFootprint regs)).trans hframe.1
  · intro address hlimit
    calc
      final address = initial address := by
        apply (runs_preserves_outside
          (primeSearch_writesWithin regs) hrun)
        intro hmember
        have hallMember :
            address ∈ regs.footprint ∪ kernel.footprint := by
          rcases Finset.mem_image.mp hmember with
            ⟨slot, _hslot, rfl⟩
          exact Finset.mem_union_left _
            (regs.index_mem_footprint (Registers.primeSlot slot))
        have hle :
            address ≤ footprintLimit regs kernel.footprint := by
          exact
            (show address ≤
              (regs.footprint ∪ kernel.footprint).sup
                (fun value : ℕ => value) from
                Finset.le_sup
                  (f := fun value : ℕ => value) hallMember)
        omega
      _ = RAM.initRegs input address :=
        hframe.2 address hlimit

theorem firstPrimeAtOrAbove_spec_internal (lower : ℕ) :
    PrimeSearch.IsFirstPrimeAtOrAbove lower
      (firstPrimeAtOrAbove lower) := by
  let hexists := Nat.exists_infinite_primes lower
  have hspec := Nat.find_spec hexists
  refine ⟨hspec.1, hspec.2, ?_⟩
  intro prior hlower hprior
  exact fun hprime =>
    Nat.find_min hexists hprior ⟨hlower, hprime⟩

private theorem firstPrime_unique
    {lower first second : ℕ}
    (hfirst : PrimeSearch.IsFirstPrimeAtOrAbove lower first)
    (hsecond : PrimeSearch.IsFirstPrimeAtOrAbove lower second) :
    first = second := by
  apply le_antisymm
  · by_contra hnot
    exact (hfirst.2.2 second hsecond.1 (Nat.lt_of_not_ge hnot))
      hsecond.2.1
  · by_contra hnot
    exact (hsecond.2.2 first hfirst.1 (Nat.lt_of_not_ge hnot))
      hfirst.2.1

theorem firstPrimeAtOrAbove_le_two_mul_internal
    (lower : ℕ) (hlower : 0 < lower) :
    firstPrimeAtOrAbove lower ≤ 2 * lower := by
  obtain ⟨prime, hprime, hlowerPrime, hprimeUpper⟩ :=
    Nat.bertrand lower (Nat.ne_of_gt hlower)
  apply le_trans (show firstPrimeAtOrAbove lower ≤ prime by
    by_contra hnot
    have hprimePrior : prime < firstPrimeAtOrAbove lower :=
      Nat.lt_of_not_ge hnot
    exact
      ((firstPrimeAtOrAbove_spec_internal lower).2.2
        prime hlowerPrime.le hprimePrior) hprime) hprimeUpper

theorem firstPrimeAtOrAbove_bitlen_le_internal
    (lower : ℕ) (hlower : 0 < lower) :
    bitlen (firstPrimeAtOrAbove lower) ≤ bitlen lower + 1 := by
  have hsize := Nat.size_le_size
    (firstPrimeAtOrAbove_le_two_mul_internal lower hlower)
  have hdouble :
      bitlen (2 * lower) = bitlen lower + 1 := by
    simpa [bitlen, Nat.shiftLeft_eq_mul_pow, Nat.mul_comm] using
      Nat.size_shiftLeft (Nat.ne_of_gt hlower) 1
  rw [← hdouble]
  simpa [bitlen] using hsize

private theorem allowed_address_le_limit
    (regs : Registers) (kernelFootprint : Finset ℕ)
    {address : ℕ}
    (haddress : address ∈ regs.footprint ∪ kernelFootprint) :
    address ≤ footprintLimit regs kernelFootprint :=
  (show address ≤
      (regs.footprint ∪ kernelFootprint).sup
        (fun value : ℕ => value) from
    Finset.le_sup (f := fun value : ℕ => value) haddress)

private theorem controller_update_inputFrame
    (regs : Registers) (kernel : TrialKernel regs)
    (input : List Bool) {store : Store}
    (hframe : InputFrame regs kernel.footprint input store)
    (slot : Fin 17) (hslot : slot ≠ 16) (value : ℕ) :
    InputFrame regs kernel.footprint input
      (Function.update store (regs.index slot) value) := by
  constructor
  · rw [Function.update_of_ne]
    · exact hframe.1
    · exact regs.index_ne (Ne.symm hslot)
  · intro address hlimit
    rw [Function.update_of_ne]
    · exact hframe.2 address hlimit
    · intro heq
      have hmember :
          regs.index slot ∈ regs.footprint ∪ kernel.footprint :=
        Finset.mem_union_left _ (regs.index_mem_footprint slot)
      have hle := allowed_address_le_limit regs kernel.footprint hmember
      omega

private theorem runs_basics (ops : List Basic) (store : Store) :
    Runs (Cmd.basics ops) store (Basic.execList ops store) := by
  obtain ⟨cost, space, hexec⟩ :=
    Structured.Internal.exec_basics_exists ops store
  exact ⟨ops.length, cost, space, hexec⟩

private theorem basics_writesWithin
    {allowed : Finset ℕ} (ops : List Basic)
    (hwrites : ∀ op ∈ ops,
      RAM.Structured.Footprint.BasicWritesWithin allowed op) :
    RAM.Structured.Footprint.CmdWritesWithin allowed
      (Cmd.basics ops) := by
  induction ops with
  | nil =>
      trivial
  | cons op rest ih =>
      cases rest with
      | nil =>
          simpa [Cmd.basics, Cmd.seqList] using
            hwrites op (by simp)
      | cons next tail =>
          have hop := hwrites op (by simp)
          have hrest :
              ∀ candidate ∈ next :: tail,
                RAM.Structured.Footprint.BasicWritesWithin
                  allowed candidate := by
            intro candidate hcandidate
            exact hwrites candidate (by simp [hcandidate])
          simpa [Cmd.basics, Cmd.seqList] using
            And.intro hop (ih hrest)

private theorem cacheInputPrefix_writesWithin
    (regs : Registers) (limit : ℕ) :
    RAM.Structured.Footprint.CmdWritesWithin
      {regs.prefixCache} (cacheInputPrefix regs limit) := by
  unfold cacheInputPrefix
  apply basics_writesWithin
  intro op hop
  simp only [cacheInputPrefixOps, List.mem_cons,
    List.mem_flatMap] at hop
  rcases hop with hop | ⟨offset, _hoffset, hop⟩
  · subst op
    simp [RAM.Structured.Footprint.BasicWritesWithin]
  · rcases hop with rfl | hop
    · simp [RAM.Structured.Footprint.BasicWritesWithin]
    · rcases hop with rfl | hop
      · simp [RAM.Structured.Footprint.BasicWritesWithin]
      · simp at hop

theorem cacheInputPrefix_runs_inputFrame_internal
    (regs : Registers) (kernel : TrialKernel regs)
    (input : List Bool) :
    let limit := footprintLimit regs kernel.footprint
    let cached :=
      Basic.execList (cacheInputPrefixOps regs limit)
        (RAM.initRegs input)
    Runs (cacheInputPrefix regs limit) (RAM.initRegs input) cached ∧
      InputFrame regs kernel.footprint input cached := by
  dsimp only
  let limit := footprintLimit regs kernel.footprint
  let cached :=
    Basic.execList (cacheInputPrefixOps regs limit)
      (RAM.initRegs input)
  have hrun :
      Runs (cacheInputPrefix regs limit) (RAM.initRegs input)
        cached := by
    simpa [cacheInputPrefix, cached] using
      runs_basics (cacheInputPrefixOps regs limit) (RAM.initRegs input)
  refine ⟨hrun, ?_⟩
  constructor
  · rfl
  · intro address hlimit
    have hcacheMember :
        regs.prefixCache ∈ regs.footprint ∪ kernel.footprint :=
      Finset.mem_union_left _
        (regs.index_mem_footprint 16)
    have hcacheLe :=
      allowed_address_le_limit regs kernel.footprint hcacheMember
    have haddressNotMem : address ∉ ({regs.prefixCache} : Finset ℕ) := by
      simp only [Finset.mem_singleton]
      omega
    exact runs_preserves_outside
      (cacheInputPrefix_writesWithin regs limit) hrun haddressNotMem

private theorem cmdWritesWithin_mono
    {small large : Finset ℕ} (hsub : small ⊆ large)
    {cmd : Cmd}
    (hwrites :
      RAM.Structured.Footprint.CmdWritesWithin small cmd) :
    RAM.Structured.Footprint.CmdWritesWithin large cmd := by
  induction cmd with
  | skip =>
      trivial
  | basic op =>
      cases op <;>
        simp only [RAM.Structured.Footprint.CmdWritesWithin,
          RAM.Structured.Footprint.BasicWritesWithin] at hwrites ⊢
      all_goals exact hsub hwrites
  | seq first second firstIH secondIH =>
      exact ⟨firstIH hwrites.1, secondIH hwrites.2⟩
  | ifZero test onZero onNonzero zeroIH nonzeroIH =>
      exact ⟨zeroIH hwrites.1, nonzeroIH hwrites.2⟩
  | whileNonzero test body bodyIH =>
      exact bodyIH hwrites

theorem sourceWritesWithin_internal
    (regs : Registers) (kernel : TrialKernel regs) :
    RAM.Structured.Footprint.CmdWritesWithin
      (regs.footprint ∪ kernel.footprint)
      (program regs kernel) := by
  let allowed := regs.footprint ∪ kernel.footprint
  have hkernel :
      RAM.Structured.Footprint.CmdWritesWithin
        allowed kernel.command :=
    cmdWritesWithin_mono Finset.subset_union_right
      kernel.writesWithin
  have hcache :
      RAM.Structured.Footprint.CmdWritesWithin allowed
        (cacheInputPrefix regs
          (footprintLimit regs kernel.footprint)) := by
    apply cmdWritesWithin_mono
      (small := {regs.prefixCache})
      (large := allowed)
    · intro address haddress
      simp only [Finset.mem_singleton] at haddress
      subst address
      exact Finset.mem_union_left _
        (regs.index_mem_footprint 16)
    · exact cacheInputPrefix_writesWithin regs _
  have hone : regs.one ∈ allowed :=
    Finset.mem_union_left _
      (regs.index_mem_footprint (Registers.primeSlot 6))
  have hprime : regs.prime ∈ allowed :=
    Finset.mem_union_left _
      (regs.index_mem_footprint (Registers.primeSlot 0))
  have hinput : regs.inputLength ∈ allowed :=
    Finset.mem_union_left _
      (regs.index_mem_footprint 0)
  rw [program]
  constructor
  · apply And.intro hcache
    simpa [allowed, coreProgram, setup, candidateBody,
      initializePrime, initializeGuesses,
      advanceCandidateOnFailure, guessLoop, guessBody,
      finishTrial, advanceGuessOrStop, stopOnSuccess,
      Cmd.seqList, RAM.Structured.Footprint.CmdWritesWithin,
      RAM.Structured.Footprint.BasicWritesWithin,
      Registers.footprint, Registers.primeRegisters,
      Registers.primeSlot, PrimeSearch.search,
      PrimeSearch.primality, PrimeSearch.primalitySetupOps,
      PrimeSearch.refreshSearchTest, PrimeSearch.searchBody,
      PrimeSearch.trialSetupOps, PrimeSearch.trialLoop,
      PrimeSearch.trialBody, PrimeSearch.decrementDivisor,
      RuntimeArithmetic.reduce, RuntimeArithmetic.reduceBody,
      RuntimeArithmetic.reduceTestOp, Cmd.basics,
      PrimeSearch.Registers.reduceRegisters] using
        And.intro hone (And.intro hprime hkernel)
  · change regs.inputLength ∈ allowed
    exact hinput

private structure CandidateInv
    (regs : Registers) (kernel : TrialKernel regs)
    (input : List Bool) (candidate : ℕ)
    (store : Store) : Prop where
  inputFrame : InputFrame regs kernel.footprint input store
  inputLength_eq : store regs.inputLength = input.length
  candidate_eq : store regs.candidate = candidate
  candidate_ge : input.length ≤ candidate
  one_eq : store regs.one = 1
  candidateActive_eq : store regs.candidateActive = 1

/-- Successful postcondition before the terminal standard-ABI write. -/
private structure CoreProgramPost
    (regs : Registers) (kernel : TrialKernel regs)
    (input : List Bool) (verdict : Bool) (store : Store) : Prop where
  inputFrame : InputFrame regs kernel.footprint input store
  inputLength_eq : store regs.inputLength = input.length
  candidate_ge : input.length ≤ store regs.candidate
  prime_eq :
    store regs.prime =
      firstPrimeAtOrAbove (store regs.candidate)
  guess_lt :
    store regs.guess <
      kernel.guessCount (store regs.candidate)
  outcome_eq :
    kernel.outcome input (store regs.candidate)
      (store regs.prime) (store regs.guess) =
        some verdict
  verdict_eq :
    store regs.verdict = Input.bitValue verdict
  success_eq : store regs.success = 1
  one_eq : store regs.one = 1
  guessActive_eq : store regs.guessActive = 0
  candidateActive_eq : store regs.candidateActive = 0

private structure GuessSuccess
    (regs : Registers) (kernel : TrialKernel regs)
    (input : List Bool) (candidate prime : ℕ)
    (verdict : Bool)
    (store : Store) : Prop where
  inputFrame : InputFrame regs kernel.footprint input store
  inputLength_eq : store regs.inputLength = input.length
  candidate_eq : store regs.candidate = candidate
  prime_eq : store regs.prime = prime
  guess_lt : store regs.guess < kernel.guessCount candidate
  outcome_eq :
    kernel.outcome input candidate prime (store regs.guess) =
      some verdict
  verdict_eq : store regs.verdict = Input.bitValue verdict
  success_eq : store regs.success = 1
  one_eq : store regs.one = 1
  guessActive_eq : store regs.guessActive = 0
  candidateActive_eq : store regs.candidateActive = 0

private structure GuessExhausted
    (regs : Registers) (kernel : TrialKernel regs)
    (input : List Bool) (candidate prime : ℕ)
    (store : Store) : Prop where
  inputFrame : InputFrame regs kernel.footprint input store
  inputLength_eq : store regs.inputLength = input.length
  candidate_eq : store regs.candidate = candidate
  prime_eq : store regs.prime = prime
  all_none :
    ∀ guess, guess < kernel.guessCount candidate →
      kernel.outcome input candidate prime guess = none
  success_eq : store regs.success = 0
  one_eq : store regs.one = 1
  guessActive_eq : store regs.guessActive = 0
  candidateActive_eq : store regs.candidateActive = 1

private theorem guessLoop_runs
    (regs : Registers) (kernel : TrialKernel regs)
    (input : List Bool)
    (candidate prime guess : ℕ) (store : Store)
    (hframe : InputFrame regs kernel.footprint input store)
    (hinput : store regs.inputLength = input.length)
    (hcandidate : store regs.candidate = candidate)
    (hprime : store regs.prime = prime)
    (hguess : store regs.guess = guess)
    (hone : store regs.one = 1)
    (hcandidateActive : store regs.candidateActive = 1)
    (hguessActive : store regs.guessActive = 1)
    (hguessLt : guess < kernel.guessCount candidate)
    (hprevious : ∀ prior, prior < guess →
      kernel.outcome input candidate prime prior = none) :
    ∃ final,
      Runs (guessLoop regs kernel) store final ∧
      ((∃ verdict,
          GuessSuccess regs kernel input candidate prime
            verdict final) ∨
        GuessExhausted regs kernel input candidate prime final) := by
  generalize hgapEq :
    kernel.guessCount candidate - guess = gap
  induction gap using Nat.strong_induction_on generalizing guess store with
  | h gap ih =>
      have hactive : store regs.guessActive ≠ 0 := by
        rw [hguessActive]
        omega
      obtain ⟨trial, htrial, hpost⟩ :=
        trialKernel_runs_internal kernel input store hframe hinput hone (by
          simpa [hcandidate, hguess] using hguessLt)
      cases hout :
          kernel.outcome input candidate prime guess with
      | some verdict =>
          let outerStopped :=
            (Basic.imm regs.candidateActive 0).exec trial
          let stopped :=
            (Basic.imm regs.guessActive 0).exec outerStopped
          have houterFrame :
              InputFrame regs kernel.footprint input outerStopped := by
            simpa [outerStopped, Basic.exec] using
              controller_update_inputFrame regs kernel input
                hpost.inputFrame 7 (by decide) 0
          have hstoppedFrame :
              InputFrame regs kernel.footprint input stopped := by
            simpa [stopped, Basic.exec] using
              controller_update_inputFrame regs kernel input
                houterFrame 6 (by decide) 0
          have htrialSuccess : trial regs.success = 1 := by
            simpa [hcandidate, hprime, hguess, hout] using
              hpost.success_eq
          have hstop :
              Runs (stopOnSuccess regs) trial stopped := by
            simpa [stopOnSuccess, outerStopped, stopped] using
              Runs.seq
                (Runs.basic
                  (Basic.imm regs.candidateActive 0) trial)
                (Runs.basic
                  (Basic.imm regs.guessActive 0) outerStopped)
          have hfinish :
              Runs (finishTrial regs) trial stopped := by
            simpa [finishTrial] using
              Runs.ifNonzero (by omega : trial regs.success ≠ 0) hstop
          have hbody :
              Runs (guessBody regs kernel) store stopped := by
            simpa [guessBody] using Runs.seq htrial hfinish
          have hstoppedActive :
              stopped regs.guessActive = 0 := by
            simp [stopped, Basic.exec]
          have hrest :
              Runs (guessLoop regs kernel) stopped stopped := by
            simpa [guessLoop] using
              Runs.whileZero hstoppedActive
          refine ⟨stopped, ?_, Or.inl ⟨verdict, ?_⟩⟩
          · simpa [guessLoop] using
              Runs.whileNonzero hactive hbody hrest
          · refine
              { inputFrame := hstoppedFrame
                inputLength_eq := ?_
                candidate_eq := ?_
                prime_eq := ?_
                guess_lt := ?_
                outcome_eq := ?_
                verdict_eq := ?_
                success_eq := ?_
                one_eq := ?_
                guessActive_eq := hstoppedActive
                candidateActive_eq := ?_ }
            · simpa [stopped, outerStopped, Basic.exec,
                regs.index_inj_iff] using
                hpost.inputLength_eq.trans hinput
            · simpa [stopped, outerStopped, Basic.exec,
                regs.index_inj_iff] using
                hpost.candidate_eq.trans hcandidate
            · simpa [stopped, outerStopped, Basic.exec,
                upper_ne_outer regs 0 7 (by decide),
                upper_ne_outer regs 0 6 (by decide)] using
                hpost.prime_eq.trans hprime
            · simpa [stopped, outerStopped, Basic.exec,
                regs.index_inj_iff, hpost.guess_eq, hguess] using
                hguessLt
            · simpa [stopped, outerStopped, Basic.exec,
                regs.index_inj_iff, hpost.guess_eq, hguess] using hout
            · simpa [stopped, outerStopped, Basic.exec,
                regs.index_inj_iff, hcandidate,
                hprime, hguess, hout] using hpost.verdict_eq
            · simpa [stopped, outerStopped, Basic.exec,
                regs.index_inj_iff] using htrialSuccess
            · simpa [stopped, outerStopped, Basic.exec,
                upper_ne_outer regs 6 7 (by decide),
                upper_ne_outer regs 6 6 (by decide)] using
                hpost.one_eq.trans hone
            · simp [stopped, outerStopped, Basic.exec]
      | none =>
          have htrialSuccess : trial regs.success = 0 := by
            simpa [hcandidate, hprime, hguess, hout] using
              hpost.success_eq
          by_cases hnext :
              guess + 1 < kernel.guessCount candidate
          · let next :=
              (Basic.add regs.guess regs.guess regs.one).exec trial
            have hnextFrame :
                InputFrame regs kernel.footprint input next := by
              simpa [next, Basic.exec] using
                controller_update_inputFrame regs kernel input
                  hpost.inputFrame 2 (by decide)
                  (trial regs.guess + trial regs.one)
            have htrialHasNext :
                trial regs.hasNext = 1 := by
              simpa [hcandidate, hguess, hasNextValue, hnext] using
                hpost.hasNext_eq
            have hadvance :
                Runs (advanceGuessOrStop regs) trial next := by
              simpa [advanceGuessOrStop, next] using
                Runs.ifNonzero
                  (by omega : trial regs.hasNext ≠ 0)
                  (Runs.basic
                    (Basic.add regs.guess regs.guess regs.one) trial)
            have hfinish :
                Runs (finishTrial regs) trial next := by
              simpa [finishTrial] using
                Runs.ifZero htrialSuccess hadvance
            have hbody :
                Runs (guessBody regs kernel) store next := by
              simpa [guessBody] using Runs.seq htrial hfinish
            have hnextInput :
                next regs.inputLength = input.length := by
              simpa [next, Basic.exec, regs.index_inj_iff] using
                hpost.inputLength_eq.trans hinput
            have hnextCandidate :
                next regs.candidate = candidate := by
              simpa [next, Basic.exec, regs.index_inj_iff] using
                hpost.candidate_eq.trans hcandidate
            have hnextPrime :
                next regs.prime = prime := by
              simpa [next, Basic.exec,
                upper_ne_outer regs 0 2 (by decide)] using
                hpost.prime_eq.trans hprime
            have hnextGuess :
                next regs.guess = guess + 1 := by
              simp [next, Basic.exec, hpost.guess_eq, hguess,
                hpost.one_eq, hone]
            have hnextOne :
                next regs.one = 1 := by
              simpa [next, Basic.exec,
                upper_ne_outer regs 6 2 (by decide)] using
                hpost.one_eq.trans hone
            have hnextCandidateActive :
                next regs.candidateActive = 1 := by
              simpa [next, Basic.exec, regs.index_inj_iff] using
                hpost.candidateActive_eq.trans hcandidateActive
            have hnextGuessActive :
                next regs.guessActive = 1 := by
              simpa [next, Basic.exec, regs.index_inj_iff] using
                hpost.guessActive_eq.trans hguessActive
            have hnextPrevious :
                ∀ prior, prior < guess + 1 →
                  kernel.outcome input candidate prime prior = none := by
              intro prior hprior
              by_cases heq : prior = guess
              · simpa [heq] using hout
              · exact hprevious prior (by omega)
            have hnextGap :
                kernel.guessCount candidate - (guess + 1) < gap := by
              omega
            obtain ⟨final, hrest, hresult⟩ :=
              ih (kernel.guessCount candidate - (guess + 1))
                hnextGap (guess + 1) next hnextFrame hnextInput
                hnextCandidate hnextPrime hnextGuess hnextOne
                hnextCandidateActive hnextGuessActive hnext
                hnextPrevious rfl
            exact ⟨final, by
              simpa [guessLoop] using
                Runs.whileNonzero hactive hbody hrest,
              hresult⟩
          · let stopped :=
              (Basic.imm regs.guessActive 0).exec trial
            have hstoppedFrame :
                InputFrame regs kernel.footprint input stopped := by
              simpa [stopped, Basic.exec] using
                controller_update_inputFrame regs kernel input
                  hpost.inputFrame 6 (by decide) 0
            have htrialHasNext :
                trial regs.hasNext = 0 := by
              simpa [hcandidate, hguess, hasNextValue, hnext] using
                hpost.hasNext_eq
            have hadvance :
                Runs (advanceGuessOrStop regs) trial stopped := by
              simpa [advanceGuessOrStop, stopped] using
                Runs.ifZero htrialHasNext
                  (Runs.basic
                    (Basic.imm regs.guessActive 0) trial)
            have hfinish :
                Runs (finishTrial regs) trial stopped := by
              simpa [finishTrial] using
                Runs.ifZero htrialSuccess hadvance
            have hbody :
                Runs (guessBody regs kernel) store stopped := by
              simpa [guessBody] using Runs.seq htrial hfinish
            have hstoppedActive :
                stopped regs.guessActive = 0 := by
              simp [stopped, Basic.exec]
            have hrest :
                Runs (guessLoop regs kernel) stopped stopped := by
              simpa [guessLoop] using
                Runs.whileZero hstoppedActive
            refine ⟨stopped, ?_, Or.inr ?_⟩
            · simpa [guessLoop] using
                Runs.whileNonzero hactive hbody hrest
            · refine
                { inputFrame := hstoppedFrame
                  inputLength_eq := ?_
                  candidate_eq := ?_
                  prime_eq := ?_
                  all_none := ?_
                  success_eq := ?_
                  one_eq := ?_
                  guessActive_eq := hstoppedActive
                  candidateActive_eq := ?_ }
              · simpa [stopped, Basic.exec, regs.index_inj_iff] using
                  hpost.inputLength_eq.trans hinput
              · simpa [stopped, Basic.exec, regs.index_inj_iff] using
                  hpost.candidate_eq.trans hcandidate
              · simpa [stopped, Basic.exec,
                  upper_ne_outer regs 0 6 (by decide)] using
                  hpost.prime_eq.trans hprime
              · intro prior hprior
                by_cases hpriorGuess : prior < guess
                · exact hprevious prior hpriorGuess
                · have heq : prior = guess := by omega
                  simpa [heq] using hout
              · simpa [stopped, Basic.exec,
                  regs.index_inj_iff] using htrialSuccess
              · simpa [stopped, Basic.exec,
                  upper_ne_outer regs 6 6 (by decide)] using
                  hpost.one_eq.trans hone
              · simpa [stopped, Basic.exec,
                  regs.index_inj_iff] using
                  hpost.candidateActive_eq.trans hcandidateActive

private theorem candidateBody_runs
    (regs : Registers) (kernel : TrialKernel regs)
    (input : List Bool)
    (candidate : ℕ) (store : Store)
    (hinv :
      CandidateInv regs kernel input candidate store) :
    ∃ final,
      Runs (candidateBody regs kernel) store final ∧
      ((∃ verdict,
          CoreProgramPost regs kernel input verdict final ∧
            final regs.candidate = candidate) ∨
        (CandidateInv regs kernel input (candidate + 1) final ∧
          ∀ guess, guess < kernel.guessCount candidate →
            kernel.outcome input candidate
              (firstPrimeAtOrAbove candidate) guess = none)) := by
  let primed :=
    (Basic.mul regs.prime regs.candidate regs.one).exec store
  have hprimedFrame :
      InputFrame regs kernel.footprint input primed := by
    simpa [primed, Basic.exec] using
      controller_update_inputFrame regs kernel input hinv.inputFrame
        (Registers.primeSlot 0) (by decide)
        (store regs.candidate * store regs.one)
  have hinitializePrime :
      Runs (initializePrime regs) store primed := by
    simpa [initializePrime, primed] using
      Runs.basic
        (Basic.mul regs.prime regs.candidate regs.one) store
  have hprimedPrime :
      primed regs.prime = candidate := by
    simp [primed, Basic.exec, hinv.candidate_eq, hinv.one_eq]
  obtain ⟨selected, hsearch, hsearchPost⟩ :=
    PrimeSearch.search_runs regs.primeRegisters primed candidate
      hprimedPrime
  have hselectedFrame :
      InputFrame regs kernel.footprint input selected :=
    primeSearch_preserves_inputFrame regs kernel input
      hprimedFrame hsearch
  have hselectedInput :
      selected regs.inputLength = input.length := by
    calc
      selected regs.inputLength = primed regs.inputLength :=
        primeSearch_preserves_outer regs hsearch 0 (by decide)
      _ = input.length := by
        simpa [primed, Basic.exec,
          (upper_ne_outer regs 0 0 (by decide)).symm] using
          hinv.inputLength_eq
  have hselectedCandidate :
      selected regs.candidate = candidate := by
    calc
      selected regs.candidate = primed regs.candidate :=
        primeSearch_preserves_outer regs hsearch 1 (by decide)
      _ = candidate := by
        simpa [primed, Basic.exec,
          (upper_ne_outer regs 0 1 (by decide)).symm] using
          hinv.candidate_eq
  have hselectedCandidateActive :
      selected regs.candidateActive = 1 := by
    calc
      selected regs.candidateActive = primed regs.candidateActive :=
        primeSearch_preserves_outer regs hsearch 7 (by decide)
      _ = 1 := by
        simpa [primed, Basic.exec,
          (upper_ne_outer regs 0 7 (by decide)).symm] using
          hinv.candidateActive_eq
  have hselectedPrime :
      selected regs.prime =
        firstPrimeAtOrAbove candidate :=
    firstPrime_unique hsearchPost.firstPrime
      (firstPrimeAtOrAbove_spec_internal candidate)
  let zeroGuess :=
    (Basic.imm regs.guess 0).exec selected
  let ready :=
    (Basic.imm regs.guessActive 1).exec zeroGuess
  have hzeroGuessFrame :
      InputFrame regs kernel.footprint input zeroGuess := by
    simpa [zeroGuess, Basic.exec] using
      controller_update_inputFrame regs kernel input hselectedFrame
        2 (by decide) 0
  have hreadyFrame :
      InputFrame regs kernel.footprint input ready := by
    simpa [ready, Basic.exec] using
      controller_update_inputFrame regs kernel input hzeroGuessFrame
        6 (by decide) 1
  have hinitializeGuesses :
      Runs (initializeGuesses regs) selected ready := by
    simpa [initializeGuesses, zeroGuess, ready] using
      Runs.seq
        (Runs.basic (Basic.imm regs.guess 0) selected)
        (Runs.basic (Basic.imm regs.guessActive 1) zeroGuess)
  have hreadyInput :
      ready regs.inputLength = input.length := by
    simpa [ready, zeroGuess, Basic.exec,
      regs.index_inj_iff] using hselectedInput
  have hreadyCandidate :
      ready regs.candidate = candidate := by
    simpa [ready, zeroGuess, Basic.exec,
      regs.index_inj_iff] using hselectedCandidate
  have hreadyPrime :
      ready regs.prime =
        firstPrimeAtOrAbove candidate := by
    simpa [ready, zeroGuess, Basic.exec,
      upper_ne_outer regs 0 2 (by decide),
      upper_ne_outer regs 0 6 (by decide)] using hselectedPrime
  have hreadyGuess :
      ready regs.guess = 0 := by
    simp [ready, zeroGuess, Basic.exec, regs.index_inj_iff]
  have hreadyOne :
      ready regs.one = 1 := by
    simpa [ready, zeroGuess, Basic.exec,
      upper_ne_outer regs 6 2 (by decide),
      upper_ne_outer regs 6 6 (by decide)] using
      hsearchPost.one_eq
  have hreadyCandidateActive :
      ready regs.candidateActive = 1 := by
    simpa [ready, zeroGuess, Basic.exec,
      regs.index_inj_iff] using hselectedCandidateActive
  have hreadyGuessActive :
      ready regs.guessActive = 1 := by
    simp [ready, Basic.exec]
  obtain ⟨guessesFinal, hguesses, hguessResult⟩ :=
    guessLoop_runs regs kernel input candidate
      (firstPrimeAtOrAbove candidate) 0 ready
      hreadyFrame hreadyInput hreadyCandidate hreadyPrime
      hreadyGuess hreadyOne
      hreadyCandidateActive hreadyGuessActive
      (kernel.guessCount_pos candidate)
      (by intro prior hprior; omega)
  rcases hguessResult with hsuccess | hexhausted
  · obtain ⟨verdict, hsuccess⟩ := hsuccess
    have hadvance :
        Runs (advanceCandidateOnFailure regs)
          guessesFinal guessesFinal := by
      simpa [advanceCandidateOnFailure] using
        Runs.ifZero hsuccess.candidateActive_eq
          (Runs.skip guessesFinal)
    refine ⟨guessesFinal, ?_, Or.inl ⟨verdict, ?_, hsuccess.candidate_eq⟩⟩
    · simpa [candidateBody] using
        Runs.seq hinitializePrime
          (Runs.seq hsearch
            (Runs.seq hinitializeGuesses
              (Runs.seq hguesses hadvance)))
    · refine
        { inputFrame := hsuccess.inputFrame
          inputLength_eq := hsuccess.inputLength_eq
          candidate_ge := ?_
          prime_eq := ?_
          guess_lt := ?_
          outcome_eq := ?_
          verdict_eq := hsuccess.verdict_eq
          success_eq := hsuccess.success_eq
          one_eq := hsuccess.one_eq
          guessActive_eq := hsuccess.guessActive_eq
          candidateActive_eq := hsuccess.candidateActive_eq }
      · simpa [hsuccess.candidate_eq] using hinv.candidate_ge
      · simpa [hsuccess.candidate_eq] using hsuccess.prime_eq
      · simpa [hsuccess.candidate_eq] using hsuccess.guess_lt
      · simpa [hsuccess.candidate_eq, hsuccess.prime_eq] using
          hsuccess.outcome_eq
  · let advanced :=
      (Basic.add regs.candidate regs.candidate regs.one).exec
        guessesFinal
    have hadvancedFrame :
        InputFrame regs kernel.footprint input advanced := by
      simpa [advanced, Basic.exec] using
        controller_update_inputFrame regs kernel input
          hexhausted.inputFrame 1 (by decide)
          (guessesFinal regs.candidate + guessesFinal regs.one)
    have hadvance :
        Runs (advanceCandidateOnFailure regs)
          guessesFinal advanced := by
      simpa [advanceCandidateOnFailure, advanced] using
        Runs.ifNonzero
          (by
            rw [hexhausted.candidateActive_eq]
            omega)
          (Runs.basic
            (Basic.add regs.candidate regs.candidate regs.one)
            guessesFinal)
    refine ⟨advanced, ?_, Or.inr ⟨?_, hexhausted.all_none⟩⟩
    · simpa [candidateBody] using
        Runs.seq hinitializePrime
          (Runs.seq hsearch
            (Runs.seq hinitializeGuesses
              (Runs.seq hguesses hadvance)))
    · refine
        { inputFrame := hadvancedFrame
          inputLength_eq := ?_
          candidate_eq := ?_
          candidate_ge := ?_
          one_eq := ?_
          candidateActive_eq := ?_ }
      · simpa [advanced, Basic.exec,
          regs.index_inj_iff] using hexhausted.inputLength_eq
      · simp [advanced, Basic.exec, hexhausted.candidate_eq,
          hexhausted.one_eq]
      · exact hinv.candidate_ge.trans (Nat.le_add_right candidate 1)
      · simpa [advanced, Basic.exec,
          upper_ne_outer regs 6 1 (by decide)] using
          hexhausted.one_eq
      · simpa [advanced, Basic.exec,
          regs.index_inj_iff] using
          hexhausted.candidateActive_eq

private theorem candidateLoop_runs
    (regs : Registers) (kernel : TrialKernel regs)
    (input : List Bool)
    (target targetGuess : ℕ)
    (targetVerdict : Bool)
    (htargetGuess :
      targetGuess < kernel.guessCount target)
    (htargetOutcome :
      kernel.outcome input target (firstPrimeAtOrAbove target)
        targetGuess = some targetVerdict)
    (candidate : ℕ) (store : Store)
    (hcandidateUpper : candidate ≤ target)
    (hinv : CandidateInv regs kernel input candidate store) :
    ∃ final verdict,
      Runs
        (.whileNonzero regs.candidateActive
          (candidateBody regs kernel))
        store final ∧
      CoreProgramPost regs kernel input verdict final ∧
      final regs.candidate ≤ target := by
  generalize hgapEq : target - candidate = gap
  induction gap using Nat.strong_induction_on
      generalizing candidate store with
  | h gap ih =>
      have hactive : store regs.candidateActive ≠ 0 := by
        rw [hinv.candidateActive_eq]
        omega
      obtain ⟨next, hbody, hresult⟩ :=
        candidateBody_runs regs kernel input candidate store hinv
      rcases hresult with hsuccess | hfailure
      · obtain ⟨verdict, hpost, hcandidateEq⟩ := hsuccess
        have hrest :
            Runs
              (.whileNonzero regs.candidateActive
                (candidateBody regs kernel))
              next next :=
          Runs.whileZero hpost.candidateActive_eq
        exact ⟨next, verdict,
          Runs.whileNonzero hactive hbody hrest,
          hpost, by simpa [hcandidateEq] using hcandidateUpper⟩
      · obtain ⟨hnextInv, hallNone⟩ := hfailure
        by_cases heq : candidate = target
        · subst candidate
          exact False.elim
            ((Option.some_ne_none targetVerdict)
              (htargetOutcome.symm.trans
                (hallNone targetGuess htargetGuess)))
        · have hcandidateLt : candidate < target := by
            omega
          have hnextUpper : candidate + 1 ≤ target := by
            omega
          have hnextGap :
              target - (candidate + 1) < gap := by
            omega
          obtain ⟨final, verdict, hrest, hpost, hfinalUpper⟩ :=
            ih (target - (candidate + 1)) hnextGap
              (candidate + 1) next hnextUpper hnextInv rfl
          exact ⟨final, verdict,
            Runs.whileNonzero hactive hbody hrest,
            hpost, hfinalUpper⟩

theorem program_runs_bounded_candidate_internal
    (regs : Registers) (kernel : TrialKernel regs)
    (input : List Bool) (target : ℕ)
    (targetVerdict : Bool)
    (htarget : input.length ≤ target)
    (hreturns :
      CandidateReturns kernel input target targetVerdict) :
    ∃ final verdict,
      Runs (program regs kernel) (RAM.initRegs input) final ∧
      ProgramPost regs kernel input verdict final ∧
      final regs.candidate ≤ target := by
  obtain ⟨targetGuess, htargetGuess, htargetOutcome⟩ := hreturns
  let limit := footprintLimit regs kernel.footprint
  let cached :=
    Basic.execList (cacheInputPrefixOps regs limit)
      (RAM.initRegs input)
  have hcache :
      Runs (cacheInputPrefix regs limit) (RAM.initRegs input)
        cached := by
    exact (cacheInputPrefix_runs_inputFrame_internal regs kernel input).1
  have hcachedFrame :
      InputFrame regs kernel.footprint input cached := by
    exact (cacheInputPrefix_runs_inputFrame_internal regs kernel input).2
  have hcachedInput :
      cached regs.inputLength = input.length := by
    have hpreserved :=
      runs_preserves_outside
        (cacheInputPrefix_writesWithin regs limit) hcache
        (index := regs.inputLength)
    calc
      cached regs.inputLength =
          RAM.initRegs input regs.inputLength := by
        apply hpreserved
        simp only [Finset.mem_singleton]
        exact regs.index_ne (by decide)
      _ = input.length := by
        simp [regs.inputLength_zero, RAM.initRegs]
  let oned :=
    (Basic.imm regs.one 1).exec cached
  let candidateSet :=
    (Basic.mul regs.candidate regs.inputLength regs.one).exec
      oned
  let ready :=
    (Basic.imm regs.candidateActive 1).exec candidateSet
  have honedFrame :
      InputFrame regs kernel.footprint input oned := by
    simpa [oned, Basic.exec] using
      controller_update_inputFrame regs kernel input hcachedFrame
        (Registers.primeSlot 6) (by decide) 1
  have hcandidateSetFrame :
      InputFrame regs kernel.footprint input candidateSet := by
    simpa [candidateSet, Basic.exec] using
      controller_update_inputFrame regs kernel input honedFrame
        1 (by decide)
        (oned regs.inputLength * oned regs.one)
  have hreadyFrame :
      InputFrame regs kernel.footprint input ready := by
    simpa [ready, Basic.exec] using
      controller_update_inputFrame regs kernel input hcandidateSetFrame
        7 (by decide) 1
  have hsetup :
      Runs (setup regs) cached ready := by
    simpa [setup, Cmd.seqList, oned, candidateSet, ready] using
      Runs.seq
        (Runs.basic (Basic.imm regs.one 1) cached)
        (Runs.seq
          (Runs.basic
            (Basic.mul regs.candidate regs.inputLength regs.one)
            oned)
          (Runs.basic
            (Basic.imm regs.candidateActive 1) candidateSet))
  have hreadyInv :
      CandidateInv regs kernel input input.length ready := by
    constructor
    · exact hreadyFrame
    · simpa [ready, candidateSet, oned, Basic.exec,
        regs.index_inj_iff,
        (upper_ne_outer regs 6 0 (by decide)).symm] using
          hcachedInput
    · simp [ready, candidateSet, oned, Basic.exec,
        regs.index_inj_iff,
        (upper_ne_outer regs 6 0 (by decide)).symm,
        hcachedInput]
    · exact le_refl input.length
    · simp [ready, candidateSet, oned, Basic.exec,
        upper_ne_outer regs 6 1 (by decide),
        upper_ne_outer regs 6 7 (by decide)]
    · simp [ready, Basic.exec]
  obtain ⟨coreFinal, verdict, hloop, hpost, hbound⟩ :=
    candidateLoop_runs regs kernel input target targetGuess
      targetVerdict htargetGuess htargetOutcome input.length ready
      htarget hreadyInv
  let final :=
    (Basic.mul regs.inputLength regs.verdict regs.one).exec coreFinal
  have hcore :
      Runs (coreProgram regs kernel) (RAM.initRegs input)
        coreFinal := by
    simpa [coreProgram, limit] using
      Runs.seq hcache (Runs.seq hsetup hloop)
  have hpublish :
      Runs (publishVerdict regs) coreFinal final := by
    simpa [publishVerdict, final] using
      Runs.basic
        (Basic.mul regs.inputLength regs.verdict regs.one)
        coreFinal
  have hfinalFrame :
      InputFrame regs kernel.footprint input final := by
    simpa [final, Basic.exec] using
      controller_update_inputFrame regs kernel input
        hpost.inputFrame 0 (by decide)
        (coreFinal regs.verdict * coreFinal regs.one)
  refine ⟨final, verdict, ?_, ?_, ?_⟩
  · simpa [program] using Runs.seq hcore hpublish
  · refine
      { inputFrame := hfinalFrame
        output_eq := ?_
        candidate_ge := ?_
        prime_eq := ?_
        guess_lt := ?_
        outcome_eq := ?_
        verdict_eq := ?_
        success_eq := ?_
        one_eq := ?_
        guessActive_eq := ?_
        candidateActive_eq := ?_ }
    · simp [final, Basic.exec, hpost.verdict_eq, hpost.one_eq]
    · simpa [final, Basic.exec, regs.index_inj_iff] using
        hpost.candidate_ge
    · simpa [final, Basic.exec,
        (regs.index_ne (by decide : (0 : Fin 17) ≠ 1)).symm,
        upper_ne_outer regs 0 0 (by decide)] using hpost.prime_eq
    · simpa [final, Basic.exec, regs.index_inj_iff] using
        hpost.guess_lt
    · simpa [final, Basic.exec, regs.index_inj_iff,
        upper_ne_outer regs 0 0 (by decide)] using
        hpost.outcome_eq
    · simpa [final, Basic.exec, regs.index_inj_iff] using
        hpost.verdict_eq
    · simpa [final, Basic.exec, regs.index_inj_iff] using
        hpost.success_eq
    · simpa [final, Basic.exec,
        upper_ne_outer regs 6 0 (by decide)] using
        hpost.one_eq
    · simpa [final, Basic.exec, regs.index_inj_iff] using
        hpost.guessActive_eq
    · simpa [final, Basic.exec, regs.index_inj_iff] using
        hpost.candidateActive_eq
  · simpa [final, Basic.exec, regs.index_inj_iff] using hbound

theorem program_runs_internal
    (regs : Registers) (kernel : TrialKernel regs)
    (input : List Bool)
    (hterminates : EventuallySucceeds kernel input) :
    ∃ final verdict,
      Runs (program regs kernel) (RAM.initRegs input) final ∧
      ProgramPost regs kernel input verdict final := by
  obtain ⟨target, targetVerdict, htarget, hreturns⟩ := hterminates
  obtain ⟨final, verdict, hrun, hpost, _hbound⟩ :=
    program_runs_bounded_candidate_internal regs kernel input
      target targetVerdict htarget hreturns
  exact ⟨final, verdict, hrun, hpost⟩

private theorem invariantRuns_mono
    {first second : Store → Prop}
    (himp : ∀ store, first store → second store)
    {cmd : Cmd} {initial final : Store} {steps : ℕ}
    (hrun : InvariantRuns first cmd initial final steps) :
    InvariantRuns second cmd initial final steps := by
  induction hrun with
  | skip store hstore =>
      exact InvariantRuns.skip store (himp store hstore)
  | basic op store hstore hnext =>
      exact InvariantRuns.basic op store
        (himp store hstore) (himp (op.exec store) hnext)
  | seq hfirst hsecond ihFirst ihSecond =>
      exact InvariantRuns.seq ihFirst ihSecond
  | ifZero htest hbranch ih =>
      exact InvariantRuns.ifZero htest ih
  | ifNonzero htest hbranch ih =>
      exact InvariantRuns.ifNonzero htest ih
  | whileZero htest hstore =>
      exact InvariantRuns.whileZero htest (himp _ hstore)
  | whileNonzero htest hbody hloop ihBody ihLoop =>
      exact InvariantRuns.whileNonzero htest ihBody ihLoop

private theorem mutableValuesWithin_update
    {allowed : Finset ℕ} {valueBits index value : ℕ}
    {store : Store}
    (hstore : MutableValuesWithin allowed valueBits store)
    (hvalue : bitlen value ≤ valueBits) :
    MutableValuesWithin allowed valueBits
      (Function.update store index value) := by
  intro address haddress
  by_cases heq : address = index
  · subst address
    simpa using hvalue
  · simpa [Function.update_of_ne heq] using
      hstore address haddress

private theorem mutableValuesWithin_imm
    {allowed : Finset ℕ} {valueBits destination value : ℕ}
    {store : Store}
    (hstore : MutableValuesWithin allowed valueBits store)
    (hvalue : bitlen value ≤ valueBits) :
    MutableValuesWithin allowed valueBits
      ((Basic.imm destination value).exec store) := by
  simpa [Basic.exec] using
    mutableValuesWithin_update hstore hvalue

private theorem mutableValuesWithin_add
    {allowed : Finset ℕ} {valueBits destination left right : ℕ}
    {store : Store}
    (hstore : MutableValuesWithin allowed valueBits store)
    (hvalue : bitlen (store left + store right) ≤ valueBits) :
    MutableValuesWithin allowed valueBits
      ((Basic.add destination left right).exec store) := by
  simpa [Basic.exec] using
    mutableValuesWithin_update hstore hvalue

private theorem mutableValuesWithin_mul
    {allowed : Finset ℕ} {valueBits destination left right : ℕ}
    {store : Store}
    (hstore : MutableValuesWithin allowed valueBits store)
    (hvalue : bitlen (store left * store right) ≤ valueBits) :
    MutableValuesWithin allowed valueBits
      ((Basic.mul destination left right).exec store) := by
  simpa [Basic.exec] using
    mutableValuesWithin_update hstore hvalue

private theorem envelope_candidate_bitlen
    (henvelope :
      PrefixEnvelope regs kernel input target valueBits)
    {candidate : ℕ} (hupper : candidate ≤ target) :
    bitlen candidate ≤ valueBits := by
  apply le_trans _ henvelope.target_bitlen
  simpa [bitlen] using Nat.size_le_size hupper

private theorem envelope_guess_bitlen
    (henvelope :
      PrefixEnvelope regs kernel input target valueBits)
    {candidate guess : ℕ}
    (hlower : input.length ≤ candidate)
    (hupper : candidate ≤ target)
    (hguess : guess < kernel.guessCount candidate) :
    bitlen guess ≤ valueBits := by
  apply le_trans _ (henvelope.guessCount_bitlen
    candidate hlower hupper)
  simpa [bitlen] using Nat.size_le_size hguess.le

private theorem control_bitlen
    (henvelope :
      PrefixEnvelope regs kernel input target valueBits)
    (value : Bool) :
    bitlen (Input.bitValue value) ≤ valueBits := by
  cases value with
  | false =>
      simp [Input.bitValue, bitlen]
  | true =>
      simpa [Input.bitValue, bitlen] using henvelope.one_le

private theorem guessLoop_invariantRuns
    (regs : Registers) (kernel : TrialKernel regs)
    (input : List Bool) (target valueBits : ℕ)
    (henvelope :
      PrefixEnvelope regs kernel input target valueBits)
    (candidate prime guess : ℕ) (store : Store)
    (hcandidateLower : input.length ≤ candidate)
    (hcandidateUpper : candidate ≤ target)
    (hbound :
      MutableValuesWithin
        (regs.footprint ∪ kernel.footprint) valueBits store)
    (hframe : InputFrame regs kernel.footprint input store)
    (hinput : store regs.inputLength = input.length)
    (hcandidate : store regs.candidate = candidate)
    (hprime : store regs.prime = prime)
    (hguess : store regs.guess = guess)
    (hone : store regs.one = 1)
    (hcandidateActive : store regs.candidateActive = 1)
    (hguessActive : store regs.guessActive = 1)
    (hguessLt : guess < kernel.guessCount candidate)
    (hprevious : ∀ prior, prior < guess →
      kernel.outcome input candidate prime prior = none) :
    ∃ final steps,
      InvariantRuns
        (MutableValuesWithin
          (regs.footprint ∪ kernel.footprint) valueBits)
        (guessLoop regs kernel) store final steps ∧
      ((∃ verdict,
          GuessSuccess regs kernel input candidate prime
            verdict final) ∨
        GuessExhausted regs kernel input candidate prime final) := by
  generalize hgapEq :
    kernel.guessCount candidate - guess = gap
  induction gap using Nat.strong_induction_on
      generalizing guess store with
  | h gap ih =>
      have hactive : store regs.guessActive ≠ 0 := by
        rw [hguessActive]
        omega
      obtain ⟨trial, trialSteps, htrialRaw, hpost⟩ :=
        kernel.prefixInvariantRuns input store hframe hinput hone
          (by simpa [hcandidate, hguess] using hguessLt)
      have htrial :
          InvariantRuns
            (MutableValuesWithin
              (regs.footprint ∪ kernel.footprint) valueBits)
            kernel.command store trial trialSteps := by
        apply invariantRuns_mono _ htrialRaw
        intro current hcurrent address haddress
        apply (hcurrent address haddress).trans
        simpa [hcandidate, hprime, hguess] using
          henvelope.kernelPrefix_le candidate hcandidateLower
            hcandidateUpper prime guess hguessLt
      have htrialBound :
          MutableValuesWithin
            (regs.footprint ∪ kernel.footprint) valueBits trial :=
        htrial.final
      cases hout :
          kernel.outcome input candidate prime guess with
      | some verdict =>
          let outerStopped :=
            (Basic.imm regs.candidateActive 0).exec trial
          let stopped :=
            (Basic.imm regs.guessActive 0).exec outerStopped
          have houterBound :
              MutableValuesWithin
                (regs.footprint ∪ kernel.footprint) valueBits
                outerStopped := by
            apply mutableValuesWithin_imm htrialBound
            simpa [Input.bitValue] using
              control_bitlen henvelope false
          have hstoppedBound :
              MutableValuesWithin
                (regs.footprint ∪ kernel.footprint) valueBits
                stopped := by
            apply mutableValuesWithin_imm houterBound
            simpa [Input.bitValue] using
              control_bitlen henvelope false
          have houterFrame :
              InputFrame regs kernel.footprint input outerStopped := by
            simpa [outerStopped, Basic.exec] using
              controller_update_inputFrame regs kernel input
                hpost.inputFrame 7 (by decide) 0
          have hstoppedFrame :
              InputFrame regs kernel.footprint input stopped := by
            simpa [stopped, Basic.exec] using
              controller_update_inputFrame regs kernel input
                houterFrame 6 (by decide) 0
          have htrialSuccess : trial regs.success = 1 := by
            simpa [hcandidate, hprime, hguess, hout] using
              hpost.success_eq
          have hstop :
              ∃ stopSteps,
                InvariantRuns
                  (MutableValuesWithin
                    (regs.footprint ∪ kernel.footprint) valueBits)
                  (stopOnSuccess regs) trial stopped stopSteps := by
            refine ⟨2, ?_⟩
            simpa [stopOnSuccess, outerStopped, stopped] using
              InvariantRuns.seq
                (InvariantRuns.basic
                  (Basic.imm regs.candidateActive 0) trial
                  htrialBound houterBound)
                (InvariantRuns.basic
                  (Basic.imm regs.guessActive 0) outerStopped
                  houterBound hstoppedBound)
          obtain ⟨stopSteps, hstop⟩ := hstop
          have hfinish :
              InvariantRuns
                (MutableValuesWithin
                  (regs.footprint ∪ kernel.footprint) valueBits)
                (finishTrial regs) trial stopped (stopSteps + 2) := by
            simpa [finishTrial] using
              InvariantRuns.ifNonzero
                (by omega : trial regs.success ≠ 0) hstop
          have hbody :
              InvariantRuns
                (MutableValuesWithin
                  (regs.footprint ∪ kernel.footprint) valueBits)
                (guessBody regs kernel) store stopped
                (trialSteps + (stopSteps + 2)) := by
            simpa [guessBody] using
              InvariantRuns.seq htrial hfinish
          have hstoppedActive :
              stopped regs.guessActive = 0 := by
            simp [stopped, Basic.exec]
          have hrest :
              InvariantRuns
                (MutableValuesWithin
                  (regs.footprint ∪ kernel.footprint) valueBits)
                (guessLoop regs kernel) stopped stopped 1 := by
            simpa [guessLoop] using
              InvariantRuns.whileZero hstoppedActive hstoppedBound
          refine ⟨stopped,
            (trialSteps + (stopSteps + 2)) + 1 + 2,
            ?_, Or.inl ⟨verdict, ?_⟩⟩
          · simpa [guessLoop] using
              InvariantRuns.whileNonzero hactive hbody hrest
          · refine
              { inputFrame := hstoppedFrame
                inputLength_eq := ?_
                candidate_eq := ?_
                prime_eq := ?_
                guess_lt := ?_
                outcome_eq := ?_
                verdict_eq := ?_
                success_eq := ?_
                one_eq := ?_
                guessActive_eq := hstoppedActive
                candidateActive_eq := ?_ }
            · simpa [stopped, outerStopped, Basic.exec,
                regs.index_inj_iff] using
                hpost.inputLength_eq.trans hinput
            · simpa [stopped, outerStopped, Basic.exec,
                regs.index_inj_iff] using
                hpost.candidate_eq.trans hcandidate
            · simpa [stopped, outerStopped, Basic.exec,
                upper_ne_outer regs 0 7 (by decide),
                upper_ne_outer regs 0 6 (by decide)] using
                hpost.prime_eq.trans hprime
            · simpa [stopped, outerStopped, Basic.exec,
                regs.index_inj_iff, hpost.guess_eq, hguess] using
                hguessLt
            · simpa [stopped, outerStopped, Basic.exec,
                regs.index_inj_iff, hpost.guess_eq, hguess] using
                hout
            · simpa [stopped, outerStopped, Basic.exec,
                regs.index_inj_iff, hcandidate,
                hprime, hguess, hout] using hpost.verdict_eq
            · simpa [stopped, outerStopped, Basic.exec,
                regs.index_inj_iff] using htrialSuccess
            · simpa [stopped, outerStopped, Basic.exec,
                upper_ne_outer regs 6 7 (by decide),
                upper_ne_outer regs 6 6 (by decide)] using
                hpost.one_eq.trans hone
            · simp [stopped, outerStopped, Basic.exec]
      | none =>
          have htrialSuccess : trial regs.success = 0 := by
            simpa [hcandidate, hprime, hguess, hout] using
              hpost.success_eq
          by_cases hnext :
              guess + 1 < kernel.guessCount candidate
          · let next :=
              (Basic.add regs.guess regs.guess regs.one).exec trial
            have hnextValue :
                trial regs.guess + trial regs.one = guess + 1 := by
              rw [hpost.guess_eq, hguess, hpost.one_eq, hone]
            have hnextBound :
                MutableValuesWithin
                  (regs.footprint ∪ kernel.footprint) valueBits
                  next := by
              apply mutableValuesWithin_add htrialBound
              rw [hnextValue]
              exact envelope_guess_bitlen henvelope
                hcandidateLower hcandidateUpper hnext
            have hnextFrame :
                InputFrame regs kernel.footprint input next := by
              simpa [next, Basic.exec] using
                controller_update_inputFrame regs kernel input
                  hpost.inputFrame 2 (by decide)
                  (trial regs.guess + trial regs.one)
            have htrialHasNext :
                trial regs.hasNext = 1 := by
              simpa [hcandidate, hguess, hasNextValue, hnext] using
                hpost.hasNext_eq
            have hadvance :
                InvariantRuns
                  (MutableValuesWithin
                    (regs.footprint ∪ kernel.footprint) valueBits)
                  (advanceGuessOrStop regs) trial next 3 := by
              simpa [advanceGuessOrStop, next] using
                InvariantRuns.ifNonzero
                  (by omega : trial regs.hasNext ≠ 0)
                  (InvariantRuns.basic
                    (Basic.add regs.guess regs.guess regs.one) trial
                    htrialBound hnextBound)
            have hfinish :
                InvariantRuns
                  (MutableValuesWithin
                    (regs.footprint ∪ kernel.footprint) valueBits)
                  (finishTrial regs) trial next 4 := by
              simpa [finishTrial] using
                InvariantRuns.ifZero htrialSuccess hadvance
            have hbody :
                InvariantRuns
                  (MutableValuesWithin
                    (regs.footprint ∪ kernel.footprint) valueBits)
                  (guessBody regs kernel) store next
                  (trialSteps + 4) := by
              simpa [guessBody] using
                InvariantRuns.seq htrial hfinish
            have hnextInput :
                next regs.inputLength = input.length := by
              simpa [next, Basic.exec, regs.index_inj_iff] using
                hpost.inputLength_eq.trans hinput
            have hnextCandidate :
                next regs.candidate = candidate := by
              simpa [next, Basic.exec, regs.index_inj_iff] using
                hpost.candidate_eq.trans hcandidate
            have hnextPrime :
                next regs.prime = prime := by
              simpa [next, Basic.exec,
                upper_ne_outer regs 0 2 (by decide)] using
                hpost.prime_eq.trans hprime
            have hnextGuess :
                next regs.guess = guess + 1 := by
              simp [next, Basic.exec, hpost.guess_eq, hguess,
                hpost.one_eq, hone]
            have hnextOne :
                next regs.one = 1 := by
              simpa [next, Basic.exec,
                upper_ne_outer regs 6 2 (by decide)] using
                hpost.one_eq.trans hone
            have hnextCandidateActive :
                next regs.candidateActive = 1 := by
              simpa [next, Basic.exec, regs.index_inj_iff] using
                hpost.candidateActive_eq.trans hcandidateActive
            have hnextGuessActive :
                next regs.guessActive = 1 := by
              simpa [next, Basic.exec, regs.index_inj_iff] using
                hpost.guessActive_eq.trans hguessActive
            have hnextPrevious :
                ∀ prior, prior < guess + 1 →
                  kernel.outcome input candidate prime prior = none := by
              intro prior hprior
              by_cases heq : prior = guess
              · simpa [heq] using hout
              · exact hprevious prior (by omega)
            have hnextGap :
                kernel.guessCount candidate - (guess + 1) < gap := by
              omega
            obtain ⟨final, restSteps, hrest, hresult⟩ :=
              ih (kernel.guessCount candidate - (guess + 1))
                hnextGap (guess + 1) next hnextBound hnextFrame
                hnextInput hnextCandidate hnextPrime hnextGuess
                hnextOne hnextCandidateActive hnextGuessActive
                hnext hnextPrevious rfl
            exact ⟨final,
              (trialSteps + 4) + restSteps + 2, by
              simpa [guessLoop] using
                InvariantRuns.whileNonzero hactive hbody hrest,
              hresult⟩
          · let stopped :=
              (Basic.imm regs.guessActive 0).exec trial
            have hstoppedBound :
                MutableValuesWithin
                  (regs.footprint ∪ kernel.footprint) valueBits
                  stopped := by
              apply mutableValuesWithin_imm htrialBound
              simpa [Input.bitValue] using
                control_bitlen henvelope false
            have hstoppedFrame :
                InputFrame regs kernel.footprint input stopped := by
              simpa [stopped, Basic.exec] using
                controller_update_inputFrame regs kernel input
                  hpost.inputFrame 6 (by decide) 0
            have htrialHasNext :
                trial regs.hasNext = 0 := by
              simpa [hcandidate, hguess, hasNextValue, hnext] using
                hpost.hasNext_eq
            have hadvance :
                InvariantRuns
                  (MutableValuesWithin
                    (regs.footprint ∪ kernel.footprint) valueBits)
                  (advanceGuessOrStop regs) trial stopped 2 := by
              simpa [advanceGuessOrStop, stopped] using
                InvariantRuns.ifZero htrialHasNext
                  (InvariantRuns.basic
                    (Basic.imm regs.guessActive 0) trial
                    htrialBound hstoppedBound)
            have hfinish :
                InvariantRuns
                  (MutableValuesWithin
                    (regs.footprint ∪ kernel.footprint) valueBits)
                  (finishTrial regs) trial stopped 3 := by
              simpa [finishTrial] using
                InvariantRuns.ifZero htrialSuccess hadvance
            have hbody :
                InvariantRuns
                  (MutableValuesWithin
                    (regs.footprint ∪ kernel.footprint) valueBits)
                  (guessBody regs kernel) store stopped
                  (trialSteps + 3) := by
              simpa [guessBody] using
                InvariantRuns.seq htrial hfinish
            have hstoppedActive :
                stopped regs.guessActive = 0 := by
              simp [stopped, Basic.exec]
            have hrest :
                InvariantRuns
                  (MutableValuesWithin
                    (regs.footprint ∪ kernel.footprint) valueBits)
                  (guessLoop regs kernel) stopped stopped 1 := by
              simpa [guessLoop] using
                InvariantRuns.whileZero hstoppedActive hstoppedBound
            refine ⟨stopped, (trialSteps + 3) + 1 + 2,
              ?_, Or.inr ?_⟩
            · simpa [guessLoop] using
                InvariantRuns.whileNonzero hactive hbody hrest
            · refine
                { inputFrame := hstoppedFrame
                  inputLength_eq := ?_
                  candidate_eq := ?_
                  prime_eq := ?_
                  all_none := ?_
                  success_eq := ?_
                  one_eq := ?_
                  guessActive_eq := hstoppedActive
                  candidateActive_eq := ?_ }
              · simpa [stopped, Basic.exec, regs.index_inj_iff] using
                  hpost.inputLength_eq.trans hinput
              · simpa [stopped, Basic.exec, regs.index_inj_iff] using
                  hpost.candidate_eq.trans hcandidate
              · simpa [stopped, Basic.exec,
                  upper_ne_outer regs 0 6 (by decide)] using
                  hpost.prime_eq.trans hprime
              · intro prior hprior
                by_cases hpriorGuess : prior < guess
                · exact hprevious prior hpriorGuess
                · have heq : prior = guess := by omega
                  simpa [heq] using hout
              · simpa [stopped, Basic.exec,
                  regs.index_inj_iff] using htrialSuccess
              · simpa [stopped, Basic.exec,
                  upper_ne_outer regs 6 6 (by decide)] using
                  hpost.one_eq.trans hone
              · simpa [stopped, Basic.exec,
                  regs.index_inj_iff] using
                  hpost.candidateActive_eq.trans hcandidateActive

private theorem candidateBody_invariantRuns
    (regs : Registers) (kernel : TrialKernel regs)
    (input : List Bool) (target targetGuess valueBits : ℕ)
    (targetVerdict : Bool)
    (htargetGuess :
      targetGuess < kernel.guessCount target)
    (htargetOutcome :
      kernel.outcome input target (firstPrimeAtOrAbove target)
        targetGuess = some targetVerdict)
    (henvelope :
      PrefixEnvelope regs kernel input target valueBits)
    (candidate : ℕ) (store : Store)
    (hcandidateUpper : candidate ≤ target)
    (hbound :
      MutableValuesWithin
        (regs.footprint ∪ kernel.footprint) valueBits store)
    (hinv :
      CandidateInv regs kernel input candidate store) :
    ∃ final steps,
      InvariantRuns
        (MutableValuesWithin
          (regs.footprint ∪ kernel.footprint) valueBits)
        (candidateBody regs kernel) store final steps ∧
      ((∃ verdict,
          CoreProgramPost regs kernel input verdict final ∧
            final regs.candidate = candidate) ∨
        (CandidateInv regs kernel input (candidate + 1) final ∧
          ∀ guess, guess < kernel.guessCount candidate →
            kernel.outcome input candidate
              (firstPrimeAtOrAbove candidate) guess = none)) := by
  let primed :=
    (Basic.mul regs.prime regs.candidate regs.one).exec store
  have hprimedValue :
      store regs.candidate * store regs.one = candidate := by
    rw [hinv.candidate_eq, hinv.one_eq, Nat.mul_one]
  have hprimedBound :
      MutableValuesWithin
        (regs.footprint ∪ kernel.footprint) valueBits primed := by
    apply mutableValuesWithin_mul hbound
    rw [hprimedValue]
    exact envelope_candidate_bitlen henvelope hcandidateUpper
  have hprimedFrame :
      InputFrame regs kernel.footprint input primed := by
    simpa [primed, Basic.exec] using
      controller_update_inputFrame regs kernel input hinv.inputFrame
        (Registers.primeSlot 0) (by decide)
        (store regs.candidate * store regs.one)
  have hinitializePrime :
      InvariantRuns
        (MutableValuesWithin
          (regs.footprint ∪ kernel.footprint) valueBits)
        (initializePrime regs) store primed 1 := by
    simpa [initializePrime, primed] using
      InvariantRuns.basic
        (Basic.mul regs.prime regs.candidate regs.one) store
        hbound hprimedBound
  have hprimedPrime :
      primed regs.prime = candidate := by
    simp [primed, Basic.exec, hinv.candidate_eq, hinv.one_eq]
  obtain ⟨selected, searchSteps, hsearch, hsearchPost⟩ :=
    henvelope.primeSearchInvariantRuns candidate primed
      hinv.candidate_ge hcandidateUpper hprimedPrime hprimedBound
  have hsearchRuns : Runs
      (PrimeSearch.search regs.primeRegisters) primed selected :=
    hsearch.toRuns
  have hselectedBound :
      MutableValuesWithin
        (regs.footprint ∪ kernel.footprint) valueBits selected :=
    hsearch.final
  have hselectedFrame :
      InputFrame regs kernel.footprint input selected :=
    primeSearch_preserves_inputFrame regs kernel input
      hprimedFrame hsearchRuns
  have hselectedInput :
      selected regs.inputLength = input.length := by
    calc
      selected regs.inputLength = primed regs.inputLength :=
        primeSearch_preserves_outer regs hsearchRuns 0 (by decide)
      _ = input.length := by
        simpa [primed, Basic.exec,
          (upper_ne_outer regs 0 0 (by decide)).symm] using
          hinv.inputLength_eq
  have hselectedCandidate :
      selected regs.candidate = candidate := by
    calc
      selected regs.candidate = primed regs.candidate :=
        primeSearch_preserves_outer regs hsearchRuns 1 (by decide)
      _ = candidate := by
        simpa [primed, Basic.exec,
          (upper_ne_outer regs 0 1 (by decide)).symm] using
          hinv.candidate_eq
  have hselectedCandidateActive :
      selected regs.candidateActive = 1 := by
    calc
      selected regs.candidateActive =
          primed regs.candidateActive :=
        primeSearch_preserves_outer regs hsearchRuns 7 (by decide)
      _ = 1 := by
        simpa [primed, Basic.exec,
          (upper_ne_outer regs 0 7 (by decide)).symm] using
          hinv.candidateActive_eq
  have hselectedPrime :
      selected regs.prime =
        firstPrimeAtOrAbove candidate :=
    firstPrime_unique hsearchPost.firstPrime
      (firstPrimeAtOrAbove_spec_internal candidate)
  let zeroGuess :=
    (Basic.imm regs.guess 0).exec selected
  let ready :=
    (Basic.imm regs.guessActive 1).exec zeroGuess
  have hzeroGuessBound :
      MutableValuesWithin
        (regs.footprint ∪ kernel.footprint) valueBits zeroGuess := by
    apply mutableValuesWithin_imm hselectedBound
    simpa [Input.bitValue] using control_bitlen henvelope false
  have hreadyBound :
      MutableValuesWithin
        (regs.footprint ∪ kernel.footprint) valueBits ready := by
    apply mutableValuesWithin_imm hzeroGuessBound
    simpa [Input.bitValue] using control_bitlen henvelope true
  have hzeroGuessFrame :
      InputFrame regs kernel.footprint input zeroGuess := by
    simpa [zeroGuess, Basic.exec] using
      controller_update_inputFrame regs kernel input hselectedFrame
        2 (by decide) 0
  have hreadyFrame :
      InputFrame regs kernel.footprint input ready := by
    simpa [ready, Basic.exec] using
      controller_update_inputFrame regs kernel input hzeroGuessFrame
        6 (by decide) 1
  have hinitializeGuesses :
      InvariantRuns
        (MutableValuesWithin
          (regs.footprint ∪ kernel.footprint) valueBits)
        (initializeGuesses regs) selected ready 2 := by
    simpa [initializeGuesses, zeroGuess, ready] using
      InvariantRuns.seq
        (InvariantRuns.basic (Basic.imm regs.guess 0) selected
          hselectedBound hzeroGuessBound)
        (InvariantRuns.basic (Basic.imm regs.guessActive 1)
          zeroGuess hzeroGuessBound hreadyBound)
  have hreadyInput :
      ready regs.inputLength = input.length := by
    simpa [ready, zeroGuess, Basic.exec,
      regs.index_inj_iff] using hselectedInput
  have hreadyCandidate :
      ready regs.candidate = candidate := by
    simpa [ready, zeroGuess, Basic.exec,
      regs.index_inj_iff] using hselectedCandidate
  have hreadyPrime :
      ready regs.prime =
        firstPrimeAtOrAbove candidate := by
    simpa [ready, zeroGuess, Basic.exec,
      upper_ne_outer regs 0 2 (by decide),
      upper_ne_outer regs 0 6 (by decide)] using hselectedPrime
  have hreadyGuess :
      ready regs.guess = 0 := by
    simp [ready, zeroGuess, Basic.exec, regs.index_inj_iff]
  have hreadyOne :
      ready regs.one = 1 := by
    simpa [ready, zeroGuess, Basic.exec,
      upper_ne_outer regs 6 2 (by decide),
      upper_ne_outer regs 6 6 (by decide)] using
      hsearchPost.one_eq
  have hreadyCandidateActive :
      ready regs.candidateActive = 1 := by
    simpa [ready, zeroGuess, Basic.exec,
      regs.index_inj_iff] using hselectedCandidateActive
  have hreadyGuessActive :
      ready regs.guessActive = 1 := by
    simp [ready, Basic.exec]
  obtain ⟨guessesFinal, guessSteps, hguesses, hguessResult⟩ :=
    guessLoop_invariantRuns regs kernel input target valueBits
      henvelope candidate (firstPrimeAtOrAbove candidate) 0 ready
      hinv.candidate_ge hcandidateUpper hreadyBound hreadyFrame
      hreadyInput hreadyCandidate hreadyPrime hreadyGuess hreadyOne
      hreadyCandidateActive hreadyGuessActive
      (kernel.guessCount_pos candidate)
      (by intro prior hprior; omega)
  have hguessesBound :
      MutableValuesWithin
        (regs.footprint ∪ kernel.footprint) valueBits
        guessesFinal :=
    hguesses.final
  rcases hguessResult with hsuccess | hexhausted
  · obtain ⟨verdict, hsuccess⟩ := hsuccess
    have hadvance :
        InvariantRuns
          (MutableValuesWithin
            (regs.footprint ∪ kernel.footprint) valueBits)
          (advanceCandidateOnFailure regs)
          guessesFinal guessesFinal 1 := by
      simpa [advanceCandidateOnFailure] using
        InvariantRuns.ifZero hsuccess.candidateActive_eq
          (InvariantRuns.skip guessesFinal hguessesBound)
    refine ⟨guessesFinal,
      1 + (searchSteps + (2 + (guessSteps + 1))),
      ?_, Or.inl ⟨verdict, ?_, hsuccess.candidate_eq⟩⟩
    · simpa [candidateBody] using
        InvariantRuns.seq hinitializePrime
          (InvariantRuns.seq hsearch
            (InvariantRuns.seq hinitializeGuesses
              (InvariantRuns.seq hguesses hadvance)))
    · refine
        { inputFrame := hsuccess.inputFrame
          inputLength_eq := hsuccess.inputLength_eq
          candidate_ge := ?_
          prime_eq := ?_
          guess_lt := ?_
          outcome_eq := ?_
          verdict_eq := hsuccess.verdict_eq
          success_eq := hsuccess.success_eq
          one_eq := hsuccess.one_eq
          guessActive_eq := hsuccess.guessActive_eq
          candidateActive_eq := hsuccess.candidateActive_eq }
      · simpa [hsuccess.candidate_eq] using hinv.candidate_ge
      · simpa [hsuccess.candidate_eq] using hsuccess.prime_eq
      · simpa [hsuccess.candidate_eq] using hsuccess.guess_lt
      · simpa [hsuccess.candidate_eq, hsuccess.prime_eq] using
          hsuccess.outcome_eq
  · by_cases heq : candidate = target
    · have hall :=
        hexhausted.all_none targetGuess (by
          simpa [heq] using htargetGuess)
      have hallTarget :
          kernel.outcome input target
            (firstPrimeAtOrAbove target) targetGuess = none := by
        simpa [heq] using hall
      exact False.elim
        ((Option.some_ne_none targetVerdict)
          (htargetOutcome.symm.trans
            hallTarget))
    · have hcandidateLt : candidate < target := by omega
      have hnextUpper : candidate + 1 ≤ target := by omega
      let advanced :=
        (Basic.add regs.candidate regs.candidate regs.one).exec
          guessesFinal
      have hadvancedValue :
          guessesFinal regs.candidate + guessesFinal regs.one =
            candidate + 1 := by
        rw [hexhausted.candidate_eq, hexhausted.one_eq]
      have hadvancedBound :
          MutableValuesWithin
            (regs.footprint ∪ kernel.footprint) valueBits
            advanced := by
        apply mutableValuesWithin_add hguessesBound
        rw [hadvancedValue]
        exact envelope_candidate_bitlen henvelope hnextUpper
      have hadvancedFrame :
          InputFrame regs kernel.footprint input advanced := by
        simpa [advanced, Basic.exec] using
          controller_update_inputFrame regs kernel input
            hexhausted.inputFrame 1 (by decide)
            (guessesFinal regs.candidate + guessesFinal regs.one)
      have hadvance :
          InvariantRuns
            (MutableValuesWithin
              (regs.footprint ∪ kernel.footprint) valueBits)
            (advanceCandidateOnFailure regs)
            guessesFinal advanced 3 := by
        simpa [advanceCandidateOnFailure, advanced] using
          InvariantRuns.ifNonzero
            (by
              rw [hexhausted.candidateActive_eq]
              omega)
            (InvariantRuns.basic
              (Basic.add regs.candidate regs.candidate regs.one)
              guessesFinal hguessesBound hadvancedBound)
      refine ⟨advanced,
        1 + (searchSteps + (2 + (guessSteps + 3))),
        ?_, Or.inr ⟨?_, hexhausted.all_none⟩⟩
      · simpa [candidateBody] using
          InvariantRuns.seq hinitializePrime
            (InvariantRuns.seq hsearch
              (InvariantRuns.seq hinitializeGuesses
                (InvariantRuns.seq hguesses hadvance)))
      · refine
          { inputFrame := hadvancedFrame
            inputLength_eq := ?_
            candidate_eq := ?_
            candidate_ge := ?_
            one_eq := ?_
            candidateActive_eq := ?_ }
        · simpa [advanced, Basic.exec,
            regs.index_inj_iff] using hexhausted.inputLength_eq
        · simp [advanced, Basic.exec, hexhausted.candidate_eq,
            hexhausted.one_eq]
        · exact hinv.candidate_ge.trans
            (Nat.le_add_right candidate 1)
        · simpa [advanced, Basic.exec,
            upper_ne_outer regs 6 1 (by decide)] using
            hexhausted.one_eq
        · simpa [advanced, Basic.exec,
            regs.index_inj_iff] using
            hexhausted.candidateActive_eq

private theorem candidateLoop_invariantRuns
    (regs : Registers) (kernel : TrialKernel regs)
    (input : List Bool)
    (target targetGuess valueBits : ℕ)
    (targetVerdict : Bool)
    (htargetGuess :
      targetGuess < kernel.guessCount target)
    (htargetOutcome :
      kernel.outcome input target (firstPrimeAtOrAbove target)
        targetGuess = some targetVerdict)
    (henvelope :
      PrefixEnvelope regs kernel input target valueBits)
    (candidate : ℕ) (store : Store)
    (hcandidateUpper : candidate ≤ target)
    (hbound :
      MutableValuesWithin
        (regs.footprint ∪ kernel.footprint) valueBits store)
    (hinv : CandidateInv regs kernel input candidate store) :
    ∃ final verdict steps,
      InvariantRuns
        (MutableValuesWithin
          (regs.footprint ∪ kernel.footprint) valueBits)
        (.whileNonzero regs.candidateActive
          (candidateBody regs kernel))
        store final steps ∧
      CoreProgramPost regs kernel input verdict final ∧
      final regs.candidate ≤ target := by
  generalize hgapEq : target - candidate = gap
  induction gap using Nat.strong_induction_on
      generalizing candidate store with
  | h gap ih =>
      have hactive : store regs.candidateActive ≠ 0 := by
        rw [hinv.candidateActive_eq]
        omega
      obtain ⟨next, bodySteps, hbody, hresult⟩ :=
        candidateBody_invariantRuns regs kernel input target
          targetGuess valueBits targetVerdict htargetGuess
          htargetOutcome henvelope candidate store
          hcandidateUpper hbound hinv
      have hnextBound :
          MutableValuesWithin
            (regs.footprint ∪ kernel.footprint) valueBits next :=
        hbody.final
      rcases hresult with hsuccess | hfailure
      · obtain ⟨verdict, hpost, hcandidateEq⟩ := hsuccess
        have hrest :
            InvariantRuns
              (MutableValuesWithin
                (regs.footprint ∪ kernel.footprint) valueBits)
              (.whileNonzero regs.candidateActive
                (candidateBody regs kernel))
              next next 1 :=
          InvariantRuns.whileZero hpost.candidateActive_eq
            hnextBound
        exact ⟨next, verdict, bodySteps + 1 + 2,
          InvariantRuns.whileNonzero hactive hbody hrest,
          hpost, by simpa [hcandidateEq] using hcandidateUpper⟩
      · obtain ⟨hnextInv, hallNone⟩ := hfailure
        have hcandidateLt : candidate < target := by
          by_cases heq : candidate = target
          · have hnone :=
              hallNone targetGuess (by
                simpa [heq] using htargetGuess)
            have hnoneTarget :
                kernel.outcome input target
                  (firstPrimeAtOrAbove target) targetGuess = none := by
              simpa [heq] using hnone
            exact False.elim
              ((Option.some_ne_none targetVerdict)
                (htargetOutcome.symm.trans hnoneTarget))
          · omega
        have hnextUpper : candidate + 1 ≤ target := by omega
        have hnextGap :
            target - (candidate + 1) < gap := by
          omega
        obtain ⟨final, verdict, restSteps, hrest, hpost,
            hfinalUpper⟩ :=
          ih (target - (candidate + 1)) hnextGap
            (candidate + 1) next hnextUpper hnextBound hnextInv rfl
        exact ⟨final, verdict, bodySteps + restSteps + 2,
          InvariantRuns.whileNonzero hactive hbody hrest,
          hpost, hfinalUpper⟩

theorem program_invariantRuns_bounded_candidate_internal
    (regs : Registers) (kernel : TrialKernel regs)
    (input : List Bool) (target valueBits : ℕ)
    (targetVerdict : Bool)
    (htarget : input.length ≤ target)
    (hreturns :
      CandidateReturns kernel input target targetVerdict)
    (henvelope :
      PrefixEnvelope regs kernel input target valueBits) :
    ∃ final verdict steps,
      InvariantRuns
        (MutableValuesWithin
          (regs.footprint ∪ kernel.footprint) valueBits)
        (program regs kernel) (RAM.initRegs input) final steps ∧
      ProgramPost regs kernel input verdict final ∧
      final regs.candidate ≤ target := by
  obtain ⟨targetGuess, htargetGuess, htargetOutcome⟩ := hreturns
  let limit := footprintLimit regs kernel.footprint
  obtain ⟨cached, cacheSteps, hcache, hcachedFrame⟩ :=
    henvelope.cacheInvariantRuns
  have hcachedBound :
      MutableValuesWithin
        (regs.footprint ∪ kernel.footprint) valueBits cached :=
    hcache.final
  have hcacheRuns :
      Runs (cacheInputPrefix regs limit)
        (RAM.initRegs input) cached := by
    simpa [limit] using hcache.toRuns
  have hcachedInput :
      cached regs.inputLength = input.length := by
    have hpreserved :=
      runs_preserves_outside
        (cacheInputPrefix_writesWithin regs limit) hcacheRuns
        (index := regs.inputLength)
    calc
      cached regs.inputLength =
          RAM.initRegs input regs.inputLength := by
        apply hpreserved
        simp only [Finset.mem_singleton]
        exact regs.index_ne (by decide)
      _ = input.length := by
        simp [regs.inputLength_zero, RAM.initRegs]
  let oned :=
    (Basic.imm regs.one 1).exec cached
  let candidateSet :=
    (Basic.mul regs.candidate regs.inputLength regs.one).exec
      oned
  let ready :=
    (Basic.imm regs.candidateActive 1).exec candidateSet
  have honedBound :
      MutableValuesWithin
        (regs.footprint ∪ kernel.footprint) valueBits oned := by
    apply mutableValuesWithin_imm hcachedBound
    simpa [Input.bitValue] using control_bitlen henvelope true
  have honedInput :
      oned regs.inputLength = input.length := by
    simpa [oned, Basic.exec,
      (upper_ne_outer regs 6 0 (by decide)).symm] using
      hcachedInput
  have honedOne : oned regs.one = 1 := by
    simp [oned, Basic.exec]
  have hcandidateSetValue :
      oned regs.inputLength * oned regs.one = input.length := by
    rw [honedInput, honedOne, Nat.mul_one]
  have hcandidateSetBound :
      MutableValuesWithin
        (regs.footprint ∪ kernel.footprint) valueBits
        candidateSet := by
    apply mutableValuesWithin_mul honedBound
    rw [hcandidateSetValue]
    exact envelope_candidate_bitlen henvelope htarget
  have hreadyBound :
      MutableValuesWithin
        (regs.footprint ∪ kernel.footprint) valueBits ready := by
    apply mutableValuesWithin_imm hcandidateSetBound
    simpa [Input.bitValue] using control_bitlen henvelope true
  have honedFrame :
      InputFrame regs kernel.footprint input oned := by
    simpa [oned, Basic.exec] using
      controller_update_inputFrame regs kernel input hcachedFrame
        (Registers.primeSlot 6) (by decide) 1
  have hcandidateSetFrame :
      InputFrame regs kernel.footprint input candidateSet := by
    simpa [candidateSet, Basic.exec] using
      controller_update_inputFrame regs kernel input honedFrame
        1 (by decide)
        (oned regs.inputLength * oned regs.one)
  have hreadyFrame :
      InputFrame regs kernel.footprint input ready := by
    simpa [ready, Basic.exec] using
      controller_update_inputFrame regs kernel input
        hcandidateSetFrame 7 (by decide) 1
  have hsetup :
      InvariantRuns
        (MutableValuesWithin
          (regs.footprint ∪ kernel.footprint) valueBits)
        (setup regs) cached ready 3 := by
    simpa [setup, Cmd.seqList, oned, candidateSet, ready] using
      InvariantRuns.seq
        (InvariantRuns.basic (Basic.imm regs.one 1) cached
          hcachedBound honedBound)
        (InvariantRuns.seq
          (InvariantRuns.basic
            (Basic.mul regs.candidate regs.inputLength regs.one)
            oned honedBound hcandidateSetBound)
          (InvariantRuns.basic
            (Basic.imm regs.candidateActive 1) candidateSet
            hcandidateSetBound hreadyBound))
  have hreadyInv :
      CandidateInv regs kernel input input.length ready := by
    constructor
    · exact hreadyFrame
    · simpa [ready, candidateSet, oned, Basic.exec,
        regs.index_inj_iff,
        (upper_ne_outer regs 6 0 (by decide)).symm] using
          hcachedInput
    · simp [ready, candidateSet, oned, Basic.exec,
        regs.index_inj_iff,
        (upper_ne_outer regs 6 0 (by decide)).symm,
        hcachedInput]
    · exact le_refl input.length
    · simp [ready, candidateSet, oned, Basic.exec,
        upper_ne_outer regs 6 1 (by decide),
        upper_ne_outer regs 6 7 (by decide)]
    · simp [ready, Basic.exec]
  obtain ⟨coreFinal, verdict, loopSteps, hloop, hpost, hbound⟩ :=
    candidateLoop_invariantRuns regs kernel input target
      targetGuess valueBits targetVerdict htargetGuess
      htargetOutcome henvelope input.length ready htarget
      hreadyBound hreadyInv
  have hcoreBound :
      MutableValuesWithin
        (regs.footprint ∪ kernel.footprint) valueBits coreFinal :=
    hloop.final
  have hcore :
      InvariantRuns
        (MutableValuesWithin
          (regs.footprint ∪ kernel.footprint) valueBits)
        (coreProgram regs kernel) (RAM.initRegs input) coreFinal
        (cacheSteps + (3 + loopSteps)) := by
    simpa [coreProgram, limit] using
      InvariantRuns.seq hcache (InvariantRuns.seq hsetup hloop)
  let final :=
    (Basic.mul regs.inputLength regs.verdict regs.one).exec coreFinal
  have hpublishValue :
      coreFinal regs.verdict * coreFinal regs.one =
        Input.bitValue verdict := by
    rw [hpost.verdict_eq, hpost.one_eq, Nat.mul_one]
  have hfinalBound :
      MutableValuesWithin
        (regs.footprint ∪ kernel.footprint) valueBits final := by
    apply mutableValuesWithin_mul hcoreBound
    rw [hpublishValue]
    exact control_bitlen henvelope verdict
  have hpublish :
      InvariantRuns
        (MutableValuesWithin
          (regs.footprint ∪ kernel.footprint) valueBits)
        (publishVerdict regs) coreFinal final 1 := by
    simpa [publishVerdict, final] using
      InvariantRuns.basic
        (Basic.mul regs.inputLength regs.verdict regs.one)
        coreFinal hcoreBound hfinalBound
  have hfinalFrame :
      InputFrame regs kernel.footprint input final := by
    simpa [final, Basic.exec] using
      controller_update_inputFrame regs kernel input
        hpost.inputFrame 0 (by decide)
        (coreFinal regs.verdict * coreFinal regs.one)
  refine ⟨final, verdict, cacheSteps + (3 + loopSteps) + 1,
    ?_, ?_, ?_⟩
  · simpa [program] using InvariantRuns.seq hcore hpublish
  · refine
      { inputFrame := hfinalFrame
        output_eq := ?_
        candidate_ge := ?_
        prime_eq := ?_
        guess_lt := ?_
        outcome_eq := ?_
        verdict_eq := ?_
        success_eq := ?_
        one_eq := ?_
        guessActive_eq := ?_
        candidateActive_eq := ?_ }
    · simp [final, Basic.exec, hpost.verdict_eq, hpost.one_eq]
    · simpa [final, Basic.exec, regs.index_inj_iff] using
        hpost.candidate_ge
    · simpa [final, Basic.exec,
        (regs.index_ne (by decide : (0 : Fin 17) ≠ 1)).symm,
        upper_ne_outer regs 0 0 (by decide)] using hpost.prime_eq
    · simpa [final, Basic.exec, regs.index_inj_iff] using
        hpost.guess_lt
    · simpa [final, Basic.exec, regs.index_inj_iff,
        upper_ne_outer regs 0 0 (by decide)] using
        hpost.outcome_eq
    · simpa [final, Basic.exec, regs.index_inj_iff] using
        hpost.verdict_eq
    · simpa [final, Basic.exec, regs.index_inj_iff] using
        hpost.success_eq
    · simpa [final, Basic.exec,
        upper_ne_outer regs 6 0 (by decide)] using
        hpost.one_eq
    · simpa [final, Basic.exec, regs.index_inj_iff] using
        hpost.guessActive_eq
    · simpa [final, Basic.exec, regs.index_inj_iff] using
        hpost.candidateActive_eq
  · simpa [final, Basic.exec, regs.index_inj_iff] using hbound

theorem compiledWritesWithin_internal
    (regs : Registers) (kernel : TrialKernel regs) :
    RAM.RegisterStore.DenseOverlay.FixedRegisters.Footprint.ProgramWritesWithin
      (program regs kernel).compile
      (regs.footprint ∪ kernel.footprint) :=
  RAM.Structured.Footprint.programWritesWithin_compile
    (sourceWritesWithin_internal regs kernel)

theorem traceBound_internal
    (regs : Registers) (kernel : TrialKernel regs)
    (input : List Bool) (fuel valueBits : ℕ)
    (hcode :
      bitlen (program regs kernel).codeSize ≤ valueBits + 1)
    (hcount :
      bitlen (regs.footprint ∪ kernel.footprint).card ≤
        valueBits + 1)
    (haddresses :
      ∀ address ∈ regs.footprint ∪ kernel.footprint,
        bitlen address ≤ valueBits + 1)
    (hvalues :
      CompiledPrefixValueBound regs kernel input fuel valueBits) :
    RAM.RegisterStore.DenseOverlay.FixedRegisters.TraceBound
      (program regs kernel).compile input fuel
      (regs.footprint ∪ kernel.footprint).card
      (valueBits + 1) := by
  apply RAM.Structured.Footprint.traceBound_compile
    (sourceWritesWithin_internal regs kernel)
  · have hmember :
        regs.inputLength ∈ regs.footprint ∪ kernel.footprint :=
      Finset.mem_union_left _
        (regs.index_mem_footprint 0)
    simpa [regs.inputLength_zero] using hmember
  · exact hcode
  · exact hcount
  · exact haddresses
  · exact hvalues

theorem traceBound_of_invariantRun_internal
    (regs : Registers) (kernel : TrialKernel regs)
    (input : List Bool) (valueBits steps : ℕ)
    {final : Store}
    (hrun :
      InvariantRuns
        (MutableValuesWithin
          (regs.footprint ∪ kernel.footprint) valueBits)
        (program regs kernel) (RAM.initRegs input) final steps)
    (hcode :
      bitlen (program regs kernel).codeSize ≤ valueBits + 1)
    (hcount :
      bitlen (regs.footprint ∪ kernel.footprint).card ≤
        valueBits + 1)
    (haddresses :
      ∀ address ∈ regs.footprint ∪ kernel.footprint,
        bitlen address ≤ valueBits + 1) :
    RAM.RegisterStore.DenseOverlay.FixedRegisters.TraceBound
      (program regs kernel).compile input steps
      (regs.footprint ∪ kernel.footprint).card
      (valueBits + 1) := by
  apply traceBound_internal regs kernel input steps valueBits
    hcode hcount haddresses
  intro k hk address haddress
  exact RAM.Structured.InvariantRuns.compile_prefix hrun hk
    address haddress

theorem programPost_candidate_bitlen_le_internal
    (regs : Registers) (store : Store)
    {target : ℕ} (hupper : store regs.candidate ≤ target) :
    bitlen (store regs.candidate) ≤ bitlen target := by
  simpa [bitlen] using Nat.size_le_size hupper

theorem programPost_prime_bitlen_le_internal
    (hpost : ProgramPost regs kernel input verdict store)
    (hcandidate : 0 < store regs.candidate) :
    bitlen (store regs.prime) ≤
      bitlen (store regs.candidate) + 1 := by
  rw [hpost.prime_eq]
  exact firstPrimeAtOrAbove_bitlen_le_internal
    (store regs.candidate) hcandidate

theorem programPost_prime_bitlen_le_target_internal
    (hpost : ProgramPost regs kernel input verdict store)
    {target : ℕ} (hupper : store regs.candidate ≤ target)
    (hinput : 0 < input.length) :
    bitlen (store regs.prime) ≤ bitlen target + 1 := by
  apply (programPost_prime_bitlen_le_internal hpost
    (lt_of_lt_of_le hinput hpost.candidate_ge)).trans
  exact Nat.add_le_add_right
    (programPost_candidate_bitlen_le_internal regs store hupper) 1

theorem programPost_guess_bitlen_le_internal
    (hpost : ProgramPost regs kernel input verdict store) :
    bitlen (store regs.guess) ≤
      bitlen (kernel.guessCount (store regs.candidate)) := by
  simpa [bitlen] using
    Nat.size_le_size (Nat.le_of_lt hpost.guess_lt)

theorem programPost_candidateReturns_internal
    (hpost : ProgramPost regs kernel input verdict store) :
    CandidateReturns kernel input (store regs.candidate) verdict := by
  refine ⟨store regs.guess, hpost.guess_lt, ?_⟩
  simpa [hpost.prime_eq] using hpost.outcome_eq

theorem programPost_sound_internal
    {Good : Bool → Prop}
    (hkernel :
      ∀ candidate prime guess result,
        kernel.outcome input candidate prime guess = some result →
          Good result)
    (hpost : ProgramPost regs kernel input verdict store) :
    Good verdict :=
  hkernel (store regs.candidate) (store regs.prime)
    (store regs.guess) verdict hpost.outcome_eq

end Internal

end SearchProgram

end Runtime

end TimeSpaceSimulation

end Complexity
