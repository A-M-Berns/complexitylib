/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.SourceValue.Defs
import Complexitylib.Models.RandomAccessMachine.Structured.Footprint
import Complexitylib.TimeSpaceSimulation.BlockRespecting
import Complexitylib.TimeSpaceSimulation.Runtime.InputLookup
import Complexitylib.TimeSpaceSimulation.Runtime.CandidateParameters.Bounds
import
  Complexitylib.TimeSpaceSimulation.Runtime.CandidateParameters.RadixBounds
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.Layout
import Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodProgram
import Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodTrial
import Complexitylib.TimeSpaceSimulation.NeighborhoodExecutableEvaluation

/-!
# Correctness internals for concrete source-leaf values
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace SourceValue
namespace Internal

open RAM Structured
open TreeEval CookMertz
open NeighborhoodExecutableEvaluation

private theorem basics_runs
    (ops : List Basic) (store : Store) :
    Runs (Cmd.basics ops) store (Basic.execList ops store) := by
  obtain ⟨cost, space, hexec⟩ :=
    RAM.Structured.Internal.exec_basics_exists ops store
  exact ⟨ops.length, cost, space, hexec⟩

private theorem valuesWithin_sup
    (allowed : Finset ℕ) (store : Store) :
    NeighborhoodProgram.ValuesWithin allowed
      (allowed.sup store) store := by
  intro address haddress
  exact Finset.le_sup haddress

private theorem valuesWithin_update
    (allowed : Finset ℕ) (bound address value : ℕ)
    (store : Store)
    (hstore :
      NeighborhoodProgram.ValuesWithin allowed bound store)
    (hvalue : value ≤ bound) :
    NeighborhoodProgram.ValuesWithin allowed bound
      (Function.update store address value) := by
  intro current hcurrent
  by_cases heq : current = address
  · subst current
    simp [hvalue]
  · simpa [Function.update_of_ne, heq] using
      hstore current hcurrent

private theorem imm_invariantRuns
    (allowed : Finset ℕ) (bound destination value : ℕ)
    (store : Store)
    (hstore :
      NeighborhoodProgram.ValuesWithin allowed bound store)
    (hvalue : value ≤ bound) :
    InvariantRuns
      (NeighborhoodProgram.ValuesWithin allowed bound)
      (.basic (.imm destination value)) store
      (Basic.exec (.imm destination value) store) 1 := by
  exact
    InvariantRuns.basic (.imm destination value) store hstore
      (valuesWithin_update allowed bound destination value store
        hstore hvalue)

private theorem add_invariantRuns
    (allowed : Finset ℕ) (bound destination left right : ℕ)
    (store : Store)
    (hstore :
      NeighborhoodProgram.ValuesWithin allowed bound store)
    (hvalue : store left + store right ≤ bound) :
    InvariantRuns
      (NeighborhoodProgram.ValuesWithin allowed bound)
      (.basic (.add destination left right)) store
      (Basic.exec (.add destination left right) store) 1 := by
  exact
    InvariantRuns.basic (.add destination left right) store hstore
      (valuesWithin_update allowed bound destination
        (store left + store right) store hstore hvalue)

private theorem sub_invariantRuns
    (allowed : Finset ℕ) (bound destination left right : ℕ)
    (store : Store)
    (hstore :
      NeighborhoodProgram.ValuesWithin allowed bound store)
    (hleft : store left ≤ bound) :
    InvariantRuns
      (NeighborhoodProgram.ValuesWithin allowed bound)
      (.basic (.sub destination left right)) store
      (Basic.exec (.sub destination left right) store) 1 := by
  exact
    InvariantRuns.basic (.sub destination left right) store hstore
      (valuesWithin_update allowed bound destination
        (store left - store right) store hstore
        ((Nat.sub_le _ _).trans hleft))

private theorem mul_invariantRuns
    (allowed : Finset ℕ) (bound destination left right : ℕ)
    (store : Store)
    (hstore :
      NeighborhoodProgram.ValuesWithin allowed bound store)
    (hvalue : store left * store right ≤ bound) :
    InvariantRuns
      (NeighborhoodProgram.ValuesWithin allowed bound)
      (.basic (.mul destination left right)) store
      (Basic.exec (.mul destination left right) store) 1 := by
  exact
    InvariantRuns.basic (.mul destination left right) store hstore
      (valuesWithin_update allowed bound destination
        (store left * store right) store hstore hvalue)

private theorem numericCap_iff_size
    (value width : ℕ) :
    value ≤ 2 ^ width - 1 ↔ Nat.size value ≤ width := by
  rw [Nat.size_le]
  have hpositive : 0 < 2 ^ width := Nat.two_pow_pos width
  omega

theorem sourceTransientValueBound_bitlen_le_trialEnvelope_internal
    (tm : TM workTapeCount) (candidate : ℕ) :
    bitlen (sourceTransientValueBound tm candidate) ≤
      NeighborhoodProgram.fixedRegisterCount *
        NeighborhoodGraph.WorkspaceAccounting.trialEnvelopeBits
          tm.Q workTapeCount candidate := by
  let width :=
    NeighborhoodProgram.fixedRegisterCount *
      NeighborhoodGraph.WorkspaceAccounting.trialEnvelopeBits
        tm.Q workTapeCount candidate
  change Nat.size (2 ^ width - 1) ≤ width
  exact (numericCap_iff_size (2 ^ width - 1) width).1 le_rfl

private theorem canonicalDomainSquare_le_sourceTransientValueBound
    (tm : TM workTapeCount) (candidate : ℕ) :
    16 *
        (CandidateParameters.domainSize
          tm.Q workTapeCount candidate) ^ 2 ≤
      sourceTransientValueBound tm candidate := by
  let envelope :=
    NeighborhoodGraph.WorkspaceAccounting.trialEnvelopeBits
      tm.Q workTapeCount candidate
  let chunkBits :=
    NeighborhoodGraph.WorkspaceAccounting.chunkBits
      tm.Q workTapeCount candidate
  let width := NeighborhoodProgram.fixedRegisterCount * envelope
  change
    16 *
        (CandidateParameters.domainSize
          tm.Q workTapeCount candidate) ^ 2 ≤
      2 ^ width - 1
  have henvelopePositive : 0 < envelope :=
    (NeighborhoodGraph.WorkspaceAccounting.blockLength_pos
      candidate).trans_le
      (NeighborhoodGraph.WorkspaceAccounting.blockLength_le_trialEnvelope
        tm.Q workTapeCount candidate)
  have hchunkScratch :
      chunkBits ≤
        NeighborhoodGraph.WorkspaceAccounting.scratchBits
          tm.Q workTapeCount candidate := by
    simp only
      [NeighborhoodGraph.WorkspaceAccounting.scratchBits]
    omega
  have hscratchTotal :
      NeighborhoodGraph.WorkspaceAccounting.scratchBits
          tm.Q workTapeCount candidate ≤
        NeighborhoodGraph.WorkspaceAccounting.totalBits
          tm.Q workTapeCount candidate := by
    simp only [NeighborhoodGraph.WorkspaceAccounting.totalBits]
    omega
  have htotalEnvelope :
      NeighborhoodGraph.WorkspaceAccounting.totalBits
          tm.Q workTapeCount candidate ≤
        envelope := by
    simpa [envelope] using
      NeighborhoodGraph.WorkspaceAccounting.totalBits_le_trialEnvelope
        tm.Q workTapeCount
        (show candidate ≤ candidate from le_rfl)
  have hchunk : chunkBits ≤ envelope :=
    hchunkScratch.trans (hscratchTotal.trans htotalEnvelope)
  have hexponent : 4 + chunkBits * 2 < width := by
    simp only [width, NeighborhoodProgram.fixedRegisterCount]
    omega
  have hpow : 2 ^ (4 + chunkBits * 2) < 2 ^ width :=
    Nat.pow_lt_pow_right (by omega) hexponent
  have hdomain :
      CandidateParameters.domainSize
          tm.Q workTapeCount candidate =
        2 ^ chunkBits := by
    rfl
  rw [hdomain]
  have hid :
      16 * (2 ^ chunkBits) ^ 2 =
        2 ^ (4 + chunkBits * 2) := by
    rw [show 16 = 2 ^ 4 by norm_num, ← pow_mul, ← pow_add]
  rw [hid]
  omega

private theorem candidate_le_sourceTransientValueBound
    (tm : TM workTapeCount) (candidate : ℕ) :
    candidate ≤ sourceTransientValueBound tm candidate := by
  let width :=
    NeighborhoodProgram.fixedRegisterCount *
      NeighborhoodGraph.WorkspaceAccounting.trialEnvelopeBits
        tm.Q workTapeCount candidate
  have hbounds :=
    CandidateParameters.Internal.parameterValueBounds_internal
      tm.Q workTapeCount
      (show candidate ≤ candidate from le_rfl)
  apply (numericCap_iff_size candidate width).2
  simpa [width, CandidateParameters.Internal.valueWidth] using
    hbounds.candidate_size

private theorem succ_le_two_pow (value : ℕ) :
    value + 1 ≤ 2 ^ value := by
  induction value with
  | zero =>
      norm_num
  | succ value ih =>
      rw [pow_succ]
      omega

set_option maxRecDepth 100000 in
private theorem canonical_footprintLimit :
    SearchProgram.footprintLimit
        SearchProgram.Registers.canonical
        NeighborhoodTrial.Registers.canonical.footprint =
      50 := by
  decide

private theorem canonical_addressCapacity
    (tm : TM workTapeCount) (candidate : ℕ) :
    2 ^
        SearchProgram.footprintLimit
          SearchProgram.Registers.canonical
          NeighborhoodTrial.Registers.canonical.footprint ≤
      sourceTransientValueBound tm candidate := by
  rw [canonical_footprintLimit]
  have hblock :=
    NeighborhoodGraph.WorkspaceAccounting.blockLength_pos candidate
  have hcoefficient :
      32 ≤
        NeighborhoodGraph.WorkspaceAccounting.workspaceCoefficient
          tm.Q workTapeCount := by
    simp only [
      NeighborhoodGraph.WorkspaceAccounting.workspaceCoefficient]
    omega
  have henvelope :
      2 ≤
        NeighborhoodGraph.WorkspaceAccounting.trialEnvelopeBits
          tm.Q workTapeCount candidate := by
    unfold
      NeighborhoodGraph.WorkspaceAccounting.trialEnvelopeBits
    nlinarith
  let width :=
    NeighborhoodProgram.fixedRegisterCount *
      NeighborhoodGraph.WorkspaceAccounting.trialEnvelopeBits
        tm.Q workTapeCount candidate
  have hwidth : 50 < width := by
    simp only [width, NeighborhoodProgram.fixedRegisterCount]
    omega
  have hpow : 2 ^ 50 < 2 ^ width :=
    Nat.pow_lt_pow_right (by omega) hwidth
  change 2 ^ 50 ≤ 2 ^ width - 1
  omega

private theorem invariantRuns_mono
    {invariant stronger : Store → Prop}
    (himp : ∀ store, invariant store → stronger store)
    {command : Cmd} {initial final : Store} {steps : ℕ}
    (hrun :
      InvariantRuns invariant command initial final steps) :
    InvariantRuns stronger command initial final steps := by
  induction hrun with
  | skip store hstore =>
      exact InvariantRuns.skip store (himp store hstore)
  | basic op store hstore hnext =>
      exact InvariantRuns.basic op store
        (himp store hstore) (himp _ hnext)
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

private theorem exec_deterministic
    {command : Cmd} {initial firstFinal secondFinal : Store}
    {firstSteps secondSteps firstCost secondCost
      firstSpace secondSpace : ℕ}
    (hfirst :
      Exec command initial firstFinal firstSteps
        firstCost firstSpace)
    (hsecond :
      Exec command initial secondFinal secondSteps
        secondCost secondSpace) :
    firstFinal = secondFinal ∧ firstSteps = secondSteps := by
  induction hfirst generalizing secondFinal secondSteps secondCost
      secondSpace with
  | skip store =>
      cases hsecond
      exact ⟨rfl, rfl⟩
  | basic op store =>
      cases hsecond
      exact ⟨rfl, rfl⟩
  | seq hfirstLeft hfirstRight ihLeft ihRight =>
      cases hsecond with
      | seq hsecondLeft hsecondRight =>
          obtain ⟨hmiddle, hleftSteps⟩ :=
            ihLeft hsecondLeft
          subst hmiddle
          obtain ⟨hfinal, hrightSteps⟩ :=
            ihRight hsecondRight
          exact ⟨hfinal, by omega⟩
  | ifZero htest hbranch ih =>
      cases hsecond with
      | ifZero _ hsecondBranch =>
          obtain ⟨hfinal, hsteps⟩ := ih hsecondBranch
          exact ⟨hfinal, by omega⟩
      | ifNonzero hnonzero _ =>
          exact (hnonzero htest).elim
  | ifNonzero htest hbranch ih =>
      cases hsecond with
      | ifZero hzero _ =>
          exact (htest hzero).elim
      | ifNonzero _ hsecondBranch =>
          obtain ⟨hfinal, hsteps⟩ := ih hsecondBranch
          exact ⟨hfinal, by omega⟩
  | whileZero htest =>
      cases hsecond with
      | whileZero _ =>
          exact ⟨rfl, rfl⟩
      | whileNonzero hnonzero _ _ =>
          exact (hnonzero htest).elim
  | whileNonzero htest hbody hloop ihBody ihLoop =>
      cases hsecond with
      | whileZero hzero =>
          exact (htest hzero).elim
      | whileNonzero _ hsecondBody hsecondLoop =>
          obtain ⟨hmiddle, hbodySteps⟩ :=
            ihBody hsecondBody
          subst hmiddle
          obtain ⟨hfinal, hloopSteps⟩ :=
            ihLoop hsecondLoop
          exact ⟨hfinal, by omega⟩

private theorem runs_final_eq
    {command : Cmd} {initial firstFinal secondFinal : Store}
    (hfirst : Runs command initial firstFinal)
    (hsecond : Runs command initial secondFinal) :
    firstFinal = secondFinal := by
  obtain ⟨firstSteps, firstCost, firstSpace, hfirst⟩ := hfirst
  obtain ⟨secondSteps, secondCost, secondSpace, hsecond⟩ := hsecond
  exact (exec_deterministic hfirst hsecond).1

private theorem exec_exists_valuesWithin_invariantRuns
    (allowed : Finset ℕ)
    {command : Cmd} {initial final : Store}
    {steps cost space : ℕ}
    (hexec : Exec command initial final steps cost space) :
    ∃ bound,
      InvariantRuns
        (NeighborhoodProgram.ValuesWithin allowed bound)
        command initial final steps := by
  induction hexec with
  | skip store =>
      exact
        ⟨allowed.sup store,
          InvariantRuns.skip store (valuesWithin_sup allowed store)⟩
  | basic op store =>
      let bound :=
        max (allowed.sup store) (allowed.sup (op.exec store))
      have hinitial :
          NeighborhoodProgram.ValuesWithin allowed bound store := by
        intro address haddress
        exact le_trans
          (valuesWithin_sup allowed store address haddress)
          (le_max_left _ _)
      have hfinal :
          NeighborhoodProgram.ValuesWithin allowed bound
            (op.exec store) := by
        intro address haddress
        exact le_trans
          (valuesWithin_sup allowed (op.exec store) address haddress)
          (le_max_right _ _)
      exact
        ⟨bound, InvariantRuns.basic op store hinitial hfinal⟩
  | seq hfirst hsecond ihFirst ihSecond =>
      obtain ⟨firstBound, hfirstInvariant⟩ := ihFirst
      obtain ⟨secondBound, hsecondInvariant⟩ := ihSecond
      let bound := max firstBound secondBound
      have hfirst :
          InvariantRuns
            (NeighborhoodProgram.ValuesWithin allowed bound)
            _ _ _ _ :=
        invariantRuns_mono
          (fun store hstore address haddress =>
            le_trans (hstore address haddress)
              (le_max_left _ _))
          hfirstInvariant
      have hsecond :
          InvariantRuns
            (NeighborhoodProgram.ValuesWithin allowed bound)
            _ _ _ _ :=
        invariantRuns_mono
          (fun store hstore address haddress =>
            le_trans (hstore address haddress)
              (le_max_right _ _))
          hsecondInvariant
      exact ⟨bound, InvariantRuns.seq hfirst hsecond⟩
  | ifZero htest hbranch ih =>
      obtain ⟨bound, hbranchInvariant⟩ := ih
      exact
        ⟨bound, InvariantRuns.ifZero htest hbranchInvariant⟩
  | ifNonzero htest hbranch ih =>
      obtain ⟨bound, hbranchInvariant⟩ := ih
      exact
        ⟨bound, InvariantRuns.ifNonzero htest hbranchInvariant⟩
  | whileZero htest =>
      exact
        ⟨allowed.sup _,
          InvariantRuns.whileZero htest
            (valuesWithin_sup allowed _)⟩
  | whileNonzero htest hbody hloop ihBody ihLoop =>
      obtain ⟨bodyBound, hbodyInvariant⟩ := ihBody
      obtain ⟨loopBound, hloopInvariant⟩ := ihLoop
      let bound := max bodyBound loopBound
      have hbody' :
          InvariantRuns
            (NeighborhoodProgram.ValuesWithin allowed bound)
            _ _ _ _ :=
        invariantRuns_mono
          (fun store hstore address haddress =>
            le_trans (hstore address haddress)
              (le_max_left _ _))
          hbodyInvariant
      have hloop' :
          InvariantRuns
            (NeighborhoodProgram.ValuesWithin allowed bound)
            _ _ _ _ :=
        invariantRuns_mono
          (fun store hstore address haddress =>
            le_trans (hstore address haddress)
              (le_max_right _ _))
          hloopInvariant
      exact
        ⟨bound,
          InvariantRuns.whileNonzero htest hbody' hloop'⟩

private theorem runs_exists_valuesWithin_invariantRuns
    (allowed : Finset ℕ) (lowerBound : ℕ)
    {command : Cmd} {initial final : Store}
    (hrun : Runs command initial final) :
    ∃ bound steps,
      lowerBound ≤ bound ∧
      InvariantRuns
        (NeighborhoodProgram.ValuesWithin allowed bound)
        command initial final steps := by
  obtain ⟨steps, cost, space, hexec⟩ := hrun
  obtain ⟨executionBound, hinvariant⟩ :=
    exec_exists_valuesWithin_invariantRuns allowed hexec
  let bound := max lowerBound executionBound
  refine ⟨bound, steps, le_max_left _ _, ?_⟩
  exact invariantRuns_mono
    (fun store hstore address haddress =>
      le_trans (hstore address haddress)
        (le_max_right _ _))
    hinvariant

private theorem copy_runs
    {destination source : ℕ} (store : Store)
    (hne : destination ≠ source) :
    Runs (copy destination source) store
      (Function.update store destination (store source)) := by
  apply Runs.seq (Runs.basic (.imm destination 0) store)
  simpa [copy, Basic.exec, Function.update_of_ne,
    hne, Ne.symm hne] using
    Runs.basic
      (.add destination source destination)
      (Basic.exec (.imm destination 0) store)

private theorem copy_invariantRuns
    (allowed : Finset ℕ) (bound destination source : ℕ)
    (store : Store) (hne : destination ≠ source)
    (hsourceBound : store source ≤ bound)
    (hstore :
      NeighborhoodProgram.ValuesWithin allowed bound store) :
    InvariantRuns
      (NeighborhoodProgram.ValuesWithin allowed bound)
      (copy destination source) store
      (Function.update store destination (store source)) 2 := by
  let zeroed := Basic.exec (.imm destination 0) store
  have hzeroed :
      NeighborhoodProgram.ValuesWithin allowed bound zeroed :=
    valuesWithin_update allowed bound destination 0 store
      hstore (by omega)
  have hzeroedSource : zeroed source = store source := by
    simp [zeroed, Basic.exec, Ne.symm hne]
  have hzeroedDestination : zeroed destination = 0 := by
    simp [zeroed, Basic.exec]
  have hfinal :
      NeighborhoodProgram.ValuesWithin allowed bound
        (Function.update store destination (store source)) :=
    valuesWithin_update allowed bound destination
      (store source) store hstore hsourceBound
  have hexec :
      Basic.exec (.add destination source destination) zeroed =
        Function.update store destination (store source) := by
    simp [zeroed, Basic.exec, Ne.symm hne]
  have hsecond :
      InvariantRuns
        (NeighborhoodProgram.ValuesWithin allowed bound)
        (.basic (.add destination source destination))
        zeroed
        (Basic.exec (.add destination source destination) zeroed)
        1 :=
    InvariantRuns.basic _ _ hzeroed (by
      rw [hexec]
      exact hfinal)
  have hseq :=
    InvariantRuns.seq
      (InvariantRuns.basic (.imm destination 0) store
        hstore hzeroed)
      hsecond
  rw [hexec] at hseq
  simpa [copy, zeroed] using hseq

private theorem equalImmediate_writesWithin_local
    (regs : NeighborhoodTrial.Registers controller)
    (value output constant : ℕ) :
    RAM.Structured.Footprint.CmdWritesWithin
      {(inputRegisters regs).buffer,
        (inputRegisters regs).test,
        (inputRegisters regs).completed, output}
      (equalImmediate regs value output constant) := by
  simp [equalImmediate, Cmd.seqList,
    RAM.Structured.Footprint.CmdWritesWithin,
    RAM.Structured.Footprint.BasicWritesWithin]

private theorem equalImmediate_runs
    (regs : NeighborhoodTrial.Registers controller)
    (value output constant : ℕ) (store : Store)
    (hvalueBuffer : value ≠ (inputRegisters regs).buffer)
    (hvalueTest : value ≠ (inputRegisters regs).test) :
    ∃ final,
      Runs (equalImmediate regs value output constant) store final ∧
      final output =
        (if store value = constant then 1 else 0) ∧
      ∀ address,
        address ∉
          ({(inputRegisters regs).buffer,
            (inputRegisters regs).test,
            (inputRegisters regs).completed, output} : Finset ℕ) →
        final address = store address := by
  let first :=
    Basic.exec
      (.imm (inputRegisters regs).buffer constant) store
  let second :=
    Basic.exec
      (.sub (inputRegisters regs).test value
        (inputRegisters regs).buffer) first
  let third :=
    Basic.exec
      (.sub (inputRegisters regs).completed
        (inputRegisters regs).buffer value) second
  let tested :=
    Basic.exec
      (.add (inputRegisters regs).test
        (inputRegisters regs).test
        (inputRegisters regs).completed) third
  have htested :
      tested (inputRegisters regs).test =
        (store value - constant) + (constant - store value) := by
    simp [tested, third, second, first, Basic.exec,
      hvalueBuffer, hvalueTest,
      (inputRegisters regs).index_ne
        (by decide : (5 : Fin 12) ≠ 9),
      (inputRegisters regs).index_ne
        (by decide : (1 : Fin 12) ≠ 5)]
  by_cases heq : store value = constant
  · let final :=
      Basic.exec (.imm output 1) tested
    have htestZero :
        tested (inputRegisters regs).test = 0 := by
      rw [htested, heq]
      simp
    have hrun :
        Runs (equalImmediate regs value output constant)
          store final := by
      simpa [equalImmediate, Cmd.seqList, first, second,
        third, tested, final] using
        Runs.seq
          (Runs.basic
            (.imm (inputRegisters regs).buffer constant) store)
          (Runs.seq
            (Runs.basic
              (.sub (inputRegisters regs).test value
                (inputRegisters regs).buffer) first)
            (Runs.seq
              (Runs.basic
                (.sub (inputRegisters regs).completed
                  (inputRegisters regs).buffer value) second)
              (Runs.seq
                (Runs.basic
                  (.add (inputRegisters regs).test
                    (inputRegisters regs).test
                    (inputRegisters regs).completed) third)
                (Runs.ifZero htestZero
                  (Runs.basic (.imm output 1) tested)))))
    refine ⟨final, hrun, ?_, ?_⟩
    · simp [final, Basic.exec, heq]
    · intro address haddress
      exact RAM.Structured.Footprint.runs_eq_outside
        (equalImmediate_writesWithin_local
          regs value output constant)
        hrun haddress
  · let final :=
      Basic.exec (.imm output 0) tested
    have htestNonzero :
        tested (inputRegisters regs).test ≠ 0 := by
      rw [htested]
      omega
    have hrun :
        Runs (equalImmediate regs value output constant)
          store final := by
      simpa [equalImmediate, Cmd.seqList, first, second,
        third, tested, final] using
        Runs.seq
          (Runs.basic
            (.imm (inputRegisters regs).buffer constant) store)
          (Runs.seq
            (Runs.basic
              (.sub (inputRegisters regs).test value
                (inputRegisters regs).buffer) first)
            (Runs.seq
              (Runs.basic
                (.sub (inputRegisters regs).completed
                  (inputRegisters regs).buffer value) second)
              (Runs.seq
                (Runs.basic
                  (.add (inputRegisters regs).test
                    (inputRegisters regs).test
                    (inputRegisters regs).completed) third)
                (Runs.ifNonzero htestNonzero
                  (Runs.basic (.imm output 0) tested)))))
    refine ⟨final, hrun, ?_, ?_⟩
    · simp [final, Basic.exec, heq]
    · intro address haddress
      exact RAM.Structured.Footprint.runs_eq_outside
        (equalImmediate_writesWithin_local
          regs value output constant)
        hrun haddress

private theorem equalImmediate_invariantRuns
    (regs : NeighborhoodTrial.Registers controller)
    (allowed : Finset ℕ) (bound value output constant : ℕ)
    (store : Store)
    (hvalueBuffer : value ≠ (inputRegisters regs).buffer)
    (hvalueTest : value ≠ (inputRegisters regs).test)
    (hvalueBound : store value ≤ bound)
    (hconstantBound : constant ≤ bound)
    (honeBound : 1 ≤ bound)
    (hstore :
      NeighborhoodProgram.ValuesWithin allowed bound store) :
    ∃ final steps,
      InvariantRuns
        (NeighborhoodProgram.ValuesWithin allowed bound)
        (equalImmediate regs value output constant)
        store final steps ∧
      final output =
        (if store value = constant then 1 else 0) ∧
      ∀ address,
        address ∉
          ({(inputRegisters regs).buffer,
            (inputRegisters regs).test,
            (inputRegisters regs).completed, output} : Finset ℕ) →
        final address = store address := by
  let first :=
    Basic.exec
      (.imm (inputRegisters regs).buffer constant) store
  let second :=
    Basic.exec
      (.sub (inputRegisters regs).test value
        (inputRegisters regs).buffer) first
  let third :=
    Basic.exec
      (.sub (inputRegisters regs).completed
        (inputRegisters regs).buffer value) second
  let tested :=
    Basic.exec
      (.add (inputRegisters regs).test
        (inputRegisters regs).test
        (inputRegisters regs).completed) third
  have hfirst :
      NeighborhoodProgram.ValuesWithin allowed bound first := by
    exact valuesWithin_update allowed bound
      (inputRegisters regs).buffer constant store
      hstore hconstantBound
  have hfirstValue :
      first value = store value := by
    simp [first, Basic.exec, hvalueBuffer]
  have hfirstBuffer :
      first (inputRegisters regs).buffer = constant := by
    simp [first, Basic.exec]
  have hsecond :
      NeighborhoodProgram.ValuesWithin allowed bound second := by
    apply valuesWithin_update allowed bound
      (inputRegisters regs).test
      (first value - first (inputRegisters regs).buffer)
      first hfirst
    rw [hfirstValue, hfirstBuffer]
    exact (Nat.sub_le _ _).trans hvalueBound
  have hsecondValue :
      second value = store value := by
    simp [second, first, Basic.exec, hvalueBuffer, hvalueTest]
  have hsecondBuffer :
      second (inputRegisters regs).buffer = constant := by
    simp [second, first, Basic.exec,
      (inputRegisters regs).index_ne
        (by decide : (1 : Fin 12) ≠ 5)]
  have hsecondTest :
      second (inputRegisters regs).test =
        store value - constant := by
    simp [second, hfirstValue, hfirstBuffer, Basic.exec]
  have hthird :
      NeighborhoodProgram.ValuesWithin allowed bound third := by
    apply valuesWithin_update allowed bound
      (inputRegisters regs).completed
      (second (inputRegisters regs).buffer - second value)
      second hsecond
    rw [hsecondBuffer, hsecondValue]
    exact (Nat.sub_le _ _).trans hconstantBound
  have hthirdTest :
      third (inputRegisters regs).test =
        store value - constant := by
    simp [third, Basic.exec,
      (inputRegisters regs).index_ne
        (by decide : (5 : Fin 12) ≠ 9),
      hsecondTest]
  have hthirdCompleted :
      third (inputRegisters regs).completed =
        constant - store value := by
    simp [third, Basic.exec, hsecondBuffer, hsecondValue]
  have htested :
      NeighborhoodProgram.ValuesWithin allowed bound tested := by
    apply valuesWithin_update allowed bound
      (inputRegisters regs).test
      (third (inputRegisters regs).test +
        third (inputRegisters regs).completed)
      third hthird
    rw [hthirdTest, hthirdCompleted]
    omega
  have htestedValue :
      tested (inputRegisters regs).test =
        (store value - constant) + (constant - store value) := by
    simp [tested, Basic.exec, hthirdTest, hthirdCompleted]
  have hfirstRun :
      InvariantRuns
        (NeighborhoodProgram.ValuesWithin allowed bound)
        (.basic
          (.imm (inputRegisters regs).buffer constant))
        store first 1 := by
    exact
      InvariantRuns.basic _ _ hstore hfirst
  have hsecondRun :
      InvariantRuns
        (NeighborhoodProgram.ValuesWithin allowed bound)
        (.basic
          (.sub (inputRegisters regs).test value
            (inputRegisters regs).buffer))
        first second 1 := by
    exact InvariantRuns.basic _ _ hfirst hsecond
  have hthirdRun :
      InvariantRuns
        (NeighborhoodProgram.ValuesWithin allowed bound)
        (.basic
          (.sub (inputRegisters regs).completed
            (inputRegisters regs).buffer value))
        second third 1 := by
    exact InvariantRuns.basic _ _ hsecond hthird
  have htestedRun :
      InvariantRuns
        (NeighborhoodProgram.ValuesWithin allowed bound)
        (.basic
          (.add (inputRegisters regs).test
            (inputRegisters regs).test
            (inputRegisters regs).completed))
        third tested 1 := by
    exact InvariantRuns.basic _ _ hthird htested
  by_cases heq : store value = constant
  · let final := Basic.exec (.imm output 1) tested
    have htestZero :
        tested (inputRegisters regs).test = 0 := by
      rw [htestedValue, heq]
      simp
    have hfinal :
        NeighborhoodProgram.ValuesWithin allowed bound final := by
      exact valuesWithin_update allowed bound output 1 tested
        htested honeBound
    have hinvariant :
        InvariantRuns
          (NeighborhoodProgram.ValuesWithin allowed bound)
          (equalImmediate regs value output constant)
          store final 6 := by
      simpa [equalImmediate, Cmd.seqList, first, second,
        third, tested, final] using
        InvariantRuns.seq hfirstRun
          (InvariantRuns.seq hsecondRun
            (InvariantRuns.seq hthirdRun
              (InvariantRuns.seq htestedRun
                (InvariantRuns.ifZero
                  (onNonzero := .basic (.imm output 0))
                  htestZero
                  (InvariantRuns.basic _ _ htested hfinal)))))
    obtain ⟨semanticFinal, hsemanticRun, hresult,
        hpreserved⟩ :=
      equalImmediate_runs regs value output constant store
        hvalueBuffer hvalueTest
    have hfinalEq : final = semanticFinal :=
      runs_final_eq (InvariantRuns.toRuns hinvariant)
        hsemanticRun
    subst semanticFinal
    exact ⟨final, 6, hinvariant, hresult, hpreserved⟩
  · let final := Basic.exec (.imm output 0) tested
    have htestNonzero :
        tested (inputRegisters regs).test ≠ 0 := by
      rw [htestedValue]
      omega
    have hfinal :
        NeighborhoodProgram.ValuesWithin allowed bound final := by
      exact valuesWithin_update allowed bound output 0 tested
        htested (by omega)
    have hinvariant :
        InvariantRuns
          (NeighborhoodProgram.ValuesWithin allowed bound)
          (equalImmediate regs value output constant)
          store final (4 + 3) := by
      simpa [equalImmediate, Cmd.seqList, first, second,
        third, tested, final] using
        InvariantRuns.seq hfirstRun
          (InvariantRuns.seq hsecondRun
            (InvariantRuns.seq hthirdRun
              (InvariantRuns.seq htestedRun
                (InvariantRuns.ifNonzero
                  (onZero := .basic (.imm output 1))
                  htestNonzero
                  (InvariantRuns.basic _ _ htested hfinal)))))
    obtain ⟨semanticFinal, hsemanticRun, hresult,
        hpreserved⟩ :=
      equalImmediate_runs regs value output constant store
        hvalueBuffer hvalueTest
    have hfinalEq : final = semanticFinal :=
      runs_final_eq (InvariantRuns.toRuns hinvariant)
        hsemanticRun
    subst semanticFinal
    exact ⟨final, 4 + 3, hinvariant, hresult, hpreserved⟩

private theorem setByZero_runs
    (test output onZero onNonzero : ℕ) (store : Store) :
    ∃ final,
      Runs
        (.ifZero test
          (.basic (.imm output onZero))
          (.basic (.imm output onNonzero)))
        store final ∧
      final output =
        (if store test = 0 then onZero else onNonzero) ∧
      ∀ address, address ≠ output →
        final address = store address := by
  by_cases hzero : store test = 0
  · let final := Basic.exec (.imm output onZero) store
    refine ⟨final, Runs.ifZero hzero (Runs.basic _ _), ?_, ?_⟩
    · simp [final, Basic.exec, hzero]
    · intro address haddress
      simp [final, Basic.exec, Function.update_of_ne, haddress]
  · let final := Basic.exec (.imm output onNonzero) store
    refine
      ⟨final, Runs.ifNonzero hzero (Runs.basic _ _), ?_, ?_⟩
    · simp [final, Basic.exec, hzero]
    · intro address haddress
      simp [final, Basic.exec, Function.update_of_ne, haddress]

private theorem tapeAt_init_cells
    (tm : TM workTapeCount) (input : List Bool)
    (tape : TapeIndex workTapeCount) (position : ℕ) :
    (tapeAt (tm.initCfg input) tape).cells position =
      if tape.val = 0 then
        (Tape.init (input.map Γ.ofBool)).cells position
      else
        (Tape.init []).cells position := by
  by_cases hinput : tape.val = 0
  · have htape : tape = TapeIndex.input workTapeCount :=
      Fin.ext hinput
    rw [if_pos hinput, htape, tapeAt_input]
  · by_cases houtput : tape.val = workTapeCount + 1
    · have htape : tape = TapeIndex.output workTapeCount :=
        Fin.ext houtput
      rw [if_neg hinput, htape, tapeAt_output]
    · let index : Fin workTapeCount :=
        ⟨tape.val - 1, by omega⟩
      have htape : tape = TapeIndex.work index := by
        apply Fin.ext
        simp only [TapeIndex.work, index]
        omega
      rw [if_neg hinput, htape, tapeAt_work]

private theorem gammaCode_initial
    (tm : TM workTapeCount) (input : List Bool)
    (tape : TapeIndex workTapeCount) (position : ℕ) :
    (FiniteEncoding.gammaEquiv
      ((tapeAt (tm.initCfg input) tape).cells position)).val =
      initialGammaCode input tape.val position := by
  rw [tapeAt_init_cells]
  unfold initialGammaCode
  by_cases hp : position = 0
  · subst position
    simp [Tape.init, FiniteEncoding.gammaEquiv]
  · by_cases ht : tape.val = 0
    · simp only [ht, ↓reduceIte]
      obtain ⟨index, rfl⟩ : ∃ index, position = index + 1 :=
        ⟨position - 1, by omega⟩
      by_cases hi : index < input.length
      · have hle : index + 1 ≤ input.length := by omega
        rw [Tape.init_ofBool_cells_lt input index hi]
        simp [FiniteEncoding.gammaEquiv, RAM.initRegs, hi, hle]
        cases input[index] <;> rfl
      · have hle : input.length ≤ index :=
          Nat.le_of_not_gt hi
        have hnle : ¬index + 1 ≤ input.length := by omega
        rw [Tape.init_ofBool_cells_ge input index hle]
        simp [FiniteEncoding.gammaEquiv, hnle]
    · simp only [ht, ↓reduceIte]
      obtain ⟨index, rfl⟩ : ∃ index, position = index + 1 :=
        ⟨position - 1, by omega⟩
      simp [FiniteEncoding.gammaEquiv]

private theorem sourceNodeState
    (tm : TM workTapeCount) (input : List Bool)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (tape : TapeIndex workTapeCount) (block : ℕ) :
    (NeighborhoodContent.nodeContent tm input blockLength hpositive
      (.source tape block)).state = tm.qstart :=
  rfl

private theorem sourceNodeHead
    (tm : TM workTapeCount) (input : List Bool)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (tape : TapeIndex workTapeCount) (block : ℕ) :
    (NeighborhoodContent.nodeContent tm input blockLength hpositive
      (.source tape block)).headRemainder.val = 0 := by
  simp only [NeighborhoodContent.nodeContent,
    NeighborhoodContent.nodeConfigurationTime,
    NeighborhoodGraph.Node.tape, TM.configurationAt_zero,
    tapeAt, Cfg.init, TM.initCfg, Tape.init]
  split_ifs <;> simp [Nat.zero_mod blockLength]

private theorem sourceNodeCells
    (tm : TM workTapeCount) (input : List Bool)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (tape : TapeIndex workTapeCount) (block : ℕ)
    (offset : Fin blockLength) :
    (NeighborhoodContent.nodeContent tm input blockLength hpositive
      (.source tape block)).cells offset =
      (tapeAt (tm.initCfg input) tape).cells
        (block * blockLength + offset.val) :=
  rfl

private theorem sourceBits_forward
    (tm : TM workTapeCount) (order : FiniteEncoding.StateOrder tm)
    (input : List Bool) (blockLength : ℕ)
    (hpositive : 0 < blockLength)
    (tape : TapeIndex workTapeCount) (block : ℕ)
    (coordinate :
      ComputationGraph.CompactEncoding.Coordinate blockLength tm.Q) :
    sourceBits tm input blockLength
        (FiniteEncoding.ofStateOrder order blockLength)
        hpositive tape block
        (FiniteEncoding.coordinateEquiv order blockLength coordinate) =
      coordinateBit tm order input blockLength tape.val block
        (FiniteEncoding.coordinateEquiv
          order blockLength coordinate).val := by
  cases coordinate with
  | inl state =>
      have hslt := (order.state state).isLt
      simp only [sourceBits, encodeBits, FiniteEncoding.ofStateOrder,
        Equiv.symm_apply_apply,
        ComputationGraph.CompactEncoding.coordinateBits]
      rw [sourceNodeState]
      have hcoordinate :
          ((FiniteEncoding.coordinateEquiv order blockLength)
            (.inl state)).val =
            (order.state state).val := by
        simp [FiniteEncoding.coordinateEquiv, finSumFinEquiv,
          finProdFinEquiv]
      rw [hcoordinate]
      simp only [coordinateBit]
      by_cases hs : state = tm.qstart
      · subst state
        rw [if_pos rfl]
        simp
      · have hcode :
            (order.state state).val ≠
              (order.state tm.qstart).val := by
          intro h
          exact hs (order.state.injective (Fin.ext h))
        rw [if_neg hcode]
        rw [if_neg (by omega)]
        rw [if_neg (by
          intro h
          omega)]
        simp [hs]
  | inr rest =>
      cases rest with
      | inl remainder =>
          have hstartlt := (order.state tm.qstart).isLt
          have hrlt := remainder.isLt
          simp only [sourceBits, encodeBits,
            FiniteEncoding.ofStateOrder, Equiv.symm_apply_apply,
            ComputationGraph.CompactEncoding.coordinateBits]
          have hcoordinate :
              ((FiniteEncoding.coordinateEquiv order blockLength)
                (.inr (.inl remainder))).val =
                Fintype.card tm.Q + remainder.val := by
            simp [FiniteEncoding.coordinateEquiv, finSumFinEquiv,
              finProdFinEquiv]
          rw [hcoordinate]
          simp only [coordinateBit]
          rw [if_neg (by omega)]
          by_cases hr : remainder.val = 0
          · rw [if_pos (by omega)]
            have heq :
                remainder =
                  (NeighborhoodContent.nodeContent
                    tm input blockLength hpositive
                    (.source tape block)).headRemainder := by
              apply Fin.ext
              rw [sourceNodeHead]
              exact hr
            simp [heq]
          · rw [if_neg (by omega)]
            rw [if_neg (by
              intro h
              omega)]
            have hne :
                remainder ≠
                  (NeighborhoodContent.nodeContent
                    tm input blockLength hpositive
                    (.source tape block)).headRemainder := by
              intro h
              have hval := congrArg Fin.val h
              rw [sourceNodeHead] at hval
              exact hr hval
            simp [hne]
      | inr cell =>
          rcases cell with ⟨offset, gamma⟩
          have hstartlt := (order.state tm.qstart).isLt
          have hoffset := offset.isLt
          have hgamma := (FiniteEncoding.gammaEquiv gamma).isLt
          simp only [sourceBits, encodeBits,
            FiniteEncoding.ofStateOrder, Equiv.symm_apply_apply,
            ComputationGraph.CompactEncoding.coordinateBits]
          have hcoordinate :
              ((FiniteEncoding.coordinateEquiv order blockLength)
                (.inr (.inr (offset, gamma)))).val =
                Fintype.card tm.Q + blockLength +
                  (offset.val * 4 +
                    (FiniteEncoding.gammaEquiv gamma).val) := by
            simp [FiniteEncoding.coordinateEquiv, finSumFinEquiv,
              finProdFinEquiv]
            omega
          rw [hcoordinate]
          simp only [coordinateBit]
          rw [if_neg (by omega), if_neg (by omega)]
          rw [if_pos (by constructor <;> omega)]
          have hmod :
              (Fintype.card tm.Q + blockLength +
                    (offset.val * 4 +
                      (FiniteEncoding.gammaEquiv gamma).val) -
                  (Fintype.card tm.Q + blockLength)) % 4 =
                (FiniteEncoding.gammaEquiv gamma).val := by
            omega
          have hdiv :
              (Fintype.card tm.Q + blockLength +
                    (offset.val * 4 +
                      (FiniteEncoding.gammaEquiv gamma).val) -
                  (Fintype.card tm.Q + blockLength)) / 4 =
                offset.val := by
            omega
          rw [hmod, hdiv, sourceNodeCells]
          rw [← gammaCode_initial tm input tape
            (block * blockLength + offset.val)]
          apply decide_eq_decide.mpr
          constructor
          · rintro rfl
            rfl
          · intro h
            apply FiniteEncoding.gammaEquiv.injective
            apply Fin.ext
            exact h

theorem sourceBits_eq_coordinateBit_internal
    (tm : TM workTapeCount) (order : FiniteEncoding.StateOrder tm)
    (input : List Bool) (blockLength : ℕ)
    (hpositive : 0 < blockLength)
    (tape : TapeIndex workTapeCount) (block : ℕ)
    (index : Fin (payloadWidth tm blockLength)) :
    sourceBits tm input blockLength
        (FiniteEncoding.ofStateOrder order blockLength)
        hpositive tape block index =
      coordinateBit tm order input blockLength tape.val block index.val := by
  let coordinate :=
    (FiniteEncoding.coordinateEquiv order blockLength).symm index
  have h := sourceBits_forward tm order input blockLength
    hpositive tape block coordinate
  simpa [coordinate] using h

private theorem list_ofFn_succ
    {α : Type*} (function : Fin (count + 1) → α) :
    List.ofFn function =
      function 0 :: List.ofFn (fun index : Fin count =>
        function index.succ) := by
  rw [List.ofFn_succ]

private theorem forwardChunk_eq
    (bits : ℕ → Bool) (start count accumulator : ℕ) :
    forwardChunk (fun index => Input.bitValue (bits index))
        start count accumulator =
      accumulator * 2 ^ count +
        Nat.fromBits
          (List.ofFn fun index : Fin count =>
            bits (start + index.val)) := by
  induction count generalizing start accumulator with
  | zero =>
      simp [forwardChunk, Nat.fromBits]
  | succ count ih =>
      rw [forwardChunk, ih]
      rw [list_ofFn_succ]
      simp only [Nat.fromBits, List.length_ofFn, Input.bitValue]
      have htail :
          (List.ofFn fun index : Fin count =>
            bits (start + index.succ.val)) =
          List.ofFn
            (fun index : Fin count =>
              bits (start + 1 + index.val)) := by
        apply congrArg List.ofFn
        funext index
        apply congrArg bits
        rw [Fin.val_succ]
        omega
      rw [htail]
      simp only [Fin.val_zero, Nat.add_zero, pow_succ]
      ring_nf

private theorem coordinateBit_eq_false_of_payload_le
    (tm : TM workTapeCount) (order : FiniteEncoding.StateOrder tm)
    (input : List Bool) (blockLength tape block coordinate : ℕ)
    (hpositive : 0 < blockLength)
    (hcoordinate : payloadWidth tm blockLength ≤ coordinate) :
    coordinateBit tm order input blockLength tape block coordinate =
      false := by
  have hstart := (order.state tm.qstart).isLt
  have hwidth :
      payloadWidth tm blockLength =
        Fintype.card tm.Q + 5 * blockLength := by
    simpa [payloadWidth] using
      ComputationGraph.CompactEncoding.width_eq
        blockLength tm.Q
  unfold coordinateBit
  rw [if_neg (by omega)]
  rw [if_neg (by omega)]
  rw [if_neg (by
    intro h
    omega)]

theorem sourceChunkValue_eq_internal
    (tm : TM workTapeCount) (order : FiniteEncoding.StateOrder tm)
    (input : List Bool) (blockLength : ℕ)
    (hpositive : 0 < blockLength)
    (tape : TapeIndex workTapeCount) (block : ℕ)
    (chunk :
      Fin
        (PrimeGrouped.Logarithmic.chunkCount
          (payloadWidth tm blockLength)
          (graphFanIn workTapeCount))) :
    sourceChunkValue tm order input blockLength tape.val block chunk.val
        (PrimeGrouped.Logarithmic.chunkBits
          (payloadWidth tm blockLength)
          (graphFanIn workTapeCount)) =
      Residue.sourceValue tm input blockLength
        (FiniteEncoding.ofStateOrder order blockLength)
        hpositive tape block chunk := by
  let chunkBits :=
    PrimeGrouped.Logarithmic.chunkBits
      (payloadWidth tm blockLength)
      (graphFanIn workTapeCount)
  rw [show
      Residue.sourceValue tm input blockLength
          (FiniteEncoding.ofStateOrder order blockLength)
          hpositive tape block chunk =
        PrimeGrouped.Logarithmic.chunkCodeNat
          (GroupedExtension.Layout.pack
            (chunkBits := chunkBits)
            (sourceBits tm input blockLength
              (FiniteEncoding.ofStateOrder order blockLength)
              hpositive tape block)
            chunk) by
    unfold Residue.sourceValue
      NeighborhoodExecutableEvaluation.sourceValue
      toResidues PrimeGrouped.Logarithmic.encodeValue
      GroupedExtension.encodeVector
    rw [PrimeGrouped.Logarithmic.codebook_encode]
    exact ZMod.val_natCast_of_lt
      (PrimeGrouped.Logarithmic.Decoding.chunkCodeNat_lt_searchModulus
        (payloadWidth tm blockLength)
        (graphFanIn workTapeCount) _)]
  unfold sourceChunkValue
  unfold coordinateBitValue
  rw [forwardChunk_eq]
  simp only [zero_mul, zero_add,
    PrimeGrouped.Logarithmic.chunkCodeNat]
  apply congrArg Nat.fromBits
  apply congrArg List.ofFn
  funext offset
  unfold GroupedExtension.Layout.pack
  split
  next hindex =>
    rw [sourceBits_eq_coordinateBit_internal]
  next hindex =>
    rw [coordinateBit_eq_false_of_payload_le
      tm order input blockLength tape.val block
      (chunk.val * chunkBits + offset.val) hpositive
      (Nat.le_of_not_gt hindex)]

private theorem writeMap_mem
    (regs : NeighborhoodTrial.Registers controller)
    (slot : Fin 16) :
    regs.index (writeMap slot) ∈ writeFootprint regs :=
  Finset.mem_image.mpr ⟨slot, Finset.mem_univ _, rfl⟩

@[simp]
private theorem inputIndex_mem_writeFootprint
    (regs : NeighborhoodTrial.Registers controller)
    (slot : Fin 12) :
    (inputRegisters regs).index slot ∈ writeFootprint regs := by
  change regs.index (inputMap slot) ∈ writeFootprint regs
  fin_cases slot <;>
    first
    | exact writeMap_mem regs 0
    | exact writeMap_mem regs 1
    | exact writeMap_mem regs 2
    | exact writeMap_mem regs 3
    | exact writeMap_mem regs 4
    | exact writeMap_mem regs 5
    | exact writeMap_mem regs 6
    | exact writeMap_mem regs 7
    | exact writeMap_mem regs 8
    | exact writeMap_mem regs 9
    | exact writeMap_mem regs 10
    | exact writeMap_mem regs 11

private theorem inputFootprint_subset
    (regs : NeighborhoodTrial.Registers controller) :
    (inputRegisters regs).footprint ⊆ writeFootprint regs := by
  intro address haddress
  rcases Finset.mem_image.mp haddress with ⟨slot, _, rfl⟩
  exact inputIndex_mem_writeFootprint regs slot

private theorem cmdWritesWithin_mono
    {small large : Finset ℕ} {command : Cmd}
    (hsubset : small ⊆ large)
    (hwrites :
      RAM.Structured.Footprint.CmdWritesWithin small command) :
    RAM.Structured.Footprint.CmdWritesWithin large command := by
  induction command with
  | skip => trivial
  | basic op =>
      cases op <;>
        simp_all [RAM.Structured.Footprint.CmdWritesWithin,
          RAM.Structured.Footprint.BasicWritesWithin] <;>
        exact hsubset hwrites
  | seq first second firstIH secondIH =>
      exact ⟨firstIH hwrites.1, secondIH hwrites.2⟩
  | ifZero test onZero onNonzero zeroIH nonzeroIH =>
      exact ⟨zeroIH hwrites.1, nonzeroIH hwrites.2⟩
  | whileNonzero test body bodyIH =>
      exact bodyIH hwrites

private theorem pop_sourceWritesWithin
    (stack : NeighborhoodProgram.StackRegisters) :
    RAM.Structured.Footprint.CmdWritesWithin
      stack.footprint (NeighborhoodProgram.pop stack) := by
  simp [NeighborhoodProgram.pop, NeighborhoodProgram.popBody,
    NeighborhoodProgram.popTestOp, Cmd.seqList,
    RAM.Structured.Footprint.CmdWritesWithin,
    RAM.Structured.Footprint.BasicWritesWithin,
    NeighborhoodProgram.StackRegisters.index_mem_footprint]

private theorem peek_sourceWritesWithin
    (stack : NeighborhoodProgram.StackRegisters) :
    RAM.Structured.Footprint.CmdWritesWithin
      stack.footprint (NeighborhoodProgram.peek stack) := by
  simp [NeighborhoodProgram.peek, RuntimeArithmetic.reduce,
    RuntimeArithmetic.reduceBody, RuntimeArithmetic.reduceTestOp,
    NeighborhoodProgram.StackRegisters.reduceRegisters,
    Cmd.seqList, RAM.Structured.Footprint.CmdWritesWithin,
    RAM.Structured.Footprint.BasicWritesWithin,
    NeighborhoodProgram.StackRegisters.index_mem_footprint]

private theorem peek_sourceWritesWithin_withoutOne
    (stack : NeighborhoodProgram.StackRegisters) :
    RAM.Structured.Footprint.CmdWritesWithin
      (stack.footprint.erase stack.one)
      (NeighborhoodProgram.peek stack) := by
  simp [NeighborhoodProgram.peek, RuntimeArithmetic.reduce,
    RuntimeArithmetic.reduceBody, RuntimeArithmetic.reduceTestOp,
    NeighborhoodProgram.StackRegisters.reduceRegisters,
    Cmd.seqList, RAM.Structured.Footprint.CmdWritesWithin,
    RAM.Structured.Footprint.BasicWritesWithin,
    NeighborhoodProgram.StackRegisters.footprint,
    stack.injective.eq_iff]

private theorem pop_sourceWritesWithin_withoutValue
    (stack : NeighborhoodProgram.StackRegisters) :
    RAM.Structured.Footprint.CmdWritesWithin
      (stack.footprint.erase stack.value)
      (NeighborhoodProgram.pop stack) := by
  simp [NeighborhoodProgram.pop, NeighborhoodProgram.popBody,
    NeighborhoodProgram.popTestOp, Cmd.seqList,
    RAM.Structured.Footprint.CmdWritesWithin,
    RAM.Structured.Footprint.BasicWritesWithin,
    NeighborhoodProgram.StackRegisters.footprint,
    stack.injective.eq_iff]

private theorem pop_writesWithin
    (regs : NeighborhoodTrial.Registers controller)
    (stack : NeighborhoodProgram.StackRegisters)
    (hstack :
      stack.footprint ⊆ (inputRegisters regs).footprint) :
    RAM.Structured.Footprint.CmdWritesWithin
      (writeFootprint regs) (NeighborhoodProgram.pop stack) := by
  apply cmdWritesWithin_mono
    (small := stack.footprint)
    (large := writeFootprint regs)
    (fun address haddress =>
      inputFootprint_subset regs (hstack haddress))
  exact pop_sourceWritesWithin stack

private theorem peek_writesWithin
    (regs : NeighborhoodTrial.Registers controller)
    (stack : NeighborhoodProgram.StackRegisters)
    (hstack :
      stack.footprint ⊆ (inputRegisters regs).footprint) :
    RAM.Structured.Footprint.CmdWritesWithin
      (writeFootprint regs) (NeighborhoodProgram.peek stack) := by
  apply cmdWritesWithin_mono
    (small := stack.footprint)
    (large := writeFootprint regs)
    (fun address haddress =>
      inputFootprint_subset regs (hstack haddress))
  exact peek_sourceWritesWithin stack

private theorem mainStack_footprint_subset
    (regs : NeighborhoodTrial.Registers controller) :
    (inputRegisters regs).mainStack.footprint ⊆
      (inputRegisters regs).footprint := by
  intro address haddress
  rcases Finset.mem_image.mp haddress with ⟨slot, _, rfl⟩
  exact (inputRegisters regs).index_mem_footprint
    (NeighborhoodProgram.BankRegisters.mainMap slot)

private theorem bufferStack_footprint_subset
    (regs : NeighborhoodTrial.Registers controller) :
    (inputRegisters regs).bufferStack.footprint ⊆
      (inputRegisters regs).footprint := by
  intro address haddress
  rcases Finset.mem_image.mp haddress with ⟨slot, _, rfl⟩
  exact (inputRegisters regs).index_mem_footprint
    (NeighborhoodProgram.BankRegisters.bufferMap slot)

private theorem lookupInput_writesWithin
    (regs : NeighborhoodTrial.Registers controller) :
    RAM.Structured.Footprint.CmdWritesWithin
      (writeFootprint regs) (lookupInput regs) := by
  apply cmdWritesWithin_mono (inputFootprint_subset regs)
  exact InputLookup.sourceWritesWithin _ _

private def recoverFootprint
    (regs : NeighborhoodTrial.Registers controller) : Finset ℕ :=
  (inputRegisters regs).footprint ∪ {recoveredChunkBits regs}

private theorem inputMap_ne_recovered :
    ∀ slot, inputMap slot ≠ (21 : Fin 34) := by
  decide

private theorem recovered_not_mem_inputFootprint
    (regs : NeighborhoodTrial.Registers controller) :
    recoveredChunkBits regs ∉ (inputRegisters regs).footprint := by
  intro hmember
  rcases Finset.mem_image.mp hmember with ⟨slot, _, heq⟩
  have hslot := regs.injective heq
  change inputMap slot = (21 : Fin 34) at hslot
  exact inputMap_ne_recovered slot hslot

private theorem recovered_ne_inputIndex
    (regs : NeighborhoodTrial.Registers controller)
    (slot : Fin 12) :
    recoveredChunkBits regs ≠ (inputRegisters regs).index slot := by
  intro heq
  apply inputMap_ne_recovered slot
  apply regs.injective
  exact heq.symm

private theorem recoverChunkBits_writesWithin_local
    (regs : NeighborhoodTrial.Registers controller) :
    RAM.Structured.Footprint.CmdWritesWithin
      (recoverFootprint regs) (recoverChunkBits regs) := by
  have hinput :
      (inputRegisters regs).footprint ⊆ recoverFootprint regs :=
    Finset.subset_union_left
  have hmain :
      RAM.Structured.Footprint.CmdWritesWithin
        (recoverFootprint regs)
        (NeighborhoodProgram.pop
          (inputRegisters regs).mainStack) := by
    apply cmdWritesWithin_mono
      (small := (inputRegisters regs).mainStack.footprint)
      (large := recoverFootprint regs)
      (fun address haddress =>
        hinput (mainStack_footprint_subset regs haddress))
    exact pop_sourceWritesWithin _
  have hrecovered :
      recoveredChunkBits regs ∈ recoverFootprint regs := by
    simp [recoverFootprint]
  have hword :=
    hinput ((inputRegisters regs).index_mem_footprint 0)
  have hbase :=
    hinput ((inputRegisters regs).index_mem_footprint 2)
  have hbasePred :=
    hinput ((inputRegisters regs).index_mem_footprint 3)
  have hone :=
    hinput ((inputRegisters regs).index_mem_footprint 6)
  have htest :=
    hinput ((inputRegisters regs).index_mem_footprint 5)
  simp [recoverChunkBits, recoverChunkBitsBody, copy,
    Cmd.seqList,
    RAM.Structured.Footprint.CmdWritesWithin,
    RAM.Structured.Footprint.BasicWritesWithin,
    hmain, hrecovered, hword, hbase, hbasePred, hone, htest]

private theorem recoverLoop_runs
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store) (remaining completed : ℕ)
    (hword :
      store (inputRegisters regs).word = 2 ^ remaining)
    (hrecovered :
      store (recoveredChunkBits regs) = completed)
    (htest :
      store (inputRegisters regs).test = 2 ^ remaining - 1)
    (hbase : store (inputRegisters regs).base = 2)
    (hbasePred : store (inputRegisters regs).basePred = 1)
    (hone : store (inputRegisters regs).one = 1) :
    ∃ final,
      Runs
        (.whileNonzero (inputRegisters regs).test
          (recoverChunkBitsBody regs))
        store final ∧
      final (inputRegisters regs).word = 1 ∧
      final (recoveredChunkBits regs) = completed + remaining ∧
      final (inputRegisters regs).test = 0 ∧
      final (inputRegisters regs).base = 2 ∧
      final (inputRegisters regs).basePred = 1 ∧
      final (inputRegisters regs).one = 1 := by
  induction remaining generalizing store completed with
  | zero =>
      have htestZero :
          store (inputRegisters regs).test = 0 := by
        simpa using htest
      exact
        ⟨store, Runs.whileZero htestZero, by simpa using hword,
          by simpa using hrecovered, htestZero, hbase,
          hbasePred, hone⟩
  | succ remaining ih =>
      have htestNonzero :
          store (inputRegisters regs).test ≠ 0 := by
        rw [htest]
        have hpow : 0 < 2 ^ (remaining + 1) :=
          pow_pos (by omega) _
        omega
      obtain ⟨afterPop, hpop, hpopWord, _hpopQuotient,
          hpopTest, hpopBase, hpopBasePred, hpopOne⟩ :=
        NeighborhoodProgram.pop_runs
          (inputRegisters regs).mainStack store
          2 (2 ^ (remaining + 1)) (by omega)
          hword hbase (by simpa using hbasePred) hone
      have hpopWord0 :
          afterPop (inputRegisters regs).word =
            PackedDigits.pop 2 (2 ^ (remaining + 1)) := by
        simpa using hpopWord
      have hpopBase0 :
          afterPop (inputRegisters regs).base = 2 := by
        simpa using hpopBase
      have hpopBasePred0 :
          afterPop (inputRegisters regs).basePred = 1 := by
        simpa using hpopBasePred
      have hpopOne0 :
          afterPop (inputRegisters regs).one = 1 := by
        simpa using hpopOne
      have hpopWord' :
          afterPop (inputRegisters regs).word =
            2 ^ remaining := by
        rw [hpopWord0]
        simp [PackedDigits.pop, pow_succ]
      have hpopRecovered :
          afterPop (recoveredChunkBits regs) = completed := by
        rw [RAM.Structured.Footprint.runs_eq_outside
          (pop_sourceWritesWithin
            (inputRegisters regs).mainStack) hpop]
        · exact hrecovered
        · intro hmember
          exact recovered_not_mem_inputFootprint regs
            (mainStack_footprint_subset regs hmember)
      let afterIncrement :=
        Basic.exec
          (.add (recoveredChunkBits regs)
            (recoveredChunkBits regs)
            (inputRegisters regs).one)
          afterPop
      let afterTest :=
        Basic.exec
          (.sub (inputRegisters regs).test
            (inputRegisters regs).word
            (inputRegisters regs).one)
          afterIncrement
      have hbody :
          Runs (recoverChunkBitsBody regs)
            store afterTest := by
        simpa [recoverChunkBitsBody, Cmd.seqList,
          afterIncrement, afterTest] using
          Runs.seq hpop
            (Runs.seq
              (Runs.basic
                (.add (recoveredChunkBits regs)
                  (recoveredChunkBits regs)
                  (inputRegisters regs).one)
                afterPop)
              (Runs.basic
                (.sub (inputRegisters regs).test
                  (inputRegisters regs).word
                  (inputRegisters regs).one)
                afterIncrement))
      have hnextWord :
          afterTest (inputRegisters regs).word =
            2 ^ remaining := by
        simp [afterTest, afterIncrement, Basic.exec,
          (inputRegisters regs).index_ne
            (by decide : (0 : Fin 12) ≠ 5),
          (recovered_ne_inputIndex regs 0).symm, hpopWord']
      have hnextRecovered :
          afterTest (recoveredChunkBits regs) =
            completed + 1 := by
        simp [afterTest, afterIncrement, Basic.exec,
          recovered_ne_inputIndex regs 5,
          hpopRecovered, hpopOne0]
      have hnextTest :
          afterTest (inputRegisters regs).test =
            2 ^ remaining - 1 := by
        simp [afterTest, Basic.exec]
        have hwordAfterIncrement :
            afterIncrement (inputRegisters regs).word =
              2 ^ remaining := by
          simp [afterIncrement, Basic.exec,
            (recovered_ne_inputIndex regs 0).symm, hpopWord']
        have honeAfterIncrement :
            afterIncrement (inputRegisters regs).one = 1 := by
          simp [afterIncrement, Basic.exec,
            (recovered_ne_inputIndex regs 6).symm, hpopOne0]
        rw [hwordAfterIncrement, honeAfterIncrement]
      have hnextBase :
          afterTest (inputRegisters regs).base = 2 := by
        simp [afterTest, afterIncrement, Basic.exec,
          (inputRegisters regs).index_ne
            (by decide : (2 : Fin 12) ≠ 5),
          (recovered_ne_inputIndex regs 2).symm, hpopBase0]
      have hnextBasePred :
          afterTest (inputRegisters regs).basePred = 1 := by
        simp [afterTest, afterIncrement, Basic.exec,
          (inputRegisters regs).index_ne
            (by decide : (3 : Fin 12) ≠ 5),
          (recovered_ne_inputIndex regs 3).symm, hpopBasePred0]
      have hnextOne :
          afterTest (inputRegisters regs).one = 1 := by
        simp [afterTest, afterIncrement, Basic.exec,
          (inputRegisters regs).index_ne
            (by decide : (6 : Fin 12) ≠ 5),
          (recovered_ne_inputIndex regs 6).symm, hpopOne0]
      obtain ⟨final, hloop, hfinalWord,
          hfinalRecovered, hfinalTest, hfinalBase,
          hfinalBasePred, hfinalOne⟩ :=
        ih afterTest (completed + 1) hnextWord
          hnextRecovered hnextTest hnextBase hnextBasePred
          hnextOne
      refine
        ⟨final,
          Runs.whileNonzero htestNonzero hbody hloop,
          hfinalWord, ?_, hfinalTest, hfinalBase,
          hfinalBasePred, hfinalOne⟩
      rw [hfinalRecovered]
      omega

private theorem recoverLoop_invariantRuns
    (regs : NeighborhoodTrial.Registers controller)
    (allowed : Finset ℕ) (bound : ℕ)
    (store : Store) (remaining completed : ℕ)
    (hword :
      store (inputRegisters regs).word = 2 ^ remaining)
    (hrecovered :
      store (recoveredChunkBits regs) = completed)
    (htest :
      store (inputRegisters regs).test = 2 ^ remaining - 1)
    (hbase : store (inputRegisters regs).base = 2)
    (hbasePred : store (inputRegisters regs).basePred = 1)
    (hone : store (inputRegisters regs).one = 1)
    (hwordBound : 2 ^ remaining ≤ bound)
    (htotalBound : completed + remaining ≤ bound)
    (hstore :
      NeighborhoodProgram.ValuesWithin allowed bound store) :
    ∃ final steps,
      InvariantRuns
        (NeighborhoodProgram.ValuesWithin allowed bound)
        (.whileNonzero (inputRegisters regs).test
          (recoverChunkBitsBody regs))
        store final steps ∧
      final (inputRegisters regs).word = 1 ∧
      final (recoveredChunkBits regs) = completed + remaining ∧
      final (inputRegisters regs).test = 0 ∧
      final (inputRegisters regs).base = 2 ∧
      final (inputRegisters regs).basePred = 1 ∧
      final (inputRegisters regs).one = 1 := by
  induction remaining generalizing store completed with
  | zero =>
      have htestZero :
          store (inputRegisters regs).test = 0 := by
        simpa using htest
      exact
        ⟨store, 1,
          InvariantRuns.whileZero htestZero hstore,
          by simpa using hword, by simpa using hrecovered,
          htestZero, hbase, hbasePred, hone⟩
  | succ remaining ih =>
      have htestNonzero :
          store (inputRegisters regs).test ≠ 0 := by
        rw [htest]
        have hpow : 0 < 2 ^ (remaining + 1) :=
          pow_pos (by omega) _
        omega
      obtain ⟨afterPop, popSteps, hpop, hpopWord,
          _hpopQuotient, _hpopTest, hpopBase,
          hpopBasePred, hpopOne⟩ :=
        NeighborhoodProgram.pop_invariantRuns
          (inputRegisters regs).mainStack allowed bound store
          2 (2 ^ (remaining + 1)) (by omega)
          hword hbase (by simpa using hbasePred) hone
          hwordBound hstore
      have hpopWord0 :
          afterPop (inputRegisters regs).word =
            PackedDigits.pop 2 (2 ^ (remaining + 1)) := by
        simpa using hpopWord
      have hpopWord' :
          afterPop (inputRegisters regs).word =
            2 ^ remaining := by
        rw [hpopWord0]
        simp [PackedDigits.pop, pow_succ]
      have hpopBase0 :
          afterPop (inputRegisters regs).base = 2 := by
        simpa using hpopBase
      have hpopBasePred0 :
          afterPop (inputRegisters regs).basePred = 1 := by
        simpa using hpopBasePred
      have hpopOne0 :
          afterPop (inputRegisters regs).one = 1 := by
        simpa using hpopOne
      have hpopRecovered :
          afterPop (recoveredChunkBits regs) = completed := by
        rw [RAM.Structured.Footprint.runs_eq_outside
          (pop_sourceWritesWithin
            (inputRegisters regs).mainStack)
          (InvariantRuns.toRuns hpop)]
        · exact hrecovered
        · intro hmember
          exact recovered_not_mem_inputFootprint regs
            (mainStack_footprint_subset regs hmember)
      let afterIncrement :=
        Basic.exec
          (.add (recoveredChunkBits regs)
            (recoveredChunkBits regs)
            (inputRegisters regs).one)
          afterPop
      have hafterIncrement :
          NeighborhoodProgram.ValuesWithin
            allowed bound afterIncrement := by
        apply valuesWithin_update allowed bound
          (recoveredChunkBits regs)
          (afterPop (recoveredChunkBits regs) +
            afterPop (inputRegisters regs).one)
          afterPop (InvariantRuns.final hpop)
        rw [hpopRecovered, hpopOne0]
        omega
      let afterTest :=
        Basic.exec
          (.sub (inputRegisters regs).test
            (inputRegisters regs).word
            (inputRegisters regs).one)
          afterIncrement
      have hnextWord :
          afterTest (inputRegisters regs).word =
            2 ^ remaining := by
        simp [afterTest, afterIncrement, Basic.exec,
          (inputRegisters regs).index_ne
            (by decide : (0 : Fin 12) ≠ 5),
          (recovered_ne_inputIndex regs 0).symm, hpopWord']
      have hnextRecovered :
          afterTest (recoveredChunkBits regs) =
            completed + 1 := by
        simp [afterTest, afterIncrement, Basic.exec,
          recovered_ne_inputIndex regs 5,
          hpopRecovered, hpopOne0]
      have hnextTest :
          afterTest (inputRegisters regs).test =
            2 ^ remaining - 1 := by
        simp [afterTest, Basic.exec]
        have hwordAfterIncrement :
            afterIncrement (inputRegisters regs).word =
              2 ^ remaining := by
          simp [afterIncrement, Basic.exec,
            (recovered_ne_inputIndex regs 0).symm, hpopWord']
        have honeAfterIncrement :
            afterIncrement (inputRegisters regs).one = 1 := by
          simp [afterIncrement, Basic.exec,
            (recovered_ne_inputIndex regs 6).symm, hpopOne0]
        rw [hwordAfterIncrement, honeAfterIncrement]
      have hnextBase :
          afterTest (inputRegisters regs).base = 2 := by
        simp [afterTest, afterIncrement, Basic.exec,
          (inputRegisters regs).index_ne
            (by decide : (2 : Fin 12) ≠ 5),
          (recovered_ne_inputIndex regs 2).symm, hpopBase0]
      have hnextBasePred :
          afterTest (inputRegisters regs).basePred = 1 := by
        simp [afterTest, afterIncrement, Basic.exec,
          (inputRegisters regs).index_ne
            (by decide : (3 : Fin 12) ≠ 5),
          (recovered_ne_inputIndex regs 3).symm, hpopBasePred0]
      have hnextOne :
          afterTest (inputRegisters regs).one = 1 := by
        simp [afterTest, afterIncrement, Basic.exec,
          (inputRegisters regs).index_ne
            (by decide : (6 : Fin 12) ≠ 5),
          (recovered_ne_inputIndex regs 6).symm, hpopOne0]
      have hafterTest :
          NeighborhoodProgram.ValuesWithin
            allowed bound afterTest := by
        apply valuesWithin_update allowed bound
          (inputRegisters regs).test
          (afterIncrement (inputRegisters regs).word -
            afterIncrement (inputRegisters regs).one)
          afterIncrement hafterIncrement
        have hnextWordBound :
            2 ^ remaining ≤ bound := by
          exact (Nat.pow_le_pow_right (by omega)
            (show remaining ≤ remaining + 1 by omega)).trans
              hwordBound
        simpa [afterIncrement, Basic.exec,
          (recovered_ne_inputIndex regs 0).symm,
          (recovered_ne_inputIndex regs 6).symm,
          hpopWord', hpopOne0] using
          (Nat.sub_le (2 ^ remaining) 1).trans
            hnextWordBound
      have hbody :
          InvariantRuns
            (NeighborhoodProgram.ValuesWithin allowed bound)
            (recoverChunkBitsBody regs)
            store afterTest (popSteps + 2) := by
        simpa [recoverChunkBitsBody, Cmd.seqList,
          afterIncrement, afterTest] using
          InvariantRuns.seq hpop
            (InvariantRuns.seq
              (InvariantRuns.basic
                (.add (recoveredChunkBits regs)
                  (recoveredChunkBits regs)
                  (inputRegisters regs).one)
                afterPop (InvariantRuns.final hpop)
                hafterIncrement)
              (InvariantRuns.basic
                (.sub (inputRegisters regs).test
                  (inputRegisters regs).word
                  (inputRegisters regs).one)
                afterIncrement hafterIncrement hafterTest))
      have hnextWordBound :
          2 ^ remaining ≤ bound := by
        exact (Nat.pow_le_pow_right (by omega)
          (show remaining ≤ remaining + 1 by omega)).trans
            hwordBound
      obtain ⟨final, loopSteps, hloop, hfinalWord,
          hfinalRecovered, hfinalTest, hfinalBase,
          hfinalBasePred, hfinalOne⟩ :=
        ih afterTest (completed + 1) hnextWord
          hnextRecovered hnextTest hnextBase hnextBasePred
          hnextOne hnextWordBound (by omega) hafterTest
      refine
        ⟨final, popSteps + 2 + loopSteps + 2,
          InvariantRuns.whileNonzero htestNonzero hbody hloop,
          hfinalWord, ?_, hfinalTest, hfinalBase,
          hfinalBasePred, hfinalOne⟩
      rw [hfinalRecovered]
      omega

private theorem recoverChunkBits_runs
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store) (chunkBits : ℕ)
    (hradix :
      store (Layout.chunkRadix regs) = 2 ^ chunkBits) :
    ∃ final,
      Runs (recoverChunkBits regs) store final ∧
      final (recoveredChunkBits regs) = chunkBits ∧
      final (inputRegisters regs).word = 1 ∧
      final (inputRegisters regs).test = 0 ∧
      final (inputRegisters regs).base = 2 ∧
      final (inputRegisters regs).basePred = 1 ∧
      final (inputRegisters regs).one = 1 ∧
      ∀ address, address ∉ recoverFootprint regs →
        final address = store address := by
  let copied :=
    Function.update store (inputRegisters regs).word
      (store (Layout.chunkRadix regs))
  let afterBase :=
    Basic.exec (.imm (inputRegisters regs).base 2) copied
  let afterBasePred :=
    Basic.exec
      (.imm (inputRegisters regs).basePred 1) afterBase
  let afterOne :=
    Basic.exec (.imm (inputRegisters regs).one 1) afterBasePred
  let afterRecovered :=
    Basic.exec (.imm (recoveredChunkBits regs) 0) afterOne
  let ready :=
    Basic.exec
      (.sub (inputRegisters regs).test
        (inputRegisters regs).word
        (inputRegisters regs).one)
      afterRecovered
  have hcopy :
      Runs
        (copy (inputRegisters regs).word
          (Layout.chunkRadix regs))
        store copied := by
    exact copy_runs store
      (regs.injective.ne (by decide))
  have hreadyWord :
      ready (inputRegisters regs).word = 2 ^ chunkBits := by
    simp [ready, afterRecovered, afterOne, afterBasePred,
      afterBase, Basic.exec, copied,
      (inputRegisters regs).index_ne
        (by decide : (0 : Fin 12) ≠ 2),
      (inputRegisters regs).index_ne
        (by decide : (0 : Fin 12) ≠ 3),
      (inputRegisters regs).index_ne
        (by decide : (0 : Fin 12) ≠ 6),
      (inputRegisters regs).index_ne
        (by decide : (0 : Fin 12) ≠ 5),
      (recovered_ne_inputIndex regs 0).symm, hradix]
  have hreadyRecovered :
      ready (recoveredChunkBits regs) = 0 := by
    simp [ready, afterRecovered, Basic.exec,
      recovered_ne_inputIndex regs 5]
  have hreadyTest :
      ready (inputRegisters regs).test =
        2 ^ chunkBits - 1 := by
    simp [ready, afterRecovered, afterOne, afterBasePred,
      afterBase, Basic.exec, copied,
      (inputRegisters regs).index_ne
        (by decide : (0 : Fin 12) ≠ 2),
      (inputRegisters regs).index_ne
        (by decide : (0 : Fin 12) ≠ 3),
      (inputRegisters regs).index_ne
        (by decide : (0 : Fin 12) ≠ 6),
      (recovered_ne_inputIndex regs 0).symm,
      (recovered_ne_inputIndex regs 6).symm, hradix]
  have hreadyBase :
      ready (inputRegisters regs).base = 2 := by
    simp [ready, afterRecovered, afterOne, afterBasePred,
      afterBase, Basic.exec,
      (inputRegisters regs).index_ne
        (by decide : (2 : Fin 12) ≠ 3),
      (inputRegisters regs).index_ne
        (by decide : (2 : Fin 12) ≠ 6),
      (inputRegisters regs).index_ne
        (by decide : (2 : Fin 12) ≠ 5),
      (recovered_ne_inputIndex regs 2).symm]
  have hreadyBasePred :
      ready (inputRegisters regs).basePred = 1 := by
    simp [ready, afterRecovered, afterOne, afterBasePred,
      Basic.exec,
      (inputRegisters regs).index_ne
        (by decide : (3 : Fin 12) ≠ 6),
      (inputRegisters regs).index_ne
        (by decide : (3 : Fin 12) ≠ 5),
      (recovered_ne_inputIndex regs 3).symm]
  have hreadyOne :
      ready (inputRegisters regs).one = 1 := by
    simp [ready, afterRecovered, afterOne, Basic.exec,
      (inputRegisters regs).index_ne
        (by decide : (6 : Fin 12) ≠ 5),
      (recovered_ne_inputIndex regs 6).symm]
  obtain ⟨final, hloop, hfinalWord, hfinalRecovered,
      hfinalTest, hfinalBase, hfinalBasePred, hfinalOne⟩ :=
    recoverLoop_runs regs ready chunkBits 0
      hreadyWord hreadyRecovered hreadyTest hreadyBase
      hreadyBasePred hreadyOne
  have hrun :
      Runs (recoverChunkBits regs) store final := by
    simpa [recoverChunkBits, Cmd.seqList, afterBase,
      afterBasePred, afterOne, afterRecovered, ready] using
      Runs.seq hcopy
        (Runs.seq
          (Runs.basic
            (.imm (inputRegisters regs).base 2) copied)
          (Runs.seq
            (Runs.basic
              (.imm (inputRegisters regs).basePred 1) afterBase)
            (Runs.seq
              (Runs.basic
                (.imm (inputRegisters regs).one 1) afterBasePred)
              (Runs.seq
                (Runs.basic
                  (.imm (recoveredChunkBits regs) 0) afterOne)
                (Runs.seq
                  (Runs.basic
                    (.sub (inputRegisters regs).test
                      (inputRegisters regs).word
                      (inputRegisters regs).one)
                    afterRecovered)
                  hloop)))))
  refine
    ⟨final, hrun, by simpa using hfinalRecovered,
      hfinalWord, hfinalTest, hfinalBase, hfinalBasePred,
      hfinalOne, ?_⟩
  intro address haddress
  exact RAM.Structured.Footprint.runs_eq_outside
    (recoverChunkBits_writesWithin_local regs)
    hrun haddress

private theorem recoverChunkBits_invariantRuns
    (regs : NeighborhoodTrial.Registers controller)
    (allowed : Finset ℕ) (bound : ℕ)
    (store : Store) (chunkBits : ℕ)
    (hradix :
      store (Layout.chunkRadix regs) = 2 ^ chunkBits)
    (hradixBound : 2 ^ chunkBits ≤ bound)
    (hchunkBitsBound : chunkBits ≤ bound)
    (htwoBound : 2 ≤ bound)
    (hstore :
      NeighborhoodProgram.ValuesWithin allowed bound store) :
    ∃ final steps,
      InvariantRuns
        (NeighborhoodProgram.ValuesWithin allowed bound)
        (recoverChunkBits regs) store final steps ∧
      final (recoveredChunkBits regs) = chunkBits ∧
      final (inputRegisters regs).word = 1 ∧
      final (inputRegisters regs).test = 0 ∧
      final (inputRegisters regs).base = 2 ∧
      final (inputRegisters regs).basePred = 1 ∧
      final (inputRegisters regs).one = 1 ∧
      ∀ address, address ∉ recoverFootprint regs →
        final address = store address := by
  let copied :=
    Function.update store (inputRegisters regs).word
      (store (Layout.chunkRadix regs))
  let afterBase :=
    Basic.exec (.imm (inputRegisters regs).base 2) copied
  let afterBasePred :=
    Basic.exec
      (.imm (inputRegisters regs).basePred 1) afterBase
  let afterOne :=
    Basic.exec (.imm (inputRegisters regs).one 1) afterBasePred
  let afterRecovered :=
    Basic.exec (.imm (recoveredChunkBits regs) 0) afterOne
  let ready :=
    Basic.exec
      (.sub (inputRegisters regs).test
        (inputRegisters regs).word
        (inputRegisters regs).one)
      afterRecovered
  have hcopy :
      InvariantRuns
        (NeighborhoodProgram.ValuesWithin allowed bound)
        (copy (inputRegisters regs).word
          (Layout.chunkRadix regs))
        store copied 2 := by
    exact copy_invariantRuns allowed bound
      (inputRegisters regs).word (Layout.chunkRadix regs)
      store (regs.injective.ne (by decide))
      (by simpa [hradix] using hradixBound) hstore
  have hcopied :
      NeighborhoodProgram.ValuesWithin allowed bound copied :=
    InvariantRuns.final hcopy
  have hafterBase :
      NeighborhoodProgram.ValuesWithin allowed bound afterBase :=
    valuesWithin_update allowed bound
      (inputRegisters regs).base 2 copied hcopied htwoBound
  have hafterBasePred :
      NeighborhoodProgram.ValuesWithin allowed bound afterBasePred :=
    valuesWithin_update allowed bound
      (inputRegisters regs).basePred 1 afterBase hafterBase
      (by omega)
  have hafterOne :
      NeighborhoodProgram.ValuesWithin allowed bound afterOne :=
    valuesWithin_update allowed bound
      (inputRegisters regs).one 1 afterBasePred
      hafterBasePred (by omega)
  have hafterRecovered :
      NeighborhoodProgram.ValuesWithin allowed bound afterRecovered :=
    valuesWithin_update allowed bound
      (recoveredChunkBits regs) 0 afterOne hafterOne
      (by omega)
  have hreadyWord :
      ready (inputRegisters regs).word = 2 ^ chunkBits := by
    simp [ready, afterRecovered, afterOne, afterBasePred,
      afterBase, Basic.exec, copied,
      (inputRegisters regs).index_ne
        (by decide : (0 : Fin 12) ≠ 2),
      (inputRegisters regs).index_ne
        (by decide : (0 : Fin 12) ≠ 3),
      (inputRegisters regs).index_ne
        (by decide : (0 : Fin 12) ≠ 6),
      (inputRegisters regs).index_ne
        (by decide : (0 : Fin 12) ≠ 5),
      (recovered_ne_inputIndex regs 0).symm, hradix]
  have hreadyRecovered :
      ready (recoveredChunkBits regs) = 0 := by
    simp [ready, afterRecovered, Basic.exec,
      recovered_ne_inputIndex regs 5]
  have hreadyTest :
      ready (inputRegisters regs).test =
        2 ^ chunkBits - 1 := by
    simp [ready, afterRecovered, afterOne, afterBasePred,
      afterBase, Basic.exec, copied,
      (inputRegisters regs).index_ne
        (by decide : (0 : Fin 12) ≠ 2),
      (inputRegisters regs).index_ne
        (by decide : (0 : Fin 12) ≠ 3),
      (inputRegisters regs).index_ne
        (by decide : (0 : Fin 12) ≠ 6),
      (recovered_ne_inputIndex regs 0).symm,
      (recovered_ne_inputIndex regs 6).symm, hradix]
  have hreadyBase :
      ready (inputRegisters regs).base = 2 := by
    simp [ready, afterRecovered, afterOne, afterBasePred,
      afterBase, Basic.exec,
      (inputRegisters regs).index_ne
        (by decide : (2 : Fin 12) ≠ 3),
      (inputRegisters regs).index_ne
        (by decide : (2 : Fin 12) ≠ 6),
      (inputRegisters regs).index_ne
        (by decide : (2 : Fin 12) ≠ 5),
      (recovered_ne_inputIndex regs 2).symm]
  have hreadyBasePred :
      ready (inputRegisters regs).basePred = 1 := by
    simp [ready, afterRecovered, afterOne, afterBasePred,
      Basic.exec,
      (inputRegisters regs).index_ne
        (by decide : (3 : Fin 12) ≠ 6),
      (inputRegisters regs).index_ne
        (by decide : (3 : Fin 12) ≠ 5),
      (recovered_ne_inputIndex regs 3).symm]
  have hreadyOne :
      ready (inputRegisters regs).one = 1 := by
    simp [ready, afterRecovered, afterOne, Basic.exec,
      (inputRegisters regs).index_ne
        (by decide : (6 : Fin 12) ≠ 5),
      (recovered_ne_inputIndex regs 6).symm]
  have hready :
      NeighborhoodProgram.ValuesWithin allowed bound ready := by
    apply valuesWithin_update allowed bound
      (inputRegisters regs).test
      (afterRecovered (inputRegisters regs).word -
        afterRecovered (inputRegisters regs).one)
      afterRecovered hafterRecovered
    have hwordAfterRecovered :
        afterRecovered (inputRegisters regs).word =
          2 ^ chunkBits := by
      simpa [ready, Basic.exec,
        (inputRegisters regs).index_ne
          (by decide : (0 : Fin 12) ≠ 5)] using
        hreadyWord
    exact
      (Nat.sub_le _ _).trans
        (by simpa [hwordAfterRecovered] using hradixBound)
  obtain ⟨final, loopSteps, hloop, hfinalWord,
      hfinalRecovered, hfinalTest, hfinalBase,
      hfinalBasePred, hfinalOne⟩ :=
    recoverLoop_invariantRuns regs allowed bound ready
      chunkBits 0 hreadyWord hreadyRecovered hreadyTest
      hreadyBase hreadyBasePred hreadyOne hradixBound
      (by simpa using hchunkBitsBound) hready
  have hinvariant :
      InvariantRuns
        (NeighborhoodProgram.ValuesWithin allowed bound)
        (recoverChunkBits regs) store final
        (2 + (1 + (1 + (1 + (1 + (1 + loopSteps)))))) := by
    simpa [recoverChunkBits, Cmd.seqList, afterBase,
      afterBasePred, afterOne, afterRecovered, ready] using
      InvariantRuns.seq hcopy
        (InvariantRuns.seq
          (InvariantRuns.basic
            (.imm (inputRegisters regs).base 2)
            copied hcopied hafterBase)
          (InvariantRuns.seq
            (InvariantRuns.basic
              (.imm (inputRegisters regs).basePred 1)
              afterBase hafterBase hafterBasePred)
            (InvariantRuns.seq
              (InvariantRuns.basic
                (.imm (inputRegisters regs).one 1)
                afterBasePred hafterBasePred hafterOne)
              (InvariantRuns.seq
                (InvariantRuns.basic
                  (.imm (recoveredChunkBits regs) 0)
                  afterOne hafterOne hafterRecovered)
                (InvariantRuns.seq
                  (InvariantRuns.basic
                    (.sub (inputRegisters regs).test
                      (inputRegisters regs).word
                      (inputRegisters regs).one)
                    afterRecovered hafterRecovered hready)
                  hloop)))))
  obtain ⟨semanticFinal, hsemanticRun, hsemanticRecovered,
      hsemanticWord, hsemanticTest, hsemanticBase,
      hsemanticBasePred, hsemanticOne, hsemanticOutside⟩ :=
    recoverChunkBits_runs regs store chunkBits hradix
  have heq : final = semanticFinal :=
    runs_final_eq (InvariantRuns.toRuns hinvariant) hsemanticRun
  subst semanticFinal
  exact
    ⟨final,
      2 + (1 + (1 + (1 + (1 + (1 + loopSteps))))),
      hinvariant, hsemanticRecovered, hsemanticWord,
      hsemanticTest, hsemanticBase, hsemanticBasePred,
      hsemanticOne, hsemanticOutside⟩

private theorem decodeTapeBlock_writesWithin_local
    (workTapeCount : ℕ)
    (regs : NeighborhoodTrial.Registers controller) :
    RAM.Structured.Footprint.CmdWritesWithin
      (inputRegisters regs).footprint
      (decodeTapeBlock workTapeCount regs) := by
  have hbufferPeek :
      RAM.Structured.Footprint.CmdWritesWithin
        (inputRegisters regs).footprint
        (NeighborhoodProgram.peek
          (inputRegisters regs).bufferStack) := by
    apply cmdWritesWithin_mono
      (bufferStack_footprint_subset regs)
    exact peek_sourceWritesWithin _
  have hbufferPop :
      RAM.Structured.Footprint.CmdWritesWithin
        (inputRegisters regs).footprint
        (NeighborhoodProgram.pop
          (inputRegisters regs).bufferStack) := by
    apply cmdWritesWithin_mono
      (bufferStack_footprint_subset regs)
    exact pop_sourceWritesWithin _
  simp [decodeTapeBlock, copy, Cmd.seqList,
    RAM.Structured.Footprint.CmdWritesWithin,
    RAM.Structured.Footprint.BasicWritesWithin,
    (inputRegisters regs).index_mem_footprint,
    hbufferPeek, hbufferPop]

private theorem inputIndex_not_mem_bufferStack
    (regs : NeighborhoodTrial.Registers controller)
    (slot : Fin 12)
    (hslot :
      ∀ index,
        NeighborhoodProgram.BankRegisters.bufferMap index ≠ slot) :
    (inputRegisters regs).index slot ∉
      (inputRegisters regs).bufferStack.footprint := by
  intro hmember
  rcases Finset.mem_image.mp hmember with
    ⟨index, _, heq⟩
  apply hslot index
  exact (inputRegisters regs).injective heq

private theorem decodeTapeBlock_runs
    (workTapeCount : ℕ)
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store) (tape block : ℕ)
    (htape : tape < tapeCount workTapeCount)
    (hpacked :
      store (packedTapeBlock regs) =
        tapeBlockCode workTapeCount tape block) :
    ∃ final,
      Runs (decodeTapeBlock workTapeCount regs) store final ∧
      final (inputRegisters regs).indexCount = tape ∧
      final (inputRegisters regs).buffer = block ∧
      final (inputRegisters regs).one = 1 ∧
      final (inputRegisters regs).replacement =
        store (inputRegisters regs).replacement ∧
      final (inputRegisters regs).word =
        store (inputRegisters regs).word ∧
      ∀ address,
        address ∉ (inputRegisters regs).footprint →
        final address = store address := by
  let copied :=
    Function.update store (inputRegisters regs).buffer
      (store (packedTapeBlock regs))
  let afterBase :=
    Basic.exec
      (.imm (inputRegisters regs).base
        (tapeCount workTapeCount))
      copied
  let afterBasePred :=
    Basic.exec
      (.imm (inputRegisters regs).basePred
        (tapeCount workTapeCount - 1))
      afterBase
  let ready :=
    Basic.exec (.imm (inputRegisters regs).one 1) afterBasePred
  have hcopy :
      Runs
        (copy (inputRegisters regs).buffer
          (packedTapeBlock regs))
        store copied := by
    exact copy_runs store
      (regs.injective.ne (by decide))
  have hreadyWord :
      ready (inputRegisters regs).buffer =
        tapeBlockCode workTapeCount tape block := by
    simp [ready, afterBasePred, afterBase, copied, Basic.exec,
      (inputRegisters regs).index_ne
        (by decide : (1 : Fin 12) ≠ 2),
      (inputRegisters regs).index_ne
        (by decide : (1 : Fin 12) ≠ 3),
      (inputRegisters regs).index_ne
        (by decide : (1 : Fin 12) ≠ 6),
      hpacked]
  have hreadyBase :
      ready (inputRegisters regs).base =
        tapeCount workTapeCount := by
    simp [ready, afterBasePred, afterBase, Basic.exec,
      (inputRegisters regs).index_ne
        (by decide : (2 : Fin 12) ≠ 3),
      (inputRegisters regs).index_ne
        (by decide : (2 : Fin 12) ≠ 6)]
  have hreadyBasePred :
      ready (inputRegisters regs).basePred =
        tapeCount workTapeCount - 1 := by
    simp [ready, afterBasePred, Basic.exec,
      (inputRegisters regs).index_ne
        (by decide : (3 : Fin 12) ≠ 6)]
  have hreadyOne :
      ready (inputRegisters regs).one = 1 := by
    simp [ready, Basic.exec]
  have hbasePositive : 0 < tapeCount workTapeCount := by
    unfold tapeCount
    omega
  obtain ⟨afterPeek, hpeek, hpeekWord, hpeekValue,
      _hpeekTest, hpeekBase, hpeekBasePred⟩ :=
    NeighborhoodProgram.peek_runs
      (inputRegisters regs).bufferStack ready
      (tapeCount workTapeCount)
      (tapeBlockCode workTapeCount tape block)
      hbasePositive hreadyWord hreadyBase hreadyBasePred
  have hpeekOne :
      afterPeek (inputRegisters regs).one = 1 := by
    calc
      afterPeek (inputRegisters regs).one =
          ready (inputRegisters regs).one := by
        apply RAM.Structured.Footprint.runs_eq_outside
          (peek_sourceWritesWithin_withoutOne
            (inputRegisters regs).bufferStack)
          hpeek
        simp
      _ = 1 := hreadyOne
  obtain ⟨afterPop, hpop, hpopWord, _hpopQuotient,
      _hpopTest, _hpopBase, _hpopBasePred, hpopOne⟩ :=
    NeighborhoodProgram.pop_runs
      (inputRegisters regs).bufferStack afterPeek
      (tapeCount workTapeCount)
      (tapeBlockCode workTapeCount tape block)
      hbasePositive hpeekWord hpeekBase hpeekBasePred hpeekOne
  have hpeekTape :
      afterPeek (inputRegisters regs).value = tape := by
    rw [show
      afterPeek (inputRegisters regs).value =
        PackedDigits.digit
          (tapeCount workTapeCount)
          (tapeBlockCode workTapeCount tape block) 0 by
      simpa using hpeekValue]
    simp [PackedDigits.digit, tapeBlockCode,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt htape]
  have hpopTape :
      afterPop (inputRegisters regs).value = tape := by
    calc
      afterPop (inputRegisters regs).value =
          afterPeek (inputRegisters regs).value := by
        apply RAM.Structured.Footprint.runs_eq_outside
          (pop_sourceWritesWithin_withoutValue
            (inputRegisters regs).bufferStack)
          hpop
        simp
      _ = tape := hpeekTape
  have hpopBlock :
      afterPop (inputRegisters regs).buffer = block := by
    rw [show
      afterPop (inputRegisters regs).buffer =
        PackedDigits.pop
          (tapeCount workTapeCount)
          (tapeBlockCode workTapeCount tape block) by
      simpa using hpopWord]
    simp [PackedDigits.pop, tapeBlockCode,
      Nat.add_mul_div_left, Nat.div_eq_of_lt htape,
      hbasePositive]
  let final :=
    Function.update afterPop
      (inputRegisters regs).indexCount
      (afterPop (inputRegisters regs).value)
  have hfinalCopy :
      Runs
        (copy (inputRegisters regs).indexCount
          (inputRegisters regs).value)
        afterPop final := by
    exact copy_runs afterPop
      ((inputRegisters regs).index_ne (by decide))
  have hrun :
      Runs (decodeTapeBlock workTapeCount regs) store final := by
    simpa [decodeTapeBlock, Cmd.seqList, afterBase,
      afterBasePred, ready, final] using
      Runs.seq hcopy
        (Runs.seq
          (Runs.basic
            (.imm (inputRegisters regs).base
              (tapeCount workTapeCount)) copied)
          (Runs.seq
            (Runs.basic
              (.imm (inputRegisters regs).basePred
                (tapeCount workTapeCount - 1))
              afterBase)
            (Runs.seq
              (Runs.basic
                (.imm (inputRegisters regs).one 1)
                afterBasePred)
              (Runs.seq hpeek
                (Runs.seq hpop hfinalCopy)))))
  refine ⟨final, hrun, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [final, hpopTape]
  · simp [final,
      (inputRegisters regs).index_ne
        (by decide : (1 : Fin 12) ≠ 8),
      hpopBlock]
  · have hpopOne0 :
        afterPop (inputRegisters regs).one = 1 := by
      simpa using hpopOne
    simp [final,
      (inputRegisters regs).index_ne
        (by decide : (6 : Fin 12) ≠ 8),
      hpopOne0]
  · have hpopReplacement :
        afterPop (inputRegisters regs).replacement =
          afterPeek (inputRegisters regs).replacement := by
      apply RAM.Structured.Footprint.runs_eq_outside
        (pop_sourceWritesWithin
          (inputRegisters regs).bufferStack)
        hpop
      exact inputIndex_not_mem_bufferStack regs 11 (by decide)
    have hpeekReplacement :
        afterPeek (inputRegisters regs).replacement =
          ready (inputRegisters regs).replacement := by
      apply RAM.Structured.Footprint.runs_eq_outside
        (peek_sourceWritesWithin
          (inputRegisters regs).bufferStack)
        hpeek
      exact inputIndex_not_mem_bufferStack regs 11 (by decide)
    simp [final,
      (inputRegisters regs).index_ne
        (by decide : (11 : Fin 12) ≠ 8),
      hpopReplacement, hpeekReplacement,
      ready, afterBasePred, afterBase, copied, Basic.exec,
      (inputRegisters regs).index_ne
        (by decide : (11 : Fin 12) ≠ 1),
      (inputRegisters regs).index_ne
        (by decide : (11 : Fin 12) ≠ 2),
      (inputRegisters regs).index_ne
        (by decide : (11 : Fin 12) ≠ 3),
      (inputRegisters regs).index_ne
        (by decide : (11 : Fin 12) ≠ 6)]
  · have hpopWordPreserved :
        afterPop (inputRegisters regs).word =
          afterPeek (inputRegisters regs).word := by
      apply RAM.Structured.Footprint.runs_eq_outside
        (pop_sourceWritesWithin
          (inputRegisters regs).bufferStack)
        hpop
      exact inputIndex_not_mem_bufferStack regs 0 (by decide)
    have hpeekWordPreserved :
        afterPeek (inputRegisters regs).word =
          ready (inputRegisters regs).word := by
      apply RAM.Structured.Footprint.runs_eq_outside
        (peek_sourceWritesWithin
          (inputRegisters regs).bufferStack)
        hpeek
      exact inputIndex_not_mem_bufferStack regs 0 (by decide)
    simp [final,
      (inputRegisters regs).index_ne
        (by decide : (0 : Fin 12) ≠ 8),
      hpopWordPreserved, hpeekWordPreserved,
      ready, afterBasePred, afterBase, copied, Basic.exec,
      (inputRegisters regs).index_ne
        (by decide : (0 : Fin 12) ≠ 1),
      (inputRegisters regs).index_ne
        (by decide : (0 : Fin 12) ≠ 2),
      (inputRegisters regs).index_ne
        (by decide : (0 : Fin 12) ≠ 3),
      (inputRegisters regs).index_ne
        (by decide : (0 : Fin 12) ≠ 6)]
  · intro address haddress
    exact RAM.Structured.Footprint.runs_eq_outside
      (decodeTapeBlock_writesWithin_local workTapeCount regs)
      hrun haddress

private theorem decodeTapeBlock_invariantRuns
    (workTapeCount : ℕ)
    (regs : NeighborhoodTrial.Registers controller)
    (allowed : Finset ℕ) (bound : ℕ)
    (store : Store) (tape block : ℕ)
    (htape : tape < tapeCount workTapeCount)
    (hpacked :
      store (packedTapeBlock regs) =
        tapeBlockCode workTapeCount tape block)
    (hpackedBound :
      tapeBlockCode workTapeCount tape block ≤ bound)
    (hbaseBound : tapeCount workTapeCount ≤ bound)
    (hstore :
      NeighborhoodProgram.ValuesWithin allowed bound store) :
    ∃ final steps,
      InvariantRuns
        (NeighborhoodProgram.ValuesWithin allowed bound)
        (decodeTapeBlock workTapeCount regs) store final steps ∧
      final (inputRegisters regs).indexCount = tape ∧
      final (inputRegisters regs).buffer = block ∧
      final (inputRegisters regs).one = 1 ∧
      final (inputRegisters regs).replacement =
        store (inputRegisters regs).replacement ∧
      final (inputRegisters regs).word =
        store (inputRegisters regs).word ∧
      ∀ address,
        address ∉ (inputRegisters regs).footprint →
        final address = store address := by
  let copied :=
    Function.update store (inputRegisters regs).buffer
      (store (packedTapeBlock regs))
  let afterBase :=
    Basic.exec
      (.imm (inputRegisters regs).base
        (tapeCount workTapeCount))
      copied
  let afterBasePred :=
    Basic.exec
      (.imm (inputRegisters regs).basePred
        (tapeCount workTapeCount - 1))
      afterBase
  let ready :=
    Basic.exec (.imm (inputRegisters regs).one 1) afterBasePred
  have hcopy :
      InvariantRuns
        (NeighborhoodProgram.ValuesWithin allowed bound)
        (copy (inputRegisters regs).buffer
          (packedTapeBlock regs))
        store copied 2 := by
    exact copy_invariantRuns allowed bound
      (inputRegisters regs).buffer (packedTapeBlock regs)
      store (regs.injective.ne (by decide))
      (by simpa [hpacked] using hpackedBound) hstore
  have hcopied :
      NeighborhoodProgram.ValuesWithin allowed bound copied :=
    InvariantRuns.final hcopy
  have hafterBase :
      NeighborhoodProgram.ValuesWithin allowed bound afterBase :=
    valuesWithin_update allowed bound
      (inputRegisters regs).base (tapeCount workTapeCount)
      copied hcopied hbaseBound
  have hafterBasePred :
      NeighborhoodProgram.ValuesWithin allowed bound afterBasePred :=
    valuesWithin_update allowed bound
      (inputRegisters regs).basePred
      (tapeCount workTapeCount - 1)
      afterBase hafterBase
      ((Nat.sub_le _ _).trans hbaseBound)
  have hready :
      NeighborhoodProgram.ValuesWithin allowed bound ready :=
    valuesWithin_update allowed bound
      (inputRegisters regs).one 1 afterBasePred
      hafterBasePred (by
        have hpositive : 0 < tapeCount workTapeCount := by
          unfold tapeCount
          omega
        omega)
  have hreadyWord :
      ready (inputRegisters regs).buffer =
        tapeBlockCode workTapeCount tape block := by
    simp [ready, afterBasePred, afterBase, copied, Basic.exec,
      (inputRegisters regs).index_ne
        (by decide : (1 : Fin 12) ≠ 2),
      (inputRegisters regs).index_ne
        (by decide : (1 : Fin 12) ≠ 3),
      (inputRegisters regs).index_ne
        (by decide : (1 : Fin 12) ≠ 6),
      hpacked]
  have hreadyBase :
      ready (inputRegisters regs).base =
        tapeCount workTapeCount := by
    simp [ready, afterBasePred, afterBase, Basic.exec,
      (inputRegisters regs).index_ne
        (by decide : (2 : Fin 12) ≠ 3),
      (inputRegisters regs).index_ne
        (by decide : (2 : Fin 12) ≠ 6)]
  have hreadyBasePred :
      ready (inputRegisters regs).basePred =
        tapeCount workTapeCount - 1 := by
    simp [ready, afterBasePred, Basic.exec,
      (inputRegisters regs).index_ne
        (by decide : (3 : Fin 12) ≠ 6)]
  have hreadyOne :
      ready (inputRegisters regs).one = 1 := by
    simp [ready, Basic.exec]
  have hbasePositive : 0 < tapeCount workTapeCount := by
    unfold tapeCount
    omega
  let digit :=
    PackedDigits.digit
      (tapeCount workTapeCount)
      (tapeBlockCode workTapeCount tape block) 0
  let afterPeek :=
    NeighborhoodProgram.peekResultStore
      (inputRegisters regs).bufferStack digit ready
  obtain ⟨peekSteps, hpeek⟩ :=
    NeighborhoodProgram.peek_invariantRuns
      (inputRegisters regs).bufferStack allowed bound ready
      (tapeCount workTapeCount)
      (tapeBlockCode workTapeCount tape block)
      hbasePositive hreadyWord hreadyBase hreadyBasePred
      hpackedBound hready
  have hpeek0 :
      InvariantRuns
        (NeighborhoodProgram.ValuesWithin allowed bound)
        (NeighborhoodProgram.peek
          (inputRegisters regs).bufferStack)
        ready afterPeek peekSteps := by
    simpa [afterPeek, digit] using hpeek
  have hdigit : digit = tape := by
    simp [digit, PackedDigits.digit, tapeBlockCode,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt htape]
  have hpeekTape :
      afterPeek (inputRegisters regs).value = tape := by
    simp [afterPeek, NeighborhoodProgram.peekResultStore,
      hdigit,
      (inputRegisters regs).index_ne
        (by decide : (7 : Fin 12) ≠ 5)]
  have hpeekWord :
      afterPeek (inputRegisters regs).buffer =
        tapeBlockCode workTapeCount tape block := by
    simp [afterPeek, NeighborhoodProgram.peekResultStore,
      hreadyWord,
      (inputRegisters regs).index_ne
        (by decide : (1 : Fin 12) ≠ 7),
      (inputRegisters regs).index_ne
        (by decide : (1 : Fin 12) ≠ 5)]
  have hpeekBase :
      afterPeek (inputRegisters regs).base =
        tapeCount workTapeCount := by
    simp [afterPeek, NeighborhoodProgram.peekResultStore,
      hreadyBase,
      (inputRegisters regs).index_ne
        (by decide : (2 : Fin 12) ≠ 7),
      (inputRegisters regs).index_ne
        (by decide : (2 : Fin 12) ≠ 5)]
  have hpeekBasePred :
      afterPeek (inputRegisters regs).basePred =
        tapeCount workTapeCount - 1 := by
    simp [afterPeek, NeighborhoodProgram.peekResultStore,
      hreadyBasePred,
      (inputRegisters regs).index_ne
        (by decide : (3 : Fin 12) ≠ 7),
      (inputRegisters regs).index_ne
        (by decide : (3 : Fin 12) ≠ 5)]
  have hpeekOne :
      afterPeek (inputRegisters regs).one = 1 := by
    simp [afterPeek, NeighborhoodProgram.peekResultStore,
      hreadyOne,
      (inputRegisters regs).index_ne
        (by decide : (6 : Fin 12) ≠ 7),
      (inputRegisters regs).index_ne
        (by decide : (6 : Fin 12) ≠ 5)]
  obtain ⟨afterPop, popSteps, hpop, hpopWord,
      _hpopQuotient, _hpopTest, _hpopBase,
      _hpopBasePred, _hpopOne⟩ :=
    NeighborhoodProgram.pop_invariantRuns
      (inputRegisters regs).bufferStack allowed bound afterPeek
      (tapeCount workTapeCount)
      (tapeBlockCode workTapeCount tape block)
      hbasePositive hpeekWord hpeekBase hpeekBasePred hpeekOne
      hpackedBound (InvariantRuns.final hpeek0)
  have hpopTape :
      afterPop (inputRegisters regs).value = tape := by
    calc
      afterPop (inputRegisters regs).value =
          afterPeek (inputRegisters regs).value := by
        apply RAM.Structured.Footprint.runs_eq_outside
          (pop_sourceWritesWithin_withoutValue
            (inputRegisters regs).bufferStack)
          (InvariantRuns.toRuns hpop)
        simp
      _ = tape := hpeekTape
  have hpopBlock :
      afterPop (inputRegisters regs).buffer = block := by
    rw [show
      afterPop (inputRegisters regs).buffer =
        PackedDigits.pop
          (tapeCount workTapeCount)
          (tapeBlockCode workTapeCount tape block) by
      simpa using hpopWord]
    simp [PackedDigits.pop, tapeBlockCode,
      Nat.add_mul_div_left, Nat.div_eq_of_lt htape,
      hbasePositive]
  let final :=
    Function.update afterPop
      (inputRegisters regs).indexCount
      (afterPop (inputRegisters regs).value)
  have hfinalCopy :
      InvariantRuns
        (NeighborhoodProgram.ValuesWithin allowed bound)
        (copy (inputRegisters regs).indexCount
          (inputRegisters regs).value)
        afterPop final 2 := by
    exact copy_invariantRuns allowed bound
      (inputRegisters regs).indexCount
      (inputRegisters regs).value afterPop
      ((inputRegisters regs).index_ne (by decide))
      (by rw [hpopTape]
          exact (Nat.le_of_lt htape).trans hbaseBound)
      (InvariantRuns.final hpop)
  have hinvariant :
      InvariantRuns
        (NeighborhoodProgram.ValuesWithin allowed bound)
        (decodeTapeBlock workTapeCount regs) store final
        (2 + (1 + (1 + (1 +
          (peekSteps + (popSteps + 2)))))) := by
    simpa [decodeTapeBlock, Cmd.seqList, afterBase,
      afterBasePred, ready, final] using
      InvariantRuns.seq hcopy
        (InvariantRuns.seq
          (InvariantRuns.basic
            (.imm (inputRegisters regs).base
              (tapeCount workTapeCount))
            copied hcopied hafterBase)
          (InvariantRuns.seq
            (InvariantRuns.basic
              (.imm (inputRegisters regs).basePred
                (tapeCount workTapeCount - 1))
              afterBase hafterBase hafterBasePred)
            (InvariantRuns.seq
              (InvariantRuns.basic
                (.imm (inputRegisters regs).one 1)
                afterBasePred hafterBasePred hready)
              (InvariantRuns.seq hpeek0
                (InvariantRuns.seq hpop hfinalCopy)))))
  obtain ⟨semanticFinal, hsemanticRun, hsemanticTape,
      hsemanticBlock, hsemanticOne, hsemanticReplacement,
      hsemanticWord, hsemanticOutside⟩ :=
    decodeTapeBlock_runs workTapeCount regs store tape block
      htape hpacked
  have heq : final = semanticFinal :=
    runs_final_eq (InvariantRuns.toRuns hinvariant) hsemanticRun
  subst semanticFinal
  exact
    ⟨final,
      2 + (1 + (1 + (1 + (peekSteps + (popSteps + 2))))),
      hinvariant, hsemanticTape, hsemanticBlock,
      hsemanticOne, hsemanticReplacement, hsemanticWord,
      hsemanticOutside⟩

private theorem prepareCellBit_writesWithin_local
    (regs : NeighborhoodTrial.Registers controller) :
    RAM.Structured.Footprint.CmdWritesWithin
      (inputRegisters regs).footprint
      (prepareCellBit regs) := by
  have hpeek :
      RAM.Structured.Footprint.CmdWritesWithin
        (inputRegisters regs).footprint
        (NeighborhoodProgram.peek
          (inputRegisters regs).bufferStack) := by
    apply cmdWritesWithin_mono
      (bufferStack_footprint_subset regs)
    exact peek_sourceWritesWithin _
  have hpop :
      RAM.Structured.Footprint.CmdWritesWithin
        (inputRegisters regs).footprint
        (NeighborhoodProgram.pop
          (inputRegisters regs).bufferStack) := by
    apply cmdWritesWithin_mono
      (bufferStack_footprint_subset regs)
    exact pop_sourceWritesWithin _
  simp [prepareCellBit, copy, Cmd.seqList,
    RAM.Structured.Footprint.CmdWritesWithin,
    RAM.Structured.Footprint.BasicWritesWithin,
    (inputRegisters regs).index_mem_footprint,
    hpeek, hpop]

private theorem prepareCellBit_runs
    (regs : NeighborhoodTrial.Registers controller)
    (input : List Bool)
    (blockLength block tape cellCode : ℕ) (store : Store)
    (hblockLength :
      store (Layout.blockLength regs) = blockLength)
    (hblock :
      store (inputRegisters regs).buffer = block)
    (htape :
      store (inputRegisters regs).indexCount = tape)
    (hcell :
      store (inputRegisters regs).replacement = cellCode)
    (hframe :
      SearchProgram.InputFrame
        controller regs.footprint input store) :
    ∃ final,
      Runs (prepareCellBit regs) store final ∧
      final (inputRegisters regs).value = cellCode % 4 ∧
      final (inputRegisters regs).indexCount = tape ∧
      final (inputRegisters regs).result =
        block * blockLength + cellCode / 4 ∧
      final (inputRegisters regs).replacement =
        block * blockLength + cellCode / 4 ∧
      final (inputRegisters regs).word =
        store (inputRegisters regs).word ∧
      final (inputRegisters regs).one = 1 ∧
      SearchProgram.InputFrame
        controller regs.footprint input final := by
  let afterMul :=
    Basic.exec
      (.mul (inputRegisters regs).result
        (inputRegisters regs).buffer
        (Layout.blockLength regs))
      store
  let afterCopy :=
    Function.update afterMul
      (inputRegisters regs).buffer
      (afterMul (inputRegisters regs).replacement)
  let afterBase :=
    Basic.exec (.imm (inputRegisters regs).base 4) afterCopy
  let afterBasePred :=
    Basic.exec (.imm (inputRegisters regs).basePred 3) afterBase
  let ready :=
    Basic.exec (.imm (inputRegisters regs).one 1) afterBasePred
  have hcopy :
      Runs
        (copy (inputRegisters regs).buffer
          (inputRegisters regs).replacement)
        afterMul afterCopy :=
    copy_runs afterMul
      ((inputRegisters regs).index_ne (by decide))
  have hreadyWord :
      ready (inputRegisters regs).buffer = cellCode := by
    simp [ready, afterBasePred, afterBase, afterCopy,
      afterMul, Basic.exec,
      (inputRegisters regs).index_ne
        (by decide : (1 : Fin 12) ≠ 2),
      (inputRegisters regs).index_ne
        (by decide : (1 : Fin 12) ≠ 3),
      (inputRegisters regs).index_ne
        (by decide : (1 : Fin 12) ≠ 6),
      (inputRegisters regs).index_ne
        (by decide : (11 : Fin 12) ≠ 10),
      hcell]
  have hreadyBase :
      ready (inputRegisters regs).base = 4 := by
    simp [ready, afterBasePred, afterBase, Basic.exec,
      (inputRegisters regs).index_ne
        (by decide : (2 : Fin 12) ≠ 3),
      (inputRegisters regs).index_ne
        (by decide : (2 : Fin 12) ≠ 6)]
  have hreadyBasePred :
      ready (inputRegisters regs).basePred = 3 := by
    simp [ready, afterBasePred, Basic.exec,
      (inputRegisters regs).index_ne
        (by decide : (3 : Fin 12) ≠ 6)]
  have hreadyOne :
      ready (inputRegisters regs).one = 1 := by
    simp [ready, Basic.exec]
  obtain ⟨afterPeek, hpeek, hpeekWord, hpeekValue,
      _hpeekTest, hpeekBase, hpeekBasePred⟩ :=
    NeighborhoodProgram.peek_runs
      (inputRegisters regs).bufferStack ready 4 cellCode
      (by omega) hreadyWord hreadyBase hreadyBasePred
  have hpeekOne :
      afterPeek (inputRegisters regs).one = 1 := by
    calc
      afterPeek (inputRegisters regs).one =
          ready (inputRegisters regs).one := by
        apply RAM.Structured.Footprint.runs_eq_outside
          (peek_sourceWritesWithin_withoutOne
            (inputRegisters regs).bufferStack)
          hpeek
        simp
      _ = 1 := hreadyOne
  obtain ⟨afterPop, hpop, hpopWord, _hpopQuotient,
      _hpopTest, _hpopBase, _hpopBasePred, hpopOne⟩ :=
    NeighborhoodProgram.pop_runs
      (inputRegisters regs).bufferStack afterPeek 4 cellCode
      (by omega) hpeekWord hpeekBase hpeekBasePred hpeekOne
  have hstream :
      Runs
        (Cmd.seq
          (NeighborhoodProgram.peek
            (inputRegisters regs).bufferStack)
          (NeighborhoodProgram.pop
            (inputRegisters regs).bufferStack))
        ready afterPop :=
    Runs.seq hpeek hpop
  have hstreamWrites :
      RAM.Structured.Footprint.CmdWritesWithin
        (inputRegisters regs).bufferStack.footprint
        (Cmd.seq
          (NeighborhoodProgram.peek
            (inputRegisters regs).bufferStack)
          (NeighborhoodProgram.pop
            (inputRegisters regs).bufferStack)) :=
    ⟨peek_sourceWritesWithin _, pop_sourceWritesWithin _⟩
  have hpopGamma :
      afterPop (inputRegisters regs).value = cellCode % 4 := by
    calc
      afterPop (inputRegisters regs).value =
          afterPeek (inputRegisters regs).value := by
        apply RAM.Structured.Footprint.runs_eq_outside
          (pop_sourceWritesWithin_withoutValue
            (inputRegisters regs).bufferStack)
          hpop
        simp
      _ = PackedDigits.digit 4 cellCode 0 := by
        simpa using hpeekValue
      _ = cellCode % 4 := by
        simp [PackedDigits.digit]
  have hpopOffset :
      afterPop (inputRegisters regs).buffer = cellCode / 4 := by
    calc
      afterPop (inputRegisters regs).buffer =
          PackedDigits.pop 4 cellCode := by
        simpa using hpopWord
      _ = cellCode / 4 := by
        simp [PackedDigits.pop]
  have hreadyResult :
      ready (inputRegisters regs).result =
        block * blockLength := by
    simp [ready, afterBasePred, afterBase, afterCopy,
      afterMul, Basic.exec,
      (inputRegisters regs).index_ne
        (by decide : (10 : Fin 12) ≠ 1),
      (inputRegisters regs).index_ne
        (by decide : (10 : Fin 12) ≠ 2),
      (inputRegisters regs).index_ne
        (by decide : (10 : Fin 12) ≠ 3),
      (inputRegisters regs).index_ne
        (by decide : (10 : Fin 12) ≠ 6),
      hblock, hblockLength]
  have hpopResult :
      afterPop (inputRegisters regs).result =
        block * blockLength := by
    calc
      afterPop (inputRegisters regs).result =
          ready (inputRegisters regs).result := by
        apply RAM.Structured.Footprint.runs_eq_outside
          hstreamWrites hstream
        exact inputIndex_not_mem_bufferStack regs 10 (by decide)
      _ = block * blockLength := hreadyResult
  have hreadyTape :
      ready (inputRegisters regs).indexCount = tape := by
    simp [ready, afterBasePred, afterBase, afterCopy,
      afterMul, Basic.exec,
      (inputRegisters regs).index_ne
        (by decide : (8 : Fin 12) ≠ 1),
      (inputRegisters regs).index_ne
        (by decide : (8 : Fin 12) ≠ 2),
      (inputRegisters regs).index_ne
        (by decide : (8 : Fin 12) ≠ 3),
      (inputRegisters regs).index_ne
        (by decide : (8 : Fin 12) ≠ 6),
      (inputRegisters regs).index_ne
        (by decide : (8 : Fin 12) ≠ 10),
      htape]
  have hpopTape :
      afterPop (inputRegisters regs).indexCount = tape := by
    calc
      afterPop (inputRegisters regs).indexCount =
          ready (inputRegisters regs).indexCount := by
        apply RAM.Structured.Footprint.runs_eq_outside
          hstreamWrites hstream
        exact inputIndex_not_mem_bufferStack regs 8 (by decide)
      _ = tape := hreadyTape
  have hreadyBankWord :
      ready (inputRegisters regs).word =
        store (inputRegisters regs).word := by
    simp [ready, afterBasePred, afterBase, afterCopy,
      afterMul, Basic.exec,
      (inputRegisters regs).index_ne
        (by decide : (0 : Fin 12) ≠ 1),
      (inputRegisters regs).index_ne
        (by decide : (0 : Fin 12) ≠ 2),
      (inputRegisters regs).index_ne
        (by decide : (0 : Fin 12) ≠ 3),
      (inputRegisters regs).index_ne
        (by decide : (0 : Fin 12) ≠ 6),
      (inputRegisters regs).index_ne
        (by decide : (0 : Fin 12) ≠ 10)]
  have hpopBankWord :
      afterPop (inputRegisters regs).word =
        store (inputRegisters regs).word := by
    calc
      afterPop (inputRegisters regs).word =
          ready (inputRegisters regs).word := by
        apply RAM.Structured.Footprint.runs_eq_outside
          hstreamWrites hstream
        exact inputIndex_not_mem_bufferStack regs 0 (by decide)
      _ = store (inputRegisters regs).word := hreadyBankWord
  let afterAdd :=
    Basic.exec
      (.add (inputRegisters regs).result
        (inputRegisters regs).result
        (inputRegisters regs).buffer)
      afterPop
  let final :=
    Function.update afterAdd
      (inputRegisters regs).replacement
      (afterAdd (inputRegisters regs).result)
  have hfinalCopy :
      Runs
        (copy (inputRegisters regs).replacement
          (inputRegisters regs).result)
        afterAdd final :=
    copy_runs afterAdd
      ((inputRegisters regs).index_ne (by decide))
  have hrun :
      Runs (prepareCellBit regs) store final := by
    simpa [prepareCellBit, Cmd.seqList, afterMul,
      afterBase, afterBasePred, ready, afterAdd, final] using
      Runs.seq
        (Runs.basic
          (.mul (inputRegisters regs).result
            (inputRegisters regs).buffer
            (Layout.blockLength regs))
          store)
        (Runs.seq hcopy
          (Runs.seq
            (Runs.basic
              (.imm (inputRegisters regs).base 4) afterCopy)
            (Runs.seq
              (Runs.basic
                (.imm (inputRegisters regs).basePred 3) afterBase)
              (Runs.seq
                (Runs.basic
                  (.imm (inputRegisters regs).one 1) afterBasePred)
                (Runs.seq hpeek
                  (Runs.seq hpop
                    (Runs.seq
                      (Runs.basic
                        (.add (inputRegisters regs).result
                          (inputRegisters regs).result
                          (inputRegisters regs).buffer)
                        afterPop)
                      hfinalCopy)))))))
  have htrialWrites :
      RAM.Structured.Footprint.CmdWritesWithin
        regs.footprint (prepareCellBit regs) := by
    have hinputTrial :
        (inputRegisters regs).footprint ⊆ regs.footprint := by
      intro address haddress
      rcases Finset.mem_image.mp haddress with
        ⟨slot, _, rfl⟩
      exact Finset.mem_union_left _
        (Layout.index_mem_layout_footprint regs (inputMap slot))
    apply cmdWritesWithin_mono
      hinputTrial
    exact prepareCellBit_writesWithin_local regs
  refine
    ⟨final, hrun, ?_, ?_, ?_, ?_, ?_, ?_,
      NeighborhoodTrial.Registers.runs_preserves_inputFrame
        regs htrialWrites hrun hframe⟩
  · simp [final, afterAdd, Basic.exec,
      (inputRegisters regs).index_ne
        (by decide : (7 : Fin 12) ≠ 10),
      (inputRegisters regs).index_ne
        (by decide : (7 : Fin 12) ≠ 11),
      hpopGamma]
  · simp [final, afterAdd, Basic.exec,
      (inputRegisters regs).index_ne
        (by decide : (8 : Fin 12) ≠ 10),
      (inputRegisters regs).index_ne
        (by decide : (8 : Fin 12) ≠ 11),
      hpopTape]
  · simp [final, afterAdd, Basic.exec,
      (inputRegisters regs).index_ne
        (by decide : (10 : Fin 12) ≠ 11),
      hpopResult, hpopOffset]
  · simp [final, afterAdd, Basic.exec,
      hpopResult, hpopOffset]
  · simp [final, afterAdd, Basic.exec,
      (inputRegisters regs).index_ne
        (by decide : (0 : Fin 12) ≠ 10),
      (inputRegisters regs).index_ne
        (by decide : (0 : Fin 12) ≠ 11),
      hpopBankWord]
  · have hpopOne0 :
        afterPop (inputRegisters regs).one = 1 := by
      simpa using hpopOne
    simp [final, afterAdd, Basic.exec,
      (inputRegisters regs).index_ne
        (by decide : (6 : Fin 12) ≠ 10),
      (inputRegisters regs).index_ne
        (by decide : (6 : Fin 12) ≠ 11),
      hpopOne0]

private theorem prepareCellBit_invariantRuns
    (regs : NeighborhoodTrial.Registers controller)
    (input : List Bool)
    (allowed : Finset ℕ) (bound : ℕ)
    (blockLength block tape cellCode : ℕ) (store : Store)
    (hblockLength :
      store (Layout.blockLength regs) = blockLength)
    (hblock :
      store (inputRegisters regs).buffer = block)
    (htape :
      store (inputRegisters regs).indexCount = tape)
    (hcell :
      store (inputRegisters regs).replacement = cellCode)
    (hblockProductBound : block * blockLength ≤ bound)
    (hcellBound : cellCode ≤ bound)
    (haddressBound :
      block * blockLength + cellCode / 4 ≤ bound)
    (hfourBound : 4 ≤ bound)
    (hstore :
      NeighborhoodProgram.ValuesWithin allowed bound store)
    (hframe :
      SearchProgram.InputFrame
        controller regs.footprint input store) :
    ∃ final steps,
      InvariantRuns
        (NeighborhoodProgram.ValuesWithin allowed bound)
        (prepareCellBit regs) store final steps ∧
      final (inputRegisters regs).value = cellCode % 4 ∧
      final (inputRegisters regs).indexCount = tape ∧
      final (inputRegisters regs).result =
        block * blockLength + cellCode / 4 ∧
      final (inputRegisters regs).replacement =
        block * blockLength + cellCode / 4 ∧
      final (inputRegisters regs).word =
        store (inputRegisters regs).word ∧
      final (inputRegisters regs).one = 1 ∧
      SearchProgram.InputFrame
        controller regs.footprint input final := by
  let afterMul :=
    Basic.exec
      (.mul (inputRegisters regs).result
        (inputRegisters regs).buffer
        (Layout.blockLength regs))
      store
  have hafterMul :
      NeighborhoodProgram.ValuesWithin allowed bound afterMul := by
    apply valuesWithin_update allowed bound
      (inputRegisters regs).result
      (store (inputRegisters regs).buffer *
        store (Layout.blockLength regs))
      store hstore
    simpa [hblock, hblockLength] using hblockProductBound
  have hafterMulCell :
      afterMul (inputRegisters regs).replacement = cellCode := by
    simp [afterMul, Basic.exec,
      (inputRegisters regs).index_ne
        (by decide : (11 : Fin 12) ≠ 10),
      hcell]
  let afterCopy :=
    Function.update afterMul
      (inputRegisters regs).buffer
      (afterMul (inputRegisters regs).replacement)
  have hcopy :
      InvariantRuns
        (NeighborhoodProgram.ValuesWithin allowed bound)
        (copy (inputRegisters regs).buffer
          (inputRegisters regs).replacement)
        afterMul afterCopy 2 := by
    exact copy_invariantRuns allowed bound
      (inputRegisters regs).buffer
      (inputRegisters regs).replacement afterMul
      ((inputRegisters regs).index_ne (by decide))
      (by simpa [hafterMulCell] using hcellBound)
      hafterMul
  have hafterCopy :
      NeighborhoodProgram.ValuesWithin allowed bound afterCopy :=
    InvariantRuns.final hcopy
  let afterBase :=
    Basic.exec (.imm (inputRegisters regs).base 4) afterCopy
  let afterBasePred :=
    Basic.exec (.imm (inputRegisters regs).basePred 3) afterBase
  let ready :=
    Basic.exec (.imm (inputRegisters regs).one 1) afterBasePred
  have hafterBase :
      NeighborhoodProgram.ValuesWithin allowed bound afterBase :=
    valuesWithin_update allowed bound
      (inputRegisters regs).base 4 afterCopy hafterCopy
      hfourBound
  have hafterBasePred :
      NeighborhoodProgram.ValuesWithin allowed bound afterBasePred :=
    valuesWithin_update allowed bound
      (inputRegisters regs).basePred 3 afterBase hafterBase
      (by omega)
  have hready :
      NeighborhoodProgram.ValuesWithin allowed bound ready :=
    valuesWithin_update allowed bound
      (inputRegisters regs).one 1 afterBasePred
      hafterBasePred (by omega)
  have hreadyWord :
      ready (inputRegisters regs).buffer = cellCode := by
    simp [ready, afterBasePred, afterBase, afterCopy,
      afterMul, Basic.exec,
      (inputRegisters regs).index_ne
        (by decide : (1 : Fin 12) ≠ 2),
      (inputRegisters regs).index_ne
        (by decide : (1 : Fin 12) ≠ 3),
      (inputRegisters regs).index_ne
        (by decide : (1 : Fin 12) ≠ 6),
      (inputRegisters regs).index_ne
        (by decide : (11 : Fin 12) ≠ 10),
      hcell]
  have hreadyBase :
      ready (inputRegisters regs).base = 4 := by
    simp [ready, afterBasePred, afterBase, Basic.exec,
      (inputRegisters regs).index_ne
        (by decide : (2 : Fin 12) ≠ 3),
      (inputRegisters regs).index_ne
        (by decide : (2 : Fin 12) ≠ 6)]
  have hreadyBasePred :
      ready (inputRegisters regs).basePred = 3 := by
    simp [ready, afterBasePred, Basic.exec,
      (inputRegisters regs).index_ne
        (by decide : (3 : Fin 12) ≠ 6)]
  have hreadyOne :
      ready (inputRegisters regs).one = 1 := by
    simp [ready, Basic.exec]
  let digit := PackedDigits.digit 4 cellCode 0
  let afterPeek :=
    NeighborhoodProgram.peekResultStore
      (inputRegisters regs).bufferStack digit ready
  obtain ⟨peekSteps, hpeek⟩ :=
    NeighborhoodProgram.peek_invariantRuns
      (inputRegisters regs).bufferStack allowed bound ready
      4 cellCode (by omega) hreadyWord hreadyBase
      hreadyBasePred hcellBound hready
  have hpeek0 :
      InvariantRuns
        (NeighborhoodProgram.ValuesWithin allowed bound)
        (NeighborhoodProgram.peek
          (inputRegisters regs).bufferStack)
        ready afterPeek peekSteps := by
    simpa [afterPeek, digit] using hpeek
  have hpeekWord :
      afterPeek (inputRegisters regs).buffer = cellCode := by
    simp [afterPeek, NeighborhoodProgram.peekResultStore,
      hreadyWord,
      (inputRegisters regs).index_ne
        (by decide : (1 : Fin 12) ≠ 7),
      (inputRegisters regs).index_ne
        (by decide : (1 : Fin 12) ≠ 5)]
  have hpeekBase :
      afterPeek (inputRegisters regs).base = 4 := by
    simp [afterPeek, NeighborhoodProgram.peekResultStore,
      hreadyBase,
      (inputRegisters regs).index_ne
        (by decide : (2 : Fin 12) ≠ 7),
      (inputRegisters regs).index_ne
        (by decide : (2 : Fin 12) ≠ 5)]
  have hpeekBasePred :
      afterPeek (inputRegisters regs).basePred = 3 := by
    simp [afterPeek, NeighborhoodProgram.peekResultStore,
      hreadyBasePred,
      (inputRegisters regs).index_ne
        (by decide : (3 : Fin 12) ≠ 7),
      (inputRegisters regs).index_ne
        (by decide : (3 : Fin 12) ≠ 5)]
  have hpeekOne :
      afterPeek (inputRegisters regs).one = 1 := by
    simp [afterPeek, NeighborhoodProgram.peekResultStore,
      hreadyOne,
      (inputRegisters regs).index_ne
        (by decide : (6 : Fin 12) ≠ 7),
      (inputRegisters regs).index_ne
        (by decide : (6 : Fin 12) ≠ 5)]
  obtain ⟨afterPop, popSteps, hpop, hpopWord,
      _hpopQuotient, _hpopTest, _hpopBase,
      _hpopBasePred, _hpopOne⟩ :=
    NeighborhoodProgram.pop_invariantRuns
      (inputRegisters regs).bufferStack allowed bound afterPeek
      4 cellCode (by omega) hpeekWord hpeekBase hpeekBasePred
      hpeekOne hcellBound (InvariantRuns.final hpeek0)
  have hstream :
      Runs
        (Cmd.seq
          (NeighborhoodProgram.peek
            (inputRegisters regs).bufferStack)
          (NeighborhoodProgram.pop
            (inputRegisters regs).bufferStack))
        ready afterPop :=
    Runs.seq (InvariantRuns.toRuns hpeek0)
      (InvariantRuns.toRuns hpop)
  have hstreamWrites :
      RAM.Structured.Footprint.CmdWritesWithin
        (inputRegisters regs).bufferStack.footprint
        (Cmd.seq
          (NeighborhoodProgram.peek
            (inputRegisters regs).bufferStack)
          (NeighborhoodProgram.pop
            (inputRegisters regs).bufferStack)) :=
    ⟨peek_sourceWritesWithin _, pop_sourceWritesWithin _⟩
  have hpopOffset :
      afterPop (inputRegisters regs).buffer = cellCode / 4 := by
    calc
      afterPop (inputRegisters regs).buffer =
          PackedDigits.pop 4 cellCode := by
        simpa using hpopWord
      _ = cellCode / 4 := by
        simp [PackedDigits.pop]
  have hreadyResult :
      ready (inputRegisters regs).result =
        block * blockLength := by
    simp [ready, afterBasePred, afterBase, afterCopy,
      afterMul, Basic.exec,
      (inputRegisters regs).index_ne
        (by decide : (10 : Fin 12) ≠ 1),
      (inputRegisters regs).index_ne
        (by decide : (10 : Fin 12) ≠ 2),
      (inputRegisters regs).index_ne
        (by decide : (10 : Fin 12) ≠ 3),
      (inputRegisters regs).index_ne
        (by decide : (10 : Fin 12) ≠ 6),
      hblock, hblockLength]
  have hpopResult :
      afterPop (inputRegisters regs).result =
        block * blockLength := by
    calc
      afterPop (inputRegisters regs).result =
          ready (inputRegisters regs).result := by
        apply RAM.Structured.Footprint.runs_eq_outside
          hstreamWrites hstream
        exact inputIndex_not_mem_bufferStack regs 10 (by decide)
      _ = block * blockLength := hreadyResult
  let afterAdd :=
    Basic.exec
      (.add (inputRegisters regs).result
        (inputRegisters regs).result
        (inputRegisters regs).buffer)
      afterPop
  have hafterAdd :
      NeighborhoodProgram.ValuesWithin allowed bound afterAdd := by
    apply valuesWithin_update allowed bound
      (inputRegisters regs).result
      (afterPop (inputRegisters regs).result +
        afterPop (inputRegisters regs).buffer)
      afterPop (InvariantRuns.final hpop)
    simpa [hpopResult, hpopOffset] using haddressBound
  have hafterAddResult :
      afterAdd (inputRegisters regs).result =
        block * blockLength + cellCode / 4 := by
    simp [afterAdd, Basic.exec, hpopResult, hpopOffset]
  let final :=
    Function.update afterAdd
      (inputRegisters regs).replacement
      (afterAdd (inputRegisters regs).result)
  have hfinalCopy :
      InvariantRuns
        (NeighborhoodProgram.ValuesWithin allowed bound)
        (copy (inputRegisters regs).replacement
          (inputRegisters regs).result)
        afterAdd final 2 := by
    exact copy_invariantRuns allowed bound
      (inputRegisters regs).replacement
      (inputRegisters regs).result afterAdd
      ((inputRegisters regs).index_ne (by decide))
      (by simpa [hafterAddResult] using haddressBound)
      hafterAdd
  have hinvariant :
      InvariantRuns
        (NeighborhoodProgram.ValuesWithin allowed bound)
        (prepareCellBit regs) store final
        (1 + (2 + (1 + (1 + (1 +
          (peekSteps + (popSteps + (1 + 2)))))))) := by
    simpa [prepareCellBit, Cmd.seqList, afterMul,
      afterBase, afterBasePred, ready, afterAdd, final] using
      InvariantRuns.seq
        (InvariantRuns.basic
          (.mul (inputRegisters regs).result
            (inputRegisters regs).buffer
            (Layout.blockLength regs))
          store hstore hafterMul)
        (InvariantRuns.seq hcopy
          (InvariantRuns.seq
            (InvariantRuns.basic
              (.imm (inputRegisters regs).base 4)
              afterCopy hafterCopy hafterBase)
            (InvariantRuns.seq
              (InvariantRuns.basic
                (.imm (inputRegisters regs).basePred 3)
                afterBase hafterBase hafterBasePred)
              (InvariantRuns.seq
                (InvariantRuns.basic
                  (.imm (inputRegisters regs).one 1)
                  afterBasePred hafterBasePred hready)
                (InvariantRuns.seq hpeek0
                  (InvariantRuns.seq hpop
                    (InvariantRuns.seq
                      (InvariantRuns.basic
                        (.add (inputRegisters regs).result
                          (inputRegisters regs).result
                          (inputRegisters regs).buffer)
                        afterPop (InvariantRuns.final hpop)
                        hafterAdd)
                      hfinalCopy)))))))
  obtain ⟨semanticFinal, hsemanticRun, hvalue,
      hsemanticTape, hresult, hreplacement, hword,
      hone, hsemanticFrame⟩ :=
    prepareCellBit_runs regs input blockLength block tape cellCode
      store hblockLength hblock htape hcell hframe
  have heq : final = semanticFinal :=
    runs_final_eq (InvariantRuns.toRuns hinvariant) hsemanticRun
  subst semanticFinal
  exact
    ⟨final,
      1 + (2 + (1 + (1 + (1 +
        (peekSteps + (popSteps + (1 + 2))))))),
      hinvariant, hvalue, hsemanticTape, hresult,
      hreplacement, hword, hone, hsemanticFrame⟩

theorem sourceChunk_writesWithin_internal
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (regs : NeighborhoodTrial.Registers controller) :
    RAM.Structured.Footprint.CmdWritesWithin
      (writeFootprint regs) (sourceChunk tm order regs) := by
  have hmain := pop_writesWithin regs
    (inputRegisters regs).mainStack
    (mainStack_footprint_subset regs)
  have hbufferPop := pop_writesWithin regs
    (inputRegisters regs).bufferStack
    (bufferStack_footprint_subset regs)
  have hbufferPeek := peek_writesWithin regs
    (inputRegisters regs).bufferStack
    (bufferStack_footprint_subset regs)
  have hlookup := lookupInput_writesWithin regs
  have hpacked := writeMap_mem regs (13 : Fin 16)
  have hrecovered := writeMap_mem regs (14 : Fin 16)
  have hoperand := writeMap_mem regs (12 : Fin 16)
  have hremaining := writeMap_mem regs (15 : Fin 16)
  change packedTapeBlock regs ∈ writeFootprint regs at hpacked
  change recoveredChunkBits regs ∈ writeFootprint regs at hrecovered
  change operand regs ∈ writeFootprint regs at hoperand
  change remaining regs ∈ writeFootprint regs at hremaining
  simp [sourceChunk, sourceChunkBody, sourceBit,
    sourcePayloadBit, sourceUpperBit, sourceCellBit, cellBit,
    prepareCellBit,
    initialCellBit, inputCellBit, blankCellBit, startCellBit,
    equalImmediate,
    decodeTapeBlock, recoverChunkBits, recoverChunkBitsBody, copy,
    Cmd.seqList,
    RAM.Structured.Footprint.CmdWritesWithin,
    RAM.Structured.Footprint.BasicWritesWithin,
    hmain, hbufferPop, hbufferPeek, hlookup,
    hpacked, hrecovered, hoperand, hremaining]

theorem failureChunk_writesWithin_internal
    (regs : NeighborhoodTrial.Registers controller) :
    RAM.Structured.Footprint.CmdWritesWithin
      (writeFootprint regs) (failureChunk regs) := by
  simpa [failureChunk,
    RAM.Structured.Footprint.CmdWritesWithin,
    RAM.Structured.Footprint.BasicWritesWithin]
    using writeMap_mem regs (12 : Fin 16)

theorem writeFootprint_subset_layout_internal
    (regs : NeighborhoodTrial.Registers controller) :
    writeFootprint regs ⊆ regs.layout.footprint := by
  intro address haddress
  rcases Finset.mem_image.mp haddress with ⟨slot, _, rfl⟩
  exact Layout.index_mem_layout_footprint regs (writeMap slot)

theorem writeFootprint_subset_trial_internal
    (regs : NeighborhoodTrial.Registers controller) :
    writeFootprint regs ⊆ regs.footprint := by
  intro address haddress
  exact Finset.mem_union_left _
    (writeFootprint_subset_layout_internal regs haddress)

private theorem inputRegisters_le_limit
    (regs : NeighborhoodTrial.Registers controller) :
    ∀ slot,
      (inputRegisters regs).index slot ≤
        SearchProgram.footprintLimit controller regs.footprint := by
  intro slot
  exact Finset.le_sup
    (f := fun address : ℕ => address)
    (Finset.mem_union_right controller.footprint
      (writeFootprint_subset_trial_internal regs
        (inputIndex_mem_writeFootprint regs slot)))

private theorem footprintLimit_positive
    (regs : NeighborhoodTrial.Registers controller) :
    0 < SearchProgram.footprintLimit controller regs.footprint := by
  have hcache :
      controller.prefixCache ∈
        controller.footprint ∪ regs.footprint :=
    Finset.mem_union_left _
      (controller.index_mem_footprint 16)
  have hle :
      controller.prefixCache ≤
        SearchProgram.footprintLimit controller regs.footprint :=
    Finset.le_sup
      (f := fun address : ℕ => address) hcache
  change controller.index 16 ≤
    SearchProgram.footprintLimit controller regs.footprint at hle
  rw [controller.prefixCache_one] at hle
  omega

private theorem lookupInput_runs
    (regs : NeighborhoodTrial.Registers controller)
    (input : List Bool) (address : ℕ) (store : Store)
    (hframe :
      SearchProgram.InputFrame
        controller regs.footprint input store)
    (hword :
      store (inputRegisters regs).word =
        SearchProgram.prefixCacheValue controller input
          (SearchProgram.footprintLimit
            controller regs.footprint))
    (haddress :
      store (inputRegisters regs).replacement = address)
    (hpositive : 0 < address)
    (hone : store (inputRegisters regs).one = 1) :
    ∃ final,
      Runs (lookupInput regs) store final ∧
      final (inputRegisters regs).result =
        RAM.initRegs input address ∧
      final (inputRegisters regs).replacement = address ∧
      final (inputRegisters regs).word =
        store (inputRegisters regs).word ∧
      final (inputRegisters regs).one = 1 ∧
      SearchProgram.InputFrame
        controller regs.footprint input final := by
  let limit :=
    SearchProgram.footprintLimit controller regs.footprint
  have hprefix :
      InputLookup.CachedPrefixRepresents input limit
        (SearchProgram.prefixCacheValue controller input limit) :=
    InputLookup.prefixCacheValue_represents
      controller input limit (footprintLimit_positive regs)
  obtain ⟨final, hrun, hpost⟩ :=
    InputLookup.runs (inputRegisters regs) input limit address
      (SearchProgram.prefixCacheValue controller input limit)
      store hpositive (inputRegisters_le_limit regs)
      hprefix hframe.2 hword haddress hone
  have htrialWrites :
      RAM.Structured.Footprint.CmdWritesWithin
        regs.footprint (lookupInput regs) :=
    cmdWritesWithin_mono
      (writeFootprint_subset_trial_internal regs)
      (lookupInput_writesWithin regs)
  exact
    ⟨final, hrun, hpost.result_eq, hpost.address_eq,
      hpost.word_eq, hpost.one_eq.trans hone,
      NeighborhoodTrial.Registers.runs_preserves_inputFrame
        regs htrialWrites hrun hframe⟩

private theorem lookupInput_invariantRuns
    (regs : NeighborhoodTrial.Registers controller)
    (input : List Bool) (address : ℕ) (store : Store)
    (allowed : Finset ℕ) (bound : ℕ)
    (hframe :
      SearchProgram.InputFrame
        controller regs.footprint input store)
    (hword :
      store (inputRegisters regs).word =
        SearchProgram.prefixCacheValue controller input
          (SearchProgram.footprintLimit
            controller regs.footprint))
    (haddress :
      store (inputRegisters regs).replacement = address)
    (hpositive : 0 < address)
    (hone : store (inputRegisters regs).one = 1)
    (hlimitSucc :
      SearchProgram.footprintLimit controller regs.footprint + 1 ≤
        bound)
    (hprefixCapacity :
      2 ^
          SearchProgram.footprintLimit controller regs.footprint ≤
        bound)
    (hstore :
      NeighborhoodProgram.ValuesWithin allowed bound store) :
    ∃ final steps,
      InvariantRuns
        (NeighborhoodProgram.ValuesWithin allowed bound)
        (lookupInput regs) store final steps ∧
      final (inputRegisters regs).result =
        RAM.initRegs input address ∧
      final (inputRegisters regs).replacement = address ∧
      final (inputRegisters regs).word =
        store (inputRegisters regs).word ∧
      final (inputRegisters regs).one = 1 ∧
      SearchProgram.InputFrame
        controller regs.footprint input final := by
  let limit :=
    SearchProgram.footprintLimit controller regs.footprint
  let afterLimit :=
    Basic.exec
      (.imm (inputRegisters regs).result (limit + 1))
      store
  let afterTest :=
    Basic.exec
      (.sub (inputRegisters regs).test
        (inputRegisters regs).result
        (inputRegisters regs).replacement)
      afterLimit
  have hafterLimit :
      NeighborhoodProgram.ValuesWithin
        allowed bound afterLimit :=
    valuesWithin_update allowed bound
      (inputRegisters regs).result (limit + 1)
      store hstore (by simpa [limit] using hlimitSucc)
  have hafterTestValue :
      afterTest (inputRegisters regs).test =
        limit + 1 - address := by
    simp [afterTest, afterLimit, Basic.exec,
      (inputRegisters regs).index_ne
        (by decide : (11 : Fin 12) ≠ 10),
      haddress]
  have hafterTest :
      NeighborhoodProgram.ValuesWithin
        allowed bound afterTest := by
    apply valuesWithin_update allowed bound
      (inputRegisters regs).test
      (afterLimit (inputRegisters regs).result -
        afterLimit (inputRegisters regs).replacement)
      afterLimit hafterLimit
    have hresult :
        afterLimit (inputRegisters regs).result =
          limit + 1 := by
      simp [afterLimit, Basic.exec]
    have hreplacement :
        afterLimit (inputRegisters regs).replacement =
          address := by
      simp [afterLimit, Basic.exec,
        (inputRegisters regs).index_ne
          (by decide : (11 : Fin 12) ≠ 10),
        haddress]
    rw [hresult, hreplacement]
    exact (Nat.sub_le _ _).trans
      (by simpa [limit] using hlimitSucc)
  have hprelude :
      InvariantRuns
        (NeighborhoodProgram.ValuesWithin allowed bound)
        (Cmd.seq
          (.basic
            (.imm (inputRegisters regs).result (limit + 1)))
          (.basic
            (.sub (inputRegisters regs).test
              (inputRegisters regs).result
              (inputRegisters regs).replacement)))
        store afterTest 2 :=
    InvariantRuns.seq
      (InvariantRuns.basic
        (.imm (inputRegisters regs).result (limit + 1))
        store hstore hafterLimit)
      (InvariantRuns.basic
        (.sub (inputRegisters regs).test
          (inputRegisters regs).result
          (inputRegisters regs).replacement)
        afterLimit hafterLimit hafterTest)
  have hlimitPositive : 0 < limit := by
    exact footprintLimit_positive regs
  have htwoPow : 2 ≤ 2 ^ limit := by
    have hpowMono :
        2 ^ 1 ≤ 2 ^ limit :=
      Nat.pow_le_pow_right (by omega) (by omega)
    simpa using hpowMono
  have htwoBound : 2 ≤ bound :=
    htwoPow.trans (by simpa [limit] using hprefixCapacity)
  have honeBound : 1 ≤ bound := by omega
  have hlimitBound : limit ≤ bound := by
    exact (Nat.le_add_right limit 1).trans
      (by simpa [limit] using hlimitSucc)
  by_cases hcached : address ≤ limit
  · have htestNonzero :
        afterTest (inputRegisters regs).test ≠ 0 := by
      rw [hafterTestValue]
      omega
    let afterIndexInit :=
      Basic.exec
        (.imm (inputRegisters regs).indexCount limit)
        afterTest
    let afterIndex :=
      Basic.exec
        (.sub (inputRegisters regs).indexCount
          (inputRegisters regs).indexCount
          (inputRegisters regs).replacement)
        afterIndexInit
    let afterBase :=
      Basic.exec
        (.imm (inputRegisters regs).base 2)
        afterIndex
    let ready :=
      Basic.exec
        (.imm (inputRegisters regs).basePred 1)
        afterBase
    have hafterIndexInit :
        NeighborhoodProgram.ValuesWithin
          allowed bound afterIndexInit :=
      valuesWithin_update allowed bound
        (inputRegisters regs).indexCount limit
        afterTest hafterTest hlimitBound
    have hafterIndexValue :
        afterIndex (inputRegisters regs).indexCount =
          limit - address := by
      simp [afterIndex, afterIndexInit, afterTest, afterLimit,
        Basic.exec,
        (inputRegisters regs).index_ne
          (by decide : (11 : Fin 12) ≠ 8),
        (inputRegisters regs).index_ne
          (by decide : (11 : Fin 12) ≠ 5),
        (inputRegisters regs).index_ne
          (by decide : (11 : Fin 12) ≠ 10),
        haddress]
    have hafterIndex :
        NeighborhoodProgram.ValuesWithin
          allowed bound afterIndex := by
      apply valuesWithin_update allowed bound
        (inputRegisters regs).indexCount
        (afterIndexInit (inputRegisters regs).indexCount -
          afterIndexInit (inputRegisters regs).replacement)
        afterIndexInit hafterIndexInit
      have hindex :
          afterIndexInit (inputRegisters regs).indexCount =
            limit := by
        simp [afterIndexInit, Basic.exec]
      rw [hindex]
      exact (Nat.sub_le _ _).trans hlimitBound
    have hafterBase :
        NeighborhoodProgram.ValuesWithin
          allowed bound afterBase :=
      valuesWithin_update allowed bound
        (inputRegisters regs).base 2 afterIndex
        hafterIndex htwoBound
    have hready :
        NeighborhoodProgram.ValuesWithin
          allowed bound ready :=
      valuesWithin_update allowed bound
        (inputRegisters regs).basePred 1 afterBase
        hafterBase honeBound
    have hreadyWord :
        ready (inputRegisters regs).word =
          SearchProgram.prefixCacheValue controller input limit := by
      simp [ready, afterBase, afterIndex, afterIndexInit,
        afterTest, afterLimit, Basic.exec,
        (inputRegisters regs).index_ne
          (by decide : (0 : Fin 12) ≠ 3),
        (inputRegisters regs).index_ne
          (by decide : (0 : Fin 12) ≠ 2),
        (inputRegisters regs).index_ne
          (by decide : (0 : Fin 12) ≠ 8),
        (inputRegisters regs).index_ne
          (by decide : (0 : Fin 12) ≠ 5),
        (inputRegisters regs).index_ne
          (by decide : (0 : Fin 12) ≠ 10),
        limit, hword]
    have hreadyBase :
        ready (inputRegisters regs).base = 2 := by
      simp [ready, afterBase, Basic.exec,
        (inputRegisters regs).index_ne
          (by decide : (2 : Fin 12) ≠ 3)]
    have hreadyBasePred :
        ready (inputRegisters regs).basePred = 1 := by
      simp [ready, Basic.exec]
    have hreadyOne :
        ready (inputRegisters regs).one = 1 := by
      simp [ready, afterBase, afterIndex, afterIndexInit,
        afterTest, afterLimit, Basic.exec,
        (inputRegisters regs).index_ne
          (by decide : (6 : Fin 12) ≠ 3),
        (inputRegisters regs).index_ne
          (by decide : (6 : Fin 12) ≠ 2),
        (inputRegisters regs).index_ne
          (by decide : (6 : Fin 12) ≠ 8),
        (inputRegisters regs).index_ne
          (by decide : (6 : Fin 12) ≠ 5),
        (inputRegisters regs).index_ne
          (by decide : (6 : Fin 12) ≠ 10),
        hone]
    have hreadyIndex :
        ready (inputRegisters regs).indexCount =
          limit - address := by
      simpa [ready, afterBase, Basic.exec,
        (inputRegisters regs).index_ne
          (by decide : (8 : Fin 12) ≠ 3),
        (inputRegisters regs).index_ne
          (by decide : (8 : Fin 12) ≠ 2)]
        using hafterIndexValue
    have hwordCapacity :
        SearchProgram.prefixCacheValue controller input limit <
          2 ^ limit := by
      rw [InputLookup.prefixCacheValue_eq_packedPrefix
        controller input limit hlimitPositive]
      exact InputLookup.packedPrefix_lt_pow input limit
    obtain ⟨final, bankSteps, hbank,
        _hfinalWord, _hbuffer, _hindex, _hcompleted,
        _hresult, _hbase, _hbasePred, _hfinalOne,
        _hfinalAddress⟩ :=
      NeighborhoodProgram.bankRead_invariantRuns
        (inputRegisters regs) allowed bound ready
        2
        (SearchProgram.prefixCacheValue controller input limit)
        (limit - address) limit
        (by omega) hreadyWord hreadyBase hreadyBasePred
        hreadyOne hreadyIndex hwordCapacity
        (Nat.sub_le _ _) (by simpa [limit] using hprefixCapacity)
        htwoBound ((Nat.sub_le _ _).trans hlimitBound) hready
    have htail :
        InvariantRuns
          (NeighborhoodProgram.ValuesWithin allowed bound)
          (Cmd.seq
            (.basic
              (.imm (inputRegisters regs).indexCount limit))
            (Cmd.seq
              (.basic
                (.sub (inputRegisters regs).indexCount
                  (inputRegisters regs).indexCount
                  (inputRegisters regs).replacement))
              (Cmd.seq
                (.basic (.imm (inputRegisters regs).base 2))
                (Cmd.seq
                  (.basic
                    (.imm (inputRegisters regs).basePred 1))
                  (NeighborhoodProgram.bankRead
                    (inputRegisters regs))))))
          afterTest final
          (1 + (1 + (1 + (1 + bankSteps)))) := by
      exact
        InvariantRuns.seq
          (InvariantRuns.basic
            (.imm (inputRegisters regs).indexCount limit)
            afterTest hafterTest hafterIndexInit)
          (InvariantRuns.seq
            (InvariantRuns.basic
              (.sub (inputRegisters regs).indexCount
                (inputRegisters regs).indexCount
                (inputRegisters regs).replacement)
              afterIndexInit hafterIndexInit hafterIndex)
            (InvariantRuns.seq
              (InvariantRuns.basic
                (.imm (inputRegisters regs).base 2)
                afterIndex hafterIndex hafterBase)
              (InvariantRuns.seq
                (InvariantRuns.basic
                  (.imm (inputRegisters regs).basePred 1)
                  afterBase hafterBase hready)
                hbank)))
    have hinvariant :
        InvariantRuns
          (NeighborhoodProgram.ValuesWithin allowed bound)
          (lookupInput regs) store final
          (1 + (1 +
            (1 + (1 + (1 + (1 + bankSteps))) + 2))) := by
      simpa [lookupInput, InputLookup.command, InputLookup.address,
        limit] using
        InvariantRuns.seq
          (InvariantRuns.basic
            (.imm (inputRegisters regs).result (limit + 1))
            store hstore hafterLimit)
          (InvariantRuns.seq
            (InvariantRuns.basic
              (.sub (inputRegisters regs).test
                (inputRegisters regs).result
                (inputRegisters regs).replacement)
              afterLimit hafterLimit hafterTest)
            (InvariantRuns.ifNonzero htestNonzero htail))
    obtain ⟨semanticFinal, hsemanticRun, hresult,
        hsemanticAddress, hsemanticWord, hsemanticOne,
        hsemanticFrame⟩ :=
      lookupInput_runs regs input address store hframe hword
        haddress hpositive hone
    have heq : final = semanticFinal :=
      runs_final_eq (InvariantRuns.toRuns hinvariant) hsemanticRun
    subst semanticFinal
    exact
      ⟨final,
        1 + (1 + (1 + (1 + (1 + (1 + bankSteps))) + 2)),
        hinvariant,
        hresult, hsemanticAddress, hsemanticWord,
        hsemanticOne, hsemanticFrame⟩
  · have houtside : limit < address := by
      omega
    have htestZero :
        afterTest (inputRegisters regs).test = 0 := by
      rw [hafterTestValue]
      omega
    have haddressOutside :
        address ∉ (inputRegisters regs).footprint := by
      intro hmember
      rcases Finset.mem_image.mp hmember with
        ⟨slot, _, hslot⟩
      rw [← hslot] at houtside
      exact (Nat.not_lt_of_ge
        (inputRegisters_le_limit regs slot)) houtside
    have hafterAddress :
        afterTest address = RAM.initRegs input address := by
      have hpreserved :
          afterTest address = store address := by
        have hpreludeRuns : Runs
            (Cmd.seq
              (.basic
                (.imm (inputRegisters regs).result (limit + 1)))
              (.basic
                (.sub (inputRegisters regs).test
                  (inputRegisters regs).result
                  (inputRegisters regs).replacement)))
            store afterTest :=
          InvariantRuns.toRuns hprelude
        apply RAM.Structured.Footprint.runs_eq_outside
          (by
            simp [RAM.Structured.Footprint.CmdWritesWithin,
              RAM.Structured.Footprint.BasicWritesWithin])
          hpreludeRuns haddressOutside
      exact hpreserved.trans (hframe.2 address (by
        simpa [limit] using houtside))
    have hafterAddressRegister :
        afterTest (inputRegisters regs).replacement = address := by
      simp [afterTest, afterLimit, Basic.exec,
        (inputRegisters regs).index_ne
          (by decide : (11 : Fin 12) ≠ 5),
        (inputRegisters regs).index_ne
          (by decide : (11 : Fin 12) ≠ 10),
        haddress]
    let final :=
      Basic.exec
        (.load (inputRegisters regs).result
          (inputRegisters regs).replacement)
        afterTest
    have hloaded :
        afterTest
            (afterTest (inputRegisters regs).replacement) =
          RAM.initRegs input address := by
      rw [hafterAddressRegister, hafterAddress]
    have hbitBound :
        RAM.initRegs input address ≤ bound := by
      have hbit :=
        InputLookup.initRegs_lt_two_of_pos input hpositive
      omega
    have hfinal :
        NeighborhoodProgram.ValuesWithin
          allowed bound final := by
      apply valuesWithin_update allowed bound
        (inputRegisters regs).result
        (afterTest
          (afterTest (inputRegisters regs).replacement))
        afterTest hafterTest
      rw [hloaded]
      exact hbitBound
    have hinvariant :
        InvariantRuns
          (NeighborhoodProgram.ValuesWithin allowed bound)
          (lookupInput regs) store final 4 := by
      simpa [lookupInput, InputLookup.command, limit, final] using
        InvariantRuns.seq
          (InvariantRuns.basic
            (.imm (inputRegisters regs).result (limit + 1))
            store hstore hafterLimit)
          (InvariantRuns.seq
            (InvariantRuns.basic
              (.sub (inputRegisters regs).test
                (inputRegisters regs).result
                (inputRegisters regs).replacement)
              afterLimit hafterLimit hafterTest)
            (InvariantRuns.ifZero htestZero
              (InvariantRuns.basic
                (.load (inputRegisters regs).result
                  (inputRegisters regs).replacement)
                afterTest hafterTest hfinal)))
    obtain ⟨semanticFinal, hsemanticRun, hresult,
        hsemanticAddress, hsemanticWord, hsemanticOne,
        hsemanticFrame⟩ :=
      lookupInput_runs regs input address store hframe hword
        haddress hpositive hone
    have heq : final = semanticFinal :=
      runs_final_eq (InvariantRuns.toRuns hinvariant) hsemanticRun
    subst semanticFinal
    exact
      ⟨final, 4, hinvariant, hresult, hsemanticAddress,
        hsemanticWord, hsemanticOne, hsemanticFrame⟩

private theorem equalResult_runs
    (regs : NeighborhoodTrial.Registers controller)
    (input : List Bool) (value constant : ℕ) (store : Store)
    (hvalueBuffer : value ≠ (inputRegisters regs).buffer)
    (hvalueTest : value ≠ (inputRegisters regs).test)
    (hframe :
      SearchProgram.InputFrame
        controller regs.footprint input store) :
    ∃ final,
      Runs
        (equalImmediate regs value
          (inputRegisters regs).result constant)
        store final ∧
      final (inputRegisters regs).result =
        (if store value = constant then 1 else 0) ∧
      final (inputRegisters regs).value =
        store (inputRegisters regs).value ∧
      final (inputRegisters regs).word =
        store (inputRegisters regs).word ∧
      final (inputRegisters regs).replacement =
        store (inputRegisters regs).replacement ∧
      final (inputRegisters regs).one =
        store (inputRegisters regs).one ∧
      SearchProgram.InputFrame
        controller regs.footprint input final := by
  obtain ⟨final, hrun, hresult, houtside⟩ :=
    equalImmediate_runs regs value
      (inputRegisters regs).result constant store
      hvalueBuffer hvalueTest
  have hlocalSubset :
      ({(inputRegisters regs).buffer,
          (inputRegisters regs).test,
          (inputRegisters regs).completed,
          (inputRegisters regs).result} : Finset ℕ) ⊆
        (inputRegisters regs).footprint := by
    intro address haddress
    simp only [Finset.mem_insert, Finset.mem_singleton] at haddress
    rcases haddress with rfl | rfl | rfl | rfl <;>
      exact (inputRegisters regs).index_mem_footprint _
  have htrialWrites :
      RAM.Structured.Footprint.CmdWritesWithin
        regs.footprint
        (equalImmediate regs value
          (inputRegisters regs).result constant) := by
    apply cmdWritesWithin_mono
      (fun address haddress =>
        writeFootprint_subset_trial_internal regs
          (inputFootprint_subset regs
            (hlocalSubset haddress)))
    exact equalImmediate_writesWithin_local
      regs value (inputRegisters regs).result constant
  refine
    ⟨final, hrun, hresult, ?_, ?_, ?_, ?_,
      NeighborhoodTrial.Registers.runs_preserves_inputFrame
        regs htrialWrites hrun hframe⟩
  · apply houtside
    simp [(inputRegisters regs).index_ne]
  · apply houtside
    simp [(inputRegisters regs).index_ne]
  · apply houtside
    simp [(inputRegisters regs).index_ne]
  · apply houtside
    simp [(inputRegisters regs).index_ne]

private theorem equalResult_invariantRuns
    (regs : NeighborhoodTrial.Registers controller)
    (input : List Bool) (allowed : Finset ℕ) (bound : ℕ)
    (value constant : ℕ) (store : Store)
    (hvalueBuffer : value ≠ (inputRegisters regs).buffer)
    (hvalueTest : value ≠ (inputRegisters regs).test)
    (hvalueBound : store value ≤ bound)
    (hconstantBound : constant ≤ bound)
    (honeBound : 1 ≤ bound)
    (hstore :
      NeighborhoodProgram.ValuesWithin allowed bound store)
    (hframe :
      SearchProgram.InputFrame
        controller regs.footprint input store) :
    ∃ final steps,
      InvariantRuns
        (NeighborhoodProgram.ValuesWithin allowed bound)
        (equalImmediate regs value
          (inputRegisters regs).result constant)
        store final steps ∧
      final (inputRegisters regs).result =
        (if store value = constant then 1 else 0) ∧
      final (inputRegisters regs).value =
        store (inputRegisters regs).value ∧
      final (inputRegisters regs).word =
        store (inputRegisters regs).word ∧
      final (inputRegisters regs).replacement =
        store (inputRegisters regs).replacement ∧
      final (inputRegisters regs).one =
        store (inputRegisters regs).one ∧
      SearchProgram.InputFrame
        controller regs.footprint input final := by
  obtain ⟨final, steps, hinvariant, _hresult,
      _houtside⟩ :=
    equalImmediate_invariantRuns regs allowed bound value
      (inputRegisters regs).result constant store
      hvalueBuffer hvalueTest hvalueBound hconstantBound
      honeBound hstore
  obtain ⟨semanticFinal, hsemanticRun, hresult,
      hvalue, hword, hreplacement, hone, hsemanticFrame⟩ :=
    equalResult_runs regs input value constant store
      hvalueBuffer hvalueTest hframe
  have heq : final = semanticFinal :=
    runs_final_eq (InvariantRuns.toRuns hinvariant) hsemanticRun
  subst semanticFinal
  exact
    ⟨final, steps, hinvariant, hresult, hvalue, hword,
      hreplacement, hone, hsemanticFrame⟩

private theorem setResultByZero_runs
    (regs : NeighborhoodTrial.Registers controller)
    (input : List Bool) (onZero onNonzero : ℕ)
    (store : Store)
    (hframe :
      SearchProgram.InputFrame
        controller regs.footprint input store) :
    ∃ final,
      Runs
        (.ifZero (inputRegisters regs).result
          (.basic
            (.imm (inputRegisters regs).result onZero))
          (.basic
            (.imm (inputRegisters regs).result onNonzero)))
        store final ∧
      final (inputRegisters regs).result =
        (if store (inputRegisters regs).result = 0 then
          onZero
        else
          onNonzero) ∧
      final (inputRegisters regs).word =
        store (inputRegisters regs).word ∧
      final (inputRegisters regs).replacement =
        store (inputRegisters regs).replacement ∧
      final (inputRegisters regs).one =
        store (inputRegisters regs).one ∧
      SearchProgram.InputFrame
        controller regs.footprint input final := by
  obtain ⟨final, hrun, hresult, houtside⟩ :=
    setByZero_runs
      (inputRegisters regs).result
      (inputRegisters regs).result
      onZero onNonzero store
  have hwrites :
      RAM.Structured.Footprint.CmdWritesWithin
        regs.footprint
        (.ifZero (inputRegisters regs).result
          (.basic
            (.imm (inputRegisters regs).result onZero))
          (.basic
            (.imm (inputRegisters regs).result onNonzero))) := by
    simp [RAM.Structured.Footprint.CmdWritesWithin,
      RAM.Structured.Footprint.BasicWritesWithin,
      writeFootprint_subset_trial_internal regs
        (inputIndex_mem_writeFootprint regs 10)]
  refine
    ⟨final, hrun, hresult, ?_, ?_, ?_,
      NeighborhoodTrial.Registers.runs_preserves_inputFrame
        regs hwrites hrun hframe⟩
  · exact houtside _ ((inputRegisters regs).index_ne (by decide))
  · exact houtside _ ((inputRegisters regs).index_ne (by decide))
  · exact houtside _ ((inputRegisters regs).index_ne (by decide))

private theorem setResultByZero_invariantRuns
    (regs : NeighborhoodTrial.Registers controller)
    (input : List Bool) (allowed : Finset ℕ) (bound : ℕ)
    (onZero onNonzero : ℕ) (store : Store)
    (honZeroBound : onZero ≤ bound)
    (honNonzeroBound : onNonzero ≤ bound)
    (hstore :
      NeighborhoodProgram.ValuesWithin allowed bound store)
    (hframe :
      SearchProgram.InputFrame
        controller regs.footprint input store) :
    ∃ final steps,
      InvariantRuns
        (NeighborhoodProgram.ValuesWithin allowed bound)
        (.ifZero (inputRegisters regs).result
          (.basic
            (.imm (inputRegisters regs).result onZero))
          (.basic
            (.imm (inputRegisters regs).result onNonzero)))
        store final steps ∧
      final (inputRegisters regs).result =
        (if store (inputRegisters regs).result = 0 then
          onZero
        else
          onNonzero) ∧
      final (inputRegisters regs).word =
        store (inputRegisters regs).word ∧
      final (inputRegisters regs).replacement =
        store (inputRegisters regs).replacement ∧
      final (inputRegisters regs).one =
        store (inputRegisters regs).one ∧
      SearchProgram.InputFrame
        controller regs.footprint input final := by
  by_cases hzero :
      store (inputRegisters regs).result = 0
  · let final :=
      Basic.exec
        (.imm (inputRegisters regs).result onZero) store
    have hfinal :
        NeighborhoodProgram.ValuesWithin allowed bound final :=
      valuesWithin_update allowed bound
        (inputRegisters regs).result onZero store hstore
        honZeroBound
    have hinvariant :
        InvariantRuns
          (NeighborhoodProgram.ValuesWithin allowed bound)
          (.ifZero (inputRegisters regs).result
            (.basic
              (.imm (inputRegisters regs).result onZero))
            (.basic
              (.imm (inputRegisters regs).result onNonzero)))
          store final 2 :=
      InvariantRuns.ifZero hzero
        (InvariantRuns.basic _ _ hstore hfinal)
    obtain ⟨semanticFinal, hsemanticRun, hresult,
        hword, hreplacement, hone, hsemanticFrame⟩ :=
      setResultByZero_runs regs input onZero onNonzero
        store hframe
    have heq : final = semanticFinal :=
      runs_final_eq (InvariantRuns.toRuns hinvariant) hsemanticRun
    subst semanticFinal
    exact
      ⟨final, 2, hinvariant, hresult, hword, hreplacement,
        hone, hsemanticFrame⟩
  · let final :=
      Basic.exec
        (.imm (inputRegisters regs).result onNonzero) store
    have hfinal :
        NeighborhoodProgram.ValuesWithin allowed bound final :=
      valuesWithin_update allowed bound
        (inputRegisters regs).result onNonzero store hstore
        honNonzeroBound
    have hinvariant :
        InvariantRuns
          (NeighborhoodProgram.ValuesWithin allowed bound)
          (.ifZero (inputRegisters regs).result
            (.basic
              (.imm (inputRegisters regs).result onZero))
            (.basic
              (.imm (inputRegisters regs).result onNonzero)))
          store final 3 :=
      InvariantRuns.ifNonzero hzero
        (InvariantRuns.basic _ _ hstore hfinal)
    obtain ⟨semanticFinal, hsemanticRun, hresult,
        hword, hreplacement, hone, hsemanticFrame⟩ :=
      setResultByZero_runs regs input onZero onNonzero
        store hframe
    have heq : final = semanticFinal :=
      runs_final_eq (InvariantRuns.toRuns hinvariant) hsemanticRun
    subst semanticFinal
    exact
      ⟨final, 3, hinvariant, hresult, hword, hreplacement,
        hone, hsemanticFrame⟩

private theorem inputCellBit_runs
    (regs : NeighborhoodTrial.Registers controller)
    (input : List Bool) (gamma address : ℕ) (store : Store)
    (hgamma :
      store (inputRegisters regs).value = gamma)
    (haddress :
      store (inputRegisters regs).replacement = address)
    (hpositive : 0 < address)
    (hword :
      store (inputRegisters regs).word =
        SearchProgram.prefixCacheValue controller input
          (SearchProgram.footprintLimit
            controller regs.footprint))
    (hone : store (inputRegisters regs).one = 1)
    (hframe :
      SearchProgram.InputFrame
        controller regs.footprint input store) :
    ∃ final,
      Runs (inputCellBit regs) store final ∧
      final (inputRegisters regs).result =
        (if gamma = RAM.initRegs input address then 1 else 0) ∧
      final (inputRegisters regs).word =
        store (inputRegisters regs).word ∧
      final (inputRegisters regs).replacement = address ∧
      final (inputRegisters regs).one = 1 ∧
      SearchProgram.InputFrame
        controller regs.footprint input final := by
  obtain ⟨afterZero, hzeroRun, hzeroResult, hzeroGamma,
      hzeroWord, hzeroAddress, hzeroOne, hzeroFrame⟩ :=
    equalResult_runs regs input
      (inputRegisters regs).value 0 store
      ((inputRegisters regs).index_ne (by decide))
      ((inputRegisters regs).index_ne (by decide))
      hframe
  have hzeroGamma' :
      afterZero (inputRegisters regs).value = gamma :=
    hzeroGamma.trans hgamma
  have hzeroWord' :
      afterZero (inputRegisters regs).word =
        SearchProgram.prefixCacheValue controller input
          (SearchProgram.footprintLimit
            controller regs.footprint) :=
    hzeroWord.trans hword
  have hzeroAddress' :
      afterZero (inputRegisters regs).replacement = address :=
    hzeroAddress.trans haddress
  have hzeroOne' :
      afterZero (inputRegisters regs).one = 1 :=
    hzeroOne.trans hone
  have hbit :
      RAM.initRegs input address < 2 :=
    InputLookup.initRegs_lt_two_of_pos input hpositive
  by_cases hgammaZero : gamma = 0
  · have hzeroNonzero :
        afterZero (inputRegisters regs).result ≠ 0 := by
      rw [hzeroResult, hgamma]
      simp [hgammaZero]
    obtain ⟨afterLookup, hlookupRun, hlookupResult,
        hlookupAddress, hlookupWord, hlookupOne,
        hlookupFrame⟩ :=
      lookupInput_runs regs input address afterZero
        hzeroFrame hzeroWord' hzeroAddress'
        hpositive hzeroOne'
    obtain ⟨final, hsetRun, hsetResult, hsetWord,
        hsetAddress, hsetOne, hsetFrame⟩ :=
      setResultByZero_runs regs input 1 0
        afterLookup hlookupFrame
    have hbranch :
        Runs
          (Cmd.seq
            (lookupInput regs)
            (.ifZero (inputRegisters regs).result
              (.basic
                (.imm (inputRegisters regs).result 1))
              (.basic
                (.imm (inputRegisters regs).result 0))))
          afterZero final :=
      Runs.seq hlookupRun hsetRun
    have hrun :
        Runs (inputCellBit regs) store final := by
      simpa [inputCellBit] using
        Runs.seq hzeroRun
          (Runs.ifNonzero hzeroNonzero hbranch)
    refine ⟨final, hrun, ?_, ?_, ?_, ?_, hsetFrame⟩
    · rw [hsetResult, hlookupResult, hgammaZero]
      by_cases hinputZero : RAM.initRegs input address = 0
      · simp [hinputZero]
      · have hinputOne :
            RAM.initRegs input address = 1 := by
          omega
        simp [hinputOne]
    · exact hsetWord.trans (hlookupWord.trans hzeroWord)
    · exact hsetAddress.trans hlookupAddress
    · exact hsetOne.trans hlookupOne
  · have hzeroZero :
        afterZero (inputRegisters regs).result = 0 := by
      rw [hzeroResult, hgamma]
      simp [hgammaZero]
    obtain ⟨afterOne, honeRun, honeResult, honeGamma,
        honeWord, honeAddress, honeOne, honeFrame⟩ :=
      equalResult_runs regs input
        (inputRegisters regs).value 1 afterZero
        ((inputRegisters regs).index_ne (by decide))
        ((inputRegisters regs).index_ne (by decide))
        hzeroFrame
    have honeGamma' :
        afterOne (inputRegisters regs).value = gamma :=
      honeGamma.trans hzeroGamma'
    have honeWord' :
        afterOne (inputRegisters regs).word =
          SearchProgram.prefixCacheValue controller input
            (SearchProgram.footprintLimit
              controller regs.footprint) :=
      honeWord.trans hzeroWord'
    have honeAddress' :
        afterOne (inputRegisters regs).replacement = address :=
      honeAddress.trans hzeroAddress'
    have honeOne' :
        afterOne (inputRegisters regs).one = 1 :=
      honeOne.trans hzeroOne'
    by_cases hgammaOne : gamma = 1
    · have honeNonzero :
          afterOne (inputRegisters regs).result ≠ 0 := by
        rw [honeResult, hzeroGamma']
        simp [hgammaOne]
      obtain ⟨afterLookup, hlookupRun, hlookupResult,
          hlookupAddress, hlookupWord, hlookupOne,
          hlookupFrame⟩ :=
        lookupInput_runs regs input address afterOne
          honeFrame honeWord' honeAddress' hpositive honeOne'
      obtain ⟨final, hsetRun, hsetResult, hsetWord,
          hsetAddress, hsetOne, hsetFrame⟩ :=
        setResultByZero_runs regs input 0 1
          afterLookup hlookupFrame
      have hinner :
          Runs
            (Cmd.seq
              (lookupInput regs)
              (.ifZero (inputRegisters regs).result
                (.basic
                  (.imm (inputRegisters regs).result 0))
                (.basic
                  (.imm (inputRegisters regs).result 1))))
            afterOne final :=
        Runs.seq hlookupRun hsetRun
      have honeBranch :
          Runs
            (Cmd.seq
              (equalImmediate regs
                (inputRegisters regs).value
                (inputRegisters regs).result 1)
              (.ifZero (inputRegisters regs).result
                (.basic
                  (.imm (inputRegisters regs).result 0))
                (Cmd.seq
                  (lookupInput regs)
                  (.ifZero (inputRegisters regs).result
                    (.basic
                      (.imm (inputRegisters regs).result 0))
                    (.basic
                      (.imm (inputRegisters regs).result 1))))))
            afterZero final :=
        Runs.seq honeRun
          (Runs.ifNonzero honeNonzero hinner)
      have hrun :
          Runs (inputCellBit regs) store final := by
        simpa [inputCellBit] using
          Runs.seq hzeroRun
            (Runs.ifZero hzeroZero honeBranch)
      refine ⟨final, hrun, ?_, ?_, ?_, ?_, hsetFrame⟩
      · rw [hsetResult, hlookupResult, hgammaOne]
        by_cases hinputZero : RAM.initRegs input address = 0
        · simp [hinputZero]
        · have hinputOne :
              RAM.initRegs input address = 1 := by
            omega
          simp [hinputOne]
      · exact hsetWord.trans
          (hlookupWord.trans (honeWord.trans hzeroWord))
      · exact hsetAddress.trans hlookupAddress
      · exact hsetOne.trans hlookupOne
    · have honeZero :
          afterOne (inputRegisters regs).result = 0 := by
        rw [honeResult, hzeroGamma']
        simp [hgammaOne]
      let final :=
        Basic.exec
          (.imm (inputRegisters regs).result 0) afterOne
      have hfinalBasic :
          Runs
            (.basic
              (.imm (inputRegisters regs).result 0))
            afterOne final :=
        Runs.basic _ _
      have honeBranch :
          Runs
            (Cmd.seq
              (equalImmediate regs
                (inputRegisters regs).value
                (inputRegisters regs).result 1)
              (.ifZero (inputRegisters regs).result
                (.basic
                  (.imm (inputRegisters regs).result 0))
                (Cmd.seq
                  (lookupInput regs)
                  (.ifZero (inputRegisters regs).result
                    (.basic
                      (.imm (inputRegisters regs).result 0))
                    (.basic
                      (.imm (inputRegisters regs).result 1))))))
            afterZero final :=
        Runs.seq honeRun
          (Runs.ifZero honeZero hfinalBasic)
      have hrun :
          Runs (inputCellBit regs) store final := by
        simpa [inputCellBit] using
          Runs.seq hzeroRun
            (Runs.ifZero hzeroZero honeBranch)
      have hfinalFrame :
          SearchProgram.InputFrame
            controller regs.footprint input final := by
        apply NeighborhoodTrial.Registers.runs_preserves_inputFrame
          regs
          (command := .basic
            (.imm (inputRegisters regs).result 0))
          (initial := afterOne)
          (final := final)
        · simpa [RAM.Structured.Footprint.CmdWritesWithin,
            RAM.Structured.Footprint.BasicWritesWithin]
            using writeFootprint_subset_trial_internal regs
              (inputIndex_mem_writeFootprint regs 10)
        · exact hfinalBasic
        · exact honeFrame
      refine ⟨final, hrun, ?_, ?_, ?_, ?_, hfinalFrame⟩
      · have hne :
            gamma ≠ RAM.initRegs input address := by
          intro heq
          have hinput := hbit
          rw [← heq] at hinput
          omega
        simp [final, Basic.exec, hne]
      · simp [final, Basic.exec,
          (inputRegisters regs).index_ne
            (by decide : (0 : Fin 12) ≠ 10),
          honeWord, hzeroWord]
      · simp [final, Basic.exec,
          (inputRegisters regs).index_ne
            (by decide : (11 : Fin 12) ≠ 10),
          honeAddress, hzeroAddress, haddress]
      · simp [final, Basic.exec,
          (inputRegisters regs).index_ne
            (by decide : (6 : Fin 12) ≠ 10),
          honeOne, hzeroOne, hone]

private theorem inputCellBit_invariantRuns
    (regs : NeighborhoodTrial.Registers controller)
    (input : List Bool) (allowed : Finset ℕ) (bound : ℕ)
    (gamma address : ℕ) (store : Store)
    (hgamma :
      store (inputRegisters regs).value = gamma)
    (haddress :
      store (inputRegisters regs).replacement = address)
    (hpositive : 0 < address)
    (hword :
      store (inputRegisters regs).word =
        SearchProgram.prefixCacheValue controller input
          (SearchProgram.footprintLimit
            controller regs.footprint))
    (hone : store (inputRegisters regs).one = 1)
    (hgammaBound : gamma ≤ bound)
    (honeBound : 1 ≤ bound)
    (hlimitSucc :
      SearchProgram.footprintLimit controller regs.footprint + 1 ≤
        bound)
    (hprefixCapacity :
      2 ^
          SearchProgram.footprintLimit controller regs.footprint ≤
        bound)
    (hstore :
      NeighborhoodProgram.ValuesWithin allowed bound store)
    (hframe :
      SearchProgram.InputFrame
        controller regs.footprint input store) :
    ∃ final steps,
      InvariantRuns
        (NeighborhoodProgram.ValuesWithin allowed bound)
        (inputCellBit regs) store final steps ∧
      final (inputRegisters regs).result =
        (if gamma = RAM.initRegs input address then 1 else 0) ∧
      final (inputRegisters regs).word =
        store (inputRegisters regs).word ∧
      final (inputRegisters regs).replacement = address ∧
      final (inputRegisters regs).one = 1 ∧
      SearchProgram.InputFrame
        controller regs.footprint input final := by
  obtain ⟨afterZero, zeroSteps, hzeroRun, hzeroResult,
      hzeroGamma, hzeroWord, hzeroAddress, hzeroOne,
      hzeroFrame⟩ :=
    equalResult_invariantRuns regs input allowed bound
      (inputRegisters regs).value 0 store
      ((inputRegisters regs).index_ne (by decide))
      ((inputRegisters regs).index_ne (by decide))
      (by simpa [hgamma] using hgammaBound) (by omega)
      honeBound hstore hframe
  have hzeroGamma' :
      afterZero (inputRegisters regs).value = gamma :=
    hzeroGamma.trans hgamma
  have hzeroWord' :
      afterZero (inputRegisters regs).word =
        SearchProgram.prefixCacheValue controller input
          (SearchProgram.footprintLimit
            controller regs.footprint) :=
    hzeroWord.trans hword
  have hzeroAddress' :
      afterZero (inputRegisters regs).replacement = address :=
    hzeroAddress.trans haddress
  have hzeroOne' :
      afterZero (inputRegisters regs).one = 1 :=
    hzeroOne.trans hone
  by_cases hgammaZero : gamma = 0
  · have hzeroNonzero :
        afterZero (inputRegisters regs).result ≠ 0 := by
      rw [hzeroResult, hgamma]
      simp [hgammaZero]
    obtain ⟨afterLookup, lookupSteps, hlookupRun,
        _hlookupResult, _hlookupAddress, _hlookupWord,
        _hlookupOne, hlookupFrame⟩ :=
      lookupInput_invariantRuns regs input address afterZero
        allowed bound hzeroFrame hzeroWord' hzeroAddress'
        hpositive hzeroOne' hlimitSucc hprefixCapacity
        (InvariantRuns.final hzeroRun)
    obtain ⟨final, setSteps, hsetRun, _hsetResult,
        _hsetWord, _hsetAddress, _hsetOne, _hsetFrame⟩ :=
      setResultByZero_invariantRuns regs input allowed bound
        1 0 afterLookup honeBound (by omega)
        (InvariantRuns.final hlookupRun) hlookupFrame
    have hbranch :=
      InvariantRuns.seq hlookupRun hsetRun
    have hinvariantExists :
        ∃ steps,
          InvariantRuns
            (NeighborhoodProgram.ValuesWithin allowed bound)
            (inputCellBit regs) store final steps := by
      refine ⟨zeroSteps + (lookupSteps + setSteps) + 2, ?_⟩
      simpa [inputCellBit] using
        InvariantRuns.seq hzeroRun
          (InvariantRuns.ifNonzero hzeroNonzero hbranch)
    obtain ⟨steps, hinvariant⟩ := hinvariantExists
    obtain ⟨semanticFinal, hsemanticRun, hresult,
        hsemanticWord, hsemanticAddress, hsemanticOne,
        hsemanticFrame⟩ :=
      inputCellBit_runs regs input gamma address store hgamma
        haddress hpositive hword hone hframe
    have heq : final = semanticFinal :=
      runs_final_eq (InvariantRuns.toRuns hinvariant) hsemanticRun
    subst semanticFinal
    exact
      ⟨final, steps, hinvariant, hresult, hsemanticWord,
        hsemanticAddress, hsemanticOne, hsemanticFrame⟩
  · have hzeroZero :
        afterZero (inputRegisters regs).result = 0 := by
      rw [hzeroResult, hgamma]
      simp [hgammaZero]
    obtain ⟨afterOne, oneSteps, honeRun, honeResult,
        honeGamma, honeWord, honeAddress, honeOne,
        honeFrame⟩ :=
      equalResult_invariantRuns regs input allowed bound
        (inputRegisters regs).value 1 afterZero
        ((inputRegisters regs).index_ne (by decide))
        ((inputRegisters regs).index_ne (by decide))
        (by simpa [hzeroGamma'] using hgammaBound)
        honeBound honeBound (InvariantRuns.final hzeroRun)
        hzeroFrame
    have honeGamma' :
        afterOne (inputRegisters regs).value = gamma :=
      honeGamma.trans hzeroGamma'
    have honeWord' :
        afterOne (inputRegisters regs).word =
          SearchProgram.prefixCacheValue controller input
            (SearchProgram.footprintLimit
              controller regs.footprint) :=
      honeWord.trans hzeroWord'
    have honeAddress' :
        afterOne (inputRegisters regs).replacement = address :=
      honeAddress.trans hzeroAddress'
    have honeOne' :
        afterOne (inputRegisters regs).one = 1 :=
      honeOne.trans hzeroOne'
    by_cases hgammaOne : gamma = 1
    · have honeNonzero :
          afterOne (inputRegisters regs).result ≠ 0 := by
        rw [honeResult, hzeroGamma']
        simp [hgammaOne]
      obtain ⟨afterLookup, lookupSteps, hlookupRun,
          _hlookupResult, _hlookupAddress, _hlookupWord,
          _hlookupOne, hlookupFrame⟩ :=
        lookupInput_invariantRuns regs input address afterOne
          allowed bound honeFrame honeWord' honeAddress'
          hpositive honeOne' hlimitSucc hprefixCapacity
          (InvariantRuns.final honeRun)
      obtain ⟨final, setSteps, hsetRun, _hsetResult,
          _hsetWord, _hsetAddress, _hsetOne, _hsetFrame⟩ :=
        setResultByZero_invariantRuns regs input allowed bound
          0 1 afterLookup (by omega) honeBound
          (InvariantRuns.final hlookupRun) hlookupFrame
      have hinner :=
        InvariantRuns.seq hlookupRun hsetRun
      have honeBranch :=
        InvariantRuns.seq honeRun
          (InvariantRuns.ifNonzero
            (onZero := .basic
              (.imm (inputRegisters regs).result 0))
            honeNonzero hinner)
      have hinvariantExists :
          ∃ steps,
            InvariantRuns
              (NeighborhoodProgram.ValuesWithin allowed bound)
              (inputCellBit regs) store final steps := by
        refine
          ⟨zeroSteps +
            (oneSteps + (lookupSteps + setSteps) + 2) + 1, ?_⟩
        simpa [inputCellBit] using
          InvariantRuns.seq hzeroRun
            (InvariantRuns.ifZero hzeroZero honeBranch)
      obtain ⟨steps, hinvariant⟩ := hinvariantExists
      obtain ⟨semanticFinal, hsemanticRun, hresult,
          hsemanticWord, hsemanticAddress, hsemanticOne,
          hsemanticFrame⟩ :=
        inputCellBit_runs regs input gamma address store hgamma
          haddress hpositive hword hone hframe
      have heq : final = semanticFinal :=
        runs_final_eq (InvariantRuns.toRuns hinvariant)
          hsemanticRun
      subst semanticFinal
      exact
        ⟨final, steps, hinvariant, hresult, hsemanticWord,
          hsemanticAddress, hsemanticOne, hsemanticFrame⟩
    · have honeZero :
          afterOne (inputRegisters regs).result = 0 := by
        rw [honeResult, hzeroGamma']
        simp [hgammaOne]
      let final :=
        Basic.exec
          (.imm (inputRegisters regs).result 0) afterOne
      have hfinal :
          NeighborhoodProgram.ValuesWithin allowed bound final :=
        valuesWithin_update allowed bound
          (inputRegisters regs).result 0 afterOne
          (InvariantRuns.final honeRun) (by omega)
      have hfinalBasic :
          InvariantRuns
            (NeighborhoodProgram.ValuesWithin allowed bound)
            (.basic
              (.imm (inputRegisters regs).result 0))
            afterOne final 1 :=
        InvariantRuns.basic _ _ (InvariantRuns.final honeRun)
          hfinal
      have honeBranch :=
        InvariantRuns.seq honeRun
          (InvariantRuns.ifZero
            (onNonzero :=
              Cmd.seq
                (lookupInput regs)
                (.ifZero (inputRegisters regs).result
                  (.basic
                    (.imm (inputRegisters regs).result 0))
                  (.basic
                    (.imm (inputRegisters regs).result 1))))
            honeZero hfinalBasic)
      have hinvariantExists :
          ∃ steps,
            InvariantRuns
              (NeighborhoodProgram.ValuesWithin allowed bound)
              (inputCellBit regs) store final steps := by
        refine ⟨zeroSteps + (oneSteps + 2) + 1, ?_⟩
        simpa [inputCellBit] using
          InvariantRuns.seq hzeroRun
            (InvariantRuns.ifZero hzeroZero honeBranch)
      obtain ⟨steps, hinvariant⟩ := hinvariantExists
      obtain ⟨semanticFinal, hsemanticRun, hresult,
          hsemanticWord, hsemanticAddress, hsemanticOne,
          hsemanticFrame⟩ :=
        inputCellBit_runs regs input gamma address store hgamma
          haddress hpositive hword hone hframe
      have heq : final = semanticFinal :=
        runs_final_eq (InvariantRuns.toRuns hinvariant)
          hsemanticRun
      subst semanticFinal
      exact
        ⟨final, steps, hinvariant, hresult, hsemanticWord,
          hsemanticAddress, hsemanticOne, hsemanticFrame⟩

private theorem initialCellBit_runs
    (regs : NeighborhoodTrial.Registers controller)
    (input : List Bool) (gamma tape position : ℕ)
    (store : Store)
    (hgamma :
      store (inputRegisters regs).value = gamma)
    (htape :
      store (inputRegisters regs).indexCount = tape)
    (hposition :
      store (inputRegisters regs).result = position)
    (haddress :
      store (inputRegisters regs).replacement = position)
    (hword :
      store (inputRegisters regs).word =
        SearchProgram.prefixCacheValue controller input
          (SearchProgram.footprintLimit
            controller regs.footprint))
    (hone : store (inputRegisters regs).one = 1)
    (hinputLength : store controller.inputLength = input.length)
    (hframe :
      SearchProgram.InputFrame
        controller regs.footprint input store) :
    ∃ final,
      Runs (initialCellBit regs) store final ∧
      final (inputRegisters regs).result =
        (if gamma = initialGammaCode input tape position then
          1
        else
          0) ∧
      final (inputRegisters regs).word =
        store (inputRegisters regs).word ∧
      final (inputRegisters regs).one = 1 ∧
      SearchProgram.InputFrame
        controller regs.footprint input final := by
  by_cases hpositionZero : position = 0
  · have htestZero :
        store (inputRegisters regs).result = 0 := by
      rw [hposition, hpositionZero]
    obtain ⟨final, hequalRun, hequalResult, _hequalGamma,
        hequalWord, _hequalAddress, hequalOne,
        hequalFrame⟩ :=
      equalResult_runs regs input
        (inputRegisters regs).value 3 store
        ((inputRegisters regs).index_ne (by decide))
        ((inputRegisters regs).index_ne (by decide))
        hframe
    have hrun :
        Runs (initialCellBit regs) store final := by
      simpa [initialCellBit, startCellBit] using
        Runs.ifZero htestZero hequalRun
    refine
      ⟨final, hrun, ?_, hequalWord,
        hequalOne.trans hone, hequalFrame⟩
    rw [hequalResult, hgamma, hpositionZero]
    simp [initialGammaCode]
  · have htestNonzero :
        store (inputRegisters regs).result ≠ 0 := by
      rw [hposition]
      exact hpositionZero
    by_cases htapeZero : tape = 0
    · have htapeTestZero :
          store (inputRegisters regs).indexCount = 0 := by
        rw [htape, htapeZero]
      let tested :=
        Basic.exec
          (.sub (inputRegisters regs).test
            (inputRegisters regs).result
            controller.inputLength)
          store
      have htestRun :
          Runs
            (.basic
              (.sub (inputRegisters regs).test
                (inputRegisters regs).result
                controller.inputLength))
            store tested :=
        Runs.basic _ _
      have htestedValue :
          tested (inputRegisters regs).test =
            position - input.length := by
        simp [tested, Basic.exec, hposition, hinputLength]
      have htestedGamma :
          tested (inputRegisters regs).value = gamma := by
        simp [tested, Basic.exec,
          (inputRegisters regs).index_ne
            (by decide : (7 : Fin 12) ≠ 5),
          hgamma]
      have htestedAddress :
          tested (inputRegisters regs).replacement = position := by
        simp [tested, Basic.exec,
          (inputRegisters regs).index_ne
            (by decide : (11 : Fin 12) ≠ 5),
          haddress]
      have htestedWord :
          tested (inputRegisters regs).word =
            SearchProgram.prefixCacheValue controller input
              (SearchProgram.footprintLimit
                controller regs.footprint) := by
        simp [tested, Basic.exec,
          (inputRegisters regs).index_ne
            (by decide : (0 : Fin 12) ≠ 5),
          hword]
      have htestedOne :
          tested (inputRegisters regs).one = 1 := by
        simp [tested, Basic.exec,
          (inputRegisters regs).index_ne
            (by decide : (6 : Fin 12) ≠ 5),
          hone]
      have htestedFrame :
          SearchProgram.InputFrame
            controller regs.footprint input tested := by
        apply NeighborhoodTrial.Registers.runs_preserves_inputFrame
          regs
          (command := .basic
            (.sub (inputRegisters regs).test
              (inputRegisters regs).result
              controller.inputLength))
          (initial := store)
          (final := tested)
        · simpa [RAM.Structured.Footprint.CmdWritesWithin,
            RAM.Structured.Footprint.BasicWritesWithin]
            using writeFootprint_subset_trial_internal regs
              (inputIndex_mem_writeFootprint regs 5)
        · exact htestRun
        · exact hframe
      by_cases hin : position ≤ input.length
      · have hwithinZero :
            tested (inputRegisters regs).test = 0 := by
          rw [htestedValue]
          omega
        obtain ⟨final, hinputRun, hresult, hfinalWord,
            _hfinalAddress, hfinalOne, hfinalFrame⟩ :=
          inputCellBit_runs regs input gamma position tested
            htestedGamma htestedAddress
            (by omega) htestedWord htestedOne htestedFrame
        have hinner :
            Runs
              (Cmd.seq
                (.basic
                  (.sub (inputRegisters regs).test
                    (inputRegisters regs).result
                    controller.inputLength))
                (.ifZero (inputRegisters regs).test
                  (inputCellBit regs)
                  (blankCellBit regs)))
              store final :=
          Runs.seq htestRun
            (Runs.ifZero hwithinZero hinputRun)
        have hrun :
            Runs (initialCellBit regs) store final := by
          simpa [initialCellBit] using
            Runs.ifNonzero htestNonzero
              (Runs.ifZero htapeTestZero hinner)
        refine
          ⟨final, hrun, ?_, hfinalWord.trans ?_,
            hfinalOne, hfinalFrame⟩
        · rw [hresult]
          simp [initialGammaCode, hpositionZero,
            htapeZero, hin]
        · exact htestedWord.trans hword.symm
      · have hwithinNonzero :
            tested (inputRegisters regs).test ≠ 0 := by
          rw [htestedValue]
          omega
        obtain ⟨final, hblankRun, hblankResult,
            _hblankGamma, hblankWord, _hblankAddress,
            hblankOne, hblankFrame⟩ :=
          equalResult_runs regs input
            (inputRegisters regs).value 2 tested
            ((inputRegisters regs).index_ne (by decide))
            ((inputRegisters regs).index_ne (by decide))
            htestedFrame
        have hinner :
            Runs
              (Cmd.seq
                (.basic
                  (.sub (inputRegisters regs).test
                    (inputRegisters regs).result
                    controller.inputLength))
                (.ifZero (inputRegisters regs).test
                  (inputCellBit regs)
                  (blankCellBit regs)))
              store final :=
          Runs.seq htestRun
            (Runs.ifNonzero hwithinNonzero
              (by simpa [blankCellBit] using hblankRun))
        have hrun :
            Runs (initialCellBit regs) store final := by
          simpa [initialCellBit] using
            Runs.ifNonzero htestNonzero
              (Runs.ifZero htapeTestZero hinner)
        refine
          ⟨final, hrun, ?_, hblankWord.trans ?_,
            hblankOne.trans htestedOne, hblankFrame⟩
        · rw [hblankResult, htestedGamma]
          simp [initialGammaCode, hpositionZero,
            htapeZero, hin]
        · exact htestedWord.trans hword.symm
    · have htapeTestNonzero :
          store (inputRegisters regs).indexCount ≠ 0 := by
        rw [htape]
        exact htapeZero
      obtain ⟨final, hblankRun, hblankResult,
          _hblankGamma, hblankWord, _hblankAddress,
          hblankOne, hblankFrame⟩ :=
        equalResult_runs regs input
          (inputRegisters regs).value 2 store
          ((inputRegisters regs).index_ne (by decide))
          ((inputRegisters regs).index_ne (by decide))
          hframe
      have hrun :
          Runs (initialCellBit regs) store final := by
        simpa [initialCellBit, blankCellBit] using
          Runs.ifNonzero htestNonzero
            (Runs.ifNonzero htapeTestNonzero hblankRun)
      refine
        ⟨final, hrun, ?_, hblankWord,
          hblankOne.trans hone, hblankFrame⟩
      rw [hblankResult, hgamma]
      simp [initialGammaCode, hpositionZero, htapeZero]

private theorem initialCellBit_invariantRuns
    (regs : NeighborhoodTrial.Registers controller)
    (input : List Bool) (allowed : Finset ℕ) (bound : ℕ)
    (gamma tape position : ℕ) (store : Store)
    (hgamma :
      store (inputRegisters regs).value = gamma)
    (htape :
      store (inputRegisters regs).indexCount = tape)
    (hposition :
      store (inputRegisters regs).result = position)
    (haddress :
      store (inputRegisters regs).replacement = position)
    (hword :
      store (inputRegisters regs).word =
        SearchProgram.prefixCacheValue controller input
          (SearchProgram.footprintLimit
            controller regs.footprint))
    (hone : store (inputRegisters regs).one = 1)
    (hinputLength : store controller.inputLength = input.length)
    (hgammaBound : gamma ≤ bound)
    (hpositionBound : position ≤ bound)
    (hthreeBound : 3 ≤ bound)
    (hlimitSucc :
      SearchProgram.footprintLimit controller regs.footprint + 1 ≤
        bound)
    (hprefixCapacity :
      2 ^
          SearchProgram.footprintLimit controller regs.footprint ≤
        bound)
    (hstore :
      NeighborhoodProgram.ValuesWithin allowed bound store)
    (hframe :
      SearchProgram.InputFrame
        controller regs.footprint input store) :
    ∃ final steps,
      InvariantRuns
        (NeighborhoodProgram.ValuesWithin allowed bound)
        (initialCellBit regs) store final steps ∧
      final (inputRegisters regs).result =
        (if gamma = initialGammaCode input tape position then
          1
        else
          0) ∧
      final (inputRegisters regs).word =
        store (inputRegisters regs).word ∧
      final (inputRegisters regs).one = 1 ∧
      SearchProgram.InputFrame
        controller regs.footprint input final := by
  have honeBound : 1 ≤ bound := by omega
  by_cases hpositionZero : position = 0
  · have htestZero :
        store (inputRegisters regs).result = 0 := by
      rw [hposition, hpositionZero]
    obtain ⟨final, equalSteps, hequalRun, _hequalResult,
        _hequalGamma, _hequalWord, _hequalAddress,
        _hequalOne, _hequalFrame⟩ :=
      equalResult_invariantRuns regs input allowed bound
        (inputRegisters regs).value 3 store
        ((inputRegisters regs).index_ne (by decide))
        ((inputRegisters regs).index_ne (by decide))
        (by simpa [hgamma] using hgammaBound)
        hthreeBound honeBound hstore hframe
    have hinvariantExists :
        ∃ steps,
          InvariantRuns
            (NeighborhoodProgram.ValuesWithin allowed bound)
            (initialCellBit regs) store final steps := by
      refine ⟨equalSteps + 1, ?_⟩
      simpa [initialCellBit, startCellBit] using
        InvariantRuns.ifZero htestZero hequalRun
    obtain ⟨steps, hinvariant⟩ := hinvariantExists
    obtain ⟨semanticFinal, hsemanticRun, hresult, hfinalWord,
        hfinalOne, hfinalFrame⟩ :=
      initialCellBit_runs regs input gamma tape position store
        hgamma htape hposition haddress hword hone
        hinputLength hframe
    have heq : final = semanticFinal :=
      runs_final_eq (InvariantRuns.toRuns hinvariant) hsemanticRun
    subst semanticFinal
    exact
      ⟨final, steps, hinvariant, hresult, hfinalWord,
        hfinalOne, hfinalFrame⟩
  · have htestNonzero :
        store (inputRegisters regs).result ≠ 0 := by
      rw [hposition]
      exact hpositionZero
    by_cases htapeZero : tape = 0
    · have htapeTestZero :
          store (inputRegisters regs).indexCount = 0 := by
        rw [htape, htapeZero]
      let tested :=
        Basic.exec
          (.sub (inputRegisters regs).test
            (inputRegisters regs).result
            controller.inputLength)
          store
      have htested :
          NeighborhoodProgram.ValuesWithin allowed bound tested := by
        apply valuesWithin_update allowed bound
          (inputRegisters regs).test
          (store (inputRegisters regs).result -
            store controller.inputLength)
          store hstore
        rw [hposition, hinputLength]
        exact (Nat.sub_le _ _).trans hpositionBound
      have htestRun :
          InvariantRuns
            (NeighborhoodProgram.ValuesWithin allowed bound)
            (.basic
              (.sub (inputRegisters regs).test
                (inputRegisters regs).result
                controller.inputLength))
            store tested 1 :=
        InvariantRuns.basic _ _ hstore htested
      have htestedValue :
          tested (inputRegisters regs).test =
            position - input.length := by
        simp [tested, Basic.exec, hposition, hinputLength]
      have htestedGamma :
          tested (inputRegisters regs).value = gamma := by
        simp [tested, Basic.exec,
          (inputRegisters regs).index_ne
            (by decide : (7 : Fin 12) ≠ 5),
          hgamma]
      have htestedAddress :
          tested (inputRegisters regs).replacement = position := by
        simp [tested, Basic.exec,
          (inputRegisters regs).index_ne
            (by decide : (11 : Fin 12) ≠ 5),
          haddress]
      have htestedWord :
          tested (inputRegisters regs).word =
            SearchProgram.prefixCacheValue controller input
              (SearchProgram.footprintLimit
                controller regs.footprint) := by
        simp [tested, Basic.exec,
          (inputRegisters regs).index_ne
            (by decide : (0 : Fin 12) ≠ 5),
          hword]
      have htestedOne :
          tested (inputRegisters regs).one = 1 := by
        simp [tested, Basic.exec,
          (inputRegisters regs).index_ne
            (by decide : (6 : Fin 12) ≠ 5),
          hone]
      have htestedFrame :
          SearchProgram.InputFrame
            controller regs.footprint input tested := by
        apply NeighborhoodTrial.Registers.runs_preserves_inputFrame
          regs
          (command := .basic
            (.sub (inputRegisters regs).test
              (inputRegisters regs).result
              controller.inputLength))
          (initial := store) (final := tested)
        · simpa [RAM.Structured.Footprint.CmdWritesWithin,
            RAM.Structured.Footprint.BasicWritesWithin]
            using writeFootprint_subset_trial_internal regs
              (inputIndex_mem_writeFootprint regs 5)
        · exact InvariantRuns.toRuns htestRun
        · exact hframe
      by_cases hin : position ≤ input.length
      · have hwithinZero :
            tested (inputRegisters regs).test = 0 := by
          rw [htestedValue]
          omega
        obtain ⟨final, inputSteps, hinputRun, _hresult,
            _hfinalWord, _hfinalAddress, _hfinalOne,
            _hfinalFrame⟩ :=
          inputCellBit_invariantRuns regs input allowed bound
            gamma position tested htestedGamma htestedAddress
            (by omega) htestedWord htestedOne hgammaBound
            honeBound hlimitSucc hprefixCapacity htested
            htestedFrame
        have hinner :=
          InvariantRuns.seq htestRun
            (InvariantRuns.ifZero
              (onNonzero := blankCellBit regs)
              hwithinZero hinputRun)
        have hinvariantExists :
            ∃ steps,
              InvariantRuns
                (NeighborhoodProgram.ValuesWithin allowed bound)
                (initialCellBit regs) store final steps := by
          refine ⟨1 + (inputSteps + 1) + 3, ?_⟩
          simpa [initialCellBit] using
            InvariantRuns.ifNonzero htestNonzero
              (InvariantRuns.ifZero
                (onNonzero := blankCellBit regs)
                htapeTestZero hinner)
        obtain ⟨steps, hinvariant⟩ := hinvariantExists
        obtain ⟨semanticFinal, hsemanticRun, hresult,
            hfinalWord, hfinalOne, hfinalFrame⟩ :=
          initialCellBit_runs regs input gamma tape position store
            hgamma htape hposition haddress hword hone
            hinputLength hframe
        have heq : final = semanticFinal :=
          runs_final_eq (InvariantRuns.toRuns hinvariant)
            hsemanticRun
        subst semanticFinal
        exact
          ⟨final, steps, hinvariant, hresult, hfinalWord,
            hfinalOne, hfinalFrame⟩
      · have hwithinNonzero :
            tested (inputRegisters regs).test ≠ 0 := by
          rw [htestedValue]
          omega
        obtain ⟨final, blankSteps, hblankRun,
            _hblankResult, _hblankGamma, _hblankWord,
            _hblankAddress, _hblankOne, _hblankFrame⟩ :=
          equalResult_invariantRuns regs input allowed bound
            (inputRegisters regs).value 2 tested
            ((inputRegisters regs).index_ne (by decide))
            ((inputRegisters regs).index_ne (by decide))
            (by simpa [htestedGamma] using hgammaBound)
            (by omega) honeBound htested htestedFrame
        have hinner :=
          InvariantRuns.seq htestRun
            (InvariantRuns.ifNonzero
              (onZero := inputCellBit regs)
              hwithinNonzero
              (by simpa [blankCellBit] using hblankRun))
        have hinvariantExists :
            ∃ steps,
              InvariantRuns
                (NeighborhoodProgram.ValuesWithin allowed bound)
                (initialCellBit regs) store final steps := by
          refine ⟨1 + (blankSteps + 2) + 3, ?_⟩
          simpa [initialCellBit] using
            InvariantRuns.ifNonzero htestNonzero
              (InvariantRuns.ifZero
                (onNonzero := blankCellBit regs)
                htapeTestZero hinner)
        obtain ⟨steps, hinvariant⟩ := hinvariantExists
        obtain ⟨semanticFinal, hsemanticRun, hresult,
            hfinalWord, hfinalOne, hfinalFrame⟩ :=
          initialCellBit_runs regs input gamma tape position store
            hgamma htape hposition haddress hword hone
            hinputLength hframe
        have heq : final = semanticFinal :=
          runs_final_eq (InvariantRuns.toRuns hinvariant)
            hsemanticRun
        subst semanticFinal
        exact
          ⟨final, steps, hinvariant, hresult, hfinalWord,
            hfinalOne, hfinalFrame⟩
    · have htapeTestNonzero :
          store (inputRegisters regs).indexCount ≠ 0 := by
        rw [htape]
        exact htapeZero
      obtain ⟨final, blankSteps, hblankRun, _hblankResult,
          _hblankGamma, _hblankWord, _hblankAddress,
          _hblankOne, _hblankFrame⟩ :=
        equalResult_invariantRuns regs input allowed bound
          (inputRegisters regs).value 2 store
          ((inputRegisters regs).index_ne (by decide))
          ((inputRegisters regs).index_ne (by decide))
          (by simpa [hgamma] using hgammaBound)
          (by omega) honeBound hstore hframe
      have hinvariantExists :
          ∃ steps,
            InvariantRuns
              (NeighborhoodProgram.ValuesWithin allowed bound)
              (initialCellBit regs) store final steps := by
        refine ⟨blankSteps + 4, ?_⟩
        simpa [initialCellBit, blankCellBit] using
          InvariantRuns.ifNonzero htestNonzero
            (InvariantRuns.ifNonzero
              (onZero :=
                Cmd.seq
                  (.basic
                    (.sub (inputRegisters regs).test
                      (inputRegisters regs).result
                      controller.inputLength))
                  (.ifZero (inputRegisters regs).test
                    (inputCellBit regs)
                    (blankCellBit regs)))
              htapeTestNonzero hblankRun)
      obtain ⟨steps, hinvariant⟩ := hinvariantExists
      obtain ⟨semanticFinal, hsemanticRun, hresult,
          hfinalWord, hfinalOne, hfinalFrame⟩ :=
        initialCellBit_runs regs input gamma tape position store
          hgamma htape hposition haddress hword hone
          hinputLength hframe
      have heq : final = semanticFinal :=
        runs_final_eq (InvariantRuns.toRuns hinvariant)
          hsemanticRun
      subst semanticFinal
      exact
        ⟨final, steps, hinvariant, hresult, hfinalWord,
          hfinalOne, hfinalFrame⟩

private theorem cellBit_runs
    (regs : NeighborhoodTrial.Registers controller)
    (input : List Bool)
    (blockLength block tape cellCode : ℕ) (store : Store)
    (hblockLength :
      store (Layout.blockLength regs) = blockLength)
    (hblock :
      store (inputRegisters regs).buffer = block)
    (htape :
      store (inputRegisters regs).indexCount = tape)
    (hcell :
      store (inputRegisters regs).replacement = cellCode)
    (hword :
      store (inputRegisters regs).word =
        SearchProgram.prefixCacheValue controller input
          (SearchProgram.footprintLimit
            controller regs.footprint))
    (hinputLength : store controller.inputLength = input.length)
    (hframe :
      SearchProgram.InputFrame
        controller regs.footprint input store) :
    ∃ final,
      Runs (cellBit regs) store final ∧
      final (inputRegisters regs).result =
        (if cellCode % 4 =
            initialGammaCode input tape
              (block * blockLength + cellCode / 4) then
          1
        else
          0) ∧
      final (inputRegisters regs).word =
        store (inputRegisters regs).word ∧
      final (inputRegisters regs).one = 1 ∧
      SearchProgram.InputFrame
        controller regs.footprint input final := by
  obtain ⟨prepared, hprepareRun, hgamma,
      hpreparedTape, hposition, haddress, hpreparedWord,
      hpreparedOne, hpreparedFrame⟩ :=
    prepareCellBit_runs regs input blockLength block tape cellCode
      store hblockLength hblock htape hcell hframe
  have hpreparedInputLength :
      prepared controller.inputLength = input.length := by
    calc
      prepared controller.inputLength =
          store controller.inputLength := by
        apply NeighborhoodTrial.Registers.runs_preserves_controller_index
          regs
          (command := prepareCellBit regs)
          (initial := store)
          (final := prepared)
        · have hinputTrial :
              (inputRegisters regs).footprint ⊆ regs.footprint := by
            intro address haddress
            rcases Finset.mem_image.mp haddress with
              ⟨slot, _, rfl⟩
            exact Finset.mem_union_left _
              (Layout.index_mem_layout_footprint
                regs (inputMap slot))
          exact cmdWritesWithin_mono hinputTrial
            (prepareCellBit_writesWithin_local regs)
        · exact hprepareRun
        · decide
        · decide
        · decide
      _ = input.length := hinputLength
  have hpreparedCache :
      prepared (inputRegisters regs).word =
        SearchProgram.prefixCacheValue controller input
          (SearchProgram.footprintLimit
            controller regs.footprint) :=
    hpreparedWord.trans hword
  obtain ⟨final, hbranchRun, hresult, hfinalWord,
      hfinalOne, hfinalFrame⟩ :=
    initialCellBit_runs regs input
      (cellCode % 4) tape
      (block * blockLength + cellCode / 4)
      prepared hgamma hpreparedTape hposition haddress
      hpreparedCache hpreparedOne hpreparedInputLength
      hpreparedFrame
  exact
    ⟨final, Runs.seq hprepareRun hbranchRun,
      hresult, hfinalWord.trans hpreparedWord,
      hfinalOne, hfinalFrame⟩

private theorem cellBit_invariantRuns
    (regs : NeighborhoodTrial.Registers controller)
    (input : List Bool) (allowed : Finset ℕ) (bound : ℕ)
    (blockLength block tape cellCode : ℕ) (store : Store)
    (hblockLength :
      store (Layout.blockLength regs) = blockLength)
    (hblock :
      store (inputRegisters regs).buffer = block)
    (htape :
      store (inputRegisters regs).indexCount = tape)
    (hcell :
      store (inputRegisters regs).replacement = cellCode)
    (hword :
      store (inputRegisters regs).word =
        SearchProgram.prefixCacheValue controller input
          (SearchProgram.footprintLimit
            controller regs.footprint))
    (hinputLength : store controller.inputLength = input.length)
    (hblockProductBound : block * blockLength ≤ bound)
    (hcellBound : cellCode ≤ bound)
    (haddressBound :
      block * blockLength + cellCode / 4 ≤ bound)
    (hfourBound : 4 ≤ bound)
    (hlimitSucc :
      SearchProgram.footprintLimit controller regs.footprint + 1 ≤
        bound)
    (hprefixCapacity :
      2 ^
          SearchProgram.footprintLimit controller regs.footprint ≤
        bound)
    (hstore :
      NeighborhoodProgram.ValuesWithin allowed bound store)
    (hframe :
      SearchProgram.InputFrame
        controller regs.footprint input store) :
    ∃ final steps,
      InvariantRuns
        (NeighborhoodProgram.ValuesWithin allowed bound)
        (cellBit regs) store final steps ∧
      final (inputRegisters regs).result =
        (if cellCode % 4 =
            initialGammaCode input tape
              (block * blockLength + cellCode / 4) then
          1
        else
          0) ∧
      final (inputRegisters regs).word =
        store (inputRegisters regs).word ∧
      final (inputRegisters regs).one = 1 ∧
      SearchProgram.InputFrame
        controller regs.footprint input final := by
  obtain ⟨prepared, prepareSteps, hprepareRun, hgamma,
      hpreparedTape, hposition, haddress, hpreparedWord,
      hpreparedOne, hpreparedFrame⟩ :=
    prepareCellBit_invariantRuns regs input allowed bound
      blockLength block tape cellCode store hblockLength hblock
      htape hcell hblockProductBound hcellBound haddressBound
      hfourBound hstore hframe
  have hpreparedInputLength :
      prepared controller.inputLength = input.length := by
    calc
      prepared controller.inputLength =
          store controller.inputLength := by
        apply NeighborhoodTrial.Registers.runs_preserves_controller_index
          regs
          (command := prepareCellBit regs)
          (initial := store) (final := prepared)
        · have hinputTrial :
              (inputRegisters regs).footprint ⊆
                regs.footprint := by
            intro address haddress
            rcases Finset.mem_image.mp haddress with
              ⟨slot, _, rfl⟩
            exact Finset.mem_union_left _
              (Layout.index_mem_layout_footprint
                regs (inputMap slot))
          exact cmdWritesWithin_mono hinputTrial
            (prepareCellBit_writesWithin_local regs)
        · exact InvariantRuns.toRuns hprepareRun
        · decide
        · decide
        · decide
      _ = input.length := hinputLength
  have hpreparedCache :
      prepared (inputRegisters regs).word =
        SearchProgram.prefixCacheValue controller input
          (SearchProgram.footprintLimit
            controller regs.footprint) :=
    hpreparedWord.trans hword
  obtain ⟨final, branchSteps, hbranchRun, hresult,
      hfinalWord, hfinalOne, hfinalFrame⟩ :=
    initialCellBit_invariantRuns regs input allowed bound
      (cellCode % 4) tape
      (block * blockLength + cellCode / 4)
      prepared hgamma hpreparedTape hposition haddress
      hpreparedCache hpreparedOne hpreparedInputLength
      (by
        have hmod : cellCode % 4 < 4 :=
          Nat.mod_lt _ (by omega)
        omega)
      haddressBound (by omega) hlimitSucc hprefixCapacity
      (InvariantRuns.final hprepareRun) hpreparedFrame
  exact
    ⟨final, prepareSteps + branchSteps,
      by simpa [cellBit] using
        InvariantRuns.seq hprepareRun hbranchRun,
      hresult, hfinalWord.trans hpreparedWord,
      hfinalOne, hfinalFrame⟩

private theorem cellBit_writesWithin_local
    (regs : NeighborhoodTrial.Registers controller) :
    RAM.Structured.Footprint.CmdWritesWithin
      (inputRegisters regs).footprint (cellBit regs) := by
  have hlookup :
      RAM.Structured.Footprint.CmdWritesWithin
        (inputRegisters regs).footprint (lookupInput regs) := by
    exact InputLookup.sourceWritesWithin _ _
  have hpeek :
      RAM.Structured.Footprint.CmdWritesWithin
        (inputRegisters regs).footprint
        (NeighborhoodProgram.peek
          (inputRegisters regs).bufferStack) := by
    exact cmdWritesWithin_mono
      (bufferStack_footprint_subset regs)
      (peek_sourceWritesWithin _)
  have hpop :
      RAM.Structured.Footprint.CmdWritesWithin
        (inputRegisters regs).footprint
        (NeighborhoodProgram.pop
          (inputRegisters regs).bufferStack) := by
    exact cmdWritesWithin_mono
      (bufferStack_footprint_subset regs)
      (pop_sourceWritesWithin _)
  simp [cellBit, prepareCellBit, initialCellBit,
    inputCellBit, startCellBit, blankCellBit,
    equalImmediate, copy, Cmd.seqList,
    RAM.Structured.Footprint.CmdWritesWithin,
    RAM.Structured.Footprint.BasicWritesWithin,
    (inputRegisters regs).index_mem_footprint,
    hlookup, hpeek, hpop]

private theorem layoutIndex_not_mem_inputFootprint
    (regs : NeighborhoodTrial.Registers controller)
    (slot : Fin 34)
    (hslot : ∀ index, inputMap index ≠ slot) :
    regs.index slot ∉ (inputRegisters regs).footprint := by
  intro hmember
  rcases Finset.mem_image.mp hmember with
    ⟨index, _, heq⟩
  apply hslot index
  exact regs.injective heq

private theorem sourceCellBit_runs
    (tm : TM workTapeCount)
    (regs : NeighborhoodTrial.Registers controller)
    (input : List Bool)
    (blockLength tape block coordinate : ℕ) (store : Store)
    (htape : tape < tapeCount workTapeCount)
    (hblockLength :
      store (Layout.blockLength regs) = blockLength)
    (hpacked :
      store (packedTapeBlock regs) =
        tapeBlockCode workTapeCount tape block)
    (hcoordinate :
      store (inputRegisters regs).replacement = coordinate)
    (hword :
      store (inputRegisters regs).word =
        SearchProgram.prefixCacheValue controller input
          (SearchProgram.footprintLimit
            controller regs.footprint))
    (hinputLength : store controller.inputLength = input.length)
    (hframe :
      SearchProgram.InputFrame
        controller regs.footprint input store) :
    ∃ final,
      Runs (sourceCellBit tm regs) store final ∧
      final (inputRegisters regs).result =
        (if (coordinate -
              (Fintype.card tm.Q + blockLength)) % 4 =
            initialGammaCode input tape
              (block * blockLength +
                (coordinate -
                  (Fintype.card tm.Q + blockLength)) / 4) then
          1
        else
          0) ∧
      final (inputRegisters regs).word =
        store (inputRegisters regs).word ∧
      final (inputRegisters regs).one = 1 ∧
      SearchProgram.InputFrame
        controller regs.footprint input final := by
  obtain ⟨decoded, hdecodeRun, hdecodedTape,
      hdecodedBlock, hdecodedOne, hdecodedCoordinate,
      hdecodedWord,
      hdecodeOutside⟩ :=
    decodeTapeBlock_runs workTapeCount regs store tape block
      htape hpacked
  have hdecodedBlockLength :
      decoded (Layout.blockLength regs) = blockLength := by
    rw [hdecodeOutside]
    · exact hblockLength
    · exact layoutIndex_not_mem_inputFootprint regs 2 (by decide)
  have hdecodedCoordinate' :
      decoded (inputRegisters regs).replacement = coordinate :=
    hdecodedCoordinate.trans hcoordinate
  let afterState :=
    Basic.exec
      (.imm (inputRegisters regs).value
        (Fintype.card tm.Q))
      decoded
  let afterLower :=
    Basic.exec
      (.add (inputRegisters regs).value
        (inputRegisters regs).value
        (Layout.blockLength regs))
      afterState
  let ready :=
    Basic.exec
      (.sub (inputRegisters regs).replacement
        (inputRegisters regs).replacement
        (inputRegisters regs).value)
      afterLower
  have hblockValueNe :
      Layout.blockLength regs ≠
        (inputRegisters regs).value :=
    regs.injective.ne (by decide)
  have hreadyCell :
      ready (inputRegisters regs).replacement =
        coordinate -
          (Fintype.card tm.Q + blockLength) := by
    simp [ready, afterLower, afterState, Basic.exec,
      (inputRegisters regs).index_ne
        (by decide : (11 : Fin 12) ≠ 7),
      hblockValueNe,
      hdecodedCoordinate', hdecodedBlockLength]
  have hreadyBlock :
      ready (inputRegisters regs).buffer = block := by
    simp [ready, afterLower, afterState, Basic.exec,
      (inputRegisters regs).index_ne
        (by decide : (1 : Fin 12) ≠ 7),
      (inputRegisters regs).index_ne
        (by decide : (1 : Fin 12) ≠ 11),
      hdecodedBlock]
  have hreadyTape :
      ready (inputRegisters regs).indexCount = tape := by
    simp [ready, afterLower, afterState, Basic.exec,
      (inputRegisters regs).index_ne
        (by decide : (8 : Fin 12) ≠ 7),
      (inputRegisters regs).index_ne
        (by decide : (8 : Fin 12) ≠ 11),
      hdecodedTape]
  have hreadyBlockLength :
      ready (Layout.blockLength regs) = blockLength := by
    have hblockReplacementNe :
        Layout.blockLength regs ≠
          (inputRegisters regs).replacement :=
      regs.injective.ne (by decide)
    simp [ready, afterLower, afterState, Basic.exec,
      hblockValueNe, hblockReplacementNe,
      hdecodedBlockLength]
  have hreadyWord :
      ready (inputRegisters regs).word =
        SearchProgram.prefixCacheValue controller input
          (SearchProgram.footprintLimit
            controller regs.footprint) := by
    simp [ready, afterLower, afterState, Basic.exec,
      (inputRegisters regs).index_ne
        (by decide : (0 : Fin 12) ≠ 7),
      (inputRegisters regs).index_ne
        (by decide : (0 : Fin 12) ≠ 11),
      hdecodedWord, hword]
  have hreadyOne :
      ready (inputRegisters regs).one = 1 := by
    simp [ready, afterLower, afterState, Basic.exec,
      (inputRegisters regs).index_ne
        (by decide : (6 : Fin 12) ≠ 7),
      (inputRegisters regs).index_ne
        (by decide : (6 : Fin 12) ≠ 11),
      hdecodedOne]
  have hprefixRun :
      Runs
        (Cmd.seqList
          [decodeTapeBlock workTapeCount regs,
            .basic
              (.imm (inputRegisters regs).value
                (Fintype.card tm.Q)),
            .basic
              (.add (inputRegisters regs).value
                (inputRegisters regs).value
                (Layout.blockLength regs)),
            .basic
              (.sub (inputRegisters regs).replacement
                (inputRegisters regs).replacement
                (inputRegisters regs).value)])
        store ready := by
    simpa [Cmd.seqList, afterState, afterLower, ready] using
      Runs.seq hdecodeRun
        (Runs.seq
          (Runs.basic
            (.imm (inputRegisters regs).value
              (Fintype.card tm.Q))
            decoded)
          (Runs.seq
            (Runs.basic
              (.add (inputRegisters regs).value
                (inputRegisters regs).value
                (Layout.blockLength regs))
              afterState)
            (Runs.basic
              (.sub (inputRegisters regs).replacement
                (inputRegisters regs).replacement
                (inputRegisters regs).value)
              afterLower)))
  have hprefixWrites :
      RAM.Structured.Footprint.CmdWritesWithin
        regs.footprint
        (Cmd.seqList
          [decodeTapeBlock workTapeCount regs,
            .basic
              (.imm (inputRegisters regs).value
                (Fintype.card tm.Q)),
            .basic
              (.add (inputRegisters regs).value
                (inputRegisters regs).value
                (Layout.blockLength regs)),
            .basic
              (.sub (inputRegisters regs).replacement
                (inputRegisters regs).replacement
                (inputRegisters regs).value)]) := by
    have hinputTrial :
        (inputRegisters regs).footprint ⊆ regs.footprint := by
      intro address haddress
      rcases Finset.mem_image.mp haddress with
        ⟨slot, _, rfl⟩
      exact Finset.mem_union_left _
        (Layout.index_mem_layout_footprint regs (inputMap slot))
    apply cmdWritesWithin_mono hinputTrial
    simp [Cmd.seqList,
      RAM.Structured.Footprint.CmdWritesWithin,
      RAM.Structured.Footprint.BasicWritesWithin,
      decodeTapeBlock_writesWithin_local,
      (inputRegisters regs).index_mem_footprint]
  have hreadyFrame :
      SearchProgram.InputFrame
        controller regs.footprint input ready :=
    NeighborhoodTrial.Registers.runs_preserves_inputFrame
      regs hprefixWrites hprefixRun hframe
  have hreadyInputLength :
      ready controller.inputLength = input.length := by
    calc
      ready controller.inputLength =
          store controller.inputLength := by
        apply NeighborhoodTrial.Registers.runs_preserves_controller_index
          regs hprefixWrites hprefixRun
        · decide
        · decide
        · decide
      _ = input.length := hinputLength
  obtain ⟨final, hcellRun, hresult, hfinalWord,
      hfinalOne, hfinalFrame⟩ :=
    cellBit_runs regs input blockLength block tape
      (coordinate - (Fintype.card tm.Q + blockLength))
      ready hreadyBlockLength hreadyBlock hreadyTape
      hreadyCell hreadyWord hreadyInputLength hreadyFrame
  have hrun :
      Runs (sourceCellBit tm regs) store final := by
    simpa [sourceCellBit, Cmd.seqList, afterState,
      afterLower, ready] using
      Runs.seq hdecodeRun
        (Runs.seq
          (Runs.basic
            (.imm (inputRegisters regs).value
              (Fintype.card tm.Q))
            decoded)
          (Runs.seq
            (Runs.basic
              (.add (inputRegisters regs).value
                (inputRegisters regs).value
                (Layout.blockLength regs))
              afterState)
            (Runs.seq
              (Runs.basic
                (.sub (inputRegisters regs).replacement
                  (inputRegisters regs).replacement
                  (inputRegisters regs).value)
                afterLower)
              hcellRun)))
  exact
    ⟨final, hrun, hresult,
      hfinalWord.trans (hreadyWord.trans hword.symm),
      hfinalOne, hfinalFrame⟩

private theorem sourceCellBit_invariantRuns
    (tm : TM workTapeCount)
    (regs : NeighborhoodTrial.Registers controller)
    (input : List Bool) (allowed : Finset ℕ) (bound : ℕ)
    (blockLength tape block coordinate : ℕ) (store : Store)
    (htape : tape < tapeCount workTapeCount)
    (hblockLength :
      store (Layout.blockLength regs) = blockLength)
    (hpacked :
      store (packedTapeBlock regs) =
        tapeBlockCode workTapeCount tape block)
    (hcoordinate :
      store (inputRegisters regs).replacement = coordinate)
    (hword :
      store (inputRegisters regs).word =
        SearchProgram.prefixCacheValue controller input
          (SearchProgram.footprintLimit
            controller regs.footprint))
    (hinputLength : store controller.inputLength = input.length)
    (hpackedBound :
      tapeBlockCode workTapeCount tape block ≤ bound)
    (htapeCountBound : tapeCount workTapeCount ≤ bound)
    (hstateBound : Fintype.card tm.Q ≤ bound)
    (hlowerBound :
      Fintype.card tm.Q + blockLength ≤ bound)
    (hcoordinateBound : coordinate ≤ bound)
    (hblockProductBound : block * blockLength ≤ bound)
    (haddressBound :
      block * blockLength +
        (coordinate -
          (Fintype.card tm.Q + blockLength)) / 4 ≤ bound)
    (hfourBound : 4 ≤ bound)
    (hlimitSucc :
      SearchProgram.footprintLimit controller regs.footprint + 1 ≤
        bound)
    (hprefixCapacity :
      2 ^
          SearchProgram.footprintLimit controller regs.footprint ≤
        bound)
    (hstore :
      NeighborhoodProgram.ValuesWithin allowed bound store)
    (hframe :
      SearchProgram.InputFrame
        controller regs.footprint input store) :
    ∃ final steps,
      InvariantRuns
        (NeighborhoodProgram.ValuesWithin allowed bound)
        (sourceCellBit tm regs) store final steps ∧
      final (inputRegisters regs).result =
        (if (coordinate -
              (Fintype.card tm.Q + blockLength)) % 4 =
            initialGammaCode input tape
              (block * blockLength +
                (coordinate -
                  (Fintype.card tm.Q + blockLength)) / 4) then
          1
        else
          0) ∧
      final (inputRegisters regs).word =
        store (inputRegisters regs).word ∧
      final (inputRegisters regs).one = 1 ∧
      SearchProgram.InputFrame
        controller regs.footprint input final := by
  obtain ⟨decoded, decodeSteps, hdecodeRun, hdecodedTape,
      hdecodedBlock, hdecodedOne, hdecodedCoordinate,
      hdecodedWord, hdecodeOutside⟩ :=
    decodeTapeBlock_invariantRuns workTapeCount regs allowed bound
      store tape block htape hpacked hpackedBound
      htapeCountBound hstore
  have hdecodedBlockLength :
      decoded (Layout.blockLength regs) = blockLength := by
    rw [hdecodeOutside]
    · exact hblockLength
    · exact layoutIndex_not_mem_inputFootprint regs 2 (by decide)
  have hdecodedCoordinate' :
      decoded (inputRegisters regs).replacement = coordinate :=
    hdecodedCoordinate.trans hcoordinate
  let afterState :=
    Basic.exec
      (.imm (inputRegisters regs).value
        (Fintype.card tm.Q))
      decoded
  have hafterState :
      NeighborhoodProgram.ValuesWithin allowed bound afterState :=
    valuesWithin_update allowed bound
      (inputRegisters regs).value (Fintype.card tm.Q)
      decoded (InvariantRuns.final hdecodeRun) hstateBound
  let afterLower :=
    Basic.exec
      (.add (inputRegisters regs).value
        (inputRegisters regs).value
        (Layout.blockLength regs))
      afterState
  have hblockValueNe :
      Layout.blockLength regs ≠
        (inputRegisters regs).value :=
    regs.injective.ne (by decide)
  have hafterStateBlockLength :
      afterState (Layout.blockLength regs) = blockLength := by
    simp [afterState, Basic.exec, hblockValueNe,
      hdecodedBlockLength]
  have hafterLower :
      NeighborhoodProgram.ValuesWithin allowed bound afterLower := by
    apply valuesWithin_update allowed bound
      (inputRegisters regs).value
      (afterState (inputRegisters regs).value +
        afterState (Layout.blockLength regs))
      afterState hafterState
    simpa [afterState, Basic.exec, hblockValueNe,
      hdecodedBlockLength] using hlowerBound
  let ready :=
    Basic.exec
      (.sub (inputRegisters regs).replacement
        (inputRegisters regs).replacement
        (inputRegisters regs).value)
      afterLower
  have hafterLowerCoordinate :
      afterLower (inputRegisters regs).replacement =
        coordinate := by
    simp [afterLower, afterState, Basic.exec,
      (inputRegisters regs).index_ne
        (by decide : (11 : Fin 12) ≠ 7),
      hdecodedCoordinate']
  have hready :
      NeighborhoodProgram.ValuesWithin allowed bound ready := by
    apply valuesWithin_update allowed bound
      (inputRegisters regs).replacement
      (afterLower (inputRegisters regs).replacement -
        afterLower (inputRegisters regs).value)
      afterLower hafterLower
    exact (Nat.sub_le _ _).trans
      (by simpa [hafterLowerCoordinate] using hcoordinateBound)
  have hreadyCell :
      ready (inputRegisters regs).replacement =
        coordinate -
          (Fintype.card tm.Q + blockLength) := by
    simp [ready, afterLower, afterState, Basic.exec,
      (inputRegisters regs).index_ne
        (by decide : (11 : Fin 12) ≠ 7),
      hblockValueNe, hdecodedCoordinate',
      hdecodedBlockLength]
  have hreadyBlock :
      ready (inputRegisters regs).buffer = block := by
    simp [ready, afterLower, afterState, Basic.exec,
      (inputRegisters regs).index_ne
        (by decide : (1 : Fin 12) ≠ 7),
      (inputRegisters regs).index_ne
        (by decide : (1 : Fin 12) ≠ 11),
      hdecodedBlock]
  have hreadyTape :
      ready (inputRegisters regs).indexCount = tape := by
    simp [ready, afterLower, afterState, Basic.exec,
      (inputRegisters regs).index_ne
        (by decide : (8 : Fin 12) ≠ 7),
      (inputRegisters regs).index_ne
        (by decide : (8 : Fin 12) ≠ 11),
      hdecodedTape]
  have hreadyBlockLength :
      ready (Layout.blockLength regs) = blockLength := by
    have hblockReplacementNe :
        Layout.blockLength regs ≠
          (inputRegisters regs).replacement :=
      regs.injective.ne (by decide)
    simp [ready, afterLower, afterState, Basic.exec,
      hblockValueNe, hblockReplacementNe,
      hdecodedBlockLength]
  have hreadyWord :
      ready (inputRegisters regs).word =
        SearchProgram.prefixCacheValue controller input
          (SearchProgram.footprintLimit
            controller regs.footprint) := by
    simp [ready, afterLower, afterState, Basic.exec,
      (inputRegisters regs).index_ne
        (by decide : (0 : Fin 12) ≠ 7),
      (inputRegisters regs).index_ne
        (by decide : (0 : Fin 12) ≠ 11),
      hdecodedWord, hword]
  have hreadyOne :
      ready (inputRegisters regs).one = 1 := by
    simp [ready, afterLower, afterState, Basic.exec,
      (inputRegisters regs).index_ne
        (by decide : (6 : Fin 12) ≠ 7),
      (inputRegisters regs).index_ne
        (by decide : (6 : Fin 12) ≠ 11),
      hdecodedOne]
  have hprefixRun :
      InvariantRuns
        (NeighborhoodProgram.ValuesWithin allowed bound)
        (Cmd.seqList
          [decodeTapeBlock workTapeCount regs,
            .basic
              (.imm (inputRegisters regs).value
                (Fintype.card tm.Q)),
            .basic
              (.add (inputRegisters regs).value
                (inputRegisters regs).value
                (Layout.blockLength regs)),
            .basic
              (.sub (inputRegisters regs).replacement
                (inputRegisters regs).replacement
                (inputRegisters regs).value)])
        store ready (decodeSteps + 3) := by
    simpa [Cmd.seqList, afterState, afterLower, ready] using
      InvariantRuns.seq hdecodeRun
        (InvariantRuns.seq
          (InvariantRuns.basic
            (.imm (inputRegisters regs).value
              (Fintype.card tm.Q))
            decoded (InvariantRuns.final hdecodeRun)
            hafterState)
          (InvariantRuns.seq
            (InvariantRuns.basic
              (.add (inputRegisters regs).value
                (inputRegisters regs).value
                (Layout.blockLength regs))
              afterState hafterState hafterLower)
            (InvariantRuns.basic
              (.sub (inputRegisters regs).replacement
                (inputRegisters regs).replacement
                (inputRegisters regs).value)
              afterLower hafterLower hready)))
  have hprefixWrites :
      RAM.Structured.Footprint.CmdWritesWithin
        regs.footprint
        (Cmd.seqList
          [decodeTapeBlock workTapeCount regs,
            .basic
              (.imm (inputRegisters regs).value
                (Fintype.card tm.Q)),
            .basic
              (.add (inputRegisters regs).value
                (inputRegisters regs).value
                (Layout.blockLength regs)),
            .basic
              (.sub (inputRegisters regs).replacement
                (inputRegisters regs).replacement
                (inputRegisters regs).value)]) := by
    have hinputTrial :
        (inputRegisters regs).footprint ⊆ regs.footprint := by
      intro address haddress
      rcases Finset.mem_image.mp haddress with
        ⟨slot, _, rfl⟩
      exact Finset.mem_union_left _
        (Layout.index_mem_layout_footprint regs (inputMap slot))
    apply cmdWritesWithin_mono hinputTrial
    simp [Cmd.seqList,
      RAM.Structured.Footprint.CmdWritesWithin,
      RAM.Structured.Footprint.BasicWritesWithin,
      decodeTapeBlock_writesWithin_local,
      (inputRegisters regs).index_mem_footprint]
  have hreadyFrame :
      SearchProgram.InputFrame
        controller regs.footprint input ready :=
    NeighborhoodTrial.Registers.runs_preserves_inputFrame
      regs hprefixWrites (InvariantRuns.toRuns hprefixRun) hframe
  have hreadyInputLength :
      ready controller.inputLength = input.length := by
    calc
      ready controller.inputLength =
          store controller.inputLength := by
        apply NeighborhoodTrial.Registers.runs_preserves_controller_index
          regs hprefixWrites (InvariantRuns.toRuns hprefixRun)
        · decide
        · decide
        · decide
      _ = input.length := hinputLength
  obtain ⟨final, cellSteps, hcellRun, hresult,
      hfinalWord, hfinalOne, hfinalFrame⟩ :=
    cellBit_invariantRuns regs input allowed bound blockLength
      block tape
      (coordinate - (Fintype.card tm.Q + blockLength))
      ready hreadyBlockLength hreadyBlock hreadyTape hreadyCell
      hreadyWord hreadyInputLength hblockProductBound
      (by
        exact (Nat.sub_le _ _).trans hcoordinateBound)
      haddressBound hfourBound hlimitSucc hprefixCapacity
      (InvariantRuns.final hprefixRun) hreadyFrame
  exact
    ⟨final, decodeSteps + (1 + (1 + (1 + cellSteps))),
      by
        simpa [sourceCellBit, Cmd.seqList, afterState,
          afterLower, ready] using
          InvariantRuns.seq hdecodeRun
            (InvariantRuns.seq
              (InvariantRuns.basic
                (.imm (inputRegisters regs).value
                  (Fintype.card tm.Q))
                decoded (InvariantRuns.final hdecodeRun)
                hafterState)
              (InvariantRuns.seq
                (InvariantRuns.basic
                  (.add (inputRegisters regs).value
                    (inputRegisters regs).value
                    (Layout.blockLength regs))
                  afterState hafterState hafterLower)
                (InvariantRuns.seq
                  (InvariantRuns.basic
                    (.sub (inputRegisters regs).replacement
                      (inputRegisters regs).replacement
                      (inputRegisters regs).value)
                    afterLower hafterLower hready)
                  hcellRun))),
      hresult,
      hfinalWord.trans (hreadyWord.trans hword.symm),
      hfinalOne, hfinalFrame⟩

private theorem sourceUpperBit_runs
    (tm : TM workTapeCount)
    (regs : NeighborhoodTrial.Registers controller)
    (input : List Bool)
    (blockLength tape block coordinate : ℕ) (store : Store)
    (htape : tape < tapeCount workTapeCount)
    (hblockLength :
      store (Layout.blockLength regs) = blockLength)
    (hpacked :
      store (packedTapeBlock regs) =
        tapeBlockCode workTapeCount tape block)
    (hcoordinate :
      store (inputRegisters regs).replacement = coordinate)
    (hword :
      store (inputRegisters regs).word =
        SearchProgram.prefixCacheValue controller input
          (SearchProgram.footprintLimit
            controller regs.footprint))
    (hone : store (inputRegisters regs).one = 1)
    (hinputLength : store controller.inputLength = input.length)
    (hframe :
      SearchProgram.InputFrame
        controller regs.footprint input store) :
    ∃ final,
      Runs (sourceUpperBit tm regs) store final ∧
      final (inputRegisters regs).result =
        (if coordinate <
            Fintype.card tm.Q + 5 * blockLength then
          if (coordinate -
                (Fintype.card tm.Q + blockLength)) % 4 =
              initialGammaCode input tape
                (block * blockLength +
                  (coordinate -
                    (Fintype.card tm.Q + blockLength)) / 4) then
            1
          else
            0
        else
          0) ∧
      final (inputRegisters regs).word =
        store (inputRegisters regs).word ∧
      final (inputRegisters regs).one = 1 ∧
      SearchProgram.InputFrame
        controller regs.footprint input final := by
  let afterFive :=
    Basic.exec (.imm (inputRegisters regs).value 5) store
  let afterMul :=
    Basic.exec
      (.mul (inputRegisters regs).buffer
        (inputRegisters regs).value
        (Layout.blockLength regs))
      afterFive
  let afterState :=
    Basic.exec
      (.imm (inputRegisters regs).value
        (Fintype.card tm.Q))
      afterMul
  let afterUpper :=
    Basic.exec
      (.add (inputRegisters regs).buffer
        (inputRegisters regs).value
        (inputRegisters regs).buffer)
      afterState
  let tested :=
    Basic.exec
      (.sub (inputRegisters regs).test
        (inputRegisters regs).buffer
        (inputRegisters regs).replacement)
      afterUpper
  have hblockValueNe :
      Layout.blockLength regs ≠
        (inputRegisters regs).value :=
    regs.injective.ne (by decide)
  have htestedValue :
      tested (inputRegisters regs).test =
        Fintype.card tm.Q + 5 * blockLength - coordinate := by
    simp [tested, afterUpper, afterState, afterMul,
      afterFive, Basic.exec,
      (inputRegisters regs).index_ne
        (by decide : (11 : Fin 12) ≠ 7),
      (inputRegisters regs).index_ne
        (by decide : (11 : Fin 12) ≠ 1),
      (inputRegisters regs).index_ne
        (by decide : (1 : Fin 12) ≠ 7),
      hblockValueNe, hblockLength, hcoordinate]
  have hprefixRun :
      Runs
        (Cmd.seqList
          [.basic (.imm (inputRegisters regs).value 5),
            .basic
              (.mul (inputRegisters regs).buffer
                (inputRegisters regs).value
                (Layout.blockLength regs)),
            .basic
              (.imm (inputRegisters regs).value
                (Fintype.card tm.Q)),
            .basic
              (.add (inputRegisters regs).buffer
                (inputRegisters regs).value
                (inputRegisters regs).buffer),
            .basic
              (.sub (inputRegisters regs).test
                (inputRegisters regs).buffer
                (inputRegisters regs).replacement)])
        store tested := by
    simpa [Cmd.seqList, afterFive, afterMul,
      afterState, afterUpper, tested] using
      Runs.seq
        (Runs.basic
          (.imm (inputRegisters regs).value 5) store)
        (Runs.seq
          (Runs.basic
            (.mul (inputRegisters regs).buffer
              (inputRegisters regs).value
              (Layout.blockLength regs))
            afterFive)
          (Runs.seq
            (Runs.basic
              (.imm (inputRegisters regs).value
                (Fintype.card tm.Q))
              afterMul)
            (Runs.seq
              (Runs.basic
                (.add (inputRegisters regs).buffer
                  (inputRegisters regs).value
                  (inputRegisters regs).buffer)
                afterState)
              (Runs.basic
                (.sub (inputRegisters regs).test
                  (inputRegisters regs).buffer
                  (inputRegisters regs).replacement)
                afterUpper))))
  have hprefixWrites :
      RAM.Structured.Footprint.CmdWritesWithin
        regs.footprint
        (Cmd.seqList
          [.basic (.imm (inputRegisters regs).value 5),
            .basic
              (.mul (inputRegisters regs).buffer
                (inputRegisters regs).value
                (Layout.blockLength regs)),
            .basic
              (.imm (inputRegisters regs).value
                (Fintype.card tm.Q)),
            .basic
              (.add (inputRegisters regs).buffer
                (inputRegisters regs).value
                (inputRegisters regs).buffer),
            .basic
              (.sub (inputRegisters regs).test
                (inputRegisters regs).buffer
                (inputRegisters regs).replacement)]) := by
    simp [Cmd.seqList,
      RAM.Structured.Footprint.CmdWritesWithin,
      RAM.Structured.Footprint.BasicWritesWithin,
      writeFootprint_subset_trial_internal regs
        (inputIndex_mem_writeFootprint regs 1),
      writeFootprint_subset_trial_internal regs
        (inputIndex_mem_writeFootprint regs 5),
      writeFootprint_subset_trial_internal regs
        (inputIndex_mem_writeFootprint regs 7)]
  have htestedFrame :
      SearchProgram.InputFrame
        controller regs.footprint input tested :=
    NeighborhoodTrial.Registers.runs_preserves_inputFrame
      regs hprefixWrites hprefixRun hframe
  have htestedBlockLength :
      tested (Layout.blockLength regs) = blockLength := by
    have hblockBuffer :
        Layout.blockLength regs ≠
          (inputRegisters regs).buffer :=
      regs.injective.ne (by decide)
    have hblockTest :
        Layout.blockLength regs ≠
          (inputRegisters regs).test :=
      regs.injective.ne (by decide)
    simp [tested, afterUpper, afterState, afterMul,
      afterFive, Basic.exec, hblockValueNe, hblockBuffer,
      hblockTest, hblockLength]
  have htestedPacked :
      tested (packedTapeBlock regs) =
        tapeBlockCode workTapeCount tape block := by
    have hpackedValue :
        packedTapeBlock regs ≠
          (inputRegisters regs).value :=
      regs.injective.ne (by decide)
    have hpackedBuffer :
        packedTapeBlock regs ≠
          (inputRegisters regs).buffer :=
      regs.injective.ne (by decide)
    have hpackedTest :
        packedTapeBlock regs ≠
          (inputRegisters regs).test :=
      regs.injective.ne (by decide)
    simp [tested, afterUpper, afterState, afterMul,
      afterFive, Basic.exec, hpackedValue, hpackedBuffer,
      hpackedTest, hpacked]
  have htestedCoordinate :
      tested (inputRegisters regs).replacement = coordinate := by
    simp [tested, afterUpper, afterState, afterMul,
      afterFive, Basic.exec,
      (inputRegisters regs).index_ne
        (by decide : (11 : Fin 12) ≠ 7),
      (inputRegisters regs).index_ne
        (by decide : (11 : Fin 12) ≠ 1),
      (inputRegisters regs).index_ne
        (by decide : (11 : Fin 12) ≠ 5),
      hcoordinate]
  have htestedWord :
      tested (inputRegisters regs).word =
        SearchProgram.prefixCacheValue controller input
          (SearchProgram.footprintLimit
            controller regs.footprint) := by
    simp [tested, afterUpper, afterState, afterMul,
      afterFive, Basic.exec,
      (inputRegisters regs).index_ne
        (by decide : (0 : Fin 12) ≠ 7),
      (inputRegisters regs).index_ne
        (by decide : (0 : Fin 12) ≠ 1),
      (inputRegisters regs).index_ne
        (by decide : (0 : Fin 12) ≠ 5),
      hword]
  have htestedOne :
      tested (inputRegisters regs).one = 1 := by
    simp [tested, afterUpper, afterState, afterMul,
      afterFive, Basic.exec,
      (inputRegisters regs).index_ne
        (by decide : (6 : Fin 12) ≠ 7),
      (inputRegisters regs).index_ne
        (by decide : (6 : Fin 12) ≠ 1),
      (inputRegisters regs).index_ne
        (by decide : (6 : Fin 12) ≠ 5),
      hone]
  have htestedInputLength :
      tested controller.inputLength = input.length := by
    calc
      tested controller.inputLength =
          store controller.inputLength := by
        apply NeighborhoodTrial.Registers.runs_preserves_controller_index
          regs hprefixWrites hprefixRun
        · decide
        · decide
        · decide
      _ = input.length := hinputLength
  by_cases hupper :
      coordinate < Fintype.card tm.Q + 5 * blockLength
  · have htestNonzero :
        tested (inputRegisters regs).test ≠ 0 := by
      rw [htestedValue]
      omega
    obtain ⟨final, hcellRun, hresult, hfinalWord,
        hfinalOne, hfinalFrame⟩ :=
      sourceCellBit_runs tm regs input blockLength tape block
        coordinate tested htape htestedBlockLength
        htestedPacked htestedCoordinate htestedWord
        htestedInputLength htestedFrame
    have hrun :
        Runs (sourceUpperBit tm regs) store final := by
      simpa [sourceUpperBit, Cmd.seqList, afterFive,
        afterMul, afterState, afterUpper, tested] using
        Runs.seq
          (Runs.basic
            (.imm (inputRegisters regs).value 5) store)
          (Runs.seq
            (Runs.basic
              (.mul (inputRegisters regs).buffer
                (inputRegisters regs).value
                (Layout.blockLength regs))
              afterFive)
            (Runs.seq
              (Runs.basic
                (.imm (inputRegisters regs).value
                  (Fintype.card tm.Q))
                afterMul)
              (Runs.seq
                (Runs.basic
                  (.add (inputRegisters regs).buffer
                    (inputRegisters regs).value
                    (inputRegisters regs).buffer)
                  afterState)
                (Runs.seq
                  (Runs.basic
                    (.sub (inputRegisters regs).test
                      (inputRegisters regs).buffer
                      (inputRegisters regs).replacement)
                    afterUpper)
                  (Runs.ifNonzero htestNonzero hcellRun)))))
    exact
      ⟨final, hrun, by simpa [hupper] using hresult,
        hfinalWord.trans (htestedWord.trans hword.symm),
        hfinalOne, hfinalFrame⟩
  · have htestZero :
        tested (inputRegisters regs).test = 0 := by
      rw [htestedValue]
      omega
    let final :=
      Basic.exec
        (.imm (inputRegisters regs).result 0) tested
    have hzeroRun :
        Runs
          (.basic
            (.imm (inputRegisters regs).result 0))
          tested final :=
      Runs.basic _ _
    have hrun :
        Runs (sourceUpperBit tm regs) store final := by
      simpa [sourceUpperBit, Cmd.seqList, afterFive,
        afterMul, afterState, afterUpper, tested, final] using
        Runs.seq
          (Runs.basic
            (.imm (inputRegisters regs).value 5) store)
          (Runs.seq
            (Runs.basic
              (.mul (inputRegisters regs).buffer
                (inputRegisters regs).value
                (Layout.blockLength regs))
              afterFive)
            (Runs.seq
              (Runs.basic
                (.imm (inputRegisters regs).value
                  (Fintype.card tm.Q))
                afterMul)
              (Runs.seq
                (Runs.basic
                  (.add (inputRegisters regs).buffer
                    (inputRegisters regs).value
                    (inputRegisters regs).buffer)
                  afterState)
                (Runs.seq
                  (Runs.basic
                    (.sub (inputRegisters regs).test
                      (inputRegisters regs).buffer
                      (inputRegisters regs).replacement)
                    afterUpper)
                  (Runs.ifZero htestZero hzeroRun)))))
    have hfinalFrame :
        SearchProgram.InputFrame
          controller regs.footprint input final := by
      apply NeighborhoodTrial.Registers.runs_preserves_inputFrame
        regs
        (command := .basic
          (.imm (inputRegisters regs).result 0))
        (initial := tested) (final := final)
      · simpa [RAM.Structured.Footprint.CmdWritesWithin,
          RAM.Structured.Footprint.BasicWritesWithin]
          using writeFootprint_subset_trial_internal regs
            (inputIndex_mem_writeFootprint regs 10)
      · exact hzeroRun
      · exact htestedFrame
    refine
      ⟨final, hrun, ?_, ?_, ?_, hfinalFrame⟩
    · simp [final, Basic.exec, hupper]
    · simp [final, Basic.exec,
        (inputRegisters regs).index_ne
          (by decide : (0 : Fin 12) ≠ 10),
        htestedWord, hword]
    · simp [final, Basic.exec,
        (inputRegisters regs).index_ne
          (by decide : (6 : Fin 12) ≠ 10),
        htestedOne]

private theorem sourceUpperBit_invariantRuns
    (tm : TM workTapeCount)
    (regs : NeighborhoodTrial.Registers controller)
    (input : List Bool) (allowed : Finset ℕ) (bound : ℕ)
    (blockLength tape block coordinate : ℕ) (store : Store)
    (htape : tape < tapeCount workTapeCount)
    (hblockLength :
      store (Layout.blockLength regs) = blockLength)
    (hpacked :
      store (packedTapeBlock regs) =
        tapeBlockCode workTapeCount tape block)
    (hcoordinate :
      store (inputRegisters regs).replacement = coordinate)
    (hword :
      store (inputRegisters regs).word =
        SearchProgram.prefixCacheValue controller input
          (SearchProgram.footprintLimit
            controller regs.footprint))
    (hone : store (inputRegisters regs).one = 1)
    (hinputLength : store controller.inputLength = input.length)
    (hpackedBound :
      tapeBlockCode workTapeCount tape block ≤ bound)
    (htapeCountBound : tapeCount workTapeCount ≤ bound)
    (hstateBound : Fintype.card tm.Q ≤ bound)
    (hfiveBlockBound : 5 * blockLength ≤ bound)
    (hupperBound :
      Fintype.card tm.Q + 5 * blockLength ≤ bound)
    (hlowerBound :
      Fintype.card tm.Q + blockLength ≤ bound)
    (hcoordinateBound : coordinate ≤ bound)
    (hblockProductBound : block * blockLength ≤ bound)
    (haddressBound :
      block * blockLength +
        (coordinate -
          (Fintype.card tm.Q + blockLength)) / 4 ≤ bound)
    (hfiveBound : 5 ≤ bound)
    (hlimitSucc :
      SearchProgram.footprintLimit controller regs.footprint + 1 ≤
        bound)
    (hprefixCapacity :
      2 ^
          SearchProgram.footprintLimit controller regs.footprint ≤
        bound)
    (hstore :
      NeighborhoodProgram.ValuesWithin allowed bound store)
    (hframe :
      SearchProgram.InputFrame
        controller regs.footprint input store) :
    ∃ final steps,
      InvariantRuns
        (NeighborhoodProgram.ValuesWithin allowed bound)
        (sourceUpperBit tm regs) store final steps ∧
      final (inputRegisters regs).result =
        (if coordinate <
            Fintype.card tm.Q + 5 * blockLength then
          if (coordinate -
                (Fintype.card tm.Q + blockLength)) % 4 =
              initialGammaCode input tape
                (block * blockLength +
                  (coordinate -
                    (Fintype.card tm.Q + blockLength)) / 4) then
            1
          else
            0
        else
          0) ∧
      final (inputRegisters regs).word =
        store (inputRegisters regs).word ∧
      final (inputRegisters regs).one = 1 ∧
      SearchProgram.InputFrame
        controller regs.footprint input final := by
  let afterFive :=
    Basic.exec (.imm (inputRegisters regs).value 5) store
  have hafterFive :
      NeighborhoodProgram.ValuesWithin allowed bound afterFive :=
    valuesWithin_update allowed bound
      (inputRegisters regs).value 5 store hstore hfiveBound
  let afterMul :=
    Basic.exec
      (.mul (inputRegisters regs).buffer
        (inputRegisters regs).value
        (Layout.blockLength regs))
      afterFive
  have hblockValueNe :
      Layout.blockLength regs ≠
        (inputRegisters regs).value :=
    regs.injective.ne (by decide)
  have hafterMul :
      NeighborhoodProgram.ValuesWithin allowed bound afterMul := by
    apply valuesWithin_update allowed bound
      (inputRegisters regs).buffer
      (afterFive (inputRegisters regs).value *
        afterFive (Layout.blockLength regs))
      afterFive hafterFive
    simpa [afterFive, Basic.exec, hblockValueNe,
      hblockLength] using hfiveBlockBound
  let afterState :=
    Basic.exec
      (.imm (inputRegisters regs).value
        (Fintype.card tm.Q))
      afterMul
  have hafterState :
      NeighborhoodProgram.ValuesWithin allowed bound afterState :=
    valuesWithin_update allowed bound
      (inputRegisters regs).value (Fintype.card tm.Q)
      afterMul hafterMul hstateBound
  let afterUpper :=
    Basic.exec
      (.add (inputRegisters regs).buffer
        (inputRegisters regs).value
        (inputRegisters regs).buffer)
      afterState
  have hafterUpper :
      NeighborhoodProgram.ValuesWithin allowed bound afterUpper := by
    apply valuesWithin_update allowed bound
      (inputRegisters regs).buffer
      (afterState (inputRegisters regs).value +
        afterState (inputRegisters regs).buffer)
      afterState hafterState
    have hvalue :
        afterState (inputRegisters regs).value =
          Fintype.card tm.Q := by
      simp [afterState, Basic.exec]
    have hbuffer :
        afterState (inputRegisters regs).buffer =
          5 * blockLength := by
      simp [afterState, afterMul, afterFive, Basic.exec,
        (inputRegisters regs).index_ne
          (by decide : (1 : Fin 12) ≠ 7),
        hblockValueNe, hblockLength]
    rw [hvalue, hbuffer]
    exact hupperBound
  let tested :=
    Basic.exec
      (.sub (inputRegisters regs).test
        (inputRegisters regs).buffer
        (inputRegisters regs).replacement)
      afterUpper
  have htested :
      NeighborhoodProgram.ValuesWithin allowed bound tested := by
    apply valuesWithin_update allowed bound
      (inputRegisters regs).test
      (afterUpper (inputRegisters regs).buffer -
        afterUpper (inputRegisters regs).replacement)
      afterUpper hafterUpper
    exact (Nat.sub_le _ _).trans
      (by
        have hbuffer :
            afterUpper (inputRegisters regs).buffer =
              Fintype.card tm.Q + 5 * blockLength := by
          simp [afterUpper, afterState, afterMul, afterFive,
            Basic.exec,
            (inputRegisters regs).index_ne
              (by decide : (1 : Fin 12) ≠ 7),
            hblockValueNe, hblockLength]
        simpa [hbuffer] using hupperBound)
  have htestedValue :
      tested (inputRegisters regs).test =
        Fintype.card tm.Q + 5 * blockLength - coordinate := by
    simp [tested, afterUpper, afterState, afterMul,
      afterFive, Basic.exec,
      (inputRegisters regs).index_ne
        (by decide : (11 : Fin 12) ≠ 7),
      (inputRegisters regs).index_ne
        (by decide : (11 : Fin 12) ≠ 1),
      (inputRegisters regs).index_ne
        (by decide : (1 : Fin 12) ≠ 7),
      hblockValueNe, hblockLength, hcoordinate]
  have hprefixRun :
      InvariantRuns
        (NeighborhoodProgram.ValuesWithin allowed bound)
        (Cmd.seqList
          [.basic (.imm (inputRegisters regs).value 5),
            .basic
              (.mul (inputRegisters regs).buffer
                (inputRegisters regs).value
                (Layout.blockLength regs)),
            .basic
              (.imm (inputRegisters regs).value
                (Fintype.card tm.Q)),
            .basic
              (.add (inputRegisters regs).buffer
                (inputRegisters regs).value
                (inputRegisters regs).buffer),
            .basic
              (.sub (inputRegisters regs).test
                (inputRegisters regs).buffer
                (inputRegisters regs).replacement)])
        store tested 5 := by
    simpa [Cmd.seqList, afterFive, afterMul,
      afterState, afterUpper, tested] using
      InvariantRuns.seq
        (InvariantRuns.basic
          (.imm (inputRegisters regs).value 5)
          store hstore hafterFive)
        (InvariantRuns.seq
          (InvariantRuns.basic
            (.mul (inputRegisters regs).buffer
              (inputRegisters regs).value
              (Layout.blockLength regs))
            afterFive hafterFive hafterMul)
          (InvariantRuns.seq
            (InvariantRuns.basic
              (.imm (inputRegisters regs).value
                (Fintype.card tm.Q))
              afterMul hafterMul hafterState)
            (InvariantRuns.seq
              (InvariantRuns.basic
                (.add (inputRegisters regs).buffer
                  (inputRegisters regs).value
                  (inputRegisters regs).buffer)
                afterState hafterState hafterUpper)
              (InvariantRuns.basic
                (.sub (inputRegisters regs).test
                  (inputRegisters regs).buffer
                  (inputRegisters regs).replacement)
                afterUpper hafterUpper htested))))
  have hprefixWrites :
      RAM.Structured.Footprint.CmdWritesWithin
        regs.footprint
        (Cmd.seqList
          [.basic (.imm (inputRegisters regs).value 5),
            .basic
              (.mul (inputRegisters regs).buffer
                (inputRegisters regs).value
                (Layout.blockLength regs)),
            .basic
              (.imm (inputRegisters regs).value
                (Fintype.card tm.Q)),
            .basic
              (.add (inputRegisters regs).buffer
                (inputRegisters regs).value
                (inputRegisters regs).buffer),
            .basic
              (.sub (inputRegisters regs).test
                (inputRegisters regs).buffer
                (inputRegisters regs).replacement)]) := by
    simp [Cmd.seqList,
      RAM.Structured.Footprint.CmdWritesWithin,
      RAM.Structured.Footprint.BasicWritesWithin,
      writeFootprint_subset_trial_internal regs
        (inputIndex_mem_writeFootprint regs 1),
      writeFootprint_subset_trial_internal regs
        (inputIndex_mem_writeFootprint regs 5),
      writeFootprint_subset_trial_internal regs
        (inputIndex_mem_writeFootprint regs 7)]
  have htestedFrame :
      SearchProgram.InputFrame
        controller regs.footprint input tested :=
    NeighborhoodTrial.Registers.runs_preserves_inputFrame
      regs hprefixWrites (InvariantRuns.toRuns hprefixRun) hframe
  have htestedBlockLength :
      tested (Layout.blockLength regs) = blockLength := by
    have hblockBuffer :
        Layout.blockLength regs ≠
          (inputRegisters regs).buffer :=
      regs.injective.ne (by decide)
    have hblockTest :
        Layout.blockLength regs ≠
          (inputRegisters regs).test :=
      regs.injective.ne (by decide)
    simp [tested, afterUpper, afterState, afterMul,
      afterFive, Basic.exec, hblockValueNe, hblockBuffer,
      hblockTest, hblockLength]
  have htestedPacked :
      tested (packedTapeBlock regs) =
        tapeBlockCode workTapeCount tape block := by
    have hpackedValue :
        packedTapeBlock regs ≠
          (inputRegisters regs).value :=
      regs.injective.ne (by decide)
    have hpackedBuffer :
        packedTapeBlock regs ≠
          (inputRegisters regs).buffer :=
      regs.injective.ne (by decide)
    have hpackedTest :
        packedTapeBlock regs ≠
          (inputRegisters regs).test :=
      regs.injective.ne (by decide)
    simp [tested, afterUpper, afterState, afterMul,
      afterFive, Basic.exec, hpackedValue, hpackedBuffer,
      hpackedTest, hpacked]
  have htestedCoordinate :
      tested (inputRegisters regs).replacement = coordinate := by
    simp [tested, afterUpper, afterState, afterMul,
      afterFive, Basic.exec,
      (inputRegisters regs).index_ne
        (by decide : (11 : Fin 12) ≠ 7),
      (inputRegisters regs).index_ne
        (by decide : (11 : Fin 12) ≠ 1),
      (inputRegisters regs).index_ne
        (by decide : (11 : Fin 12) ≠ 5),
      hcoordinate]
  have htestedWord :
      tested (inputRegisters regs).word =
        SearchProgram.prefixCacheValue controller input
          (SearchProgram.footprintLimit
            controller regs.footprint) := by
    simp [tested, afterUpper, afterState, afterMul,
      afterFive, Basic.exec,
      (inputRegisters regs).index_ne
        (by decide : (0 : Fin 12) ≠ 7),
      (inputRegisters regs).index_ne
        (by decide : (0 : Fin 12) ≠ 1),
      (inputRegisters regs).index_ne
        (by decide : (0 : Fin 12) ≠ 5),
      hword]
  have htestedInputLength :
      tested controller.inputLength = input.length := by
    calc
      tested controller.inputLength =
          store controller.inputLength := by
        apply NeighborhoodTrial.Registers.runs_preserves_controller_index
          regs hprefixWrites (InvariantRuns.toRuns hprefixRun)
        · decide
        · decide
        · decide
      _ = input.length := hinputLength
  by_cases hupper :
      coordinate < Fintype.card tm.Q + 5 * blockLength
  · have htestNonzero :
        tested (inputRegisters regs).test ≠ 0 := by
      rw [htestedValue]
      omega
    obtain ⟨final, cellSteps, hcellRun, _hresult,
        _hfinalWord, _hfinalOne, _hfinalFrame⟩ :=
      sourceCellBit_invariantRuns tm regs input allowed bound
        blockLength tape block coordinate tested htape
        htestedBlockLength htestedPacked htestedCoordinate
        htestedWord htestedInputLength hpackedBound
        htapeCountBound hstateBound hlowerBound
        hcoordinateBound hblockProductBound haddressBound
        (by omega) hlimitSucc hprefixCapacity htested
        htestedFrame
    have hinvariant :
        InvariantRuns
          (NeighborhoodProgram.ValuesWithin allowed bound)
          (sourceUpperBit tm regs) store final
          (1 + (1 + (1 + (1 +
            (1 + (cellSteps + 2)))))) := by
      simpa [sourceUpperBit, Cmd.seqList, afterFive,
        afterMul, afterState, afterUpper, tested] using
        InvariantRuns.seq
          (InvariantRuns.basic
            (.imm (inputRegisters regs).value 5)
            store hstore hafterFive)
          (InvariantRuns.seq
            (InvariantRuns.basic
              (.mul (inputRegisters regs).buffer
                (inputRegisters regs).value
                (Layout.blockLength regs))
              afterFive hafterFive hafterMul)
            (InvariantRuns.seq
              (InvariantRuns.basic
                (.imm (inputRegisters regs).value
                  (Fintype.card tm.Q))
                afterMul hafterMul hafterState)
              (InvariantRuns.seq
                (InvariantRuns.basic
                  (.add (inputRegisters regs).buffer
                    (inputRegisters regs).value
                    (inputRegisters regs).buffer)
                  afterState hafterState hafterUpper)
                (InvariantRuns.seq
                  (InvariantRuns.basic
                    (.sub (inputRegisters regs).test
                      (inputRegisters regs).buffer
                      (inputRegisters regs).replacement)
                    afterUpper hafterUpper htested)
                  (InvariantRuns.ifNonzero
                    (onZero := .basic
                      (.imm (inputRegisters regs).result 0))
                    htestNonzero
                    hcellRun)))))
    obtain ⟨semanticFinal, hsemanticRun, hresult,
        hfinalWord, hfinalOne, hfinalFrame⟩ :=
      sourceUpperBit_runs tm regs input blockLength tape block
        coordinate store htape hblockLength hpacked hcoordinate
        hword hone hinputLength hframe
    have heq : final = semanticFinal :=
      runs_final_eq (InvariantRuns.toRuns hinvariant) hsemanticRun
    subst semanticFinal
    exact
      ⟨final,
        1 + (1 + (1 + (1 + (1 + (cellSteps + 2))))),
        hinvariant,
        hresult, hfinalWord, hfinalOne, hfinalFrame⟩
  · have htestZero :
        tested (inputRegisters regs).test = 0 := by
      rw [htestedValue]
      omega
    let final :=
      Basic.exec
        (.imm (inputRegisters regs).result 0) tested
    have hfinal :
        NeighborhoodProgram.ValuesWithin allowed bound final :=
      valuesWithin_update allowed bound
        (inputRegisters regs).result 0 tested htested
        (by omega)
    have hzeroRun :
        InvariantRuns
          (NeighborhoodProgram.ValuesWithin allowed bound)
          (.basic
            (.imm (inputRegisters regs).result 0))
          tested final 1 :=
      InvariantRuns.basic _ _ htested hfinal
    have hinvariant :
        InvariantRuns
          (NeighborhoodProgram.ValuesWithin allowed bound)
          (sourceUpperBit tm regs) store final 7 := by
      simpa [sourceUpperBit, Cmd.seqList, afterFive,
        afterMul, afterState, afterUpper, tested, final] using
        InvariantRuns.seq
          (InvariantRuns.basic
            (.imm (inputRegisters regs).value 5)
            store hstore hafterFive)
          (InvariantRuns.seq
            (InvariantRuns.basic
              (.mul (inputRegisters regs).buffer
                (inputRegisters regs).value
                (Layout.blockLength regs))
              afterFive hafterFive hafterMul)
            (InvariantRuns.seq
              (InvariantRuns.basic
                (.imm (inputRegisters regs).value
                  (Fintype.card tm.Q))
                afterMul hafterMul hafterState)
              (InvariantRuns.seq
                (InvariantRuns.basic
                  (.add (inputRegisters regs).buffer
                    (inputRegisters regs).value
                    (inputRegisters regs).buffer)
                  afterState hafterState hafterUpper)
                (InvariantRuns.seq
                  (InvariantRuns.basic
                    (.sub (inputRegisters regs).test
                      (inputRegisters regs).buffer
                      (inputRegisters regs).replacement)
                    afterUpper hafterUpper htested)
                  (InvariantRuns.ifZero htestZero hzeroRun)))))
    obtain ⟨semanticFinal, hsemanticRun, hresult,
        hfinalWord, hfinalOne, hfinalFrame⟩ :=
      sourceUpperBit_runs tm regs input blockLength tape block
        coordinate store htape hblockLength hpacked hcoordinate
        hword hone hinputLength hframe
    have heq : final = semanticFinal :=
      runs_final_eq (InvariantRuns.toRuns hinvariant) hsemanticRun
    subst semanticFinal
    exact
      ⟨final, 7, hinvariant, hresult, hfinalWord,
        hfinalOne, hfinalFrame⟩

private theorem sourcePayloadBit_runs
    (tm : TM workTapeCount)
    (regs : NeighborhoodTrial.Registers controller)
    (input : List Bool)
    (blockLength tape block coordinate : ℕ) (store : Store)
    (htape : tape < tapeCount workTapeCount)
    (hblockLength :
      store (Layout.blockLength regs) = blockLength)
    (hpacked :
      store (packedTapeBlock regs) =
        tapeBlockCode workTapeCount tape block)
    (hcoordinate :
      store (inputRegisters regs).replacement = coordinate)
    (hword :
      store (inputRegisters regs).word =
        SearchProgram.prefixCacheValue controller input
          (SearchProgram.footprintLimit
            controller regs.footprint))
    (hone : store (inputRegisters regs).one = 1)
    (hinputLength : store controller.inputLength = input.length)
    (hframe :
      SearchProgram.InputFrame
        controller regs.footprint input store) :
    ∃ final,
      Runs (sourcePayloadBit tm regs) store final ∧
      final (inputRegisters regs).result =
        (if Fintype.card tm.Q + blockLength ≤ coordinate ∧
            coordinate <
              Fintype.card tm.Q + 5 * blockLength then
          if (coordinate -
                (Fintype.card tm.Q + blockLength)) % 4 =
              initialGammaCode input tape
                (block * blockLength +
                  (coordinate -
                    (Fintype.card tm.Q + blockLength)) / 4) then
            1
          else
            0
        else
          0) ∧
      final (inputRegisters regs).word =
        store (inputRegisters regs).word ∧
      final (inputRegisters regs).one = 1 ∧
      SearchProgram.InputFrame
        controller regs.footprint input final := by
  let afterState :=
    Basic.exec
      (.imm (inputRegisters regs).buffer
        (Fintype.card tm.Q))
      store
  let afterLower :=
    Basic.exec
      (.add (inputRegisters regs).buffer
        (inputRegisters regs).buffer
        (Layout.blockLength regs))
      afterState
  let tested :=
    Basic.exec
      (.sub (inputRegisters regs).test
        (inputRegisters regs).buffer
        (inputRegisters regs).replacement)
      afterLower
  have htestedValue :
      tested (inputRegisters regs).test =
        Fintype.card tm.Q + blockLength - coordinate := by
    have hblockBufferNe :
        Layout.blockLength regs ≠
          (inputRegisters regs).buffer :=
      regs.injective.ne (by decide)
    simp [tested, afterLower, afterState, Basic.exec,
      hblockBufferNe,
      (inputRegisters regs).index_ne
        (by decide : (11 : Fin 12) ≠ 1),
      hblockLength, hcoordinate]
  have hprefixRun :
      Runs
        (Cmd.seqList
          [.basic
            (.imm (inputRegisters regs).buffer
              (Fintype.card tm.Q)),
            .basic
              (.add (inputRegisters regs).buffer
                (inputRegisters regs).buffer
                (Layout.blockLength regs)),
            .basic
              (.sub (inputRegisters regs).test
                (inputRegisters regs).buffer
                (inputRegisters regs).replacement)])
        store tested := by
    simpa [Cmd.seqList, afterState, afterLower, tested] using
      Runs.seq
        (Runs.basic
          (.imm (inputRegisters regs).buffer
            (Fintype.card tm.Q))
          store)
        (Runs.seq
          (Runs.basic
            (.add (inputRegisters regs).buffer
              (inputRegisters regs).buffer
              (Layout.blockLength regs))
            afterState)
          (Runs.basic
            (.sub (inputRegisters regs).test
              (inputRegisters regs).buffer
              (inputRegisters regs).replacement)
            afterLower))
  have hprefixWrites :
      RAM.Structured.Footprint.CmdWritesWithin
        regs.footprint
        (Cmd.seqList
          [.basic
            (.imm (inputRegisters regs).buffer
              (Fintype.card tm.Q)),
            .basic
              (.add (inputRegisters regs).buffer
                (inputRegisters regs).buffer
                (Layout.blockLength regs)),
            .basic
              (.sub (inputRegisters regs).test
                (inputRegisters regs).buffer
                (inputRegisters regs).replacement)]) := by
    simp [Cmd.seqList,
      RAM.Structured.Footprint.CmdWritesWithin,
      RAM.Structured.Footprint.BasicWritesWithin,
      writeFootprint_subset_trial_internal regs
        (inputIndex_mem_writeFootprint regs 1),
      writeFootprint_subset_trial_internal regs
        (inputIndex_mem_writeFootprint regs 5)]
  have htestedFrame :
      SearchProgram.InputFrame
        controller regs.footprint input tested :=
    NeighborhoodTrial.Registers.runs_preserves_inputFrame
      regs hprefixWrites hprefixRun hframe
  have htestedBlockLength :
      tested (Layout.blockLength regs) = blockLength := by
    have hblockBuffer :
        Layout.blockLength regs ≠
          (inputRegisters regs).buffer :=
      regs.injective.ne (by decide)
    have hblockTest :
        Layout.blockLength regs ≠
          (inputRegisters regs).test :=
      regs.injective.ne (by decide)
    simp [tested, afterLower, afterState, Basic.exec,
      hblockBuffer, hblockTest, hblockLength]
  have htestedPacked :
      tested (packedTapeBlock regs) =
        tapeBlockCode workTapeCount tape block := by
    have hpackedBuffer :
        packedTapeBlock regs ≠
          (inputRegisters regs).buffer :=
      regs.injective.ne (by decide)
    have hpackedTest :
        packedTapeBlock regs ≠
          (inputRegisters regs).test :=
      regs.injective.ne (by decide)
    simp [tested, afterLower, afterState, Basic.exec,
      hpackedBuffer, hpackedTest, hpacked]
  have htestedCoordinate :
      tested (inputRegisters regs).replacement = coordinate := by
    simp [tested, afterLower, afterState, Basic.exec,
      (inputRegisters regs).index_ne
        (by decide : (11 : Fin 12) ≠ 1),
      (inputRegisters regs).index_ne
        (by decide : (11 : Fin 12) ≠ 5),
      hcoordinate]
  have htestedWord :
      tested (inputRegisters regs).word =
        SearchProgram.prefixCacheValue controller input
          (SearchProgram.footprintLimit
            controller regs.footprint) := by
    simp [tested, afterLower, afterState, Basic.exec,
      (inputRegisters regs).index_ne
        (by decide : (0 : Fin 12) ≠ 1),
      (inputRegisters regs).index_ne
        (by decide : (0 : Fin 12) ≠ 5),
      hword]
  have htestedOne :
      tested (inputRegisters regs).one = 1 := by
    simp [tested, afterLower, afterState, Basic.exec,
      (inputRegisters regs).index_ne
        (by decide : (6 : Fin 12) ≠ 1),
      (inputRegisters regs).index_ne
        (by decide : (6 : Fin 12) ≠ 5),
      hone]
  have htestedInputLength :
      tested controller.inputLength = input.length := by
    calc
      tested controller.inputLength =
          store controller.inputLength := by
        apply NeighborhoodTrial.Registers.runs_preserves_controller_index
          regs hprefixWrites hprefixRun
        · decide
        · decide
        · decide
      _ = input.length := hinputLength
  by_cases hlower :
      Fintype.card tm.Q + blockLength ≤ coordinate
  · have htestZero :
        tested (inputRegisters regs).test = 0 := by
      rw [htestedValue]
      omega
    obtain ⟨final, hupperRun, hresult,
        hfinalWord, hfinalOne, hfinalFrame⟩ :=
      sourceUpperBit_runs tm regs input blockLength tape block
        coordinate tested htape htestedBlockLength
        htestedPacked htestedCoordinate htestedWord htestedOne
        htestedInputLength htestedFrame
    have hrun :
        Runs (sourcePayloadBit tm regs) store final := by
      simpa [sourcePayloadBit, Cmd.seqList, afterState,
        afterLower, tested] using
        Runs.seq
          (Runs.basic
            (.imm (inputRegisters regs).buffer
              (Fintype.card tm.Q))
            store)
          (Runs.seq
            (Runs.basic
              (.add (inputRegisters regs).buffer
                (inputRegisters regs).buffer
                (Layout.blockLength regs))
              afterState)
            (Runs.seq
              (Runs.basic
                (.sub (inputRegisters regs).test
                  (inputRegisters regs).buffer
                  (inputRegisters regs).replacement)
                afterLower)
              (Runs.ifZero htestZero hupperRun)))
    by_cases hupper :
        coordinate < Fintype.card tm.Q + 5 * blockLength
    · exact
        ⟨final, hrun, by simpa [hlower, hupper] using hresult,
          hfinalWord.trans (htestedWord.trans hword.symm),
          hfinalOne, hfinalFrame⟩
    · exact
        ⟨final, hrun, by simpa [hlower, hupper] using hresult,
          hfinalWord.trans (htestedWord.trans hword.symm),
          hfinalOne, hfinalFrame⟩
  · have htestNonzero :
        tested (inputRegisters regs).test ≠ 0 := by
      rw [htestedValue]
      omega
    let final :=
      Basic.exec
        (.imm (inputRegisters regs).result 0) tested
    have hzeroRun :
        Runs
          (.basic
            (.imm (inputRegisters regs).result 0))
          tested final :=
      Runs.basic _ _
    have hrun :
        Runs (sourcePayloadBit tm regs) store final := by
      simpa [sourcePayloadBit, Cmd.seqList, afterState,
        afterLower, tested, final] using
        Runs.seq
          (Runs.basic
            (.imm (inputRegisters regs).buffer
              (Fintype.card tm.Q))
            store)
          (Runs.seq
            (Runs.basic
              (.add (inputRegisters regs).buffer
                (inputRegisters regs).buffer
                (Layout.blockLength regs))
              afterState)
            (Runs.seq
              (Runs.basic
                (.sub (inputRegisters regs).test
                  (inputRegisters regs).buffer
                  (inputRegisters regs).replacement)
                afterLower)
              (Runs.ifNonzero htestNonzero hzeroRun)))
    have hfinalFrame :
        SearchProgram.InputFrame
          controller regs.footprint input final := by
      apply NeighborhoodTrial.Registers.runs_preserves_inputFrame
        regs
        (command := .basic
          (.imm (inputRegisters regs).result 0))
        (initial := tested) (final := final)
      · simpa [RAM.Structured.Footprint.CmdWritesWithin,
          RAM.Structured.Footprint.BasicWritesWithin]
          using writeFootprint_subset_trial_internal regs
            (inputIndex_mem_writeFootprint regs 10)
      · exact hzeroRun
      · exact htestedFrame
    refine
      ⟨final, hrun, ?_, ?_, ?_, hfinalFrame⟩
    · simp [final, Basic.exec, hlower]
    · simp [final, Basic.exec,
        (inputRegisters regs).index_ne
          (by decide : (0 : Fin 12) ≠ 10),
        htestedWord, hword]
    · simp [final, Basic.exec,
        (inputRegisters regs).index_ne
          (by decide : (6 : Fin 12) ≠ 10),
        htestedOne]

private theorem sourcePayloadBit_invariantRuns
    (tm : TM workTapeCount)
    (regs : NeighborhoodTrial.Registers controller)
    (input : List Bool) (allowed : Finset ℕ) (bound : ℕ)
    (blockLength tape block coordinate : ℕ) (store : Store)
    (htape : tape < tapeCount workTapeCount)
    (hblockLength :
      store (Layout.blockLength regs) = blockLength)
    (hpacked :
      store (packedTapeBlock regs) =
        tapeBlockCode workTapeCount tape block)
    (hcoordinate :
      store (inputRegisters regs).replacement = coordinate)
    (hword :
      store (inputRegisters regs).word =
        SearchProgram.prefixCacheValue controller input
          (SearchProgram.footprintLimit
            controller regs.footprint))
    (hone : store (inputRegisters regs).one = 1)
    (hinputLength : store controller.inputLength = input.length)
    (hpackedBound :
      tapeBlockCode workTapeCount tape block ≤ bound)
    (htapeCountBound : tapeCount workTapeCount ≤ bound)
    (hstateBound : Fintype.card tm.Q ≤ bound)
    (hfiveBlockBound : 5 * blockLength ≤ bound)
    (hupperBound :
      Fintype.card tm.Q + 5 * blockLength ≤ bound)
    (hlowerBound :
      Fintype.card tm.Q + blockLength ≤ bound)
    (hcoordinateBound : coordinate ≤ bound)
    (hblockProductBound : block * blockLength ≤ bound)
    (haddressBound :
      block * blockLength +
        (coordinate -
          (Fintype.card tm.Q + blockLength)) / 4 ≤ bound)
    (hfiveBound : 5 ≤ bound)
    (hlimitSucc :
      SearchProgram.footprintLimit controller regs.footprint + 1 ≤
        bound)
    (hprefixCapacity :
      2 ^
          SearchProgram.footprintLimit controller regs.footprint ≤
        bound)
    (hstore :
      NeighborhoodProgram.ValuesWithin allowed bound store)
    (hframe :
      SearchProgram.InputFrame
        controller regs.footprint input store) :
    ∃ final steps,
      InvariantRuns
        (NeighborhoodProgram.ValuesWithin allowed bound)
        (sourcePayloadBit tm regs) store final steps ∧
      final (inputRegisters regs).result =
        (if Fintype.card tm.Q + blockLength ≤ coordinate ∧
            coordinate <
              Fintype.card tm.Q + 5 * blockLength then
          if (coordinate -
                (Fintype.card tm.Q + blockLength)) % 4 =
              initialGammaCode input tape
                (block * blockLength +
                  (coordinate -
                    (Fintype.card tm.Q + blockLength)) / 4) then
            1
          else
            0
        else
          0) ∧
      final (inputRegisters regs).word =
        store (inputRegisters regs).word ∧
      final (inputRegisters regs).one = 1 ∧
      SearchProgram.InputFrame
        controller regs.footprint input final := by
  let afterState :=
    Basic.exec
      (.imm (inputRegisters regs).buffer
        (Fintype.card tm.Q))
      store
  have hafterState :
      NeighborhoodProgram.ValuesWithin allowed bound afterState :=
    valuesWithin_update allowed bound
      (inputRegisters regs).buffer (Fintype.card tm.Q)
      store hstore hstateBound
  let afterLower :=
    Basic.exec
      (.add (inputRegisters regs).buffer
        (inputRegisters regs).buffer
        (Layout.blockLength regs))
      afterState
  have hblockBufferNe :
      Layout.blockLength regs ≠
        (inputRegisters regs).buffer :=
    regs.injective.ne (by decide)
  have hafterLower :
      NeighborhoodProgram.ValuesWithin allowed bound afterLower := by
    apply valuesWithin_update allowed bound
      (inputRegisters regs).buffer
      (afterState (inputRegisters regs).buffer +
        afterState (Layout.blockLength regs))
      afterState hafterState
    simpa [afterState, Basic.exec, hblockBufferNe,
      hblockLength] using hlowerBound
  let tested :=
    Basic.exec
      (.sub (inputRegisters regs).test
        (inputRegisters regs).buffer
        (inputRegisters regs).replacement)
      afterLower
  have htested :
      NeighborhoodProgram.ValuesWithin allowed bound tested := by
    apply valuesWithin_update allowed bound
      (inputRegisters regs).test
      (afterLower (inputRegisters regs).buffer -
        afterLower (inputRegisters regs).replacement)
      afterLower hafterLower
    exact (Nat.sub_le _ _).trans
      (by
        have hbuffer :
            afterLower (inputRegisters regs).buffer =
              Fintype.card tm.Q + blockLength := by
          simp [afterLower, afterState, Basic.exec,
            hblockBufferNe, hblockLength]
        simpa [hbuffer] using hlowerBound)
  have htestedValue :
      tested (inputRegisters regs).test =
        Fintype.card tm.Q + blockLength - coordinate := by
    simp [tested, afterLower, afterState, Basic.exec,
      hblockBufferNe,
      (inputRegisters regs).index_ne
        (by decide : (11 : Fin 12) ≠ 1),
      hblockLength, hcoordinate]
  have hprefixRun :
      InvariantRuns
        (NeighborhoodProgram.ValuesWithin allowed bound)
        (Cmd.seqList
          [.basic
            (.imm (inputRegisters regs).buffer
              (Fintype.card tm.Q)),
            .basic
              (.add (inputRegisters regs).buffer
                (inputRegisters regs).buffer
                (Layout.blockLength regs)),
            .basic
              (.sub (inputRegisters regs).test
                (inputRegisters regs).buffer
                (inputRegisters regs).replacement)])
        store tested 3 := by
    simpa [Cmd.seqList, afterState, afterLower, tested] using
      InvariantRuns.seq
        (InvariantRuns.basic
          (.imm (inputRegisters regs).buffer
            (Fintype.card tm.Q))
          store hstore hafterState)
        (InvariantRuns.seq
          (InvariantRuns.basic
            (.add (inputRegisters regs).buffer
              (inputRegisters regs).buffer
              (Layout.blockLength regs))
            afterState hafterState hafterLower)
          (InvariantRuns.basic
            (.sub (inputRegisters regs).test
              (inputRegisters regs).buffer
              (inputRegisters regs).replacement)
            afterLower hafterLower htested))
  have hprefixWrites :
      RAM.Structured.Footprint.CmdWritesWithin
        regs.footprint
        (Cmd.seqList
          [.basic
            (.imm (inputRegisters regs).buffer
              (Fintype.card tm.Q)),
            .basic
              (.add (inputRegisters regs).buffer
                (inputRegisters regs).buffer
                (Layout.blockLength regs)),
            .basic
              (.sub (inputRegisters regs).test
                (inputRegisters regs).buffer
                (inputRegisters regs).replacement)]) := by
    simp [Cmd.seqList,
      RAM.Structured.Footprint.CmdWritesWithin,
      RAM.Structured.Footprint.BasicWritesWithin,
      writeFootprint_subset_trial_internal regs
        (inputIndex_mem_writeFootprint regs 1),
      writeFootprint_subset_trial_internal regs
        (inputIndex_mem_writeFootprint regs 5)]
  have htestedFrame :
      SearchProgram.InputFrame
        controller regs.footprint input tested :=
    NeighborhoodTrial.Registers.runs_preserves_inputFrame
      regs hprefixWrites (InvariantRuns.toRuns hprefixRun) hframe
  have htestedBlockLength :
      tested (Layout.blockLength regs) = blockLength := by
    have hblockTest :
        Layout.blockLength regs ≠
          (inputRegisters regs).test :=
      regs.injective.ne (by decide)
    simp [tested, afterLower, afterState, Basic.exec,
      hblockBufferNe, hblockTest, hblockLength]
  have htestedPacked :
      tested (packedTapeBlock regs) =
        tapeBlockCode workTapeCount tape block := by
    have hpackedBuffer :
        packedTapeBlock regs ≠
          (inputRegisters regs).buffer :=
      regs.injective.ne (by decide)
    have hpackedTest :
        packedTapeBlock regs ≠
          (inputRegisters regs).test :=
      regs.injective.ne (by decide)
    simp [tested, afterLower, afterState, Basic.exec,
      hpackedBuffer, hpackedTest, hpacked]
  have htestedCoordinate :
      tested (inputRegisters regs).replacement = coordinate := by
    simp [tested, afterLower, afterState, Basic.exec,
      (inputRegisters regs).index_ne
        (by decide : (11 : Fin 12) ≠ 1),
      (inputRegisters regs).index_ne
        (by decide : (11 : Fin 12) ≠ 5),
      hcoordinate]
  have htestedWord :
      tested (inputRegisters regs).word =
        SearchProgram.prefixCacheValue controller input
          (SearchProgram.footprintLimit
            controller regs.footprint) := by
    simp [tested, afterLower, afterState, Basic.exec,
      (inputRegisters regs).index_ne
        (by decide : (0 : Fin 12) ≠ 1),
      (inputRegisters regs).index_ne
        (by decide : (0 : Fin 12) ≠ 5),
      hword]
  have htestedOne :
      tested (inputRegisters regs).one = 1 := by
    simp [tested, afterLower, afterState, Basic.exec,
      (inputRegisters regs).index_ne
        (by decide : (6 : Fin 12) ≠ 1),
      (inputRegisters regs).index_ne
        (by decide : (6 : Fin 12) ≠ 5),
      hone]
  have htestedInputLength :
      tested controller.inputLength = input.length := by
    calc
      tested controller.inputLength =
          store controller.inputLength := by
        apply NeighborhoodTrial.Registers.runs_preserves_controller_index
          regs hprefixWrites (InvariantRuns.toRuns hprefixRun)
        · decide
        · decide
        · decide
      _ = input.length := hinputLength
  by_cases hlower :
      Fintype.card tm.Q + blockLength ≤ coordinate
  · have htestZero :
        tested (inputRegisters regs).test = 0 := by
      rw [htestedValue]
      omega
    obtain ⟨final, upperSteps, hupperRun, _hresult,
        _hfinalWord, _hfinalOne, _hfinalFrame⟩ :=
      sourceUpperBit_invariantRuns tm regs input allowed bound
        blockLength tape block coordinate tested htape
        htestedBlockLength htestedPacked htestedCoordinate
        htestedWord htestedOne htestedInputLength hpackedBound
        htapeCountBound hstateBound hfiveBlockBound hupperBound
        hlowerBound hcoordinateBound hblockProductBound
        haddressBound hfiveBound hlimitSucc hprefixCapacity
        htested htestedFrame
    have hinvariant :
        InvariantRuns
          (NeighborhoodProgram.ValuesWithin allowed bound)
          (sourcePayloadBit tm regs) store final
          (1 + (1 + (1 + (upperSteps + 1)))) := by
      simpa [sourcePayloadBit, Cmd.seqList, afterState,
        afterLower, tested] using
        InvariantRuns.seq
          (InvariantRuns.basic
            (.imm (inputRegisters regs).buffer
              (Fintype.card tm.Q))
            store hstore hafterState)
          (InvariantRuns.seq
            (InvariantRuns.basic
              (.add (inputRegisters regs).buffer
                (inputRegisters regs).buffer
                (Layout.blockLength regs))
              afterState hafterState hafterLower)
            (InvariantRuns.seq
              (InvariantRuns.basic
                (.sub (inputRegisters regs).test
                  (inputRegisters regs).buffer
                  (inputRegisters regs).replacement)
                afterLower hafterLower htested)
              (InvariantRuns.ifZero
                (onNonzero := .basic
                  (.imm (inputRegisters regs).result 0))
                htestZero hupperRun)))
    obtain ⟨semanticFinal, hsemanticRun, hresult,
        hfinalWord, hfinalOne, hfinalFrame⟩ :=
      sourcePayloadBit_runs tm regs input blockLength tape block
        coordinate store htape hblockLength hpacked hcoordinate
        hword hone hinputLength hframe
    have heq : final = semanticFinal :=
      runs_final_eq (InvariantRuns.toRuns hinvariant) hsemanticRun
    subst semanticFinal
    exact
      ⟨final, 1 + (1 + (1 + (upperSteps + 1))),
        hinvariant,
        hresult, hfinalWord, hfinalOne, hfinalFrame⟩
  · have htestNonzero :
        tested (inputRegisters regs).test ≠ 0 := by
      rw [htestedValue]
      omega
    let final :=
      Basic.exec
        (.imm (inputRegisters regs).result 0) tested
    have hfinal :
        NeighborhoodProgram.ValuesWithin allowed bound final :=
      valuesWithin_update allowed bound
        (inputRegisters regs).result 0 tested htested
        (by omega)
    have hzeroRun :
        InvariantRuns
          (NeighborhoodProgram.ValuesWithin allowed bound)
          (.basic
            (.imm (inputRegisters regs).result 0))
          tested final 1 :=
      InvariantRuns.basic _ _ htested hfinal
    have hinvariant :
        InvariantRuns
          (NeighborhoodProgram.ValuesWithin allowed bound)
          (sourcePayloadBit tm regs) store final 6 := by
      simpa [sourcePayloadBit, Cmd.seqList, afterState,
        afterLower, tested, final] using
        InvariantRuns.seq
          (InvariantRuns.basic
            (.imm (inputRegisters regs).buffer
              (Fintype.card tm.Q))
            store hstore hafterState)
          (InvariantRuns.seq
            (InvariantRuns.basic
              (.add (inputRegisters regs).buffer
                (inputRegisters regs).buffer
                (Layout.blockLength regs))
              afterState hafterState hafterLower)
            (InvariantRuns.seq
              (InvariantRuns.basic
                (.sub (inputRegisters regs).test
                  (inputRegisters regs).buffer
                  (inputRegisters regs).replacement)
                afterLower hafterLower htested)
              (InvariantRuns.ifNonzero
                (onZero := sourceUpperBit tm regs)
                htestNonzero hzeroRun)))
    obtain ⟨semanticFinal, hsemanticRun, hresult,
        hfinalWord, hfinalOne, hfinalFrame⟩ :=
      sourcePayloadBit_runs tm regs input blockLength tape block
        coordinate store htape hblockLength hpacked hcoordinate
        hword hone hinputLength hframe
    have heq : final = semanticFinal :=
      runs_final_eq (InvariantRuns.toRuns hinvariant) hsemanticRun
    subst semanticFinal
    exact
      ⟨final, 6, hinvariant, hresult, hfinalWord,
        hfinalOne, hfinalFrame⟩

private theorem equalResult_writesWithin_input
    (regs : NeighborhoodTrial.Registers controller)
    (value constant : ℕ) :
    RAM.Structured.Footprint.CmdWritesWithin
      (inputRegisters regs).footprint
      (equalImmediate regs value
        (inputRegisters regs).result constant) := by
  apply cmdWritesWithin_mono _ <|
    equalImmediate_writesWithin_local regs value
      (inputRegisters regs).result constant
  intro address haddress
  simp only [Finset.mem_insert, Finset.mem_singleton] at haddress
  rcases haddress with rfl | rfl | rfl | rfl <;>
    exact (inputRegisters regs).index_mem_footprint _

private theorem sourceBit_runs
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (regs : NeighborhoodTrial.Registers controller)
    (input : List Bool)
    (blockLength tape block coordinate : ℕ) (store : Store)
    (htape : tape < tapeCount workTapeCount)
    (hblockLength :
      store (Layout.blockLength regs) = blockLength)
    (hpacked :
      store (packedTapeBlock regs) =
        tapeBlockCode workTapeCount tape block)
    (hcoordinate :
      store (inputRegisters regs).replacement = coordinate)
    (hword :
      store (inputRegisters regs).word =
        SearchProgram.prefixCacheValue controller input
          (SearchProgram.footprintLimit
            controller regs.footprint))
    (hone : store (inputRegisters regs).one = 1)
    (hinputLength : store controller.inputLength = input.length)
    (hframe :
      SearchProgram.InputFrame
        controller regs.footprint input store) :
    ∃ final,
      Runs (sourceBit tm order regs) store final ∧
      final (inputRegisters regs).result =
        coordinateBitValue tm order input blockLength tape block
          coordinate ∧
      final (inputRegisters regs).word =
        store (inputRegisters regs).word ∧
      final (inputRegisters regs).one = 1 ∧
      SearchProgram.InputFrame
        controller regs.footprint input final := by
  let startCode := (order.state tm.qstart).val
  obtain ⟨afterStart, hstartRun, hstartResult, _hstartValue,
      hstartWord, hstartCoordinate, hstartOne,
      hstartFrame⟩ :=
    equalResult_runs regs input
      (inputRegisters regs).replacement startCode store
      ((inputRegisters regs).index_ne (by decide))
      ((inputRegisters regs).index_ne (by decide))
      hframe
  have hstartCoordinate' :
      afterStart (inputRegisters regs).replacement = coordinate :=
    hstartCoordinate.trans hcoordinate
  have hstartOne' :
      afterStart (inputRegisters regs).one = 1 :=
    hstartOne.trans hone
  by_cases hstart : coordinate = startCode
  · have hstartNonzero :
        afterStart (inputRegisters regs).result ≠ 0 := by
      rw [hstartResult, hcoordinate]
      simp [hstart]
    have hrun :
        Runs (sourceBit tm order regs) store afterStart := by
      simpa [sourceBit, startCode] using
        Runs.seq hstartRun
          (Runs.ifNonzero hstartNonzero (Runs.skip afterStart))
    refine
      ⟨afterStart, hrun, ?_, hstartWord, hstartOne',
        hstartFrame⟩
    rw [hstartResult, hcoordinate]
    simp [coordinateBitValue, coordinateBit, startCode, hstart]
  · have hstartZero :
        afterStart (inputRegisters regs).result = 0 := by
      rw [hstartResult, hcoordinate]
      simp [hstart]
    have hstart' :
        coordinate ≠ (order.state tm.qstart).val := by
      simpa [startCode] using hstart
    obtain ⟨afterHead, hheadRun, hheadResult, _hheadValue,
        hheadWord, hheadCoordinate, hheadOne,
        hheadFrame⟩ :=
      equalResult_runs regs input
        (inputRegisters regs).replacement
        (Fintype.card tm.Q) afterStart
        ((inputRegisters regs).index_ne (by decide))
        ((inputRegisters regs).index_ne (by decide))
        hstartFrame
    have hheadCoordinate' :
        afterHead (inputRegisters regs).replacement = coordinate :=
      hheadCoordinate.trans hstartCoordinate'
    have hheadOne' :
        afterHead (inputRegisters regs).one = 1 :=
      hheadOne.trans hstartOne'
    by_cases hhead : coordinate = Fintype.card tm.Q
    · have hheadNonzero :
          afterHead (inputRegisters regs).result ≠ 0 := by
        rw [hheadResult, hstartCoordinate']
        simp [hhead]
      have hrun :
          Runs (sourceBit tm order regs) store afterHead := by
        simpa [sourceBit, startCode] using
          Runs.seq hstartRun
            (Runs.ifZero hstartZero
              (Runs.seq hheadRun
                (Runs.ifNonzero hheadNonzero
                  (Runs.skip afterHead))))
      refine
        ⟨afterHead, hrun, ?_,
          hheadWord.trans hstartWord, hheadOne',
          hheadFrame⟩
      rw [hheadResult, hstartCoordinate']
      simp [coordinateBitValue, coordinateBit, hhead]
    · have hheadZero :
          afterHead (inputRegisters regs).result = 0 := by
        rw [hheadResult, hstartCoordinate']
        simp [hhead]
      have hinputWrites :=
        equalResult_writesWithin_input regs
          (inputRegisters regs).replacement
          (Fintype.card tm.Q)
      have hheadBlockLength :
          afterHead (Layout.blockLength regs) = blockLength := by
        calc
          afterHead (Layout.blockLength regs) =
              afterStart (Layout.blockLength regs) := by
            exact RAM.Structured.Footprint.runs_eq_outside
              hinputWrites hheadRun
              (layoutIndex_not_mem_inputFootprint regs 2 (by decide))
          _ = store (Layout.blockLength regs) := by
            exact RAM.Structured.Footprint.runs_eq_outside
              (equalResult_writesWithin_input regs
                (inputRegisters regs).replacement startCode)
              hstartRun
              (layoutIndex_not_mem_inputFootprint regs 2 (by decide))
          _ = blockLength := hblockLength
      have hheadPacked :
          afterHead (packedTapeBlock regs) =
            tapeBlockCode workTapeCount tape block := by
        calc
          afterHead (packedTapeBlock regs) =
              afterStart (packedTapeBlock regs) := by
            exact RAM.Structured.Footprint.runs_eq_outside
              hinputWrites hheadRun
              (layoutIndex_not_mem_inputFootprint regs 20
                (by decide))
          _ = store (packedTapeBlock regs) := by
            exact RAM.Structured.Footprint.runs_eq_outside
              (equalResult_writesWithin_input regs
                (inputRegisters regs).replacement startCode)
              hstartRun
              (layoutIndex_not_mem_inputFootprint regs 20
                (by decide))
          _ = tapeBlockCode workTapeCount tape block := hpacked
      have hheadInputLength :
          afterHead controller.inputLength = input.length := by
        have hstartTrial :
            RAM.Structured.Footprint.CmdWritesWithin
              regs.footprint
              (equalImmediate regs
                (inputRegisters regs).replacement
                (inputRegisters regs).result startCode) :=
          cmdWritesWithin_mono
            (fun address haddress =>
              writeFootprint_subset_trial_internal regs
                (inputFootprint_subset regs haddress))
            (equalResult_writesWithin_input regs
              (inputRegisters regs).replacement startCode)
        have hheadTrial :
            RAM.Structured.Footprint.CmdWritesWithin
              regs.footprint
              (equalImmediate regs
                (inputRegisters regs).replacement
                (inputRegisters regs).result
                (Fintype.card tm.Q)) :=
          cmdWritesWithin_mono
            (fun address haddress =>
              writeFootprint_subset_trial_internal regs
                (inputFootprint_subset regs haddress))
            hinputWrites
        calc
          afterHead controller.inputLength =
              afterStart controller.inputLength := by
            apply NeighborhoodTrial.Registers.runs_preserves_controller_index
              regs hheadTrial hheadRun
            · decide
            · decide
            · decide
          _ = store controller.inputLength := by
            apply NeighborhoodTrial.Registers.runs_preserves_controller_index
              regs hstartTrial hstartRun
            · decide
            · decide
            · decide
          _ = input.length := hinputLength
      obtain ⟨final, hpayloadRun, hresult,
          hfinalWord, hfinalOne, hfinalFrame⟩ :=
        sourcePayloadBit_runs tm regs input blockLength tape block
          coordinate afterHead htape hheadBlockLength
          hheadPacked hheadCoordinate'
          (hheadWord.trans (hstartWord.trans hword))
          hheadOne' hheadInputLength hheadFrame
      have hrun :
          Runs (sourceBit tm order regs) store final := by
        simpa [sourceBit, startCode] using
          Runs.seq hstartRun
            (Runs.ifZero hstartZero
              (Runs.seq hheadRun
                (Runs.ifZero hheadZero hpayloadRun)))
      refine
        ⟨final, hrun, ?_,
          hfinalWord.trans (hheadWord.trans hstartWord),
          hfinalOne, hfinalFrame⟩
      rw [hresult]
      by_cases hpayload :
          Fintype.card tm.Q + blockLength ≤ coordinate ∧
            coordinate <
              Fintype.card tm.Q + 5 * blockLength
      · by_cases hgamma :
            (coordinate -
                (Fintype.card tm.Q + blockLength)) % 4 =
              initialGammaCode input tape
                (block * blockLength +
                  (coordinate -
                    (Fintype.card tm.Q + blockLength)) / 4)
        · simp [coordinateBitValue, coordinateBit, hstart',
            hhead, hpayload, hgamma]
        · simp [coordinateBitValue, coordinateBit, hstart',
            hhead, hpayload, hgamma]
      · simp [coordinateBitValue, coordinateBit, hstart',
          hhead, hpayload]

private theorem sourceBit_invariantRuns
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (regs : NeighborhoodTrial.Registers controller)
    (input : List Bool) (allowed : Finset ℕ) (bound : ℕ)
    (blockLength tape block coordinate : ℕ) (store : Store)
    (htape : tape < tapeCount workTapeCount)
    (hblockLength :
      store (Layout.blockLength regs) = blockLength)
    (hpacked :
      store (packedTapeBlock regs) =
        tapeBlockCode workTapeCount tape block)
    (hcoordinate :
      store (inputRegisters regs).replacement = coordinate)
    (hword :
      store (inputRegisters regs).word =
        SearchProgram.prefixCacheValue controller input
          (SearchProgram.footprintLimit
            controller regs.footprint))
    (hone : store (inputRegisters regs).one = 1)
    (hinputLength : store controller.inputLength = input.length)
    (hpackedBound :
      tapeBlockCode workTapeCount tape block ≤ bound)
    (htapeCountBound : tapeCount workTapeCount ≤ bound)
    (hstateBound : Fintype.card tm.Q ≤ bound)
    (hfiveBlockBound : 5 * blockLength ≤ bound)
    (hupperBound :
      Fintype.card tm.Q + 5 * blockLength ≤ bound)
    (hlowerBound :
      Fintype.card tm.Q + blockLength ≤ bound)
    (hcoordinateBound : coordinate ≤ bound)
    (hblockProductBound : block * blockLength ≤ bound)
    (haddressBound :
      block * blockLength +
        (coordinate -
          (Fintype.card tm.Q + blockLength)) / 4 ≤ bound)
    (hfiveBound : 5 ≤ bound)
    (hlimitSucc :
      SearchProgram.footprintLimit controller regs.footprint + 1 ≤
        bound)
    (hprefixCapacity :
      2 ^
          SearchProgram.footprintLimit controller regs.footprint ≤
        bound)
    (hstore :
      NeighborhoodProgram.ValuesWithin allowed bound store)
    (hframe :
      SearchProgram.InputFrame
        controller regs.footprint input store) :
    ∃ final steps,
      InvariantRuns
        (NeighborhoodProgram.ValuesWithin allowed bound)
        (sourceBit tm order regs) store final steps ∧
      final (inputRegisters regs).result =
        coordinateBitValue tm order input blockLength tape block
          coordinate ∧
      final (inputRegisters regs).word =
        store (inputRegisters regs).word ∧
      final (inputRegisters regs).one = 1 ∧
      SearchProgram.InputFrame
        controller regs.footprint input final := by
  let startCode := (order.state tm.qstart).val
  have hstartCodeBound : startCode ≤ bound := by
    exact (Nat.le_of_lt (order.state tm.qstart).isLt).trans
      hstateBound
  obtain ⟨afterStart, startSteps, hstartRun, hstartResult,
      _hstartValue, hstartWord, hstartCoordinate, hstartOne,
      hstartFrame⟩ :=
    equalResult_invariantRuns regs input allowed bound
      (inputRegisters regs).replacement startCode store
      ((inputRegisters regs).index_ne (by decide))
      ((inputRegisters regs).index_ne (by decide))
      (by simpa [hcoordinate] using hcoordinateBound)
      hstartCodeBound (by omega) hstore hframe
  have hstartCoordinate' :
      afterStart (inputRegisters regs).replacement = coordinate :=
    hstartCoordinate.trans hcoordinate
  have hstartOne' :
      afterStart (inputRegisters regs).one = 1 :=
    hstartOne.trans hone
  by_cases hstart : coordinate = startCode
  · have hstartNonzero :
        afterStart (inputRegisters regs).result ≠ 0 := by
      rw [hstartResult, hcoordinate]
      simp [hstart]
    have hskip :
        InvariantRuns
          (NeighborhoodProgram.ValuesWithin allowed bound)
          .skip afterStart afterStart 0 :=
      InvariantRuns.skip afterStart
        (InvariantRuns.final hstartRun)
    have hinvariant :
        InvariantRuns
          (NeighborhoodProgram.ValuesWithin allowed bound)
          (sourceBit tm order regs) store afterStart
          (startSteps + 2) := by
      simpa [sourceBit, startCode] using
        InvariantRuns.seq hstartRun
          (InvariantRuns.ifNonzero
            (onZero :=
              Cmd.seq
                (equalImmediate regs
                  (inputRegisters regs).replacement
                  (inputRegisters regs).result
                  (Fintype.card tm.Q))
                (.ifZero (inputRegisters regs).result
                  (sourcePayloadBit tm regs) .skip))
            hstartNonzero hskip)
    obtain ⟨semanticFinal, hsemanticRun, hresult,
        hfinalWord, hfinalOne, hfinalFrame⟩ :=
      sourceBit_runs tm order regs input blockLength tape block
        coordinate store htape hblockLength hpacked hcoordinate
        hword hone hinputLength hframe
    have heq : afterStart = semanticFinal :=
      runs_final_eq (InvariantRuns.toRuns hinvariant) hsemanticRun
    subst semanticFinal
    exact
      ⟨afterStart, startSteps + 2, hinvariant, hresult,
        hfinalWord, hfinalOne, hfinalFrame⟩
  · have hstartZero :
        afterStart (inputRegisters regs).result = 0 := by
      rw [hstartResult, hcoordinate]
      simp [hstart]
    obtain ⟨afterHead, headSteps, hheadRun, hheadResult,
        _hheadValue, hheadWord, hheadCoordinate, hheadOne,
        hheadFrame⟩ :=
      equalResult_invariantRuns regs input allowed bound
        (inputRegisters regs).replacement
        (Fintype.card tm.Q) afterStart
        ((inputRegisters regs).index_ne (by decide))
        ((inputRegisters regs).index_ne (by decide))
        (by simpa [hstartCoordinate'] using hcoordinateBound)
        hstateBound (by omega) (InvariantRuns.final hstartRun)
        hstartFrame
    have hheadCoordinate' :
        afterHead (inputRegisters regs).replacement = coordinate :=
      hheadCoordinate.trans hstartCoordinate'
    by_cases hhead : coordinate = Fintype.card tm.Q
    · have hheadNonzero :
          afterHead (inputRegisters regs).result ≠ 0 := by
        rw [hheadResult, hstartCoordinate']
        simp [hhead]
      have hskip :
          InvariantRuns
            (NeighborhoodProgram.ValuesWithin allowed bound)
            .skip afterHead afterHead 0 :=
        InvariantRuns.skip afterHead
          (InvariantRuns.final hheadRun)
      have hheadBranch :=
        InvariantRuns.seq hheadRun
          (InvariantRuns.ifNonzero
            (onZero := sourcePayloadBit tm regs)
            hheadNonzero hskip)
      have hinvariant :
          InvariantRuns
            (NeighborhoodProgram.ValuesWithin allowed bound)
            (sourceBit tm order regs) store afterHead
            (startSteps + (headSteps + 2) + 1) := by
        simpa [sourceBit, startCode] using
          InvariantRuns.seq hstartRun
            (InvariantRuns.ifZero
              (onNonzero := .skip)
              hstartZero hheadBranch)
      obtain ⟨semanticFinal, hsemanticRun, hresult,
          hfinalWord, hfinalOne, hfinalFrame⟩ :=
        sourceBit_runs tm order regs input blockLength tape block
          coordinate store htape hblockLength hpacked hcoordinate
          hword hone hinputLength hframe
      have heq : afterHead = semanticFinal :=
        runs_final_eq (InvariantRuns.toRuns hinvariant)
          hsemanticRun
      subst semanticFinal
      exact
        ⟨afterHead, startSteps + (headSteps + 2) + 1,
          hinvariant, hresult, hfinalWord, hfinalOne,
          hfinalFrame⟩
    · have hheadZero :
          afterHead (inputRegisters regs).result = 0 := by
        rw [hheadResult, hstartCoordinate']
        simp [hhead]
      have hinputWrites :=
        equalResult_writesWithin_input regs
          (inputRegisters regs).replacement
          (Fintype.card tm.Q)
      have hheadBlockLength :
          afterHead (Layout.blockLength regs) = blockLength := by
        calc
          afterHead (Layout.blockLength regs) =
              afterStart (Layout.blockLength regs) := by
            exact RAM.Structured.Footprint.runs_eq_outside
              hinputWrites (InvariantRuns.toRuns hheadRun)
              (layoutIndex_not_mem_inputFootprint regs 2 (by decide))
          _ = store (Layout.blockLength regs) := by
            exact RAM.Structured.Footprint.runs_eq_outside
              (equalResult_writesWithin_input regs
                (inputRegisters regs).replacement startCode)
              (InvariantRuns.toRuns hstartRun)
              (layoutIndex_not_mem_inputFootprint regs 2 (by decide))
          _ = blockLength := hblockLength
      have hheadPacked :
          afterHead (packedTapeBlock regs) =
            tapeBlockCode workTapeCount tape block := by
        calc
          afterHead (packedTapeBlock regs) =
              afterStart (packedTapeBlock regs) := by
            exact RAM.Structured.Footprint.runs_eq_outside
              hinputWrites (InvariantRuns.toRuns hheadRun)
              (layoutIndex_not_mem_inputFootprint regs 20
                (by decide))
          _ = store (packedTapeBlock regs) := by
            exact RAM.Structured.Footprint.runs_eq_outside
              (equalResult_writesWithin_input regs
                (inputRegisters regs).replacement startCode)
              (InvariantRuns.toRuns hstartRun)
              (layoutIndex_not_mem_inputFootprint regs 20
                (by decide))
          _ = tapeBlockCode workTapeCount tape block := hpacked
      have hheadInputLength :
          afterHead controller.inputLength = input.length := by
        have hstartTrial :
            RAM.Structured.Footprint.CmdWritesWithin
              regs.footprint
              (equalImmediate regs
                (inputRegisters regs).replacement
                (inputRegisters regs).result startCode) :=
          cmdWritesWithin_mono
            (fun address haddress =>
              writeFootprint_subset_trial_internal regs
                (inputFootprint_subset regs haddress))
            (equalResult_writesWithin_input regs
              (inputRegisters regs).replacement startCode)
        have hheadTrial :
            RAM.Structured.Footprint.CmdWritesWithin
              regs.footprint
              (equalImmediate regs
                (inputRegisters regs).replacement
                (inputRegisters regs).result
                (Fintype.card tm.Q)) :=
          cmdWritesWithin_mono
            (fun address haddress =>
              writeFootprint_subset_trial_internal regs
                (inputFootprint_subset regs haddress))
            hinputWrites
        calc
          afterHead controller.inputLength =
              afterStart controller.inputLength := by
            apply NeighborhoodTrial.Registers.runs_preserves_controller_index
              regs hheadTrial (InvariantRuns.toRuns hheadRun)
            · decide
            · decide
            · decide
          _ = store controller.inputLength := by
            apply NeighborhoodTrial.Registers.runs_preserves_controller_index
              regs hstartTrial (InvariantRuns.toRuns hstartRun)
            · decide
            · decide
            · decide
          _ = input.length := hinputLength
      obtain ⟨final, payloadSteps, hpayloadRun, _hresult,
          _hfinalWord, _hfinalOne, _hfinalFrame⟩ :=
        sourcePayloadBit_invariantRuns tm regs input allowed bound
          blockLength tape block coordinate afterHead htape
          hheadBlockLength hheadPacked hheadCoordinate'
          (hheadWord.trans (hstartWord.trans hword))
          (hheadOne.trans (hstartOne.trans hone))
          hheadInputLength hpackedBound htapeCountBound
          hstateBound hfiveBlockBound hupperBound hlowerBound
          hcoordinateBound hblockProductBound haddressBound
          hfiveBound hlimitSucc hprefixCapacity
          (InvariantRuns.final hheadRun) hheadFrame
      have hheadBranch :=
        InvariantRuns.seq hheadRun
          (InvariantRuns.ifZero
            (onNonzero := .skip)
            hheadZero hpayloadRun)
      have hinvariant :
          InvariantRuns
            (NeighborhoodProgram.ValuesWithin allowed bound)
            (sourceBit tm order regs) store final
            (startSteps +
              (headSteps + (payloadSteps + 1)) + 1) := by
        simpa [sourceBit, startCode] using
          InvariantRuns.seq hstartRun
            (InvariantRuns.ifZero
              (onNonzero := .skip)
              hstartZero hheadBranch)
      obtain ⟨semanticFinal, hsemanticRun, hresult,
          hfinalWord, hfinalOne, hfinalFrame⟩ :=
        sourceBit_runs tm order regs input blockLength tape block
          coordinate store htape hblockLength hpacked hcoordinate
          hword hone hinputLength hframe
      have heq : final = semanticFinal :=
        runs_final_eq (InvariantRuns.toRuns hinvariant)
          hsemanticRun
      subst semanticFinal
      exact
        ⟨final,
          startSteps + (headSteps + (payloadSteps + 1)) + 1,
          hinvariant, hresult, hfinalWord, hfinalOne,
          hfinalFrame⟩

private theorem sourceBit_writesWithin_input
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (regs : NeighborhoodTrial.Registers controller) :
    RAM.Structured.Footprint.CmdWritesWithin
      (inputRegisters regs).footprint
      (sourceBit tm order regs) := by
  have hlookup :
      RAM.Structured.Footprint.CmdWritesWithin
        (inputRegisters regs).footprint (lookupInput regs) :=
    InputLookup.sourceWritesWithin _ _
  have hpeek :
      RAM.Structured.Footprint.CmdWritesWithin
        (inputRegisters regs).footprint
        (NeighborhoodProgram.peek
          (inputRegisters regs).bufferStack) :=
    cmdWritesWithin_mono
      (bufferStack_footprint_subset regs)
      (peek_sourceWritesWithin _)
  have hpop :
      RAM.Structured.Footprint.CmdWritesWithin
        (inputRegisters regs).footprint
        (NeighborhoodProgram.pop
          (inputRegisters regs).bufferStack) :=
    cmdWritesWithin_mono
      (bufferStack_footprint_subset regs)
      (pop_sourceWritesWithin _)
  simp [sourceBit, sourcePayloadBit, sourceUpperBit,
    sourceCellBit, cellBit, prepareCellBit, initialCellBit,
    inputCellBit, blankCellBit, startCellBit,
    equalImmediate, decodeTapeBlock, copy, Cmd.seqList,
    RAM.Structured.Footprint.CmdWritesWithin,
    RAM.Structured.Footprint.BasicWritesWithin,
    (inputRegisters regs).index_mem_footprint,
    hlookup, hpeek, hpop]

private theorem sourceChunkBody_writesWithin_local
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (regs : NeighborhoodTrial.Registers controller) :
    RAM.Structured.Footprint.CmdWritesWithin
      (writeFootprint regs) (sourceChunkBody tm order regs) := by
  have hinput :
      (inputRegisters regs).footprint ⊆ writeFootprint regs :=
    inputFootprint_subset regs
  have hsource :
      RAM.Structured.Footprint.CmdWritesWithin
        (writeFootprint regs) (sourceBit tm order regs) :=
    cmdWritesWithin_mono hinput
      (sourceBit_writesWithin_input tm order regs)
  have hdecode :
      RAM.Structured.Footprint.CmdWritesWithin
        (writeFootprint regs)
        (decodeTapeBlock workTapeCount regs) :=
    cmdWritesWithin_mono hinput
      (decodeTapeBlock_writesWithin_local workTapeCount regs)
  have hoperand := writeMap_mem regs (12 : Fin 16)
  have hremaining := writeMap_mem regs (15 : Fin 16)
  change operand regs ∈ writeFootprint regs at hoperand
  change remaining regs ∈ writeFootprint regs at hremaining
  simp [sourceChunkBody, Cmd.seqList,
    RAM.Structured.Footprint.CmdWritesWithin,
    RAM.Structured.Footprint.BasicWritesWithin,
    hsource, hdecode, inputIndex_mem_writeFootprint,
    hoperand, hremaining]

private theorem layoutIndex_ne_inputIndex
    (regs : NeighborhoodTrial.Registers controller)
    (slot : Fin 34) (inputSlot : Fin 12)
    (hne : slot ≠ inputMap inputSlot) :
    regs.index slot ≠ (inputRegisters regs).index inputSlot :=
  regs.injective.ne hne

private theorem sourceChunkBody_runs
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (regs : NeighborhoodTrial.Registers controller)
    (input : List Bool)
    (blockLength tape block chunk chunkBits remainingBits
      accumulator : ℕ)
    (store : Store)
    (htape : tape < tapeCount workTapeCount)
    (hblockLength :
      store (Layout.blockLength regs) = blockLength)
    (hpacked :
      store (packedTapeBlock regs) =
        tapeBlockCode workTapeCount tape block)
    (hcursor :
      store (Layout.codecScratch regs) = chunk)
    (hchunkBits :
      store (recoveredChunkBits regs) = chunkBits)
    (hremaining :
      store (remaining regs) = remainingBits + 1)
    (hoperand :
      store (operand regs) = accumulator)
    (hword :
      store (inputRegisters regs).word =
        SearchProgram.prefixCacheValue controller input
          (SearchProgram.footprintLimit
            controller regs.footprint))
    (hinputLength : store controller.inputLength = input.length)
    (hframe :
      SearchProgram.InputFrame
        controller regs.footprint input store) :
    ∃ final,
      Runs (sourceChunkBody tm order regs) store final ∧
      final (remaining regs) = remainingBits ∧
      final (operand regs) =
        2 * accumulator +
          coordinateBitValue tm order input blockLength tape block
            (chunk * chunkBits + chunkBits -
              (remainingBits + 1)) ∧
      final (packedTapeBlock regs) =
        tapeBlockCode workTapeCount tape block ∧
      final (recoveredChunkBits regs) = chunkBits ∧
      final (Layout.codecScratch regs) = chunk ∧
      final (Layout.blockLength regs) = blockLength ∧
      final (inputRegisters regs).word =
        SearchProgram.prefixCacheValue controller input
          (SearchProgram.footprintLimit
            controller regs.footprint) ∧
      final (inputRegisters regs).one = 1 ∧
      final controller.inputLength = input.length ∧
      SearchProgram.InputFrame
        controller regs.footprint input final := by
  obtain ⟨decoded, hdecodeRun, _hdecodedTape,
      _hdecodedBlock, hdecodedOne, _hdecodedReplacement,
      hdecodedWord, hdecodeOutside⟩ :=
    decodeTapeBlock_runs workTapeCount regs store tape block
      htape hpacked
  let afterMul :=
    Basic.exec
      (.mul (inputRegisters regs).replacement
        (Layout.codecScratch regs) (recoveredChunkBits regs))
      decoded
  let afterAdd :=
    Basic.exec
      (.add (inputRegisters regs).replacement
        (inputRegisters regs).replacement
        (recoveredChunkBits regs))
      afterMul
  let ready :=
    Basic.exec
      (.sub (inputRegisters regs).replacement
        (inputRegisters regs).replacement (remaining regs))
      afterAdd
  have hdecodedCursor :
      decoded (Layout.codecScratch regs) = chunk := by
    rw [hdecodeOutside]
    · exact hcursor
    · exact layoutIndex_not_mem_inputFootprint regs 31 (by decide)
  have hdecodedChunkBits :
      decoded (recoveredChunkBits regs) = chunkBits := by
    rw [hdecodeOutside]
    · exact hchunkBits
    · exact layoutIndex_not_mem_inputFootprint regs 21 (by decide)
  have hdecodedRemaining :
      decoded (remaining regs) = remainingBits + 1 := by
    rw [hdecodeOutside]
    · exact hremaining
    · exact layoutIndex_not_mem_inputFootprint regs 30 (by decide)
  have hdecodedOperand :
      decoded (operand regs) = accumulator := by
    rw [hdecodeOutside]
    · exact hoperand
    · exact layoutIndex_not_mem_inputFootprint regs 19 (by decide)
  have hdecodedPacked :
      decoded (packedTapeBlock regs) =
        tapeBlockCode workTapeCount tape block := by
    rw [hdecodeOutside]
    · exact hpacked
    · exact layoutIndex_not_mem_inputFootprint regs 20 (by decide)
  have hdecodedBlockLength :
      decoded (Layout.blockLength regs) = blockLength := by
    rw [hdecodeOutside]
    · exact hblockLength
    · exact layoutIndex_not_mem_inputFootprint regs 2 (by decide)
  have hreadyCoordinate :
      ready (inputRegisters regs).replacement =
        chunk * chunkBits + chunkBits -
          (remainingBits + 1) := by
    have hchunkReplacement :
        recoveredChunkBits regs ≠
          (inputRegisters regs).replacement :=
      layoutIndex_ne_inputIndex regs 21 11 (by decide)
    have hremainingReplacement :
        remaining regs ≠
          (inputRegisters regs).replacement :=
      layoutIndex_ne_inputIndex regs 30 11 (by decide)
    simp [ready, afterAdd, afterMul, Basic.exec,
      hchunkReplacement, hremainingReplacement, hdecodedCursor,
      hdecodedChunkBits, hdecodedRemaining]
  have hprefixRun :
      Runs
        (Cmd.seqList
          [decodeTapeBlock workTapeCount regs,
            .basic
              (.mul (inputRegisters regs).replacement
                (Layout.codecScratch regs)
                (recoveredChunkBits regs)),
            .basic
              (.add (inputRegisters regs).replacement
                (inputRegisters regs).replacement
                (recoveredChunkBits regs)),
            .basic
              (.sub (inputRegisters regs).replacement
                (inputRegisters regs).replacement
                (remaining regs))])
        store ready := by
    simpa [Cmd.seqList, afterMul, afterAdd, ready] using
      Runs.seq hdecodeRun
        (Runs.seq
          (Runs.basic
            (.mul (inputRegisters regs).replacement
              (Layout.codecScratch regs)
              (recoveredChunkBits regs))
            decoded)
          (Runs.seq
            (Runs.basic
              (.add (inputRegisters regs).replacement
                (inputRegisters regs).replacement
                (recoveredChunkBits regs))
              afterMul)
            (Runs.basic
              (.sub (inputRegisters regs).replacement
                (inputRegisters regs).replacement
                (remaining regs))
              afterAdd)))
  have hprefixWrites :
      RAM.Structured.Footprint.CmdWritesWithin
        regs.footprint
        (Cmd.seqList
          [decodeTapeBlock workTapeCount regs,
            .basic
              (.mul (inputRegisters regs).replacement
                (Layout.codecScratch regs)
                (recoveredChunkBits regs)),
            .basic
              (.add (inputRegisters regs).replacement
                (inputRegisters regs).replacement
                (recoveredChunkBits regs)),
            .basic
              (.sub (inputRegisters regs).replacement
                (inputRegisters regs).replacement
                (remaining regs))]) := by
    have hdecodeTrial :
        RAM.Structured.Footprint.CmdWritesWithin
          regs.footprint
          (decodeTapeBlock workTapeCount regs) :=
      cmdWritesWithin_mono
        (fun address haddress =>
          writeFootprint_subset_trial_internal regs
            (inputFootprint_subset regs haddress))
        (decodeTapeBlock_writesWithin_local workTapeCount regs)
    simp [Cmd.seqList,
      RAM.Structured.Footprint.CmdWritesWithin,
      RAM.Structured.Footprint.BasicWritesWithin,
      hdecodeTrial,
      writeFootprint_subset_trial_internal regs
        (inputIndex_mem_writeFootprint regs 11)]
  have hreadyFrame :
      SearchProgram.InputFrame
        controller regs.footprint input ready :=
    NeighborhoodTrial.Registers.runs_preserves_inputFrame
      regs hprefixWrites hprefixRun hframe
  have hreadyInputLength :
      ready controller.inputLength = input.length := by
    calc
      ready controller.inputLength =
          store controller.inputLength := by
        apply NeighborhoodTrial.Registers.runs_preserves_controller_index
          regs hprefixWrites hprefixRun
        · decide
        · decide
        · decide
      _ = input.length := hinputLength
  have hreadyBlockLength :
      ready (Layout.blockLength regs) = blockLength := by
    have hblockReplacement :
        Layout.blockLength regs ≠
          (inputRegisters regs).replacement :=
      layoutIndex_ne_inputIndex regs 2 11 (by decide)
    simp [ready, afterAdd, afterMul, Basic.exec,
      hblockReplacement, hdecodedBlockLength]
  have hreadyPacked :
      ready (packedTapeBlock regs) =
        tapeBlockCode workTapeCount tape block := by
    have hpackedReplacement :
        packedTapeBlock regs ≠
          (inputRegisters regs).replacement :=
      layoutIndex_ne_inputIndex regs 20 11 (by decide)
    simp [ready, afterAdd, afterMul, Basic.exec,
      hpackedReplacement, hdecodedPacked]
  have hreadyWord :
      ready (inputRegisters regs).word =
        SearchProgram.prefixCacheValue controller input
          (SearchProgram.footprintLimit
            controller regs.footprint) := by
    simp [ready, afterAdd, afterMul, Basic.exec,
      (inputRegisters regs).index_ne
        (by decide : (0 : Fin 12) ≠ 11),
      hdecodedWord, hword]
  obtain ⟨afterSource, hsourceRun, hsourceResult,
      hsourceWord, hsourceOne, hsourceFrame⟩ :=
    sourceBit_runs tm order regs input blockLength tape block
      (chunk * chunkBits + chunkBits - (remainingBits + 1))
      ready htape hreadyBlockLength hreadyPacked hreadyCoordinate
      hreadyWord (by
        have hreadyOne :
            ready (inputRegisters regs).one = 1 := by
          simp [ready, afterAdd, afterMul, Basic.exec,
            (inputRegisters regs).index_ne
              (by decide : (6 : Fin 12) ≠ 11)]
          exact hdecodedOne
        exact hreadyOne)
      hreadyInputLength hreadyFrame
  have hsourceWrites :=
    sourceBit_writesWithin_input tm order regs
  have hsourceOutside :
      ∀ slot : Fin 34,
        (∀ index, inputMap index ≠ slot) →
        afterSource (regs.index slot) = ready (regs.index slot) := by
    intro slot hslot
    exact RAM.Structured.Footprint.runs_eq_outside
      hsourceWrites hsourceRun
      (layoutIndex_not_mem_inputFootprint regs slot hslot)
  have hsourceInputLength :
      afterSource controller.inputLength = input.length := by
    have htrial :
        RAM.Structured.Footprint.CmdWritesWithin
          regs.footprint (sourceBit tm order regs) :=
      cmdWritesWithin_mono
        (fun address haddress =>
          writeFootprint_subset_trial_internal regs
            (inputFootprint_subset regs haddress))
        hsourceWrites
    calc
      afterSource controller.inputLength =
          ready controller.inputLength := by
        apply NeighborhoodTrial.Registers.runs_preserves_controller_index
          regs htrial hsourceRun
        · decide
        · decide
        · decide
      _ = input.length := hreadyInputLength
  let afterBase :=
    Basic.exec (.imm (inputRegisters regs).base 2) afterSource
  let afterScale :=
    Basic.exec
      (.mul (operand regs) (operand regs)
        (inputRegisters regs).base)
      afterBase
  let afterAccumulate :=
    Basic.exec
      (.add (operand regs) (inputRegisters regs).result
        (operand regs))
      afterScale
  let final :=
    Basic.exec
      (.sub (remaining regs) (remaining regs)
        (inputRegisters regs).one)
      afterAccumulate
  have htailRun :
      Runs
        (Cmd.seqList
          [.basic (.imm (inputRegisters regs).base 2),
            .basic
              (.mul (operand regs) (operand regs)
                (inputRegisters regs).base),
            .basic
              (.add (operand regs)
                (inputRegisters regs).result (operand regs)),
            .basic
              (.sub (remaining regs) (remaining regs)
                (inputRegisters regs).one)])
        afterSource final := by
    simpa [Cmd.seqList, afterBase, afterScale,
      afterAccumulate, final] using
      Runs.seq
        (Runs.basic
          (.imm (inputRegisters regs).base 2) afterSource)
        (Runs.seq
          (Runs.basic
            (.mul (operand regs) (operand regs)
              (inputRegisters regs).base)
            afterBase)
          (Runs.seq
            (Runs.basic
              (.add (operand regs)
                (inputRegisters regs).result (operand regs))
              afterScale)
            (Runs.basic
              (.sub (remaining regs) (remaining regs)
                (inputRegisters regs).one)
              afterAccumulate)))
  have hrun :
      Runs (sourceChunkBody tm order regs) store final := by
    simpa [sourceChunkBody, Cmd.seqList, afterMul, afterAdd,
      ready] using
      Runs.seq hdecodeRun
        (Runs.seq
          (Runs.basic
            (.mul (inputRegisters regs).replacement
              (Layout.codecScratch regs)
              (recoveredChunkBits regs))
            decoded)
          (Runs.seq
            (Runs.basic
              (.add (inputRegisters regs).replacement
                (inputRegisters regs).replacement
                (recoveredChunkBits regs))
              afterMul)
            (Runs.seq
              (Runs.basic
                (.sub (inputRegisters regs).replacement
                  (inputRegisters regs).replacement
                  (remaining regs))
                afterAdd)
              (Runs.seq hsourceRun htailRun))))
  have hsourceOperand :
      afterSource (operand regs) = accumulator := by
    calc
      afterSource (operand regs) =
          ready (operand regs) :=
        hsourceOutside 19 (by decide)
      _ = decoded (operand regs) := by
        have hoperandReplacement :
            operand regs ≠
              (inputRegisters regs).replacement :=
          layoutIndex_ne_inputIndex regs 19 11 (by decide)
        simp [ready, afterAdd, afterMul, Basic.exec,
          hoperandReplacement]
      _ = accumulator := hdecodedOperand
  have hsourceRemaining :
      afterSource (remaining regs) = remainingBits + 1 := by
    calc
      afterSource (remaining regs) =
          ready (remaining regs) :=
        hsourceOutside 30 (by decide)
      _ = decoded (remaining regs) := by
        have hremainingReplacement :
            remaining regs ≠
              (inputRegisters regs).replacement :=
          layoutIndex_ne_inputIndex regs 30 11 (by decide)
        simp [ready, afterAdd, afterMul, Basic.exec,
          hremainingReplacement]
      _ = remainingBits + 1 := hdecodedRemaining
  have hopBase :
      operand regs ≠ (inputRegisters regs).base :=
    layoutIndex_ne_inputIndex regs 19 2 (by decide)
  have hopResult :
      operand regs ≠ (inputRegisters regs).result :=
    layoutIndex_ne_inputIndex regs 19 10 (by decide)
  have hresultBase :
      (inputRegisters regs).result ≠
        (inputRegisters regs).base :=
    (inputRegisters regs).index_ne (by decide)
  have hremainingBase :
      remaining regs ≠ (inputRegisters regs).base :=
    layoutIndex_ne_inputIndex regs 30 2 (by decide)
  have hremainingResult :
      remaining regs ≠ (inputRegisters regs).result :=
    layoutIndex_ne_inputIndex regs 30 10 (by decide)
  have hremainingOperand :
      remaining regs ≠ operand regs :=
    regs.injective.ne (by decide)
  have hremainingOne :
      remaining regs ≠ (inputRegisters regs).one :=
    layoutIndex_ne_inputIndex regs 30 6 (by decide)
  have honeBase :
      (inputRegisters regs).one ≠
        (inputRegisters regs).base :=
    (inputRegisters regs).index_ne (by decide)
  have honeOperand :
      (inputRegisters regs).one ≠ operand regs :=
    (layoutIndex_ne_inputIndex regs 19 6 (by decide)).symm
  have hfinalOperand :
      final (operand regs) =
        2 * accumulator +
          coordinateBitValue tm order input blockLength tape block
            (chunk * chunkBits + chunkBits -
              (remainingBits + 1)) := by
    simp [final, afterAccumulate, afterScale, afterBase,
      Basic.exec, hremainingOperand.symm, hopResult.symm,
      hopBase, hresultBase, hsourceOperand, hsourceResult]
    omega
  have hfinalRemaining :
      final (remaining regs) = remainingBits := by
    simp [final, afterAccumulate, afterScale, afterBase,
      Basic.exec, hremainingBase, hremainingOperand,
      honeBase, honeOperand, hsourceRemaining, hsourceOne]
  have hfinalFrame :
      SearchProgram.InputFrame
        controller regs.footprint input final :=
    NeighborhoodTrial.Registers.runs_preserves_inputFrame
      regs
      (cmdWritesWithin_mono
        (writeFootprint_subset_trial_internal regs)
        (sourceChunkBody_writesWithin_local tm order regs))
      hrun hframe
  refine
    ⟨final, hrun, hfinalRemaining, hfinalOperand,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfinalFrame⟩
  · have hpackedBase :
        packedTapeBlock regs ≠ (inputRegisters regs).base :=
      layoutIndex_ne_inputIndex regs 20 2 (by decide)
    have hpackedOperand :
        packedTapeBlock regs ≠ operand regs :=
      regs.injective.ne (by decide)
    have hpackedRemaining :
        packedTapeBlock regs ≠ remaining regs :=
      regs.injective.ne (by decide)
    simp [final, afterAccumulate, afterScale, afterBase,
      Basic.exec, hpackedBase, hpackedOperand, hpackedRemaining,
      hsourceOutside 20 (by decide), hreadyPacked]
  · have hchunkBase :
        recoveredChunkBits regs ≠ (inputRegisters regs).base :=
      layoutIndex_ne_inputIndex regs 21 2 (by decide)
    have hchunkOperand :
        recoveredChunkBits regs ≠ operand regs :=
      regs.injective.ne (by decide)
    have hchunkRemaining :
        recoveredChunkBits regs ≠ remaining regs :=
      regs.injective.ne (by decide)
    have hreadyChunkBits :
        ready (recoveredChunkBits regs) = chunkBits := by
      have hchunkReplacement :
          recoveredChunkBits regs ≠
            (inputRegisters regs).replacement :=
        layoutIndex_ne_inputIndex regs 21 11 (by decide)
      simp [ready, afterAdd, afterMul, Basic.exec,
        hchunkReplacement, hdecodedChunkBits]
    simp [final, afterAccumulate, afterScale, afterBase,
      Basic.exec, hchunkBase, hchunkOperand, hchunkRemaining,
      hsourceOutside 21 (by decide), hreadyChunkBits]
  · have hcursorBase :
        Layout.codecScratch regs ≠ (inputRegisters regs).base :=
      layoutIndex_ne_inputIndex regs 31 2 (by decide)
    have hcursorOperand :
        Layout.codecScratch regs ≠ operand regs :=
      regs.injective.ne (by decide)
    have hcursorRemaining :
        Layout.codecScratch regs ≠ remaining regs :=
      regs.injective.ne (by decide)
    have hreadyCursor :
        ready (Layout.codecScratch regs) = chunk := by
      have hcursorReplacement :
          Layout.codecScratch regs ≠
            (inputRegisters regs).replacement :=
        layoutIndex_ne_inputIndex regs 31 11 (by decide)
      simp [ready, afterAdd, afterMul, Basic.exec,
        hcursorReplacement, hdecodedCursor]
    simp [final, afterAccumulate, afterScale, afterBase,
      Basic.exec, hcursorBase, hcursorOperand, hcursorRemaining,
      hsourceOutside 31 (by decide), hreadyCursor]
  · have hblockBase :
        Layout.blockLength regs ≠ (inputRegisters regs).base :=
      layoutIndex_ne_inputIndex regs 2 2 (by decide)
    have hblockOperand :
        Layout.blockLength regs ≠ operand regs :=
      regs.injective.ne (by decide)
    have hblockRemaining :
        Layout.blockLength regs ≠ remaining regs :=
      regs.injective.ne (by decide)
    simp [final, afterAccumulate, afterScale, afterBase,
      Basic.exec, hblockBase, hblockOperand, hblockRemaining,
      hsourceOutside 2 (by decide), hreadyBlockLength]
  · have hwordBase :
        (inputRegisters regs).word ≠
          (inputRegisters regs).base :=
      (inputRegisters regs).index_ne (by decide)
    have hwordOperand :
        (inputRegisters regs).word ≠ operand regs :=
      (layoutIndex_ne_inputIndex regs 19 0 (by decide)).symm
    have hwordRemaining :
        (inputRegisters regs).word ≠ remaining regs :=
      (layoutIndex_ne_inputIndex regs 30 0 (by decide)).symm
    simp [final, afterAccumulate, afterScale, afterBase,
      Basic.exec, hwordBase, hwordOperand, hwordRemaining,
      hsourceWord, hreadyWord]
  · have honeBase' :
        (inputRegisters regs).one ≠
          (inputRegisters regs).base :=
      honeBase
    simp [final, afterAccumulate, afterScale, afterBase,
      Basic.exec, honeBase', honeOperand,
      hremainingOne.symm, hsourceOne]
  · have htailWrites :
        RAM.Structured.Footprint.CmdWritesWithin
          regs.footprint
          (Cmd.seqList
            [.basic (.imm (inputRegisters regs).base 2),
              .basic
                (.mul (operand regs) (operand regs)
                  (inputRegisters regs).base),
              .basic
                (.add (operand regs)
                  (inputRegisters regs).result (operand regs)),
              .basic
                (.sub (remaining regs) (remaining regs)
                  (inputRegisters regs).one)]) := by
      have hoperand := writeMap_mem regs (12 : Fin 16)
      have hremaining := writeMap_mem regs (15 : Fin 16)
      change operand regs ∈ writeFootprint regs at hoperand
      change remaining regs ∈ writeFootprint regs at hremaining
      exact cmdWritesWithin_mono
        (writeFootprint_subset_trial_internal regs)
        (by
          simp [Cmd.seqList,
            RAM.Structured.Footprint.CmdWritesWithin,
            RAM.Structured.Footprint.BasicWritesWithin,
            inputIndex_mem_writeFootprint,
            hoperand, hremaining])
    calc
      final controller.inputLength =
          afterSource controller.inputLength := by
        apply NeighborhoodTrial.Registers.runs_preserves_controller_index
          regs htailWrites htailRun
        · decide
        · decide
        · decide
      _ = input.length := hsourceInputLength

private theorem sourceChunkBody_invariantRuns
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (regs : NeighborhoodTrial.Registers controller)
    (input : List Bool) (allowed : Finset ℕ) (bound : ℕ)
    (blockLength tape block chunk chunkBits remainingBits
      accumulator : ℕ)
    (store : Store)
    (htape : tape < tapeCount workTapeCount)
    (hblockLength :
      store (Layout.blockLength regs) = blockLength)
    (hpacked :
      store (packedTapeBlock regs) =
        tapeBlockCode workTapeCount tape block)
    (hcursor :
      store (Layout.codecScratch regs) = chunk)
    (hchunkBits :
      store (recoveredChunkBits regs) = chunkBits)
    (hremaining :
      store (remaining regs) = remainingBits + 1)
    (hoperand :
      store (operand regs) = accumulator)
    (hword :
      store (inputRegisters regs).word =
        SearchProgram.prefixCacheValue controller input
          (SearchProgram.footprintLimit
            controller regs.footprint))
    (hinputLength : store controller.inputLength = input.length)
    (hpackedBound :
      tapeBlockCode workTapeCount tape block ≤ bound)
    (htapeCountBound : tapeCount workTapeCount ≤ bound)
    (hstateBound : Fintype.card tm.Q ≤ bound)
    (hfiveBlockBound : 5 * blockLength ≤ bound)
    (hupperBound :
      Fintype.card tm.Q + 5 * blockLength ≤ bound)
    (hlowerBound :
      Fintype.card tm.Q + blockLength ≤ bound)
    (hchunkProductBound : chunk * chunkBits ≤ bound)
    (hchunkCoordinateBound :
      chunk * chunkBits + chunkBits ≤ bound)
    (hcoordinateBound :
      chunk * chunkBits + chunkBits -
          (remainingBits + 1) ≤
        bound)
    (hblockProductBound : block * blockLength ≤ bound)
    (haddressBound :
      block * blockLength +
        (chunk * chunkBits + chunkBits -
            (remainingBits + 1) -
          (Fintype.card tm.Q + blockLength)) / 4 ≤
        bound)
    (haccumulatorDoubleBound : 2 * accumulator ≤ bound)
    (haccumulatorNextBound : 2 * accumulator + 1 ≤ bound)
    (hremainingBound : remainingBits + 1 ≤ bound)
    (hfiveBound : 5 ≤ bound)
    (hlimitSucc :
      SearchProgram.footprintLimit controller regs.footprint + 1 ≤
        bound)
    (hprefixCapacity :
      2 ^
          SearchProgram.footprintLimit controller regs.footprint ≤
        bound)
    (hstore :
      NeighborhoodProgram.ValuesWithin allowed bound store)
    (hframe :
      SearchProgram.InputFrame
        controller regs.footprint input store) :
    ∃ final steps,
      InvariantRuns
        (NeighborhoodProgram.ValuesWithin allowed bound)
        (sourceChunkBody tm order regs) store final steps ∧
      final (remaining regs) = remainingBits ∧
      final (operand regs) =
        2 * accumulator +
          coordinateBitValue tm order input blockLength tape block
            (chunk * chunkBits + chunkBits -
              (remainingBits + 1)) ∧
      final (packedTapeBlock regs) =
        tapeBlockCode workTapeCount tape block ∧
      final (recoveredChunkBits regs) = chunkBits ∧
      final (Layout.codecScratch regs) = chunk ∧
      final (Layout.blockLength regs) = blockLength ∧
      final (inputRegisters regs).word =
        SearchProgram.prefixCacheValue controller input
          (SearchProgram.footprintLimit
            controller regs.footprint) ∧
      final (inputRegisters regs).one = 1 ∧
      final controller.inputLength = input.length ∧
      SearchProgram.InputFrame
        controller regs.footprint input final := by
  obtain ⟨decoded, decodeSteps, hdecodeRun, _hdecodedTape,
      _hdecodedBlock, hdecodedOne, _hdecodedReplacement,
      hdecodedWord, hdecodeOutside⟩ :=
    decodeTapeBlock_invariantRuns workTapeCount regs allowed bound
      store tape block htape hpacked hpackedBound
      htapeCountBound hstore
  have hdecodedCursor :
      decoded (Layout.codecScratch regs) = chunk := by
    rw [hdecodeOutside]
    · exact hcursor
    · exact layoutIndex_not_mem_inputFootprint regs 31 (by decide)
  have hdecodedChunkBits :
      decoded (recoveredChunkBits regs) = chunkBits := by
    rw [hdecodeOutside]
    · exact hchunkBits
    · exact layoutIndex_not_mem_inputFootprint regs 21 (by decide)
  have hdecodedRemaining :
      decoded (remaining regs) = remainingBits + 1 := by
    rw [hdecodeOutside]
    · exact hremaining
    · exact layoutIndex_not_mem_inputFootprint regs 30 (by decide)
  have hdecodedBlockLength :
      decoded (Layout.blockLength regs) = blockLength := by
    rw [hdecodeOutside]
    · exact hblockLength
    · exact layoutIndex_not_mem_inputFootprint regs 2 (by decide)
  let afterMul :=
    Basic.exec
      (.mul (inputRegisters regs).replacement
        (Layout.codecScratch regs) (recoveredChunkBits regs))
      decoded
  have hafterMul :
      NeighborhoodProgram.ValuesWithin allowed bound afterMul := by
    apply valuesWithin_update allowed bound
      (inputRegisters regs).replacement
      (decoded (Layout.codecScratch regs) *
        decoded (recoveredChunkBits regs))
      decoded (InvariantRuns.final hdecodeRun)
    simpa [hdecodedCursor, hdecodedChunkBits] using
      hchunkProductBound
  let afterAdd :=
    Basic.exec
      (.add (inputRegisters regs).replacement
        (inputRegisters regs).replacement
        (recoveredChunkBits regs))
      afterMul
  have hchunkReplacement :
      recoveredChunkBits regs ≠
        (inputRegisters regs).replacement :=
    layoutIndex_ne_inputIndex regs 21 11 (by decide)
  have hafterAdd :
      NeighborhoodProgram.ValuesWithin allowed bound afterAdd := by
    apply valuesWithin_update allowed bound
      (inputRegisters regs).replacement
      (afterMul (inputRegisters regs).replacement +
        afterMul (recoveredChunkBits regs))
      afterMul hafterMul
    simpa [afterMul, Basic.exec, hchunkReplacement,
      hdecodedCursor, hdecodedChunkBits] using
      hchunkCoordinateBound
  let ready :=
    Basic.exec
      (.sub (inputRegisters regs).replacement
        (inputRegisters regs).replacement (remaining regs))
      afterAdd
  have hready :
      NeighborhoodProgram.ValuesWithin allowed bound ready := by
    apply valuesWithin_update allowed bound
      (inputRegisters regs).replacement
      (afterAdd (inputRegisters regs).replacement -
        afterAdd (remaining regs))
      afterAdd hafterAdd
    exact (Nat.sub_le _ _).trans
      (by
        have hadd :
            afterAdd (inputRegisters regs).replacement =
              chunk * chunkBits + chunkBits := by
          simp [afterAdd, afterMul, Basic.exec,
            hchunkReplacement, hdecodedCursor,
            hdecodedChunkBits]
        simpa [hadd] using hchunkCoordinateBound)
  have hremainingReplacement :
      remaining regs ≠
        (inputRegisters regs).replacement :=
    layoutIndex_ne_inputIndex regs 30 11 (by decide)
  have hreadyCoordinate :
      ready (inputRegisters regs).replacement =
        chunk * chunkBits + chunkBits -
          (remainingBits + 1) := by
    simp [ready, afterAdd, afterMul, Basic.exec,
      hchunkReplacement, hremainingReplacement, hdecodedCursor,
      hdecodedChunkBits, hdecodedRemaining]
  have hprefixRun :
      InvariantRuns
        (NeighborhoodProgram.ValuesWithin allowed bound)
        (Cmd.seqList
          [decodeTapeBlock workTapeCount regs,
            .basic
              (.mul (inputRegisters regs).replacement
                (Layout.codecScratch regs)
                (recoveredChunkBits regs)),
            .basic
              (.add (inputRegisters regs).replacement
                (inputRegisters regs).replacement
                (recoveredChunkBits regs)),
            .basic
              (.sub (inputRegisters regs).replacement
                (inputRegisters regs).replacement
                (remaining regs))])
        store ready
        (decodeSteps + (1 + (1 + 1))) := by
    simpa [Cmd.seqList, afterMul, afterAdd, ready] using
      InvariantRuns.seq hdecodeRun
        (InvariantRuns.seq
          (InvariantRuns.basic
            (.mul (inputRegisters regs).replacement
              (Layout.codecScratch regs)
              (recoveredChunkBits regs))
            decoded (InvariantRuns.final hdecodeRun)
            hafterMul)
          (InvariantRuns.seq
            (InvariantRuns.basic
              (.add (inputRegisters regs).replacement
                (inputRegisters regs).replacement
                (recoveredChunkBits regs))
              afterMul hafterMul hafterAdd)
            (InvariantRuns.basic
              (.sub (inputRegisters regs).replacement
                (inputRegisters regs).replacement
                (remaining regs))
              afterAdd hafterAdd hready)))
  have hprefixWrites :
      RAM.Structured.Footprint.CmdWritesWithin
        regs.footprint
        (Cmd.seqList
          [decodeTapeBlock workTapeCount regs,
            .basic
              (.mul (inputRegisters regs).replacement
                (Layout.codecScratch regs)
                (recoveredChunkBits regs)),
            .basic
              (.add (inputRegisters regs).replacement
                (inputRegisters regs).replacement
                (recoveredChunkBits regs)),
            .basic
              (.sub (inputRegisters regs).replacement
                (inputRegisters regs).replacement
                (remaining regs))]) := by
    have hdecodeTrial :
        RAM.Structured.Footprint.CmdWritesWithin
          regs.footprint
          (decodeTapeBlock workTapeCount regs) :=
      cmdWritesWithin_mono
        (fun address haddress =>
          writeFootprint_subset_trial_internal regs
            (inputFootprint_subset regs haddress))
        (decodeTapeBlock_writesWithin_local workTapeCount regs)
    simp [Cmd.seqList,
      RAM.Structured.Footprint.CmdWritesWithin,
      RAM.Structured.Footprint.BasicWritesWithin,
      hdecodeTrial,
      writeFootprint_subset_trial_internal regs
        (inputIndex_mem_writeFootprint regs 11)]
  have hreadyFrame :
      SearchProgram.InputFrame
        controller regs.footprint input ready :=
    NeighborhoodTrial.Registers.runs_preserves_inputFrame
      regs hprefixWrites (InvariantRuns.toRuns hprefixRun) hframe
  have hreadyInputLength :
      ready controller.inputLength = input.length := by
    calc
      ready controller.inputLength =
          store controller.inputLength := by
        apply NeighborhoodTrial.Registers.runs_preserves_controller_index
          regs hprefixWrites (InvariantRuns.toRuns hprefixRun)
        · decide
        · decide
        · decide
      _ = input.length := hinputLength
  have hreadyBlockLength :
      ready (Layout.blockLength regs) = blockLength := by
    have hblockReplacement :
        Layout.blockLength regs ≠
          (inputRegisters regs).replacement :=
      layoutIndex_ne_inputIndex regs 2 11 (by decide)
    simp [ready, afterAdd, afterMul, Basic.exec,
      hblockReplacement, hdecodedBlockLength]
  have hreadyPacked :
      ready (packedTapeBlock regs) =
        tapeBlockCode workTapeCount tape block := by
    have hpackedReplacement :
        packedTapeBlock regs ≠
          (inputRegisters regs).replacement :=
      layoutIndex_ne_inputIndex regs 20 11 (by decide)
    have hdecodedPacked :
        decoded (packedTapeBlock regs) =
          tapeBlockCode workTapeCount tape block := by
      rw [hdecodeOutside]
      · exact hpacked
      · exact layoutIndex_not_mem_inputFootprint regs 20
          (by decide)
    simp [ready, afterAdd, afterMul, Basic.exec,
      hpackedReplacement, hdecodedPacked]
  have hreadyWord :
      ready (inputRegisters regs).word =
        SearchProgram.prefixCacheValue controller input
          (SearchProgram.footprintLimit
            controller regs.footprint) := by
    simp [ready, afterAdd, afterMul, Basic.exec,
      (inputRegisters regs).index_ne
        (by decide : (0 : Fin 12) ≠ 11),
      hdecodedWord, hword]
  have hreadyOne :
      ready (inputRegisters regs).one = 1 := by
    simp [ready, afterAdd, afterMul, Basic.exec,
      (inputRegisters regs).index_ne
        (by decide : (6 : Fin 12) ≠ 11)]
    exact hdecodedOne
  obtain ⟨afterSource, sourceSteps, hsourceRun,
      hsourceResult, _hsourceWord, hsourceOne,
      _hsourceFrame⟩ :=
    sourceBit_invariantRuns tm order regs input allowed bound
      blockLength tape block
      (chunk * chunkBits + chunkBits - (remainingBits + 1))
      ready htape hreadyBlockLength hreadyPacked
      hreadyCoordinate hreadyWord hreadyOne hreadyInputLength
      hpackedBound htapeCountBound hstateBound hfiveBlockBound
      hupperBound hlowerBound hcoordinateBound
      hblockProductBound haddressBound hfiveBound
      hlimitSucc hprefixCapacity (InvariantRuns.final hprefixRun)
      hreadyFrame
  have hsourceWrites :=
    sourceBit_writesWithin_input tm order regs
  have hsourceOutside :
      ∀ slot : Fin 34,
        (∀ index, inputMap index ≠ slot) →
        afterSource (regs.index slot) = ready (regs.index slot) := by
    intro slot hslot
    exact RAM.Structured.Footprint.runs_eq_outside
      hsourceWrites (InvariantRuns.toRuns hsourceRun)
      (layoutIndex_not_mem_inputFootprint regs slot hslot)
  have hsourceOperand :
      afterSource (operand regs) = accumulator := by
    calc
      afterSource (operand regs) = ready (operand regs) :=
        hsourceOutside 19 (by decide)
      _ = decoded (operand regs) := by
        have hoperandReplacement :
            operand regs ≠
              (inputRegisters regs).replacement :=
          layoutIndex_ne_inputIndex regs 19 11 (by decide)
        simp [ready, afterAdd, afterMul, Basic.exec,
          hoperandReplacement]
      _ = store (operand regs) := by
        rw [hdecodeOutside]
        exact layoutIndex_not_mem_inputFootprint regs 19
          (by decide)
      _ = accumulator := hoperand
  have hsourceRemaining :
      afterSource (remaining regs) = remainingBits + 1 := by
    calc
      afterSource (remaining regs) = ready (remaining regs) :=
        hsourceOutside 30 (by decide)
      _ = decoded (remaining regs) := by
        simp [ready, afterAdd, afterMul, Basic.exec,
          hremainingReplacement]
      _ = remainingBits + 1 := hdecodedRemaining
  let afterBase :=
    Basic.exec (.imm (inputRegisters regs).base 2) afterSource
  have hafterBase :
      NeighborhoodProgram.ValuesWithin allowed bound afterBase :=
    valuesWithin_update allowed bound
      (inputRegisters regs).base 2 afterSource
      (InvariantRuns.final hsourceRun) (by omega)
  let afterScale :=
    Basic.exec
      (.mul (operand regs) (operand regs)
        (inputRegisters regs).base)
      afterBase
  have hopBase :
      operand regs ≠ (inputRegisters regs).base :=
    layoutIndex_ne_inputIndex regs 19 2 (by decide)
  have hafterScale :
      NeighborhoodProgram.ValuesWithin allowed bound afterScale := by
    apply valuesWithin_update allowed bound
      (operand regs)
      (afterBase (operand regs) *
        afterBase (inputRegisters regs).base)
      afterBase hafterBase
    have hop : afterBase (operand regs) = accumulator := by
      simp [afterBase, Basic.exec, hopBase, hsourceOperand]
    have hbase :
        afterBase (inputRegisters regs).base = 2 := by
      simp [afterBase, Basic.exec]
    rw [hop, hbase]
    simpa [Nat.mul_comm] using haccumulatorDoubleBound
  let afterAccumulate :=
    Basic.exec
      (.add (operand regs) (inputRegisters regs).result
        (operand regs))
      afterScale
  have hopResult :
      operand regs ≠ (inputRegisters regs).result :=
    layoutIndex_ne_inputIndex regs 19 10 (by decide)
  have hresultBase :
      (inputRegisters regs).result ≠
        (inputRegisters regs).base :=
    (inputRegisters regs).index_ne (by decide)
  have hsourceResultBound :
      afterSource (inputRegisters regs).result ≤ 1 := by
    rw [hsourceResult]
    unfold coordinateBitValue
    cases coordinateBit tm order input blockLength tape block
        (chunk * chunkBits + chunkBits - (remainingBits + 1)) <;>
      simp
  have hafterAccumulate :
      NeighborhoodProgram.ValuesWithin
        allowed bound afterAccumulate := by
    apply valuesWithin_update allowed bound
      (operand regs)
      (afterScale (inputRegisters regs).result +
        afterScale (operand regs))
      afterScale hafterScale
    have hresult :
        afterScale (inputRegisters regs).result ≤ 1 := by
      simpa [afterScale, afterBase, Basic.exec,
        Ne.symm hopResult, hresultBase] using
        hsourceResultBound
    have hop :
        afterScale (operand regs) = 2 * accumulator := by
      simp [afterScale, afterBase, Basic.exec, hopBase,
        hsourceOperand]
      omega
    rw [hop]
    omega
  let final :=
    Basic.exec
      (.sub (remaining regs) (remaining regs)
        (inputRegisters regs).one)
      afterAccumulate
  have hafterAccumulateRemaining :
      afterAccumulate (remaining regs) =
        remainingBits + 1 := by
    have hremainingBase :
        remaining regs ≠ (inputRegisters regs).base :=
      layoutIndex_ne_inputIndex regs 30 2 (by decide)
    have hremainingOperand :
        remaining regs ≠ operand regs :=
      regs.injective.ne (by decide)
    simp [afterAccumulate, afterScale, afterBase, Basic.exec,
      hremainingBase, hremainingOperand, hsourceRemaining]
  have hfinal :
      NeighborhoodProgram.ValuesWithin allowed bound final := by
    apply valuesWithin_update allowed bound
      (remaining regs)
      (afterAccumulate (remaining regs) -
        afterAccumulate (inputRegisters regs).one)
      afterAccumulate hafterAccumulate
    exact (Nat.sub_le _ _).trans
      (by simpa [hafterAccumulateRemaining] using
        hremainingBound)
  have htailRun :
      InvariantRuns
        (NeighborhoodProgram.ValuesWithin allowed bound)
        (Cmd.seqList
          [.basic (.imm (inputRegisters regs).base 2),
            .basic
              (.mul (operand regs) (operand regs)
                (inputRegisters regs).base),
            .basic
              (.add (operand regs)
                (inputRegisters regs).result (operand regs)),
            .basic
              (.sub (remaining regs) (remaining regs)
                (inputRegisters regs).one)])
        afterSource final 4 := by
    simpa [Cmd.seqList, afterBase, afterScale,
      afterAccumulate, final] using
      InvariantRuns.seq
        (InvariantRuns.basic
          (.imm (inputRegisters regs).base 2)
          afterSource (InvariantRuns.final hsourceRun)
          hafterBase)
        (InvariantRuns.seq
          (InvariantRuns.basic
            (.mul (operand regs) (operand regs)
              (inputRegisters regs).base)
            afterBase hafterBase hafterScale)
          (InvariantRuns.seq
            (InvariantRuns.basic
              (.add (operand regs)
                (inputRegisters regs).result (operand regs))
              afterScale hafterScale hafterAccumulate)
            (InvariantRuns.basic
              (.sub (remaining regs) (remaining regs)
                (inputRegisters regs).one)
              afterAccumulate hafterAccumulate hfinal)))
  have hinvariantExists :
      ∃ steps,
        InvariantRuns
          (NeighborhoodProgram.ValuesWithin allowed bound)
          (sourceChunkBody tm order regs) store final steps := by
    refine
      ⟨decodeSteps + (1 + (1 + (1 + (sourceSteps + 4)))),
        ?_⟩
    simpa [sourceChunkBody, Cmd.seqList, afterMul, afterAdd,
      ready] using
      InvariantRuns.seq hdecodeRun
        (InvariantRuns.seq
          (InvariantRuns.basic
            (.mul (inputRegisters regs).replacement
              (Layout.codecScratch regs)
              (recoveredChunkBits regs))
            decoded (InvariantRuns.final hdecodeRun)
            hafterMul)
          (InvariantRuns.seq
            (InvariantRuns.basic
              (.add (inputRegisters regs).replacement
                (inputRegisters regs).replacement
                (recoveredChunkBits regs))
              afterMul hafterMul hafterAdd)
            (InvariantRuns.seq
              (InvariantRuns.basic
                (.sub (inputRegisters regs).replacement
                  (inputRegisters regs).replacement
                  (remaining regs))
                afterAdd hafterAdd hready)
              (InvariantRuns.seq hsourceRun htailRun))))
  obtain ⟨steps, hinvariant⟩ := hinvariantExists
  obtain ⟨semanticFinal, hsemanticRun, hfinalRemaining,
      hfinalOperand, hfinalPacked, hfinalChunkBits,
      hfinalCursor, hfinalBlockLength, hfinalWord,
      hfinalOne, hfinalInputLength, hfinalFrame⟩ :=
    sourceChunkBody_runs tm order regs input blockLength tape
      block chunk chunkBits remainingBits accumulator store htape
      hblockLength hpacked hcursor hchunkBits hremaining hoperand
      hword hinputLength hframe
  have heq : final = semanticFinal :=
    runs_final_eq (InvariantRuns.toRuns hinvariant) hsemanticRun
  subst semanticFinal
  exact
    ⟨final, steps, hinvariant, hfinalRemaining, hfinalOperand,
      hfinalPacked, hfinalChunkBits, hfinalCursor,
      hfinalBlockLength, hfinalWord, hfinalOne,
      hfinalInputLength, hfinalFrame⟩

private theorem sourceChunkLoop_runs
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (regs : NeighborhoodTrial.Registers controller)
    (input : List Bool)
    (blockLength tape block chunk chunkBits remainingBits
      accumulator : ℕ)
    (store : Store)
    (htape : tape < tapeCount workTapeCount)
    (hle : remainingBits ≤ chunkBits)
    (hblockLength :
      store (Layout.blockLength regs) = blockLength)
    (hpacked :
      store (packedTapeBlock regs) =
        tapeBlockCode workTapeCount tape block)
    (hcursor :
      store (Layout.codecScratch regs) = chunk)
    (hchunkBits :
      store (recoveredChunkBits regs) = chunkBits)
    (hremaining :
      store (remaining regs) = remainingBits)
    (hoperand :
      store (operand regs) = accumulator)
    (hword :
      store (inputRegisters regs).word =
        SearchProgram.prefixCacheValue controller input
          (SearchProgram.footprintLimit
            controller regs.footprint))
    (hone : store (inputRegisters regs).one = 1)
    (hinputLength : store controller.inputLength = input.length)
    (hframe :
      SearchProgram.InputFrame
        controller regs.footprint input store) :
    ∃ final,
      Runs
        (.whileNonzero (remaining regs)
          (sourceChunkBody tm order regs))
        store final ∧
      final (operand regs) =
        forwardChunk
          (coordinateBitValue tm order input blockLength tape block)
          (chunk * chunkBits + chunkBits - remainingBits)
          remainingBits accumulator ∧
      final (remaining regs) = 0 ∧
      final (packedTapeBlock regs) =
        tapeBlockCode workTapeCount tape block ∧
      final (recoveredChunkBits regs) = chunkBits ∧
      final (Layout.codecScratch regs) = chunk ∧
      final (Layout.blockLength regs) = blockLength ∧
      final (inputRegisters regs).word =
        SearchProgram.prefixCacheValue controller input
          (SearchProgram.footprintLimit
            controller regs.footprint) ∧
      final (inputRegisters regs).one = 1 ∧
      final controller.inputLength = input.length ∧
      SearchProgram.InputFrame
        controller regs.footprint input final := by
  induction remainingBits generalizing store accumulator with
  | zero =>
      have hzero : store (remaining regs) = 0 := by
        simpa using hremaining
      refine
        ⟨store, Runs.whileZero hzero, ?_, hzero, hpacked,
          hchunkBits, hcursor, hblockLength, hword, hone,
          hinputLength, hframe⟩
      simpa [forwardChunk] using hoperand
  | succ remainingBits ih =>
      have hnonzero :
          store (remaining regs) ≠ 0 := by
        rw [hremaining]
        omega
      let coordinate :=
        chunk * chunkBits + chunkBits - (remainingBits + 1)
      let nextAccumulator :=
        2 * accumulator +
          coordinateBitValue tm order input blockLength tape block
            coordinate
      obtain ⟨afterBody, hbodyRun, hbodyRemaining,
          hbodyOperand, hbodyPacked, hbodyChunkBits,
          hbodyCursor, hbodyBlockLength, hbodyWord, hbodyOne,
          hbodyInputLength, hbodyFrame⟩ :=
        sourceChunkBody_runs tm order regs input blockLength
          tape block chunk chunkBits remainingBits accumulator
          store htape hblockLength hpacked hcursor hchunkBits
          (by simpa using hremaining) hoperand hword
          hinputLength hframe
      have hbodyOperand' :
          afterBody (operand regs) = nextAccumulator := by
        simpa [nextAccumulator, coordinate] using hbodyOperand
      obtain ⟨final, hloopRun, hloopOperand, hloopRemaining,
          hloopPacked, hloopChunkBits, hloopCursor,
          hloopBlockLength, hloopWord, hloopOne,
          hloopInputLength, hloopFrame⟩ :=
        ih nextAccumulator afterBody (by omega)
          hbodyBlockLength hbodyPacked hbodyCursor
          hbodyChunkBits hbodyRemaining hbodyOperand'
          hbodyWord hbodyOne hbodyInputLength hbodyFrame
      refine
        ⟨final,
          Runs.whileNonzero hnonzero hbodyRun hloopRun,
          ?_, hloopRemaining, hloopPacked, hloopChunkBits,
          hloopCursor, hloopBlockLength, hloopWord, hloopOne,
          hloopInputLength, hloopFrame⟩
      rw [hloopOperand]
      have hnextCoordinate :
          chunk * chunkBits + chunkBits - remainingBits =
            coordinate + 1 := by
        dsimp [coordinate]
        omega
      simp only [forwardChunk]
      rw [hnextCoordinate]

private theorem sourceChunkLoop_invariantRuns
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (regs : NeighborhoodTrial.Registers controller)
    (input : List Bool) (allowed : Finset ℕ) (bound : ℕ)
    (blockLength tape block chunk chunkBits remainingBits
      accumulator : ℕ)
    (store : Store)
    (htape : tape < tapeCount workTapeCount)
    (hle : remainingBits ≤ chunkBits)
    (hblockLength :
      store (Layout.blockLength regs) = blockLength)
    (hpacked :
      store (packedTapeBlock regs) =
        tapeBlockCode workTapeCount tape block)
    (hcursor :
      store (Layout.codecScratch regs) = chunk)
    (hchunkBits :
      store (recoveredChunkBits regs) = chunkBits)
    (hremaining :
      store (remaining regs) = remainingBits)
    (hoperand :
      store (operand regs) = accumulator)
    (hword :
      store (inputRegisters regs).word =
        SearchProgram.prefixCacheValue controller input
          (SearchProgram.footprintLimit
            controller regs.footprint))
    (hone : store (inputRegisters regs).one = 1)
    (hinputLength : store controller.inputLength = input.length)
    (hpackedBound :
      tapeBlockCode workTapeCount tape block ≤ bound)
    (htapeCountBound : tapeCount workTapeCount ≤ bound)
    (hstateBound : Fintype.card tm.Q ≤ bound)
    (hfiveBlockBound : 5 * blockLength ≤ bound)
    (hupperBound :
      Fintype.card tm.Q + 5 * blockLength ≤ bound)
    (hlowerBound :
      Fintype.card tm.Q + blockLength ≤ bound)
    (hchunkProductBound : chunk * chunkBits ≤ bound)
    (hchunkCoordinateBound :
      chunk * chunkBits + chunkBits ≤ bound)
    (hblockProductBound : block * blockLength ≤ bound)
    (haddressMaxBound :
      block * blockLength +
        (chunk * chunkBits + chunkBits) / 4 ≤ bound)
    (hremainingBitsBound : chunkBits ≤ bound)
    (haccumulatorPotential :
      (accumulator + 1) * 2 ^ remainingBits ≤ bound)
    (hfiveBound : 5 ≤ bound)
    (hlimitSucc :
      SearchProgram.footprintLimit controller regs.footprint + 1 ≤
        bound)
    (hprefixCapacity :
      2 ^
          SearchProgram.footprintLimit controller regs.footprint ≤
        bound)
    (hstore :
      NeighborhoodProgram.ValuesWithin allowed bound store)
    (hframe :
      SearchProgram.InputFrame
        controller regs.footprint input store) :
    ∃ final steps,
      InvariantRuns
        (NeighborhoodProgram.ValuesWithin allowed bound)
        (.whileNonzero (remaining regs)
          (sourceChunkBody tm order regs))
        store final steps ∧
      final (operand regs) =
        forwardChunk
          (coordinateBitValue tm order input blockLength tape block)
          (chunk * chunkBits + chunkBits - remainingBits)
          remainingBits accumulator ∧
      final (remaining regs) = 0 ∧
      final (packedTapeBlock regs) =
        tapeBlockCode workTapeCount tape block ∧
      final (recoveredChunkBits regs) = chunkBits ∧
      final (Layout.codecScratch regs) = chunk ∧
      final (Layout.blockLength regs) = blockLength ∧
      final (inputRegisters regs).word =
        SearchProgram.prefixCacheValue controller input
          (SearchProgram.footprintLimit
            controller regs.footprint) ∧
      final (inputRegisters regs).one = 1 ∧
      final controller.inputLength = input.length ∧
      SearchProgram.InputFrame
        controller regs.footprint input final := by
  induction remainingBits generalizing store accumulator with
  | zero =>
      have hzero : store (remaining regs) = 0 := by
        simpa using hremaining
      refine
        ⟨store, 1, InvariantRuns.whileZero hzero hstore,
          ?_, hzero, hpacked, hchunkBits, hcursor,
          hblockLength, hword, hone, hinputLength, hframe⟩
      simpa [forwardChunk] using hoperand
  | succ remainingBits ih =>
      have hnonzero :
          store (remaining regs) ≠ 0 := by
        rw [hremaining]
        omega
      let coordinate :=
        chunk * chunkBits + chunkBits - (remainingBits + 1)
      let nextAccumulator :=
        2 * accumulator +
          coordinateBitValue tm order input blockLength tape block
            coordinate
      have hcoordinateBound : coordinate ≤ bound := by
        exact (Nat.sub_le _ _).trans hchunkCoordinateBound
      have haddressBound :
          block * blockLength +
              (coordinate -
                (Fintype.card tm.Q + blockLength)) / 4 ≤
            bound := by
        have hcoordinateSub :
            coordinate -
                (Fintype.card tm.Q + blockLength) ≤
              chunk * chunkBits + chunkBits :=
          calc
            coordinate -
                  (Fintype.card tm.Q + blockLength) ≤
                coordinate :=
              Nat.sub_le _ _
            _ ≤ chunk * chunkBits + chunkBits :=
              Nat.sub_le _ _
        have hdiv :
            (coordinate -
                (Fintype.card tm.Q + blockLength)) / 4 ≤
              (chunk * chunkBits + chunkBits) / 4 :=
          Nat.div_le_div_right hcoordinateSub
        omega
      have hdoubleBound : 2 * accumulator ≤ bound := by
        have hpowTwo : 2 ≤ 2 ^ (remainingBits + 1) := by
          rw [pow_succ]
          have hpositive := Nat.two_pow_pos remainingBits
          nlinarith
        have hpotentialAtLeastDouble :
            2 * (accumulator + 1) ≤
              (accumulator + 1) * 2 ^ (remainingBits + 1) := by
          simpa [Nat.mul_comm] using
            Nat.mul_le_mul_left (accumulator + 1) hpowTwo
        omega
      have hnextBound : 2 * accumulator + 1 ≤ bound := by
        have hpotentialAtLeastDouble :
            2 * (accumulator + 1) ≤
              (accumulator + 1) * 2 ^ (remainingBits + 1) := by
          have hpowTwo : 2 ≤ 2 ^ (remainingBits + 1) := by
            rw [pow_succ]
            have hpositive := Nat.two_pow_pos remainingBits
            nlinarith
          simpa [Nat.mul_comm] using
            Nat.mul_le_mul_left (accumulator + 1) hpowTwo
        omega
      obtain ⟨afterBody, bodySteps, hbodyRun,
          hbodyRemaining, hbodyOperand, hbodyPacked,
          hbodyChunkBits, hbodyCursor, hbodyBlockLength,
          hbodyWord, hbodyOne, hbodyInputLength,
          hbodyFrame⟩ :=
        sourceChunkBody_invariantRuns tm order regs input
          allowed bound blockLength tape block chunk chunkBits
          remainingBits accumulator store htape hblockLength
          hpacked hcursor hchunkBits (by simpa using hremaining)
          hoperand hword hinputLength hpackedBound
          htapeCountBound hstateBound hfiveBlockBound
          hupperBound hlowerBound hchunkProductBound
          hchunkCoordinateBound hcoordinateBound
          hblockProductBound haddressBound hdoubleBound
          hnextBound (by omega) hfiveBound hlimitSucc
          hprefixCapacity hstore hframe
      have hbodyOperand' :
          afterBody (operand regs) = nextAccumulator := by
        simpa [nextAccumulator, coordinate] using hbodyOperand
      have hbitBound :
          coordinateBitValue tm order input blockLength tape block
              coordinate ≤
            1 := by
        unfold coordinateBitValue
        cases coordinateBit tm order input blockLength tape block
            coordinate <;>
          simp
      have hnextPotential :
          (nextAccumulator + 1) * 2 ^ remainingBits ≤ bound := by
        have hnextLe :
            nextAccumulator + 1 ≤ 2 * (accumulator + 1) := by
          dsimp [nextAccumulator]
          omega
        calc
          (nextAccumulator + 1) * 2 ^ remainingBits ≤
              (2 * (accumulator + 1)) * 2 ^ remainingBits :=
            Nat.mul_le_mul_right _ hnextLe
          _ = (accumulator + 1) * 2 ^ (remainingBits + 1) := by
            rw [pow_succ]
            ring
          _ ≤ bound := haccumulatorPotential
      obtain ⟨final, loopSteps, hloopRun, hloopOperand,
          hloopRemaining, hloopPacked, hloopChunkBits,
          hloopCursor, hloopBlockLength, hloopWord, hloopOne,
          hloopInputLength, hloopFrame⟩ :=
        ih nextAccumulator afterBody (by omega)
          hbodyBlockLength hbodyPacked hbodyCursor
          hbodyChunkBits hbodyRemaining hbodyOperand'
          hbodyWord hbodyOne hbodyInputLength
          hnextPotential (InvariantRuns.final hbodyRun) hbodyFrame
      refine
        ⟨final, bodySteps + loopSteps + 2,
          InvariantRuns.whileNonzero hnonzero hbodyRun hloopRun,
          ?_, hloopRemaining, hloopPacked, hloopChunkBits,
          hloopCursor, hloopBlockLength, hloopWord, hloopOne,
          hloopInputLength, hloopFrame⟩
      rw [hloopOperand]
      have hnextCoordinate :
          chunk * chunkBits + chunkBits - remainingBits =
            coordinate + 1 := by
        dsimp [coordinate]
        omega
      simp only [forwardChunk]
      rw [hnextCoordinate]

private theorem index_not_mem_writeFootprint
    (regs : NeighborhoodTrial.Registers controller)
    (slot : Fin 34)
    (hslot :
      slot ∉ Finset.univ.image writeMap) :
    regs.index slot ∉ writeFootprint regs := by
  intro hmember
  rcases Finset.mem_image.mp hmember with
    ⟨writeSlot, _, heq⟩
  apply hslot
  refine Finset.mem_image.mpr
    ⟨writeSlot, Finset.mem_univ _, ?_⟩
  exact regs.injective heq

private theorem post_of_run
    (regs : NeighborhoodTrial.Registers controller)
    (input : List Bool) (expected : ℕ)
    {command : Cmd} {initial final : Store}
    (hwrites :
      RAM.Structured.Footprint.CmdWritesWithin
        (writeFootprint regs) command)
    (hrun : Runs command initial final)
    (hframe :
      SearchProgram.InputFrame
        controller regs.footprint input initial)
    (hoperand : final (operand regs) = expected) :
    SourceChunkPost regs input expected initial final := by
  have htrialWrites :
      RAM.Structured.Footprint.CmdWritesWithin
        regs.footprint command :=
    cmdWritesWithin_mono
      (writeFootprint_subset_trial_internal regs) hwrites
  have hfuel :=
    index_not_mem_writeFootprint regs 22 (by decide)
  have hnode :=
    index_not_mem_writeFootprint regs 23 (by decide)
  have hscalar :=
    index_not_mem_writeFootprint regs 25 (by decide)
  have hout :=
    index_not_mem_writeFootprint regs 26 (by decide)
  have hphase :=
    index_not_mem_writeFootprint regs 27 (by decide)
  have hactive :=
    index_not_mem_writeFootprint regs 28 (by decide)
  have hcursor :=
    index_not_mem_writeFootprint regs 31 (by decide)
  have hbank :=
    index_not_mem_writeFootprint regs 33 (by decide)
  have hbase :=
    index_not_mem_writeFootprint regs 14 (by decide)
  have hmodulus :=
    index_not_mem_writeFootprint regs 24 (by decide)
  have hmodulusPred :=
    index_not_mem_writeFootprint regs 16 (by decide)
  change Layout.fuel regs ∉ writeFootprint regs at hfuel
  change Layout.nodeCode regs ∉ writeFootprint regs at hnode
  change Layout.scalar regs ∉ writeFootprint regs at hscalar
  change Layout.out regs ∉ writeFootprint regs at hout
  change Layout.phaseCode regs ∉ writeFootprint regs at hphase
  change Layout.active regs ∉ writeFootprint regs at hactive
  change Layout.codecScratch regs ∉ writeFootprint regs at hcursor
  change
    (Layout.residueScaleRegisters regs).bank.bank.word ∉
      writeFootprint regs at hbank
  change
    (Layout.residueScaleRegisters regs).bank.bank.base ∉
      writeFootprint regs at hbase
  change
    (Layout.residueScaleRegisters regs).bank.modulus ∉
      writeFootprint regs at hmodulus
  change
    (Layout.residueScaleRegisters regs).bank.modulusPred ∉
      writeFootprint regs at hmodulusPred
  exact
    { operand_eq := hoperand
      inputFrame :=
        NeighborhoodTrial.Registers.runs_preserves_inputFrame
          regs htrialWrites hrun hframe
      fuel_eq :=
        RAM.Structured.Footprint.runs_eq_outside
          hwrites hrun hfuel
      nodeCode_eq :=
        RAM.Structured.Footprint.runs_eq_outside
          hwrites hrun hnode
      scalar_eq :=
        RAM.Structured.Footprint.runs_eq_outside
          hwrites hrun hscalar
      out_eq :=
        RAM.Structured.Footprint.runs_eq_outside
          hwrites hrun hout
      phaseCode_eq :=
        RAM.Structured.Footprint.runs_eq_outside
          hwrites hrun hphase
      active_eq :=
        RAM.Structured.Footprint.runs_eq_outside
          hwrites hrun hactive
      cursor_eq :=
        RAM.Structured.Footprint.runs_eq_outside
          hwrites hrun hcursor
      bankWord_eq :=
        RAM.Structured.Footprint.runs_eq_outside
          hwrites hrun hbank
      bankBase_eq :=
        RAM.Structured.Footprint.runs_eq_outside
          hwrites hrun hbase
      modulus_eq :=
        RAM.Structured.Footprint.runs_eq_outside
          hwrites hrun hmodulus
      modulusPred_eq :=
        RAM.Structured.Footprint.runs_eq_outside
          hwrites hrun hmodulusPred }

private theorem layoutIndex_not_mem_recoverFootprint
    (regs : NeighborhoodTrial.Registers controller)
    (slot : Fin 34)
    (hinput : ∀ index, inputMap index ≠ slot)
    (hrecovered : slot ≠ 21) :
    regs.index slot ∉ recoverFootprint regs := by
  intro hmember
  rcases Finset.mem_union.mp hmember with hmember | hmember
  · exact layoutIndex_not_mem_inputFootprint regs slot hinput hmember
  · simp only [Finset.mem_singleton] at hmember
    exact hrecovered (regs.injective hmember)

theorem sourceChunk_runs_internal
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (regs : NeighborhoodTrial.Registers controller)
    (input : List Bool) (blockLength : ℕ)
    (hpositive : 0 < blockLength)
    (tape : TapeIndex workTapeCount) (block : ℕ)
    (chunk :
      Fin
        (PrimeGrouped.Logarithmic.chunkCount
          (payloadWidth tm blockLength)
          (graphFanIn workTapeCount)))
    (initial : Store)
    (htape :
      initial (ControlDecode.nodeTape regs) = tape.val)
    (hblock :
      initial (ControlDecode.nodePayload0 regs) = block)
    (hblockLength :
      initial (Layout.blockLength regs) = blockLength)
    (hradix :
      initial (Layout.chunkRadix regs) =
        2 ^
          PrimeGrouped.Logarithmic.chunkBits
            (payloadWidth tm blockLength)
            (graphFanIn workTapeCount))
    (hcursor :
      initial (Layout.codecScratch regs) = chunk.val)
    (hinputLength :
      initial controller.inputLength = input.length)
    (hframe :
      SearchProgram.InputFrame
        controller regs.footprint input initial) :
    ∃ final,
      Runs (sourceChunk tm order regs) initial final ∧
      SourceChunkPost regs input
        (Residue.sourceValue tm input blockLength
          (FiniteEncoding.ofStateOrder order blockLength)
          hpositive tape block chunk)
        initial final := by
  let chunkBits :=
    PrimeGrouped.Logarithmic.chunkBits
      (payloadWidth tm blockLength)
      (graphFanIn workTapeCount)
  let afterTapeCount :=
    Basic.exec
      (.imm (packedTapeBlock regs)
        (tapeCount workTapeCount))
      initial
  let afterBlock :=
    Basic.exec
      (.mul (packedTapeBlock regs)
        (ControlDecode.nodePayload0 regs)
        (packedTapeBlock regs))
      afterTapeCount
  let packed :=
    Basic.exec
      (.add (packedTapeBlock regs)
        (ControlDecode.nodeTape regs)
        (packedTapeBlock regs))
      afterBlock
  have hpackedValue :
      packed (packedTapeBlock regs) =
        tapeBlockCode workTapeCount tape.val block := by
    have hpackedTape :
        packedTapeBlock regs ≠ ControlDecode.nodeTape regs :=
      regs.injective.ne (by decide)
    have hpackedBlock :
        packedTapeBlock regs ≠
          ControlDecode.nodePayload0 regs :=
      regs.injective.ne (by decide)
    simp [packed, afterBlock, afterTapeCount, Basic.exec,
      hpackedTape.symm, hpackedBlock.symm, htape, hblock,
      tapeBlockCode]
    rw [Nat.mul_comm]
  have hpackedRadix :
      packed (Layout.chunkRadix regs) = 2 ^ chunkBits := by
    have hradixPacked :
        Layout.chunkRadix regs ≠ packedTapeBlock regs :=
      regs.injective.ne (by decide)
    simp [packed, afterBlock, afterTapeCount, Basic.exec,
      hradixPacked, chunkBits, hradix]
  obtain ⟨recovered, hrecoverRun, hrecoveredChunkBits,
      _hrecoveredWord, _hrecoveredTest, _hrecoveredBase,
      _hrecoveredBasePred, hrecoveredOne,
      hrecoverOutside⟩ :=
    recoverChunkBits_runs regs packed chunkBits hpackedRadix
  let afterRemaining :=
    Function.update recovered (remaining regs)
      (recovered (recoveredChunkBits regs))
  have hremainingRun :
      Runs
        (copy (remaining regs) (recoveredChunkBits regs))
        recovered afterRemaining := by
    exact copy_runs recovered
      (regs.injective.ne (by decide))
  let afterWord :=
    Function.update afterRemaining
      (inputRegisters regs).word
      (afterRemaining controller.prefixCache)
  have hwordRun :
      Runs
        (copy (inputRegisters regs).word
          controller.prefixCache)
        afterRemaining afterWord := by
    exact copy_runs afterRemaining
      (by
        change regs.index 29 ≠ controller.index 16
        exact regs.index_ne_controller 29 16)
  let ready :=
    Basic.exec (.imm (operand regs) 0) afterWord
  have hoperandRun :
      Runs (.basic (.imm (operand regs) 0))
        afterWord ready :=
    Runs.basic _ _
  have hsetupRun :
      Runs
        (Cmd.seqList
          [.basic
            (.imm (packedTapeBlock regs)
              (tapeCount workTapeCount)),
            .basic
              (.mul (packedTapeBlock regs)
                (ControlDecode.nodePayload0 regs)
                (packedTapeBlock regs)),
            .basic
              (.add (packedTapeBlock regs)
                (ControlDecode.nodeTape regs)
                (packedTapeBlock regs)),
            recoverChunkBits regs,
            copy (remaining regs) (recoveredChunkBits regs),
            copy (inputRegisters regs).word
              controller.prefixCache,
            .basic (.imm (operand regs) 0)])
        initial ready := by
    simpa [Cmd.seqList, afterTapeCount, afterBlock, packed,
      afterRemaining, afterWord, ready] using
      Runs.seq
        (Runs.basic
          (.imm (packedTapeBlock regs)
            (tapeCount workTapeCount))
          initial)
        (Runs.seq
          (Runs.basic
            (.mul (packedTapeBlock regs)
              (ControlDecode.nodePayload0 regs)
              (packedTapeBlock regs))
            afterTapeCount)
          (Runs.seq
            (Runs.basic
              (.add (packedTapeBlock regs)
                (ControlDecode.nodeTape regs)
                (packedTapeBlock regs))
              afterBlock)
            (Runs.seq hrecoverRun
              (Runs.seq hremainingRun
                (Runs.seq hwordRun hoperandRun)))))
  have hrecoverWithin :
      RAM.Structured.Footprint.CmdWritesWithin
        (writeFootprint regs) (recoverChunkBits regs) := by
    apply cmdWritesWithin_mono _ <|
      recoverChunkBits_writesWithin_local regs
    intro address haddress
    rcases Finset.mem_union.mp haddress with haddress | haddress
    · exact inputFootprint_subset regs haddress
    · rw [Finset.mem_singleton.mp haddress]
      simpa using writeMap_mem regs (14 : Fin 16)
  have hsetupWrites :
      RAM.Structured.Footprint.CmdWritesWithin
        (writeFootprint regs)
        (Cmd.seqList
          [.basic
            (.imm (packedTapeBlock regs)
              (tapeCount workTapeCount)),
            .basic
              (.mul (packedTapeBlock regs)
                (ControlDecode.nodePayload0 regs)
                (packedTapeBlock regs)),
            .basic
              (.add (packedTapeBlock regs)
                (ControlDecode.nodeTape regs)
                (packedTapeBlock regs)),
            recoverChunkBits regs,
            copy (remaining regs) (recoveredChunkBits regs),
            copy (inputRegisters regs).word
              controller.prefixCache,
            .basic (.imm (operand regs) 0)]) := by
    have hpacked := writeMap_mem regs (13 : Fin 16)
    have hremaining := writeMap_mem regs (15 : Fin 16)
    have hword :=
      inputIndex_mem_writeFootprint regs (0 : Fin 12)
    have hoperand := writeMap_mem regs (12 : Fin 16)
    change packedTapeBlock regs ∈ writeFootprint regs at hpacked
    change remaining regs ∈ writeFootprint regs at hremaining
    change
      (inputRegisters regs).word ∈ writeFootprint regs at hword
    change operand regs ∈ writeFootprint regs at hoperand
    simp [Cmd.seqList, copy,
      RAM.Structured.Footprint.CmdWritesWithin,
      RAM.Structured.Footprint.BasicWritesWithin,
      hpacked, hremaining, hword, hoperand, hrecoverWithin]
  have hsetupTrial :
      RAM.Structured.Footprint.CmdWritesWithin
        regs.footprint
        (Cmd.seqList
          [.basic
            (.imm (packedTapeBlock regs)
              (tapeCount workTapeCount)),
            .basic
              (.mul (packedTapeBlock regs)
                (ControlDecode.nodePayload0 regs)
                (packedTapeBlock regs)),
            .basic
              (.add (packedTapeBlock regs)
                (ControlDecode.nodeTape regs)
                (packedTapeBlock regs)),
            recoverChunkBits regs,
            copy (remaining regs) (recoveredChunkBits regs),
            copy (inputRegisters regs).word
              controller.prefixCache,
            .basic (.imm (operand regs) 0)]) :=
    cmdWritesWithin_mono
      (writeFootprint_subset_trial_internal regs) hsetupWrites
  have hreadyFrame :
      SearchProgram.InputFrame
        controller regs.footprint input ready :=
    NeighborhoodTrial.Registers.runs_preserves_inputFrame
      regs hsetupTrial hsetupRun hframe
  have hreadyInputLength :
      ready controller.inputLength = input.length := by
    calc
      ready controller.inputLength =
          initial controller.inputLength := by
        apply NeighborhoodTrial.Registers.runs_preserves_controller_index
          regs hsetupTrial hsetupRun
        · decide
        · decide
        · decide
      _ = input.length := hinputLength
  have hrecoveredPacked :
      recovered (packedTapeBlock regs) =
        tapeBlockCode workTapeCount tape.val block := by
    rw [hrecoverOutside]
    · exact hpackedValue
    · exact layoutIndex_not_mem_recoverFootprint regs 20
        (by decide) (by decide)
  have hreadyPacked :
      ready (packedTapeBlock regs) =
        tapeBlockCode workTapeCount tape.val block := by
    have hpackedRemaining :
        packedTapeBlock regs ≠ remaining regs :=
      regs.injective.ne (by decide)
    have hpackedWord :
        packedTapeBlock regs ≠ (inputRegisters regs).word :=
      layoutIndex_ne_inputIndex regs 20 0 (by decide)
    have hpackedOperand :
        packedTapeBlock regs ≠ operand regs :=
      regs.injective.ne (by decide)
    simp [ready, afterWord, afterRemaining, Basic.exec,
      hpackedRemaining, hpackedWord, hpackedOperand,
      hrecoveredPacked]
  have hrecoveredCursor :
      recovered (Layout.codecScratch regs) = chunk.val := by
    rw [hrecoverOutside]
    · have hpackedCursor :
          Layout.codecScratch regs ≠ packedTapeBlock regs :=
        regs.injective.ne (by decide)
      simp [packed, afterBlock, afterTapeCount, Basic.exec,
        hpackedCursor, hcursor]
    · exact layoutIndex_not_mem_recoverFootprint regs 31
        (by decide) (by decide)
  have hreadyCursor :
      ready (Layout.codecScratch regs) = chunk.val := by
    have hcursorRemaining :
        Layout.codecScratch regs ≠ remaining regs :=
      regs.injective.ne (by decide)
    have hcursorWord :
        Layout.codecScratch regs ≠
          (inputRegisters regs).word :=
      layoutIndex_ne_inputIndex regs 31 0 (by decide)
    have hcursorOperand :
        Layout.codecScratch regs ≠ operand regs :=
      regs.injective.ne (by decide)
    simp [ready, afterWord, afterRemaining, Basic.exec,
      hcursorRemaining, hcursorWord, hcursorOperand,
      hrecoveredCursor]
  have hrecoveredBlockLength :
      recovered (Layout.blockLength regs) = blockLength := by
    rw [hrecoverOutside]
    · have hblockPacked :
          Layout.blockLength regs ≠ packedTapeBlock regs :=
        regs.injective.ne (by decide)
      simp [packed, afterBlock, afterTapeCount, Basic.exec,
        hblockPacked, hblockLength]
    · exact layoutIndex_not_mem_recoverFootprint regs 2
        (by decide) (by decide)
  have hreadyBlockLength :
      ready (Layout.blockLength regs) = blockLength := by
    have hblockRemaining :
        Layout.blockLength regs ≠ remaining regs :=
      regs.injective.ne (by decide)
    have hblockWord :
        Layout.blockLength regs ≠
          (inputRegisters regs).word :=
      layoutIndex_ne_inputIndex regs 2 0 (by decide)
    have hblockOperand :
        Layout.blockLength regs ≠ operand regs :=
      regs.injective.ne (by decide)
    simp [ready, afterWord, afterRemaining, Basic.exec,
      hblockRemaining, hblockWord, hblockOperand,
      hrecoveredBlockLength]
  have hreadyChunkBits :
      ready (recoveredChunkBits regs) = chunkBits := by
    have hchunkRemaining :
        recoveredChunkBits regs ≠ remaining regs :=
      regs.injective.ne (by decide)
    have hchunkWord :
        recoveredChunkBits regs ≠
          (inputRegisters regs).word :=
      (recovered_ne_inputIndex regs 0)
    have hchunkOperand :
        recoveredChunkBits regs ≠ operand regs :=
      regs.injective.ne (by decide)
    simp [ready, afterWord, afterRemaining, Basic.exec,
      hchunkRemaining, hchunkWord, hchunkOperand,
      hrecoveredChunkBits]
  have hreadyRemaining :
      ready (remaining regs) = chunkBits := by
    have hremainingWord :
        remaining regs ≠ (inputRegisters regs).word :=
      layoutIndex_ne_inputIndex regs 30 0 (by decide)
    have hremainingOperand :
        remaining regs ≠ operand regs :=
      regs.injective.ne (by decide)
    simp [ready, afterWord, afterRemaining, Basic.exec,
      hremainingWord, hremainingOperand,
      hrecoveredChunkBits]
  have hreadyOperand :
      ready (operand regs) = 0 := by
    simp [ready, Basic.exec]
  have hreadyWord :
      ready (inputRegisters regs).word =
        SearchProgram.prefixCacheValue controller input
          (SearchProgram.footprintLimit
            controller regs.footprint) := by
    calc
      ready (inputRegisters regs).word =
          ready controller.prefixCache := by
        have hwordOperand :
            (inputRegisters regs).word ≠ operand regs :=
          (layoutIndex_ne_inputIndex regs 19 0 (by decide)).symm
        have hcacheOperand :
            controller.prefixCache ≠ operand regs := by
          change controller.index 16 ≠ regs.index 19
          exact (regs.index_ne_controller 19 16).symm
        have hcacheRemaining :
            controller.prefixCache ≠ remaining regs := by
          change controller.index 16 ≠ regs.index 30
          exact (regs.index_ne_controller 30 16).symm
        have hcacheWord :
            controller.prefixCache ≠
              (inputRegisters regs).word := by
          change controller.index 16 ≠ regs.index 29
          exact (regs.index_ne_controller 29 16).symm
        simp [ready, afterWord, afterRemaining, Basic.exec,
          hwordOperand, hcacheOperand, hcacheRemaining,
          hcacheWord]
      _ = SearchProgram.prefixCacheValue controller input
          (SearchProgram.footprintLimit
            controller regs.footprint) :=
        hreadyFrame.1
  have hreadyOne :
      ready (inputRegisters regs).one = 1 := by
    have honeRemaining :
        (inputRegisters regs).one ≠ remaining regs :=
      (layoutIndex_ne_inputIndex regs 30 6 (by decide)).symm
    have honeWord :
        (inputRegisters regs).one ≠
          (inputRegisters regs).word :=
      (inputRegisters regs).index_ne (by decide)
    have honeOperand :
        (inputRegisters regs).one ≠ operand regs :=
      (layoutIndex_ne_inputIndex regs 19 6 (by decide)).symm
    simp [ready, afterWord, afterRemaining, Basic.exec,
      honeRemaining, honeWord, honeOperand, hrecoveredOne]
  obtain ⟨final, hloopRun, hloopOperand, _hloopRemaining,
      _hloopPacked, _hloopChunkBits, _hloopCursor,
      _hloopBlockLength, _hloopWord, _hloopOne,
      _hloopInputLength, _hloopFrame⟩ :=
    sourceChunkLoop_runs tm order regs input blockLength tape.val
      block chunk.val chunkBits chunkBits 0 ready tape.isLt
      (by rfl) hreadyBlockLength hreadyPacked hreadyCursor
      hreadyChunkBits hreadyRemaining hreadyOperand hreadyWord
      hreadyOne hreadyInputLength hreadyFrame
  have hrun :
      Runs (sourceChunk tm order regs) initial final := by
    simpa [sourceChunk, Cmd.seqList, afterTapeCount,
      afterBlock, packed, afterRemaining, afterWord, ready] using
      Runs.seq
        (Runs.basic
          (.imm (packedTapeBlock regs)
            (tapeCount workTapeCount))
          initial)
        (Runs.seq
          (Runs.basic
            (.mul (packedTapeBlock regs)
              (ControlDecode.nodePayload0 regs)
              (packedTapeBlock regs))
            afterTapeCount)
          (Runs.seq
            (Runs.basic
              (.add (packedTapeBlock regs)
                (ControlDecode.nodeTape regs)
                (packedTapeBlock regs))
              afterBlock)
            (Runs.seq hrecoverRun
              (Runs.seq hremainingRun
                (Runs.seq hwordRun
                  (Runs.seq hoperandRun hloopRun))))))
  have hvalue :
      final (operand regs) =
        Residue.sourceValue tm input blockLength
          (FiniteEncoding.ofStateOrder order blockLength)
          hpositive tape block chunk := by
    calc
      final (operand regs) =
          sourceChunkValue tm order input blockLength tape.val
            block chunk.val chunkBits := by
        simpa [sourceChunkValue] using hloopOperand
      _ = Residue.sourceValue tm input blockLength
          (FiniteEncoding.ofStateOrder order blockLength)
          hpositive tape block chunk :=
        sourceChunkValue_eq_internal tm order input blockLength
          hpositive tape block chunk
  exact
    ⟨final, hrun,
      post_of_run regs input _
        (sourceChunk_writesWithin_internal tm order regs)
        hrun hframe hvalue⟩

theorem sourceChunk_fixedCap_invariantRuns_internal
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (regs : NeighborhoodTrial.Registers controller)
    (input : List Bool) (candidate blockLength : ℕ)
    (hcanonical :
      blockLength =
        NeighborhoodGraph.WorkspaceAccounting.blockLength candidate)
    (hinput : input.length ≤ candidate)
    (tape : TapeIndex workTapeCount) (block : ℕ)
    (hblockBound :
      block ≤
        max
          (NeighborhoodGraph.WorkspaceAccounting.horizon candidate)
          1)
    (chunk :
      Fin
        (PrimeGrouped.Logarithmic.chunkCount
          (payloadWidth tm blockLength)
          (graphFanIn workTapeCount)))
    (allowed : Finset ℕ) (initial : Store)
    (htape :
      initial (ControlDecode.nodeTape regs) = tape.val)
    (hblock :
      initial (ControlDecode.nodePayload0 regs) = block)
    (hblockLength :
      initial (Layout.blockLength regs) = blockLength)
    (hradix :
      initial (Layout.chunkRadix regs) =
        2 ^
          PrimeGrouped.Logarithmic.chunkBits
            (payloadWidth tm blockLength)
            (graphFanIn workTapeCount))
    (hcursor :
      initial (Layout.codecScratch regs) = chunk.val)
    (hinputLength :
      initial controller.inputLength = input.length)
    (hvalues :
      NeighborhoodProgram.ValuesWithin allowed
        (sourceTransientValueBound tm candidate) initial)
    (hwriteSubset : writeFootprint regs ⊆ allowed)
    (haddressCapacity :
      2 ^ SearchProgram.footprintLimit controller regs.footprint ≤
        sourceTransientValueBound tm candidate)
    (hframe :
      SearchProgram.InputFrame
        controller regs.footprint input initial) :
    ∃ final steps,
      InvariantRuns
        (NeighborhoodProgram.ValuesWithin allowed
          (sourceTransientValueBound tm candidate))
        (sourceChunk tm order regs) initial final steps ∧
      SourceChunkPost regs input
        (Residue.sourceValue tm input blockLength
          (FiniteEncoding.ofStateOrder order blockLength)
          (hcanonical ▸
            NeighborhoodGraph.WorkspaceAccounting.blockLength_pos
              candidate)
          tape block chunk)
        initial final := by
  let cap := sourceTransientValueBound tm candidate
  let domain :=
    CandidateParameters.domainSize tm.Q workTapeCount candidate
  let chunkBits :=
    PrimeGrouped.Logarithmic.chunkBits
      (payloadWidth tm blockLength)
      (graphFanIn workTapeCount)
  have hpositive : 0 < blockLength := by
    simpa [hcanonical] using
      NeighborhoodGraph.WorkspaceAccounting.blockLength_pos
        candidate
  have hgamma : Fintype.card Γ = 4 := by
    decide
  have hpayload :
      payloadWidth tm blockLength =
        CandidateParameters.booleanWidth tm.Q candidate := by
    simp [payloadWidth, ComputationGraph.CompactEncoding.width,
      CandidateParameters.booleanWidth,
      NeighborhoodGraph.WorkspaceAccounting.booleanWidth,
      hcanonical, ComputationGraph.CompactEncoding.Coordinate,
      hgamma]
    omega
  have hchunkBitsCanonical :
      chunkBits =
        CandidateParameters.chunkBits
          tm.Q workTapeCount candidate := by
    dsimp [chunkBits]
    rw [hpayload]
    rfl
  have hdomainPow : domain = 2 ^ chunkBits := by
    rw [hchunkBitsCanonical]
    rfl
  have hbooleanDomain :
      CandidateParameters.booleanWidth tm.Q candidate <
        domain := by
    simpa [domain] using
      CandidateParameters.RadixBounds.booleanWidth_lt_domainSize
        tm.Q workTapeCount candidate
  have hblockLengthDomain : blockLength < domain := by
    have hbound :=
      CandidateParameters.RadixBounds.blockLength_lt_domainSize
        tm.Q workTapeCount candidate
    simpa [domain, hcanonical] using hbound
  have hhorizonDomain :
      NeighborhoodGraph.WorkspaceAccounting.horizon candidate <
        domain := by
    simpa [domain] using
      CandidateParameters.RadixBounds.horizon_lt_domainSize
        tm.Q workTapeCount candidate
  have honeDomain : 1 < domain := by
    simpa [domain] using
      CandidateParameters.RadixBounds.one_lt_domainSize
        tm.Q workTapeCount candidate
  have hblockDomain : block < domain :=
    hblockBound.trans_lt
      (max_lt hhorizonDomain honeDomain)
  have hchunkBitsDomain : chunkBits < domain := by
    rw [hdomainPow]
    exact
      (Nat.lt_two_pow_self :
        chunkBits < 2 ^ chunkBits)
  have hchunkCountLe :
      PrimeGrouped.Logarithmic.chunkCount
          (payloadWidth tm blockLength)
          (graphFanIn workTapeCount) ≤
        payloadWidth tm blockLength :=
    GroupedExtension.LogarithmicParameters.chunkCount_le_payloadWidth
      _ _
  have hchunkDomain : chunk.val < domain := by
    exact chunk.isLt.trans_le
      (hchunkCountLe.trans (hpayload ▸ hbooleanDomain.le))
  have hfanDomain :
      CandidateParameters.fanIn workTapeCount < domain := by
    simpa [domain] using
      CandidateParameters.RadixBounds.fanIn_lt_domainSize
        tm.Q workTapeCount candidate
  have htapeCountDomain :
      tapeCount workTapeCount < domain := by
    change 4 * tapeCount workTapeCount < domain at hfanDomain
    omega
  have htapeDomain : tape.val < domain :=
    tape.isLt.trans htapeCountDomain
  have hupperDomain :
      Fintype.card tm.Q + 5 * blockLength < domain := by
    simpa [CandidateParameters.booleanWidth,
      NeighborhoodGraph.WorkspaceAccounting.booleanWidth,
      hcanonical] using hbooleanDomain
  have hdomainSquareCap :
      16 * domain ^ 2 ≤ cap := by
    simpa [domain, cap] using
      canonicalDomainSquare_le_sourceTransientValueBound
        tm candidate
  have hdomainCap : domain ≤ cap := by
    nlinarith only [hdomainSquareCap, honeDomain]
  have htapeCountCap :
      tapeCount workTapeCount ≤ cap := by
    omega
  have htapeBlockCap :
      tapeBlockCode workTapeCount tape.val block ≤ cap := by
    unfold tapeBlockCode
    nlinarith only [hdomainSquareCap, htapeDomain,
      htapeCountDomain, hblockDomain]
  have hblockTapeCountCap :
      block * tapeCount workTapeCount ≤ cap := by
    nlinarith only [hdomainSquareCap, hblockDomain,
      htapeCountDomain]
  have hstateCap : Fintype.card tm.Q ≤ cap := by
    omega
  have hfiveBlockCap : 5 * blockLength ≤ cap := by
    omega
  have hupperCap :
      Fintype.card tm.Q + 5 * blockLength ≤ cap := by
    omega
  have hlowerCap :
      Fintype.card tm.Q + blockLength ≤ cap := by
    omega
  have hchunkProductCap :
      chunk.val * chunkBits ≤ cap := by
    nlinarith only [hdomainSquareCap, hchunkDomain,
      hchunkBitsDomain]
  have hchunkCoordinateCap :
      chunk.val * chunkBits + chunkBits ≤ cap := by
    nlinarith only [hdomainSquareCap, hchunkDomain,
      hchunkBitsDomain]
  have hblockProductCap :
      block * blockLength ≤ cap := by
    nlinarith only [hdomainSquareCap, hblockDomain,
      hblockLengthDomain]
  have haddressMaxCap :
      block * blockLength +
          (chunk.val * chunkBits + chunkBits) / 4 ≤
        cap := by
    have hdiv :
        (chunk.val * chunkBits + chunkBits) / 4 ≤
          chunk.val * chunkBits + chunkBits :=
      Nat.div_le_self _ _
    nlinarith only [hdomainSquareCap, hblockDomain,
      hblockLengthDomain, hchunkDomain, hchunkBitsDomain,
      hdiv]
  have hchunkBitsCap : chunkBits ≤ cap := by
    omega
  have hfiveCap : 5 ≤ cap := by
    nlinarith only [hdomainSquareCap, honeDomain]
  have hradixCap : 2 ^ chunkBits ≤ cap := by
    rw [← hdomainPow]
    exact hdomainCap
  have hlimitSucc :
      SearchProgram.footprintLimit controller regs.footprint + 1 ≤
        cap :=
    (succ_le_two_pow _).trans haddressCapacity
  have hinputCap : input.length ≤ cap :=
    hinput.trans <|
      by
        simpa [cap] using
          candidate_le_sourceTransientValueBound tm candidate
  have hinitialWriteValues :
      ∀ address ∈ writeFootprint regs,
        initial address ≤ cap := by
    intro address haddress
    exact hvalues address (hwriteSubset haddress)
  let afterTapeCount :=
    Basic.exec
      (.imm (packedTapeBlock regs)
        (tapeCount workTapeCount))
      initial
  have hafterTapeCountRun :
      InvariantRuns
        (NeighborhoodProgram.ValuesWithin allowed cap)
        (.basic
          (.imm (packedTapeBlock regs)
            (tapeCount workTapeCount)))
        initial afterTapeCount 1 := by
    exact imm_invariantRuns allowed cap
      (packedTapeBlock regs) (tapeCount workTapeCount)
      initial hvalues htapeCountCap
  have hafterTapeCount :
      NeighborhoodProgram.ValuesWithin allowed cap
        afterTapeCount :=
    InvariantRuns.final hafterTapeCountRun
  let afterBlock :=
    Basic.exec
      (.mul (packedTapeBlock regs)
        (ControlDecode.nodePayload0 regs)
        (packedTapeBlock regs))
      afterTapeCount
  have hpackedBlock :
      packedTapeBlock regs ≠
        ControlDecode.nodePayload0 regs :=
    regs.injective.ne (by decide)
  have hafterBlockValue :
      afterTapeCount (ControlDecode.nodePayload0 regs) *
          afterTapeCount (packedTapeBlock regs) ≤
        cap := by
    simpa [afterTapeCount, Basic.exec, hpackedBlock.symm,
      hblock] using hblockTapeCountCap
  have hafterBlockRun :
      InvariantRuns
        (NeighborhoodProgram.ValuesWithin allowed cap)
        (.basic
          (.mul (packedTapeBlock regs)
            (ControlDecode.nodePayload0 regs)
            (packedTapeBlock regs)))
        afterTapeCount afterBlock 1 := by
    exact mul_invariantRuns allowed cap
      (packedTapeBlock regs)
      (ControlDecode.nodePayload0 regs)
      (packedTapeBlock regs) afterTapeCount
      hafterTapeCount hafterBlockValue
  have hafterBlock :
      NeighborhoodProgram.ValuesWithin allowed cap afterBlock :=
    InvariantRuns.final hafterBlockRun
  let packed :=
    Basic.exec
      (.add (packedTapeBlock regs)
        (ControlDecode.nodeTape regs)
        (packedTapeBlock regs))
      afterBlock
  have hpackedTape :
      packedTapeBlock regs ≠ ControlDecode.nodeTape regs :=
    regs.injective.ne (by decide)
  have hpackedValue :
      packed (packedTapeBlock regs) =
        tapeBlockCode workTapeCount tape.val block := by
    simp [packed, afterBlock, afterTapeCount, Basic.exec,
      hpackedTape.symm, hpackedBlock.symm, htape, hblock,
      tapeBlockCode]
    rw [Nat.mul_comm]
  have hafterPackedValue :
      afterBlock (ControlDecode.nodeTape regs) +
          afterBlock (packedTapeBlock regs) ≤
        cap := by
    simpa [afterBlock, afterTapeCount, Basic.exec,
      hpackedTape.symm, hpackedBlock.symm, htape, hblock,
      tapeBlockCode, Nat.mul_comm] using htapeBlockCap
  have hpackedRun :
      InvariantRuns
        (NeighborhoodProgram.ValuesWithin allowed cap)
        (.basic
          (.add (packedTapeBlock regs)
            (ControlDecode.nodeTape regs)
            (packedTapeBlock regs)))
        afterBlock packed 1 := by
    exact add_invariantRuns allowed cap
      (packedTapeBlock regs)
      (ControlDecode.nodeTape regs)
      (packedTapeBlock regs) afterBlock hafterBlock
      hafterPackedValue
  have hpackedWithin :
      NeighborhoodProgram.ValuesWithin allowed cap packed :=
    InvariantRuns.final hpackedRun
  have hpackedRadix :
      packed (Layout.chunkRadix regs) =
        2 ^ chunkBits := by
    have hradixPacked :
        Layout.chunkRadix regs ≠ packedTapeBlock regs :=
      regs.injective.ne (by decide)
    simp [packed, afterBlock, afterTapeCount, Basic.exec,
      hradixPacked, chunkBits, hradix]
  obtain ⟨recovered, recoverSteps, hrecoverRun,
      hrecoveredChunkBits, _hrecoveredWord,
      _hrecoveredTest, _hrecoveredBase,
      _hrecoveredBasePred, hrecoveredOne,
      hrecoverOutside⟩ :=
    recoverChunkBits_invariantRuns regs allowed cap packed
      chunkBits hpackedRadix hradixCap hchunkBitsCap
      (by omega) hpackedWithin
  let afterRemaining :=
    Function.update recovered (remaining regs)
      (recovered (recoveredChunkBits regs))
  have hremainingRun :
      InvariantRuns
        (NeighborhoodProgram.ValuesWithin allowed cap)
        (copy (remaining regs) (recoveredChunkBits regs))
        recovered afterRemaining 2 := by
    exact copy_invariantRuns allowed cap
      (remaining regs) (recoveredChunkBits regs) recovered
      (regs.injective.ne (by decide))
      (by
        rw [hrecoveredChunkBits]
        exact hchunkBitsCap)
      (InvariantRuns.final hrecoverRun)
  have hcacheRecover :
      controller.prefixCache ∉ recoverFootprint regs := by
    intro hmember
    rcases Finset.mem_union.mp hmember with hmember | hmember
    · rcases Finset.mem_image.mp hmember with
        ⟨slot, _, heq⟩
      exact
        (regs.index_ne_controller (inputMap slot) 16)
          (by simpa using heq)
    · rw [Finset.mem_singleton] at hmember
      exact
        (regs.index_ne_controller 21 16)
          hmember.symm
  have hcachePacked :
      packed controller.prefixCache =
        initial controller.prefixCache := by
    have hcacheTape :
        controller.prefixCache ≠ packedTapeBlock regs := by
      change controller.index 16 ≠ regs.index 20
      exact (regs.index_ne_controller 20 16).symm
    simp [packed, afterBlock, afterTapeCount, Basic.exec,
      hcacheTape]
  have hcacheRecovered :
      recovered controller.prefixCache =
        initial controller.prefixCache := by
    rw [hrecoverOutside controller.prefixCache hcacheRecover]
    exact hcachePacked
  have hcacheRemaining :
      afterRemaining controller.prefixCache =
        initial controller.prefixCache := by
    have hne : controller.prefixCache ≠ remaining regs := by
      change controller.index 16 ≠ regs.index 30
      exact (regs.index_ne_controller 30 16).symm
    simp [afterRemaining, hne, hcacheRecovered]
  have hprefixValueCap :
      SearchProgram.prefixCacheValue controller input
          (SearchProgram.footprintLimit
            controller regs.footprint) ≤
        cap := by
    let limit :=
      SearchProgram.footprintLimit controller regs.footprint
    have hlt :
        SearchProgram.prefixCacheValue controller input limit <
          2 ^ limit := by
      rw [InputLookup.prefixCacheValue_eq_packedPrefix
        controller input limit (footprintLimit_positive regs)]
      exact InputLookup.packedPrefix_lt_pow input limit
    exact hlt.le.trans haddressCapacity
  have hcacheRemainingCap :
      afterRemaining controller.prefixCache ≤ cap := by
    rw [hcacheRemaining, hframe.1]
    exact hprefixValueCap
  let afterWord :=
    Function.update afterRemaining
      (inputRegisters regs).word
      (afterRemaining controller.prefixCache)
  have hwordRun :
      InvariantRuns
        (NeighborhoodProgram.ValuesWithin allowed cap)
        (copy (inputRegisters regs).word
          controller.prefixCache)
        afterRemaining afterWord 2 := by
    exact copy_invariantRuns allowed cap
      (inputRegisters regs).word controller.prefixCache
      afterRemaining
      (by
        change regs.index 29 ≠ controller.index 16
        exact regs.index_ne_controller 29 16)
      hcacheRemainingCap (InvariantRuns.final hremainingRun)
  let ready :=
    Basic.exec (.imm (operand regs) 0) afterWord
  have hoperandRun :
      InvariantRuns
        (NeighborhoodProgram.ValuesWithin allowed cap)
        (.basic (.imm (operand regs) 0))
        afterWord ready 1 :=
    imm_invariantRuns allowed cap (operand regs) 0
      afterWord (InvariantRuns.final hwordRun) (by omega)
  have hsetupRun :
      InvariantRuns
        (NeighborhoodProgram.ValuesWithin allowed cap)
        (Cmd.seqList
          [.basic
            (.imm (packedTapeBlock regs)
              (tapeCount workTapeCount)),
            .basic
              (.mul (packedTapeBlock regs)
                (ControlDecode.nodePayload0 regs)
                (packedTapeBlock regs)),
            .basic
              (.add (packedTapeBlock regs)
                (ControlDecode.nodeTape regs)
                (packedTapeBlock regs)),
            recoverChunkBits regs,
            copy (remaining regs) (recoveredChunkBits regs),
            copy (inputRegisters regs).word
              controller.prefixCache,
            .basic (.imm (operand regs) 0)])
        initial ready (1 + (1 + (1 +
          (recoverSteps + (2 + (2 + 1)))))) := by
    simpa [Cmd.seqList, afterTapeCount, afterBlock, packed,
      afterRemaining, afterWord, ready] using
      InvariantRuns.seq hafterTapeCountRun
        (InvariantRuns.seq hafterBlockRun
          (InvariantRuns.seq hpackedRun
            (InvariantRuns.seq hrecoverRun
              (InvariantRuns.seq hremainingRun
                (InvariantRuns.seq hwordRun hoperandRun)))))
  have hrecoverWithin :
      RAM.Structured.Footprint.CmdWritesWithin
        (writeFootprint regs) (recoverChunkBits regs) := by
    apply cmdWritesWithin_mono _ <|
      recoverChunkBits_writesWithin_local regs
    intro address haddress
    rcases Finset.mem_union.mp haddress with haddress | haddress
    · exact inputFootprint_subset regs haddress
    · rw [Finset.mem_singleton.mp haddress]
      simpa using writeMap_mem regs (14 : Fin 16)
  have hsetupWrites :
      RAM.Structured.Footprint.CmdWritesWithin
        (writeFootprint regs)
        (Cmd.seqList
          [.basic
            (.imm (packedTapeBlock regs)
              (tapeCount workTapeCount)),
            .basic
              (.mul (packedTapeBlock regs)
                (ControlDecode.nodePayload0 regs)
                (packedTapeBlock regs)),
            .basic
              (.add (packedTapeBlock regs)
                (ControlDecode.nodeTape regs)
                (packedTapeBlock regs)),
            recoverChunkBits regs,
            copy (remaining regs) (recoveredChunkBits regs),
            copy (inputRegisters regs).word
              controller.prefixCache,
            .basic (.imm (operand regs) 0)]) := by
    have hpacked := writeMap_mem regs (13 : Fin 16)
    have hremaining := writeMap_mem regs (15 : Fin 16)
    have hword :=
      inputIndex_mem_writeFootprint regs (0 : Fin 12)
    have hoperand := writeMap_mem regs (12 : Fin 16)
    change packedTapeBlock regs ∈ writeFootprint regs at hpacked
    change remaining regs ∈ writeFootprint regs at hremaining
    change
      (inputRegisters regs).word ∈ writeFootprint regs at hword
    change operand regs ∈ writeFootprint regs at hoperand
    simp [Cmd.seqList, copy,
      RAM.Structured.Footprint.CmdWritesWithin,
      RAM.Structured.Footprint.BasicWritesWithin,
      hpacked, hremaining, hword, hoperand, hrecoverWithin]
  have hsetupTrial :
      RAM.Structured.Footprint.CmdWritesWithin
        regs.footprint
        (Cmd.seqList
          [.basic
            (.imm (packedTapeBlock regs)
              (tapeCount workTapeCount)),
            .basic
              (.mul (packedTapeBlock regs)
                (ControlDecode.nodePayload0 regs)
                (packedTapeBlock regs)),
            .basic
              (.add (packedTapeBlock regs)
                (ControlDecode.nodeTape regs)
                (packedTapeBlock regs)),
            recoverChunkBits regs,
            copy (remaining regs) (recoveredChunkBits regs),
            copy (inputRegisters regs).word
              controller.prefixCache,
            .basic (.imm (operand regs) 0)]) :=
    cmdWritesWithin_mono
      (writeFootprint_subset_trial_internal regs) hsetupWrites
  have hreadyFrame :
      SearchProgram.InputFrame
        controller regs.footprint input ready :=
    NeighborhoodTrial.Registers.runs_preserves_inputFrame
      regs hsetupTrial (InvariantRuns.toRuns hsetupRun) hframe
  have hreadyInputLength :
      ready controller.inputLength = input.length := by
    calc
      ready controller.inputLength =
          initial controller.inputLength := by
        apply NeighborhoodTrial.Registers.runs_preserves_controller_index
          regs hsetupTrial (InvariantRuns.toRuns hsetupRun)
        · decide
        · decide
        · decide
      _ = input.length := hinputLength
  have hrecoveredPacked :
      recovered (packedTapeBlock regs) =
        tapeBlockCode workTapeCount tape.val block := by
    rw [hrecoverOutside]
    · exact hpackedValue
    · exact layoutIndex_not_mem_recoverFootprint regs 20
        (by decide) (by decide)
  have hreadyPacked :
      ready (packedTapeBlock regs) =
        tapeBlockCode workTapeCount tape.val block := by
    have hpackedRemaining :
        packedTapeBlock regs ≠ remaining regs :=
      regs.injective.ne (by decide)
    have hpackedWord :
        packedTapeBlock regs ≠ (inputRegisters regs).word :=
      layoutIndex_ne_inputIndex regs 20 0 (by decide)
    have hpackedOperand :
        packedTapeBlock regs ≠ operand regs :=
      regs.injective.ne (by decide)
    simp [ready, afterWord, afterRemaining, Basic.exec,
      hpackedRemaining, hpackedWord, hpackedOperand,
      hrecoveredPacked]
  have hrecoveredCursor :
      recovered (Layout.codecScratch regs) = chunk.val := by
    rw [hrecoverOutside]
    · have hpackedCursor :
          Layout.codecScratch regs ≠ packedTapeBlock regs :=
        regs.injective.ne (by decide)
      simp [packed, afterBlock, afterTapeCount, Basic.exec,
        hpackedCursor, hcursor]
    · exact layoutIndex_not_mem_recoverFootprint regs 31
        (by decide) (by decide)
  have hreadyCursor :
      ready (Layout.codecScratch regs) = chunk.val := by
    have hcursorRemaining :
        Layout.codecScratch regs ≠ remaining regs :=
      regs.injective.ne (by decide)
    have hcursorWord :
        Layout.codecScratch regs ≠
          (inputRegisters regs).word :=
      layoutIndex_ne_inputIndex regs 31 0 (by decide)
    have hcursorOperand :
        Layout.codecScratch regs ≠ operand regs :=
      regs.injective.ne (by decide)
    simp [ready, afterWord, afterRemaining, Basic.exec,
      hcursorRemaining, hcursorWord, hcursorOperand,
      hrecoveredCursor]
  have hrecoveredBlockLength :
      recovered (Layout.blockLength regs) = blockLength := by
    rw [hrecoverOutside]
    · have hblockPacked :
          Layout.blockLength regs ≠ packedTapeBlock regs :=
        regs.injective.ne (by decide)
      simp [packed, afterBlock, afterTapeCount, Basic.exec,
        hblockPacked, hblockLength]
    · exact layoutIndex_not_mem_recoverFootprint regs 2
        (by decide) (by decide)
  have hreadyBlockLength :
      ready (Layout.blockLength regs) = blockLength := by
    have hblockRemaining :
        Layout.blockLength regs ≠ remaining regs :=
      regs.injective.ne (by decide)
    have hblockWord :
        Layout.blockLength regs ≠
          (inputRegisters regs).word :=
      layoutIndex_ne_inputIndex regs 2 0 (by decide)
    have hblockOperand :
        Layout.blockLength regs ≠ operand regs :=
      regs.injective.ne (by decide)
    simp [ready, afterWord, afterRemaining, Basic.exec,
      hblockRemaining, hblockWord, hblockOperand,
      hrecoveredBlockLength]
  have hreadyChunkBits :
      ready (recoveredChunkBits regs) = chunkBits := by
    have hchunkRemaining :
        recoveredChunkBits regs ≠ remaining regs :=
      regs.injective.ne (by decide)
    have hchunkWord :
        recoveredChunkBits regs ≠
          (inputRegisters regs).word :=
      recovered_ne_inputIndex regs 0
    have hchunkOperand :
        recoveredChunkBits regs ≠ operand regs :=
      regs.injective.ne (by decide)
    simp [ready, afterWord, afterRemaining, Basic.exec,
      hchunkRemaining, hchunkWord, hchunkOperand,
      hrecoveredChunkBits]
  have hreadyRemaining :
      ready (remaining regs) = chunkBits := by
    have hremainingWord :
        remaining regs ≠ (inputRegisters regs).word :=
      layoutIndex_ne_inputIndex regs 30 0 (by decide)
    have hremainingOperand :
        remaining regs ≠ operand regs :=
      regs.injective.ne (by decide)
    simp [ready, afterWord, afterRemaining, Basic.exec,
      hremainingWord, hremainingOperand,
      hrecoveredChunkBits]
  have hreadyOperand :
      ready (operand regs) = 0 := by
    simp [ready, Basic.exec]
  have hreadyWord :
      ready (inputRegisters regs).word =
        SearchProgram.prefixCacheValue controller input
          (SearchProgram.footprintLimit
            controller regs.footprint) := by
    calc
      ready (inputRegisters regs).word =
          ready controller.prefixCache := by
        have hwordOperand :
            (inputRegisters regs).word ≠ operand regs :=
          (layoutIndex_ne_inputIndex regs 19 0
            (by decide)).symm
        have hcacheOperand :
            controller.prefixCache ≠ operand regs := by
          change controller.index 16 ≠ regs.index 19
          exact (regs.index_ne_controller 19 16).symm
        have hcacheRemaining :
            controller.prefixCache ≠ remaining regs := by
          change controller.index 16 ≠ regs.index 30
          exact (regs.index_ne_controller 30 16).symm
        have hcacheWord :
            controller.prefixCache ≠
              (inputRegisters regs).word := by
          change controller.index 16 ≠ regs.index 29
          exact (regs.index_ne_controller 29 16).symm
        simp [ready, afterWord, afterRemaining, Basic.exec,
          hwordOperand, hcacheOperand, hcacheRemaining,
          hcacheWord]
      _ = SearchProgram.prefixCacheValue controller input
          (SearchProgram.footprintLimit
            controller regs.footprint) :=
        hreadyFrame.1
  have hreadyOne :
      ready (inputRegisters regs).one = 1 := by
    have honeRemaining :
        (inputRegisters regs).one ≠ remaining regs :=
      (layoutIndex_ne_inputIndex regs 30 6 (by decide)).symm
    have honeWord :
        (inputRegisters regs).one ≠
          (inputRegisters regs).word :=
      (inputRegisters regs).index_ne (by decide)
    have honeOperand :
        (inputRegisters regs).one ≠ operand regs :=
      (layoutIndex_ne_inputIndex regs 19 6 (by decide)).symm
    simp [ready, afterWord, afterRemaining, Basic.exec,
      honeRemaining, honeWord, honeOperand, hrecoveredOne]
  obtain ⟨final, loopSteps, hloopRun, _hloopOperand,
      _hloopRemaining, _hloopPacked, _hloopChunkBits,
      _hloopCursor, _hloopBlockLength, _hloopWord,
      _hloopOne, _hloopInputLength, _hloopFrame⟩ :=
    sourceChunkLoop_invariantRuns tm order regs input
      allowed cap blockLength tape.val block chunk.val
      chunkBits chunkBits 0 ready tape.isLt le_rfl
      hreadyBlockLength hreadyPacked hreadyCursor
      hreadyChunkBits hreadyRemaining hreadyOperand
      hreadyWord hreadyOne hreadyInputLength
      htapeBlockCap htapeCountCap hstateCap
      hfiveBlockCap hupperCap hlowerCap
      hchunkProductCap hchunkCoordinateCap
      hblockProductCap haddressMaxCap hchunkBitsCap
      (by simpa using hradixCap) hfiveCap hlimitSucc
      haddressCapacity (InvariantRuns.final hsetupRun)
      hreadyFrame
  have hinvariantExists :
      ∃ steps,
        InvariantRuns
          (NeighborhoodProgram.ValuesWithin allowed cap)
          (sourceChunk tm order regs) initial final steps := by
    refine
      ⟨1 + (1 + (1 +
        (recoverSteps + (2 + (2 + (1 + loopSteps)))))), ?_⟩
    simpa [sourceChunk, Cmd.seqList, afterTapeCount,
      afterBlock, packed, afterRemaining, afterWord, ready] using
      InvariantRuns.seq hafterTapeCountRun
        (InvariantRuns.seq hafterBlockRun
          (InvariantRuns.seq hpackedRun
            (InvariantRuns.seq hrecoverRun
              (InvariantRuns.seq hremainingRun
                (InvariantRuns.seq hwordRun
                  (InvariantRuns.seq hoperandRun hloopRun))))))
  obtain ⟨totalSteps, hinvariant⟩ := hinvariantExists
  obtain ⟨semanticFinal, hsemanticRun, hpost⟩ :=
    sourceChunk_runs_internal tm order regs input blockLength
      hpositive tape block chunk initial htape hblock
      hblockLength hradix hcursor hinputLength hframe
  have heq : final = semanticFinal :=
    runs_final_eq (InvariantRuns.toRuns hinvariant) hsemanticRun
  subst semanticFinal
  refine
    ⟨final, totalSteps, ?_, ?_⟩
  · simpa [cap] using hinvariant
  · simpa using hpost

theorem sourceChunk_fixedCap_invariantRuns_canonical_internal
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (input : List Bool) (candidate blockLength : ℕ)
    (hcanonical :
      blockLength =
        NeighborhoodGraph.WorkspaceAccounting.blockLength candidate)
    (hinput : input.length ≤ candidate)
    (tape : TapeIndex workTapeCount) (block : ℕ)
    (hblockBound :
      block ≤
        max
          (NeighborhoodGraph.WorkspaceAccounting.horizon candidate)
          1)
    (chunk :
      Fin
        (PrimeGrouped.Logarithmic.chunkCount
          (payloadWidth tm blockLength)
          (graphFanIn workTapeCount)))
    (allowed : Finset ℕ) (initial : Store)
    (htape :
      initial
          (ControlDecode.nodeTape
            NeighborhoodTrial.Registers.canonical) =
        tape.val)
    (hblock :
      initial
          (ControlDecode.nodePayload0
            NeighborhoodTrial.Registers.canonical) =
        block)
    (hblockLength :
      initial
          (Layout.blockLength
            NeighborhoodTrial.Registers.canonical) =
        blockLength)
    (hradix :
      initial
          (Layout.chunkRadix
            NeighborhoodTrial.Registers.canonical) =
        2 ^
          PrimeGrouped.Logarithmic.chunkBits
            (payloadWidth tm blockLength)
            (graphFanIn workTapeCount))
    (hcursor :
      initial
          (Layout.codecScratch
            NeighborhoodTrial.Registers.canonical) =
        chunk.val)
    (hinputLength :
      initial SearchProgram.Registers.canonical.inputLength =
        input.length)
    (hvalues :
      NeighborhoodProgram.ValuesWithin allowed
        (sourceTransientValueBound tm candidate) initial)
    (hwriteSubset :
      writeFootprint NeighborhoodTrial.Registers.canonical ⊆
        allowed)
    (hframe :
      SearchProgram.InputFrame
        SearchProgram.Registers.canonical
        NeighborhoodTrial.Registers.canonical.footprint
        input initial) :
    ∃ final steps,
      InvariantRuns
        (NeighborhoodProgram.ValuesWithin allowed
          (sourceTransientValueBound tm candidate))
        (sourceChunk tm order
          NeighborhoodTrial.Registers.canonical)
        initial final steps ∧
      SourceChunkPost NeighborhoodTrial.Registers.canonical input
        (Residue.sourceValue tm input blockLength
          (FiniteEncoding.ofStateOrder order blockLength)
          (hcanonical ▸
            NeighborhoodGraph.WorkspaceAccounting.blockLength_pos
              candidate)
          tape block chunk)
        initial final := by
  exact
    sourceChunk_fixedCap_invariantRuns_internal tm order
      NeighborhoodTrial.Registers.canonical input candidate
      blockLength hcanonical hinput tape block hblockBound chunk
      allowed initial htape hblock hblockLength hradix hcursor
      hinputLength hvalues hwriteSubset
      (canonical_addressCapacity tm candidate) hframe

theorem sourceChunk_invariantRuns_internal
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (regs : NeighborhoodTrial.Registers controller)
    (input : List Bool) (blockLength : ℕ)
    (hpositive : 0 < blockLength)
    (tape : TapeIndex workTapeCount) (block : ℕ)
    (chunk :
      Fin
        (PrimeGrouped.Logarithmic.chunkCount
          (payloadWidth tm blockLength)
          (graphFanIn workTapeCount)))
    (allowed : Finset ℕ) (lowerBound : ℕ)
    (initial : Store)
    (htape :
      initial (ControlDecode.nodeTape regs) = tape.val)
    (hblock :
      initial (ControlDecode.nodePayload0 regs) = block)
    (hblockLength :
      initial (Layout.blockLength regs) = blockLength)
    (hradix :
      initial (Layout.chunkRadix regs) =
        2 ^
          PrimeGrouped.Logarithmic.chunkBits
            (payloadWidth tm blockLength)
            (graphFanIn workTapeCount))
    (hcursor :
      initial (Layout.codecScratch regs) = chunk.val)
    (hinputLength :
      initial controller.inputLength = input.length)
    (hframe :
      SearchProgram.InputFrame
        controller regs.footprint input initial) :
    ∃ final bound steps,
      lowerBound ≤ bound ∧
      InvariantRuns
        (NeighborhoodProgram.ValuesWithin allowed bound)
        (sourceChunk tm order regs) initial final steps ∧
      SourceChunkPost regs input
        (Residue.sourceValue tm input blockLength
          (FiniteEncoding.ofStateOrder order blockLength)
          hpositive tape block chunk)
        initial final := by
  obtain ⟨final, hrun, hpost⟩ :=
    sourceChunk_runs_internal tm order regs input blockLength
      hpositive tape block chunk initial htape hblock hblockLength
      hradix hcursor hinputLength hframe
  obtain ⟨bound, steps, hlower, hinvariant⟩ :=
    runs_exists_valuesWithin_invariantRuns
      allowed lowerBound hrun
  exact
    ⟨final, bound, steps, hlower, hinvariant, hpost⟩

theorem failureChunk_runs_internal
    (tm : TM workTapeCount) (blockLength : ℕ)
    (chunk :
      Fin
        (PrimeGrouped.Logarithmic.chunkCount
          (payloadWidth tm blockLength)
          (graphFanIn workTapeCount)))
    (regs : NeighborhoodTrial.Registers controller)
    (input : List Bool) (initial : Store)
    (hframe :
      SearchProgram.InputFrame
        controller regs.footprint input initial) :
    ∃ final,
      Runs (failureChunk regs) initial final ∧
      SourceChunkPost regs input
        (Residue.failureValue tm blockLength chunk)
        initial final := by
  let final := Basic.exec (.imm (operand regs) 0) initial
  have hrun : Runs (failureChunk regs) initial final := by
    simpa [failureChunk, final] using
      Runs.basic (.imm (operand regs) 0) initial
  have hvalue :
      final (operand regs) =
        Residue.failureValue tm blockLength chunk := by
    simp [final, Basic.exec, Residue.failureValue,
      Residue.zeroValue, PrimeField.Runtime.normalize]
  exact
    ⟨final, hrun,
      post_of_run regs input _ (failureChunk_writesWithin_internal regs)
        hrun hframe hvalue⟩

theorem failureChunk_invariantRuns_internal
    (tm : TM workTapeCount) (blockLength : ℕ)
    (chunk :
      Fin
        (PrimeGrouped.Logarithmic.chunkCount
          (payloadWidth tm blockLength)
          (graphFanIn workTapeCount)))
    (regs : NeighborhoodTrial.Registers controller)
    (input : List Bool) (allowed : Finset ℕ)
    (lowerBound : ℕ) (initial : Store)
    (hframe :
      SearchProgram.InputFrame
        controller regs.footprint input initial) :
    ∃ final bound steps,
      lowerBound ≤ bound ∧
      InvariantRuns
        (NeighborhoodProgram.ValuesWithin allowed bound)
        (failureChunk regs) initial final steps ∧
      SourceChunkPost regs input
        (Residue.failureValue tm blockLength chunk)
        initial final := by
  obtain ⟨final, hrun, hpost⟩ :=
    failureChunk_runs_internal tm blockLength chunk regs input
      initial hframe
  obtain ⟨bound, steps, hlower, hinvariant⟩ :=
    runs_exists_valuesWithin_invariantRuns
      allowed lowerBound hrun
  exact
    ⟨final, bound, steps, hlower, hinvariant, hpost⟩

theorem failureChunk_invariantRuns_at_internal
    (tm : TM workTapeCount) (blockLength : ℕ)
    (chunk :
      Fin
        (PrimeGrouped.Logarithmic.chunkCount
          (payloadWidth tm blockLength)
          (graphFanIn workTapeCount)))
    (regs : NeighborhoodTrial.Registers controller)
    (input : List Bool) (allowed : Finset ℕ)
    (bound : ℕ) (initial : Store)
    (hvalues :
      NeighborhoodProgram.ValuesWithin allowed bound initial)
    (hframe :
      SearchProgram.InputFrame
        controller regs.footprint input initial) :
    ∃ final,
      InvariantRuns
        (NeighborhoodProgram.ValuesWithin allowed bound)
        (failureChunk regs) initial final 1 ∧
      SourceChunkPost regs input
        (Residue.failureValue tm blockLength chunk)
        initial final := by
  let final := Basic.exec (.imm (operand regs) 0) initial
  have hfinalValues :
      NeighborhoodProgram.ValuesWithin allowed bound final := by
    intro address haddress
    by_cases heq : address = operand regs
    · subst address
      simp [final, Basic.exec]
    · simpa [final, Basic.exec, Function.update_of_ne, heq] using
        hvalues address haddress
  have hinvariant :
      InvariantRuns
        (NeighborhoodProgram.ValuesWithin allowed bound)
        (failureChunk regs) initial final 1 := by
    simpa [failureChunk, final] using
      InvariantRuns.basic (.imm (operand regs) 0)
        initial hvalues hfinalValues
  have hrun : Runs (failureChunk regs) initial final :=
    InvariantRuns.toRuns hinvariant
  have hvalue :
      final (operand regs) =
        Residue.failureValue tm blockLength chunk := by
    simp [final, Basic.exec, Residue.failureValue,
      Residue.zeroValue, PrimeField.Runtime.normalize]
  exact
    ⟨final, hinvariant,
      post_of_run regs input _
        (failureChunk_writesWithin_internal regs)
        hrun hframe hvalue⟩

end Internal
end SourceValue
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
