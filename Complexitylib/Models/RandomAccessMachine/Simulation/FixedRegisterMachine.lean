/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.Models.RandomAccessMachine.Simulation.FixedRegisterMachine.Defs
import
  Complexitylib.Models.RandomAccessMachine.Simulation.FixedRegisterMachine.Internal

/-!
# Direct fixed-register RAM simulation

This module exposes the representation boundary for a RAM compiler that gives
every register in a fixed program-dependent prefix its own work tape. Runtime
indirect loads select one of those tapes or fall back to the immutable input
bank. The number of tapes depends on the fixed source program, while the space
on each tape is linear in the current RAM word width.
-/

namespace Complexity
namespace RAM
namespace FixedRegisterMachine

open RegisterStore DenseOverlay
open DenseOverlay.FixedRegisters.Footprint

/-- A direct-write footprint excludes indirect stores. -/
theorem programNoStore_of_writesWithin
    {program : Program} {allowed : Finset ℕ}
    (hwrites : ProgramWritesWithin program allowed) :
    ProgramNoStore program :=
  Internal.programNoStore_of_writesWithin_internal hwrites

/-- Build a direct-register compiler specification from any finite mutable
footprint containing R0. The exclusive register bound is inferred
automatically from the footprint and every hardwired program operand. -/
noncomputable def Spec.ofFootprint
    {program : Program} (allowed : Finset ℕ)
    (hzero : 0 ∈ allowed)
    (hwrites : ProgramWritesWithin program allowed) :
    Spec program where
  allowed := allowed
  registerBound := compilationRegisterBound program allowed
  zero_mem := hzero
  writesWithin := hwrites
  noStore := programNoStore_of_writesWithin hwrites
  allowed_lt :=
    Internal.allowed_lt_compilationRegisterBound_internal program allowed
  registersBelow :=
    Internal.programRegistersBelow_compilationRegisterBound_internal
      program allowed

@[simp]
theorem registerTape_val {program : Program} (spec : Spec program)
    (address : ℕ) (haddress : address < spec.registerBound) :
    (registerTape spec address haddress).val = address :=
  Internal.registerTape_val_internal spec address haddress

@[simp]
theorem scratchTape_val {program : Program} (spec : Spec program)
    (slot : Fin scratchCount) :
    (scratchTape spec slot).val = spec.registerBound + slot.val :=
  Internal.scratchTape_val_internal spec slot

/-- Distinct bounded register addresses have distinct direct tapes. -/
theorem registerTape_injective {program : Program}
    (spec : Spec program) {first second : ℕ}
    (hfirst : first < spec.registerBound)
    (hsecond : second < spec.registerBound)
    (heq : registerTape spec first hfirst =
      registerTape spec second hsecond) :
    first = second :=
  Internal.registerTape_injective_internal spec hfirst hsecond heq

/-- Direct register tapes and shared scratch tapes are disjoint. -/
theorem registerTape_ne_scratchTape {program : Program}
    (spec : Spec program) (address : ℕ)
    (haddress : address < spec.registerBound)
    (slot : Fin scratchCount) :
    registerTape spec address haddress ≠ scratchTape spec slot :=
  Internal.registerTape_ne_scratchTape_internal spec address haddress slot

/-- Distinct scratch roles have distinct tapes. -/
theorem scratchTape_injective {program : Program}
    (spec : Spec program) {first second : Fin scratchCount}
    (heq : scratchTape spec first = scratchTape spec second) :
    first = second :=
  Internal.scratchTape_injective_internal spec heq

/-- The canonical direct tape decodes to its advertised natural number. -/
theorem natTape_hasBinaryNat (value : ℕ) :
    (natTape value).HasBinaryNat value :=
  Internal.natTape_hasBinaryNat_internal value

/-- The canonical direct tape is parked at its reusable boundary. -/
theorem natTape_parked (value : ℕ) :
    TM.Parked (natTape value) :=
  Internal.natTape_parked_internal value

/-- The direct prefix is nonempty because R0 belongs to the advertised
mutable footprint. -/
theorem registerBound_pos {program : Program} (spec : Spec program) :
    0 < spec.registerBound :=
  Internal.registerBound_pos_internal spec

/-- The canonical endpoint of fixed-prefix materialization represents the
ordinary public-ABI initial RAM snapshot. -/
theorem prefixInitWork_ready_initial {program : Program}
    (spec : Spec program) (input : List Bool) :
    Ready spec input (DenseOverlay.Snapshot.initial input)
      (prefixInitWork spec input (prefixInitTime spec)) :=
  Internal.prefixInitWork_ready_initial_internal spec input

/-- The fixed-prefix pass reaches its canonical endpoint in exactly one
transition per positive direct register. -/
theorem prefixInitTM_reachesIn {program : Program}
    (spec : Spec program) (input : List Bool) :
    (prefixInitTM spec).reachesIn (prefixInitTime spec)
      (prefixInitCfg spec input 0)
      (prefixInitCfg spec input (prefixInitTime spec)) :=
  Internal.prefixInitTM_reachesIn_internal spec input

/-- Every prefix of fixed-prefix materialization uses one work-tape cell.
Its program-dependent number of transitions is not charged as space. -/
theorem prefixInitTM_prefix_withinAuxSpace {program : Program}
    (spec : Spec program) (input : List Bool)
    (time : ℕ) (current : Complexity.Cfg
      (workTapeCount spec) (prefixInitTM spec).Q)
    (hreach : (prefixInitTM spec).reachesIn time
      (prefixInitCfg spec input 0) current)
    (htime : time ≤ prefixInitTime spec) :
    current.WithinAuxSpace input.length 1 :=
  Internal.prefixInitTM_prefix_withinAuxSpace_internal spec input time
    current hreach htime

/-- Exact time-and-space contract for fixed-prefix materialization from its
rewound canonical boundary. -/
theorem prefixInitTM_hoareTimeSpace {program : Program}
    (spec : Spec program) (input : List Bool) :
    (prefixInitTM spec).HoareTimeSpace
      (fun inp work out =>
        inp = prefixInitInput input 0 ∧
        work = prefixInitWork spec input 0 ∧
        out = natTape 0)
      (fun inp work out =>
        inp = prefixInitInput input (prefixInitTime spec) ∧
        work = prefixInitWork spec input (prefixInitTime spec) ∧
        Ready spec input (DenseOverlay.Snapshot.initial input) work ∧
        out = natTape 0)
      (prefixInitTime spec) input.length 1 :=
  Internal.prefixInitTM_hoareTimeSpace_internal spec input

/-- The concrete fresh-start initializer establishes the direct-register
representation. Its growing auxiliary space is exactly the logarithmic input
length counter; input rewind and materialization preserve that bound. -/
theorem initializeTM_hoareTimeSpace {program : Program}
    (spec : Spec program) (input : List Bool) :
    (initializeTM spec).HoareTimeSpace
      (fun inp work out =>
        inp = Tape.init (input.map Γ.ofBool) ∧
        work = (fun _ => Tape.init []) ∧ out = Tape.init [])
      (fun inp work out =>
        inp = prefixInitInput input (prefixInitTime spec) ∧
        work = prefixInitWork spec input (prefixInitTime spec) ∧
        Ready spec input (DenseOverlay.Snapshot.initial input) work ∧
        out = natTape 0)
      (initializeTime spec input.length) input.length
      (initializeSpace spec input.length) :=
  Internal.initializeTM_hoareTimeSpace_internal spec input

/-- The canonical work image satisfies the direct-register boundary
representation. -/
theorem snapshotWork_ready {program : Program}
    (spec : Spec program) (input : List Bool)
    (snapshot : DenseOverlay.Snapshot) :
    Ready spec input snapshot (snapshotWork spec input snapshot) :=
  Internal.snapshotWork_ready_internal spec input snapshot

@[simp]
theorem readRoute_eq_direct {registerBound address : ℕ}
    (haddress : address < registerBound) :
    readRoute registerBound address = .inl ⟨address, haddress⟩ :=
  Internal.readRoute_eq_direct_internal haddress

@[simp]
theorem readRoute_eq_fallback {registerBound address : ℕ}
    (haddress : registerBound ≤ address) :
    readRoute registerBound address = .inr () :=
  Internal.readRoute_eq_fallback_internal haddress

/-- On a covered overlay, finite direct dispatch plus immutable-input fallback
agrees with the ordinary dense-overlay register read at every address. -/
theorem routedRead_eq_denseRead
    {program : Program} (spec : Spec program)
    (input : List Bool) (snapshot : DenseOverlay.Snapshot)
    (hcovered : Covered snapshot.overlay spec.allowed)
    (address : ℕ) :
    routedRead input snapshot spec.registerBound address =
      DenseOverlay.read input snapshot.overlay address :=
  Internal.routedRead_eq_denseRead_internal spec input snapshot hcovered address

/-- Exact-time semantic contract for the concrete direct/fallback routed-read
machine. The selector and result endpoints are canonical, and every other
tape is preserved. -/
theorem readDispatchTM_hoareTime
    {program : Program} (spec : Spec program)
    (input : List Bool) (snapshot : DenseOverlay.Snapshot)
    (address : ℕ)
    (work₀ : Fin (workTapeCount spec) → Tape) (out₀ : Tape)
    (hready : ReadTreeReady spec input snapshot address address work₀)
    (houtput : TM.Parked out₀) :
    (readDispatchTM spec).HoareTime
      (fun inp work out =>
        inp = executionInput input ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = executionInput input ∧
        work =
          Function.update
            (Function.update work₀ (selectorTape spec) (natTape 0))
            (resultTape spec)
            (natTape
              (routedRead input snapshot spec.registerBound address)) ∧
        out = out₀)
      (readDispatchTime spec input snapshot address) :=
  Internal.readDispatchTM_hoareTime_internal spec input snapshot address
    work₀ out₀ hready houtput

/-- A fixed direct-register compiler decides every language whose dense
execution has a length-uniform word-width trace bound. The number of work
tapes is fixed by `spec`; only the maximum live word width is charged
asymptotically. -/
theorem programTM_decidesInSpace_traceBound
    {program : Program} (spec : Spec program) (L : Language)
    (wordBits : ℕ → ℕ)
    (hrun : ∀ input, ∃ fuel,
      let final :=
        (DenseOverlay.Snapshot.initial input).run program input fuel
      final.Halted program ∧
      DenseOverlay.FixedRegisters.TraceBound
        program input fuel spec.allowed.card (wordBits input.length) ∧
      (input ∈ L → DenseOverlay.read input final.overlay 0 = 1) ∧
      (input ∉ L → DenseOverlay.read input final.overlay 0 = 0)) :
    (programTM spec).DecidesInSpace L
      (fun n => max (initializeSpace spec n)
        (instructionSpace (wordBits n))) :=
  Internal.programTM_decidesInSpace_traceBound_internal
    spec L wordBits hrun

@[simp]
theorem controlPC_val_of_lt {program : Program} {pc : ℕ}
    (hpc : pc < program.length) :
    (controlPC program pc).val = pc :=
  Internal.controlPC_val_of_lt_internal hpc

@[simp]
theorem controlPC_val_of_ge {program : Program} {pc : ℕ}
    (hpc : program.length ≤ pc) :
    (controlPC program pc).val = program.length :=
  Internal.controlPC_val_of_ge_internal hpc

end FixedRegisterMachine
end RAM
end Complexity
