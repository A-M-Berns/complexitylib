/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.ChildNode.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.ChildNode.Internal

/-!
# Fixed-register child-node regeneration

This surface exposes exact arithmetic, footprint, and scheduler-semantic
theorems for complete recursive child regeneration.
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace ChildNode

open RAM Structured

variable {controller : SearchProgram.Registers}

/-- Recursive ternary suffix agrees with ordinary division by a power. -/
theorem ternarySuffix_eq_div_pow
    (word count : ℕ) :
    ternarySuffix word count = word / 3 ^ count :=
  Internal.ternarySuffix_eq_div_pow_internal word count

/-- The pure endpoint of concrete lookup is the standard packed digit. -/
theorem movementDigitValue_eq_digit
    (word index : ℕ) :
    movementDigitValue word index =
      PackedDigits.digit 3 word index :=
  Internal.movementDigitValue_eq_digit_internal word index

/-- Runtime ternary lookup decodes exactly the movement used by
`Enumeration.candidateGuess`. -/
theorem movementDigitValue_candidateGuess
    (code :
      Fin
        (3 ^
          NeighborhoodGraph.Guess.Enumeration.movementCount
            workTapeCount horizon))
    (interval : Fin horizon)
    (tape : TapeIndex workTapeCount) :
    NeighborhoodGraph.Guess.Enumeration.moveOfDigit
        (movementDigitValue code.val
          (interval.val * (workTapeCount + 2) + tape.val)) =
      (NeighborhoodGraph.Guess.Enumeration.candidateGuess code).movement
        interval tape :=
  Internal.movementDigitValue_candidateGuess_internal
    code interval tape

/-- The pure center scan agrees with the typed candidate guess at every
in-horizon boundary. -/
theorem derivedCenterValue_candidateGuess
    (code :
      Fin
        (3 ^
          NeighborhoodGraph.Guess.Enumeration.movementCount
            workTapeCount horizon))
    (tape : TapeIndex workTapeCount)
    (boundary : ℕ) (hboundary : boundary ≤ horizon) :
    derivedCenterValue workTapeCount code.val tape.val boundary =
      (NeighborhoodGraph.Guess.Enumeration.candidateGuess code).derivedCenter
        tape boundary :=
  Internal.derivedCenterValue_candidateGuess_internal
    code tape boundary hboundary

/-- On a valid current prefix, the numeric backward search is exactly the
candidate guess's greatest-prior-neighborhood query, including the matching
center needed to choose the predecessor slot. -/
theorem priorSearchValue_candidateGuess
    (code :
      Fin
        (3 ^
          NeighborhoodGraph.Guess.Enumeration.movementCount
            workTapeCount horizon))
    (tape : TapeIndex workTapeCount)
    (requested interval current : ℕ)
    (hinterval : interval ≤ horizon)
    (hcurrent :
      derivedCenterValue workTapeCount code.val tape.val interval =
        some current) :
    priorSearchValue
        workTapeCount code.val tape.val requested interval =
      match
        NeighborhoodGraph.Guess.CenterGuess.previousInterval
          (NeighborhoodGraph.Guess.Enumeration.candidateGuess code)
          tape requested interval with
      | none => some none
      | some previous =>
          match
            NeighborhoodGraph.Guess.CenterGuess.derivedCenter
              (NeighborhoodGraph.Guess.Enumeration.candidateGuess code)
              tape previous.val with
          | none => none
          | some center => some (some (previous.val, center)) :=
  Internal.priorSearchValue_candidateGuess_internal
    code tape requested interval current hinterval hcurrent

/-- Content-query assembly agrees exactly with the candidate guess's
option-valued content predecessor. -/
theorem priorQueryValue_candidateGuess
    (code :
      Fin
        (3 ^
          NeighborhoodGraph.Guess.Enumeration.movementCount
            workTapeCount horizon))
    (tape : TapeIndex workTapeCount)
    (slot : NeighborhoodGraph.Slot)
    (interval : ℕ) (hinterval : interval < horizon)
    (current : ℕ)
    (hcurrent :
      derivedCenterValue workTapeCount code.val tape.val interval =
        some current) :
    priorQueryValue
        (horizon := horizon) tape
        (NeighborhoodGraph.neighborBlock current slot)
        (priorSearchValue
          workTapeCount code.val tape.val
          (NeighborhoodGraph.neighborBlock current slot) interval) =
      match
        NeighborhoodGraph.Guess.CenterGuess.contentPredecessor?
          (NeighborhoodGraph.Guess.Enumeration.candidateGuess code)
          ⟨interval, hinterval⟩ tape slot with
      | none => .failure
      | some node => .graph node :=
  Internal.priorQueryValue_candidateGuess_internal
    code tape slot interval hinterval current hcurrent

/-- The same content query is exactly the candidate guess's fixed-Fin
predecessor oracle at the role-major content index. -/
theorem priorQueryValue_predecessorAt
    (code :
      Fin
        (3 ^
          NeighborhoodGraph.Guess.Enumeration.movementCount
            workTapeCount horizon))
    (tape : TapeIndex workTapeCount)
    (slot : NeighborhoodGraph.Slot)
    (interval : ℕ) (hinterval : interval < horizon)
    (current : ℕ)
    (hcurrent :
      derivedCenterValue workTapeCount code.val tape.val interval =
        some current) :
    priorQueryValue
        (horizon := horizon) tape
        (NeighborhoodGraph.neighborBlock current slot)
        (priorSearchValue
          workTapeCount code.val tape.val
          (NeighborhoodGraph.neighborBlock current slot) interval) =
      match
        NeighborhoodGraph.Guess.CenterGuess.predecessorAt?
          (NeighborhoodGraph.Guess.Enumeration.candidateGuess code)
          ⟨interval, hinterval⟩
          (NeighborhoodGraph.predecessorIndexEquiv workTapeCount
            (.content slot, tape)) with
      | none => .failure
      | some node => .graph node :=
  Internal.priorQueryValue_predecessorAt_internal
    code tape slot interval hinterval current hcurrent

/-- The content branch is the exact evaluator child at its role-major
predecessor index. -/
theorem priorQueryValue_childAt
    (code :
      Fin
        (3 ^
          NeighborhoodGraph.Guess.Enumeration.movementCount
            workTapeCount horizon))
    (parentTape tape : TapeIndex workTapeCount)
    (parentSlot slot : NeighborhoodGraph.Slot)
    (interval : ℕ) (hinterval : interval < horizon)
    (current : ℕ)
    (hcurrent :
      derivedCenterValue workTapeCount code.val tape.val interval =
        some current) :
    priorQueryValue
        (horizon := horizon) tape
        (NeighborhoodGraph.neighborBlock current slot)
        (priorSearchValue
          workTapeCount code.val tape.val
          (NeighborhoodGraph.neighborBlock current slot) interval) =
      NeighborhoodEvaluator.childAt
        (NeighborhoodGraph.Guess.Enumeration.candidateGuess code)
        (.graph
          (.computation parentTape parentSlot interval))
        (NeighborhoodGraph.predecessorIndexEquiv workTapeCount
          (.content slot, tape)) :=
  Internal.priorQueryValue_childAt_internal
    code parentTape tape parentSlot slot interval hinterval current hcurrent

/-- The same exact content-branch statement at the scheduler-frame API
boundary. -/
theorem priorQueryValue_frameChild
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (code :
      Fin
        (3 ^
          NeighborhoodGraph.Guess.Enumeration.movementCount
            workTapeCount instanceData.horizon))
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (parentTape tape : TapeIndex workTapeCount)
    (parentSlot slot : NeighborhoodGraph.Slot)
    (interval : ℕ)
    (hinterval : interval < instanceData.horizon)
    (current : ℕ)
    (hcurrent :
      derivedCenterValue
          workTapeCount code.val tape.val interval =
        some current)
    (hguess :
      instanceData.guess =
        NeighborhoodGraph.Guess.Enumeration.candidateGuess code)
    (hnode :
      frame.node =
        .graph (.computation parentTape parentSlot interval)) :
    priorQueryValue
        (horizon := instanceData.horizon) tape
        (NeighborhoodGraph.neighborBlock current slot)
        (priorSearchValue
          workTapeCount code.val tape.val
          (NeighborhoodGraph.neighborBlock current slot) interval) =
      NeighborhoodScheduler.Frame.childNode frame
        (NeighborhoodGraph.predecessorIndexEquiv workTapeCount
          (.content slot, tape)) :=
  Internal.priorQueryValue_frameChild_internal
    code frame parentTape tape parentSlot slot interval hinterval current
    hcurrent hguess hnode

/-- Chronological query assembly agrees exactly with the candidate guess's
option-valued chronological predecessor. -/
theorem chronologicalQueryValue_candidateGuess
    (code :
      Fin
        (3 ^
          NeighborhoodGraph.Guess.Enumeration.movementCount
            workTapeCount horizon))
    (tape : TapeIndex workTapeCount)
    (interval : ℕ) (hinterval : interval < horizon)
    (result : Option ℕ)
    (hresult :
      derivedCenterValue workTapeCount code.val tape.val interval =
        result) :
    chronologicalQueryValue
        (horizon := horizon) tape interval result =
      match
        NeighborhoodGraph.Guess.CenterGuess.chronologicalPredecessor?
          (NeighborhoodGraph.Guess.Enumeration.candidateGuess code)
          ⟨interval, hinterval⟩ tape with
      | none => .failure
      | some node => .graph node :=
  Internal.chronologicalQueryValue_candidateGuess_internal
    code tape interval hinterval result hresult

/-- The chronological branch is the exact evaluator child at the
role-major chronological predecessor index. -/
theorem chronologicalQueryValue_childAt
    (code :
      Fin
        (3 ^
          NeighborhoodGraph.Guess.Enumeration.movementCount
            workTapeCount horizon))
    (parentTape tape : TapeIndex workTapeCount)
    (parentSlot : NeighborhoodGraph.Slot)
    (interval : ℕ) (hinterval : interval < horizon)
    (result : Option ℕ)
    (hresult :
      derivedCenterValue workTapeCount code.val tape.val interval =
        result) :
    chronologicalQueryValue
        (horizon := horizon) tape interval result =
      NeighborhoodEvaluator.childAt
        (NeighborhoodGraph.Guess.Enumeration.candidateGuess code)
        (.graph
          (.computation parentTape parentSlot interval))
        (NeighborhoodGraph.predecessorIndexEquiv workTapeCount
          (.chronological, tape)) :=
  Internal.chronologicalQueryValue_childAt_internal
    code parentTape tape parentSlot interval hinterval result hresult

/-- The same exactness statement at the scheduler-frame API boundary. -/
theorem chronologicalQueryValue_frameChild
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (code :
      Fin
        (3 ^
          NeighborhoodGraph.Guess.Enumeration.movementCount
            workTapeCount instanceData.horizon))
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (parentTape tape : TapeIndex workTapeCount)
    (parentSlot : NeighborhoodGraph.Slot)
    (interval : ℕ)
    (hinterval : interval < instanceData.horizon)
    (result : Option ℕ)
    (hresult :
      derivedCenterValue
          workTapeCount code.val tape.val interval =
        result)
    (hguess :
      instanceData.guess =
        NeighborhoodGraph.Guess.Enumeration.candidateGuess code)
    (hnode :
      frame.node =
        .graph (.computation parentTape parentSlot interval)) :
    chronologicalQueryValue
        (horizon := instanceData.horizon) tape interval result =
      NeighborhoodScheduler.Frame.childNode frame
        (NeighborhoodGraph.predecessorIndexEquiv workTapeCount
          (.chronological, tape)) :=
  Internal.chronologicalQueryValue_frameChild_internal
    code frame parentTape tape parentSlot interval hinterval result
    hresult hguess hnode

/-- Ternary digit lookup writes only its six time-multiplexed cells. -/
theorem movementDigit_writesWithin
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (movementFootprint regs)
      (movementDigit controller regs) :=
  Internal.movementDigit_writesWithin_internal controller regs

/-- Every ternary lookup cell belongs to the shared evaluator layout. -/
theorem movementFootprint_subset_layout
    (regs : NeighborhoodTrial.Registers controller) :
    movementFootprint regs ⊆ regs.layout.footprint :=
  Internal.movementFootprint_subset_layout_internal regs

/-- The concrete lookup terminates with the exact selected little-endian
ternary digit and preserves every address outside its six-cell footprint. -/
theorem movementDigit_runs
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store) (word index : ℕ)
    (hguess : store controller.guess = word)
    (hindex : store (movementIndex regs) = index) :
    ∃ final,
      Runs (movementDigit controller regs) store final ∧
      MovementDigitPost controller regs word index store final :=
  Internal.movementDigit_runs_internal
    controller regs store word index hguess hindex

/-- Predecessor-cursor decoding writes only the shared six-cell arithmetic
footprint. -/
theorem decodeChildIndex_writesWithin
    (workTapeCount : ℕ)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (movementFootprint regs)
      (decodeChildIndex workTapeCount regs) :=
  Internal.decodeChildIndex_writesWithin_internal
    workTapeCount regs

/-- Role-major predecessor decoding computes the exact named-tape
remainder and predecessor-kind quotient. -/
theorem decodeChildIndex_runs
    (workTapeCount child : ℕ)
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store)
    (hchild : store (savedChildIndex regs) = child) :
    ∃ final,
      Runs (decodeChildIndex workTapeCount regs) store final ∧
      ChildIndexPost workTapeCount child regs store final :=
  Internal.decodeChildIndex_runs_internal
    workTapeCount child regs store hchild

/-- Rebuilding node fields writes only the packed-node destination and one
transient immediate cell. -/
theorem encodeNodeFields_writesWithin
    (regs : NeighborhoodTrial.Registers controller)
    (tag : ℕ) :
    Footprint.CmdWritesWithin (nodeEncodingFootprint regs)
      (encodeNodeFields regs tag) :=
  Internal.encodeNodeFields_writesWithin_internal regs tag

/-- Both node-encoder destinations belong to the evaluator layout. -/
theorem nodeEncodingFootprint_subset_layout
    (regs : NeighborhoodTrial.Registers controller) :
    nodeEncodingFootprint regs ⊆ regs.layout.footprint :=
  Internal.nodeEncodingFootprint_subset_layout_internal regs

/-- Straight-line node encoding terminates with the exact four-field radix
numeral and preserves every other address. -/
theorem encodeNodeFields_runs
    (regs : NeighborhoodTrial.Registers controller)
    (tag : ℕ) (store : Store) :
    ∃ final,
      Runs (encodeNodeFields regs tag) store final ∧
      EncodeNodeFieldsPost regs tag store final :=
  Internal.encodeNodeFields_runs_internal regs tag store

/-- Center-prefix reconstruction writes only its eleven time-multiplexed
workspace cells. -/
theorem deriveCenter_writesWithin
    (workTapeCount : ℕ)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (centerFootprint regs)
      (deriveCenter workTapeCount controller regs) :=
  Internal.deriveCenter_writesWithin_internal
    workTapeCount controller regs

/-- Every center-prefix scratch cell belongs to the shared evaluator layout. -/
theorem centerFootprint_subset_layout
    (regs : NeighborhoodTrial.Registers controller) :
    centerFootprint regs ⊆ regs.layout.footprint :=
  Internal.centerFootprint_subset_layout_internal regs

/-- The concrete center-prefix loop terminates with the exact option-valued
center decoded from the packed movement word. -/
theorem deriveCenter_runs
    (workTapeCount : ℕ)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store) (word tape interval : ℕ)
    (hguess : store controller.guess = word)
    (htape : store (ControlDecode.nodeTape regs) = tape)
    (hinterval :
      store (ControlDecode.nodePayload1 regs) = interval) :
    ∃ final,
      Runs (deriveCenter workTapeCount controller regs) store final ∧
      DeriveCenterPost workTapeCount word tape interval
        controller regs store final :=
  Internal.deriveCenter_runs_internal
    workTapeCount controller regs store word tape interval
    hguess htape hinterval

/-- Backward greatest-prior scanning writes only its fixed local scratch
allocation and the shared interval field used for candidate testing. -/
theorem scanPrior_writesWithin
    (workTapeCount : ℕ)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (priorFootprint regs)
      (scanPrior workTapeCount controller regs) :=
  Internal.scanPrior_writesWithin_internal
    workTapeCount controller regs

/-- Every greatest-prior scan cell belongs to the shared evaluator layout. -/
theorem priorFootprint_subset_layout
    (regs : NeighborhoodTrial.Registers controller) :
    priorFootprint regs ⊆ regs.layout.footprint :=
  Internal.priorFootprint_subset_layout_internal regs

/-- Testing one valid candidate for neighborhood containment stays inside
the fixed predecessor-search footprint. -/
theorem recordPriorIfContains_writesWithin
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (priorFootprint regs)
      (recordPriorIfContains regs) :=
  Internal.recordPriorIfContains_writesWithin_internal regs

/-- The containment test records exactly the current candidate when its
three-block neighborhood contains the requested block. -/
theorem recordPriorIfContains_runs
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store)
    (center requested candidate countdown word tape : ℕ)
    (hcenter : store (centerValue regs) = center)
    (hrequested : store (requestedBlock regs) = requested)
    (hcandidate :
      store (ControlDecode.nodePayload1 regs) = candidate)
    (hcountdown : store (priorCountdown regs) = countdown)
    (hfound : store (priorFound regs) = 0)
    (hinterval : store (priorInterval regs) = 0)
    (hpriorCenter : store (priorCenter regs) = 0)
    (hvalid : store (centerValid regs) = 1)
    (hone : store (movementDivision regs).one = 1)
    (htape : store (ControlDecode.nodeTape regs) = tape)
    (hguess : store controller.guess = word) :
    ∃ final,
      Runs (recordPriorIfContains regs) store final ∧
      RecordPriorIfContainsPost regs center requested candidate
        countdown word tape final :=
  Internal.recordPriorIfContains_runs_internal
    controller regs store center requested candidate countdown word tape
    hcenter hrequested hcandidate hcountdown hfound hinterval
    hpriorCenter hvalid hone htape hguess

/-- The descending local scan returns the greatest earlier valid guessed
neighborhood containing the requested block, or distinguishes absence from
an invalid movement prefix. -/
theorem scanPrior_runs
    (workTapeCount : ℕ)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store) (word tape requested interval : ℕ)
    (hguess : store controller.guess = word)
    (htape : store (ControlDecode.nodeTape regs) = tape)
    (hrequested : store (requestedBlock regs) = requested)
    (hinterval :
      store (ControlDecode.nodePayload1 regs) = interval) :
    ∃ final,
      Runs (scanPrior workTapeCount controller regs) store final ∧
      ScanPriorPost workTapeCount word tape requested interval
        controller regs store final :=
  Internal.scanPrior_runs_internal
    workTapeCount controller regs store word tape requested interval
    hguess htape hrequested hinterval

/-- Content-result installation writes only the predecessor scratch,
selected tape field, and two node-encoder destinations. -/
theorem installPrior_writesWithin
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (priorAssemblyFootprint regs)
      (installPrior regs) :=
  Internal.installPrior_writesWithin_internal regs

/-- The scan-and-install content branch has the same fixed write
footprint. -/
theorem scanAndInstallPrior_writesWithin
    (workTapeCount : ℕ)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (priorAssemblyFootprint regs)
      (scanAndInstallPrior workTapeCount controller regs) :=
  Internal.scanAndInstallPrior_writesWithin_internal
    workTapeCount controller regs

/-- Every content-result installation cell belongs to the shared evaluator
layout. -/
theorem priorAssemblyFootprint_subset_layout
    (regs : NeighborhoodTrial.Registers controller) :
    priorAssemblyFootprint regs ⊆ regs.layout.footprint :=
  Internal.priorAssemblyFootprint_subset_layout_internal regs

/-- The concrete three-way content installer produces the exact packed
failure, source, or matching prior computation node. -/
theorem installPrior_runs
    {horizon : ℕ}
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store)
    (tape : TapeIndex workTapeCount) (requested : ℕ)
    (result : Option (Option (ℕ × ℕ)))
    (hvalid :
      store (centerValid regs) = priorValidValue result)
    (hfound :
      store (priorFound regs) = priorFoundValue result)
    (hinterval :
      store (priorInterval regs) = priorIntervalValue result)
    (hcenter :
      store (priorCenter regs) = priorCenterValue result)
    (htape : store (ControlDecode.nodeTape regs) = tape.val)
    (hrequested : store (requestedBlock regs) = requested)
    (hone : store (movementDivision regs).one = 1)
    (hcontains :
      ∀ interval center,
        result = some (some (interval, center)) →
          NeighborhoodGraph.NeighborhoodContains center requested) :
    ∃ final,
      Runs (installPrior regs) store final ∧
      InstallPriorPost tape requested result regs store final :=
  Internal.installPrior_runs_internal
    (horizon := horizon) regs store tape requested result
    hvalid hfound hinterval hcenter htape hrequested hone hcontains

/-- End-to-end content regeneration scans the packed movement guess and
installs exactly the role-major scheduler child selected by `Frame.childNode`. -/
theorem scanAndInstallPrior_frameChild_runs
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (code :
      Fin
        (3 ^
          NeighborhoodGraph.Guess.Enumeration.movementCount
            workTapeCount instanceData.horizon))
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store)
    (parentTape tape : TapeIndex workTapeCount)
    (parentSlot slot : NeighborhoodGraph.Slot)
    (interval : ℕ)
    (hinterval : interval < instanceData.horizon)
    (current : ℕ)
    (hcurrent :
      derivedCenterValue
          workTapeCount code.val tape.val interval =
        some current)
    (hstoreGuess : store controller.guess = code.val)
    (htape : store (ControlDecode.nodeTape regs) = tape.val)
    (hrequested :
      store (requestedBlock regs) =
        NeighborhoodGraph.neighborBlock current slot)
    (hstoreInterval :
      store (ControlDecode.nodePayload1 regs) = interval)
    (hguess :
      instanceData.guess =
        NeighborhoodGraph.Guess.Enumeration.candidateGuess code)
    (hnode :
      frame.node =
        .graph (.computation parentTape parentSlot interval)) :
    ∃ final,
      Runs
        (scanAndInstallPrior workTapeCount controller regs)
        store final ∧
      final (Layout.nodeCode regs) =
        FrameCodec.encodeNode
          (store (Layout.chunkRadix regs))
          (NeighborhoodScheduler.Frame.childNode frame
            (NeighborhoodGraph.predecessorIndexEquiv workTapeCount
              (.content slot, tape))) ∧
      final (Layout.codecDigit regs) = 0 ∧
      ∀ address, address ∉ priorAssemblyFootprint regs →
        final address = store address :=
  Internal.scanAndInstallPrior_frameChild_runs_internal
    code frame controller regs store parentTape tape parentSlot slot
    interval hinterval current hcurrent hstoreGuess htape hrequested
    hstoreInterval hguess hnode

/-- Generic child regeneration stays within the same fixed content-assembly
footprint. -/
theorem regenerateChild_writesWithin
    (workTapeCount : ℕ)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (priorAssemblyFootprint regs)
      (regenerateChild workTapeCount controller regs) :=
  Internal.regenerateChild_writesWithin_internal
    workTapeCount controller regs

/-- From decoded computation fields and a saved role-major cursor, the
generic RAM dispatcher installs exactly the scheduler's selected child. -/
theorem regenerateChild_frameChild_runs
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (code :
      Fin
        (3 ^
          NeighborhoodGraph.Guess.Enumeration.movementCount
            workTapeCount instanceData.horizon))
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store)
    (parentTape tape : TapeIndex workTapeCount)
    (parentSlot : NeighborhoodGraph.Slot)
    (kind : NeighborhoodGraph.PredecessorKind)
    (interval : ℕ)
    (hinterval : interval < instanceData.horizon)
    (hdecoded :
      ControlDecode.EncodedNodePost regs frame.node store)
    (hchild :
      store (savedChildIndex regs) =
        (NeighborhoodGraph.predecessorIndexEquiv
          workTapeCount (kind, tape)).val)
    (hstoreGuess : store controller.guess = code.val)
    (hguess :
      instanceData.guess =
        NeighborhoodGraph.Guess.Enumeration.candidateGuess code)
    (hnode :
      frame.node =
        .graph (.computation parentTape parentSlot interval)) :
    ∃ final,
      Runs
        (regenerateChild workTapeCount controller regs)
        store final ∧
      final (Layout.nodeCode regs) =
        FrameCodec.encodeNode
          (store (Layout.chunkRadix regs))
          (NeighborhoodScheduler.Frame.childNode frame
            (NeighborhoodGraph.predecessorIndexEquiv
              workTapeCount (kind, tape))) ∧
      final (Layout.codecDigit regs) = 0 ∧
      ∀ address, address ∉ priorAssemblyFootprint regs →
        final address = store address :=
  Internal.regenerateChild_frameChild_runs_internal
    code frame controller regs store parentTape tape parentSlot kind
    interval hinterval hdecoded hchild hstoreGuess hguess hnode

/-- Chronological child installation writes only the predecessor scratch,
selected tape field, and two node-encoder destinations. -/
theorem installChronological_writesWithin
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (chronologicalFootprint regs)
      (installChronological regs) :=
  Internal.installChronological_writesWithin_internal regs

/-- Every chronological installation cell belongs to the shared evaluator
layout. -/
theorem chronologicalFootprint_subset_layout
    (regs : NeighborhoodTrial.Registers controller) :
    chronologicalFootprint regs ⊆ regs.layout.footprint :=
  Internal.chronologicalFootprint_subset_layout_internal regs

/-- The concrete valid/invalid chronological branch installs exactly the
packed semantic query node and clears its transient encoder digit. -/
theorem installChronological_runs
    {horizon : ℕ}
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store)
    (tape : TapeIndex workTapeCount)
    (interval : ℕ) (result : Option ℕ)
    (hvalid :
      store (centerValid regs) = centerValidValue result)
    (hcenter :
      store (centerValue regs) = centerOutputValue result)
    (htape : store (ControlDecode.nodeTape regs) = tape.val)
    (hinterval :
      store (ControlDecode.nodePayload1 regs) = interval)
    (hone : store (movementDivision regs).one = 1) :
    ∃ final,
      Runs (installChronological regs) store final ∧
      InstallChronologicalPost
        tape interval result regs store final :=
  Internal.installChronological_runs_internal
    (horizon := horizon) controller regs store tape interval result
    hvalid hcenter htape hinterval hone

end ChildNode
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
