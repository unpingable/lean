/-
  Custody-Class: UNRATIFIED-CANDIDATE

  Temporal basis specimen (2026-07-09). Time assurance for the NQ seam,
  formalization leading implementation: this is NQ-T4 of the temporal-basis
  track — the theorem set NQ's doctrine doc, fixtures, and preflight
  verdicts (NQ-T0..T3) are meant to cite, written BEFORE NQ implements
  them. Forcing consumer: NQ (`~/git/nq-root/nq`), whose live doctrine
  already carries the debts this file pins:

    "Present tense requires a live basis. … Retirement is explicit, not
     inferred from silence." (EVIDENCE_RETIREMENT_GAP.md)
    "Freshness is evaluated against `observed_at`, not `generated_at` or
     ingest time." (VERDICTS.md, stale_testimony)
    basis-stale transitions keyed to "the operator-declared freshness
     window" and an authority timestamp — never inferred cadence
     (BASIS_STALE_CONTRACT.md)
    `cannot_testify` is constitutional output, not an error condition
     (VERDICTS.md / CANNOT_TESTIFY_STATUS.md)

  The doctrine, one line: **freshness is not elapsed time; freshness is
  admitted elapsed time under a declared witness contract.** Time is
  testimony. A clock may testify; the profile decides whether the clock may
  be believed for this act.

  The temporal exchange-rate frauds refused here, each a named theorem:

    minted ≠ observed      — a fresh packet does not refresh old testimony
    existed ≠ fresh        — a timestamp proves existence, not current truth
    silence ≠ recovery     — no fresh witness never clears a finding
    late ≠ timely          — completed after the deadline is a refusal fact
    elapsed ≠ revived      — a retired source does not come back with time
    two clocks ≠ an order  — ordering needs a shared or bridged time basis

  Sibling seams, CITED not re-proved: custody hops cannot refresh a
  producer clock (`CustodyFreshnessSpecimen` — that file owns the chain;
  this one owns the packet/witness/contract layer); single-receipt
  metric-time staleness (`Freshness` [1.0]); late-witness completion
  licenses (`DeferredWitness`, ANNEX); silence-shape inequations
  (`ProjectionLaundering`, candidate). NQ's five-state `basis_state`
  lifecycle is NQ's own cut and is deliberately NOT mirrored — this file's
  three-state source lifecycle (live/retired/invalidated) is the minimal
  slice the theorems need, not a wire enum.

  NOT modeled, on purpose: a global trusted clock (unrepresentable — every
  predicate is Profile-indexed; there is no `GlobalTrustedTime` to derive),
  clock-sync protocols (NTP/RFC 3161 verifiers are future adapters emitting
  receipts), schedulability/WCET (admissibility governs reliance on timing
  testimony, never proves the scheduler), NQ's detector/runtime behavior.

  Unwired: not imported by `LeanProofs.lean` or any default target. Build
  directly: `lake build LeanProofs.Admissibility.TemporalBasis`.
  Promotion to ANNEX gates on NQ citing named theorems under its
  `[annex]` pinning discipline (the DeferredWitness precedent — whose
  forcing consumer was also NQ).
-/

/-!
# Temporal Basis

A temporal observation carries who observed (`witness`), what clock family
it read (`basis`), when the substrate was looked at (`observedAt` — the
authority time, possibly absent), and when the packet was minted
(`generatedAt`). A profile admits clock witnesses with declared
uncertainty, declares freshness windows per subject class, records source
lifecycle, and declares clock-basis bridges. The evaluator (`verdictAt`)
returns a typed verdict — `stale` and `cannotTestify` are siblings in one
inductive, not cousins hidden in a string field. The tempting evaluator
(`freshByGeneration` — "the packet is recent") is modeled and refuted by
countermodel, per the house pattern.
-/

namespace Admissibility.TemporalBasis

abbrev Time         := Nat
abbrev Duration     := Nat
abbrev WitnessId    := String
abbrev SubjectClass := String
abbrev ClockBasis   := String

/-! ## Objects -/

/-- A temporal observation: testimony about when, from a witness reading a
    clock basis. `observedAt` is the authority time (when the substrate was
    looked at); `none` models an absent/uncredentialed authority timestamp —
    a `collected_at` is NOT this field unless a contract admits it.
    `generatedAt` is packet-minting time and, per the theorems, buys
    nothing. -/
structure TemporalObservation where
  subject     : String
  witness     : WitnessId
  basis       : ClockBasis
  observedAt  : Option Time
  generatedAt : Time
deriving Repr, DecidableEq

/-- An admitted clock witness: the profile's declaration that this witness,
    on this basis, may testify to time with this declared uncertainty. -/
structure ClockRule where
  witness     : WitnessId
  basis       : ClockBasis
  uncertainty : Duration
deriving Repr, DecidableEq

/-- A declared freshness window for a subject class. Declared, never
    inferred — there is no constructor from cadence to contract. -/
structure FreshnessContract where
  subjectClass : SubjectClass
  window       : Duration
deriving Repr, DecidableEq

/-- Source lifecycle, minimal cut (NOT NQ's `basis_state` wire enum).
    Retirement is explicit; nothing here transitions by time passing. -/
inductive SourceState
  | live
  | retired
  | invalidated
deriving Repr, DecidableEq

structure Profile where
  clocks    : List ClockRule
  contracts : List FreshnessContract
  sources   : List (WitnessId × SourceState)
  bridges   : List (ClockBasis × ClockBasis)
deriving Repr

/-! ## The evaluator -/

/-- Typed temporal verdicts. Siblings, not string reasons: `stale` and
    `cannotTestify` and `unknownAuthorityTime` are distinct constitutional
    outputs, and none of them is `fresh`. -/
inductive TemporalVerdict
  | fresh
  | stale
  | cannotTestify              -- clock witness not admitted by the profile
  | unknownAuthorityTime       -- no admitted authority timestamp
  | uncertaintyTooLarge        -- declared uncertainty exceeds the window
  | windowNotDeclared          -- no freshness contract for this class
  | blockedByRetiredSource
  | blockedByInvalidatedSource
deriving Repr, DecidableEq

def sourceStateOf (p : Profile) (w : WitnessId) : SourceState :=
  match p.sources.find? (fun s => s.1 = w) with
  | some s => s.2
  | none   => SourceState.live

/-- The lawful evaluator. Reads the source lifecycle, the clock admission,
    the declared contract, and the authority timestamp — and provably never
    reads `generatedAt`. -/
def verdictAt (p : Profile) (sc : SubjectClass) (o : TemporalObservation)
    (now : Time) : TemporalVerdict :=
  match sourceStateOf p o.witness with
  | .retired     => .blockedByRetiredSource
  | .invalidated => .blockedByInvalidatedSource
  | .live =>
    match p.clocks.find? (fun c => c.witness = o.witness && c.basis = o.basis) with
    | none => .cannotTestify
    | some rule =>
      match p.contracts.find? (fun fc => fc.subjectClass = sc) with
      | none => .windowNotDeclared
      | some fc =>
        match o.observedAt with
        | none => .unknownAuthorityTime
        | some t =>
          if fc.window < rule.uncertainty then .uncertaintyTooLarge
          else if now ≤ t + fc.window then .fresh
          else .stale

/-- The TEMPTING evaluator — "the packet is recent": freshness read off
    `generatedAt`. The laundering move, given a type so it can be refuted
    by name. Used by nothing. -/
def freshByGeneration (window now : Time) (o : TemporalObservation) : Bool :=
  decide (now ≤ o.generatedAt + window)

/-! ## The inversion (what `fresh` certifies) -/

/-- A `fresh` verdict certifies the whole contract: live source, admitted
    clock witness on the observation's basis, declared window, present
    authority timestamp, tolerable uncertainty, and the window arithmetic.
    Nothing else produces `fresh`. -/
theorem fresh_requires {p sc o now}
    (h : verdictAt p sc o now = .fresh) :
    sourceStateOf p o.witness = .live ∧
    ∃ rule, p.clocks.find? (fun c => c.witness = o.witness && c.basis = o.basis)
        = some rule ∧
    ∃ fc, p.contracts.find? (fun fc => fc.subjectClass = sc) = some fc ∧
    ∃ t, o.observedAt = some t ∧ rule.uncertainty ≤ fc.window ∧
      now ≤ t + fc.window := by
  unfold verdictAt at h
  split at h
  · cases h
  · cases h
  next hlive =>
    split at h
    · cases h
    next rule hrule =>
      split at h
      · cases h
      next fc hfc =>
        split at h
        · cases h
        next t ht =>
          split at h
          · cases h
          next hunc =>
            split at h
            next hwin =>
              exact ⟨hlive, rule, hrule, fc, hfc, t, ht,
                Nat.not_lt.mp hunc, hwin⟩
            · cases h

/-! ## minted ≠ observed -/

/-- A fresh packet does not refresh old testimony: the lawful verdict is
    invariant in `generatedAt`. `verdictAt` is a real evaluator over the
    whole observation — this is the proof it has no input path from
    packet-minting time. -/
theorem generated_at_does_not_refresh_observation
    (p : Profile) (sc : SubjectClass) (o : TemporalObservation)
    (now g' : Time) :
    verdictAt p sc { o with generatedAt := g' } now = verdictAt p sc o now := rfl

/-- Old observation, freshly minted packet (observed at t=0, window 100,
    minted at t=999, evaluated at t=1000). -/
def repackagedStale : TemporalObservation :=
  { subject := "svc-a", witness := "clock:mono-01", basis := "host-mono"
  , observedAt := some 0, generatedAt := 999 }

def specimenProfile : Profile :=
  { clocks    := [{ witness := "clock:mono-01", basis := "host-mono"
                  , uncertainty := 5 }]
  , contracts := [{ subjectClass := "runtime-input", window := 100 }]
  , sources   := []
  , bridges   := [] }

/-- Separation: the tempting evaluator blesses the repackaged packet; the
    lawful one refuses. Old observation → new packet → "fresh evidence" is
    refuted by countermodel. Nice try, envelope. -/
theorem repackaging_is_not_freshness :
    freshByGeneration 100 1000 repackagedStale = true ∧
    verdictAt specimenProfile "runtime-input" repackagedStale 1000
      = .stale := by
  constructor <;> decide

/-! ## The refusal corollaries (each surface separately) -/

/-- Stale evidence cannot derive a fresh claim: past the declared window,
    the verdict is never `fresh`. -/
theorem stale_evidence_cannot_derive_fresh_claim {p sc o now t fc}
    (ht : o.observedAt = some t)
    (hfc : p.contracts.find? (fun fc => fc.subjectClass = sc) = some fc)
    (hexp : t + fc.window < now) :
    verdictAt p sc o now ≠ .fresh := by
  intro h
  obtain ⟨_, _, _, fc', hfc', t', ht', _, hwin⟩ := fresh_requires h
  rw [hfc] at hfc'; cases hfc'
  rw [ht] at ht'; cases ht'
  exact Nat.lt_irrefl now (Nat.lt_of_le_of_lt hwin hexp)

/-- A clock the profile has not admitted (for this witness on this basis)
    blocks every time claim. `cannot_testify` is constitutional output. -/
theorem clock_cannot_testify_blocks_time_claim {p sc o now}
    (h : p.clocks.find? (fun c => c.witness = o.witness && c.basis = o.basis)
      = none) :
    verdictAt p sc o now ≠ .fresh := by
  intro hf
  obtain ⟨_, rule, hrule, _⟩ := fresh_requires hf
  rw [h] at hrule; cases hrule

/-- No admitted authority timestamp, no fresh claim — whatever
    `generatedAt` or any custody field says. `collected_at` is not an
    authority timestamp unless a contract admits it as `observedAt`. -/
theorem missing_authority_time_no_fresh_claim {p sc o now}
    (h : o.observedAt = none) : verdictAt p sc o now ≠ .fresh := by
  intro hf
  obtain ⟨_, _, _, _, _, t, ht, _⟩ := fresh_requires hf
  rw [h] at ht; cases ht

/-- Declared uncertainty exceeding the declared window blocks freshness:
    a clock that cannot resolve the window cannot testify to it. -/
theorem uncertainty_exceeding_window_not_fresh {p sc o now rule fc}
    (hrule : p.clocks.find? (fun c => c.witness = o.witness && c.basis = o.basis)
      = some rule)
    (hfc : p.contracts.find? (fun fc => fc.subjectClass = sc) = some fc)
    (hbig : fc.window < rule.uncertainty) :
    verdictAt p sc o now ≠ .fresh := by
  intro hf
  obtain ⟨_, rule', hrule', fc', hfc', _, _, hunc, _⟩ := fresh_requires hf
  rw [hrule] at hrule'; cases hrule'
  rw [hfc] at hfc'; cases hfc'
  exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hbig hunc)

/-- An undeclared window blocks freshness: windows are declared, never
    inferred from cadence or vibes. -/
theorem undeclared_window_not_fresh {p sc o now}
    (h : p.contracts.find? (fun fc => fc.subjectClass = sc) = none) :
    verdictAt p sc o now ≠ .fresh := by
  intro hf
  obtain ⟨_, _, _, fc, hfc, _⟩ := fresh_requires hf
  rw [h] at hfc; cases hfc

/-! ## elapsed ≠ revived -/

/-- A retired source does not come back by time passing: the verdict is
    `blockedByRetiredSource` at EVERY evaluation time. Retirement is
    explicit; only an explicit lifecycle change (a new profile) ends it. -/
theorem retired_source_cannot_become_live_by_time_passing {p o}
    (h : sourceStateOf p o.witness = .retired) (sc : SubjectClass) :
    ∀ now, verdictAt p sc o now = .blockedByRetiredSource := by
  intro now
  simp [verdictAt, h]

/-! ## silence ≠ recovery -/

/-- Finding lifecycle, minimal cut: silence suppresses (preserves with a
    "can't see this right now" banner); it never clears. -/
inductive FindingState
  | active
  | suppressed
  | cleared
deriving Repr, DecidableEq

/-- What silence does: active findings are suppressed, not cleared.
    "Loss of observability reduces confidence; it does not fabricate
    health." -/
def onSilence : FindingState → FindingState
  | .active     => .suppressed
  | .suppressed => .suppressed
  | .cleared    => .cleared

/-- Recovery requires fresh admissible testimony of the clear state —
    the ONLY constructor of `cleared` from a non-cleared state. -/
def onTestimony (v : TemporalVerdict) (st : FindingState) : FindingState :=
  if v = .fresh then .cleared else st

/-- Absence of fresh testimony does not establish a clear state: silence
    never produces `cleared` from a non-cleared finding. -/
theorem silence_does_not_establish_clear {st : FindingState}
    (h : st ≠ .cleared) : onSilence st ≠ .cleared := by
  cases st <;> simp_all [onSilence]

/-- Inversion: a finding that became `cleared` on testimony was cleared by
    a `fresh` verdict, or was already cleared. Stale-to-live requires a
    fresh admissible basis — there is no third door. -/
theorem stale_to_live_requires_fresh_admissible_basis
    {v : TemporalVerdict} {st : FindingState}
    (h : onTestimony v st = .cleared) : v = .fresh ∨ st = .cleared := by
  unfold onTestimony at h
  split at h
  · exact Or.inl (by assumption)
  · exact Or.inr h

/-! ## existed ≠ fresh -/

/-- Existence attestation (RFC 3161-shape): the observation says its
    subject existed no later than `T`. -/
def existedBy (o : TemporalObservation) (T : Time) : Bool :=
  match o.observedAt with
  | some t => decide (t ≤ T)
  | none   => false

/-- Separation: existence attested, freshness refused — on the same
    observation. A timestamp token is custody evidence about the past, not
    authority about the present. The temporal version of "publication is
    not authorization." -/
theorem timestamped_existence_is_not_current_freshness :
    existedBy repackagedStale 0 = true ∧
    verdictAt specimenProfile "runtime-input" repackagedStale 1000
      = .stale := by
  constructor <;> decide

/-! ## late ≠ timely -/

/-- A monitored step against a deadline. `finishedAt = none` = never
    completed. -/
structure StepReport where
  deadline   : Time
  finishedAt : Option Time
deriving Repr, DecidableEq

def completed (r : StepReport) : Bool := r.finishedAt.isSome

def deadlineMet (r : StepReport) : Bool :=
  match r.finishedAt with
  | some f => decide (f ≤ r.deadline)
  | none   => false

/-- Late success is not timely success: one and the same report is
    `completed` AND fails `deadlineMet`. Do not hide a deadline miss as
    "late success" — it is a temporal refusal fact with its own name. -/
theorem late_success_is_not_timely_success {r : StepReport} {f : Time}
    (hf : r.finishedAt = some f) (hlate : r.deadline < f) :
    completed r = true ∧ deadlineMet r = false := by
  refine ⟨by simp [completed, hf], ?_⟩
  simp [deadlineMet, hf, Nat.not_le.mpr hlate]

/-- The degenerate corollary: an incomplete step meets no deadline. -/
theorem incomplete_step_meets_no_deadline {r : StepReport}
    (h : r.finishedAt = none) : deadlineMet r = false := by
  simp [deadlineMet, h]

/-! ## two clocks ≠ an order -/

/-- Ordering between two observations is established only on a shared clock
    basis or an explicitly bridged pair — and then by authority times. -/
def orderingEstablished (p : Profile) (a b : TemporalObservation) : Bool :=
  (decide (a.basis = b.basis) ||
    p.bridges.any fun br => decide (br.1 = a.basis) && decide (br.2 = b.basis)) &&
  match a.observedAt, b.observedAt with
  | some ta, some tb => decide (ta < tb)
  | _, _             => false

/-- Two clocks are not an order: with distinct bases and no declared
    bridge, ordering is not established — whatever the timestamps say.
    Numbers from different clocks do not compare by looking numeric. -/
theorem cross_basis_ordering_not_established {p : Profile}
    {a b : TemporalObservation} (hne : a.basis ≠ b.basis)
    (hbr : ∀ br ∈ p.bridges, ¬(br.1 = a.basis ∧ br.2 = b.basis)) :
    orderingEstablished p a b = false := by
  have hor : (decide (a.basis = b.basis) ||
      p.bridges.any fun br =>
        decide (br.1 = a.basis) && decide (br.2 = b.basis)) = false := by
    rw [Bool.or_eq_false_iff]
    refine ⟨by simp [hne], ?_⟩
    rw [List.any_eq_false]
    intro br hbrmem
    have := hbr br hbrmem
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    intro hcontra
    exact this hcontra
  simp [orderingEstablished, hor]

/-- Missing authority time on either side blocks ordering — packets without
    admitted timestamps do not order, even on one basis. -/
theorem no_authority_time_no_ordering {p : Profile}
    {a b : TemporalObservation} (h : a.observedAt = none) :
    orderingEstablished p a b = false := by
  simp [orderingEstablished, h]

/-! ## Doctrine -/

def doctrine : List String :=
  [ "freshness is not elapsed time; freshness is admitted elapsed time under a declared witness contract",
    "time is testimony: a clock may testify, and the profile decides whether it may be believed for this act",
    "observed_at and generated_at are not interchangeable; a fresh packet does not refresh old testimony",
    "a timestamp proves existence, not current freshness",
    "silence suppresses; it never clears — loss of observability does not fabricate health",
    "late success is not timely success; a deadline miss is a first-class refusal fact",
    "a retired source does not come back by time passing",
    "two clocks are not an order without a shared or bridged basis",
    "there is no GlobalTrustedTime — every temporal verdict is profile-indexed" ]

/-! ## Specimens (the NQ fixture shapes, as #evals) -/

def goodObs : TemporalObservation :=
  { repackagedStale with observedAt := some 950, generatedAt := 951 }

-- Runnable demonstrations (window 100, evaluated at now = 1000):
#eval verdictAt specimenProfile "runtime-input" goodObs 1000
  -- fresh (TB-P001: fresh authority timestamp supports fresh claim)
#eval verdictAt specimenProfile "runtime-input" repackagedStale 1000
  -- stale (TB-R001: old observed_at, new generated_at — no refresh)
#eval freshByGeneration 100 1000 repackagedStale
  -- true (the tempting evaluator falls for it; the theorem refutes it)
#eval verdictAt specimenProfile "runtime-input"
  { repackagedStale with observedAt := none } 1000
  -- unknownAuthorityTime (TB-R003: missing authority timestamp)
#eval verdictAt specimenProfile "runtime-input"
  { repackagedStale with witness := "clock:untrusted", basis := "wall" } 1000
  -- cannotTestify (TB-R010: clock witness not admitted)
#eval verdictAt
  { specimenProfile with
      clocks := [{ witness := "clock:mono-01", basis := "host-mono"
                 , uncertainty := 500 }] }
  "runtime-input" goodObs 1000
  -- uncertaintyTooLarge (TB-R011: uncertainty exceeds window)
#eval verdictAt
  { specimenProfile with sources := [("clock:mono-01", SourceState.retired)] }
  "runtime-input" goodObs 1000
  -- blockedByRetiredSource (TB-R004: retired source blocks — at any now)
#eval onSilence FindingState.active
  -- suppressed (TB-R006: silence does not clear a finding)
#eval deadlineMet { deadline := 100, finishedAt := some 150 }
  -- false (TB-R008: late success is not timely success)
#eval completed { deadline := 100, finishedAt := some 150 }
  -- true (…but it IS completed; the pair is the point)
#eval orderingEstablished specimenProfile goodObs
  { goodObs with basis := "wall", observedAt := some 990 }
  -- false (TB-R012: ordering across bases not established)

#eval doctrine

end Admissibility.TemporalBasis
