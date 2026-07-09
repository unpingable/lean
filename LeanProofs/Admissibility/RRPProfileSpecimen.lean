/-
  Custody-Class: UNRATIFIED-CANDIDATE

  Minimal RRP profile-checker semantics (2026-07-09). Forcing consumer: the RRP
  admissibility-gate prototype (~/git/rrp — receipt-indexed gate, Python
  reference checker + Rust parity). This file models the checker's SEMANTIC
  kernel only — the doctrine its corpus cases test — not the implementation:

    observations are not claims
    claims require admitted observation receipts
    effects require claims
    missing / cannot-testify / stale / revoked evidence refuses
    profile_id cannot substitute for profile_digest
    a requester's self-witnessed receipt does not testify unless admitted

  NOT modeled, on purpose: canonical JSON, SHA-256 digesting, parsers, unknown
  key rejection, transport, bridge custody, PKI. `Profile.digest` is a symbolic
  stand-in for the canonical-body digest; collision resistance is what makes a
  real hash behave like this symbol. Receipt-level obstruction codes from the
  RRP ABI (`MissingReceipt`, `CannotTestify`, `StaleWitness`) appear here as
  derivation-level refusal THEOREMS, not as emitted decision payloads — the
  specimen's `decision` collapses evidence failures to `claimNotEstablished`,
  which is the coarser honest claim. This file does not prove anything about
  the Python/Rust checkers; it pins the semantics they are supposed to have.

  Unwired: not imported by `LeanProofs.lean` or any default target. Build
  directly: `lake build LeanProofs.Admissibility.RRPProfileSpecimen`.
  Promotion to ANNEX gates on the RRP repo actually citing named theorems
  under its pinning discipline (the DeferredWitness precedent).
-/

/-!
# RRP Profile Specimen

The RRP-shaped nucleus, one layer above `Authority.lean`'s verdict algebra:
a `Profile` declares which witnesses may testify to which observation kinds,
how claims derive from admitted receipts, and which claims an effect requires.
`deriveClaims` is the read side; `decision` is the gate. Everything refuses
by construction — there is no path to `permit` that does not pass through an
admitted receipt for every required claim.

Lean ancestors: `Authority.authorized_iff_all_green` (all dimensions green),
`Derivation.decide_authorized_requires_all_green` (composed derivations),
`Freshness.expired_not_fresh` (staleness), `DeferredWitness` (classifier +
reflection house pattern).
-/

namespace Admissibility.RRPProfileSpecimen

abbrev Time            := Nat
abbrev ObservationKind := String
abbrev ClaimKind       := String
abbrev EffectKind      := String
abbrev WitnessId       := String
abbrev Subject         := String
/-- Symbolic stand-in for the canonical-body digest. `profileId` is display
    metadata; this is the authority identity. -/
abbrev Digest          := Nat

/-! ## Objects -/

/-- One observation receipt: testimony, not a fact, and not a claim. -/
structure Receipt where
  witness    : WitnessId
  kind       : ObservationKind
  subject    : Subject
  observedAt : Time
deriving Repr, DecidableEq

/-- A bounded conclusion derived by the checker. Claims exist only as outputs
    of `deriveClaims` — there is no constructor path from a receipt to a claim
    that skips a rule. -/
structure Claim where
  kind    : ClaimKind
  subject : Subject
deriving Repr, DecidableEq

/-- claim rule: observations of `fromObservation`, reported by an allowed
    witness, fresh within `maxAge`, derive `toClaim` for the receipt's subject. -/
structure ClaimRule where
  fromObservation  : ObservationKind
  toClaim          : ClaimKind
  allowedWitnesses : List WitnessId
  maxAge           : Time
deriving Repr, DecidableEq

/-- effect rule: the governed action `effectKind` requires every claim kind in
    `requires`, for the requesting subject. -/
structure EffectRule where
  effectKind : EffectKind
  requires   : List ClaimKind
deriving Repr, DecidableEq

structure Profile where
  digest           : Digest
  profileId        : String
  claimRules       : List ClaimRule
  effectRules      : List EffectRule
  /-- standing-basis revocations known at evaluation time -/
  revokedWitnesses : List WitnessId
deriving Repr

structure GateRequest where
  actor         : WitnessId
  effect        : EffectKind
  subject       : Subject
  /-- authority reference. `none` models a request that names the profile only
      by `profileId` — display metadata carrying no authority. -/
  profileDigest : Option Digest
  profileId     : String
deriving Repr

/-! ## Derivation (read side) -/

/-- Does this rule admit this receipt at time `now`? All four surfaces must be
    green: kind match, witness allowed, basis not revoked, evidence fresh. -/
def admitsB (p : Profile) (rule : ClaimRule) (r : Receipt) (now : Time) : Bool :=
  decide (r.kind = rule.fromObservation) &&
  decide (r.witness ∈ rule.allowedWitnesses) &&
  decide (r.witness ∉ p.revokedWitnesses) &&
  decide (now ≤ r.observedAt + rule.maxAge)

/-- Claims derived from the evidence set. Observations are not claims: the ONLY
    path from a receipt to a claim is through an admitting rule. -/
def deriveClaims (p : Profile) (ev : List Receipt) (now : Time) : List Claim :=
  p.claimRules.flatMap fun rule =>
    (ev.filter fun r => admitsB p rule r now).map fun r =>
      { kind := rule.toClaim, subject := r.subject }

/-! ## Decision (gate) -/

/-- Obstructions the specimen `decision` actually emits. Receipt-level ABI
    codes (MissingReceipt / CannotTestify / StaleWitness) are derivation-level
    theorems below, deliberately NOT decision payloads here. -/
inductive Obstruction
  | profileRefByIdOnly                          -- profile named by id, no digest
  | profileDigestMismatch                       -- digest is not this profile's
  | effectKindUnknown (kind : EffectKind)       -- no effect rule for the request
  | claimNotEstablished (kind : ClaimKind)      -- a required claim did not derive
deriving Repr, DecidableEq

/-- A gate decision is a discriminated union, not a boolean. -/
inductive Decision
  | permit  (derived : List Claim) (effect : EffectKind)
  | refusal (o : Obstruction)
deriving Repr, DecidableEq

/-- The gate. Authority identity first (digest, never id), then the effect
    rule, then every required claim for the requesting subject. -/
def decision (p : Profile) (req : GateRequest) (ev : List Receipt) (now : Time) :
    Decision :=
  match req.profileDigest with
  | none => .refusal .profileRefByIdOnly
  | some d =>
    if d = p.digest then
      match p.effectRules.find? (fun er => decide (er.effectKind = req.effect)) with
      | none => .refusal (.effectKindUnknown req.effect)
      | some er =>
        match er.requires.find? (fun ck =>
            !((deriveClaims p ev now).any fun c =>
              decide (c.kind = ck) && decide (c.subject = req.subject))) with
        | some ck => .refusal (.claimNotEstablished ck)
        | none => .permit (deriveClaims p ev now) req.effect
    else .refusal .profileDigestMismatch

/-! ## Receipt-level refusal surfaces

Each is one conjunct of `admitsB` with teeth. These are the Lean faces of the
ABI's receipt-level obstruction codes. -/

/-- Admitted receipts match the rule's observation kind. -/
theorem admits_kind {p rule r now} (h : admitsB p rule r now = true) :
    r.kind = rule.fromObservation := by
  simp [admitsB] at h
  exact h.1.1.1

/-- CannotTestify: a witness the rule does not admit contributes nothing,
    whatever it observed. -/
theorem cannot_testify_not_admitted {p rule r now}
    (h : r.witness ∉ rule.allowedWitnesses) : admitsB p rule r now = false := by
  simp [admitsB, h]

/-- StaleWitness: evidence older than the rule's freshness window contributes
    nothing. -/
theorem stale_not_admitted {p rule r now}
    (h : r.observedAt + rule.maxAge < now) : admitsB p rule r now = false := by
  simp [admitsB, Nat.not_le.mpr h]

/-- Revoked basis: a witness whose standing basis is revoked contributes
    nothing, even if the rule lists it. -/
theorem revoked_not_admitted {p rule r now}
    (h : r.witness ∈ p.revokedWitnesses) : admitsB p rule r now = false := by
  simp [admitsB, h]

/-- Self-authorization refused: a receipt the requesting actor witnessed about
    itself does not testify unless the profile explicitly admits the actor as a
    witness. The specimen's anti-laundering face: being the subject of a claim
    buys no standing to witness it. -/
theorem self_authorization_refused {p rule now} (req : GateRequest) (r : Receipt)
    (hself : r.witness = req.actor)
    (hnoself : req.actor ∉ rule.allowedWitnesses) :
    admitsB p rule r now = false :=
  cannot_testify_not_admitted (hself ▸ hnoself)

/-! ## Claim-level refusal theorems -/

/-- Inversion: every derived claim is backed by an admitted receipt under a
    profile rule. No claim is free. -/
theorem mem_deriveClaims {p ev now} {c : Claim} (h : c ∈ deriveClaims p ev now) :
    ∃ rule, rule ∈ p.claimRules ∧ ∃ r, r ∈ ev ∧ admitsB p rule r now = true ∧
      c = { kind := rule.toClaim, subject := r.subject } := by
  simp only [deriveClaims, List.mem_flatMap, List.mem_map, List.mem_filter] at h
  obtain ⟨rule, hrule, r, ⟨hr, hadm⟩, hc⟩ := h
  exact ⟨rule, hrule, r, hr, hadm, hc.symm⟩

/-- MissingReceipt, empty form: no evidence, no claims. -/
theorem missing_receipt_no_claim (p : Profile) (now : Time) :
    deriveClaims p [] now = [] := by
  simp [deriveClaims]

/-- MissingReceipt, kind form: if the evidence set contains no receipt of the
    observation kind any rule needs for claim kind `ck`, no claim of kind `ck`
    derives. Receipt *presence* of the right kind is a necessary condition —
    this is "receipt presence is not admissibility"'s converse guard. -/
theorem missing_receipt_kind_no_claim {p ev now} {ck : ClaimKind}
    (h : ∀ rule ∈ p.claimRules, rule.toClaim = ck →
         ∀ r ∈ ev, r.kind ≠ rule.fromObservation) :
    ∀ c ∈ deriveClaims p ev now, c.kind ≠ ck := by
  intro c hc hckind
  obtain ⟨rule, hrule, r, hr, hadm, hceq⟩ := mem_deriveClaims hc
  exact h rule hrule (by rw [hceq] at hckind; exact hckind) r hr (admits_kind hadm)

/-- CannotTestify, lifted: evidence consisting entirely of receipts whose
    witnesses no rule admits derives nothing. -/
theorem cannot_testify_no_claim {p ev now}
    (h : ∀ r ∈ ev, ∀ rule ∈ p.claimRules, r.witness ∉ rule.allowedWitnesses) :
    deriveClaims p ev now = [] := by
  rw [List.eq_nil_iff_forall_not_mem]
  intro c hc
  obtain ⟨rule, hrule, r, hr, hadm, _⟩ := mem_deriveClaims hc
  rw [cannot_testify_not_admitted (h r hr rule hrule)] at hadm
  exact Bool.false_ne_true hadm

/-- StaleWitness, lifted: evidence that is stale for every rule derives
    nothing. Late evidence cannot be spent as fresh evidence. -/
theorem stale_receipt_no_claim {p ev now}
    (h : ∀ r ∈ ev, ∀ rule ∈ p.claimRules, r.observedAt + rule.maxAge < now) :
    deriveClaims p ev now = [] := by
  rw [List.eq_nil_iff_forall_not_mem]
  intro c hc
  obtain ⟨rule, hrule, r, hr, hadm, _⟩ := mem_deriveClaims hc
  rw [stale_not_admitted (h r hr rule hrule)] at hadm
  exact Bool.false_ne_true hadm

/-- Revoked basis, lifted: if every witness in the evidence set is revoked,
    nothing derives. Revocation reaches through the whole evidence set. -/
theorem revoked_basis_no_claim {p ev now}
    (h : ∀ r ∈ ev, r.witness ∈ p.revokedWitnesses) :
    deriveClaims p ev now = [] := by
  rw [List.eq_nil_iff_forall_not_mem]
  intro c hc
  obtain ⟨_, _, r, hr, hadm, _⟩ := mem_deriveClaims hc
  rw [revoked_not_admitted (h r hr)] at hadm
  exact Bool.false_ne_true hadm

/-! ## Decision-level refusal theorems -/

/-- profile_id is not authority: a request that names the profile only by id
    is refused before evidence is even considered. -/
theorem profile_id_only_no_decision (p : Profile) (req : GateRequest)
    (ev : List Receipt) (now : Time) (h : req.profileDigest = none) :
    decision p req ev now = .refusal .profileRefByIdOnly := by
  simp [decision, h]

/-- Wrong digest is wrong authority, whatever the id says. -/
theorem digest_mismatch_refused (p : Profile) (req : GateRequest)
    (ev : List Receipt) (now : Time) {d : Digest}
    (h : req.profileDigest = some d) (hne : d ≠ p.digest) :
    decision p req ev now = .refusal .profileDigestMismatch := by
  simp [decision, h, hne]

/-- effect_requires_claim: a permit certifies that some effect rule for the
    requested kind had EVERY required claim derived from admitted evidence for
    the requesting subject. There is no permit without the claims. -/
theorem effect_requires_claim {p req ev now claims eff}
    (h : decision p req ev now = .permit claims eff) :
    ∃ er, er ∈ p.effectRules ∧ er.effectKind = req.effect ∧
      ∀ ck ∈ er.requires, ∃ c ∈ deriveClaims p ev now,
        c.kind = ck ∧ c.subject = req.subject := by
  unfold decision at h
  split at h
  · cases h
  · split at h
    · rename_i heq _ _ _
      split at h
      · cases h
      · rename_i er hfind
        split at h
        · cases h
        · rename_i hnone
          have hkind : er.effectKind = req.effect := by
            have hp := List.find?_some hfind
            simpa using hp
          refine ⟨er, List.mem_of_find?_eq_some hfind, hkind, ?_⟩
          intro ck hck
          have hmet := List.find?_eq_none.mp hnone ck hck
          simp only [Bool.not_eq_true', Bool.not_eq_false] at hmet
          obtain ⟨c, hc, hcond⟩ := List.any_eq_true.mp hmet
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
          exact ⟨c, hc, hcond⟩
    · cases h

/-- No required claim, no permit: if every effect rule matching the request has
    some required claim that the evidence cannot establish, the gate cannot
    permit. Contrapositive face of `effect_requires_claim`. -/
theorem no_required_claim_no_permit {p req ev now}
    (h : ∀ er ∈ p.effectRules, er.effectKind = req.effect →
         ∃ ck ∈ er.requires, ∀ c ∈ deriveClaims p ev now,
           ¬(c.kind = ck ∧ c.subject = req.subject)) :
    ∀ claims eff, decision p req ev now ≠ .permit claims eff := by
  intro claims eff hperm
  obtain ⟨er, her, hkind, hall⟩ := effect_requires_claim hperm
  obtain ⟨ck, hck, hnone⟩ := h er her hkind
  obtain ⟨c, hc, hckind, hcsubj⟩ := hall ck hck
  exact hnone c hc ⟨hckind, hcsubj⟩

/-- No evidence, no permit (for effects that require anything at all). The
    degenerate corpus case: an empty evidence set cannot buy a governed effect. -/
theorem no_evidence_no_permit {p req now}
    (hreq : ∀ er ∈ p.effectRules, er.effectKind = req.effect → er.requires ≠ []) :
    ∀ claims eff, decision p req [] now ≠ .permit claims eff := by
  apply no_required_claim_no_permit
  intro er her hkind
  obtain ⟨ck, hck⟩ := List.exists_mem_of_ne_nil _ (hreq er her hkind)
  exact ⟨ck, hck, by simp [missing_receipt_no_claim]⟩

/-! ## Doctrine -/

def doctrine : List String :=
  [ "observations are not claims — the only path from receipt to claim is an admitting rule",
    "claims require admitted observations; effects require claims",
    "missing, stale, cannot-testify, and revoked evidence refuse — each surface separately",
    "profile_id is display metadata; profile_digest is the authority identity",
    "being the subject of a claim buys no standing to witness it" ]

/-! ## Specimens -/

/-- Standing-flavored worked profile: one observation kind, one claim, one
    governed effect. Digest value is a symbolic stand-in. -/
def specimenProfile : Profile :=
  { digest     := 0xC0FFEE
  , profileId  := "ag.standing.v1"
  , claimRules :=
      [ { fromObservation  := "standing.basis_active_observed"
        , toClaim          := "ag.actor_has_standing"
        , allowedWitnesses := ["standing-collector"]
        , maxAge           := 100 } ]
  , effectRules :=
      [ { effectKind := "promote_candidate"
        , requires   := ["ag.actor_has_standing"] } ]
  , revokedWitnesses := [] }

def goodReceipt : Receipt :=
  { witness := "standing-collector", kind := "standing.basis_active_observed"
  , subject := "actor-a", observedAt := 1000 }

def goodRequest : GateRequest :=
  { actor := "actor-a", effect := "promote_candidate", subject := "actor-a"
  , profileDigest := some 0xC0FFEE, profileId := "ag.standing.v1" }

/-- The requester writes a receipt about itself. -/
def selfWitnessedReceipt : Receipt :=
  { goodReceipt with witness := "actor-a" }

-- Runnable demonstrations (now := 1050; the receipt is 50 old, window is 100):
#eval decision specimenProfile goodRequest [goodReceipt] 1050
  -- permit [ag.actor_has_standing for actor-a]
#eval decision specimenProfile goodRequest [] 1050
  -- refusal claimNotEstablished — no receipt, no claim, no effect
#eval decision specimenProfile goodRequest [goodReceipt] 2000
  -- refusal claimNotEstablished — stale evidence does not derive
#eval decision specimenProfile goodRequest [selfWitnessedReceipt] 1050
  -- refusal claimNotEstablished — self-witnessed testimony not admitted
#eval decision { specimenProfile with revokedWitnesses := ["standing-collector"] }
  goodRequest [goodReceipt] 1050
  -- refusal claimNotEstablished — revoked basis reaches through evidence
#eval decision specimenProfile { goodRequest with profileDigest := none }
  [goodReceipt] 1050
  -- refusal profileRefByIdOnly — profile_id is not authority
#eval decision specimenProfile { goodRequest with profileDigest := some 0xBAD }
  [goodReceipt] 1050
  -- refusal profileDigestMismatch

#eval doctrine

end Admissibility.RRPProfileSpecimen
