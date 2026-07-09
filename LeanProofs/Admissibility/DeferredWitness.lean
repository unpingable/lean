/-
  Custody-Class: ANNEX

  Promoted from `LeanProofs/Scratch/DeferredWitness.lean` (2026-06-26): compiled,
  sorry-free, wired into `LeanProofs.lean` for build coverage. Signatures are NOT
  part of the 1.0 compatibility claim — annex semantics (may rename, refactor, or
  absorb without notice). Provenance: scratch reconnaissance graduated to annex so
  downstream operational work (NQ's EVIDENCE_RETIREMENT basis-stale slice) can cite
  it as evidence under the pinning discipline, rather than steer implementation
  from a fenced module. A refusal kernel for temporal backflow: it pins the one
  lawful form of late-witness completion and the laundering moves it blocks.
-/

/-!
# Deferred Witness

Companion kernel to the Admissibility Kernels. Governs the one lawful form of
"backflow": a witness observed *after* a claim was asserted completing that
claim, and the exact license that makes it reconciliation rather than laundering.

The matched pair:

  FORBIDDEN  no grant live at assertion, and at t₂ you pretend there was one
  ALLOWED    a witnessed deferral grant live at assertion, exercised at t₂

The discriminator lives entirely at assertion time. Same arrow, opposite verdict.

This file is the corrected version of a prior draft. Four things it adds that the
draft left open — each is a named refusal surface below:

  1. grant_witness_prior   — the grant's OWN witness must predate the claim's
                             reliance. The draft only asserted `witness_ref ≠ none`
                             ("a reference exists"), which lets a grant be witnessed
                             after the fact while passing as witnessed. signed≠witnessed,
                             aimed at the grant. This is the line that was dropped.
  2. grant_terms_witnessed — the witness binds to the EXACT terms (digest), not to
                             "a grant exists". Without it you witness narrow terms and
                             widen scope post hoc: mutation laundering under a real
                             signature. (Tooth: `mutated_terms_rejected`.)
  3. evidence_is_late      — a lower bound on the evidence. The rule is meant to govern
                             *late* witness; without `asserted_at < observed_at` it also
                             admits evidence that predates the claim, so it never isolates
                             the case it exists for.
  4. statusOf / Admissible — the lapse path. A grant whose window closes with no
                             completing witness must dump the claim back to a
                             non-admissible state, not leave it in indefinite `pending`
                             (which becomes de-facto admissible — "it's been pending
                             eight months, ship it"). Only `completed` is admissible.

No grading. Count discrete violations; never relax the count into a coefficient.
"0.73 admissible" leaks back into decisions and rebuilds graded clearance through
the reporting layer. The taxonomy below is individuated and typed for that reason.

Concretization note: Time/ClaimKind/EvidenceKind/Scope are pinned to Nat/String/
List String so the kernel is self-contained and computable (`#eval` works). Lifting
to abstract `[LinearOrder]` / `[DecidableEq]` carriers is mechanical.
-/

namespace Admissibility.DeferredWitness

abbrev Time         := Nat
abbrev ClaimKind    := String
abbrev EvidenceKind := String
abbrev Scope        := List String        -- hierarchical path; [] = root

/-- Grant scope covers claim scope iff it is a prefix of it. Illustrative semantics. -/
def Covers (grant claim : Scope) : Prop := grant.isPrefixOf claim = true
instance (g c : Scope) : Decidable (Covers g c) := by unfold Covers; infer_instance

/-! ## Objects -/

structure GrantTerms where
  claim_kind     : ClaimKind
  opened_at      : Time
  expires_at     : Time
  accepted_forms : List EvidenceKind
  scope          : Scope
deriving DecidableEq, Repr

/-- A witness attesting a grant. `over` is the content it is bound to — a stand-in
    for `hash(terms)`. Modelling it as the terms themselves makes the binding
    provably injective; real collision-resistance is what makes a hash behave so. -/
structure GrantWitness where
  observed_at : Time
  over        : GrantTerms
deriving Repr

structure DeferralGrant where
  terms   : GrantTerms
  witness : GrantWitness
deriving Repr

structure Claim where
  kind        : ClaimKind
  scope       : Scope
  asserted_at : Time
deriving Repr

/-- The late-arriving observation that *completes* a pending claim. A distinct
    witnessing act from the grant's own witness — the recursion is precisely that
    the artifact licensing this act needs its own witness. -/
structure Evidence where
  kind        : EvidenceKind
  observed_at : Time
deriving Repr

structure LateWitnessUse where
  grant    : DeferralGrant
  claim    : Claim
  evidence : Evidence
deriving Repr

/-! ## Layer A — Lawful completion (closed)

Each field is a named refusal surface. Negating any one is a temporal-backflow
violation (see `Backflow`). -/

structure LawfulCompletion (u : LateWitnessUse) : Prop where
  /-- witness binds to exactly these terms — no post-hoc widening -/
  grant_terms_witnessed : u.grant.witness.over = u.grant.terms
  /-- the grant was witnessed *by the time the claim relied on it* (anti-necromancy) -/
  grant_witness_prior   : u.grant.witness.observed_at ≤ u.claim.asserted_at
  /-- claim asserted at/after the grant window opened -/
  window_front          : u.grant.terms.opened_at ≤ u.claim.asserted_at
  /-- claim asserted at/before the grant window closes -/
  window_back           : u.claim.asserted_at ≤ u.grant.terms.expires_at
  /-- the evidence is genuinely late — this is what isolates the deferred case -/
  evidence_is_late      : u.claim.asserted_at < u.evidence.observed_at
  /-- the evidence arrived within the window -/
  evidence_in_window    : u.evidence.observed_at ≤ u.grant.terms.expires_at
  /-- the evidence is of an accepted form -/
  evidence_form_ok      : u.evidence.kind ∈ u.grant.terms.accepted_forms
  /-- the grant is for this claim's kind -/
  kind_matches          : u.claim.kind = u.grant.terms.claim_kind
  /-- the grant's scope covers the claim's -/
  scope_covered         : Covers u.grant.terms.scope u.claim.scope

/-! ## The named corpses

These are projections / one-line contrapositions. The design work is in the
predicate; the theorems confirm each surface is present and has teeth. -/

/-- No Retroactive Standing: a lawful completion entails the grant was witnessed
    no later than the claim's assertion. Contrapositive: no prior-witnessed grant,
    no completion. -/
theorem no_retroactive_standing {u} (h : LawfulCompletion u) :
    u.grant.witness.observed_at ≤ u.claim.asserted_at :=
  h.grant_witness_prior

/-- Necromancy rejected (the recursion closed): a grant witnessed *after* the claim
    relied on it cannot lawfully complete it. The license can no more be conjured at
    t₂ than the standing could. -/
theorem necromancy_rejected {u}
    (late : u.claim.asserted_at < u.grant.witness.observed_at) :
    ¬ LawfulCompletion u :=
  fun hc => Nat.lt_irrefl _ (Nat.lt_of_lt_of_le late hc.grant_witness_prior)

/-- Mutation rejected: present terms differing from the witnessed terms (e.g. a
    widened scope) cannot complete. Witnessing "a grant exists" is not enough;
    the witness freezes the content. -/
theorem mutated_terms_rejected {u}
    (h : u.grant.witness.over ≠ u.grant.terms) : ¬ LawfulCompletion u :=
  fun hc => h hc.grant_terms_witnessed

/-- Stale evidence rejected: evidence that does not postdate the assertion is not
    the late case this rule governs. -/
theorem stale_evidence_rejected {u}
    (h : ¬ u.claim.asserted_at < u.evidence.observed_at) : ¬ LawfulCompletion u :=
  fun hc => h hc.evidence_is_late

/-! ## Violation taxonomy (TemporalBackflow)

Disjoint, named, countable. `firstViolation` is the executable classifier. Its
agreement with `LawfulCompletion` — `firstViolation u = none ↔ LawfulCompletion u`
— is the natural reflection lemma, proved below as
`firstViolation_none_iff_lawful` (2026-07-09; previously left to the host
environment). The classifier is now theorem-backed: `none` is a proof that every
refusal surface was checked, not a default. Counts of these are admissible
telemetry. A severity score is not. -/

inductive Backflow
  | grant_unwitnessed        -- witness not over these terms (mutation, or never witnessed)
  | grant_witness_posterior  -- grant witnessed after the claim relied on it (necromancy)
  | assertion_before_open    -- claim asserted before the grant window opened
  | assertion_after_expiry   -- claim asserted after the grant expired
  | evidence_not_late        -- "late" evidence actually predates the assertion
  | evidence_after_expiry    -- evidence arrived after the window closed
  | evidence_wrong_form      -- evidence kind not among accepted forms
  | kind_mismatch            -- grant is for a different claim kind
  | scope_escape             -- claim scope not covered by grant scope
deriving Repr, DecidableEq

/-- First failing surface, in order. `none` means lawful. -/
def firstViolation (u : LateWitnessUse) : Option Backflow :=
  if u.grant.witness.over ≠ u.grant.terms then some .grant_unwitnessed
  else if u.claim.asserted_at < u.grant.witness.observed_at then some .grant_witness_posterior
  else if u.claim.asserted_at < u.grant.terms.opened_at then some .assertion_before_open
  else if u.grant.terms.expires_at < u.claim.asserted_at then some .assertion_after_expiry
  else if ¬ u.claim.asserted_at < u.evidence.observed_at then some .evidence_not_late
  else if u.grant.terms.expires_at < u.evidence.observed_at then some .evidence_after_expiry
  else if u.evidence.kind ∉ u.grant.terms.accepted_forms then some .evidence_wrong_form
  else if u.claim.kind ≠ u.grant.terms.claim_kind then some .kind_mismatch
  else if ¬ Covers u.grant.terms.scope u.claim.scope then some .scope_escape
  else none

/-- Reflection: the executable classifier agrees exactly with the spec. `none` is
    not a default — it certifies that all nine refusal surfaces were checked and
    passed. Each `ite` guard in `firstViolation` is the negation of the
    corresponding `LawfulCompletion` field, in field order; this lemma is the
    proof that the mirroring is exact (no surface dropped, none weakened). -/
theorem firstViolation_none_iff_lawful (u : LateWitnessUse) :
    firstViolation u = none ↔ LawfulCompletion u := by
  constructor
  · intro h
    unfold firstViolation at h
    split at h
    · cases h
    next h1 =>
    split at h
    · cases h
    next h2 =>
    split at h
    · cases h
    next h3 =>
    split at h
    · cases h
    next h4 =>
    split at h
    · cases h
    next h5 =>
    split at h
    · cases h
    next h6 =>
    split at h
    · cases h
    next h7 =>
    split at h
    · cases h
    next h8 =>
    split at h
    · cases h
    next h9 =>
    exact
      { grant_terms_witnessed := Decidable.of_not_not h1
      , grant_witness_prior   := Nat.not_lt.mp h2
      , window_front          := Nat.not_lt.mp h3
      , window_back           := Nat.not_lt.mp h4
      , evidence_is_late      := Decidable.of_not_not h5
      , evidence_in_window    := Nat.not_lt.mp h6
      , evidence_form_ok      := Decidable.of_not_not h7
      , kind_matches          := Decidable.of_not_not h8
      , scope_covered         := Decidable.of_not_not h9 }
  · intro hc
    unfold firstViolation
    rw [ if_neg (fun h => h hc.grant_terms_witnessed)
       , if_neg (Nat.not_lt.mpr hc.grant_witness_prior)
       , if_neg (Nat.not_lt.mpr hc.window_front)
       , if_neg (Nat.not_lt.mpr hc.window_back)
       , if_neg (fun h => h hc.evidence_is_late)
       , if_neg (Nat.not_lt.mpr hc.evidence_in_window)
       , if_neg (fun h => h hc.evidence_form_ok)
       , if_neg (fun h => h hc.kind_matches)
       , if_neg (fun h => h hc.scope_covered) ]

/-- Corollary: a violation is reported iff the completion is unlawful. The
    classifier can neither invent a violation for a lawful use nor stay silent
    on an unlawful one. -/
theorem firstViolation_isSome_iff_not_lawful (u : LateWitnessUse) :
    (firstViolation u).isSome ↔ ¬ LawfulCompletion u := by
  rw [← firstViolation_none_iff_lawful]
  cases firstViolation u <;> simp

/-! ## Lifecycle and the lapse path

`pending` is provisional, NOT admissible. A window that closes with no completing
witness goes to `lapsed`, also not admissible. Only `completed` is admissible. -/

inductive Status
  | refused      -- no grant stands for this claim
  | pending      -- stands under a live witnessed grant; awaiting evidence; window open
  | completed    -- a late witness validly completed it
  | lapsed       -- window closed with no completing witness
deriving Repr, DecidableEq

/-- Grant-side standing: everything in `LawfulCompletion` except the evidence
    obligations. This is what makes a claim legitimately *pending*. -/
def grantStandsB (g : DeferralGrant) (c : Claim) : Bool :=
  decide (g.witness.over = g.terms) &&
  decide (g.witness.observed_at ≤ c.asserted_at) &&
  decide (g.terms.opened_at ≤ c.asserted_at) &&
  decide (c.asserted_at ≤ g.terms.expires_at) &&
  decide (c.kind = g.terms.claim_kind) &&
  g.terms.scope.isPrefixOf c.scope

/-- Status of a claim under a grant, given an optional completing observation and
    the current time. Note `none` + expired ⇒ `lapsed`, never `pending`. -/
def statusOf (g : DeferralGrant) (c : Claim) (e : Option Evidence) (now : Time) : Status :=
  if grantStandsB g c then
    match e with
    | some ev =>
        if decide (c.asserted_at < ev.observed_at) &&
           decide (ev.observed_at ≤ g.terms.expires_at) &&
           decide (ev.kind ∈ g.terms.accepted_forms)
        then Status.completed
        else if g.terms.expires_at < now then Status.lapsed else Status.pending
    | none =>
        if g.terms.expires_at < now then Status.lapsed else Status.pending
  else Status.refused

def Admissible (s : Status) : Prop := s = Status.completed

theorem pending_not_admissible : ¬ Admissible Status.pending := by unfold Admissible; decide
theorem lapsed_not_admissible  : ¬ Admissible Status.lapsed  := by unfold Admissible; decide
theorem refused_not_admissible : ¬ Admissible Status.refused := by unfold Admissible; decide

/-! ## Layer B — the open frontier: kind vs instance scope

Layer A closes temporal laundering. It does NOT bound how many claims one grant
may complete. `GrantTerms.claim_kind` scopes a grant to a KIND, so a single
witnessed grant licenses deferral for *every* in-window claim of that kind —
admissibility decoupled from per-instance witness by construction. That is a
standing witness-exemption: blanket clearance, re-smuggled.

The discriminator we keep deferring is the budget the grant spends down. The
ledger (`priorUses`) and the cap are parameters on purpose; choosing them IS the
next design decision, not a detail:

    cap = 1,  priorUses keyed on (grant, claim)   ⇒ instance scope: sound, doesn't scale
    cap = ∞  (no ledger)                          ⇒ kind scope: scales, launders
    cap = k finite, forced re-witness every k uses ⇒ the bounded middle (the live design)

The recursion does not vanish in the bounded-middle case: exhausting a grant must
mint a *fresh* grant whose witness must itself predate the next claim's reliance —
i.e. `necromancy_rejected` re-fires at refresh time. The budget refresh is governed
by the same rule as the original grant. That the prohibition reappears unchanged at
the refresh boundary is the consistency check that the structure is stable rather
than merely pushed up a floor. -/

structure Budget where
  cap : Nat
deriving Repr

def WithinBudget (priorUses : Nat) (b : Budget) : Prop := priorUses < b.cap

/-- Full admissibility = lawful (Layer A, closed) ∧ within budget (Layer B, open). -/
def AdmissibleCompletion (priorUses : Nat) (b : Budget) (u : LateWitnessUse) : Prop :=
  LawfulCompletion u ∧ WithinBudget priorUses b

/-! ## Doctrine -/

def doctrine : List String :=
  [ "signed is not witnessed — a grant's opened_at and terms are signings; its witness makes them admissible, and must predate reliance",
    "later evidence is not prior standing",
    "a license to defer is itself a declared state requiring a witness",
    "count temporal-backflow violations; never grade truth" ]

/-! ## Specimens -/

/-- TLS cert expiry claim, completed by an ACME renewal log under a grant that was
    witnessed at t=110, before the claim asserted at t=120, evidence at t=150. -/
def goodUse : LateWitnessUse :=
  let terms : GrantTerms :=
    { claim_kind     := "tls-cert-expiry"
    , opened_at      := 100
    , expires_at     := 200
    , accepted_forms := ["acme-renewal-log"]
    , scope          := ["edge", "tls"] }
  { grant    := { terms := terms, witness := { observed_at := 110, over := terms } }
  , claim    := { kind := "tls-cert-expiry", scope := ["edge", "tls", "host-a"], asserted_at := 120 }
  , evidence := { kind := "acme-renewal-log", observed_at := 150 } }

example : LawfulCompletion goodUse :=
  { grant_terms_witnessed := rfl
  , grant_witness_prior   := by decide
  , window_front          := by decide
  , window_back           := by decide
  , evidence_is_late      := by decide
  , evidence_in_window    := by decide
  , evidence_form_ok      := by decide
  , kind_matches          := rfl
  , scope_covered         := by decide }

/-- Grant witnessed at t=130, *after* the claim asserted at t=120. Necromancy. -/
def necromancyUse : LateWitnessUse :=
  { goodUse with grant := { goodUse.grant with
      witness := { goodUse.grant.witness with observed_at := 130 } } }

example : ¬ LawfulCompletion necromancyUse := necromancy_rejected (by decide)

/-- Witnessed over narrow terms (scope ["edge","tls"]); grant presents widened
    terms (scope [] = root). Mutation under a real signature. -/
def mutatedUse : LateWitnessUse :=
  { goodUse with grant := { goodUse.grant with
      terms := { goodUse.grant.terms with scope := [] } } }

example : ¬ LawfulCompletion mutatedUse := mutated_terms_rejected (by decide)

/-- "Late" evidence at t=115, before the claim asserted at t=120. Not the late case. -/
def staleUse : LateWitnessUse :=
  { goodUse with evidence := { goodUse.evidence with observed_at := 115 } }

example : ¬ LawfulCompletion staleUse := stale_evidence_rejected (by decide)

-- Runnable demonstrations:
#eval firstViolation goodUse        -- none
#eval firstViolation necromancyUse  -- some Backflow.grant_witness_posterior
#eval firstViolation mutatedUse     -- some Backflow.grant_unwitnessed
#eval firstViolation staleUse       -- some Backflow.evidence_not_late

#eval statusOf goodUse.grant goodUse.claim none 150                      -- pending  (window open, no evidence)
#eval statusOf goodUse.grant goodUse.claim none 250                      -- lapsed   (expired, no completion)
#eval statusOf goodUse.grant goodUse.claim (some goodUse.evidence) 250   -- completed (valid late witness)

#eval doctrine

end Admissibility.DeferredWitness
