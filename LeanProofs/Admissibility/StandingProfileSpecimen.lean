/-
  Custody-Class: UNRATIFIED-CANDIDATE

  Standing-backed claim specimen (2026-07-09). Sibling of `RRPProfileSpecimen`
  (the general profile semantics); this file instantiates the standing domain:
  which observations may derive `actor_has_standing`, and what that claim does
  and does not buy at the effect gate.

  Formalization leads implementation here: these are the laws the AG/RRP
  standing profile is SUPPOSED to satisfy, written before any runtime cites
  them. This file does not testify for any runtime's compliance.

  The load-bearing negatives, each a named theorem:

    schedule is not standing        — a timer firing conveys no standing
    operator ack is not standing    — acknowledgement is not authorization
    model output is not standing    — an LLM asserting standing mints nothing
    revoked basis is not standing   — revocation reaches the derivation
    wrong actor does not satisfy    — standing is not transferable at the gate
    wrong project does not satisfy  — standing is scoped, not ambient

  NOT modeled, on purpose: Wicket, LA, Porter, transition-kernel execution,
  budgets, transport. The Standing project's output is evidence/testimony
  consumed by a profile rule — never a universal authority and never an RRP
  core primitive.

  Unwired: not imported by `LeanProofs.lean` or any default target. Build
  directly: `lake build LeanProofs.Admissibility.StandingProfileSpecimen`.
  Promotion to ANNEX gates on a runtime artifact citing named theorems
  under the pinning discipline (the DeferredWitness precedent).
-/

/-!
# Standing Profile Specimen

One profile rule, fully explicit: only a standing-collector observation with
an ACTIVE basis derives `actor_has_standing`, and the derived claim satisfies
the `promote_candidate` effect rule only for the same actor and project.
Everything else refuses, and each refusal surface has its own theorem.

Lean ancestors: `Authority.no_standing_never_authorized` (standing is a
verdict dimension), `Derivation.revoked_standing_never_authorized`,
`RRPProfileSpecimen.cannot_testify_no_claim` (source admission is the
general mechanism; this file pins the standing-domain instances).
-/

namespace Admissibility.StandingProfileSpecimen

abbrev Actor   := String
abbrev Project := String

/-- Where a standing observation came from. Only the standing collector is an
    admitted witness source in this profile; the other three are the recurring
    laundering candidates, enumerated so their refusals are theorems rather
    than absences. -/
inductive Source
  | standingCollector
  | schedule        -- a timer / cron firing
  | operatorAck     -- a human acknowledged something
  | modelOutput     -- an LLM said so
deriving Repr, DecidableEq

/-- Basis state at observation time. -/
inductive BasisState
  | active
  | revoked
deriving Repr, DecidableEq

/-- A standing observation: testimony about an actor's standing basis in a
    project, from some source. Not itself a claim. -/
structure StandingObservation where
  source  : Source
  actor   : Actor
  project : Project
  basis   : BasisState
deriving Repr, DecidableEq

/-- The profile-local claim this specimen is about. Deliberately NOT a
    universal "has standing" — it is scoped to (actor, project). -/
structure StandingClaim where
  actor   : Actor
  project : Project
deriving Repr, DecidableEq

/-- The one claim rule of this profile: standing-collector testimony with an
    active basis derives `actor_has_standing` for exactly the observed
    (actor, project). -/
def derivesStanding (o : StandingObservation) : Bool :=
  decide (o.source = Source.standingCollector) &&
  decide (o.basis = BasisState.active)

def deriveClaim (o : StandingObservation) : Option StandingClaim :=
  if derivesStanding o then some { actor := o.actor, project := o.project }
  else none

/-- The governed effect: promote a candidate in a project, requested by an
    actor. -/
structure PromoteRequest where
  actor   : Actor
  project : Project
deriving Repr, DecidableEq

/-- The effect rule: `promote_candidate` requires `actor_has_standing` for the
    SAME actor and the SAME project. -/
def permitsPromote (c : StandingClaim) (req : PromoteRequest) : Bool :=
  decide (c.actor = req.actor) && decide (c.project = req.project)

/-! ## Positive law (so the negatives are not vacuous) -/

/-- An active standing-collector observation derives the claim for exactly its
    (actor, project). -/
theorem active_basis_derives (a : Actor) (p : Project) :
    deriveClaim { source := .standingCollector, actor := a, project := p
                , basis := .active }
      = some { actor := a, project := p } := by
  simp [deriveClaim, derivesStanding]

/-- The derived claim satisfies the effect rule for the matching request. -/
theorem derived_claim_permits_matching_request (a : Actor) (p : Project) :
    permitsPromote { actor := a, project := p } { actor := a, project := p }
      = true := by
  simp [permitsPromote]

/-! ## Refusal surfaces — derivation side -/

/-- Revoked basis does not derive `actor_has_standing`, whatever the source. -/
theorem revoked_basis_no_standing (o : StandingObservation)
    (h : o.basis = BasisState.revoked) : deriveClaim o = none := by
  simp [deriveClaim, derivesStanding, h]

/-- Schedule is not standing: a timer firing derives nothing. -/
theorem schedule_is_not_standing (o : StandingObservation)
    (h : o.source = Source.schedule) : deriveClaim o = none := by
  simp [deriveClaim, derivesStanding, h]

/-- Operator ack is not standing: acknowledgement is not authorization. -/
theorem operator_ack_is_not_standing (o : StandingObservation)
    (h : o.source = Source.operatorAck) : deriveClaim o = none := by
  simp [deriveClaim, derivesStanding, h]

/-- Model output is not standing: an LLM asserting standing mints nothing. -/
theorem model_output_is_not_standing (o : StandingObservation)
    (h : o.source = Source.modelOutput) : deriveClaim o = none := by
  simp [deriveClaim, derivesStanding, h]

/-- Only the standing collector can be the source of a derived claim —
    the inversion form of the three refusals above. -/
theorem derived_claim_source_is_collector {o : StandingObservation}
    {c : StandingClaim} (h : deriveClaim o = some c) :
    o.source = Source.standingCollector := by
  unfold deriveClaim at h
  split at h
  · rename_i hd
    simp [derivesStanding] at hd
    exact hd.1
  · cases h

/-- A derived claim carries an active basis — revocation cannot hide inside a
    successful derivation. -/
theorem derived_claim_basis_is_active {o : StandingObservation}
    {c : StandingClaim} (h : deriveClaim o = some c) :
    o.basis = BasisState.active := by
  unfold deriveClaim at h
  split at h
  · rename_i hd
    simp [derivesStanding] at hd
    exact hd.2
  · cases h

/-- A derived claim is scoped to exactly the observed actor and project. -/
theorem derived_claim_matches_observation {o : StandingObservation}
    {c : StandingClaim} (h : deriveClaim o = some c) :
    c.actor = o.actor ∧ c.project = o.project := by
  unfold deriveClaim at h
  split at h
  · cases h; exact ⟨rfl, rfl⟩
  · cases h

/-! ## Refusal surfaces — effect side -/

/-- Wrong actor does not satisfy the effect rule: standing is not
    transferable at the gate. -/
theorem wrong_actor_not_permitted (c : StandingClaim) (req : PromoteRequest)
    (h : c.actor ≠ req.actor) : permitsPromote c req = false := by
  simp [permitsPromote, h]

/-- Wrong project does not satisfy the effect rule: standing is scoped,
    not ambient. -/
theorem wrong_project_not_permitted (c : StandingClaim) (req : PromoteRequest)
    (h : c.project ≠ req.project) : permitsPromote c req = false := by
  simp [permitsPromote, h]

/-- End-to-end refusal: an observation about actor A never funds a promote
    request by actor B ≠ A, through any derived claim. -/
theorem other_actors_observation_never_permits
    (o : StandingObservation) (req : PromoteRequest)
    (h : o.actor ≠ req.actor) :
    ∀ c, deriveClaim o = some c → permitsPromote c req = false := by
  intro c hc
  have := (derived_claim_matches_observation hc).1
  exact wrong_actor_not_permitted c req (this ▸ h)

/-! ## Doctrine -/

def doctrine : List String :=
  [ "standing derives only from admitted collector testimony over an active basis",
    "schedule, operator ack, and model output are not standing — each refusal is a theorem",
    "revocation reaches the derivation; no claim carries a revoked basis",
    "actor_has_standing is scoped to (actor, project); it is not ambient and not transferable" ]

/-! ## Specimens -/

def goodObs : StandingObservation :=
  { source := .standingCollector, actor := "actor-a", project := "proj-x"
  , basis := .active }

def promoteReq : PromoteRequest := { actor := "actor-a", project := "proj-x" }

-- Runnable demonstrations:
#eval deriveClaim goodObs                                        -- some {actor-a, proj-x}
#eval deriveClaim { goodObs with basis := .revoked }             -- none
#eval deriveClaim { goodObs with source := .schedule }           -- none
#eval deriveClaim { goodObs with source := .operatorAck }        -- none
#eval deriveClaim { goodObs with source := .modelOutput }        -- none
#eval permitsPromote { actor := "actor-a", project := "proj-x" } promoteReq  -- true
#eval permitsPromote { actor := "actor-b", project := "proj-x" } promoteReq  -- false (wrong actor)
#eval permitsPromote { actor := "actor-a", project := "proj-y" } promoteReq  -- false (wrong project)

#eval doctrine

end Admissibility.StandingProfileSpecimen
