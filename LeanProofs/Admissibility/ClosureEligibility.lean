/-
  Custody-Class: ANNEX

  Admissibility — ClosureEligibility.

  Refusal kernel for closure verdicts on shift-bounded operations.
  The theorem is portable: *survival alone does not authorize closure.*

  Keeper:
    Survival is a handoff condition, not a closure condition.

  Sharper:
    A survived shift with unresolved threat or depleted operator slack
    must emit handoff, not closure.

  Invariant proved:
    closure ⇔ (survived ∧ resolved ∧ slack-available).
    Any deficit on any of the three dimensions forces handoff or incident.

  Consumers:
    Nightshift-style operational doctrines are the obvious downstream
    consumer (overnight on-call, security monitoring, real-time platform
    moderation, regulatory surveillance). Other consumers may apply
    wherever the question is "does a survived interval authorize closing
    out an obligation?" The kernel does not depend on any particular
    operational substrate.

  Custody:
    A `closure` verdict claims the system has reached a stable state.
    A `handoffRequired` verdict claims the operator has reached the end
    of their interval but the system has not. Confusing these is the
    operational analog of admitting visible survival as if it were
    underlying resolution — same family resemblance as admitting
    testimony as if it were substrate theory.

  Operator-family membership:
    Instantiates the row `Survival ⇏ ClosureEligibility` in the
    `surface ⇏ substance` operator-family table at
    `working/tooltheory/refusal-kernel-to-refusal-receipt-seam.md`,
    which catalogs verified refusal-kernel instances on the books
    (RecoveryMargin, ClosureEligibility, ConsolidationDenial; plus
    the spec-level `specifications/signed_is_not_witnessed.md`).
    The seam note also carries the layer split (refusal kernel /
    refusal algebra / refusal calculus) and the brake against
    promoting algebra-shape recognition to calculus-shape composition
    without composition theorems.

  Relation to existing kit:
    - Sibling to RecoveryMargin: that module governs *within-interval*
      visible vs. recovery-capacity; this module governs *end-of-interval*
      survival vs. closure.
    - Sibling to SurfaceAuthorization: both encode refusal gates over
      claims (cause-specific authority / resolution-specific closure)
      given insufficient discriminating evidence (no breaker / threat
      not resolved or slack depleted).
    - Same family resemblance as the admissibility-decay candidates:
      a visible outcome is being asked to license a substantive claim
      it does not, by itself, support.

  Scope fence:
    This kernel only models ordinary closure through `Verdict.closure`.
    It does not model retirement, waiver, supersession, abandonment,
    reset, escalation, or externally authorized closure paths.

    The absorption theorem proves only that a direct transition from
    a handoff-eligible state to a closure verdict requires a
    closure-relevant non-regressing improvement in the modeled
    threat/slack dimensions. It does not prove temporal persistence
    over arbitrary traces, nor does it prove that all real-world
    closure paths are blocked absent such an event.

    Out of scope (deferred to future kernels):
      * Trace model — persistence across intervals / "cannot wait out
        an obligation."
      * Disposition model — waiver, supersession, retirement,
        abandonment, escalation.
      * Authority model — who is allowed to waive or supersede.
      * Resolution-event logging — this kernel proves any valid
        handoff→closure transition contains an improvement; it does
        not enforce that the improvement was logged or witnessed.
-/

namespace Admissibility.ClosureEligibility

/-- Whether the systemic threat has been resolved or merely deflected
    for the duration of the interval. -/
inductive ThreatState where
  | resolved
  | unresolved
deriving DecidableEq, Repr

/-- Whether the operator's slack / maneuver capacity remains available
    at end-of-interval, or has been consumed by within-interval
    defensive action. -/
inductive SlackState where
  | available
  | depleted
deriving DecidableEq, Repr

/-- Whether the bounded interval terminated visibly intact or visibly
    failed. -/
inductive IntervalOutcome where
  | survived
  | failed
deriving DecidableEq, Repr

/-- The end-of-interval verdict for the modeled closure path.
    `closure`: the system has reached a resolved, stable state and
               the ordinary-closure obligation may be discharged. This
               verdict models only ordinary closure; retirement,
               waiver, supersession, and other disposition paths are
               not modeled here.
    `handoffRequired`: the interval survived but without
                       ordinary-closure eligibility — either threat
                       remains unresolved, or operator slack is
                       depleted, or both. Downstream responsibility
                       must be transferred with explicit state
                       preservation.
    `incident`: the interval visibly failed; post-incident process
                applies. -/
inductive Verdict where
  | closure
  | handoffRequired
  | incident
deriving DecidableEq, Repr

/-- Total verdict function. Closure is permitted only when survival,
    threat-resolution, and available slack all coincide. -/
def verdict
    (outcome : IntervalOutcome)
    (threat : ThreatState)
    (slack : SlackState) : Verdict :=
  match outcome, threat, slack with
  | .failed,   _,          _          => .incident
  | .survived, .resolved,  .available => .closure
  | .survived, _,          _          => .handoffRequired

/-! ### Characterization lemmas (the receipts) -/

/-- `handoffRequired` is emitted exactly when the interval survived
    and at least one closure dimension is deficient (threat unresolved
    or slack depleted). This is the named characterization the main
    absorption theorem rests on; downstream proofs should depend on
    this lemma rather than on `simp [verdict]`. -/
theorem verdict_handoffRequired_iff
    {outcome : IntervalOutcome} {threat : ThreatState} {slack : SlackState} :
    verdict outcome threat slack = Verdict.handoffRequired ↔
      outcome = IntervalOutcome.survived
        ∧ (threat = ThreatState.unresolved ∨ slack = SlackState.depleted) := by
  cases outcome <;> cases threat <;> cases slack <;> simp [verdict]

/-- `closure` is emitted exactly when survival, threat-resolution, and
    available slack all coincide. Named characterization; downstream
    proofs should depend on this lemma. -/
theorem verdict_closure_iff
    {outcome : IntervalOutcome} {threat : ThreatState} {slack : SlackState} :
    verdict outcome threat slack = Verdict.closure ↔
      outcome = IntervalOutcome.survived
        ∧ threat = ThreatState.resolved
        ∧ slack = SlackState.available := by
  cases outcome <;> cases threat <;> cases slack <;> simp [verdict]

/-! ### Local refusal lemmas -/

/-- Unresolved threat at survival forces handoff regardless of slack. -/
theorem survived_unresolved_requires_handoff
    (slack : SlackState) :
    verdict IntervalOutcome.survived ThreatState.unresolved slack =
      Verdict.handoffRequired := by
  cases slack <;> rfl

/-- Depleted slack at survival forces handoff regardless of threat. -/
theorem survived_depleted_requires_handoff
    (threat : ThreatState) :
    verdict IntervalOutcome.survived threat SlackState.depleted =
      Verdict.handoffRequired := by
  cases threat <;> rfl

/-- Kernel claim: survival alone does not authorize closure. There
    exists a survived configuration whose verdict is not closure. -/
theorem survival_alone_does_not_authorize_closure :
    ∃ threat slack,
      verdict IntervalOutcome.survived threat slack ≠ Verdict.closure := by
  refine ⟨ThreatState.unresolved, SlackState.available, ?_⟩
  decide

/-- Failure is incident regardless of threat or slack — the gate does not
    let other dimensions launder away a visible failure. -/
theorem failed_outcome_is_incident
    (threat : ThreatState) (slack : SlackState) :
    verdict IntervalOutcome.failed threat slack = Verdict.incident := by
  cases threat <;> cases slack <;> rfl

/-- Closure requires resolution and slack. Corollary of
    `verdict_closure_iff`, retained as a named one-direction implication
    because most downstream uses want the consequence rather than the
    iff. -/
theorem closure_requires_resolution_and_slack
    {outcome : IntervalOutcome} {threat : ThreatState} {slack : SlackState}
    (h : verdict outcome threat slack = Verdict.closure) :
    outcome = IntervalOutcome.survived
      ∧ threat  = ThreatState.resolved
      ∧ slack   = SlackState.available :=
  verdict_closure_iff.mp h

/-! ### Non-regression and closure-relevant improvement -/

/-- Threat axis does not regress: `resolved → unresolved` is forbidden.
    Refuses to count a transition that gives up resolution as
    closure-relevant progress. -/
def ThreatState.NoRegress (before after : ThreatState) : Prop :=
  ¬ (before = ThreatState.resolved ∧ after = ThreatState.unresolved)

/-- Slack axis does not regress: `available → depleted` is forbidden.
    Refuses to count a transition that gives up slack as
    closure-relevant progress. -/
def SlackState.NoRegress (before after : SlackState) : Prop :=
  ¬ (before = SlackState.available ∧ after = SlackState.depleted)

/-- A pair of (threat, slack) configurations exhibits closure-relevant
    improvement iff *neither axis regresses* and *at least one axis
    strictly improves*. Trading a deficit on one axis for surplus on
    another does not satisfy this predicate.

    The predicate names exactly what the absorption theorem licenses:
    not "resolution occurred," not "closure was justified," not
    "obligation persisted forever," but: *you cannot reach closure
    from a handoff state by swapping one deficit for another.* -/
def HasClosureRelevantImprovement
    (before after : ThreatState × SlackState) : Prop :=
  ThreatState.NoRegress before.1 after.1
    ∧ SlackState.NoRegress before.2 after.2
    ∧ ((before.1 = ThreatState.unresolved ∧ after.1 = ThreatState.resolved)
        ∨ (before.2 = SlackState.depleted ∧ after.2 = SlackState.available))

/-! ### Absorption theorem -/

/-- Absorption theorem: a direct handoff→closure transition requires
    closure-relevant improvement. If verdict at configuration T₁ is
    `handoffRequired` and verdict at configuration T₂ is `closure`,
    then between those two configurations at least one closure
    dimension must have strictly improved *without* regression on
    the other.

    Scope: this proves only that a *direct* transition contains an
    improvement. It does not prove temporal persistence over arbitrary
    traces. It does not prove that closure-shaped outcomes outside
    `Verdict.closure` (waiver, retirement, supersession, etc.) are
    blocked — those are not modeled by this kernel. It does not
    enforce that the improvement was logged or witnessed — the
    consuming layer must do that work.

    Operationally: when a downstream handoff process emits closure
    against a state that was previously handoff-eligible, this theorem
    guarantees the kernel-modeled threat/slack dimensions actually
    improved. It is the proof-side receipt for "no closure by
    trade." -/
theorem closure_after_handoff_requires_closure_relevant_improvement
    {before_outcome after_outcome : IntervalOutcome}
    {before_threat after_threat : ThreatState}
    {before_slack after_slack : SlackState}
    (h_before : verdict before_outcome before_threat before_slack
                  = Verdict.handoffRequired)
    (h_after  : verdict after_outcome  after_threat  after_slack
                  = Verdict.closure) :
    HasClosureRelevantImprovement
      (before_threat, before_slack) (after_threat, after_slack) := by
  obtain ⟨_, hb⟩ := verdict_handoffRequired_iff.mp h_before
  obtain ⟨_, ha_t, ha_s⟩ := verdict_closure_iff.mp h_after
  refine ⟨?nonregT, ?nonregS, ?strict⟩
  · rintro ⟨_, har⟩
    rw [ha_t] at har
    cases har
  · rintro ⟨_, har⟩
    rw [ha_s] at har
    cases har
  · rcases hb with ht | hs
    · exact Or.inl ⟨ht, ha_t⟩
    · exact Or.inr ⟨hs, ha_s⟩

end Admissibility.ClosureEligibility
