/-
  Custody-Class: SCRATCH

  DeadlockEscalation — fenced scratch slice, 2026-06-14. Not imported by
  `LeanProofs.lean`. Not part of any 1.0 surface. No paper anchor. No
  promotion path. NOT used as discharge for any doctrine. Compile-is-
  contact only. **Forward-looking** (multigov escalation Q2); models the
  invariants, not the unbuilt feature.

  ## The seam (continues DeadlockTrajectory)

  `DeadlockTrajectory` ends at `operatorRequired`. This file models what a
  *multi-governor* escalation must get right at that handoff. The reviewer's
  load-bearing point: the marquee theorem (`at_most_one_active_resolver`) is
  DECORATIVE — a partial resolver map is ≤1-valued by its type. The risk
  lives in five other invariants, all classification boundaries:

    1. concurrent equivalent observations COALESCE (key stable across observers)
    2. distinct issues do NOT merge (key injective across issues)
    3. a resolved occurrence does NOT suppress a later recurrence (epoch / ABA)
    4. a decision binds to the OCCURRENCE, not the lease token (survives rotation)
    5. options are a function of the issue basis, not the race-winner

  Plus the footgun: first-writer-wins is only ≤1-winner over a *linearizable*
  substrate; a fake CAS gives confident stampede.

  ## Division of labor (deliberate)

  Lean models the **classification boundaries** above. NOT modeled (it is the
  governor's Python, owned by the AG session): the CAS/lease implementation,
  the webhook/UI operator sink, the receipt store, retry counters, key
  normalization heuristics. And the *substrate* question — whether a real
  linearizable lease exists — is an operational precondition, not a theorem;
  here it is an explicit hypothesis (`AtomicLease`). Distributed multigov stays
  HELD until that substrate exists; in-process (one lock) is a separate call.

  ## Prior art (read-only, not imported)
    - LeanProofs/Scratch/DeadlockTrajectory.lean   (the family parent: → operatorRequired)
    - LeanProofs/Scratch/OperatorBasisGateInput.lean (the "make it unrepresentable" move, reused for options)
    - LeanProofs/Scratch/TemporalTrajectory.lean    (composition-failure family)
-/

namespace Admissibility.Scratch.DeadlockEscalation

/-! ## 1–2. Issue identity vs evidence — coalescing & injectivity

  Identity is observer-INVARIANT; evidence (chain_tip, observed_at) MOVES
  across concurrent observers. The key must be a function of identity only —
  then equivalent observers coalesce by construction, and the chain_tip bug
  is structurally impossible (evidence is not even an argument to the key). -/

structure IssueIdentity where
  kind : Nat        -- deadlock_kind
  artifact : Nat    -- blocked_artifact_id
  stateId : Nat     -- stable unresolved-transition / artifact-state id
  deriving DecidableEq, Repr

structure Evidence where
  chainTip : Nat    -- advances monotonically — DIFFERENT per concurrent observer
  observedAt : Nat
  deriving DecidableEq, Repr

structure Observation where
  identity : IssueIdentity
  evidence : Evidence
  deriving DecidableEq, Repr

/-- Correct key: identity only. Evidence is not in the channel. -/
def issueKey (o : Observation) : IssueIdentity := o.identity

/-- **Coalescing.** Two observers of the same issue, differing only in
    evidence (e.g. different `chainTip`), produce the SAME key. By
    construction — `issueKey` cannot see evidence. -/
theorem concurrent_observations_coalesce
    (id : IssueIdentity) (e1 e2 : Evidence) :
    issueKey ⟨id, e1⟩ = issueKey ⟨id, e2⟩ := rfl

/-- **Injectivity.** Distinct identities give distinct keys: distinct issues
    do not merge. -/
theorem distinct_issues_do_not_merge
    (o1 o2 : Observation) (h : o1.identity ≠ o2.identity) :
    issueKey o1 ≠ issueKey o2 := h

/-! ### The two failure modes the correct key avoids -/

/-- BAD (too fine): putting moving evidence in the key. -/
def badKeyWithTip (o : Observation) : IssueIdentity × Nat :=
  (o.identity, o.evidence.chainTip)

/-- chain_tip in the key SPLITS the same issue across concurrent observers →
    both escalate → stampede. The fail-loud-but-wrong direction. -/
theorem chain_tip_in_key_splits_same_issue :
    ∃ (id : IssueIdentity) (e1 e2 : Evidence),
      badKeyWithTip ⟨id, e1⟩ ≠ badKeyWithTip ⟨id, e2⟩ :=
  ⟨⟨0, 0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, by decide⟩

/-- BAD (too coarse): dropping a distinguishing identity field. -/
def coarseKey (o : Observation) : Nat × Nat :=
  (o.identity.kind, o.identity.artifact)   -- drops stateId

/-- A too-coarse key MERGES distinct issues (differing only in `stateId`) →
    one silently masks the other. The fail-OPEN direction — the dangerous
    one. -/
theorem coarse_key_merges_distinct_issues :
    ∃ o1 o2 : Observation, o1.identity ≠ o2.identity ∧ coarseKey o1 = coarseKey o2 :=
  ⟨⟨⟨0, 0, 1⟩, ⟨0, 0⟩⟩, ⟨⟨0, 0, 2⟩, ⟨0, 0⟩⟩, by decide, rfl⟩

/-! ## 3. Occurrence epoch — recurrence safety (the ABA bug)

  Content-addressing alone: a recurrence has the same key as a resolved
  issue → swallowed as stale (resolve once = immune forever). An occurrence
  is `(key, epoch)`: collides for concurrent observers (same epoch), fresh
  across recurrences (new epoch). The temporal axis, again. -/

structure Occurrence where
  key : IssueIdentity
  epoch : Nat
  deriving DecidableEq, Repr

/-- Epoch-aware suppression rule: an incoming occurrence is suppressed by a
    resolved one iff they are equal (same key AND same epoch). -/
def suppressedBy (resolved incoming : Occurrence) : Bool :=
  decide (resolved = incoming)

/-- **Recurrence safety.** A later recurrence (same key, new epoch) is NOT
    suppressed by the resolved occurrence — the suppression rule returns
    `false`. This backs the name with an actual suppression check, not bare
    inequality. -/
theorem resolved_does_not_suppress_recurrence
    (k : IssueIdentity) (e1 e2 : Nat) (h : e1 ≠ e2) :
    suppressedBy ⟨k, e1⟩ ⟨k, e2⟩ = false := by
  have hne : (⟨k, e1⟩ : Occurrence) ≠ ⟨k, e2⟩ := by
    intro heq; rw [Occurrence.mk.injEq] at heq; exact h heq.2
  simp [suppressedBy, hne]

/-- Content-only suppression rule (the bug): no epoch, key the bare identity. -/
def suppressedByCA (resolved incoming : IssueIdentity) : Bool :=
  decide (resolved = incoming)

/-- The ABA contrast, witnessed as actual suppression: under content-only
    addressing a recurrence (same key) IS suppressed — `true`. Resolve the
    deadlock once and you immunize yourself against ever escalating that
    shape again. This is what the epoch exists to prevent. -/
theorem content_only_suppresses_recurrence (k : IssueIdentity) :
    suppressedByCA k k = true := by
  simp [suppressedByCA]

/-! ## 4. Decision binds to the occurrence, not the lease token

  The escalation lease (short, rotating, prevents double-ping) and the
  operator-decision binding (must outlive rotation) are DIFFERENT lifetimes.
  Bind the decision to the occurrence basis; then operator latency > lease
  TTL does not throw away the human's answer. -/

structure EscalationState where
  occurrence : Occurrence
  leaseToken : Nat        -- rotates as the lease changes hands
  deriving Repr

structure Decision where
  forOccurrence : Occurrence   -- bound to the occurrence, NOT a token
  deriving Repr

/-- A decision applies iff it is for the current occurrence — independent of
    the lease token. -/
def decisionApplies (d : Decision) (s : EscalationState) : Bool :=
  decide (d.forOccurrence = s.occurrence)

/-- **Decision survives lease rotation.** Bound to the occurrence, the
    decision applies under ANY lease token — in particular across any
    rotation `t1 → t2` (`t1 ≠ t2`), since `decisionApplies` never reads the
    token. The human's answer is not discarded when the lease rotates out
    from under it. Stronger than requiring a specific `t1 ≠ t2`: it holds
    for all token pairs. -/
theorem decision_survives_lease_rotation
    (d : Decision) (occ : Occurrence) (t1 t2 : Nat)
    (h : d.forOccurrence = occ) :
    decisionApplies d ⟨occ, t1⟩ = true ∧ decisionApplies d ⟨occ, t2⟩ = true := by
  unfold decisionApplies
  constructor <;> simp [h]

/-- Contrast: a token-bound decision dies on rotation — valid under token 7,
    rejected as stale after rotation to 8. This is the discarded-answer bug. -/
def tokenBinds (dToken : Nat) (s : EscalationState) : Bool :=
  decide (dToken = s.leaseToken)

theorem token_bound_decision_dies_on_rotation :
    ∃ (dToken : Nat) (occ : Occurrence) (t1 t2 : Nat),
      tokenBinds dToken ⟨occ, t1⟩ = true ∧ tokenBinds dToken ⟨occ, t2⟩ = false :=
  ⟨7, ⟨⟨0, 0, 0⟩, 0⟩, 7, 8, by decide, by decide⟩

/-! ## 5. Options are a function of the issue basis, not the race-winner

  Letting the CAS-winner author `options`/`recommended_default` hands the
  operator's choice architecture to first-to-write, not best-informed. Make
  the template a function of `(issueKey, basis)` — then it is the SAME no
  matter who won. The `OperatorBasisGateInput` move: the leaseholder is not
  an argument, so winner-authored options are unrepresentable. -/

abbrev Options := Nat

/-- Deterministic from the issue basis. No leaseholder argument exists. -/
def renderOptions (k : IssueIdentity) (basis : Nat) : Options := k.kind + basis

-- Structural guarantee (a TYPE fact, not a theorem — the
-- `OperatorBasisGateInput` move): `renderOptions : IssueIdentity → Nat →
-- Options` has no leaseholder argument, so "the race-winner authored the
-- options" is *unrepresentable*. Asserting it as a theorem
-- (`∀ lh1 lh2, render = render`) would be decorative — the leaseholders go
-- unused, which is precisely the point and precisely why it is not worth a
-- theorem. The contrast below shows what the absence buys.

/-- Contrast: options authored BY the leaseholder vary with who won — the
    race-winner controls the operator's menu. This is the shape `renderOptions`
    refuses by leaving `leaseholder` out of its type. -/
def leaseholderOptions (leaseholder : Nat) : Options := leaseholder

theorem leaseholder_authored_options_vary :
    ∃ lh1 lh2 : Nat, leaseholderOptions lh1 ≠ leaseholderOptions lh2 :=
  ⟨0, 1, by decide⟩

/-! ## 6. The footgun: ≤1 winner is conditional on a linearizable lease

  `at_most_one_active_resolver` is decorative (a partial map is ≤1-valued by
  type). The real content: first-writer-wins is ≤1-winner ONLY over a
  linearizable substrate. Model that substrate as the hypothesis
  `AtomicLease`. Uniqueness REQUIRES it; drop it and two winners — confident
  stampede — are representable. The bridge-price shape. -/

/-- The linearizable-lease guarantee: at most one governor wins. A property
    the SUBSTRATE must provide; not a free fact of "we wrote a CAS." -/
def AtomicLease {Gov : Type} (won : Gov → Prop) : Prop :=
  ∀ g1 g2, won g1 → won g2 → g1 = g2

/-- Sufficiency: `AtomicLease` gives ≤1 winner. (Honest name — this proves
    atomicity SUFFICES; the NECESSITY direction — uniqueness fails without it
    — is `fake_cas_admits_two_winners` below. Together: ≤1-winner iff a
    linearizable lease.) -/
theorem atomic_lease_gives_unique_winner
    {Gov : Type} (won : Gov → Prop) (h : AtomicLease won)
    {g1 g2 : Gov} (h1 : won g1) (h2 : won g2) : g1 = g2 :=
  h g1 g2 h1 h2

/-- **Fake CAS = confident stampede.** Without `AtomicLease`, two distinct
    winners are representable — and the system believes it is not a
    stampede (worse than no lease, because it removes downstream dedup).
    The negative control: the uniqueness theorem genuinely consumes the
    `AtomicLease` hypothesis. -/
theorem fake_cas_admits_two_winners :
    ∃ (Gov : Type) (won : Gov → Prop) (g1 g2 : Gov),
      g1 ≠ g2 ∧ won g1 ∧ won g2 ∧ ¬ AtomicLease won := by
  refine ⟨Bool, fun _ => True, false, true, by decide, trivial, trivial, ?_⟩
  intro hatomic
  exact (by decide : (false : Bool) ≠ true) (hatomic false true trivial trivial)

end Admissibility.Scratch.DeadlockEscalation
