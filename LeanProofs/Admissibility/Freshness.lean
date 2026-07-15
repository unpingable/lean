/-
  Custody-Class: PUBLIC-SHIPPED

  Admissibility — Freshness kernel (metric-time admissibility axis).

  Keeper:
    Expired evidence cannot prove current standing.
    Future-issued evidence cannot prove current standing.
    Incoherent intervals cannot prove standing.
    Excessive clock divergence makes the assessment unsafe.

  Metric-time sibling to the kernel's existing ordinal-time apparatus
  (Step sequences in `StateTransition`, `WeaklyLessPermissive` preorder
  in `Corrective`, before/after pairs in `ClosureEligibility`,
  `RevocationStore` evolution). Where the ordinal apparatus answers
  *"did this happen before that,"* this module answers *"is this
  timestamp within an acceptable window."*

  Canonical consumer: `~/git/standing` — the workload-identity / grant
  authorization tool. Standing's `AssessmentResult` enum has nine
  verdict kinds; four are explicitly temporal (`Expired`, `NotYetValid`,
  `ReplayDetected`, `AssessmentCompromised`). Three of those four are
  metric-time-shaped and are formalized here:

    Expired                          ↔ ¬ (now ≤ expires + skew)
    NotYetValid                      ↔ ¬ ((issued - skew) ≤ now)
    AssessmentCompromised (incoherent) ↔ expires ≤ issued
    AssessmentCompromised (divergence) ↔ ¬ (|now - issued| ≤ maxDiv)

  The fourth temporal verdict (`ReplayDetected`) is sequence-position-
  keyed rather than metric-keyed; it stays in the kernel's ordinal
  apparatus and is not formalized here.

  Runtime correspondence receipt (historically the promotion context):
    Standing's `AssessmentResult::AssessmentCompromised` is exactly the
    kernel's "gap" verdict applied to metric-time admissibility — and
    the Lean kernel previously could not express that the gap was
    *temporal* rather than basis-, precedence-, or standing-shaped.
    This module closes that asymmetry.

  Scope fences:
    - This module formalizes *metric-time freshness for standing
      evidence*. It does NOT formalize ordinal/state-evolution time —
      that lives in `Corrective`, `CorrectiveBoundary`,
      `ClosureEligibility`, `StateTransition`.
    - It does NOT model replay caches or sequence-position semantics.
    - It does NOT model signature, audience, key-ID, or version
      checks. Those are the five non-temporal verdicts in Standing's
      `AssessmentResult`; they compose at the consumer side, not here.
    - It is NOT `Δt.lean`. Composition with other admissibility
      kernels (`FiatAdmissibility`, `NumericalAdmissibility`,
      `SurfaceAuthorization`, `RecoveryMargin`, `ClosureEligibility`)
      is explicitly deferred — same defer-marker pattern as
      `FiatAdmissibility`.

  Sibling modules in `LeanProofs/Admissibility/`:
    Authority              — verdict algebra (Layer 0)
    StateTransition        — mutation algebra
    Derivation             — read-side bridge
    Execution              — authorized step composition
    Corrective             — corrective transitions as down-edges
    CorrectiveBoundary     — boundary-result module
    WitnessInvariance      — witness behavior under perturbation
    FiatAdmissibility      — artifact-kind × use-kind axis
    NumericalAdmissibility — numerical-kind axis
    SurfaceAuthorization   — cause-attribution refusal gate
    PublicReceiptRefinement — receipt-refinement recovery doctrine
    ClosureEligibility     — end-of-interval closure refusal
    RecoveryMargin         — visibility ≠ recovery-capacity gap

  This module is the eighth refusal-gate / axis-kernel sibling.

  Related doctrine notes (papers repo):
    ~/git/papers/working/admissibility-decay-family-note.md
      Descriptive family covering five "license persists after admissibility
      failure" primitives. This Freshness kernel is the evidence-side
      metric-time substrate: when the family invariant runs over time-bearing
      evidence, `Fresh` is the licensing relation that may expire while the
      artifact persists. NOT a sixth family axis; the kernel is upstream of
      every axis whose `X` is time-bearing evidence.

    ~/git/papers/working/commitment-standing-decay-candidate.md
      Operational-standing axis (admissibility-set membership at time t).
      Distinct from this kernel's metric-time freshness: operational standing
      can decay while evidence is fresh, and evidence can expire while
      operational standing persists. The header keeper "Expired evidence
      cannot prove current standing" governs which sense of "standing"
      Freshness applies to.

    ~/git/papers/working/vocabulary/standing-three-senses.md
      Disambiguation of three distinct senses of "standing" across the
      corpus: state-fact (this repo's Derivation.lean), operational
      (commitment-standing-decay), and provable-now (this kernel). Glossary
      only; not a primitive, not doctrine.

  Custody:
    This module is canonical only via its commit hash + lake build
    proof gate + ratification rule on changes to `Time` / its
    operations / `TemporallyCoherent` / `DivergenceAcceptable` /
    `WithinValidity` / `Fresh`. A definition matching this signature
    elsewhere does not inherit the canonical anchoring of this file.
-/

namespace Admissibility.Freshness

/-! ### Opaque metric time

Time and Duration are conflated under a single opaque type. Concrete
consumers (Standing, hypothetical others) supply real types — chrono's
`DateTime<Utc>` plus `chrono::Duration` collapse into one ordered
abelian-group-shaped type at the abstraction this kernel needs.

The kernel proves invariants of the *shape*, not of the underlying
type. Concretizing to `Nat` / `Int` would leak structural facts into
theorems and break the abstraction over real consumer types. Keep
opaque. -/

axiom Time : Type
axiom Time.le : Time → Time → Prop
axiom Time.add : Time → Time → Time
axiom Time.sub : Time → Time → Time
axiom Time.absSub : Time → Time → Time

instance : LE Time := ⟨Time.le⟩
noncomputable instance : Add Time := ⟨Time.add⟩
noncomputable instance : Sub Time := ⟨Time.sub⟩

/-! ### Positive predicates

The three sub-predicates of `Fresh`. Each maps directly onto a step
of Standing's `verify_identity` function. -/

/-- The issued/expires interval is coherent: issued precedes expires
    in the ordering. Standing's `verify_identity` step 2 returns
    `AssessmentCompromised` when this fails — either a compromised
    issuer or a clock disaster. -/
def TemporallyCoherent (issued expires : Time) : Prop :=
  issued ≤ expires ∧ ¬ (expires ≤ issued)

/-- Verifier and issuer clocks are within acceptable divergence.
    Standing's `verify_identity` step 3 returns
    `AssessmentCompromised` when this fails — the freshness assessment
    cannot be trusted because the two clocks have drifted too far. -/
def DivergenceAcceptable (verifier issuer maxDiv : Time) : Prop :=
  Time.absSub verifier issuer ≤ maxDiv

/-- `now` falls within the validity window, with skew tolerance on
    both sides. Standing returns `NotYetValid` if `now` falls below
    the left bound, `Expired` if above the right bound, and `Valid`
    when both conjuncts hold. -/
def WithinValidity (now issued expires skew : Time) : Prop :=
  (issued - skew) ≤ now ∧ now ≤ (expires + skew)

/-- Time-bearing standing evidence is admissibly fresh when the
    issued interval is coherent, the clocks have not diverged beyond
    assessment-tolerance, and the present time falls within the
    skewed validity window. Composition of the three sub-predicates;
    consumer-side `AssessmentResult::Valid` requires this temporal
    component plus the non-temporal checks (signature, audience,
    version, key ID, replay) that compose at the consumer side and
    are outside this module's scope. -/
def Fresh (now issued expires skew maxDiv : Time) : Prop :=
  TemporallyCoherent issued expires ∧
  DivergenceAcceptable now issued maxDiv ∧
  WithinValidity now issued expires skew

/-! ### Negative theorems — one per failure mode

Each theorem says: if the corresponding sub-predicate's conjunct
fails, the evidence is not Fresh. Proofs are intro-elim through the
nested conjunction; no ordering axioms required. The negative shape
is load-bearing — it lets a consumer prove that a specific failure
condition rules out admissibility without having to construct a
positive witness. -/

/-- If `now` exceeds the right edge of the skewed validity window,
    the evidence is not Fresh. Mirrors Standing's
    `AssessmentResult::Expired`. -/
theorem expired_not_fresh
    {now issued expires skew maxDiv : Time}
    (h : ¬ (now ≤ expires + skew)) :
    ¬ Fresh now issued expires skew maxDiv := by
  intro hfresh
  exact h hfresh.2.2.2

/-- If `now` precedes the left edge of the skewed validity window,
    the evidence is not Fresh. Mirrors Standing's
    `AssessmentResult::NotYetValid`. -/
theorem not_yet_valid_not_fresh
    {now issued expires skew maxDiv : Time}
    (h : ¬ ((issued - skew) ≤ now)) :
    ¬ Fresh now issued expires skew maxDiv := by
  intro hfresh
  exact h hfresh.2.2.1

/-- If the issued/expires interval is incoherent in the direction
    `expires ≤ issued`, the evidence is not Fresh. Covers one of two
    failure modes of `TemporallyCoherent` under opaque `Time.le`.
    Mirrors Standing's `AssessmentCompromised` branch for
    temporally-incoherent claims (active-incoherence direction:
    expires actually precedes or equals issued). -/
theorem incoherent_not_fresh
    {now issued expires skew maxDiv : Time}
    (h : expires ≤ issued) :
    ¬ Fresh now issued expires skew maxDiv := by
  intro hfresh
  exact hfresh.1.2 h

/-- If `issued ≤ expires` fails to hold, the evidence is not Fresh.
    Sibling to `incoherent_not_fresh`; covers the second failure mode
    of `TemporallyCoherent` under opaque `Time.le`. In a total order
    `¬ (issued ≤ expires)` and `expires < issued` collapse, but since
    `Time.le` is kept opaque (no order axioms), both failure modes
    are structurally distinct and each gets its own refusal theorem.
    Also mirrors Standing's `AssessmentCompromised` for
    temporally-incoherent claims (absent-precedence direction:
    issued does not actually precede expires). -/
theorem not_precedes_not_fresh
    {now issued expires skew maxDiv : Time}
    (h : ¬ (issued ≤ expires)) :
    ¬ Fresh now issued expires skew maxDiv := by
  intro hfresh
  exact h hfresh.1.1

/-- If clock divergence between verifier and issuer exceeds the
    assessment-tolerance bound, the evidence is not Fresh. Mirrors
    Standing's `AssessmentCompromised` branch for excessive clock
    divergence — the freshness check itself cannot be trusted. -/
theorem divergence_excessive_not_fresh
    {now issued expires skew maxDiv : Time}
    (h : ¬ (Time.absSub now issued ≤ maxDiv)) :
    ¬ Fresh now issued expires skew maxDiv := by
  intro hfresh
  exact h hfresh.2.1

end Admissibility.Freshness
