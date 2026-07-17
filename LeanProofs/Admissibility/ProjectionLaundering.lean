/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE

  Admissibility — ProjectionLaundering (terminal public evidence).

  Adjudicated in v13 as public evidence outside the exact stable surface. The
  paired negative+positive theorem structure has independent
  shape distinct from the existing CBA-vocabulary / FiatAdmissibility
  routing / WitnessInvariance / SurfaceAuthorization family.

  Companion working note:
    papers/working/tooltheory/projection-laundering.md
    (filed separately; this file is the witness, not the doctrine).

  Keepers:
    A projection may simplify evidence. It may not erase
    the conditions under which evidence was allowed to bind.

    The gate cannot enforce a predicate it cannot see.

  Sharper:
    Projection laundering is the representation-stage failure
    mode where compression erases the predicate a downstream
    custody gate requires in order to refuse consequential action.
    The kernel is two paired theorems over abstract
    `Belief / Artifact / Action` bindings:
      - negative: erasing projection + incautious policy yields
        a must-defer belief whose artifact-only routing acts
        consequentially.
      - positive: defer-preserving projection + defer-respecting
        policy makes the same artifact-only routing
        non-consequential for every must-defer belief.

  Structural relation to siblings:
    - CBA (compression-becomes-authority): essay-vocabulary parent;
      PL is the refusal-kernel form of CBA's
      "compression-authority laundering."
    - FiatAdmissibility: closest formal slot if PL were ever
      promoted. PL refines the artifact-kind × use-kind cell
      with a predicate-preservation axis.
    - WitnessInvariance: cousin under information-loss family.
      WI tests witness-output invariance under perturbation;
      PL tests deferral-signal invariance under projection.
    - SurfaceAuthorization: cause-attribution-axis sibling.
    - ConsequencePartition: policy-expressibility-axis sibling;
      shares the projection mechanism.
    - UncertaintyCustody (sketched in tooltheory): downstream
      composition partner. PL's `ArtifactSignalsDefer` is what
      UC's gate respects.

  Scope fence:
    - No Mathlib. No coercions to existing kernel modules.
    - No multi-stage pipeline calculus
      (composition with UC is prose, not theorem here).
    - No substrate-specific compression families.
    - Regression-built through `lake build AdmissibilityEvidence`; publication
      does not make it a member of the exact stable kernel root.

  Custody:
    Canonical anchoring of `Admissibility.ProjectionLaundering`.
    A definition matching this signature elsewhere does not
    inherit canonical anchoring from this file.
-/

namespace Admissibility.ProjectionLaundering

universe u v w

/-! ## Predicates over projections -/

/-- `project` erases a custody-relevant deferral predicate:
    some belief that must be deferred is projected to an artifact
    that fails to signal deferral. -/
def ErasesDefer
    {Belief : Type u} {Artifact : Type v}
    (MustDefer : Belief → Prop)
    (ArtifactSignalsDefer : Artifact → Prop)
    (project : Belief → Artifact) : Prop :=
  ∃ b : Belief, MustDefer b ∧ ¬ ArtifactSignalsDefer (project b)

/-- `project` preserves the deferral predicate: every must-defer
    belief is projected to a defer-signalling artifact. -/
def PreservesDefer
    {Belief : Type u} {Artifact : Type v}
    (MustDefer : Belief → Prop)
    (ArtifactSignalsDefer : Artifact → Prop)
    (project : Belief → Artifact) : Prop :=
  ∀ b : Belief, MustDefer b → ArtifactSignalsDefer (project b)

/-! ## Artifact-only policy composition -/

/-- Belief is routed through the projection and then through
    the artifact-only policy. The composed map is what downstream
    consequences observe. -/
def ArtifactOnlyPolicy
    {Belief : Type u} {Artifact : Type v} {Action : Type w}
    (project : Belief → Artifact)
    (policy : Artifact → Action) : Belief → Action :=
  fun b => policy (project b)

/-- The policy treats absence-of-defer-signal as a license to act
    consequentially. The incautious shape. -/
def ArtifactOnlyIncautious
    {Artifact : Type v} {Action : Type w}
    (Consequential : Action → Prop)
    (ArtifactSignalsDefer : Artifact → Prop)
    (policy : Artifact → Action) : Prop :=
  ∀ a : Artifact,
    ¬ ArtifactSignalsDefer a → Consequential (policy a)

/-- The policy respects the artifact-level defer signal: when the
    signal is present, the policy refuses consequential action. -/
def PolicyRespectsDeferSignal
    {Artifact : Type v} {Action : Type w}
    (Consequential : Action → Prop)
    (ArtifactSignalsDefer : Artifact → Prop)
    (policy : Artifact → Action) : Prop :=
  ∀ a : Artifact, ArtifactSignalsDefer a → ¬ Consequential (policy a)

/-! ## Paired theorems -/

/-- Negative theorem. Erasing projection plus incautious
    artifact-only policy yields a state where the original
    belief demanded deferral but the composed route is
    consequential. -/
theorem projection_launders_deferral
    {Belief : Type u} {Artifact : Type v} {Action : Type w}
    (MustDefer : Belief → Prop)
    (Consequential : Action → Prop)
    (ArtifactSignalsDefer : Artifact → Prop)
    (project : Belief → Artifact)
    (policy : Artifact → Action)
    (h_erases :
      ErasesDefer MustDefer ArtifactSignalsDefer project)
    (h_policy_incautious :
      ArtifactOnlyIncautious Consequential ArtifactSignalsDefer policy) :
    ∃ b : Belief,
      MustDefer b ∧
      Consequential ((ArtifactOnlyPolicy project policy) b) := by
  rcases h_erases with ⟨b, h_def, h_no_signal⟩
  exact ⟨b, h_def, h_policy_incautious (project b) h_no_signal⟩

/-- Positive theorem. Defer-preserving projection plus
    defer-respecting policy blocks the laundering route: for every
    must-defer belief, the composed artifact-only route is
    non-consequential. -/
theorem loss_aware_projection_blocks_deferral_laundering
    {Belief : Type u} {Artifact : Type v} {Action : Type w}
    (MustDefer : Belief → Prop)
    (Consequential : Action → Prop)
    (ArtifactSignalsDefer : Artifact → Prop)
    (project : Belief → Artifact)
    (policy : Artifact → Action)
    (h_preserve :
      PreservesDefer MustDefer ArtifactSignalsDefer project)
    (h_policy_respects :
      PolicyRespectsDeferSignal Consequential ArtifactSignalsDefer policy) :
    ∀ b : Belief,
      MustDefer b →
      ¬ Consequential ((ArtifactOnlyPolicy project policy) b) := by
  intro b h_def
  exact h_policy_respects (project b) (h_preserve b h_def)

end Admissibility.ProjectionLaundering
