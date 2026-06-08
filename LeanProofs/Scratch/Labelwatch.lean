/-
  Custody-Class: SCRATCH

  Labelwatch — first non-synthetic pressure test, 2026-06-08. Not
  imported by `LeanProofs.lean`. Not part of any 1.0 surface. No
  paper anchor. No promotion path. NOT used as discharge for any
  doctrine.

  Goal: formalize the smallest calculus vocabulary that can represent
  Labelwatch specimens 001 and 002 without laundering testimony into
  constraint.

  Discipline (per DeepSeek's corrected frame, operator-confirmed):

    Do NOT prove "LabelObserved → ¬ ConstraintApplied" — that
    confuses factual non-occurrence with inadmissibility.

    DO prove statements about permitted derivations from evidence
    bundles:
      - LabelObserved alone cannot derive AdmissibleClaim(ConstraintApplied ...)
      - LabelObserved + PolicyDocumented still cannot derive
        AdmissibleClaim(ConstraintApplied ...)
      - LabelObserved + PolicyDocumented + RenderObserved CAN derive
        the admissible constraint claim, if render context and
        timestamps line up.

    The non-laundering property is about which derivations are
    licensed from explicit evidence bundles, not about whether the
    world-state secretly contained an applied constraint.

  Required distinctions (from the handoff packet, expanded):
    - LabelObservation       : testimony witnessed
    - PolicyDocumentation    : source artifact / public rule documented
    - PolicyWitness          : live consumer version/application attested
    - RenderObservation      : execution receipt in a specific render_context
    - ConstraintClaim        : claim shape space
    - EvidenceBundle         : the explicit evidence bundle
    - ConversionGap          : failure-mode classification

  Specimen 001 (encoded as spec001 below):
    LabelObserved        = yes
    PolicyDocumented     = yes
    PolicyWitness        = no
    RenderObserved       = no
    Admissible:    documented conversion path exists under named policy artifact
    Inadmissible:  this post was actually constrained for any concrete render

  Specimen 002 (encoded as spec002 below):
    LabelObserved        = yes
    PolicyDocumented     = no    (no default-client conversion documented)
    PolicyWitness        = no
    RenderObserved       = no
    Admissible:    label exists and no default-client conversion is documented
                   (audited absence)
    Inadmissible:  any default-client constraint followed from the
                   third-party label

  Open formal questions (recorded, choice noted; not resolved):
    Q1. Is PolicyDocumented a basis_state or a separate evidence
        class below witness?
        — This spike treats PolicyDocumented as a separate evidence
          class: it witnesses *artifact existence*, not consumer
          application. PolicyWitness is the separate evidence class
          for live consumer attestation.
    Q2. Is render_context part of the witness identity?
        — Yes for the claim shape: ConstraintClaim.constraint_applied
          carries renderContext as a parameter, so different contexts
          produce different claims. The coherence check does NOT
          constrain renderContext; only subject/constraint/label
          identity and timing.
    Q3. Conversion-witness gap vs execution gap: separate constructors
        or indexed states?
        — Separate constructors in ConversionGap. Spec001 exhibits
          execution_gap_policy_present; Spec002 exhibits
          conversion_witness_gap_no_consumer.
-/

namespace Admissibility.Scratch.Labelwatch

/-! ## Evidence types (the minimum vocabulary) -/

/-- A LabelObservation: testimony that a label was applied to a subject. -/
structure LabelObservation where
  label : String
  subject : String
  observer : String
  timestamp : Nat
  deriving DecidableEq, Repr

/-- A PolicyDocumentation: a published artifact stating a label→constraint
    rule. Witnesses *artifact existence*, not consumer application. -/
structure PolicyDocumentation where
  artifactId : String
  label : String
  constraint : String
  documenter : String
  publishedAt : Nat
  deriving DecidableEq, Repr

/-- A PolicyWitness: live consumer attestation that a specific consumer
    version applied a policy. Witnesses *consumer-side application*.
    Distinct from PolicyDocumentation (artifact existence). Distinct
    from RenderObservation (execution on a specific subject).

    Not consumed by any admissibility constructor in this minimum spike
    — its presence in the bundle is recorded for Spec001 (which has
    PolicyWitness = no/partial) without forcing a constructor that
    relies on it. Available for future specimens. -/
structure PolicyWitness where
  artifactId : String       -- references the policy artifact
  consumer : String
  version : String
  witnessedAt : Nat
  deriving DecidableEq, Repr

/-- A RenderObservation: execution receipt that the constraint was
    applied on a specific render_context. -/
structure RenderObservation where
  subject : String
  constraint : String
  observer : String
  renderContext : String
  timestamp : Nat
  deriving DecidableEq, Repr

/-- The space of admissible constraint claims (claim *shapes*). -/
inductive ConstraintClaim where
  /-- A label was observed on this subject. -/
  | label_observed (subject : String) (label : String)
  /-- A documented conversion path exists under the named policy artifact. -/
  | documented_conversion_path
      (subject : String) (label : String) (constraint : String) (policyArtifact : String)
  /-- The constraint was applied (rendered) on this subject in this context. -/
  | constraint_applied
      (subject : String) (constraint : String) (renderContext : String)
  /-- No default-client conversion is documented (audited absence). -/
  | no_default_constraint_followed (subject : String) (label : String)
  deriving DecidableEq, Repr

/-! ## Evidence bundles (explicit) -/

structure EvidenceBundle where
  labelObs : Option LabelObservation
  policyDoc : Option PolicyDocumentation
  policyWit : Option PolicyWitness
  renderObs : Option RenderObservation
  /-- Positive evidence: an audit established that no default-client
      consumer would have converted this label. Required to ground
      the no_default_constraint_followed claim. -/
  noDefaultConsumerAudit : Bool
  deriving DecidableEq, Repr

/-! ## Admissibility relation

Positive constructors only. Each constructor names the evidence
required and the claim it grounds. There is NO constructor that
takes (Label, Policy) and produces `constraint_applied` — the only
path to `constraint_applied` is via the full coherent bundle. This
is the non-laundering property.
-/

inductive AdmissibleFromBundle : EvidenceBundle → ConstraintClaim → Prop where
  /-- A labelObs grounds the label_observed claim. -/
  | from_label
      (b : EvidenceBundle) (l : LabelObservation)
      (hLabel : b.labelObs = some l)
      : AdmissibleFromBundle b (.label_observed l.subject l.label)
  /-- labelObs + policyDoc (matching label) grounds the documented
      conversion path claim (under the named policy artifact). -/
  | from_label_and_policy_doc
      (b : EvidenceBundle) (l : LabelObservation) (p : PolicyDocumentation)
      (hLabel : b.labelObs = some l)
      (hPolicy : b.policyDoc = some p)
      (hLabelMatch : l.label = p.label)
      : AdmissibleFromBundle b
          (.documented_conversion_path l.subject p.label p.constraint p.artifactId)
  /-- The full coherent bundle (labelObs + policyDoc + renderObs with
      matching label/subject/constraint and policy preceding render
      in time) grounds the constraint_applied claim. PolicyWitness is
      NOT required by this constructor — RenderObservation is the
      stronger witness. -/
  | from_full_coherent_bundle
      (b : EvidenceBundle) (l : LabelObservation) (p : PolicyDocumentation)
      (r : RenderObservation)
      (hLabel : b.labelObs = some l)
      (hPolicy : b.policyDoc = some p)
      (hRender : b.renderObs = some r)
      (hLabelMatch : l.label = p.label)
      (hSubjectMatch : l.subject = r.subject)
      (hConstraintMatch : p.constraint = r.constraint)
      (hTimingOK : p.publishedAt ≤ r.timestamp)
      : AdmissibleFromBundle b (.constraint_applied r.subject r.constraint r.renderContext)
  /-- A labelObs + audited absence of default-client consumer grounds
      the no_default_constraint_followed claim. -/
  | from_audited_no_default
      (b : EvidenceBundle) (l : LabelObservation)
      (hLabel : b.labelObs = some l)
      (hNoPolicy : b.policyDoc = none)
      (hAudit : b.noDefaultConsumerAudit = true)
      : AdmissibleFromBundle b (.no_default_constraint_followed l.subject l.label)

/-! ## ConversionGap classification

Failure-mode classification for bundles with a labelObs but no
renderObs. Separate constructors per the open-question Q3 decision.
-/

inductive ConversionGap where
  /-- Policy documented, but no render observed (Spec001 shape). -/
  | execution_gap_policy_present
  /-- No consumer converted at all; audit witnessed absence (Spec002 shape). -/
  | conversion_witness_gap_no_consumer
  /-- Other failure shapes (placeholder for future specimens). -/
  | other_gap
  deriving DecidableEq, Repr

def classifyBundleGap (b : EvidenceBundle) : Option ConversionGap :=
  match b.labelObs, b.policyDoc, b.renderObs, b.noDefaultConsumerAudit with
  | some _, some _, none, _ => some .execution_gap_policy_present
  | some _, none, none, true => some .conversion_witness_gap_no_consumer
  | some _, _, none, _ => some .other_gap
  | _, _, _, _ => none

/-! ## Specimens 001 and 002 (concrete encodings) -/

def spec001 : EvidenceBundle := {
  labelObs := some {
    label := "harmful", subject := "post_xyz",
    observer := "moderator_a", timestamp := 100 },
  policyDoc := some {
    artifactId := "policy_v3", label := "harmful",
    constraint := "demote_in_feed",
    documenter := "policy_team", publishedAt := 50 },
  policyWit := none,    -- per packet: no/partial
  renderObs := none,    -- per packet: no
  noDefaultConsumerAudit := false
}

def spec002 : EvidenceBundle := {
  labelObs := some {
    label := "warning", subject := "post_abc",
    observer := "moderator_b", timestamp := 200 },
  policyDoc := none,    -- per packet: no
  policyWit := none,    -- per packet: no
  renderObs := none,    -- per packet: no
  noDefaultConsumerAudit := true   -- audited absence
}

/-- Hypothetical full-bundle specimen used to demonstrate that the
    positive coherent-bundle theorem is NOT vacuous: when all evidence
    is present and coherent, the constraint_applied claim IS
    admissible. -/
def spec_demo_full_render : EvidenceBundle := {
  labelObs := some {
    label := "harmful", subject := "post_xyz",
    observer := "moderator_a", timestamp := 100 },
  policyDoc := some {
    artifactId := "policy_v3", label := "harmful",
    constraint := "demote_in_feed",
    documenter := "policy_team", publishedAt := 50 },
  policyWit := none,
  renderObs := some {
    subject := "post_xyz", constraint := "demote_in_feed",
    observer := "feed_telemetry", renderContext := "user_feed_render",
    timestamp := 150 },
  noDefaultConsumerAudit := false
}

/-! ## Positive admissibility theorems (the vacuity guard)

These come BEFORE the refusal theorems. Each refusal is paired
with a positive admissibility for the same bundle (or a related
bundle that demonstrates the relation is non-empty in the relevant
area).
-/

theorem spec001_admits_label_observed :
    AdmissibleFromBundle spec001 (.label_observed "post_xyz" "harmful") :=
  AdmissibleFromBundle.from_label spec001
    { label := "harmful", subject := "post_xyz",
      observer := "moderator_a", timestamp := 100 }
    rfl

theorem spec001_admits_documented_conversion_path :
    AdmissibleFromBundle spec001
      (.documented_conversion_path "post_xyz" "harmful" "demote_in_feed" "policy_v3") :=
  AdmissibleFromBundle.from_label_and_policy_doc spec001
    { label := "harmful", subject := "post_xyz",
      observer := "moderator_a", timestamp := 100 }
    { artifactId := "policy_v3", label := "harmful", constraint := "demote_in_feed",
      documenter := "policy_team", publishedAt := 50 }
    rfl rfl rfl

theorem spec002_admits_label_observed :
    AdmissibleFromBundle spec002 (.label_observed "post_abc" "warning") :=
  AdmissibleFromBundle.from_label spec002
    { label := "warning", subject := "post_abc",
      observer := "moderator_b", timestamp := 200 }
    rfl

theorem spec002_admits_no_default_constraint_followed :
    AdmissibleFromBundle spec002 (.no_default_constraint_followed "post_abc" "warning") :=
  AdmissibleFromBundle.from_audited_no_default spec002
    { label := "warning", subject := "post_abc",
      observer := "moderator_b", timestamp := 200 }
    rfl rfl rfl

/-- The positive coherent-bundle theorem: the relation IS non-empty
    for `constraint_applied` claims when the full bundle is present
    and coherent. This guards against the trap of refusing
    everything (vacuity-in-mirror). -/
theorem spec_demo_full_admits_constraint_applied :
    AdmissibleFromBundle spec_demo_full_render
      (.constraint_applied "post_xyz" "demote_in_feed" "user_feed_render") := by
  apply AdmissibleFromBundle.from_full_coherent_bundle
    spec_demo_full_render _ _ _ rfl rfl rfl rfl rfl rfl
  decide   -- 50 ≤ 150

/-! ## Non-laundering theorems (the required ones, per DeepSeek's frame)

These are statements about *permitted derivations from evidence*, not
about factual non-occurrence in the world. The negation is:
"AdmissibleFromBundle b claim is not provable from the supplied
evidence in b." Whether the world actually contains an applied
constraint is a separate question.
-/

/-- General refusal lemma: an EvidenceBundle without policyDoc cannot
    derive any constraint_applied claim. -/
theorem no_constraint_applied_without_policy_doc
    {b : EvidenceBundle} (hNoPolicy : b.policyDoc = none)
    (subj constr ctx : String) :
    ¬ AdmissibleFromBundle b (.constraint_applied subj constr ctx) := by
  intro h
  cases h with
  | from_full_coherent_bundle _ _ _ _ hPolicy _ _ _ _ _ =>
      rw [hNoPolicy] at hPolicy
      cases hPolicy

/-- General refusal lemma: an EvidenceBundle without renderObs cannot
    derive any constraint_applied claim. -/
theorem no_constraint_applied_without_render
    {b : EvidenceBundle} (hNoRender : b.renderObs = none)
    (subj constr ctx : String) :
    ¬ AdmissibleFromBundle b (.constraint_applied subj constr ctx) := by
  intro h
  cases h with
  | from_full_coherent_bundle _ _ _ _ _ hRender _ _ _ _ =>
      rw [hNoRender] at hRender
      cases hRender

/-- THE THEOREM (derivation-shape, per the corrected frame):
    LabelObserved alone cannot derive AdmissibleClaim(ConstraintApplied ...).
    "Alone" is captured by: no policyDoc, no renderObs available in
    the bundle. -/
theorem label_alone_cannot_derive_constraint_applied
    (b : EvidenceBundle)
    (hNoPolicy : b.policyDoc = none)
    (_hNoRender : b.renderObs = none)
    (subj constr ctx : String) :
    ¬ AdmissibleFromBundle b (.constraint_applied subj constr ctx) :=
  no_constraint_applied_without_policy_doc hNoPolicy subj constr ctx

/-- LabelObserved + PolicyDocumented still cannot derive
    AdmissibleClaim(ConstraintApplied ...). "Still" is captured by:
    no renderObs in the bundle. -/
theorem label_and_policy_doc_cannot_derive_constraint_applied
    (b : EvidenceBundle)
    (hNoRender : b.renderObs = none)
    (subj constr ctx : String) :
    ¬ AdmissibleFromBundle b (.constraint_applied subj constr ctx) :=
  no_constraint_applied_without_render hNoRender subj constr ctx

/-! ### Specimen-instance refusals (paired with the positives above) -/

/-- Spec001 has labelObs + policyDoc but no renderObs. The
    constraint_applied claim is not derivable from this bundle.
    Paired positive: spec001_admits_documented_conversion_path. -/
theorem spec001_refuses_constraint_applied (constr ctx : String) :
    ¬ AdmissibleFromBundle spec001 (.constraint_applied "post_xyz" constr ctx) :=
  label_and_policy_doc_cannot_derive_constraint_applied spec001 rfl _ _ _

/-- Spec002 has only labelObs + audit. The constraint_applied claim
    is not derivable.
    Paired positive: spec002_admits_no_default_constraint_followed. -/
theorem spec002_refuses_constraint_applied (constr ctx : String) :
    ¬ AdmissibleFromBundle spec002 (.constraint_applied "post_abc" constr ctx) :=
  label_alone_cannot_derive_constraint_applied spec002 rfl rfl _ _ _

/-- Spec002 has no policyDoc. The documented_conversion_path claim is
    not derivable.
    Paired positive: spec002_admits_label_observed. -/
theorem spec002_refuses_documented_conversion_path
    (subj lab constr pol : String) :
    ¬ AdmissibleFromBundle spec002
      (.documented_conversion_path subj lab constr pol) := by
  intro h
  cases h with
  | from_label_and_policy_doc _ _ _ hPolicy _ =>
      rw [show spec002.policyDoc = none from rfl] at hPolicy
      cases hPolicy

/-! ## Gap classification theorems -/

theorem spec001_has_execution_gap :
    classifyBundleGap spec001 = some .execution_gap_policy_present := rfl

theorem spec002_has_conversion_witness_gap :
    classifyBundleGap spec002 = some .conversion_witness_gap_no_consumer := rfl

theorem spec001_and_spec002_gaps_differ :
    classifyBundleGap spec001 ≠ classifyBundleGap spec002 := by
  intro h
  rw [spec001_has_execution_gap, spec002_has_conversion_witness_gap] at h
  cases h

/-! ## Vacuity guard: admissibility is non-empty for each specimen -/

theorem spec001_admissibility_nonempty :
    ∃ c, AdmissibleFromBundle spec001 c :=
  ⟨_, spec001_admits_label_observed⟩

theorem spec002_admissibility_nonempty :
    ∃ c, AdmissibleFromBundle spec002 c :=
  ⟨_, spec002_admits_label_observed⟩

theorem spec_demo_full_admissibility_nonempty :
    ∃ c, AdmissibleFromBundle spec_demo_full_render c :=
  ⟨_, spec_demo_full_admits_constraint_applied⟩

end Admissibility.Scratch.Labelwatch
