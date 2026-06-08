/-
  Custody-Class: SCRATCH

  Labelwatch — first non-synthetic pressure test, 2026-06-08
  (revised 2026-06-08 per operator: EvidenceInput / DerivedJudgment
  separation). Not imported by `LeanProofs.lean`. Not part of any
  1.0 surface. No paper anchor. No promotion path. NOT used as
  discharge for any doctrine.

  Goal: formalize the smallest calculus vocabulary that can represent
  Labelwatch specimens 001 and 002 without laundering testimony into
  constraint, with explicit EvidenceInput / DerivedJudgment separation.

  Hard discipline (this revision):
    1. Hand-authored evidence packets are FIXTURES only.
    2. EvidenceInput contains ONLY observable/documentary facts:
       label observation, policy documentation, policy witness,
       render observation, consumer/context/artifact identity,
       timestamps/provenance, audit events. NO verdict-like fields,
       NO Bool flags determining bundle interpretation.
    3. DerivedJudgment contains the products of interpretation: a
       ConversionGap classification, admissible/inadmissible claims.
       It is computed FROM EvidenceInput via `deriveJudgment` and
       never appears as an input.
    4. No specimen theorem takes its gap as a premise.
    5. No evidence constructor contains a verdict-like field.
    6. Derived judgments are NOT admissible as input evidence unless
       witnessed independently. (Theorem
       `derived_judgments_require_independent_witness` below.)

  Per the prior round's correction (DeepSeek + operator):
    The non-laundering property is about which derivations are
    licensed from explicit evidence bundles, not about whether the
    world-state secretly contained an applied constraint.

  Required distinctions (from the handoff packet):
    - LabelObservation       : testimony witnessed
    - PolicyDocumentation    : source artifact / public rule documented
    - PolicyWitness          : live consumer version/application attested
    - RenderObservation      : execution receipt in a specific render_context
    - AuditEvent             : documentary record of an audit performed
    - ConstraintClaim        : claim shape space
    - EvidenceInput          : the explicit observable evidence bundle
    - DerivedJudgment        : the products of interpretation
    - ConversionGap          : failure-mode classification (inside DerivedJudgment)

  Specimen 001:
    LabelObservation     = yes
    PolicyDocumentation  = yes
    PolicyWitness        = no
    RenderObservation    = no
    AuditEvent           = none required
    Admissible:    documented conversion path exists under named policy artifact
    Inadmissible:  this post was actually constrained for any concrete render

  Specimen 002:
    LabelObservation     = yes
    PolicyDocumentation  = no
    PolicyWitness        = no
    RenderObservation    = no
    AuditEvent           = single AuditEvent with outcome no_consumer_found_converting
    Admissible:    label exists and no default-client conversion is documented
                   (audited absence, grounded by the AuditEvent)
    Inadmissible:  any default-client constraint followed from the third-party label
-/

namespace Admissibility.Scratch.Labelwatch

/-! ## Evidence types (observable/documentary facts only) -/

/-- A LabelObservation: testimony that a label was applied to a subject. -/
structure LabelObservation where
  label : String
  subject : String
  observer : String
  timestamp : Nat
  deriving DecidableEq, Repr

/-- A PolicyDocumentation: a published artifact stating a label→constraint
    rule. Witnesses artifact existence, not consumer application. -/
structure PolicyDocumentation where
  artifactId : String
  label : String
  constraint : String
  documenter : String
  publishedAt : Nat
  deriving DecidableEq, Repr

/-- A PolicyWitness: live consumer attestation that a specific consumer
    version applied a policy. Distinct from PolicyDocumentation (artifact
    existence) and from RenderObservation (execution on a specific
    subject). Present as a type; not consumed by any current
    admissibility constructor (recorded for Spec001 where it = no/partial). -/
structure PolicyWitness where
  artifactId : String
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

/-- Observable audit outcomes. Each constructor names what the auditor
    recorded; it is *what the auditor observed and wrote down*, not a
    verdict about the bundle. -/
inductive AuditOutcome where
  | no_consumer_found_converting
  | consumer_found_converting (consumer : String)
  | inconclusive
  deriving DecidableEq, Repr

/-- An AuditEvent: documentary record of an audit performed. The
    outcome is an observable categorical record (what was found), not
    a Bool verdict. -/
structure AuditEvent where
  auditor : String
  scope : String   -- what was audited (e.g., "default-client conversion of label X")
  outcome : AuditOutcome
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

/-! ## EvidenceInput (observation-only) -/

/-- EvidenceInput contains ONLY observable/documentary facts. No
    verdict-shaped fields. No Bool flags determining interpretation.
    All fields are either Option<observation> or List<observation>. -/
structure EvidenceInput where
  labelObs : Option LabelObservation
  policyDoc : Option PolicyDocumentation
  policyWit : Option PolicyWitness
  renderObs : Option RenderObservation
  auditEvents : List AuditEvent
  deriving DecidableEq, Repr

/-! ## Admissibility relation

Positive constructors only. Each constructor consumes ONLY
EvidenceInput fields and propositional consequences thereof. No
constructor takes a DerivedJudgment, ConversionGap, or any
verdict-shaped value.
-/

inductive AdmissibleFromInput : EvidenceInput → ConstraintClaim → Prop where
  /-- A labelObs grounds the label_observed claim. -/
  | from_label
      (e : EvidenceInput) (l : LabelObservation)
      (hLabel : e.labelObs = some l)
      : AdmissibleFromInput e (.label_observed l.subject l.label)
  /-- labelObs + policyDoc (matching label) grounds the documented
      conversion path claim. -/
  | from_label_and_policy_doc
      (e : EvidenceInput) (l : LabelObservation) (p : PolicyDocumentation)
      (hLabel : e.labelObs = some l)
      (hPolicy : e.policyDoc = some p)
      (hLabelMatch : l.label = p.label)
      : AdmissibleFromInput e
          (.documented_conversion_path l.subject p.label p.constraint p.artifactId)
  /-- Full coherent bundle (labelObs + policyDoc + renderObs with
      matching identities and policy preceding render in time) grounds
      the constraint_applied claim. -/
  | from_full_coherent_bundle
      (e : EvidenceInput) (l : LabelObservation) (p : PolicyDocumentation)
      (r : RenderObservation)
      (hLabel : e.labelObs = some l)
      (hPolicy : e.policyDoc = some p)
      (hRender : e.renderObs = some r)
      (hLabelMatch : l.label = p.label)
      (hSubjectMatch : l.subject = r.subject)
      (hConstraintMatch : p.constraint = r.constraint)
      (hTimingOK : p.publishedAt ≤ r.timestamp)
      : AdmissibleFromInput e (.constraint_applied r.subject r.constraint r.renderContext)
  /-- A labelObs + an AuditEvent with the no_consumer_found_converting
      outcome (an observable finding) grounds the
      no_default_constraint_followed claim. The audit is the
      independent witness; the bundle's noDefault status is NOT a
      stored verdict. -/
  | from_audited_no_default
      (e : EvidenceInput) (l : LabelObservation) (a : AuditEvent)
      (hLabel : e.labelObs = some l)
      (hNoPolicy : e.policyDoc = none)
      (hAuditPresent : a ∈ e.auditEvents)
      (hAuditOutcome : a.outcome = .no_consumer_found_converting)
      : AdmissibleFromInput e (.no_default_constraint_followed l.subject l.label)

/-! ## DerivedJudgment (products of interpretation, NOT input)

DerivedJudgment is what `deriveJudgment` produces from EvidenceInput.
It is never an input to any admissibility constructor. The
ConversionGap classification lives here, not in EvidenceInput.
-/

inductive ConversionGap where
  /-- Policy documented, but no render observed (Spec001 shape). -/
  | execution_gap_policy_present
  /-- No consumer converted at all; audit witnessed absence (Spec002 shape). -/
  | conversion_witness_gap_no_consumer
  /-- Other failure shapes (placeholder for future specimens). -/
  | other_gap
  deriving DecidableEq, Repr

/-- A DerivedJudgment is the product of interpreting an EvidenceInput.
    It contains the gap classification (and conceptually the
    admissible/inadmissible-claim status of any candidate claim, which
    is given by AdmissibleFromInput as a Prop predicate over claims —
    not stored as a List in this minimum). -/
structure DerivedJudgment where
  gap : Option ConversionGap
  deriving DecidableEq, Repr

/-- Check whether an audit-event list contains a positive "no consumer
    found converting" finding. -/
def hasNoConsumerAudit : List AuditEvent → Bool
  | [] => false
  | a :: rest =>
      match a.outcome with
      | .no_consumer_found_converting => true
      | _ => hasNoConsumerAudit rest

/-- Gap classifier — observation-side. Reads only EvidenceInput. -/
def classifyInputGap (e : EvidenceInput) : Option ConversionGap :=
  match e.labelObs, e.policyDoc, e.renderObs, hasNoConsumerAudit e.auditEvents with
  | some _, some _, none, _ => some .execution_gap_policy_present
  | some _, none, none, true => some .conversion_witness_gap_no_consumer
  | some _, _, none, _ => some .other_gap
  | _, _, _, _ => none

/-- Derivation: EvidenceInput → DerivedJudgment. Pure function. -/
def deriveJudgment (e : EvidenceInput) : DerivedJudgment :=
  { gap := classifyInputGap e }

/-! ## Specimens 001 and 002 (fixtures — observation-only) -/

/-- Spec002's audit event, named for theorem reference. -/
def spec002_audit : AuditEvent := {
  auditor := "compliance_team",
  scope := "default-client conversion of warning-labeled posts",
  outcome := .no_consumer_found_converting,
  timestamp := 250
}

def spec001 : EvidenceInput := {
  labelObs := some {
    label := "harmful", subject := "post_xyz",
    observer := "moderator_a", timestamp := 100 },
  policyDoc := some {
    artifactId := "policy_v3", label := "harmful",
    constraint := "demote_in_feed",
    documenter := "policy_team", publishedAt := 50 },
  policyWit := none,
  renderObs := none,
  auditEvents := []
}

def spec002 : EvidenceInput := {
  labelObs := some {
    label := "warning", subject := "post_abc",
    observer := "moderator_b", timestamp := 200 },
  policyDoc := none,
  policyWit := none,
  renderObs := none,
  auditEvents := [spec002_audit]
}

/-- Hypothetical full-bundle fixture (used to demonstrate the positive
    coherent-bundle theorem is not vacuous). -/
def spec_demo_full_render : EvidenceInput := {
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
  auditEvents := []
}

/-! ## Positive admissibility theorems (the vacuity guard) -/

theorem spec001_admits_label_observed :
    AdmissibleFromInput spec001 (.label_observed "post_xyz" "harmful") :=
  AdmissibleFromInput.from_label spec001
    { label := "harmful", subject := "post_xyz",
      observer := "moderator_a", timestamp := 100 }
    rfl

theorem spec001_admits_documented_conversion_path :
    AdmissibleFromInput spec001
      (.documented_conversion_path "post_xyz" "harmful" "demote_in_feed" "policy_v3") :=
  AdmissibleFromInput.from_label_and_policy_doc spec001
    { label := "harmful", subject := "post_xyz",
      observer := "moderator_a", timestamp := 100 }
    { artifactId := "policy_v3", label := "harmful", constraint := "demote_in_feed",
      documenter := "policy_team", publishedAt := 50 }
    rfl rfl rfl

theorem spec002_admits_label_observed :
    AdmissibleFromInput spec002 (.label_observed "post_abc" "warning") :=
  AdmissibleFromInput.from_label spec002
    { label := "warning", subject := "post_abc",
      observer := "moderator_b", timestamp := 200 }
    rfl

theorem spec002_admits_no_default_constraint_followed :
    AdmissibleFromInput spec002 (.no_default_constraint_followed "post_abc" "warning") :=
  AdmissibleFromInput.from_audited_no_default spec002
    { label := "warning", subject := "post_abc",
      observer := "moderator_b", timestamp := 200 }
    spec002_audit
    rfl rfl (List.Mem.head _) rfl

theorem spec_demo_full_admits_constraint_applied :
    AdmissibleFromInput spec_demo_full_render
      (.constraint_applied "post_xyz" "demote_in_feed" "user_feed_render") := by
  apply AdmissibleFromInput.from_full_coherent_bundle
    spec_demo_full_render _ _ _ rfl rfl rfl rfl rfl rfl
  decide

/-! ## Non-laundering theorems (derivation-shape) -/

theorem no_constraint_applied_without_policy_doc
    {e : EvidenceInput} (hNoPolicy : e.policyDoc = none)
    (subj constr ctx : String) :
    ¬ AdmissibleFromInput e (.constraint_applied subj constr ctx) := by
  intro h
  cases h with
  | from_full_coherent_bundle _ _ _ _ hPolicy _ _ _ _ _ =>
      rw [hNoPolicy] at hPolicy
      cases hPolicy

theorem no_constraint_applied_without_render
    {e : EvidenceInput} (hNoRender : e.renderObs = none)
    (subj constr ctx : String) :
    ¬ AdmissibleFromInput e (.constraint_applied subj constr ctx) := by
  intro h
  cases h with
  | from_full_coherent_bundle _ _ _ _ _ hRender _ _ _ _ =>
      rw [hNoRender] at hRender
      cases hRender

/-- THE THEOREM (derivation-shape, per the corrected frame):
    LabelObserved alone cannot derive AdmissibleClaim(ConstraintApplied ...). -/
theorem label_alone_cannot_derive_constraint_applied
    (e : EvidenceInput)
    (hNoPolicy : e.policyDoc = none)
    (_hNoRender : e.renderObs = none)
    (subj constr ctx : String) :
    ¬ AdmissibleFromInput e (.constraint_applied subj constr ctx) :=
  no_constraint_applied_without_policy_doc hNoPolicy subj constr ctx

/-- LabelObserved + PolicyDocumented still cannot derive
    AdmissibleClaim(ConstraintApplied ...). -/
theorem label_and_policy_doc_cannot_derive_constraint_applied
    (e : EvidenceInput)
    (hNoRender : e.renderObs = none)
    (subj constr ctx : String) :
    ¬ AdmissibleFromInput e (.constraint_applied subj constr ctx) :=
  no_constraint_applied_without_render hNoRender subj constr ctx

/-! ### Specimen-instance refusals (paired with the positives above)

Critically: NONE of these theorems takes the specimen's gap as a
premise. Each is a function of the specimen's observable evidence
alone.
-/

theorem spec001_refuses_constraint_applied (constr ctx : String) :
    ¬ AdmissibleFromInput spec001 (.constraint_applied "post_xyz" constr ctx) :=
  label_and_policy_doc_cannot_derive_constraint_applied spec001 rfl _ _ _

theorem spec002_refuses_constraint_applied (constr ctx : String) :
    ¬ AdmissibleFromInput spec002 (.constraint_applied "post_abc" constr ctx) :=
  label_alone_cannot_derive_constraint_applied spec002 rfl rfl _ _ _

theorem spec002_refuses_documented_conversion_path
    (subj lab constr pol : String) :
    ¬ AdmissibleFromInput spec002
      (.documented_conversion_path subj lab constr pol) := by
  intro h
  cases h with
  | from_label_and_policy_doc _ _ _ hPolicy _ =>
      rw [show spec002.policyDoc = none from rfl] at hPolicy
      cases hPolicy

/-! ## Gap classification theorems (on DerivedJudgment side) -/

theorem spec001_derived_gap :
    (deriveJudgment spec001).gap = some .execution_gap_policy_present := rfl

theorem spec002_derived_gap :
    (deriveJudgment spec002).gap = some .conversion_witness_gap_no_consumer := rfl

theorem spec001_and_spec002_gaps_differ :
    (deriveJudgment spec001).gap ≠ (deriveJudgment spec002).gap := by
  rw [spec001_derived_gap, spec002_derived_gap]
  intro h; cases h

/-! ## Vacuity guard: admissibility is non-empty for each fixture -/

theorem spec001_admissibility_nonempty :
    ∃ c, AdmissibleFromInput spec001 c :=
  ⟨_, spec001_admits_label_observed⟩

theorem spec002_admissibility_nonempty :
    ∃ c, AdmissibleFromInput spec002 c :=
  ⟨_, spec002_admits_label_observed⟩

theorem spec_demo_full_admissibility_nonempty :
    ∃ c, AdmissibleFromInput spec_demo_full_render c :=
  ⟨_, spec_demo_full_admits_constraint_applied⟩

/-! ## The separation invariant

The principle, per operator (2026-06-08):
  "Derived judgments are not admissible as input evidence unless
   witnessed independently."

Structural reading: there is no constructor of `AdmissibleFromInput`
that takes a `DerivedJudgment` or `ConversionGap` as an argument.
Every admissibility derivation reaches back to an observable fact in
EvidenceInput.

The theorem below proves a concrete consequence: every admissibility
derivation requires a `LabelObservation` to be present in the
EvidenceInput. This is the observable anchor — the derivation cannot
short-circuit through a DerivedJudgment because no constructor reads
a DerivedJudgment field.

If a future specimen forces admitting a claim about a derived
judgment (e.g., "the gap is X" as evidence-grade fact), the
extension would need to introduce an AttestationObservation type — a
documentary record of someone reporting the judgment — and a paired
admissibility constructor that consumes the AttestationObservation,
NOT the bare DerivedJudgment. The separation would be preserved.
-/

theorem derived_judgments_require_independent_witness
    {e : EvidenceInput} {claim : ConstraintClaim}
    (hAdm : AdmissibleFromInput e claim) :
    e.labelObs ≠ none := by
  cases hAdm with
  | from_label _ hLabel =>
      intro hNone; rw [hNone] at hLabel; cases hLabel
  | from_label_and_policy_doc _ _ hLabel _ _ =>
      intro hNone; rw [hNone] at hLabel; cases hLabel
  | from_full_coherent_bundle _ _ _ hLabel _ _ _ _ _ _ =>
      intro hNone; rw [hNone] at hLabel; cases hLabel
  | from_audited_no_default _ _ hLabel _ _ _ =>
      intro hNone; rw [hNone] at hLabel; cases hLabel

/-- Companion structural commitment: admissibility is a pure function
    of EvidenceInput. Two inputs that agree as data agree on which
    claims they admit. -/
theorem admissibility_pure_of_evidence_input
    {e1 e2 : EvidenceInput} (h : e1 = e2) (claim : ConstraintClaim) :
    AdmissibleFromInput e1 claim ↔ AdmissibleFromInput e2 claim := by
  rw [h]

/-- Companion structural commitment: deriveJudgment is a pure function
    of EvidenceInput. The DerivedJudgment cannot depend on anything
    outside the EvidenceInput it was derived from. -/
theorem deriveJudgment_pure_of_evidence_input
    {e1 e2 : EvidenceInput} (h : e1 = e2) :
    deriveJudgment e1 = deriveJudgment e2 := by
  rw [h]

end Admissibility.Scratch.Labelwatch
