/-
  Custody-Class: SCRATCH

  Labelwatch — first non-synthetic pressure test, 2026-06-08
  (revised 2026-06-08 per operator: EvidenceInput / DerivedJudgment
  separation; further revised 2026-06-08 per detection-lane D-001:
  ExecutionSurface schema patch). Not imported by `LeanProofs.lean`.
  Not part of any 1.0 surface. No paper anchor. No promotion path.
  NOT used as discharge for any doctrine.

  Goal: smallest calculus vocabulary that can represent Labelwatch
  specimens 001 and 002 — AND can correctly classify D-001's
  hosting-layer action without misreading it as a render-execution
  gap.

  Hard discipline:
    1. Hand-authored evidence packets are FIXTURES only.
    2. EvidenceInput contains ONLY observable/documentary facts.
       No verdict-like fields. No Bool flags.
    3. DerivedJudgment contains the products of interpretation.
       Computed FROM EvidenceInput, never appears as an input.
    4. No specimen theorem takes its gap as a premise.
    5. No evidence constructor contains a verdict-like field.
    6. Derived judgments are NOT admissible as input evidence unless
       witnessed independently.

  D-001 finding (detection lane, 2026-06-08):
    moderation.bsky.app + !takedown was auto-classified as a
    render-execution gap because the schema lacked execution surface.
    Audit: !takedown converts at the hosting/PDS availability layer,
    not the client render layer. The classifier could not see this
    distinction; both surfaces collapsed to "no render observation."

  Schema patch (this revision):
    - ExecutionSurface : render | hosting | mixed | unknown
    - PolicyDocumentation now carries executionSurface (where the
      policy's action is supposed to execute)
    - RenderObservation generalized to ExecutionObservation(surface).
      executionContext replaces renderContext.
    - ConversionGap.execution_gap_policy_present now carries surface,
      so a gap on hosting layer is distinguishable from a gap on
      render layer.
    - No new constructors added (avoiding constructor explosion).

  Surface guard (per operator, 2026-06-08):
    `executionSurface` is admissible as input evidence ONLY as a
    field of PolicyDocumentation (or ExecutionObservation), not as a
    derived-gap verdict surfaced back into the bundle. The classifier
    reads surface FROM PolicyDocumentation; the gap classification
    inherits surface from that read. There is no path by which a
    derived `execution_gap_policy_present surface` becomes an input
    to admissibility.
-/

namespace Admissibility.Scratch.Labelwatch

/-! ## Execution surface (new in this revision) -/

inductive ExecutionSurface where
  | render    -- client-side rendering (feed, UI, ranking)
  | hosting   -- hosting / PDS availability layer (takedown, blocked)
  | mixed     -- policy effects span both
  | unknown   -- policy unspecified or layer not yet classified
  deriving DecidableEq, Repr

/-! ## Evidence types (observable/documentary facts only) -/

structure LabelObservation where
  label : String
  subject : String
  observer : String
  timestamp : Nat
  deriving DecidableEq, Repr

/-- PolicyDocumentation: a published artifact stating a label→constraint
    rule at a specific execution surface. Witnesses artifact existence
    AND its named execution surface, not consumer application. -/
structure PolicyDocumentation where
  artifactId : String
  label : String
  constraint : String
  executionSurface : ExecutionSurface
  documenter : String
  publishedAt : Nat
  deriving DecidableEq, Repr

structure PolicyWitness where
  artifactId : String
  consumer : String
  version : String
  witnessedAt : Nat
  deriving DecidableEq, Repr

/-- ExecutionObservation: execution receipt that the constraint was
    applied at a specific surface and execution context.
    (Generalized from the prior RenderObservation; surface is now an
    explicit field, executionContext replaces renderContext.) -/
structure ExecutionObservation where
  subject : String
  constraint : String
  observer : String
  surface : ExecutionSurface
  executionContext : String
  timestamp : Nat
  deriving DecidableEq, Repr

inductive AuditOutcome where
  | no_consumer_found_converting
  | consumer_found_converting (consumer : String)
  | inconclusive
  deriving DecidableEq, Repr

structure AuditEvent where
  auditor : String
  scope : String
  outcome : AuditOutcome
  timestamp : Nat
  deriving DecidableEq, Repr

/-- The space of admissible constraint claims (claim shapes). -/
inductive ConstraintClaim where
  | label_observed (subject : String) (label : String)
  /-- Documented conversion path: includes the policy's executionSurface
      so the claim distinguishes hosting-layer from render-layer paths. -/
  | documented_conversion_path
      (subject : String) (label : String) (constraint : String)
      (policyArtifact : String) (surface : ExecutionSurface)
  /-- Constraint applied at a specific surface and execution context. -/
  | constraint_applied
      (subject : String) (constraint : String)
      (surface : ExecutionSurface) (executionContext : String)
  | no_default_constraint_followed (subject : String) (label : String)
  deriving DecidableEq, Repr

/-! ## EvidenceInput (observation-only) -/

structure EvidenceInput where
  labelObs : Option LabelObservation
  policyDoc : Option PolicyDocumentation
  policyWit : Option PolicyWitness
  executionObs : Option ExecutionObservation
  auditEvents : List AuditEvent
  deriving DecidableEq, Repr

/-! ## Admissibility relation -/

inductive AdmissibleFromInput : EvidenceInput → ConstraintClaim → Prop where
  | from_label
      (e : EvidenceInput) (l : LabelObservation)
      (hLabel : e.labelObs = some l)
      : AdmissibleFromInput e (.label_observed l.subject l.label)
  /-- labelObs + policyDoc (matching label) grounds the documented
      conversion path claim, carrying the policy's executionSurface. -/
  | from_label_and_policy_doc
      (e : EvidenceInput) (l : LabelObservation) (p : PolicyDocumentation)
      (hLabel : e.labelObs = some l)
      (hPolicy : e.policyDoc = some p)
      (hLabelMatch : l.label = p.label)
      : AdmissibleFromInput e
          (.documented_conversion_path l.subject p.label p.constraint
            p.artifactId p.executionSurface)
  /-- Full coherent bundle: labelObs + policyDoc + executionObs with
      matching identities, surface coherent between policy and
      execution, and policy preceding execution in time. The surface
      coherence check is new: it refuses bundles where a hosting-layer
      policy is "witnessed" by a render-layer execution observation
      (or vice versa). -/
  | from_full_coherent_bundle
      (e : EvidenceInput) (l : LabelObservation) (p : PolicyDocumentation)
      (r : ExecutionObservation)
      (hLabel : e.labelObs = some l)
      (hPolicy : e.policyDoc = some p)
      (hExec : e.executionObs = some r)
      (hLabelMatch : l.label = p.label)
      (hSubjectMatch : l.subject = r.subject)
      (hConstraintMatch : p.constraint = r.constraint)
      (hSurfaceMatch : p.executionSurface = r.surface)
      (hTimingOK : p.publishedAt ≤ r.timestamp)
      : AdmissibleFromInput e
          (.constraint_applied r.subject r.constraint r.surface r.executionContext)
  | from_audited_no_default
      (e : EvidenceInput) (l : LabelObservation) (a : AuditEvent)
      (hLabel : e.labelObs = some l)
      (hNoPolicy : e.policyDoc = none)
      (hAuditPresent : a ∈ e.auditEvents)
      (hAuditOutcome : a.outcome = .no_consumer_found_converting)
      : AdmissibleFromInput e (.no_default_constraint_followed l.subject l.label)

/-! ## DerivedJudgment (products of interpretation) -/

inductive ConversionGap where
  /-- Policy documented at a specific surface, but no execution observed
      at that surface. The surface is now explicit so D-001 (hosting)
      is distinguishable from S001 (render). -/
  | execution_gap_policy_present (surface : ExecutionSurface)
  | conversion_witness_gap_no_consumer
  | other_gap
  deriving DecidableEq, Repr

structure DerivedJudgment where
  gap : Option ConversionGap
  deriving DecidableEq, Repr

def hasNoConsumerAudit : List AuditEvent → Bool
  | [] => false
  | a :: rest =>
      match a.outcome with
      | .no_consumer_found_converting => true
      | _ => hasNoConsumerAudit rest

/-- Gap classifier. Reads only EvidenceInput. The surface in
    execution_gap_policy_present is inherited from PolicyDocumentation
    (the canonical source) — NOT a verdict re-surfaced into the
    bundle. -/
def classifyInputGap (e : EvidenceInput) : Option ConversionGap :=
  match e.labelObs, e.policyDoc, e.executionObs, hasNoConsumerAudit e.auditEvents with
  | some _, some p, none, _ => some (.execution_gap_policy_present p.executionSurface)
  | some _, none, none, true => some .conversion_witness_gap_no_consumer
  | some _, _, none, _ => some .other_gap
  | _, _, _, _ => none

def deriveJudgment (e : EvidenceInput) : DerivedJudgment :=
  { gap := classifyInputGap e }

/-! ## Specimens (fixtures — observation-only) -/

def spec002_audit : AuditEvent := {
  auditor := "compliance_team",
  scope := "default-client conversion of warning-labeled posts at render layer",
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
    executionSurface := .render,
    documenter := "policy_team", publishedAt := 50 },
  policyWit := none,
  executionObs := none,
  auditEvents := []
}

def spec002 : EvidenceInput := {
  labelObs := some {
    label := "warning", subject := "post_abc",
    observer := "moderator_b", timestamp := 200 },
  policyDoc := none,
  policyWit := none,
  executionObs := none,
  auditEvents := [spec002_audit]
}

def spec_demo_full_render : EvidenceInput := {
  labelObs := some {
    label := "harmful", subject := "post_xyz",
    observer := "moderator_a", timestamp := 100 },
  policyDoc := some {
    artifactId := "policy_v3", label := "harmful",
    constraint := "demote_in_feed",
    executionSurface := .render,
    documenter := "policy_team", publishedAt := 50 },
  policyWit := none,
  executionObs := some {
    subject := "post_xyz", constraint := "demote_in_feed",
    observer := "feed_telemetry",
    surface := .render,
    executionContext := "user_feed_render",
    timestamp := 150 },
  auditEvents := []
}

/-! ## Positive admissibility theorems -/

theorem spec001_admits_label_observed :
    AdmissibleFromInput spec001 (.label_observed "post_xyz" "harmful") :=
  AdmissibleFromInput.from_label spec001
    { label := "harmful", subject := "post_xyz",
      observer := "moderator_a", timestamp := 100 }
    rfl

theorem spec001_admits_documented_conversion_path :
    AdmissibleFromInput spec001
      (.documented_conversion_path "post_xyz" "harmful" "demote_in_feed"
        "policy_v3" .render) :=
  AdmissibleFromInput.from_label_and_policy_doc spec001
    { label := "harmful", subject := "post_xyz",
      observer := "moderator_a", timestamp := 100 }
    { artifactId := "policy_v3", label := "harmful", constraint := "demote_in_feed",
      executionSurface := .render,
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
      (.constraint_applied "post_xyz" "demote_in_feed" .render "user_feed_render") := by
  apply AdmissibleFromInput.from_full_coherent_bundle
    spec_demo_full_render _ _ _ rfl rfl rfl rfl rfl rfl rfl
  decide

/-! ## Non-laundering theorems -/

theorem no_constraint_applied_without_policy_doc
    {e : EvidenceInput} (hNoPolicy : e.policyDoc = none)
    (subj constr : String) (s : ExecutionSurface) (ctx : String) :
    ¬ AdmissibleFromInput e (.constraint_applied subj constr s ctx) := by
  intro h
  cases h with
  | from_full_coherent_bundle _ _ _ _ hPolicy _ _ _ _ _ _ =>
      rw [hNoPolicy] at hPolicy
      cases hPolicy

theorem no_constraint_applied_without_execution_observation
    {e : EvidenceInput} (hNoExec : e.executionObs = none)
    (subj constr : String) (s : ExecutionSurface) (ctx : String) :
    ¬ AdmissibleFromInput e (.constraint_applied subj constr s ctx) := by
  intro h
  cases h with
  | from_full_coherent_bundle _ _ _ _ _ hExec _ _ _ _ _ =>
      rw [hNoExec] at hExec
      cases hExec

theorem label_alone_cannot_derive_constraint_applied
    (e : EvidenceInput)
    (hNoPolicy : e.policyDoc = none)
    (_hNoExec : e.executionObs = none)
    (subj constr : String) (s : ExecutionSurface) (ctx : String) :
    ¬ AdmissibleFromInput e (.constraint_applied subj constr s ctx) :=
  no_constraint_applied_without_policy_doc hNoPolicy subj constr s ctx

theorem label_and_policy_doc_cannot_derive_constraint_applied
    (e : EvidenceInput)
    (hNoExec : e.executionObs = none)
    (subj constr : String) (s : ExecutionSurface) (ctx : String) :
    ¬ AdmissibleFromInput e (.constraint_applied subj constr s ctx) :=
  no_constraint_applied_without_execution_observation hNoExec subj constr s ctx

/-! ### Specimen-instance refusals -/

theorem spec001_refuses_constraint_applied
    (constr : String) (s : ExecutionSurface) (ctx : String) :
    ¬ AdmissibleFromInput spec001 (.constraint_applied "post_xyz" constr s ctx) :=
  label_and_policy_doc_cannot_derive_constraint_applied spec001 rfl _ _ _ _

theorem spec002_refuses_constraint_applied
    (constr : String) (s : ExecutionSurface) (ctx : String) :
    ¬ AdmissibleFromInput spec002 (.constraint_applied "post_abc" constr s ctx) :=
  label_alone_cannot_derive_constraint_applied spec002 rfl rfl _ _ _ _

theorem spec002_refuses_documented_conversion_path
    (subj lab constr pol : String) (s : ExecutionSurface) :
    ¬ AdmissibleFromInput spec002
      (.documented_conversion_path subj lab constr pol s) := by
  intro h
  cases h with
  | from_label_and_policy_doc _ _ _ hPolicy _ =>
      rw [show spec002.policyDoc = none from rfl] at hPolicy
      cases hPolicy

/-! ## Gap classification (on DerivedJudgment side)

D-001's lesson: the gap classifier now carries surface. spec001's
gap is on render surface; a hosting-layer policy would produce a
gap on hosting surface, no longer collapsing to a generic
"execution_gap_policy_present."
-/

theorem spec001_derived_gap :
    (deriveJudgment spec001).gap = some (.execution_gap_policy_present .render) := rfl

theorem spec002_derived_gap :
    (deriveJudgment spec002).gap = some .conversion_witness_gap_no_consumer := rfl

theorem spec001_and_spec002_gaps_differ :
    (deriveJudgment spec001).gap ≠ (deriveJudgment spec002).gap := by
  rw [spec001_derived_gap, spec002_derived_gap]
  intro h; cases h

/-! ## Vacuity guard -/

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

The schema patch (D-001) preserves the separation: `ExecutionSurface`
appears as input evidence ONLY as a field of `PolicyDocumentation`
and `ExecutionObservation` (observation-shaped). The classifier reads
surface from `PolicyDocumentation`; the derived
`execution_gap_policy_present surface` inherits surface from that
read, but is NEVER fed back into the bundle as an input. No
constructor of `AdmissibleFromInput` reads `ConversionGap`-side
surface as a premise.

CAVEAT 1 (recorded 2026-06-08 per operator): the theorem name
`derived_judgments_require_independent_witness` slightly overclaims
what the proof shows. The proof demonstrates that every current
admissibility constructor requires a `LabelObservation`. That is
"specimen-track local" — it holds because all four current
constructors happen to need a `LabelObservation`. The broader
principle (no derived judgment may serve as primary evidence unless
independently witnessed) is enforced STRUCTURALLY by the type
signature of `AdmissibleFromInput`, not by this theorem alone. A
more accurate name for what the theorem proves would be
`admissible_claims_require_label_anchor`. Kept under the broader
name as a fenced marker; rename if/when a future constructor breaks
the label-anchor invariant while preserving the separation principle.

CAVEAT 2 (recorded 2026-06-08 per operator): `AuditEvent.scope` is
the new laundering pressure point. The `no_consumer_found_converting`
outcome is safe ONLY if scope is precise enough — e.g., "auditor A
checked consumer C / context ctx / label V / policy surface S at
time T and found no documented/default conversion." It is NOT safe
if scope is a global no-conversion claim ("nothing converted this
anywhere"). The type system does not enforce scope precision. That
is a Labelwatch-side discipline question for the producer of
AuditEvent records.

CAVEAT 3 (added 2026-06-08, schema patch): `ExecutionSurface` is the
newest laundering pressure point. The surface guard requires it to
appear as input evidence ONLY as a field of `PolicyDocumentation` or
`ExecutionObservation`. It must NOT appear as a free-standing
"surface verdict" injected back into the bundle from a downstream
classifier. The type system enforces this structurally: `EvidenceInput`
has no `executionSurface : ExecutionSurface` field; surface is always
sub-field of a documented observation.
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
  | from_full_coherent_bundle _ _ _ hLabel _ _ _ _ _ _ _ =>
      intro hNone; rw [hNone] at hLabel; cases hLabel
  | from_audited_no_default _ _ hLabel _ _ _ =>
      intro hNone; rw [hNone] at hLabel; cases hLabel

theorem admissibility_pure_of_evidence_input
    {e1 e2 : EvidenceInput} (h : e1 = e2) (claim : ConstraintClaim) :
    AdmissibleFromInput e1 claim ↔ AdmissibleFromInput e2 claim := by
  rw [h]

theorem deriveJudgment_pure_of_evidence_input
    {e1 e2 : EvidenceInput} (h : e1 = e2) :
    deriveJudgment e1 = deriveJudgment e2 := by
  rw [h]

end Admissibility.Scratch.Labelwatch
