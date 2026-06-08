/-
  Custody-Class: SCRATCH

  Labelwatch — first non-synthetic pressure test, 2026-06-08
  (revisions: EvidenceInput/DerivedJudgment separation;
  ExecutionSurface schema patch from D-001; ConsumerAdoption /
  ConsumerScope patch from Specimen 003 / Driftwatch).
  Not imported by `LeanProofs.lean`. Not part of any 1.0 surface.
  No paper anchor. No promotion path. NOT used as discharge for
  any doctrine.

  Hard discipline:
    1. Hand-authored evidence packets are FIXTURES only.
    2. EvidenceInput contains ONLY observable/documentary facts.
    3. DerivedJudgment contains the products of interpretation.
       Computed FROM EvidenceInput, never appears as an input.
    4. No specimen theorem takes its gap or scope as a premise.
    5. No evidence constructor contains a verdict-like field.
    6. Derived judgments are NOT admissible as input evidence
       unless witnessed independently.

  Specimen 003 / Driftwatch finding (2026-06-08):
    skywatch.blue emits "fringe-media" label (third-party emitter).
    Case A: no consumer adopts → consumer_scope_effective = emitter_declared
    Case B: driftwatch adopts + has action receipt → consumer_scope_effective = opt_in:driftwatch
    The same underlying third-party label witnesses two different
    effective scopes. The schema must represent the difference
    without allowing local conversion to promote evidence to global.

  Spec003 patch (this revision):
    - ConsumerScope : global_platform | emitter_declared | opt_in consumer_id
    - ConsumerAdoption (structure): documentary record of a consumer
      adopting a label/policy artifact
    - ConsumerActionObservation (structure): receipt that a consumer
      acted on the label at some surface
    - Two new admissibility constructors:
        from_emitter_only_scope (no adoption → emitter_declared)
        from_consumer_adoption_and_action (adoption + action → opt_in)
    - no_cross_consumer_inference theorem
    - no_global_promotion theorem (vacuous-by-design: there is no
      constructor for .global_platform; admitting one would require
      platform-specific witness evidence we do not model)

  Spec003 guard (per operator):
    No subscription graph modeling. No multi-consumer adoption yet.
    One named consumer (driftwatch), one label (fringe-media), one
    receipt.

  Non-global provenance inheritance:
    The opt_in tag in `.consumer_scope ... (.opt_in cid)` IS the
    non-global provenance marker. There is no path by which a claim
    with opt_in scope is rewritten or promoted to global_platform.
    Structural — not requiring a separate theorem beyond
    no_global_promotion.
-/

namespace Admissibility.Scratch.Labelwatch

/-! ## Execution surface -/

inductive ExecutionSurface where
  | render
  | hosting
  | mixed
  | unknown
  deriving DecidableEq, Repr

/-! ## Consumer scope (added Specimen 003) -/

inductive ConsumerScope where
  | global_platform           -- platform-default adoption (no constructor admits this)
  | emitter_declared          -- only the emitter has declared; no consumer has acted
  | opt_in (consumerId : String)  -- a specific named consumer has adopted
  deriving DecidableEq, Repr

/-! ## Evidence types -/

structure LabelObservation where
  label : String
  subject : String
  observer : String
  timestamp : Nat
  deriving DecidableEq, Repr

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

/-- ConsumerAdoption: documentary record that a named consumer adopted
    a label/policy artifact. Adoption is the consumer's commitment to
    apply the label's conversion; it is distinct from policy witness
    (which witnesses an artifact application) and from action
    observation (which records the receipt of a specific act). -/
structure ConsumerAdoption where
  consumerId : String
  artifactId : String
  adoptedAt : Nat
  deriving DecidableEq, Repr

/-- ConsumerActionObservation: receipt that a specific named consumer
    acted on the label at some surface and context. Distinct from
    `ExecutionObservation` (which is platform or policy level) in that
    this is consumer-local — the consumer's own action receipt. -/
structure ConsumerActionObservation where
  consumerId : String
  subject : String
  constraint : String
  surface : ExecutionSurface
  actionContext : String
  timestamp : Nat
  deriving DecidableEq, Repr

/-! ## ConstraintClaim -/

inductive ConstraintClaim where
  | label_observed (subject : String) (label : String)
  | documented_conversion_path
      (subject : String) (label : String) (constraint : String)
      (policyArtifact : String) (surface : ExecutionSurface)
  | constraint_applied
      (subject : String) (constraint : String)
      (surface : ExecutionSurface) (executionContext : String)
  | no_default_constraint_followed (subject : String) (label : String)
  /-- The effective consumer scope of a label observation. -/
  | consumer_scope
      (subject : String) (label : String) (scope : ConsumerScope)
  deriving DecidableEq, Repr

/-! ## EvidenceInput -/

structure EvidenceInput where
  labelObs : Option LabelObservation
  policyDoc : Option PolicyDocumentation
  policyWit : Option PolicyWitness
  executionObs : Option ExecutionObservation
  auditEvents : List AuditEvent
  consumerAdoptions : List ConsumerAdoption
  consumerActions : List ConsumerActionObservation
  deriving DecidableEq, Repr

/-! ## Admissibility relation -/

inductive AdmissibleFromInput : EvidenceInput → ConstraintClaim → Prop where
  | from_label
      (e : EvidenceInput) (l : LabelObservation)
      (hLabel : e.labelObs = some l)
      : AdmissibleFromInput e (.label_observed l.subject l.label)
  | from_label_and_policy_doc
      (e : EvidenceInput) (l : LabelObservation) (p : PolicyDocumentation)
      (hLabel : e.labelObs = some l)
      (hPolicy : e.policyDoc = some p)
      (hLabelMatch : l.label = p.label)
      : AdmissibleFromInput e
          (.documented_conversion_path l.subject p.label p.constraint
            p.artifactId p.executionSurface)
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
  /-- A label observation with NO consumer adoptions grounds the
      emitter_declared scope claim. -/
  | from_emitter_only_scope
      (e : EvidenceInput) (l : LabelObservation)
      (hLabel : e.labelObs = some l)
      (hNoAdoption : e.consumerAdoptions = [])
      : AdmissibleFromInput e (.consumer_scope l.subject l.label .emitter_declared)
  /-- A label observation + a consumer adoption + a consumer action
      receipt (same consumerId, same subject) grounds the opt_in
      scope claim. The opt_in tag carries the consumer's name as the
      non-global provenance marker. -/
  | from_consumer_adoption_and_action
      (e : EvidenceInput) (l : LabelObservation)
      (ca : ConsumerAdoption) (action : ConsumerActionObservation)
      (hLabel : e.labelObs = some l)
      (hAdoption : ca ∈ e.consumerAdoptions)
      (hAction : action ∈ e.consumerActions)
      (hSameConsumer : ca.consumerId = action.consumerId)
      (hSubjectMatch : l.subject = action.subject)
      : AdmissibleFromInput e
          (.consumer_scope l.subject l.label (.opt_in ca.consumerId))

/-! ## DerivedJudgment -/

inductive ConversionGap where
  | execution_gap_policy_present (surface : ExecutionSurface)
  | conversion_witness_gap_no_consumer
  | other_gap
  deriving DecidableEq, Repr

structure DerivedJudgment where
  gap : Option ConversionGap
  effectiveScope : Option ConsumerScope
  deriving DecidableEq, Repr

def hasNoConsumerAudit : List AuditEvent → Bool
  | [] => false
  | a :: rest =>
      match a.outcome with
      | .no_consumer_found_converting => true
      | _ => hasNoConsumerAudit rest

def classifyInputGap (e : EvidenceInput) : Option ConversionGap :=
  match e.labelObs, e.policyDoc, e.executionObs, hasNoConsumerAudit e.auditEvents with
  | some _, some p, none, _ => some (.execution_gap_policy_present p.executionSurface)
  | some _, none, none, true => some .conversion_witness_gap_no_consumer
  | some _, _, none, _ => some .other_gap
  | _, _, _, _ => none

/-- Classify the effective consumer scope. Reads only EvidenceInput.
    Takes the first ConsumerAdoption (per "one named consumer" guard).
    If a future patch admits multi-consumer, this classifier extends. -/
def classifyEffectiveScope (e : EvidenceInput) : Option ConsumerScope :=
  match e.labelObs, e.consumerAdoptions with
  | some _, [] => some .emitter_declared
  | some _, c :: _ => some (.opt_in c.consumerId)
  | none, _ => none

def deriveJudgment (e : EvidenceInput) : DerivedJudgment :=
  { gap := classifyInputGap e, effectiveScope := classifyEffectiveScope e }

/-! ## Specimens -/

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
  auditEvents := [],
  consumerAdoptions := [],
  consumerActions := []
}

def spec002 : EvidenceInput := {
  labelObs := some {
    label := "warning", subject := "post_abc",
    observer := "moderator_b", timestamp := 200 },
  policyDoc := none,
  policyWit := none,
  executionObs := none,
  auditEvents := [spec002_audit],
  consumerAdoptions := [],
  consumerActions := []
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
  auditEvents := [],
  consumerAdoptions := [],
  consumerActions := []
}

/-- skywatch.blue emits "fringe-media" label — third-party emitter. -/
def skywatch_fringe_label : LabelObservation := {
  label := "fringe-media",
  subject := "post_uvw",
  observer := "skywatch.blue",
  timestamp := 500
}

/-- Spec003 Case A: same skywatch label, NO consumer adoption.
    Effective scope should be emitter_declared. -/
def spec003a : EvidenceInput := {
  labelObs := some skywatch_fringe_label,
  policyDoc := none,
  policyWit := none,
  executionObs := none,
  auditEvents := [],
  consumerAdoptions := [],
  consumerActions := []
}

def driftwatch_adoption : ConsumerAdoption := {
  consumerId := "driftwatch",
  artifactId := "skywatch.blue/fringe-media",
  adoptedAt := 600
}

def driftwatch_action : ConsumerActionObservation := {
  consumerId := "driftwatch",
  subject := "post_uvw",
  constraint := "demote_locally",
  surface := .render,
  actionContext := "driftwatch_feed",
  timestamp := 700
}

/-- Spec003 Case B: same skywatch label, driftwatch has adopted and
    has an action receipt. Effective scope should be opt_in:driftwatch.
    Effective scope MUST NOT be global_platform. -/
def spec003b : EvidenceInput := {
  labelObs := some skywatch_fringe_label,
  policyDoc := none,
  policyWit := none,
  executionObs := none,
  auditEvents := [],
  consumerAdoptions := [driftwatch_adoption],
  consumerActions := [driftwatch_action]
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

/-- Spec003 Case A: no adoption → emitter_declared scope is admissible. -/
theorem spec003a_admits_emitter_declared_scope :
    AdmissibleFromInput spec003a
      (.consumer_scope "post_uvw" "fringe-media" .emitter_declared) :=
  AdmissibleFromInput.from_emitter_only_scope spec003a skywatch_fringe_label rfl rfl

/-- Spec003 Case B: driftwatch adopted + acted → opt_in:driftwatch
    scope is admissible. -/
theorem spec003b_admits_opt_in_driftwatch_scope :
    AdmissibleFromInput spec003b
      (.consumer_scope "post_uvw" "fringe-media" (.opt_in "driftwatch")) :=
  AdmissibleFromInput.from_consumer_adoption_and_action
    spec003b skywatch_fringe_label driftwatch_adoption driftwatch_action
    rfl (List.Mem.head _) (List.Mem.head _) rfl rfl

/-! ## Non-laundering theorems (carried forward) -/

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

/-! ## Spec003 non-inference theorems

These are the load-bearing theorems for the patch.
-/

/-- Adoption by consumer C does not imply adoption by consumer D.
    Phrased as: if every ConsumerAdoption in the bundle has
    consumerId equal to c, and d ≠ c, then the bundle cannot derive
    an opt_in:d scope claim. -/
theorem no_cross_consumer_inference
    {e : EvidenceInput} {subject label d : String}
    (h_no_d_adoption :
      ∀ ca : ConsumerAdoption, ca ∈ e.consumerAdoptions → ca.consumerId ≠ d) :
    ¬ AdmissibleFromInput e (.consumer_scope subject label (.opt_in d)) := by
  intro h
  cases h with
  | from_consumer_adoption_and_action _ ca _ _ hAdoption _ _ _ =>
      -- After cases, the claim's .opt_in d unifies with the constructor's
      -- .opt_in ca.consumerId, so d is substituted by ca.consumerId.
      -- h_no_d_adoption ca hAdoption (after substitution) has type
      -- ca.consumerId ≠ ca.consumerId. Apply to rfl → False.
      exact h_no_d_adoption ca hAdoption rfl

/-- Spec003b specifically: cannot infer that "otherwatch" has adopted
    from "driftwatch"'s adoption. Pairs with
    spec003b_admits_opt_in_driftwatch_scope as the positive counterpart. -/
theorem spec003b_refuses_otherwatch_scope :
    ¬ AdmissibleFromInput spec003b
      (.consumer_scope "post_uvw" "fringe-media" (.opt_in "otherwatch")) := by
  apply no_cross_consumer_inference (d := "otherwatch")
  intro ca hCa
  rcases List.mem_cons.mp hCa with rfl | h
  · decide
  · cases h

/-- Opt_in consumer adoption does not promote to global_platform.
    Proven structurally: there is NO admissibility constructor that
    produces a `.global_platform` scope claim. Adding one would
    require platform-specific witness evidence that this minimum
    vocabulary does not model. -/
theorem no_global_promotion
    (e : EvidenceInput) (subject label : String) :
    ¬ AdmissibleFromInput e (.consumer_scope subject label .global_platform) := by
  intro h
  cases h

/-! ## Gap classification + scope classification (DerivedJudgment side)

These are PROPERTIES of derived judgments. No specimen theorem
takes any of them as a premise.
-/

theorem spec001_derived_gap :
    (deriveJudgment spec001).gap = some (.execution_gap_policy_present .render) := rfl

theorem spec002_derived_gap :
    (deriveJudgment spec002).gap = some .conversion_witness_gap_no_consumer := rfl

theorem spec001_and_spec002_gaps_differ :
    (deriveJudgment spec001).gap ≠ (deriveJudgment spec002).gap := by
  rw [spec001_derived_gap, spec002_derived_gap]
  intro h; cases h

theorem spec003a_derived_scope :
    (deriveJudgment spec003a).effectiveScope = some .emitter_declared := rfl

theorem spec003b_derived_scope :
    (deriveJudgment spec003b).effectiveScope = some (.opt_in "driftwatch") := rfl

/-- The same underlying label produces different effective scopes
    depending on whether a consumer has adopted. This is the
    Spec003 / Driftwatch counterexample to the accidental rule
    "third-party → no conversion." -/
theorem spec003a_and_spec003b_scopes_differ :
    (deriveJudgment spec003a).effectiveScope ≠ (deriveJudgment spec003b).effectiveScope := by
  rw [spec003a_derived_scope, spec003b_derived_scope]
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

theorem spec003a_admissibility_nonempty :
    ∃ c, AdmissibleFromInput spec003a c :=
  ⟨_, spec003a_admits_emitter_declared_scope⟩

theorem spec003b_admissibility_nonempty :
    ∃ c, AdmissibleFromInput spec003b c :=
  ⟨_, spec003b_admits_opt_in_driftwatch_scope⟩

/-! ## The separation invariant

The principle:
  "Derived judgments are not admissible as input evidence unless
   witnessed independently."

CAVEAT 1 (recorded 2026-06-08): the theorem name
`derived_judgments_require_independent_witness` slightly overclaims.
The proof shows every current admissibility constructor requires a
LabelObservation — specimen-track local. The broader principle is
structural (type signature of `AdmissibleFromInput`).
`admissible_claims_require_label_anchor` would be a more accurate
name.

CAVEAT 2 (recorded 2026-06-08): `AuditEvent.scope` is a laundering
pressure point. The no_consumer_found_converting outcome is safe
ONLY if scope is precise (consumer/context/surface/time-named).
Type system doesn't enforce this.

CAVEAT 3 (recorded 2026-06-08 with D-001 patch): `ExecutionSurface`
appears as input evidence ONLY as a field of `PolicyDocumentation`
or `ExecutionObservation`. Not as a free-standing verdict.

CAVEAT 4 (recorded 2026-06-08 with Spec003 patch, updated post-review):
`ConsumerScope` appears as input evidence ONLY through
`ConsumerAdoption` (consumerId field) and `ConsumerActionObservation`
(consumerId field). Not as a free-standing scope verdict in the
bundle.

Two sub-caveats on this slice's claim of "no global promotion":

  (a) `no_global_promotion` is named more broadly than what it
  proves. The proof is: "there is no constructor in this fenced
  consumer-adoption fragment that produces `.global_platform`." It
  is NOT a general claim that no evidence anywhere can ground
  `.global_platform`. A future patch admitting a platform-witness
  constructor (e.g., first-party protocol evidence) would
  legitimately derive `.global_platform`. The current theorem is
  correct only WITHIN this fragment. A more honest name would be
  `opt_in_adoption_does_not_promote_to_global` or
  `no_global_scope_from_consumer_adoption_fragment`. Kept under the
  broader name as a fenced marker; rename when a platform-witness
  constructor is added.

  (b) Non-globality is structurally preserved through
  `ConsumerScope.opt_in cid` (the consumerId tag is the
  non-global-provenance marker). This spike does NOT model arbitrary
  caveat-list inheritance (e.g., Labelwatch packets carrying named
  caveats like `non_global_provenance`, `consumer_local_scope_only`,
  `no_cross_consumer_inference` as a free-form set). The Lean side
  preserves the SCOPE caveat structurally; it does not yet model
  caveat lists as data. That is the correct boundary for this slice.

CAVEAT 5 (recorded 2026-06-08 with Spec003 patch, updated post-review):
the `classifyEffectiveScope` function takes the FIRST
ConsumerAdoption per the "one named consumer" guard. This is a quiet
policy — deterministic but not loud about its choice. If
multi-consumer adoption is ever admitted in a future slice, the
operator's stated preference is to make >1 ConsumerAdoption return
`none` (unsupported/ambiguous) rather than silently take the first.
The current single-consumer reading is a known partial; the
fail-over-first preference is recorded as the next likely D-style
bite if multi-consumer specimens appear before the classifier is
patched.
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
  | from_emitter_only_scope _ hLabel _ =>
      intro hNone; rw [hNone] at hLabel; cases hLabel
  | from_consumer_adoption_and_action _ _ _ hLabel _ _ _ _ =>
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
