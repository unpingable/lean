/-
  Custody-Class: PUBLIC-SHIPPED

  Admissibility — SurfaceAuthorization (Governor-facing refusal gate).

  Sibling to CollapsedSurface (which proves the negative kernel: a
  collapsed surface cannot identify cause). This module adds the
  *authorization* consequence: a collapsed surface cannot authorize
  cause-specific consequence without discriminating evidence.

  Keeper:
    A collapsed surface may authorize inquiry. It may not authorize attribution.

  Governor-shaped form:
    Cause-specific authority requires discriminating evidence.

  Provenance:
    Derived from the cross-primitive recurrence of the recovery-side
    question across testimony-vs-self-theory, Signal Authority,
    CollapsedSurface, and Paper 25's observation-equivalence framework.
    Earlier policy deferred this until Governor identified a concrete
    runtime use. That consumer gate is superseded as of 2026-07-14: the
    abstract refusal statement stands on its formal merits. Governor later
    supplied correspondence evidence; it did not authorize the theorem.

  Scope fence:
    - Encodes the *refusal gate*: collapsed + cause-specific + no
      discriminator ⇒ deny.
    - Does NOT encode the recovery machinery itself. `Breaker` is an
      abstract enum naming the three known recovery paths (preserved
      history, independent measurement, admissible perturbation); the
      predicates that constitute each kind remain unformalized here.
    - Companion working note:
      papers/working/signal-authority-candidate.md §Recovery side
    - Sibling Lean module:
      LeanProofs/CollapsedSurface.lean (the discrete-finite negative kernel)

  This is the authorization-side kernel. The recovery doctrine
  (`public_receipt_refines_observation` and its siblings) remains
  deliberately abstract: the gate encodes the boundary, not the
  epistemology.

  Repair-channel substrate:
    `LeanProofs/Admissibility/PublicReceiptRefinement.lean` is the
    closest existing partial-repair substrate, formalizing one of the
    three channels named in this kernel's `Breaker` enum (the public
    receipt that excludes some surface-admitted cause while remaining
    consistent with at least one). The other two `Breaker` cases
    (independent measurement, admissible perturbation) remain
    unformalized; that asymmetry is intentional, not an oversight.
    A future refusal-repair kernel (NOT a unified calculus — that
    framing was retired 2026-06-03) may extend
    `PublicReceiptRefinement`'s pattern once the two remaining evidence
    predicates are specified. Runtime demand is not a formalization gate.

  Custody:
    Public 1.0 surface; imported by the AdmissibilityKernels aggregator;
    signature anchored by commit hash + lake build proof gate + ratification
    rule on changes to the load-bearing names enumerated in the aggregator
    docstring. A definition matching this signature elsewhere does not
    inherit this anchoring.
-/

namespace Admissibility.SurfaceAuthorization

/-- Whether the observed public surface discriminates among possible
    causes. A `discriminating` surface is one where distinct causes
    produce distinct rendered states; a `collapsed` surface is one
    where multiple distinct causes render identically. -/
inductive SurfaceStatus where
  | discriminating
  | collapsed
deriving DecidableEq, Repr

/-- Kinds of action a controller may attempt against an observed
    surface. Observation-shaped actions (`observe`, `requestReceipt`,
    `openFinding`) inquire about state without imputing cause.
    Cause-specific actions impute a particular cause and act on that
    imputation. -/
inductive ActionKind where
  | observe
  | requestReceipt
  | openFinding
  | causeSpecificMutation
  | causeSpecificAccusation
  | revokeStanding
deriving DecidableEq, Repr

/-- Abstract recovery channel kinds. Each names a way collapsed
    observation-equivalence can be broken. The kernel does not yet
    formalize the predicates that constitute each kind; the gate
    only requires that *some* discriminator is present. -/
inductive Breaker where
  | preservedHistory       -- receipts, lineage, state-at-time-T
  | independentMeasurement -- another witness adding rank, not replication
  | admissiblePerturbation -- controlled excitation; not harm as measurement
deriving DecidableEq, Repr

/-- An action is cause-specific if it imputes a particular cause to the
    observed surface — mutating, accusing, or revoking on that basis. -/
def causeSpecific : ActionKind → Bool
  | .causeSpecificMutation   => true
  | .causeSpecificAccusation => true
  | .revokeStanding          => true
  | _                        => false

/-- At least one discriminating channel must be present to license
    cause-specific authority over a collapsed surface. -/
def hasDiscriminator : List Breaker → Bool
  | [] => false
  | _  => true

/-- Governor's verdict space for this gate. `advisoryOnly` is reserved
    for future use (e.g. allow-but-flag patterns); the current gate
    returns only `deny` or `allow`. -/
inductive Verdict where
  | allow
  | deny
  | advisoryOnly
deriving DecidableEq, Repr

/-- The authorization gate. Deny exactly the structurally invalid
    combination: collapsed surface + cause-specific action + no
    discriminating evidence. All other combinations allow. -/
def authorize
    (surface : SurfaceStatus)
    (action : ActionKind)
    (breakers : List Breaker) : Verdict :=
  match surface, causeSpecific action, hasDiscriminator breakers with
  | .collapsed, true, false => .deny
  | _, _, _                 => .allow

/-- The kernel theorem: a collapsed surface denies cause-specific
    consequence when no discriminating evidence has been produced.
    *Cause-specific authority requires discriminating evidence.* -/
theorem collapsed_surface_denies_cause_specific_without_breaker
    {action : ActionKind}
    (hcausal : causeSpecific action = true) :
    authorize SurfaceStatus.collapsed action [] = Verdict.deny := by
  simp [authorize, hasDiscriminator, hcausal]

/-- A discriminator (any of the three abstract recovery channels)
    licenses cause-specific consequence even against a collapsed surface.
    The kernel does not certify the recovery; it only refuses to deny
    when the recovery has been claimed. -/
theorem discriminator_licenses_cause_specific
    {action : ActionKind} {b : Breaker} {rest : List Breaker}
    (hcausal : causeSpecific action = true) :
    authorize SurfaceStatus.collapsed action (b :: rest) = Verdict.allow := by
  simp [authorize, hasDiscriminator, hcausal]

/-- Inquiry remains licensed even under collapsed surface with no
    discriminators. Observation does not require discriminating
    evidence; only attribution does. -/
theorem collapsed_surface_permits_observe :
    authorize SurfaceStatus.collapsed ActionKind.observe [] = Verdict.allow := by
  rfl

/-- Discriminating surfaces license any action (the gate only fires
    on collapse). -/
theorem discriminating_surface_permits_all
    (action : ActionKind) (breakers : List Breaker) :
    authorize SurfaceStatus.discriminating action breakers = Verdict.allow := by
  rfl

/-- Concrete instance: cause-specific mutation against a collapsed
    surface without discriminator is denied. -/
theorem collapsed_surface_denies_causeSpecificMutation :
    authorize SurfaceStatus.collapsed ActionKind.causeSpecificMutation [] = Verdict.deny :=
  collapsed_surface_denies_cause_specific_without_breaker rfl

/-- Concrete instance: revoking standing against a collapsed surface
    without discriminator is denied. -/
theorem collapsed_surface_denies_revokeStanding :
    authorize SurfaceStatus.collapsed ActionKind.revokeStanding [] = Verdict.deny :=
  collapsed_surface_denies_cause_specific_without_breaker rfl

end Admissibility.SurfaceAuthorization
