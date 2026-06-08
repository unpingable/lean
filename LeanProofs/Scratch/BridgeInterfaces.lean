/-
  Custody-Class: SCRATCH

  BridgeInterfaces — fenced spike, 2026-06-07. Not imported by
  `LeanProofs.lean`. Not part of any 1.0 surface. No paper anchor.
  No promotion path. NOT used as discharge for any doctrine.

  Goal: test whether admissibility refusals can be assigned to unique
  bridge owners when each bridge may consult only a declared narrow
  dependency interface, not the full State.

  Discipline:
  - Each bridge has a declared dependency interface (named functions)
  - Bridge decision functions pattern-match on specific State fields
    (visible by inspection); none read "whole State"
  - Refusal receipts carry the list of dependencies consulted
  - Cascade order assigns ownership: Resource → Index → Modality → Protocol
  - First-refusal wins for ownership; downstream bridges' opinions are
    recorded but not authoritative
  - "Grand calculus" framing is explicitly refused. This is a probe.

  See companion markdown:
  `~/git/papers/working/admissibility/bridge-interface-spike.md`
  for declared interfaces, specimen results, and ambiguity analysis.
-/

namespace Admissibility.Scratch.BridgeInterfaces

/-! ## Columns -/

inductive ResourceClass : Type where
  | linear_event
  | affine_budgeted
  | copyable_record
  | reusable_standing
  | counted_token
  deriving DecidableEq, Repr

inductive Modality : Type where
  | witnessed_live
  | receipt_of_witnessing
  | authorized
  | observed
  | justified
  | obligated
  | advisory
  | enforcement
  deriving DecidableEq, Repr

inductive ClaimKind : Type where
  | revocation
  | observation
  | authorization
  | risk_score
  | visibility_constraint
  | enforcement_action
  | obligation_claim
  deriving DecidableEq, Repr

structure Index where
  actor : String
  surface : String
  time : Nat
  scope : String
  deriving DecidableEq, Repr

structure State where
  resource : ResourceClass
  modality : Modality
  claimKind : ClaimKind
  index : Index
  deriving DecidableEq, Repr

/-! ## Bridge owners, dependency names, receipts, decisions -/

inductive BridgeOwner : Type where
  | resource
  | index
  | modality
  | protocol
  deriving DecidableEq, Repr

inductive DependencyName : Type where
  | requiredResourceClass
  | surfaceScopePolicy
  | allowedModalTransition
  | isDemotionPolicy
  | custodyRequirement
  deriving DecidableEq, Repr

structure RefusalReceipt where
  owner : BridgeOwner
  ruleName : String
  dependenciesConsulted : List DependencyName
  source : State
  target : State
  deriving Repr

inductive BridgeDecision : Type where
  | accept
  | acceptWithDemotion (rule : String)
  | refuse (receipt : RefusalReceipt)
  deriving Repr

/-! ## Concrete policies (the narrow declared interfaces)

Each policy below is named in exactly one bridge's interface. The
bridge consults the policy; nothing else. No bridge reads the whole
State by pattern matching across all four columns simultaneously.
-/

namespace Policies

/-- ResourceBridge interface — requiredResourceClass.
    For a given (modality, claimKind), which resource classes are
    admissible. Returns true if the resource class is admissible. -/
def requiredResourceClass : Modality → ClaimKind → ResourceClass → Bool
  -- witnessed_live requires linear_event
  | .witnessed_live, _, .linear_event => true
  | .witnessed_live, _, .affine_budgeted => false
  | .witnessed_live, _, .copyable_record => false
  | .witnessed_live, _, .reusable_standing => false
  | .witnessed_live, _, .counted_token => false
  -- receipt_of_witnessing accepts copyable_record (emission target)
  | .receipt_of_witnessing, _, .linear_event => false
  | .receipt_of_witnessing, _, .affine_budgeted => false
  | .receipt_of_witnessing, _, .copyable_record => true
  | .receipt_of_witnessing, _, .reusable_standing => false
  | .receipt_of_witnessing, _, .counted_token => false
  -- other modalities are unconstrained by this rule (return true)
  | .authorized, _, _ => true
  | .observed, _, _ => true
  | .justified, _, _ => true
  | .obligated, _, _ => true
  | .advisory, _, _ => true
  | .enforcement, _, _ => true

/-- IndexBridge interface — surfaceScopePolicy.
    For an (modality, claimKind, source_surface, target_surface), is the
    transition surface-admissible. Returns true if admissible. -/
def surfaceScopePolicy : Modality → ClaimKind → String → String → Bool
  | .authorized, .revocation, a, b => decide (a = b)
  | _, _, _, _ => true

/-- ModalityBridge interface — allowedModalTransition.
    Baseline: identity transitions only. Lawful demotions are handled
    via the separate isDemotionPolicy interface. -/
def allowedModalTransition : ClaimKind → ResourceClass → Modality → Modality → Bool
  | _, _, m1, m2 => decide (m1 = m2)

/-- ModalityBridge interface — isDemotionPolicy.
    Lawful (witnessed_live → receipt_of_witnessing) demotion is the only
    declared demotion in this spike. -/
def isDemotionPolicy : Modality → Modality → Bool
  | .witnessed_live, .receipt_of_witnessing => true
  | _, _ => false

/-- ProtocolBridge interface — custodyRequirement.
    Stub. No specimen in this spike forces it; included to keep the
    column structurally complete. -/
def custodyRequirement : Modality → ClaimKind → Bool
  | _, _ => true

end Policies

/-! ## Bridge decision functions

Each function declares above it which State fields it inspects. By
inspection, no bridge reads the whole State; each reads a narrow,
column-specific subset. The dependency interface names (consulted
policies) are recorded in each receipt.
-/

/-- ResourceBridge.
    Inspects: s.modality, s.claimKind, s.resource, t.modality,
    t.claimKind, t.resource.
    Does NOT inspect: s.index, t.index.
    Declared interface: requiredResourceClass. -/
def ResourceBridge.decide (s t : State) : BridgeDecision :=
  if !Policies.requiredResourceClass t.modality t.claimKind t.resource then
    .refuse {
      owner := .resource,
      ruleName := "target_resource_invalid_for_modality",
      dependenciesConsulted := [.requiredResourceClass],
      source := s, target := t }
  else if !Policies.requiredResourceClass s.modality s.claimKind s.resource then
    .refuse {
      owner := .resource,
      ruleName := "source_resource_invalid_for_modality",
      dependenciesConsulted := [.requiredResourceClass],
      source := s, target := t }
  else
    .accept

/-- IndexBridge.
    Inspects: s.modality, s.claimKind, s.index.surface, t.modality,
    t.claimKind, t.index.surface.
    Does NOT inspect: s.resource, t.resource, actor, time, scope.
    Declared interface: surfaceScopePolicy.
    Fires only when modality and claimKind are stable across the
    transition (i.e., this bridge owns surface-scope within a column;
    cross-column transitions are not its territory). -/
def IndexBridge.decide (s t : State) : BridgeDecision :=
  if s.modality = t.modality ∧ s.claimKind = t.claimKind then
    if !Policies.surfaceScopePolicy s.modality s.claimKind s.index.surface t.index.surface then
      .refuse {
        owner := .index,
        ruleName := "surface_scope_violation",
        dependenciesConsulted := [.surfaceScopePolicy],
        source := s, target := t }
    else .accept
  else .accept

/-- ModalityBridge.
    Inspects: s.modality, s.claimKind, s.resource, t.modality.
    Does NOT inspect: s.index, t.index, t.resource, t.claimKind.
    Declared interfaces: allowedModalTransition, isDemotionPolicy. -/
def ModalityBridge.decide (s t : State) : BridgeDecision :=
  if Policies.isDemotionPolicy s.modality t.modality then
    .acceptWithDemotion "lawful_demotion"
  else if Policies.allowedModalTransition s.claimKind s.resource s.modality t.modality then
    .accept
  else
    .refuse {
      owner := .modality,
      ruleName := "modality_transition_not_authorized",
      dependenciesConsulted := [.allowedModalTransition, .isDemotionPolicy],
      source := s, target := t }

/-- ProtocolBridge.
    Inspects: nothing in this spike (stub).
    Declared interface: custodyRequirement. -/
def ProtocolBridge.decide (_s _t : State) : BridgeDecision :=
  .accept

/-! ## Cascade composition

Cascade order: Resource → Index → Modality → Protocol.
First refusal wins for ownership assignment. Downstream bridges'
decisions are recorded but not authoritative. Demotions are
propagated as acceptWithDemotion with the demoting bridge's owner.
-/

inductive CascadeOutcome : Type where
  | accept
  | acceptWithDemotion (rule : String) (owner : BridgeOwner)
  | refuse (receipt : RefusalReceipt)
  deriving Repr

def cascade (s t : State) : CascadeOutcome :=
  match ResourceBridge.decide s t with
  | .refuse rc => .refuse rc
  | _ =>
    match IndexBridge.decide s t with
    | .refuse rc => .refuse rc
    | _ =>
      match ModalityBridge.decide s t with
      | .refuse rc => .refuse rc
      | .acceptWithDemotion rule => .acceptWithDemotion rule .modality
      | _ =>
        match ProtocolBridge.decide s t with
        | .refuse rc => .refuse rc
        | _ => .accept

/-! ## Extractor helpers (avoid match-pattern Decidable synthesis pain) -/

def CascadeOutcome.refusedBy : CascadeOutcome → Option BridgeOwner
  | .refuse rc => some rc.owner
  | _ => none

def CascadeOutcome.refusalRule : CascadeOutcome → Option String
  | .refuse rc => some rc.ruleName
  | _ => none

def CascadeOutcome.refusalDeps : CascadeOutcome → Option (List DependencyName)
  | .refuse rc => some rc.dependenciesConsulted
  | _ => none

def CascadeOutcome.demotedBy : CascadeOutcome → Option BridgeOwner
  | .acceptWithDemotion _ owner => some owner
  | _ => none

def CascadeOutcome.demotionRule : CascadeOutcome → Option String
  | .acceptWithDemotion rule _ => some rule
  | _ => none

def BridgeDecision.isAccept : BridgeDecision → Bool
  | .accept => true
  | _ => false

/-! ## Specimens

Each specimen is a (source, target) pair with an expected verdict.
Verdicts are checked at the type level via `decide` over the cascade
result. None of the proofs use `sorry`. None rely on unevaluated
String comparison beyond the rule names (which are short literals).
-/

namespace Specimens

/-- Specimen 1: witnessed_live source/target, copyable_record at target.
    Expected: ResourceBridge refuses with
    target_resource_invalid_for_modality. -/
def s1_source : State := {
  resource := .linear_event,
  modality := .witnessed_live,
  claimKind := .observation,
  index := { actor := "A", surface := "S1", time := 0, scope := "default" }
}
def s1_target : State := {
  resource := .copyable_record,
  modality := .witnessed_live,
  claimKind := .observation,
  index := { actor := "A", surface := "S1", time := 0, scope := "default" }
}

example : (cascade s1_source s1_target).refusedBy = some .resource := by rfl
example : (cascade s1_source s1_target).refusalRule = some "target_resource_invalid_for_modality" := by rfl
example : (cascade s1_source s1_target).refusalDeps = some [.requiredResourceClass] := by rfl

/-- Specimen 2: linear_event/witnessed_live → copyable_record/receipt_of_witnessing.
    Expected: ModalityBridge demotion (witnessed_live → receipt_of_witnessing). -/
def s2_source : State := s1_source
def s2_target : State := {
  resource := .copyable_record,
  modality := .receipt_of_witnessing,
  claimKind := .observation,
  index := { actor := "A", surface := "S1", time := 0, scope := "default" }
}

example : (cascade s2_source s2_target).demotedBy = some .modality := by rfl
example : (cascade s2_source s2_target).demotionRule = some "lawful_demotion" := by rfl

/-- Specimen 3: authorized revocation across surfaces.
    Expected: IndexBridge refuses with surface_scope_violation. -/
def s3_source : State := {
  resource := .copyable_record,
  modality := .authorized,
  claimKind := .revocation,
  index := { actor := "A", surface := "Asurf", time := 0, scope := "default" }
}
def s3_target : State := {
  resource := .copyable_record,
  modality := .authorized,
  claimKind := .revocation,
  index := { actor := "A", surface := "Bsurf", time := 0, scope := "default" }
}

example : (cascade s3_source s3_target).refusedBy = some .index := by rfl
example : (cascade s3_source s3_target).refusalRule = some "surface_scope_violation" := by rfl
example : (cascade s3_source s3_target).refusalDeps = some [.surfaceScopePolicy] := by rfl

/-- Specimen 4: authorized → observed (signature-as-observation).
    Expected: ModalityBridge refuses with modality_transition_not_authorized. -/
def s4_source : State := {
  resource := .copyable_record,
  modality := .authorized,
  claimKind := .authorization,
  index := { actor := "A", surface := "S1", time := 0, scope := "default" }
}
def s4_target : State := {
  resource := .copyable_record,
  modality := .observed,
  claimKind := .observation,
  index := { actor := "A", surface := "S1", time := 0, scope := "default" }
}

example : (cascade s4_source s4_target).refusedBy = some .modality := by rfl
example : (cascade s4_source s4_target).refusalRule = some "modality_transition_not_authorized" := by rfl

/-- Specimen 5: advisory risk_score → enforcement enforcement_action.
    Expected: ModalityBridge refuses with modality_transition_not_authorized.
    This is the ambiguity probe: multiple bridges could conceivably
    refuse, but under this spike's bounded interfaces, only
    ModalityBridge fires (others accept or don't apply). -/
def s5_source : State := {
  resource := .copyable_record,
  modality := .advisory,
  claimKind := .risk_score,
  index := { actor := "A", surface := "S1", time := 0, scope := "default" }
}
def s5_target : State := {
  resource := .copyable_record,
  modality := .enforcement,
  claimKind := .enforcement_action,
  index := { actor := "A", surface := "S1", time := 0, scope := "default" }
}

example : (cascade s5_source s5_target).refusedBy = some .modality := by rfl
example : (cascade s5_source s5_target).refusalRule = some "modality_transition_not_authorized" := by rfl

/-- Negative check: for specimen 5, neither IndexBridge nor ResourceBridge
    fires in isolation. This is the "no Resource OR Modality" ownership
    requirement: ownership is unambiguous. -/
example : (ResourceBridge.decide s5_source s5_target).isAccept = true := by rfl
example : (IndexBridge.decide s5_source s5_target).isAccept = true := by rfl
example : (ProtocolBridge.decide s5_source s5_target).isAccept = true := by rfl

/-- Specimen 6a: advisory risk_score → advisory visibility_constraint.
    Intra-modality claim-kind drift (modality stable, claimKind escalates
    within the advisory altitude). Tests whether the current bridges
    catch claim-kind transitions.

    EXPECTED (under current bounded interfaces): ACCEPT.
    DISCOVERY: no current bridge owns ClaimKind transitions when modality
    is stable. ModalityBridge's allowedModalTransition is parameterized
    over claimKind but its current policy (m1 = m2) is claimKind-blind.
    IndexBridge requires modality AND claimKind stability before firing,
    so a claimKind change makes it decline ownership. ResourceBridge
    treats advisory as unconstrained on resource. Net: ACCEPT — but this
    accept is the discovery, not the verdict. It reveals that the
    current interface set is incomplete for intra-modality claim-kind
    drift. See companion receipt for the missing-interface candidate. -/
def s6a_source : State := {
  resource := .copyable_record,
  modality := .advisory,
  claimKind := .risk_score,
  index := { actor := "A", surface := "S1", time := 0, scope := "default" }
}
def s6a_target : State := {
  resource := .copyable_record,
  modality := .advisory,
  claimKind := .visibility_constraint,
  index := { actor := "A", surface := "S1", time := 0, scope := "default" }
}

example : cascade s6a_source s6a_target = .accept := by rfl

/-- Specimen 6b: advisory visibility_constraint → enforcement
    enforcement_action. Cross-modality leg of the gradient. Similar
    structurally to Specimen 5 but with a different source claimKind.
    EXPECTED: REFUSED by ModalityBridge (advisory→enforcement is not
    identity, not a lawful demotion). -/
def s6b_source : State := s6a_target
def s6b_target : State := {
  resource := .copyable_record,
  modality := .enforcement,
  claimKind := .enforcement_action,
  index := { actor := "A", surface := "S1", time := 0, scope := "default" }
}

example : (cascade s6b_source s6b_target).refusedBy = some .modality := by rfl
example : (cascade s6b_source s6b_target).refusalRule = some "modality_transition_not_authorized" := by rfl

/-
  Specimen 6 gradient composition: the three-state chain
  advisory/risk_score → advisory/visibility_constraint → enforcement/enforcement_action.

  Per-step verdicts:
    Step 1 (S6a): ACCEPT — discovery; current interfaces do not catch
                          intra-modality claim-kind drift.
    Step 2 (S6b): REFUSED by ModalityBridge — cross-modality escalation
                          caught.

  Net observation: the gradient passes the cross-modality gate (Step 2)
  only because Step 1 silently smuggled the claim-kind escalation into
  the advisory column. The chain's *first* leg is the laundering surface;
  the *second* leg is where the existing instrument fires. This is the
  kind of finding the bounded-interface design exists to expose: an
  under-owned column visible by the order in which refusals land along a
  multi-step chain.
-/

end Specimens

end Admissibility.Scratch.BridgeInterfaces
