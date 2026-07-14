/-
  Custody-Class: SCRATCH

  StatusConversionBinding — formalization-leading repair of the field-guide
  `ReportedStatusRequiresConversionWitness` fragment.

  Source:
    `papers/working/tooltheory/admissibility-field-guide-2026-06-05.md`

  The source shape accepts every `some witness`; its justification, authority,
  scope, and timestamp fields are inert, and no report object is bound. This
  specimen makes the conversion witness dependent on the exact internal status,
  external status, report object, and evaluation time. Authority, scope, and
  conversion permission come from an external policy relation: the witness
  cannot certify its own issuer or mint its own validity window.

  The positive path remains usable, while source erasure and report-object
  erasure are exhibited as concrete laundering moves. This file is unwired and
  is not imported by `LeanProofs.lean`.
-/

import LeanProofs.ViewSemantics.Core

namespace Admissibility.Scratch.StatusConversionBinding

open LeanProofs.ViewSemantics

inductive InternalStatus where
  | green
  | yellow
  | red
  | unknown
deriving DecidableEq, Repr

inductive ExternalStatus where
  | green
  | degraded
  | red
  | unknown
deriving DecidableEq, Repr

inductive Scope where
  | alpha
  | beta
deriving DecidableEq, Repr

/-- The object being reported is part of the conversion boundary. -/
structure ReportObject where
  id : Nat
  requiredScope : Scope
deriving DecidableEq, Repr

def consistentStatusB : InternalStatus → ExternalStatus → Bool
  | .green, .green => true
  | .green, .degraded => false
  | .green, .red => false
  | .green, .unknown => false
  | .yellow, .green => false
  | .yellow, .degraded => true
  | .yellow, .red => false
  | .yellow, .unknown => false
  | .red, .green => false
  | .red, .degraded => false
  | .red, .red => true
  | .red, .unknown => false
  | .unknown, .green => false
  | .unknown, .degraded => false
  | .unknown, .red => false
  | .unknown, .unknown => true

def ConsistentStatus (internal : InternalStatus)
    (external : ExternalStatus) : Prop :=
  consistentStatusB internal external = true

/-- External validation relations. None of these facts is supplied merely by
    naming an issuer or writing a justification string in a witness. -/
structure ConversionPolicy where
  issuerStandingAt : Nat → Nat → Prop
  scopeCovers : Scope → ReportObject → Prop
  permitsConversion :
    Nat → Scope → ReportObject → InternalStatus → ExternalStatus → Prop

/-- A conversion receipt bound to the exact report coordinates and checked at
    `now`. `justification` remains metadata; the proof-bearing fields below are
    what authorize the crossing. -/
structure StatusConversionWitness
    (policy : ConversionPolicy)
    (report : ReportObject)
    (internal : InternalStatus)
    (external : ExternalStatus)
    (now : Nat) where
  issuer : Nat
  scope : Scope
  issuedAt : Nat
  justification : String
  notFuture : issuedAt ≤ now
  issuerStandingAtIssue : policy.issuerStandingAt issuer issuedAt
  issuerStandingAtReport : policy.issuerStandingAt issuer now
  scopeCovers : policy.scopeCovers scope report
  conversionPermitted :
    policy.permitsConversion issuer scope report internal external

/-- A report is admissible either because the status pair is faithful already,
    or because an externally validated, exactly indexed conversion is present. -/
inductive AdmissibleReport
    (policy : ConversionPolicy) (report : ReportObject) (now : Nat) :
    InternalStatus → ExternalStatus → Prop where
  | consistent {internal external}
      (h : ConsistentStatus internal external) :
      AdmissibleReport policy report now internal external
  | converted {internal external}
      (w : StatusConversionWitness policy report internal external now) :
      AdmissibleReport policy report now internal external

theorem consistent_report_admissible_without_conversion
    (policy : ConversionPolicy) (report : ReportObject) (now : Nat) :
    AdmissibleReport policy report now .green .green :=
  .consistent rfl

/-- Inverting an inconsistent admissible report exposes every paid coordinate;
    there is no `isSome` shortcut. -/
theorem inconsistent_admissible_report_has_exact_binding
    (policy : ConversionPolicy) (report : ReportObject) (now : Nat)
    (internal : InternalStatus) (external : ExternalStatus)
    (hInconsistent : ¬ ConsistentStatus internal external)
    (hAdmissible : AdmissibleReport policy report now internal external) :
    ∃ witness : StatusConversionWitness policy report internal external now,
      witness.issuedAt ≤ now ∧
      policy.issuerStandingAt witness.issuer witness.issuedAt ∧
      policy.issuerStandingAt witness.issuer now ∧
      policy.scopeCovers witness.scope report ∧
      policy.permitsConversion witness.issuer witness.scope report
        internal external := by
  cases hAdmissible with
  | consistent hConsistent => exact False.elim (hInconsistent hConsistent)
  | converted witness =>
      exact
        ⟨witness, witness.notFuture,
          witness.issuerStandingAtIssue, witness.issuerStandingAtReport,
          witness.scopeCovers, witness.conversionPermitted⟩

/-! ## Externally checked specimen -/

def alphaReport : ReportObject := ⟨100, .alpha⟩
def otherAlphaReport : ReportObject := ⟨101, .alpha⟩
def betaReport : ReportObject := ⟨100, .beta⟩

def specimenIssuerStanding (issuer now : Nat) : Prop :=
  issuer = 7 ∧ now < 10

def specimenScopeCovers (scope : Scope) (report : ReportObject) : Prop :=
  scope = report.requiredScope

def specimenPermitsConversion
    (issuer : Nat) (scope : Scope) (report : ReportObject)
    (internal : InternalStatus) (external : ExternalStatus) : Prop :=
  issuer = 7 ∧
    scope = .alpha ∧
    report = alphaReport ∧
    internal = .yellow ∧
    external = .green

def specimenPolicy : ConversionPolicy where
  issuerStandingAt := specimenIssuerStanding
  scopeCovers := specimenScopeCovers
  permitsConversion := specimenPermitsConversion

def exactYellowGreenWitness :
    StatusConversionWitness specimenPolicy alphaReport .yellow .green 5 where
  issuer := 7
  scope := .alpha
  issuedAt := 2
  justification := "bounded external presentation"
  notFuture := by decide
  issuerStandingAtIssue := ⟨rfl, by decide⟩
  issuerStandingAtReport := ⟨rfl, by decide⟩
  scopeCovers := rfl
  conversionPermitted := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem exact_authorized_conversion_admissible :
    AdmissibleReport specimenPolicy alphaReport 5 .yellow .green :=
  .converted exactYellowGreenWitness

theorem wrong_source_not_admissible :
    ¬ AdmissibleReport specimenPolicy alphaReport 5 .red .green := by
  intro h
  cases h with
  | consistent hConsistent =>
      exact Bool.noConfusion hConsistent
  | converted witness =>
      have hSource : InternalStatus.red = .yellow :=
        witness.conversionPermitted.2.2.2.1
      exact (by decide : InternalStatus.red ≠ .yellow) hSource

theorem wrong_report_object_not_admissible :
    ¬ AdmissibleReport specimenPolicy otherAlphaReport 5 .yellow .green := by
  intro h
  cases h with
  | consistent hConsistent =>
      exact Bool.noConfusion hConsistent
  | converted witness =>
      have hReport : otherAlphaReport = alphaReport :=
        witness.conversionPermitted.2.2.1
      exact (by decide : otherAlphaReport ≠ alphaReport) hReport

theorem wrong_scope_not_admissible :
    ¬ AdmissibleReport specimenPolicy betaReport 5 .yellow .green := by
  intro h
  cases h with
  | consistent hConsistent =>
      exact Bool.noConfusion hConsistent
  | converted witness =>
      have hBeta : witness.scope = Scope.beta := witness.scopeCovers
      have hAlpha : witness.scope = Scope.alpha :=
        witness.conversionPermitted.2.1
      have hScope : Scope.beta = .alpha := hBeta.symm.trans hAlpha
      exact (by decide : Scope.beta ≠ .alpha) hScope

theorem expired_conversion_not_admissible :
    ¬ AdmissibleReport specimenPolicy alphaReport 10 .yellow .green := by
  intro h
  cases h with
  | consistent hConsistent =>
      exact Bool.noConfusion hConsistent
  | converted witness =>
      have hStanding : specimenIssuerStanding witness.issuer 10 :=
        witness.issuerStandingAtReport
      exact (Nat.lt_irrefl 10) hStanding.2

/-! ## Same external surface, different admissibility -/

inductive ReportWorld where
  | authorizedYellowGreen
  | unauthorizedRedGreen
deriving DecidableEq, Repr

def externalSurface : ReportWorld → ExternalStatus
  | .authorizedYellowGreen => .green
  | .unauthorizedRedGreen => .green

/-- Internal status remains part of the faithful world even though the
    external-only surface below erases it. -/
def internalStatus : ReportWorld → InternalStatus
  | .authorizedYellowGreen => .yellow
  | .unauthorizedRedGreen => .red

def admissibilityVerdict : ReportWorld → Bool
  | .authorizedYellowGreen => true
  | .unauthorizedRedGreen => false

/-- The finite Boolean verdict is proved faithful to `AdmissibleReport`; it is
    not an independently asserted label. -/
theorem admissibility_verdict_true_iff (world : ReportWorld) :
    admissibilityVerdict world = true ↔
      AdmissibleReport specimenPolicy alphaReport 5
        (internalStatus world) (externalSurface world) := by
  cases world with
  | authorizedYellowGreen =>
      constructor
      · intro _
        exact exact_authorized_conversion_admissible
      · intro _
        rfl
  | unauthorizedRedGreen =>
      constructor
      · intro hVerdict
        exact Bool.noConfusion hVerdict
      · intro hAdmissible
        exact False.elim (wrong_source_not_admissible hAdmissible)

theorem same_external_surface_different_admissibility :
    externalSurface .authorizedYellowGreen =
        externalSurface .unauthorizedRedGreen ∧
      admissibilityVerdict .authorizedYellowGreen ≠
        admissibilityVerdict .unauthorizedRedGreen := by
  decide

theorem external_surface_does_not_determine_admissibility :
    NotFullyDetermining externalSurface admissibilityVerdict := by
  intro hDetermines
  exact (same_external_surface_different_admissibility.2
    (hDetermines .authorizedYellowGreen .unauthorizedRedGreen
      same_external_surface_different_admissibility.1))

/-! ## Deliberately collapsed witness shapes -/

/-- Erasing source and report object leaves only the destination label. -/
structure DestinationOnlyWitness where
  target : ExternalStatus
deriving DecidableEq, Repr

def eraseToDestination
    {policy report internal external now}
    (_ : StatusConversionWitness policy report internal external now) :
    DestinationOnlyWitness :=
  ⟨external⟩

def DestinationOnlyAdmissible
    (external : ExternalStatus) (witness : DestinationOnlyWitness) : Prop :=
  witness.target = external

/-- A legitimate yellow→green conversion becomes a reusable red→green token
    after the source coordinate is erased; the faithful gate refuses it. -/
theorem destination_only_witness_launders_source :
    DestinationOnlyAdmissible .green
        (eraseToDestination exactYellowGreenWitness) ∧
      ¬ AdmissibleReport specimenPolicy alphaReport 5 .red .green :=
  ⟨rfl, wrong_source_not_admissible⟩

/-- Preserving the pair but erasing the report object permits replay elsewhere. -/
structure PairOnlyWitness where
  source : InternalStatus
  target : ExternalStatus
deriving DecidableEq, Repr

def eraseReportObject
    {policy report internal external now}
    (_ : StatusConversionWitness policy report internal external now) :
    PairOnlyWitness :=
  ⟨internal, external⟩

def PairOnlyAdmissible (internal : InternalStatus) (external : ExternalStatus)
    (witness : PairOnlyWitness) : Prop :=
  witness.source = internal ∧ witness.target = external

theorem object_erasure_allows_replay :
    PairOnlyAdmissible .yellow .green
        (eraseReportObject exactYellowGreenWitness) ∧
      ¬ AdmissibleReport specimenPolicy otherAlphaReport 5 .yellow .green :=
  ⟨⟨rfl, rfl⟩, wrong_report_object_not_admissible⟩

#print axioms consistent_report_admissible_without_conversion
#print axioms inconsistent_admissible_report_has_exact_binding
#print axioms exact_authorized_conversion_admissible
#print axioms wrong_source_not_admissible
#print axioms wrong_report_object_not_admissible
#print axioms wrong_scope_not_admissible
#print axioms expired_conversion_not_admissible
#print axioms admissibility_verdict_true_iff
#print axioms external_surface_does_not_determine_admissibility
#print axioms destination_only_witness_launders_source
#print axioms object_erasure_allows_replay

end Admissibility.Scratch.StatusConversionBinding
