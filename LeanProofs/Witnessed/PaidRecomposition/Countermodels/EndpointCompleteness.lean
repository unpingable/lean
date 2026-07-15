/-
  LeanProofs.Witnessed.PaidRecomposition.Countermodels.EndpointCompleteness --
  endpoint coverage is too weak for exact paid catalog adequacy.

  Custody-Class: ANNEX

  This Mathlib-free countermodel separates two attempts with identical
  endpoints but different custody and expected-payment content.  A catalog
  containing only the forged attempt covers every endpoint admitted by the
  topology, yet it cannot catalogue the authorized paid global plan because
  `PaidCatalogPlan` retains the exact certified attempt and its dependent
  positive receipt.

  Scope.  `EndpointCatalogComplete` is countermodel-local and intentionally
  absent from the stable catalog core.  The catalog refusal below is scoped to
  the named singleton catalog and has no transition or debt interpretation.
-/

import LeanProofs.Witnessed.PaidRecomposition.Catalog

namespace LeanProofs.Witnessed.PaidRecomposition.Countermodels.EndpointCompleteness

open LeanProofs.Witnessed.PaidRecomposition.Payment
open LeanProofs.Witnessed.PaidRecomposition.Catalog

/-! ## Two submissions with the same endpoints -/

/-- The two submitted attempts have the same endpoints.  Their constructors
    remain distinct because exact catalog custody is about attempts, not only
    endpoint pairs. -/
inductive Attempt where
  | authorized
  | forged
  deriving DecidableEq, Repr

abbrev Origin := Unit
abbrev Target := Unit
abbrev Token := Nat

def originOf (_ : Attempt) : Origin := ()

def targetOf (_ : Attempt) : Target := ()

/-- The expected payment is retained attempt content.  The forged submission
    self-declares a different token despite sharing the authorized endpoint. -/
def expectedOf : Attempt -> Token
  | .authorized => 7
  | .forged => 13

/-- Native positive submissions remain dependent on the exact checked
    attempt.  The forged attempt can pass its own self-declared submission
    check, but that receipt cannot change its retained expected payment. -/
inductive NativePositive : Attempt -> Type where
  | authorized : NativePositive .authorized
  | selfDeclaredForged : NativePositive .forged

/-- Endpoint topology deliberately admits both submissions.  Their exact
    identities, dependent receipts, and expected payments remain separate. -/
def topology (_ : Attempt) : Prop := True

def forgedOnlyCatalog : List Attempt := [.forged]

theorem attempts_share_endpoints :
    originOf .authorized = originOf .forged ∧
      targetOf .authorized = targetOf .forged := by
  exact ⟨rfl, rfl⟩

theorem attempts_have_different_expected_payments :
    expectedOf .authorized ≠ expectedOf .forged := by
  decide

/-! ## Endpoint-only coverage -/

/-- Countermodel-local endpoint completeness.  Every topological attempt has
    some catalog entry with the same endpoints; the entry need not be the same
    attempt and need not carry that attempt's dependent positive receipt. -/
def EndpointCatalogComplete (catalog : List Attempt) : Prop :=
  forall attempt : Attempt,
    topology attempt -> NativePositive attempt ->
      ∃ listed, listed ∈ catalog ∧
        originOf listed = originOf attempt ∧
        targetOf listed = targetOf attempt ∧
        topology listed ∧ Nonempty (NativePositive listed)

/-- The forged singleton covers all endpoints because both attempt
    constructors share the only endpoint pair. -/
theorem forgedOnly_endpoint_complete :
    EndpointCatalogComplete forgedOnlyCatalog := by
  intro attempt _ _
  exact ⟨.forged, by simp [forgedOnlyCatalog], rfl, rfl, True.intro,
    ⟨.selfDeclaredForged⟩⟩

/-! ## An authorized paid global plan -/

def authorizedReceipt : NativePositive .authorized := .authorized

def authorizedGlobalEdge :
    PaidGlobalEdge originOf targetOf NativePositive topology () () where
  attempt := .authorized
  receipt := authorizedReceipt
  origin_eq := rfl
  target_eq := rfl
  topologyAccepted := True.intro

def oneExpected (_ : Origin) : Token := 7

/-- The payment consumes occurrence zero of the submitted wallet and computes
    the empty residue.  The `removeAt` equation in `PaymentTrace.cons` is the
    authoritative occurrence certificate. -/
def onePayment : PaymentTrace oneExpected [()] [7] [] := by
  exact PaymentTrace.cons () 0 rfl rfl (PaymentTrace.nil [])

def authorizedGlobalPlan :
    PaidGlobalPlan originOf targetOf expectedOf NativePositive topology
      [()] [7] where
  assign := fun _ => ()
  certified := by
    intro origin _
    cases origin
    exact authorizedGlobalEdge
  injectiveOn := by
    intro left _ right _ _
    exact Subsingleton.elim left right
  expected := oneExpected
  expected_eq := by
    intro origin _
    cases origin
    rfl
  residue := []
  payment := onePayment

theorem authorized_global_paid_plan_exists :
    Nonempty (PaidGlobalPlan originOf targetOf expectedOf
      NativePositive topology [()] [7]) :=
  ⟨authorizedGlobalPlan⟩

/-! ## Endpoint coverage cannot globalize exact paid refusal -/

/-- Exact membership in the forged-only catalog fixes the certified attempt
    to `.forged`; `expected_eq` then demands token 13, which cannot be removed
    from the submitted wallet `[7]`. -/
theorem forgedOnly_has_no_paid_catalog_plan :
    ¬ Nonempty (PaidCatalogPlan originOf targetOf expectedOf
      NativePositive topology forgedOnlyCatalog [()] [7]) := by
  rintro ⟨plan⟩
  have owedMember : () ∈ [()] := List.Mem.head []
  have exactMembership := plan.inCatalog () owedMember
  have exactAttempt :
      (plan.global.certified () owedMember).attempt = .forged := by
    simpa [forgedOnlyCatalog] using exactMembership
  have expectedEq := plan.global.expected_eq () owedMember
  rw [exactAttempt] at expectedEq
  have expectedForged : plan.global.expected () = 13 := by
    simpa [expectedOf] using expectedEq.symm
  cases plan.global.payment with
  | cons _ occurrenceIndex selected _ _ =>
      rw [expectedForged] at selected
      simp at selected

/-- Endpoint completeness and catalog-relative paid refusal coexist with an
    authorized paid global plan.  Therefore endpoint coverage alone cannot
    support the stable core's refusal-globalization conclusion. -/
theorem endpoint_completeness_does_not_globalize_paid_refusal :
    EndpointCatalogComplete forgedOnlyCatalog ∧
      Nonempty (PaidGlobalPlan originOf targetOf expectedOf
        NativePositive topology [()] [7]) ∧
      ¬ Nonempty (PaidCatalogPlan originOf targetOf expectedOf
        NativePositive topology forgedOnlyCatalog [()] [7]) :=
  ⟨forgedOnly_endpoint_complete, authorized_global_paid_plan_exists,
    forgedOnly_has_no_paid_catalog_plan⟩

/-- Exact completeness rejects precisely the substitution that endpoint
    completeness permits: the authorized attempt itself is absent. -/
theorem forgedOnly_not_exact_complete :
    ¬ ExactPaidCatalogComplete NativePositive topology
      forgedOnlyCatalog := by
  intro complete
  have exactMembership : Attempt.authorized ∈ forgedOnlyCatalog :=
    complete .authorized True.intro authorizedReceipt
  simp [forgedOnlyCatalog] at exactMembership

end LeanProofs.Witnessed.PaidRecomposition.Countermodels.EndpointCompleteness
