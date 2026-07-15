/-
  LeanProofs.Witnessed.PaidRecomposition.Applications.ResourceTraceOneCrossing
  -- public-only one-crossing evidence for occurrence-exact paid recomposition.

  Custody-Class: ANNEX

  This Mathlib-free application instantiates the paid-recomposition core with
  the resident `ResourceCheckerExec.Trace` attempt type and the native
  `checkTrace = some ...` positive receipt used by `LaunderingCorpus`.  The
  catalog conversion nests the original global plan, so it cannot replace the
  submitted trace, its resident receipt, the expected-payment map, the
  occurrence-indexed payment trace, or the computed residue.  It is public
  evidence, not part of the stable import graph.

  Scope.  This is a one-crossing corpus application.  Its payment occurrence
  index is relative to the submitted wallet.  It gives no persistent serial,
  plan search, rich meaning to `checkTrace = none`, or transition/debt claim.
-/

import LeanProofs.Witnessed.LaunderingCorpus
import LeanProofs.Witnessed.PaidRecomposition.Catalog

namespace LeanProofs.Witnessed.PaidRecomposition.Applications.ResourceTraceOneCrossing

open LeanProofs.Witnessed.ResourceSequent
open LeanProofs.Witnessed.ResourceChecker
open LeanProofs.Witnessed.ResourceCheckerExec
open LeanProofs.Witnessed.LaunderingCorpus
open LeanProofs.Witnessed.PaidRecomposition.Payment
open LeanProofs.Witnessed.PaidRecomposition.Catalog

/-! ## Application-local executable equality -/

/-- Constructive structural equality for the resident `Nat` resource formulas
    used as this application's payment tokens.  It remains local to the
    application; the public resource syntax itself requires no decidable
    equality. -/
private def resourceFormulaDecidableEq :
    DecidableEq (ResourceFormula Nat Nat) := by
  intro left right
  cases left <;> cases right
  case claim.claim leftClaim rightClaim =>
    exact decidable_of_iff (leftClaim = rightClaim) (by
      constructor <;> intro equality <;> cases equality <;> rfl)
  case claim.bridge => exact isFalse (by intro equality; cases equality)
  case claim.residue => exact isFalse (by intro equality; cases equality)
  case bridge.claim => exact isFalse (by intro equality; cases equality)
  case bridge.bridge leftSource leftTarget rightSource rightTarget =>
    exact decidable_of_iff
      (leftSource = rightSource ∧ leftTarget = rightTarget) (by
        constructor
        · rintro ⟨rfl, rfl⟩
          rfl
        · intro equality
          cases equality
          exact ⟨rfl, rfl⟩)
  case bridge.residue => exact isFalse (by intro equality; cases equality)
  case residue.claim => exact isFalse (by intro equality; cases equality)
  case residue.bridge => exact isFalse (by intro equality; cases equality)
  case residue.residue leftResidue rightResidue =>
    exact decidable_of_iff (leftResidue = rightResidue) (by
      constructor <;> intro equality <;> cases equality <;> rfl)

local instance applicationResourceFormulaDecidableEq :
    DecidableEq (ResourceFormula Nat Nat) :=
  resourceFormulaDecidableEq

local instance applicationResourceFormulaReflBEq :
    ReflBEq (ResourceFormula Nat Nat) where
  rfl := by simp

local instance applicationResourceFormulaLawfulBEq :
    LawfulBEq (ResourceFormula Nat Nat) where
  eq_of_beq := by
    intro left right equal
    exact of_decide_eq_true equal

/-! ## The resident submitted trace and receipt -/

/-- The public corpus context: a local claim and the one bridge occurrence it
    may spend. -/
def input : Context Nat Nat :=
  [ResourceFormula.claim 1, ResourceFormula.bridge 1 2]

/-- The public corpus trace, named here only so it can be retained as the exact
    catalogued attempt. -/
def submitted : Trace Nat :=
  { base := BaseStep.hypStep 1 0
    bridges := [{ target := 2, index := 0 }] }

/-- Read the initial claim directly from the resident trace syntax. -/
def originOf (attempt : Trace Nat) : Nat :=
  match attempt.base with
  | .floorStep claim => claim
  | .hypStep claim _ => claim

/-- Follow the resident bridge-step targets to the submitted trace's endpoint. -/
private def finalTarget : Nat -> List (BridgeStep Nat) -> Nat
  | running, [] => running
  | _, step :: rest => finalTarget step.target rest

/-- The endpoint computed from the resident submitted trace. -/
def targetOf (attempt : Trace Nat) : Nat :=
  finalTarget (originOf attempt) attempt.bridges

/-- The bridge resource expected from an attempt is computed from the endpoints
    of that same resident trace. -/
def expectedOf (attempt : Trace Nat) : ResourceFormula Nat Nat :=
  ResourceFormula.bridge (originOf attempt) (targetOf attempt)

/-- The native positive receipt family is exactly the resident executable
    checker's accepted-result equation.  No replacement receipt record is
    introduced. -/
def NativePositive (attempt : Trace Nat) : Prop :=
  checkTrace kbNone bbA input attempt = some (2, [])

/-- This application admits the named public-corpus submission.  Admission is
    distinct from, and accompanied by, its native checker receipt. -/
def topology (attempt : Trace Nat) : Prop :=
  attempt = submitted

/-- The existing public corpus theorem supplies the native positive receipt. -/
theorem submitted_accepted : NativePositive submitted := by
  simpa [NativePositive, input, submitted] using valid_crossing_accepted

/-- The retained native receipt reconstructs the resident position-pinned
    resource judgment. -/
theorem submitted_checks :
    Checks (fun claim => kbNone claim = true)
      (fun source target => bbA source target = true)
      input 2 [] :=
  checkTrace_sound (fun _ _ accepted => accepted) submitted_accepted

/-- The resident checker judgment in turn reconstructs the public resource
    derivation. -/
theorem submitted_derives :
    Derives (fun claim => kbNone claim = true)
      (fun source target => bbA source target = true)
      input 2 [] :=
  checks_sound submitted_checks

/-! ## Occurrence-exact payment -/

/-- The ordered obligation submitted to the generic payment core. -/
def owed : List Nat := [1]

/-- The payment wallet after the resident trace's local-claim base step. -/
def available : Context Nat Nat := [ResourceFormula.bridge 1 2]

/-- The exact expected-payment map used by the plan and its payment trace. -/
def expected : Nat -> ResourceFormula Nat Nat :=
  fun _ => ResourceFormula.bridge 1 2

/-- The generic payment trace removes occurrence zero from the current wallet
    and computes the empty residue. -/
def payment : PaymentTrace expected owed available [] :=
  .cons 1 0 rfl rfl (.nil [])

/-- The executable generic payment checker accepts the same submitted order
    and wallet; completeness does not replace the trace or postulate a plan. -/
theorem payment_checker_accepts :
    ∃ accepted, checkPayment expected owed available = .inl accepted :=
  (checkPayment_accepts_iff
    (expected := expected) (owed := owed) (wallet := available)).2
      ⟨⟨[], payment⟩⟩

/-- The resident bridge validator exposes the same exact removal equation used
    by the generic payment trace on its intermediate resource context. -/
theorem resident_bridge_occurrence :
    bbA 1 2 = true ∧
      removeAt available 0 = some (expected 1, []) := by
  have checked :
      checkBridge bbA
        ((1, [ResourceFormula.bridge 1 2]) : Nat × Context Nat Nat)
        { target := 2, index := 0 } = some (2, []) := rfl
  obtain ⟨allowed, _targetEq, removed⟩ := checkBridge_sound checked
  exact ⟨by simpa using allowed, by simpa [available, expected] using removed⟩

/-! ## Exact global/catalog plans -/

/-- The one-attempt catalog used by the application. -/
def catalog : List (Trace Nat) := [submitted]

/-- The admitted global edge carries the native resident checker equation. -/
def globalEdge :
    PaidGlobalEdge originOf targetOf NativePositive topology 1 2 where
  attempt := submitted
  receipt := submitted_accepted
  origin_eq := rfl
  target_eq := rfl
  topologyAccepted := rfl

/-- A global paid plan whose receipt is the resident checker equation and whose
    payment is the generic occurrence-indexed trace above. -/
def globalPlan :
    PaidGlobalPlan originOf targetOf expectedOf NativePositive topology
      owed available where
  assign := fun _ => 2
  certified := by
    intro origin member
    have originEq : origin = 1 := by
      simpa [owed] using member
    subst originEq
    exact globalEdge
  injectiveOn := by
    intro left leftMember right rightMember _
    have leftEq : left = 1 := by
      simpa [owed] using leftMember
    have rightEq : right = 1 := by
      simpa [owed] using rightMember
    exact leftEq.trans rightEq.symm
  expected := expected
  expected_eq := by
    intro origin member
    have originEq : origin = 1 := by
      simpa [owed] using member
    subst originEq
    rfl
  residue := []
  payment := payment

/-- Exact attempt-level completeness for the named one-attempt corpus catalog. -/
theorem exact_complete :
    ExactPaidCatalogComplete NativePositive topology catalog := by
  intro attempt admitted _receipt
  subst admitted
  exact List.Mem.head []

/-- Add exact catalog membership without reconstructing the global plan. -/
def catalogPlan :
    PaidCatalogPlan originOf targetOf expectedOf NativePositive topology
      catalog owed available :=
  globalPlan.toCatalog exact_complete

/-- The application instantiates the unconditional catalog-to-global
    conversion as well as the completeness-dependent direction. -/
def recoveredGlobalPlan :
    PaidGlobalPlan originOf targetOf expectedOf NativePositive topology
      owed available :=
  catalogPlan.toGlobal

/-- The application supplies both sides of the generic adequacy theorem. -/
theorem application_exact_adequacy :
    Nonempty
        (PaidCatalogPlan originOf targetOf expectedOf NativePositive topology
          catalog owed available) ↔
      Nonempty
        (PaidGlobalPlan originOf targetOf expectedOf NativePositive topology
          owed available) :=
  exact_catalog_adequate exact_complete

/-- The entire global plan survives the roundtrip definitionally. -/
theorem recovered_global_plan_is_original :
    recoveredGlobalPlan = globalPlan := rfl

/-- Canonical membership of the application's sole submitted obligation. -/
private theorem one_mem_owed : (1 : Nat) ∈ owed := by
  simp [owed]

/-- The dependent native checker receipt is the same field before and after
    catalog conversion; no private receipt is manufactured. -/
theorem native_receipt_preserved :
    (catalogPlan.global.certified 1 one_mem_owed).receipt =
      (globalPlan.certified 1 one_mem_owed).receipt := rfl

/-- The exact expected-payment map is retained definitionally. -/
theorem expected_map_preserved :
    catalogPlan.global.expected = globalPlan.expected := rfl

/-- The occurrence-indexed payment witness is retained definitionally. -/
theorem payment_trace_preserved :
    catalogPlan.global.payment = globalPlan.payment := rfl

/-- The checker-computed payment residue is retained definitionally. -/
theorem computed_residue_preserved :
    catalogPlan.global.residue = globalPlan.residue := rfl

/-- The retained receipt still reconstructs the resident checker judgment
    after catalog conversion. -/
theorem catalog_receipt_reconstructs_checks :
    Checks (fun claim => kbNone claim = true)
      (fun source target => bbA source target = true)
      input 2 [] :=
  checkTrace_sound (fun _ _ accepted => accepted)
    (catalogPlan.global.certified 1 one_mem_owed).receipt

end LeanProofs.Witnessed.PaidRecomposition.Applications.ResourceTraceOneCrossing
