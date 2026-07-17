/-
  LeanProofs.Witnessed.PaidRecomposition.Applications.FiniteSupportOneCrossing
  -- terminal checker-integration evidence for occurrence-exact paid recomposition.

  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE

  Application custody. This module intentionally imports the stable
  `FiniteSupportChecker`; the integration itself is terminal public evidence,
  not part of PaidRecomposition's stable core. The source and resource sides retain the exact
  equations returned by the resident checkers.  The payment side uses the
  public occurrence-indexed `PaymentTrace` directly over the resident
  `ResourceFormula` context; no parallel token encoding is introduced.

  Scope.  The resource checker's `none` result is not interpreted here, and no
  refusal transition, refusal debt preservation, persistent token serial, plan
  search, PC-1, or PC-2 claim is made.  Only accepted-path obligation-residue
  preservation is stated.
-/

import LeanProofs.CustodyIndexed.FiniteSupportChecker
import LeanProofs.Witnessed.LaunderingCorpus
import LeanProofs.Witnessed.PaidRecomposition.Payment
import LeanProofs.BoundedCalculi.ObligationResidue

namespace LeanProofs.Witnessed.PaidRecomposition.Applications.FiniteSupportOneCrossing

open LeanProofs.CustodyIndexed.StructuralPolicySequent (PJ dupSystem linear)
open LeanProofs.CustodyIndexed.StructuralNormalization (Core)
open LeanProofs.CustodyIndexed.DerivationData (Deriv)
open LeanProofs.CustodyIndexed.LinearNormalization (LinResult emptyCalc dupTree dupTree₂)
open LeanProofs.CustodyIndexed.TracedCoherence (tagged)
open LeanProofs.CustodyIndexed.FiniteSupportChecker
open LeanProofs.BoundedCalculi.MeasureAccounting (wsum)
open LeanProofs.BoundedCalculi.ObligationResidue (obligation_residue_persists)
open LeanProofs.Witnessed.ResourceSequent
open LeanProofs.Witnessed.ResourceChecker
open LeanProofs.Witnessed.ResourceCheckerExec
open LeanProofs.Witnessed.LaunderingCorpus (kbNone bbA)
open LeanProofs.Witnessed.PaidRecomposition.Payment

/-! ## Native finite-support submissions -/

/-- The resident paid tree with the two distinct occurrences it consumes. -/
def paidSourceAttempt :
    Core dupSystem emptyCalc [PJ.res, PJ.res] PJ.out :=
  dupTree₂

/-- The exact supply submitted to the resident checker. -/
def paidSourceSupply : List PJ := [PJ.res, PJ.res]

/-- The exact positional trace returned by the resident checker. -/
def paidSourceTrace : List (Nat × PJ) :=
  [(0, PJ.res), (1, PJ.res)]

/-- The native accepted checker equation is retained unchanged. -/
theorem paid_source_native_accepted :
    paidSourceAttempt.checkCtx paidSourceSupply =
      .ok paidSourceTrace := by
  simpa [paidSourceAttempt, paidSourceSupply, paidSourceTrace] using
    paid_tree_checks_ok

/-- The accepted native equation reconstructs the normalized derivation, the
    exact read spine, and positional single-use testimony. -/
theorem paid_source_native_sound :
    (∃ (residual : List PJ)
        (derivation : Deriv dupSystem emptyCalc (linear PJ)
          paidSourceSupply PJ.out residual),
      paidSourceAttempt.linearize paidSourceSupply =
        LinResult.ok residual derivation) ∧
    paidSourceTrace.map Prod.snd = paidSourceAttempt.readsOf ∧
    (∀ occurrenceIndex : Nat,
      wsum (fun entry => if entry.1 = occurrenceIndex then 1 else 0)
        paidSourceTrace ≤ 1) :=
  checkCtx_ok_sound paid_source_native_accepted

/-- Every position in the accepted trace comes from the canonically tagged
    submitted supply, and its label occurs in that supply. -/
theorem paid_source_positional_provenance
    (entry : Nat × PJ) (member : entry ∈ paidSourceTrace) :
    entry ∈ tagged paidSourceSupply ∧ entry.2 ∈ paidSourceSupply :=
  checkCtx_trace_entries_from_context paid_source_native_accepted entry member

/-- The existing free-contraction tree submitted one occurrence short. -/
def deficientSourceAttempt : Core dupSystem emptyCalc [PJ.res] PJ.out :=
  dupTree

/-- The exact deficient supply submitted to the resident checker. -/
def deficientSourceSupply : List PJ := [PJ.res]

/-- The deficient submission produces the resident typed refusal, including
    its exact offender. -/
theorem deficient_source_native_refused :
    deficientSourceAttempt.checkCtx deficientSourceSupply =
      .refusal PJ.res := by
  simpa [deficientSourceAttempt, deficientSourceSupply] using
    free_contraction_checks_refused

/-- The resident refusal theorem gives the offender its native excess-demand
    meaning; no application-defined refusal semantics are substituted. -/
theorem deficient_source_native_excess :
    wsum (fun label => if label = PJ.res then 1 else 0)
        deficientSourceSupply <
      wsum (fun label => if label = PJ.res then 1 else 0)
        deficientSourceAttempt.readsOf :=
  checkCtx_refusal_excess deficient_source_native_refused

/-- The exact refused offender is also genuinely demanded by the submitted
    tree.  This is recovered from the resident tagged-check theorem. -/
theorem deficient_source_offender_demanded :
    PJ.res ∈ deficientSourceAttempt.readsOf := by
  have taggedRefusal :
      deficientSourceAttempt.check (tagged deficientSourceSupply) =
        .refusal PJ.res := by
    simpa only [Core.checkCtx] using deficient_source_native_refused
  exact check_refusal_offender_demanded taggedRefusal

/-! ## Native resource trace and accepted-path residue -/

/-- The actual resident resource context.  The local claim and bridge token
    are consumable; the obligation residue is not. -/
def resourceInput : Context Nat Nat :=
  [ResourceFormula.residue 0,
    ResourceFormula.claim 1,
    ResourceFormula.bridge 1 2]

/-- The exact context after the resident base step consumes `claim 1`. -/
def afterBase : Context Nat Nat :=
  [ResourceFormula.residue 0, ResourceFormula.bridge 1 2]

/-- The exact checker-computed resource residue. -/
def resourceResidue : Context Nat Nat :=
  [ResourceFormula.residue 0]

/-- One resident local read followed by one pinned crossing. -/
def submittedResourceTrace : Trace Nat where
  base := .hypStep 1 1
  bridges := [{ target := 2, index := 1 }]

/-- The native `ResourceCheckerExec` accepted equation is retained unchanged. -/
theorem resource_trace_native_accepted :
    checkTrace kbNone bbA resourceInput submittedResourceTrace =
      some (2, resourceResidue) := by
  rfl

/-- The base step's exact occurrence removal computes its intermediate
    context. -/
theorem resource_base_native_accepted :
    checkBase kbNone resourceInput (.hypStep 1 1) =
      some (1, afterBase) := by
  rfl

/-- The bridge step's exact occurrence removal computes the final residue. -/
theorem resource_bridge_native_accepted :
    checkBridge bbA (1, afterBase) { target := 2, index := 1 } =
      some (2, resourceResidue) := by
  rfl

/-- The native accepted equation reconstructs the resident occurrence-pinned
    resource judgment. -/
theorem resource_trace_native_checks :
    Checks (fun claim => kbNone claim = true)
      (fun source target => bbA source target = true)
      resourceInput 2 resourceResidue :=
  checkTrace_sound (fun _ _ accepted => accepted)
    resource_trace_native_accepted

/-- The resident checker judgment reconstructs the public resource
    derivation. -/
theorem resource_trace_native_derives :
    Derives (fun claim => kbNone claim = true)
      (fun source target => bbA source target = true)
      resourceInput 2 resourceResidue :=
  checks_sound resource_trace_native_checks

/-- The submitted bridge position is an exact context-relative occurrence,
    and removing it computes the same resource residue as the native checker. -/
theorem resource_bridge_exact_occurrence :
    removeAt afterBase 1 =
      some (ResourceFormula.bridge 1 2, resourceResidue) := by
  exact (checkBridge_sound resource_bridge_native_accepted).2.2

/-- Accepted execution preserves the outstanding obligation residue by the
    existing public residue theorem.  This is an accepted-path result only. -/
theorem accepted_path_obligation_residue_preserved :
    ResourceFormula.residue 0 ∈ resourceResidue := by
  apply obligation_residue_persists resource_trace_native_derives
  exact List.Mem.head _

/-! ## Generic occurrence-indexed payment -/

/-- Application-local structural equality for the resident resource formulas.
    It exists only to run the generic payment checker over the exact native
    context; it introduces no admission or custody semantics. -/
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

/-- The submitted crossing order. -/
def owed : List Nat := [1]

/-- The resident bridge resource expected for the named origin. -/
def expectedPayment : Nat → ResourceFormula Nat Nat :=
  fun _ => ResourceFormula.bridge 1 2

/-- The exact resident context exposed after the native local base step. -/
def available : Context Nat Nat := afterBase

/-- The payment core computes the identical residue as the native checker. -/
def paymentResidue : Context Nat Nat := resourceResidue

/-- The generic payment witness pins occurrence one in the current resident
    context.  Its `removeAt` equation is the same authoritative equation
    recovered from the native bridge checker. -/
def paymentTrace :
    PaymentTrace expectedPayment owed available paymentResidue :=
  .cons 1 1 (by decide) resource_bridge_exact_occurrence
    (.nil paymentResidue)

/-- The generic total checker accepts exactly because the occurrence-indexed
    witness exists. -/
theorem payment_checker_accepts :
    ∃ accepted,
      checkPayment expectedPayment owed available = .inl accepted :=
  (checkPayment_accepts_iff
    (expected := expectedPayment) (owed := owed) (wallet := available)).2
      ⟨⟨paymentResidue, paymentTrace⟩⟩

/-- The payment trace exposes its exact context-relative removal directly. -/
theorem payment_exact_occurrence :
    removeAt available 1 =
      some (ResourceFormula.bridge 1 2, paymentResidue) :=
  resource_bridge_exact_occurrence

/-- The payment core and native resource checker compute the same residue
    definitionally; no conversion or replacement witness intervenes. -/
theorem payment_residue_is_native_residue :
    paymentResidue = resourceResidue := rfl

/-- Payment accounting is inherited from the generic theorem family. -/
theorem payment_length_conservation :
    available.length = owed.length + paymentResidue.length :=
  paymentTrace.length_conservation

/-! ## Integrated one-crossing evidence -/

/-- The terminal-evidence integration uses the two unchanged resident checker equations
    and the generic payment witness.  Its resource residue is computed by the
    resident trace, and the outstanding obligation survives by proof rather
    than by a stored application field. -/
theorem finite_support_one_crossing_evidence :
    paidSourceAttempt.checkCtx paidSourceSupply =
        .ok paidSourceTrace ∧
    checkTrace kbNone bbA resourceInput submittedResourceTrace =
        some (2, resourceResidue) ∧
    Nonempty
      (PaymentTrace expectedPayment owed available paymentResidue) ∧
    removeAt afterBase 1 =
        some (ResourceFormula.bridge 1 2, resourceResidue) ∧
    ResourceFormula.residue 0 ∈ resourceResidue := by
  exact ⟨paid_source_native_accepted, resource_trace_native_accepted,
    ⟨paymentTrace⟩, payment_exact_occurrence,
    accepted_path_obligation_residue_preserved⟩

end LeanProofs.Witnessed.PaidRecomposition.Applications.FiniteSupportOneCrossing
