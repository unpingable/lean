/-
  Custody-Class: SCRATCH

  BestEffortCompleteness — fenced scratch slice, 2026-06-15. Not imported by
  `LeanProofs.lean`. Not part of any 1.0 surface. No paper anchor. No
  promotion path. NOT used as discharge for any doctrine. Compile-is-contact
  only. Informs the loop/governor doctrine; blesses nothing.

  ## The specimen sentence

      Completeness requires satisfied closure under a basis licensed for the
      specific obligation kind. Terminal accounting is not discharge;
      satisfaction without a kind-matched basis is not discharge; no actor
      rank universally converts one justification type into another.

  Equivalently, the hinge the loop/governor doctrine needs:

      Best effort is admissible only as bounded operational traversal; it has
      no authority to convert open required discharge into completeness.

  ## Provenance — three rounds, the bug relocated twice

  A draft of this annex was reviewed adversarially across three rounds, and
  the same silent-conversion sin (the NQ sin: a terminal/forged state
  rendering as `ok`) relocated one rung up the provenance ladder each time:

    1. `closed := ∃ c, closes o = some c` counted ANY closure as discharge,
       so `exhausted` sailed through as complete. Bulk-realism in a helper.
    2. Fixed to `discharged := closes o = some satisfied`, the bug moved: any
       `satisfied` stamp discharged, provenance-blind. System could forge.
    3. Fixed to require an `operator` issuer, the bug moved again: `operator`
       became a universal solvent — it discharged an evidentiary gap with no
       evidence, a custodial gap with no custody. `chmod 777` for governance.

  The tell: the *structure* was wrong, not the predicate. A ladder always has
  a top, and the top is always the next 777. The fix is not ranking issuers
  (system < operator < root) but TYPING the justification: a `Basis` matched
  to the obligation `kind`, with NO conversion across justification types
  (authority ≠ evidence ≠ custody). That is "signed is not witnessed" and
  No-Silent-Conversion enforced at the discharge predicate.

  ## What is modeled

    - `GapKind`   — the five obligation kinds (each is load-bearing: each is
      licensed by exactly one `Basis`; see `licenses_unique`).
    - `Closure`   — five terminal closures; only `satisfied` can discharge.
    - `Basis`     — typed justification (the issuer's WARRANT, not its rank).
    - `licenses`  — a DIAGONAL match of basis→kind, not a partial order.
    - `discharged`— satisfied closure under a kind-matched basis.
    - `complete`  — every required obligation discharged.

  ## What is proved (denote-and-refute, not exile-and-congratulate)

    - `licenses_unique` — AT MOST ONE basis licenses any gap kind. The formal
      anti-rank statement: no second basis (no higher rank) sneaks into a
      kind it does not warrant.
    - `unlicensed_for_kind_is_not_discharge` — THE HINGE. A stamp whose basis
      does not license the obligation's kind does not discharge it.
    - `complete_is_achievable` / `good_custody_discharges` — THE ANTI-VACUITY
      GUARD. A kind-matched satisfied stamp DOES discharge and DOES complete.
      Without this, the negative family below could be passing vacuously
      (an always-false `discharged` proves every "not discharged" for free).
    - specimens: forged stamps that are denotable, inspectable, and refused —
      `semantic_satisfaction_on_custodial_gap`,
      `evidence_witness_..._authority`, `authority_ratification_..._evidentiary`,
      `custody_receipt_..._semantic`, `system_execution_..._authority`.
    - `exhaustion_is_closed_but_not_discharged` — wall one: best-effort
      residue (exhausted) closes the record without completing the claim.
    - `system_execution_cannot_complete_authority_requirement` — the headline,
      connected THROUGH `complete` (not through a grammar restriction):
      automatic best effort cannot complete an authority-required obligation.
    - `auto_step_cannot_discharge_authority` — the traversal asymmetry,
      located correctly. `AutoStep` is left UNGATED (it can stamp any
      obligation) precisely to show the wall lives in `discharged`, not in the
      step grammar: even an authority-targeting auto-step cannot discharge,
      because `systemExecution` does not license `authority`.

  ## Architecture note — why discharge, not AutoStep

  An earlier sketch put the authority wall in `AutoStep` (a step grammar that
  could not be CONSTRUCTED across an authority gap). That is exile, and it is
  strictly weaker: `complete` never mentioned `AutoStep`, so the forbidden
  state was reachable by stamping `satisfied` directly. The load belongs in
  `discharged` — the refutation layer — where a bad record may EXIST yet
  cannot support the clean claim. `AutoStep` survives here only as a
  secondary process observation (automatic execution mints only
  `systemExecution`), not as the anti-laundering wall.

  ## Refused theorems (explicit non-claims)

    1. Not a model of "best effort" itself (that is vibes-with-constructors).
       Only the WALL is formalized: which closures/bases discharge which kinds.
    2. Not a claim that the loop/governor runtime is correct or complete.
    3. The basis→kind diagonal is a stipulation of THIS specimen, not a
       discovered ontology; the point is the SHAPE (typed, non-interconverting),
       not the particular five rows.

  ## Prior art (read-only, not imported, no correspondence claim)
    - LeanProofs/Scratch/OperatorBasisGateInput.lean  (typed binding > detached bit; same "type not rank" move on a gate input)
    - LeanProofs/Scratch/NoUniversalRoot.lean         (no universal root; the rank-has-a-top intuition, observer axis)
    - LeanProofs/Admissibility/AmendmentFragment.lean (the denote-and-refute lineage: bad state representable, claim refused)
-/

namespace Admissibility.Scratch.BestEffortCompleteness

/-! ## Vocabulary -/

/-- The kind of an obligation — what kind of gap it leaves open. -/
inductive GapKind where
  | operational
  | semantic
  | evidentiary
  | custodial
  | authority
  deriving DecidableEq, Repr

/-- Terminal closures. All five close the accounting record; only `satisfied`
    can discharge a requirement. The other four are best-effort residue. -/
inductive Closure where
  | satisfied
  | refused
  | quarantined
  | exhausted
  | escalated
  deriving DecidableEq, Repr

/-- The BASIS of a closure — the typed justification behind it. This is the
    issuer's warrant, not the issuer's rank: there is no order on `Basis`. -/
inductive Basis where
  | systemExecution
  | semanticRuling
  | evidenceWitness
  | custodyReceipt
  | authorityRatification
  deriving DecidableEq, Repr

structure Obligation where
  name : Nat
  kind : GapKind
  deriving DecidableEq, Repr

/-- A closure stamp: what closed it, and on what basis. -/
structure Stamp where
  closure : Closure
  basis : Basis
  deriving DecidableEq, Repr

/-- An accounting assigns at most one stamp to each obligation. -/
structure Accounting where
  closes : Obligation → Option Stamp

/-! ## The licensing diagonal — typed, not ranked -/

/-- Which basis licenses which gap kind. A DIAGONAL: each basis warrants
    exactly the one kind it is the justification for. The catch-all `false`
    is the No-Silent-Conversion clause — no basis interconverts to a kind it
    does not warrant, and there is no universal/top basis. -/
def licensesB : Basis → GapKind → Bool
  | .systemExecution,       .operational  => true
  | .semanticRuling,        .semantic     => true
  | .evidenceWitness,       .evidentiary  => true
  | .custodyReceipt,        .custodial    => true
  | .authorityRatification, .authority    => true
  | _, _                                  => false

/-- Propositional form of the licensing relation. -/
def licenses (b : Basis) (k : GapKind) : Prop := licensesB b k = true

instance (b : Basis) (k : GapKind) : Decidable (licenses b k) := by
  unfold licenses; infer_instance

/-! ## Closure / discharge / completeness -/

/-- The record was closed (any stamp). NOT discharge — this is exactly the
    helper that laundered round one. -/
def closed (a : Accounting) (o : Obligation) : Prop :=
  ∃ s, a.closes o = some s

/-- An obligation is DISCHARGED iff it carries a `satisfied` stamp whose basis
    licenses its kind. Three conjuncts, each a wall a previous round lacked:
    a stamp exists; it is `satisfied` (not residue); its basis is kind-matched
    (not a forged or universal warrant). -/
def discharged (a : Accounting) (o : Obligation) : Prop :=
  ∃ s, a.closes o = some s ∧ s.closure = Closure.satisfied ∧ licenses s.basis o.kind

/-- Completeness: every required obligation is discharged. -/
def complete (reqs : Obligation → Prop) (a : Accounting) : Prop :=
  ∀ o, reqs o → discharged a o

/-- The four authority-bearing gap kinds — best effort may not traverse these
    automatically. (`operational` is the only kind it may.) -/
def authorityGap (o : Obligation) : Prop :=
  o.kind = GapKind.semantic ∨
  o.kind = GapKind.evidentiary ∨
  o.kind = GapKind.custodial ∨
  o.kind = GapKind.authority

/-! ## Anti-rank: at most one basis licenses any kind -/

/-- The formal "type the authority, don't rank it" theorem: no two distinct
    bases license the same gap kind. There is no higher rank that also
    discharges a lower kind — the diagonal is injective in the basis. -/
theorem licenses_unique {b₁ b₂ : Basis} {k : GapKind}
    (h₁ : licenses b₁ k) (h₂ : licenses b₂ k) : b₁ = b₂ := by
  cases k <;> cases b₁ <;> cases b₂ <;> simp_all [licenses, licensesB]

/-- Specialization at the top kind: ONLY authority ratification licenses an
    authority gap. No system/operator/evidence rank climbs into it. -/
theorem only_ratification_licenses_authority {b : Basis}
    (h : licenses b GapKind.authority) : b = Basis.authorityRatification := by
  cases b <;> simp_all [licenses, licensesB]

/-! ## A helper accounting that stamps one target -/

/-- An accounting that stamps exactly `target` with `s`, nothing else. -/
def stamped (target : Obligation) (s : Stamp) : Accounting :=
  { closes := fun o => if o = target then some s else none }

@[simp] theorem stamped_closes (target : Obligation) (s : Stamp) :
    (stamped target s).closes target = some s := by
  simp [stamped]

/-! ## THE HINGE -/

/-- A stamp whose basis does not license the obligation's kind does not
    discharge it — no matter the closure. Everything below is downstream. -/
theorem unlicensed_for_kind_is_not_discharge
    {a : Accounting} {o : Obligation} {s : Stamp}
    (hclose : a.closes o = some s)
    (hunlic : ¬ licenses s.basis o.kind) :
    ¬ discharged a o := by
  rintro ⟨s', hclose', _hsat, hlic⟩
  rw [hclose] at hclose'
  injection hclose' with hss
  subst hss
  exact hunlic hlic

/-! ## ANTI-VACUITY GUARD — a licensed discharge that actually fires

  Without this, the negative family could be true vacuously: an always-false
  `discharged` proves every "not discharged" for free, and the file would be
  green while proving nothing. This freshness check shows `discharged` and
  `complete` are inhabited. -/

/-- A kind-matched satisfied stamp DOES discharge. -/
theorem licensed_satisfaction_discharges
    {a : Accounting} {o : Obligation} {s : Stamp}
    (hclose : a.closes o = some s)
    (hsat : s.closure = Closure.satisfied)
    (hlic : licenses s.basis o.kind) :
    discharged a o :=
  ⟨s, hclose, hsat, hlic⟩

/-- A custodial obligation honestly discharged by a custody receipt. -/
def custodialObl : Obligation := { name := 0, kind := GapKind.custodial }
def goodCustodyStamp : Stamp := { closure := Closure.satisfied, basis := Basis.custodyReceipt }

theorem good_custody_discharges :
    discharged (stamped custodialObl goodCustodyStamp) custodialObl :=
  licensed_satisfaction_discharges (stamped_closes _ _) rfl (by decide)

/-- Completeness is achievable: a single required custodial obligation,
    honestly discharged, satisfies `complete`. -/
theorem complete_is_achievable :
    complete (fun o => o = custodialObl) (stamped custodialObl goodCustodyStamp) := by
  intro o ho; subst ho; exact good_custody_discharges

/-! ## SPECIMENS — forged stamps, denotable and refused

  Each is a `satisfied` stamp under the WRONG basis for the gap kind. The bad
  record exists, can be inspected, and `discharged` refuses it. -/

/-- A semantic ruling does not discharge a custodial gap (a ruling is not a
    custody receipt). -/
theorem semantic_satisfaction_on_custodial_gap_not_discharged
    {o : Obligation} (hkind : o.kind = GapKind.custodial) :
    ¬ discharged (stamped o ⟨Closure.satisfied, Basis.semanticRuling⟩) o := by
  apply unlicensed_for_kind_is_not_discharge (stamped_closes o _)
  rw [hkind]; decide

/-- Evidence does not discharge an authority gap (a witness is not a
    ratification). -/
theorem evidence_witness_does_not_discharge_authority_gap
    {o : Obligation} (hkind : o.kind = GapKind.authority) :
    ¬ discharged (stamped o ⟨Closure.satisfied, Basis.evidenceWitness⟩) o := by
  apply unlicensed_for_kind_is_not_discharge (stamped_closes o _)
  rw [hkind]; decide

/-- Ratification does not discharge an evidentiary gap (authority is not
    evidence — the asymmetry runs both ways). -/
theorem authority_ratification_does_not_discharge_evidentiary_gap
    {o : Obligation} (hkind : o.kind = GapKind.evidentiary) :
    ¬ discharged (stamped o ⟨Closure.satisfied, Basis.authorityRatification⟩) o := by
  apply unlicensed_for_kind_is_not_discharge (stamped_closes o _)
  rw [hkind]; decide

/-- A custody receipt does not discharge a semantic gap. -/
theorem custody_receipt_does_not_discharge_semantic_gap
    {o : Obligation} (hkind : o.kind = GapKind.semantic) :
    ¬ discharged (stamped o ⟨Closure.satisfied, Basis.custodyReceipt⟩) o := by
  apply unlicensed_for_kind_is_not_discharge (stamped_closes o _)
  rw [hkind]; decide

/-- System execution does not discharge an authority gap — the original
    "system cannot forge operator-grade discharge" case, now stated in basis
    terms. -/
theorem system_execution_does_not_discharge_authority_gap
    {o : Obligation} (hkind : o.kind = GapKind.authority) :
    ¬ discharged (stamped o ⟨Closure.satisfied, Basis.systemExecution⟩) o := by
  apply unlicensed_for_kind_is_not_discharge (stamped_closes o _)
  rw [hkind]; decide

/-! ## WALL ONE — terminal residue closes without discharging -/

/-- Exhaustion (best-effort residue) closes the record yet does not discharge:
    the cheating accounting is denotable, you can ask `complete`, it says no. -/
theorem exhaustion_is_closed_but_not_discharged {o : Obligation} :
    closed (stamped o ⟨Closure.exhausted, Basis.systemExecution⟩) o ∧
    ¬ discharged (stamped o ⟨Closure.exhausted, Basis.systemExecution⟩) o := by
  refine ⟨⟨_, stamped_closes o _⟩, ?_⟩
  rintro ⟨s, hclose, hsat, _⟩
  rw [stamped_closes] at hclose
  injection hclose with hs
  subst hs
  simp at hsat

/-! ## THE HEADLINE — best effort cannot complete an authority requirement -/

/-- Connected THROUGH `complete`, not through a step grammar: if an
    authority-kind obligation is required and closed only by system execution,
    the accounting is not complete. Automatic best effort has no authority to
    complete an authority-bearing requirement. -/
theorem system_execution_cannot_complete_authority_requirement
    {reqs : Obligation → Prop} {a : Accounting} {o : Obligation} {s : Stamp}
    (hreq : reqs o) (hkind : o.kind = GapKind.authority)
    (hclose : a.closes o = some s) (hbasis : s.basis = Basis.systemExecution) :
    ¬ complete reqs a := by
  intro hcomplete
  have hnot : ¬ discharged a o := by
    apply unlicensed_for_kind_is_not_discharge hclose
    rw [hbasis, hkind]; decide
  exact hnot (hcomplete o hreq)

/-- An authority-gap obligation closed by system execution is never
    discharged — across all four authority-bearing kinds. -/
theorem system_execution_never_discharges_authority_gap
    {a : Accounting} {o : Obligation} {s : Stamp}
    (hgap : authorityGap o) (hclose : a.closes o = some s)
    (hbasis : s.basis = Basis.systemExecution) :
    ¬ discharged a o := by
  apply unlicensed_for_kind_is_not_discharge hclose
  rw [hbasis]
  rcases hgap with h | h | h | h <;> (rw [h]; decide)

/-! ## THE TRAVERSAL ASYMMETRY — located in `discharged`, not in the grammar -/

/-- Record a stamp at one target (used by the auto-step). -/
def Accounting.record (a : Accounting) (target : Obligation) (s : Stamp) : Accounting :=
  { closes := fun o => if o = target then some s else a.closes o }

@[simp] theorem record_closes (a : Accounting) (target : Obligation) (s : Stamp) :
    (a.record target s).closes target = some s := by
  simp [Accounting.record]

/-- Automatic execution. DELIBERATELY UNGATED on the obligation kind: it may
    stamp ANY obligation with any closure — but only ever on the
    `systemExecution` basis (it has no authority to mint another). Leaving it
    ungated is the point: the wall is not "you cannot build this step." -/
inductive AutoStep : Accounting → Obligation → Accounting → Prop where
  | stamp (a : Accounting) (o : Obligation) (c : Closure) :
      AutoStep a o (a.record o ⟨c, Basis.systemExecution⟩)

/-- Even an authority-targeting auto-step cannot discharge the authority gap:
    not because the step is unbuildable (it is buildable), but because
    `systemExecution` does not license `authority`. The wall is in
    `discharged`. -/
theorem auto_step_cannot_discharge_authority
    {a a' : Accounting} {o : Obligation}
    (hstep : AutoStep a o a') (hkind : o.kind = GapKind.authority) :
    ¬ discharged a' o := by
  cases hstep with
  | stamp c =>
    apply unlicensed_for_kind_is_not_discharge (record_closes a o _)
    rw [hkind]; simp [licenses, licensesB]

end Admissibility.Scratch.BestEffortCompleteness
