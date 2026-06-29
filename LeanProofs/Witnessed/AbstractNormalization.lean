/-
  LeanProofs.Witnessed.AbstractNormalization — the normalization theorem lifted OFF the
  freshness model. This is the WDC 2.0 structural strengthening: the normal-form
  factorization holds for ANY two-family paid-bridge system satisfying a local commutation
  law, not just the freshness model `(Nat, <, b−a)`.

  Custody class: PROMOTED WDC 2.0 receipt. Imports only the spine (`NoFreeLift`, for
  `PaidFrom`). Imported by the Witnessed aggregator and footprint-attested
  (`scripts/check-witnessed-footprint.sh`). The shipped
  `Normalization.bridge_path_normal_form` is the freshness INSTANCE of
  `normal_form_iff_of_commutes` (see that file).

  The move (per the corrected plan): the existing `bridge_path_normal_form` proof is a
  finite-path bubble-sort driven entirely by the local permutation law
  `weaken ; carry ⟹ carry ; weaken` (`perm_weaken_carry`) — NOT by a well-founded measure.
  So the abstraction is just that commutation law over abstract `Carry`/`Weaken`:

      Commutes C W := ∀ {a b c}, W a b → C b c → ∃ d, C a d ∧ W d c

  and the freshness theorem becomes the instance where `perm_weaken_carry` discharges it.

  No axioms (structural induction only). No new constructor on the judgment.
-/

import LeanProofs.Witnessed.NoFreeLift

namespace LeanProofs.Witnessed.AbstractNormalization

open LeanProofs.Witnessed.NoFreeLift

variable {α : Type}

/-
  Why `Chain` and not just `PaidFrom`? `PaidFrom` is the exported paid-path judgment, with
  steps appended at the TAIL. `Chain` is a local single-family closure with FRONT-cons
  structure, used so the normalization proof can induct over homogeneous carry/weaken
  segments and bubble one carry leftward through a weaken chain. It is proof plumbing
  (induction direction), not a second authority judgment.
-/
/-- A single-family chain (reflexive-transitive, cons at front). -/
inductive Chain (R : α → α → Prop) : α → α → Prop
  | nil  {a} : Chain R a a
  | cons {a b c} : R a b → Chain R b c → Chain R a c

/-- A paid step is carry OR weaken — the two-family bridge relation, abstractly. -/
abbrev Step (C W : α → α → Prop) : α → α → Prop := fun a b => C a b ∨ W a b

/-- The local commutation law: a weaken followed by a carry can be reordered to a carry
    followed by a weaken (same endpoints). The whole abstraction rides on this. -/
def Commutes (C W : α → α → Prop) : Prop :=
  ∀ {a b c}, W a b → C b c → ∃ d, C a d ∧ W d c

/-! ## Chain plumbing -/

/-- Append a step at the end of a chain. -/
theorem Chain_snoc {R : α → α → Prop} {a m m' : α} (h : Chain R a m) : R m m' → Chain R a m' := by
  induction h with
  | nil => intro s; exact Chain.cons s Chain.nil
  | cons hs _ ih => intro s; exact Chain.cons hs (ih s)

/-! ## PaidFrom plumbing (front-cons + transitivity, derived from the tail-step judgment) -/

theorem PaidFrom_cons {B : α → α → Prop} {a b c : α} (s : B a b) (p : PaidFrom B b c) :
    PaidFrom B a c := by
  induction p with
  | refl => exact PaidFrom.step PaidFrom.refl s
  | step _ s' ih => exact PaidFrom.step ih s'

theorem PaidFrom_trans {B : α → α → Prop} {a b c : α} (p : PaidFrom B a b) (q : PaidFrom B b c) :
    PaidFrom B a c := by
  induction q with
  | refl => exact p
  | step _ s ih => exact PaidFrom.step ih s

/-! ## The hinge — bubble one carry to the front of a weaken chain (uses Commutes) -/

theorem bubble {C W : α → α → Prop} (hcomm : Commutes C W) {m g : α} (hw : Chain W m g) :
    ∀ {h}, C g h → ∃ m', C m m' ∧ Chain W m' h := by
  induction hw with
  | nil => intro h hc; exact ⟨h, hc, Chain.nil⟩
  | @cons a b c hws _ ih =>
      intro h hc
      obtain ⟨k', hck, hwk⟩ := ih hc
      obtain ⟨m', hcm, hpm⟩ := hcomm hws hck
      exact ⟨m', hcm, Chain.cons hpm hwk⟩

/-! ## Forward: every paid path factors as a carry segment then a weaken segment -/

theorem normalize {C W : α → α → Prop} (hcomm : Commutes C W) {a c : α}
    (p : PaidFrom (Step C W) a c) : ∃ z, Chain C a z ∧ Chain W z c := by
  induction p with
  | refl => exact ⟨a, Chain.nil, Chain.nil⟩
  | step _ hstep ih =>
      obtain ⟨m, hcm, hwm⟩ := ih
      rcases hstep with hc | hw
      · obtain ⟨m', hcm', hwm'⟩ := bubble hcomm hwm hc
        exact ⟨m', Chain_snoc hcm hcm', hwm'⟩
      · exact ⟨m, hcm, Chain_snoc hwm hw⟩

/-! ## Reverse: a factored pair inhabits the paid path (no lossy summary) -/

theorem chainC_to_paid {C W : α → α → Prop} {a z : α} (h : Chain C a z) :
    PaidFrom (Step C W) a z := by
  induction h with
  | nil => exact PaidFrom.refl
  | cons hs _ ih => exact PaidFrom_cons (Or.inl hs) ih

theorem chainW_to_paid {C W : α → α → Prop} {z c : α} (h : Chain W z c) :
    PaidFrom (Step C W) z c := by
  induction h with
  | nil => exact PaidFrom.refl
  | cons hs _ ih => exact PaidFrom_cons (Or.inr hs) ih

/-- A carry-then-weaken factorization always inhabits the paid path. This direction is
    UNCONDITIONAL — it does NOT use the commutation law; only the forward/completeness
    direction (`normalize`) needs `Commutes`. (Kept separate so the dependency bill is
    explicit per-direction, matching the repo's footprint discipline.) -/
theorem factored_to_paid {C W : α → α → Prop} {a c : α}
    (h : ∃ z, Chain C a z ∧ Chain W z c) : PaidFrom (Step C W) a c := by
  obtain ⟨z, hc, hw⟩ := h
  exact PaidFrom_trans (chainC_to_paid hc) (chainW_to_paid hw)

/-! ## The capstone — both halves, abstract, no model, no axiom -/

/-- **normal_form_iff_of_commutes** — the WDC 2.0 theorem. For any two-family paid bridge
    `Step C W` whose families satisfy the local commutation law, a paid path admits a
    NORMAL-FORM FACTORIZATION as a carry segment followed by a weaken segment (existence of
    the split, not a unique canonical representative), and every such factored pair is itself
    a paid path. Only the forward (`.mp`) direction is conditional on `Commutes`; the reverse
    is `factored_to_paid` (unconditional). The freshness `bridge_path_normal_form` is the
    instance `C := CarryStep`, `W := WeakenStep`, `hcomm := perm_weaken_carry`. -/
theorem normal_form_iff_of_commutes {C W : α → α → Prop} (hcomm : Commutes C W) {a c : α} :
    PaidFrom (Step C W) a c ↔ ∃ z, Chain C a z ∧ Chain W z c := by
  constructor
  · exact normalize hcomm
  · exact factored_to_paid

end LeanProofs.Witnessed.AbstractNormalization
