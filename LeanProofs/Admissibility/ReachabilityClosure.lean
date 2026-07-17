/-
  LeanProofs.Admissibility.ReachabilityClosure — reachability/refusal hygiene slice.

  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE

  Status: terminal public evidence, deliberately outside the exact
  `AdmissibilityKernels` compatibility surface and distinct from the retired
  composition classifier.

  Purpose (the guardrail, not the prize): pin one honest meaning of "composable" /
  "refused" over a declared step relation, BEFORE any abstract normalization builds on
  the word. `Composable = reachable under declared steps`; `Refused = not reachable`.
  NOT "semantically false", NOT "malformed", NOT "redundant".

  Explicitly NOT a revival of `composition_classification` (retired: `naive_exclusivity_fails`,
  per experiments/no_free_lift_wiring/COMPOSITION-CLASSIFICATION-TARGET.md). No classifier,
  no trichotomy, no exclusivity claim. Just the reachability vocabulary and its closure.

  The key refinement after v2.0.0: bare refusal is just a negation. A useful refusal can
  carry a closed-lane witness: a forward-closed set containing the source and excluding the
  destination. This is the Prop-valued, spine-independent version of the `TaxonomyGraph`
  `no_reach_of_closed_lane` receipt.

  Self-contained (no imports). Deliberately independent of the Witnessed spine so a static
  reachability claim here cannot inherit any dynamic/documentary axiom from elsewhere
  (e.g. TaxonomyGraph's former `persistence_normalizes`). WDC-specific adapters live in
  `LeanProofs.Admissibility.WitnessedReachability`.
-/

namespace LeanProofs.Admissibility.ReachabilityClosure

variable {α : Type}

/-- Reflexive-transitive closure of a one-step relation (step at the tail). -/
inductive Reach (Step : α → α → Prop) : α → α → Prop
  | refl {a} : Reach Step a a
  | tail {a b c} : Reach Step a b → Step b c → Reach Step a c

/-- Composable = reachable under the declared paid steps. -/
def Composable (Step : α → α → Prop) (a b : α) : Prop := Reach Step a b

/-- Refused = NOT reachable under the declared paid steps. Not falsity, not malformation. -/
def Refused (Step : α → α → Prop) (a b : α) : Prop := ¬ Reach Step a b

theorem composable_refl (Step : α → α → Prop) (a : α) : Composable Step a a := Reach.refl

theorem step_composable {Step : α → α → Prop} {a b : α} (h : Step a b) : Composable Step a b :=
  Reach.tail Reach.refl h

/-- Reachability composes — the only structural law this slice asserts. -/
theorem composable_trans {Step : α → α → Prop} {a b c : α}
    (hab : Composable Step a b) (hbc : Composable Step b c) : Composable Step a c := by
  induction hbc with
  | refl => exact hab
  | tail _ hstep ih => exact Reach.tail ih hstep

/-- Refusal is exactly the negation — no hidden classifier content. -/
theorem refused_iff_not_composable {Step : α → α → Prop} {a b : α} :
    Refused Step a b ↔ ¬ Composable Step a b := Iff.rfl

/-! ## Closed-lane witnesses -/

/-- A lane is forward-closed under a step relation when every declared step out of the lane
    stays in the lane. -/
def ClosedUnder (Step : α → α → Prop) (S : α → Prop) : Prop :=
  ∀ {a b}, S a → Step a b → S b

/-- Reachability preserves membership in a forward-closed lane. -/
theorem reach_stays_in_closed {Step : α → α → Prop} {S : α → Prop}
    (h_closed : ClosedUnder Step S)
    {a b : α} (h : Reach Step a b) (ha : S a) : S b := by
  induction h with
  | refl => exact ha
  | tail _ hstep ih => exact h_closed ih hstep

/-- **no_reach_of_closed_lane** — Prop-valued closed-lane obstruction. If `src` is inside a
    forward-closed lane `S` and `dst` is outside it, no declared-step path reaches `dst`
    from `src`. This turns non-reachability from a bare absence into a witnessed refusal. -/
theorem no_reach_of_closed_lane {Step : α → α → Prop} {S : α → Prop} {src dst : α}
    (h_closed : ClosedUnder Step S) (h_src : S src) (h_dst : ¬ S dst) :
    ¬ Reach Step src dst := by
  intro h
  exact h_dst (reach_stays_in_closed (Step := Step) (S := S) h_closed h h_src)

/-- A closed-lane refusal carries the obstruction witness for a refused pair. -/
structure ClosedLaneRefusal (Step : α → α → Prop) (src dst : α) : Type where
  lane : α → Prop
  closed : ClosedUnder Step lane
  src_mem : lane src
  dst_not_mem : ¬ lane dst

/-- A witnessed refusal is a closed-lane refusal: source inside, destination outside, lane
    closed under every declared step. -/
abbrev WitnessedRefusal (Step : α → α → Prop) (src dst : α) : Type :=
  ClosedLaneRefusal Step src dst

/-- The closed-lane witness implies ordinary refusal. -/
theorem ClosedLaneRefusal.refused {Step : α → α → Prop} {src dst : α}
    (h : ClosedLaneRefusal Step src dst) : Refused Step src dst :=
  no_reach_of_closed_lane (Step := Step) (S := h.lane) h.closed h.src_mem h.dst_not_mem

/-- Named projection for callers that do not want to use the structure method syntax. -/
theorem witnessed_refusal_sound {Step : α → α → Prop} {src dst : α}
    (h : WitnessedRefusal Step src dst) : Refused Step src dst :=
  h.refused

end LeanProofs.Admissibility.ReachabilityClosure
