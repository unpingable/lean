/-
  LeanProofs.Admissibility.ReachabilityClosure — reachability/refusal hygiene slice.

  Custody class: CANDIDATE / de-risking slice. NOT imported by `LeanProofs.lean`, NOT
  wired, NOT the retired composition classifier. Compile-is-contact only.

  Purpose (the guardrail, not the prize): pin one honest meaning of "composable" /
  "refused" over a declared step relation, BEFORE any abstract normalization builds on
  the word. `Composable = reachable under declared steps`; `Refused = not reachable`.
  NOT "semantically false", NOT "malformed", NOT "redundant".

  Explicitly NOT a revival of `composition_classification` (retired: `naive_exclusivity_fails`,
  per experiments/no_free_lift_wiring/COMPOSITION-CLASSIFICATION-TARGET.md). No classifier,
  no trichotomy, no exclusivity claim. Just the reachability vocabulary and its closure.

  Self-contained (no imports). Deliberately independent of the Witnessed spine so a static
  reachability claim here cannot inherit any dynamic/documentary axiom from elsewhere
  (e.g. TaxonomyGraph's `persistence_normalizes`).
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

end LeanProofs.Admissibility.ReachabilityClosure
