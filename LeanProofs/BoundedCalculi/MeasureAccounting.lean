/-
  Custody-Class: ANNEX

  BoundedCalculi.MeasureAccounting -- generic measure accounting over
  `Witnessed.ResourceSequent`'s occurrence-linear `Split`/`Consumes`.

  Release-surface support module. NOT imported by promoted kernels. NOT a
  calculus: it defines no judgment and carries no authority -- it is the pure
  conservation engine (measure sums over linear contexts, split additivity,
  singleton-consumption inversions) shared by `CheckpointSettlement` (ANNEX)
  and the scratch sequent ladder.

  Extracted 2026-07-01 from `Scratch/ExecutionSequent.lean` at the v3 promotion
  fork, so that release-surface modules never import scratch (import direction:
  ANNEX -> Witnessed; Scratch -> ANNEX).
-/

import LeanProofs.Witnessed.ResourceSequent

namespace LeanProofs.BoundedCalculi.MeasureAccounting

open LeanProofs.Witnessed.ResourceSequent (Split Consumes)

/-- Total measure of a linear context. -/
def wsum {α : Type} (w : α → Nat) : List α → Nat
  | [] => 0
  | x :: xs => w x + wsum w xs

/-- Splits preserve measure: an interleaving neither mints nor destroys. -/
theorem split_wsum {α : Type} {w : α → Nat} {c r i : List α}
    (h : Split c r i) : wsum w i = wsum w c + wsum w r := by
  induction h with
  | nil => rfl
  | left _ ih => simp only [wsum, ih]; omega
  | right _ ih => simp only [wsum, ih]; omega

/-- Consuming one token costs exactly its measure. -/
theorem consumes_wsum {α : Type} {w : α → Nat} {t : α} {i r : List α}
    (h : Consumes t i r) : wsum w i = w t + wsum w r := by
  have hs := split_wsum (w := w) h
  simp only [wsum] at hs
  omega

/-- A measure vanishing on every member of a list sums to zero over it. -/
theorem wsum_eq_zero_of_all_zero {α : Type} {w : α → Nat}
    {l : List α} (h : ∀ x ∈ l, w x = 0) : wsum w l = 0 := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      simp only [wsum]
      rw [h x (List.Mem.head _), ih (fun y hy => h y (List.Mem.tail _ hy))]

/-- Nothing splits out of an empty input. -/
theorem split_from_nil {α : Type} {c r : List α}
    (h : Split c r []) : c = [] ∧ r = [] := by
  cases h
  exact ⟨rfl, rfl⟩

/-- An empty context cannot consume any token: spent authority is gone. -/
theorem consumes_from_nil {α : Type} {t : α} {r : List α}
    (h : Consumes t [] r) : False := by
  have hnil := split_from_nil h
  cases hnil.1

/-- Consuming from a singleton context: the occurrence is the token and the
    residual is empty. -/
theorem consume_singleton {α : Type} {t x : α} {r : List α}
    (h : Consumes t [x] r) : x = t ∧ r = [] := by
  cases h with
  | left h' =>
      cases h'
      exact ⟨rfl, rfl⟩
  | right h' =>
      exact absurd (split_from_nil h').1 (by simp)

end LeanProofs.BoundedCalculi.MeasureAccounting
