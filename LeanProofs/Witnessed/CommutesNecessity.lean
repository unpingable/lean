/-
  LeanProofs.Witnessed.CommutesNecessity — teeth for the 2.0 normalization theorem.

  Custody class: ANNEX (Mathlib-free). Imports only the spine + AbstractNormalization.

  `AbstractNormalization.normal_form_iff_of_commutes` is an ADMITTING-CLASS theorem: it
  holds for bridge systems whose carry/weaken families satisfy the local commutation law
  `Commutes C W`. This module proves that hypothesis is LOAD-BEARING — not decorative,
  not "works in our favorite room under flattering light":

    there is a concrete two-family system where `Commutes` FAILS, a paid path EXISTS, and
    that path does NOT factor as a carry segment then a weaken segment.

  So the 2.0 result is genuinely conditional on the commutation law; dropping it is not
  free. The model: three nodes with a single weaken edge `a→b` and a single carry edge
  `b→c`. The path is `a --W--> b --C--> c` (weaken then carry), and there is no reordering
  `a --C--> d --W--> c` because `a` has no carry-out.

  No axioms (finite structural model).
-/

import LeanProofs.Witnessed.AbstractNormalization

namespace LeanProofs.Witnessed.CommutesNecessity

open LeanProofs.Witnessed.NoFreeLift
open LeanProofs.Witnessed.AbstractNormalization

inductive V | a | b | c
  deriving DecidableEq, Repr

/-- Single carry edge: `b → c`. -/
def C : V → V → Prop := fun x y => x = .b ∧ y = .c
/-- Single weaken edge: `a → b`. -/
def W : V → V → Prop := fun x y => x = .a ∧ y = .b

/-- Commutation fails: there is a `weaken ; carry` (`a→b→c`) with no `carry ; weaken`
    reordering, because `a` has no outgoing carry. -/
theorem not_commutes : ¬ Commutes C W := by
  intro hcomm
  obtain ⟨_d, hcad, _⟩ := @hcomm V.a V.b V.c ⟨rfl, rfl⟩ ⟨rfl, rfl⟩
  exact absurd hcad.1 (by decide)

/-- A paid path `a → c` exists (weaken then carry). -/
theorem paid_a_c : PaidFrom (Step C W) V.a V.c :=
  PaidFrom.step (PaidFrom.step PaidFrom.refl (Or.inr ⟨rfl, rfl⟩)) (Or.inl ⟨rfl, rfl⟩)

/-- A carry chain out of `a` goes nowhere — `a` has no carry-out. -/
theorem chainC_from_a {z : V} (h : Chain C V.a z) : z = V.a := by
  cases h with
  | nil => rfl
  | cons hs _ => exact absurd hs.1 (by decide)

/-- Weaken-confinement: `{a, b}` is forward-closed under weaken, and excludes `c`. -/
def inS : V → Bool | .a => true | .b => true | .c => false

theorem chainW_stays {x z : V} (h : Chain W x z) (hx : inS x = true) : inS z = true := by
  induction h with
  | nil => exact hx
  | cons hs _ ih => obtain ⟨_, hb⟩ := hs; subst hb; exact ih rfl

/-- The paid path does NOT factor as carry-then-weaken: the only carry-chain from `a`
    stays at `a`, and no weaken-chain from `a` reaches `c`. -/
theorem not_factorable : ¬ ∃ z, Chain C V.a z ∧ Chain W z V.c := by
  rintro ⟨z, hcz, hwz⟩
  have hz : z = V.a := chainC_from_a hcz
  subst hz
  exact absurd (chainW_stays hwz rfl) (by decide)

/-- **commutes_is_necessary** — the commutation law is load-bearing for the 2.0
    normalization theorem: a system where `Commutes` fails admits a paid path with no
    carry-then-weaken factorization. `normal_form_iff_of_commutes` is genuinely
    conditional; the hypothesis is not free. -/
theorem commutes_is_necessary :
    ∃ (β : Type) (Carry Weaken : β → β → Prop) (a c : β),
      ¬ Commutes Carry Weaken ∧
      PaidFrom (Step Carry Weaken) a c ∧
      ¬ ∃ z, Chain Carry a z ∧ Chain Weaken z c :=
  ⟨V, C, W, V.a, V.c, not_commutes, paid_a_c, not_factorable⟩

end LeanProofs.Witnessed.CommutesNecessity
