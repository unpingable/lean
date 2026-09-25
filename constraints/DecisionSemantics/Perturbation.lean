/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE

  DecisionSemantics.Perturbation — equal perturbation magnitude does not
  determine the direction of an argmax-style decision.

  ## What this module establishes

  A consumer that perturbs an input, observes a distribution over a finite
  choice space, and measures "how much the distribution moved" is holding a
  scalar.  The scalar is frequently used as if it explained the decision: same
  movement, same effect.  It does not, and the failure is not a corner case —
  it happens at the first non-degenerate example, for *every* rule that selects
  a maximizer, with a base distribution whose own maximizer is unique.

  §1–§3 fix reusable, architecture-independent vocabulary; §4 is the witness;
  §5 states the strongest form: the selected option is not a function of the
  base distribution together with the perturbation distance.

  ## Numeric representation, disclosed

  This module is Mathlib-free by construction, so distributions carry
  natural-number weights over a fixed common denominator `scale` rather than
  real or rational masses.  Total variation is therefore represented exactly by
  its numerator: `TV p q = l1 p q / (2 * scale)`.  `TVEq` compares two such
  distances by cross-multiplication, so the comparison is exact and needs no
  division; `tvEq_iff_l1_eq` shows that at a shared positive scale this is just
  equality of `l1` numerators.  Nothing in the results depends on the
  representation: the witness is a pair of honest probability distributions
  (6/10, 4/10), (8/10, 2/10), (4/10, 6/10).

  ## What this module does NOT establish

  * No calibration, estimator, sampling, or stochastic-process content.  The
    distributions here are given data, not the output of any process.
  * No claim about any API, provider, model, or implementation.
  * No claim that distance is uninformative.  A margin-based sufficient
    condition ("perturbations strictly smaller than the base margin preserve
    the decision") is NOT proved here, and its absence is deliberate: this file
    proves only that magnitude alone is insufficient.
  * No tie-breaking policy.  The witness is built so that both perturbed
    distributions have unique maximizers, so the conclusion holds for every
    argmax-style rule and depends on no tie-breaking convention.
-/

namespace DecisionSemantics

/-! ## §1 Finite weightings and distributions -/

/-- Sum of a `Fin n`-indexed family, defined directly so the package stays
Mathlib-free and closed instances reduce in the kernel. -/
def sumFin : (n : Nat) → (Fin n → Nat) → Nat
  | 0, _ => 0
  | n + 1, w => w (Fin.mk 0 (Nat.succ_pos n)) + sumFin n (fun i => w i.succ)

/-- A weighting of a finite choice space. -/
abbrev Weighting (n : Nat) : Type := Fin n → Nat

/--
A distribution over the `n`-element choice space, given as natural-number
weights over the common denominator `scale`.  Option `i` carries probability
`weight i / scale`.
-/
structure Dist (n : Nat) (scale : Nat) where
  weight : Weighting n
  normalized : sumFin n weight = scale

/-! ## §2 Distance -/

/-- Absolute difference of naturals. -/
def natDist (a b : Nat) : Nat := (a - b) + (b - a)

theorem natDist_self (a : Nat) : natDist a a = 0 := by
  simp [natDist]

theorem natDist_comm (a b : Nat) : natDist a b = natDist b a := by
  simp [natDist, Nat.add_comm]

/--
The `l1` numerator of two distributions at a common scale:
`l1 p q = 2 * scale * TV(p, q)`.
-/
def l1 {n scale : Nat} (p q : Dist n scale) : Nat :=
  sumFin n (fun i => natDist (p.weight i) (q.weight i))

/--
Exact equality of total-variation distances, possibly at different scales,
compared by cross-multiplication:
`l1 p q / (2 * s) = l1 p' q' / (2 * t)` iff `l1 p q * t = l1 p' q' * s`.
-/
def TVEq {n s t : Nat} (p q : Dist n s) (p' q' : Dist n t) : Prop :=
  l1 p q * t = l1 p' q' * s

/-- At a shared scale, equal total variation is exactly equal `l1` numerator. -/
theorem tvEq_iff_l1_eq {n s : Nat} (hs : 0 < s) (p q p' q' : Dist n s) :
    TVEq p q p' q' ↔ l1 p q = l1 p' q' := by
  constructor
  · intro h
    exact Nat.eq_of_mul_eq_mul_right hs h
  · intro h
    simp [TVEq, h]

/-! ## §3 Decision rules -/

/-- A decision rule selects one option from the choice space. -/
abbrev DecisionRule (n : Nat) : Type := Weighting n → Fin n

/-- `i` attains the maximum weight. -/
def IsMaximizer {n : Nat} (w : Weighting n) (i : Fin n) : Prop :=
  ∀ j : Fin n, w j ≤ w i

/-- `i` attains the maximum weight and is the only option that does. -/
def UniqueMaximizer {n : Nat} (w : Weighting n) (i : Fin n) : Prop :=
  ∀ j : Fin n, j ≠ i → w j < w i

/--
The assumption on the rule, isolated: it is argmax-style, i.e. it always
selects some maximizer.  Tie-breaking is left entirely unspecified.
-/
def ArgmaxRule {n : Nat} (r : DecisionRule n) : Prop :=
  ∀ w : Weighting n, IsMaximizer w (r w)

/-- Where the maximizer is unique, every argmax-style rule agrees on it, with
no appeal to a tie-breaking convention. -/
theorem argmax_eq_of_uniqueMaximizer {n : Nat} {r : DecisionRule n}
    (hr : ArgmaxRule r) {w : Weighting n} {i : Fin n}
    (hu : UniqueMaximizer w i) : r w = i := by
  by_cases hEq : r w = i
  · exact hEq
  · exact absurd (hr w i) (Nat.not_le.mpr (hu (r w) hEq))

/-! ## §4 The witness

  Choice space `Fin 2`, common denominator `10`.  The base distribution has a
  unique maximizer, so the phenomenon is not an artifact of a tied base.
-/

/-- The two-point weighting `(a, b)`. -/
def pair (a b : Nat) : Weighting 2 := fun i => if i.val = 0 then a else b

/-- Base distribution `(6/10, 4/10)`; option `0` is the unique maximizer. -/
def base : Dist 2 10 := { weight := pair 6 4, normalized := by decide }

/-- Perturbation that reinforces the base decision: `(8/10, 2/10)`. -/
def reinforcing : Dist 2 10 := { weight := pair 8 2, normalized := by decide }

/-- Perturbation that reverses the base decision: `(4/10, 6/10)`. -/
def reversing : Dist 2 10 := { weight := pair 4 6, normalized := by decide }

theorem l1_base_reinforcing : l1 base reinforcing = 4 := by decide

theorem l1_base_reversing : l1 base reversing = 4 := by decide

/-- Both perturbations sit at total variation `4 / 20 = 1 / 5` from the base. -/
theorem equal_perturbation_magnitude : TVEq base reinforcing base reversing := by
  unfold TVEq
  decide

theorem uniqueMaximizer_base : UniqueMaximizer base.weight 0 := by
  unfold UniqueMaximizer
  decide

theorem uniqueMaximizer_reinforcing : UniqueMaximizer reinforcing.weight 0 := by
  unfold UniqueMaximizer
  decide

theorem uniqueMaximizer_reversing : UniqueMaximizer reversing.weight 1 := by
  unfold UniqueMaximizer
  decide

theorem argmax_base {r : DecisionRule 2} (hr : ArgmaxRule r) :
    r base.weight = 0 :=
  argmax_eq_of_uniqueMaximizer hr uniqueMaximizer_base

theorem argmax_reinforcing {r : DecisionRule 2} (hr : ArgmaxRule r) :
    r reinforcing.weight = 0 :=
  argmax_eq_of_uniqueMaximizer hr uniqueMaximizer_reinforcing

theorem argmax_reversing {r : DecisionRule 2} (hr : ArgmaxRule r) :
    r reversing.weight = 1 :=
  argmax_eq_of_uniqueMaximizer hr uniqueMaximizer_reversing

/--
**Headline (witness).**  One base distribution, two perturbations at equal
total-variation distance from it, opposite selected options — for every
argmax-style rule.
-/
theorem equal_magnitude_opposite_decisions {r : DecisionRule 2}
    (hr : ArgmaxRule r) :
    TVEq base reinforcing base reversing ∧
      r reinforcing.weight ≠ r reversing.weight := by
  refine ⟨equal_perturbation_magnitude, ?_⟩
  rw [argmax_reinforcing hr, argmax_reversing hr]
  decide

/-- The same witness read as an attribution failure: at identical magnitude one
perturbation preserves the base decision and the other reverses it. -/
theorem equal_magnitude_preserves_and_reverses {r : DecisionRule 2}
    (hr : ArgmaxRule r) :
    TVEq base reinforcing base reversing ∧
      r reinforcing.weight = r base.weight ∧
      r reversing.weight ≠ r base.weight := by
  refine ⟨equal_perturbation_magnitude, ?_, ?_⟩
  · rw [argmax_reinforcing hr, argmax_base hr]
  · rw [argmax_reversing hr, argmax_base hr]
    decide

/-- Existential form. -/
theorem exists_equal_magnitude_opposite_decisions {r : DecisionRule 2}
    (hr : ArgmaxRule r) :
    ∃ p q₁ q₂ : Dist 2 10,
      TVEq p q₁ p q₂ ∧ r q₁.weight ≠ r q₂.weight :=
  ⟨base, reinforcing, reversing, equal_magnitude_opposite_decisions hr⟩

/-! ## §5 The strongest form: no magnitude-only attribution -/

/--
A *magnitude-only attribution* for a rule claims the selected option after a
perturbation is a function of the base distribution's weighting together with
the perturbation's total-variation distance — that is, the scalar "how far it
moved" explains the decision.
-/
def MagnitudeOnlyAttribution {n : Nat} (scale : Nat) (r : DecisionRule n)
    (f : Weighting n → Nat → Fin n) : Prop :=
  ∀ p q : Dist n scale, r q.weight = f p.weight (l1 p q)

/--
**Headline (general).**  No argmax-style rule admits any magnitude-only
attribution.  Distance-only perturbation magnitude does not determine decision
direction, for any candidate explanation function whatsoever.
-/
theorem no_magnitudeOnly_attribution {r : DecisionRule 2} (hr : ArgmaxRule r)
    (f : Weighting 2 → Nat → Fin 2) :
    ¬ MagnitudeOnlyAttribution 10 r f := by
  intro h
  have h₁ : r reinforcing.weight = f base.weight 4 := by
    have := h base reinforcing
    rwa [l1_base_reinforcing] at this
  have h₂ : r reversing.weight = f base.weight 4 := by
    have := h base reversing
    rwa [l1_base_reversing] at this
  have : (0 : Fin 2) = 1 := by
    rw [← argmax_reinforcing hr, ← argmax_reversing hr, h₁, h₂]
  exact absurd this (by decide)

end DecisionSemantics
