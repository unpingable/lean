/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE

  DecisionSemantics.InterfaceCoherence — when an interface exposes both a
  reported choice and the weights it was chosen from, what invariant does a
  consumer need before the two readings of the response may be used
  interchangeably?

  ## What this module establishes

  A response that carries both a selected option and a distribution over the
  choice space can be read two ways: trust the reported choice, or ignore it
  and recompute the selection from the weights.  Downstream code routinely does
  one in one place and the other in another, on the assumption that they
  coincide.

  The natural invariant to reach for — "the reported choice is a maximizer" —
  is NOT enough, and the gap is not exotic: it opens exactly when the weights
  admit two maximizers, because the emitter and the consumer may then resolve
  the tie differently.  §3 proves the insufficiency in the weakest generic
  form, §4 exhibits a closed constructive counterexample, and §2 identifies the
  invariant that does work: agreement with a *designated* rule, named as part
  of the invariant.

  ## What this module does NOT establish

  * No calibration, estimator, sampling, or stochastic-process content.  A
    response is given data; nothing produces it.
  * No claim about any API, provider, model, implementation, wire format, or
    dataset.  `Response` is a two-field record over the vocabulary already
    fixed in `DecisionSemantics.Perturbation`.
  * No recommendation of a tie-breaking policy.  `leastIndexArgmax` and
    `greatestIndexArgmax` exist only as two concrete argmax rules that differ
    on a tie; neither is endorsed.
  * No claim that ties are rare, common, avoidable, or pathological.
  * No claim that an interface ought to expose either field, or both.
-/

import DecisionSemantics.Perturbation

namespace DecisionSemantics

/-! ## §1 Responses, the two consumers, and observational agreement -/

/--
A response from a decision interface that exposes both readings: the weights it
scored the choice space with, and the option it reports having selected.
-/
structure Response (n : Nat) (scale : Nat) where
  weights : Dist n scale
  choice : Fin n

/-- The consumer that trusts the reported choice. -/
def trustChoice {n scale : Nat} (r : Response n scale) : Fin n :=
  r.choice

/-- The consumer that discards the reported choice and recomputes it from the
weights with a designated rule. -/
def recompute {n scale : Nat} (rule : DecisionRule n) (r : Response n scale) :
    Fin n :=
  rule r.weights.weight

/--
Observational agreement on a response: the two consumers select the same
option.  This is the only notion of "the two readings may be used
interchangeably" used in this module.
-/
def Agree {n scale : Nat} (rule : DecisionRule n) (r : Response n scale) :
    Prop :=
  trustChoice r = recompute rule r

/-! ## §2 Two candidate invariants -/

/--
The weak invariant: the reported choice is *some* maximizer of the reported
weights.  It names no rule.
-/
def MaximizerCoherent {n scale : Nat} (r : Response n scale) : Prop :=
  IsMaximizer r.weights.weight r.choice

/--
The strong invariant, stated relative to a designated rule: the reported choice
is the one that rule computes from the reported weights.  The rule is part of
the invariant, not an afterthought.
-/
def RuleCoherent {n scale : Nat} (rule : DecisionRule n)
    (r : Response n scale) : Prop :=
  r.choice = rule r.weights.weight

/--
**Headline (positive).**  Under the strong invariant the two consumers agree.

This theorem establishes exactly one thing: for a fixed `rule` and response
`r`, `Agree rule r` and `RuleCoherent rule r` are the same proposition (the
proof is `Iff.rfl`).  It says nothing on its own about any other invariant.
The stronger readings are established elsewhere: that the maximizer-only
weakening does not yield agreement is `maximizerCoherent_permits_disagreement`
and `maximizerCoherent_insufficient_for_agreement`; that coherence with one
argmax rule does not yield agreement with another, so the invariant must name
its rule, is `coherence_is_rule_relative`.
-/
theorem agree_iff_ruleCoherent {n scale : Nat} (rule : DecisionRule n)
    (r : Response n scale) : Agree rule r ↔ RuleCoherent rule r :=
  Iff.rfl

/-- The direction the consumer uses. -/
theorem agree_of_ruleCoherent {n scale : Nat} {rule : DecisionRule n}
    {r : Response n scale} (h : RuleCoherent rule r) : Agree rule r :=
  h

/-- The strong invariant is satisfiable: every weighting has a coherent
response, so §3 is an insufficiency result about the weak invariant and not a
no-go result about coherence. -/
def canonicalResponse {n scale : Nat} (rule : DecisionRule n)
    (w : Dist n scale) : Response n scale :=
  { weights := w, choice := rule w.weight }

theorem canonicalResponse_ruleCoherent {n scale : Nat} (rule : DecisionRule n)
    (w : Dist n scale) : RuleCoherent rule (canonicalResponse rule w) :=
  rfl

/-- The strong invariant implies the weak one, for any argmax-style designated
rule.  So the weak invariant is genuinely the weaker of the two. -/
theorem maximizerCoherent_of_ruleCoherent {n scale : Nat}
    {rule : DecisionRule n} (hr : ArgmaxRule rule) {r : Response n scale}
    (h : RuleCoherent rule r) : MaximizerCoherent r := by
  unfold MaximizerCoherent
  rw [h]
  exact hr r.weights.weight

/-! ## §3 The weak invariant is insufficient, generically -/

/--
**Headline (insufficiency, weakest form).**  Whenever the reported weights
admit two distinct maximizers, the weak invariant permits disagreement: for
*any* designated rule whatsoever there is a response on those exact weights
that satisfies `MaximizerCoherent` and on which the two consumers disagree.

No assumption is made on `rule` — not even `ArgmaxRule` — so the obstruction is
the tie, not the rule's quality.
-/
theorem maximizerCoherent_permits_disagreement {n scale : Nat}
    (rule : DecisionRule n) (w : Dist n scale) {i j : Fin n}
    (hi : IsMaximizer w.weight i) (hj : IsMaximizer w.weight j) (hij : i ≠ j) :
    ∃ r : Response n scale,
      r.weights = w ∧ MaximizerCoherent r ∧ ¬ Agree rule r := by
  by_cases h : rule w.weight = i
  · refine ⟨{ weights := w, choice := j }, rfl, hj, ?_⟩
    intro hAgree
    have hEq : j = rule w.weight := hAgree
    exact hij (h.symm.trans hEq.symm)
  · refine ⟨{ weights := w, choice := i }, rfl, hi, ?_⟩
    intro hAgree
    have hEq : i = rule w.weight := hAgree
    exact h hEq.symm

/--
The converse boundary, stated so the insufficiency is not overread: when the
reported weights have no tie at the top, the weak invariant already forces
agreement with every argmax-style rule.  Ties are the whole gap.
-/
def NoTopTie {n : Nat} (w : Weighting n) : Prop :=
  ∀ i j : Fin n, IsMaximizer w i → IsMaximizer w j → i = j

theorem agree_of_maximizerCoherent_of_noTopTie {n scale : Nat}
    {rule : DecisionRule n} (hr : ArgmaxRule rule) {r : Response n scale}
    (hTie : NoTopTie r.weights.weight) (h : MaximizerCoherent r) :
    Agree rule r :=
  hTie r.choice (rule r.weights.weight) h (hr r.weights.weight)

/-- A unique maximizer is a special case of no top tie. -/
theorem eq_of_isMaximizer_of_uniqueMaximizer {n : Nat} {w : Weighting n}
    {i j : Fin n} (hu : UniqueMaximizer w i) (hj : IsMaximizer w j) : j = i := by
  by_cases hEq : j = i
  · exact hEq
  · exact absurd (hj i) (Nat.not_le.mpr (hu j hEq))

theorem noTopTie_of_uniqueMaximizer {n : Nat} {w : Weighting n} {i : Fin n}
    (hu : UniqueMaximizer w i) : NoTopTie w := by
  intro a b ha hb
  rw [eq_of_isMaximizer_of_uniqueMaximizer hu ha,
    eq_of_isMaximizer_of_uniqueMaximizer hu hb]

/-! ## §4 Closed constructive counterexample

  Choice space `Fin 2`, scale `10`, weights `(5/10, 5/10)`.  Everything below
  is a closed term; the disagreements are decided by the kernel.
-/

/-- Tie-break toward the least index. -/
def leastIndexArgmax : DecisionRule 2 :=
  fun w => if w 1 ≤ w 0 then 0 else 1

/-- Tie-break toward the greatest index. -/
def greatestIndexArgmax : DecisionRule 2 :=
  fun w => if w 0 ≤ w 1 then 1 else 0

theorem fin2_eq_zero_or_one (i : Fin 2) : i = 0 ∨ i = 1 := by
  revert i
  decide

theorem leastIndexArgmax_isArgmax : ArgmaxRule leastIndexArgmax := by
  intro w
  unfold IsMaximizer leastIndexArgmax
  intro j
  rcases fin2_eq_zero_or_one j with hj | hj
  · subst hj
    by_cases h : w 1 ≤ w 0
    · rw [if_pos h]
      exact Nat.le_refl _
    · rw [if_neg h]
      exact Nat.le_of_lt (Nat.not_le.mp h)
  · subst hj
    by_cases h : w 1 ≤ w 0
    · rw [if_pos h]
      exact h
    · rw [if_neg h]
      exact Nat.le_refl _

theorem greatestIndexArgmax_isArgmax : ArgmaxRule greatestIndexArgmax := by
  intro w
  unfold IsMaximizer greatestIndexArgmax
  intro j
  rcases fin2_eq_zero_or_one j with hj | hj
  · subst hj
    by_cases h : w 0 ≤ w 1
    · rw [if_pos h]
      exact h
    · rw [if_neg h]
      exact Nat.le_refl _
  · subst hj
    by_cases h : w 0 ≤ w 1
    · rw [if_pos h]
      exact Nat.le_refl _
    · rw [if_neg h]
      exact Nat.le_of_lt (Nat.not_le.mp h)

/-- The tied weighting `(5/10, 5/10)`. -/
def tiedWeights : Dist 2 10 := { weight := pair 5 5, normalized := by decide }

/-- A response on tied weights reporting option `1`, which *is* a maximizer. -/
def tiedResponse : Response 2 10 :=
  { weights := tiedWeights, choice := 1 }

theorem tiedResponse_maximizerCoherent : MaximizerCoherent tiedResponse := by
  unfold MaximizerCoherent IsMaximizer
  decide

theorem tiedResponse_not_ruleCoherent :
    ¬ RuleCoherent leastIndexArgmax tiedResponse := by
  unfold RuleCoherent
  decide

/-- The two consumers disagree on a response the weak invariant admits. -/
theorem tiedResponse_disagree : ¬ Agree leastIndexArgmax tiedResponse := by
  unfold Agree trustChoice recompute
  decide

/--
**Headline (counterexample).**  A designated argmax rule and a concrete
response satisfying the maximizer-only invariant, on which trusting the
reported choice and recomputing disagree.
-/
theorem maximizerCoherent_insufficient_for_agreement :
    ∃ (rule : DecisionRule 2) (r : Response 2 10),
      ArgmaxRule rule ∧ MaximizerCoherent r ∧ ¬ Agree rule r :=
  ⟨leastIndexArgmax, tiedResponse, leastIndexArgmax_isArgmax,
    tiedResponse_maximizerCoherent, tiedResponse_disagree⟩

/-- No designated rule is immune — argmax-style or not; no hypothesis is placed
on `rule`: the concrete tie defeats every rule, because the emitter may always
report the other maximizer. -/
theorem every_rule_admits_disagreement_on_tie (rule : DecisionRule 2) :
    ∃ r : Response 2 10, MaximizerCoherent r ∧ ¬ Agree rule r := by
  have h0 : IsMaximizer tiedWeights.weight 0 := by
    unfold IsMaximizer
    decide
  have h1 : IsMaximizer tiedWeights.weight 1 := by
    unfold IsMaximizer
    decide
  obtain ⟨r, _, hMax, hDis⟩ :=
    maximizerCoherent_permits_disagreement rule tiedWeights h0 h1 (by decide)
  exact ⟨r, hMax, hDis⟩

/--
**Headline (rule-relativity).**  The strong invariant must name its rule.  A
response can be `RuleCoherent` for one argmax rule and still disagree with a
consumer that recomputes using a different argmax rule, so "coherent" is not a
property of the response alone.
-/
theorem coherence_is_rule_relative :
    ∃ (rule₁ rule₂ : DecisionRule 2) (r : Response 2 10),
      ArgmaxRule rule₁ ∧ ArgmaxRule rule₂ ∧
        RuleCoherent rule₁ r ∧ ¬ Agree rule₂ r :=
  ⟨leastIndexArgmax, greatestIndexArgmax,
    { weights := tiedWeights, choice := 0 },
    leastIndexArgmax_isArgmax, greatestIndexArgmax_isArgmax,
    by unfold RuleCoherent; decide,
    by unfold Agree trustChoice recompute; decide⟩

/-! ## §5 `ArgmaxRule` is necessary for the tie-free rescue

  `agree_of_maximizerCoherent_of_noTopTie` assumes `ArgmaxRule rule`.  The
  closed witness below shows the hypothesis cannot be dropped: with a rule that
  ignores the weights, tie-free weights and a maximizer-coherent response still
  admit disagreement.
-/

/-- A rule that ignores the weights and always selects option `1`. -/
def constantOneRule : DecisionRule 2 := fun _ => 1

theorem constantOneRule_not_argmax : ¬ ArgmaxRule constantOneRule := by
  intro h
  have h0 : base.weight 0 ≤ base.weight (constantOneRule base.weight) := h base.weight 0
  exact absurd h0 (by unfold constantOneRule; decide)

/-- `base = (6/10, 4/10)` from `Perturbation` has no top tie. -/
theorem noTopTie_base : NoTopTie base.weight :=
  noTopTie_of_uniqueMaximizer uniqueMaximizer_base

/-- A tie-free response reporting the unique maximizer `0`. -/
def tieFreeResponse : Response 2 10 :=
  { weights := base, choice := 0 }

theorem tieFreeResponse_maximizerCoherent :
    MaximizerCoherent tieFreeResponse := by
  unfold MaximizerCoherent IsMaximizer
  decide

theorem tieFreeResponse_disagree_constantOneRule :
    ¬ Agree constantOneRule tieFreeResponse := by
  unfold Agree trustChoice recompute constantOneRule
  decide

/--
**Necessity of `ArgmaxRule`.**  A non-argmax rule, tie-free weights, and a
maximizer-coherent response on which the two consumers disagree.  So the
`ArgmaxRule` hypothesis of `agree_of_maximizerCoherent_of_noTopTie` is not
removable.
-/
theorem argmaxRule_necessary_for_noTopTie_agreement :
    ∃ (rule : DecisionRule 2) (r : Response 2 10),
      ¬ ArgmaxRule rule ∧ NoTopTie r.weights.weight ∧
        MaximizerCoherent r ∧ ¬ Agree rule r :=
  ⟨constantOneRule, tieFreeResponse, constantOneRule_not_argmax,
    noTopTie_base, tieFreeResponse_maximizerCoherent,
    tieFreeResponse_disagree_constantOneRule⟩

end DecisionSemantics
