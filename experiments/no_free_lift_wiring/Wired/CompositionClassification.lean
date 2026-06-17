/-
  Wired.CompositionClassification — findings + one trivial first lemma.
  NOT a calculus, NOT a classifier. Unwired. Custody class: TARGET SCAFFOLD / FINDINGS.

  An adversarial pass (codex, gpt-5.5) gutted the first "two-register classifier"
  draft and was right: it was mostly theater — unused outcome enums, a verbatim
  re-export masquerading as classification, and theorem names stronger than the
  propositions. Pared back here to what is actually true plus the structural
  findings (which are real and are the point).

  WHAT IS ACTUALLY TRUE / FOUND:

  1. The single `classify : Attempt × validity → Outcome` target is dead. The real
     `Embedding.Bridge` is same-axis by construction (`bridge_both_freshness`;
     cross edges definitionally `False`), so cross-axis outcomes cannot be
     `Attempt Bridge` values. Same-axis and cross-axis are different domains.

  2. Same-axis "composition" is, formally, just `paid_lift_sound` specialized to a
     two-step `Lift` (`freshness_two_step_lift_sound` below). It proves SOUND REACH
     (`Sem` holds at the end), NOT that the composite is a single `Bridge`, NOT a
     `PaidFrom`-returning composition lemma — and it accepts DEGENERATE steps (the
     weakening disjunct of `Bridge` includes reflexive `f = f'`). "Composes" was an
     overclaim; this is a near-trivial soundness instance.

  3. The freshness `Bridge` RELATION is not closed under composition (two
     carry-forwards give budget = base + spend₁ + spend₂ ≥ base + d(direct) by
     triangle — carry THEN weaken). What is sound/closed is the `Lift`/`PaidFrom`
     PATH. The carry law makes the path sound; it does not close the relation.

  4. Cross-axis non-conversion is ALREADY proved — `Embedding.cross_edge_dichotomy`
     (unpaid ⇒ unsound; valid ⇒ target-already-true). This file does NOT restate it
     under a new name (the first draft did — laundering). Cite the original.
     CAVEAT (codex): its "redundant" only proves the target is semantically TRUE
     under a valid bridge; it does NOT prove the edge adds no DERIVABILITY/reach
     relative to a floor `K` (a valid cross edge could reach a true-but-otherwise-
     unreachable freshness claim). "Adds nothing" is an Embedding-level overclaim to
     fix before any coverage theorem.

  5. NOT EXHAUSTIVE. Covered: 2-step same-axis freshness paths, and (by citation)
     authority→freshness candidate edges. NOT covered: freshness→authority and
     authority→authority candidates, 1-step and n-step paths, malformed /
     neither-register attempts. Two SPECIMENS, not a partition. There is no
     "two-register calculus" yet — that framing was a placard. A real classifier
     needs a function over a stated domain that USES outcome values, exhaustively,
     with a soundness theorem. Unbuilt.
-/
import Wired.NoFreeLift
import Wired.Embedding

namespace Wired.CompositionClassification

/-- **freshness_two_step_lift_sound.** A two-step same-axis freshness `Lift` from a
    sound floor reaches a true `Sem` claim. This is `embedded_lift_sound`
    (= `paid_lift_sound`) at a length-2 path — near-trivial, and it accepts
    degenerate/weakening steps. Kept only as the concrete same-axis witness; it is
    NOT a composition lemma (proves reach-soundness, not that the composite is a
    bridge), and the name says so. -/
theorem freshness_two_step_lift_sound
    {f f' f'' : Embedding.FreshClaim}
    {K : Embedding.Claim → Prop} (hK : Embedding.EnvSound K)
    (hbase : K (Sum.inr f))
    (h₁ : Embedding.Bridge (Sum.inr f) (Sum.inr f'))
    (h₂ : Embedding.Bridge (Sum.inr f') (Sum.inr f'')) :
    Embedding.Sem (Sum.inr f'') :=
  Embedding.embedded_lift_sound hK
    (NoFreeLift.Lift.cross (NoFreeLift.Lift.cross (NoFreeLift.Lift.base hbase) h₁) h₂)

-- Cross-axis non-conversion: see `Embedding.cross_edge_dichotomy` directly
-- (cited, not restated — see finding 4 and its `redundant` caveat). No classifier
-- function or outcome enum is defined yet: there is no honest formal classification
-- to host them, and dead vocabulary is what codex (correctly) flagged.

end Wired.CompositionClassification
