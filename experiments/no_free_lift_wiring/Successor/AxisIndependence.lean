/-
  Successor.AxisIndependence — the four axes of `WitnessedDiscipline` are independent
  (irredundant) under the present definitions.

  Custody class: EXPERIMENTAL-WIRING. NOT in `defaultTargets`; build with
  `lake build Successor`. Schematic over a 3-element model; axiom-free.

  CLAIM (exact): for each of the four axes, there is a compiled finite model in which
  **exactly that axis fails** while the other three hold. Equivalently, no axis follows
  from the conjunction of the other three — the four conditions are **logically
  independent / irredundant under these definitions**.

  This is NOT a claim that the taxonomy is "minimal" without qualification. It does NOT
  prove: that no alternative basis (e.g. some three-axis encoding) expresses the same
  discipline; that these four axes are uniquely natural; or that the taxonomy is complete
  for every notion of witnessed discipline. It proves irredundancy, nothing more.

  Each witness is a 3-element carrier with a concrete `Sem` and `B`; the failing axis is
  refuted by a concrete counterexample, the surviving three by concrete witnesses.
-/
import Successor.Tightened

namespace Successor.AxisIndependence

open Wired.NoFreeLift Successor.Tightened

inductive Three | a | b | c deriving DecidableEq
open Three

/-- (1) `bridge_valid` fails alone: `Sem = {a,b}`, edges `a→b` and `a→c`. The `a→c`
    edge leaves `Sem` (validity fails); selectivity, liveness, and non-triviality hold. -/
theorem bridge_valid_independent :
    ∃ (Sem : Three → Prop) (B : Three → Three → Prop),
      ¬ BridgeValid Sem B ∧ SemanticNontrivial Sem ∧ BridgeSelectiveOnSem Sem B
        ∧ ProperlyLive Sem B := by
  refine ⟨fun t => t = a ∨ t = b, fun x y => (x = a ∧ y = b) ∨ (x = a ∧ y = c), ?_, ?_, ?_, ?_⟩
  · intro hbv
    rcases hbv a c (Or.inl rfl) (Or.inr ⟨rfl, rfl⟩) with h | h <;> exact absurd h (by decide)
  · exact ⟨⟨a, Or.inl rfl⟩, ⟨c, by decide⟩⟩
  · exact ⟨a, b, a, Or.inl rfl, Or.inr rfl, Or.inl rfl, Or.inl ⟨rfl, rfl⟩, by decide⟩
  · exact ⟨a, b, Or.inl rfl, Or.inr rfl, by decide, Or.inl ⟨rfl, rfl⟩⟩

/-- (2) `semantic_nontrivial` fails alone: `Sem ≡ True`, edge `a→b`. No `Sem`-false claim
    (non-triviality fails); validity, selectivity, and liveness hold. -/
theorem semantic_nontrivial_independent :
    ∃ (Sem : Three → Prop) (B : Three → Three → Prop),
      ¬ SemanticNontrivial Sem ∧ BridgeValid Sem B ∧ BridgeSelectiveOnSem Sem B
        ∧ ProperlyLive Sem B := by
  refine ⟨fun _ => True, fun x y => x = a ∧ y = b, ?_, ?_, ?_, ?_⟩
  · rintro ⟨_, _, ht⟩; exact ht trivial
  · intro _ _ _ _; trivial
  · exact ⟨a, b, c, trivial, trivial, trivial, ⟨rfl, rfl⟩, by decide⟩
  · exact ⟨a, b, trivial, trivial, by decide, ⟨rfl, rfl⟩⟩

/-- (3) `bridge_selective` fails alone: `Sem = {a,b}`, `B` fully connected on `Sem`. From
    any sound source every sound target is allowed — no refusal (selectivity fails);
    validity, non-triviality, and liveness hold. -/
theorem bridge_selective_independent :
    ∃ (Sem : Three → Prop) (B : Three → Three → Prop),
      ¬ BridgeSelectiveOnSem Sem B ∧ BridgeValid Sem B ∧ SemanticNontrivial Sem
        ∧ ProperlyLive Sem B := by
  refine ⟨fun t => t = a ∨ t = b, fun x y => (x = a ∨ x = b) ∧ (y = a ∨ y = b), ?_, ?_, ?_, ?_⟩
  · rintro ⟨a', b', c', hsa, _, hsc, _, hnb⟩; exact hnb ⟨hsa, hsc⟩
  · intro x y _ hb; exact hb.2
  · exact ⟨⟨a, Or.inl rfl⟩, ⟨c, by decide⟩⟩
  · exact ⟨a, b, Or.inl rfl, Or.inr rfl, by decide, ⟨Or.inl rfl, Or.inr rfl⟩⟩

/-- (4) `properly_live` fails alone: `Sem = {a,b}`, `B` = sound self-loops only. No
    non-identity sound edge (liveness fails); validity, non-triviality, and selectivity
    hold (a self-loop is an allowed edge, a non-loop a refusal). -/
theorem properly_live_independent :
    ∃ (Sem : Three → Prop) (B : Three → Three → Prop),
      ¬ ProperlyLive Sem B ∧ BridgeValid Sem B ∧ SemanticNontrivial Sem
        ∧ BridgeSelectiveOnSem Sem B := by
  refine ⟨fun t => t = a ∨ t = b, fun x y => (x = a ∧ y = a) ∨ (x = b ∧ y = b), ?_, ?_, ?_, ?_⟩
  · rintro ⟨x, y, _, _, hne, hb⟩
    rcases hb with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> exact hne (h1.trans h2.symm)
  · intro x y _ hb
    rcases hb with ⟨_, h2⟩ | ⟨_, h2⟩
    · exact Or.inl h2
    · exact Or.inr h2
  · exact ⟨⟨a, Or.inl rfl⟩, ⟨c, by decide⟩⟩
  · exact ⟨a, a, b, Or.inl rfl, Or.inl rfl, Or.inr rfl, Or.inl ⟨rfl, rfl⟩, by decide⟩

end Successor.AxisIndependence
