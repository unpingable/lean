/-
  Successor.DisciplineObstruction — obstruction-of-record + the retired `Discriminating`
  formulation.

  Custody class: EXPERIMENTAL-WIRING (negative result / history). NOT in defaultTargets.

  The model-admission discipline (`Tightened.WitnessedDiscipline`) once had a single
  axis `Discriminating`. This file is the compiled record of WHY it was factored out:
  under `BridgeValid`, `Discriminating` carries no information about the bridge `B`
  beyond semantic non-triviality — it was `SemanticNontrivial` in a relational-sounding
  costume. The obstruction did not invalidate the property; it exposed its real name and
  forced the hidden product (`SemanticNontrivial Sem` × `BridgeSelectiveOnSem Sem B`)
  apart. `Discriminating` is retained here as the discovered formulation, no longer part
  of the canonical structure.
-/
import Successor.Tightened
import Successor.WitnessedDerivation

namespace Successor.DisciplineObstruction

open Wired Wired.NoFreeLift Successor.Tightened Successor.WitnessedDerivation

variable {Claim : Type}

/-- **Discriminating** (HISTORICAL) — the original single discrimination axis: a sound
    source, an unsound target, no bridge between. Retired from the canonical discipline. -/
def Discriminating (Sem : Claim → Prop) (B : Claim → Claim → Prop) : Prop :=
  ∃ c c', Sem c ∧ ¬ Sem c' ∧ ¬ B c c'

/-- **discriminating_is_just_nonconstant_sem** — under `BridgeValid` the `¬ B c c'`
    conjunct is free (validity + `¬ Sem c'` supply it), so `Discriminating` collapses to
    "Sem has a true and a false claim." No residual information about `B`. -/
theorem discriminating_is_just_nonconstant_sem
    {Sem : Claim → Prop} {B : Claim → Claim → Prop} (hv : BridgeValid Sem B) :
    Discriminating Sem B ↔ ∃ c c', Sem c ∧ ¬ Sem c' := by
  constructor
  · rintro ⟨c, c', hc, hc', _⟩; exact ⟨c, c', hc, hc'⟩
  · rintro ⟨c, c', hc, hc'⟩
    exact ⟨c, c', hc, hc', fun hb => hc' (hv c c' hc hb)⟩

/-- **bridgeValid_discriminating_iff_semanticNontrivial** — the factorization theorem:
    under `BridgeValid`, the historical `Discriminating` axis is exactly the canonical
    `SemanticNontrivial` axis. The bridge from the old formulation to the factored one;
    the obstruction exposed `Discriminating`'s real name. -/
theorem bridgeValid_discriminating_iff_semanticNontrivial
    {Sem : Claim → Prop} {B : Claim → Claim → Prop} (hv : BridgeValid Sem B) :
    Discriminating Sem B ↔ SemanticNontrivial Sem := by
  rw [discriminating_is_just_nonconstant_sem hv]
  constructor
  · rintro ⟨c, c', hc, hc'⟩; exact ⟨⟨c, hc⟩, ⟨c', hc'⟩⟩
  · rintro ⟨⟨c, hc⟩, ⟨c', hc'⟩⟩; exact ⟨c, c', hc, hc'⟩

/-- **cut_is_redundant** (HISTORICAL) — the round-1 singleton-context cut is not
    independent content: it follows from `derivation_extends_along_paid_path` +
    `no_free_lift` (the `{c}` context is `PaidFrom B c`). The canonical cut is the
    multi-context `Tightened.cut_admissible_general`. -/
theorem cut_is_redundant
    {K : Claim → Prop} {B : Claim → Claim → Prop} {c c' : Claim}
    (hc : Lift K B c) (hc' : Lift (· = c) B c') : Lift K B c' := by
  obtain ⟨c₀, hc₀, hpath⟩ := no_free_lift hc'
  subst hc₀
  exact derivation_extends_along_paid_path hc hpath

end Successor.DisciplineObstruction
