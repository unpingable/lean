/-
  LeanProofs.Scratch.DerivationData -- the v5 seed (F7 artifact): derivations
  reified as data, and the already-normal theorem.

  Custody-Class: SCRATCH. Unpromoted, compile-is-contact only. Not imported by
  `LeanProofs.lean`, `LeanProofs.BoundedCalculi`, or any promoted kernel.
  Post-v4 work (docs/POST-V4-CAMPAIGN.md, F7).

  THE F7 FINDING: custody-preserving normalization (the v5 prestige target,
  "no normalization step may erase custody evidence") has an honest starting
  point that had to be discovered before designing v5:

    UNDER THE v4 DISCIPLINE, THERE ARE NO REDEXES. Every derivation is
    ALREADY in read-rooted normal form -- not as a theorem about a
    normalization procedure, but because the discipline makes detours
    unstatable: no rule concludes evidence, so an evidence premise cannot
    contain a cut, so the only shape an evidence sub-derivation can have is
    derive*(read). Normalization is the identity on this calculus.

  Consequently v5 proper is scoped as: (1) reify derivations as DATA (this
  file); (2) add structural rules as explicit, policy-priced NODES (weakening
  / contraction / exchange) -- these create genuine detours; (3) define
  normalization eliminating the detours; (4) prove it terminates, lands back
  in the read-rooted class, and PRESERVES `chainOf` -- the evidence chain
  defined here is the invariant-to-be. The classifier insight carries: the
  discipline is a class of systems, and v5 normalization must be an operation
  that provably cannot leave the class.

  Landed here:
  * `Deriv` -- derivation trees as a Type family mirroring `EEntail`.
  * `toEntail` / `deriv_exists` / `eentail_iff_nonempty_deriv` -- the
    reflection pair: Prop-derivability coincides with data-derivability.
  * `chainOf` -- the evidence chain of a derivation tree, as data.
  * `Pure` / `evidence_derivs_pure` -- under the discipline, evidence-typed
    sub-derivations contain no cuts (pure derive-chains over reads).
  * `ReadRooted` / `all_derivs_read_rooted` -- THE already-normal theorem:
    under the discipline, every derivation tree is read-rooted normal.
  * `pure_chain_empty` -- pure sub-derivations contribute no chain entries
    (the chain is exactly the cut spine's evidence list).

  Honesty notes:
  * `deriv_exists` produces `Nonempty` (Prop-level existence of data) --
    EEntail is a Prop and cannot compute a tree; the checker that BUILDS
    trees is v6 work.
  * `chainOf` records each cut's evidence endpoint in spine order; recording
    full per-hop derivation chains (origin + steps) is a v5 design decision
    deferred until structural nodes exist to threaten them.

  Mathlib-free.
-/

import LeanProofs.Scratch.EvidenceCalculusSequent

namespace LeanProofs.Scratch.DerivationData

open LeanProofs.Scratch.CustodyIndexedSequent (System IsEvidence
  EvidenceNeverConcluded)
open LeanProofs.Scratch.StructuralPolicySequent (ContextPolicy)
open LeanProofs.Scratch.EvidenceCalculusSequent (EvidenceCalculus EEntail)

variable {J : Type} {Ix : Type} {Ctx : Type}

/-! ## Derivations as data -/

/-- Derivation trees: the data mirror of `EEntail`. -/
inductive Deriv (S : System J Ix) (E : EvidenceCalculus S)
    (P : ContextPolicy J Ctx) : Ctx → J → Ctx → Type where
  | ax {c c' : Ctx} {j : J} :
      P.Reads c j c' → Deriv S E P c j c'
  | cut {c c₁ c₂ : Ctx} {src evid tgt : J} :
      S.Rule src evid tgt →
      Deriv S E P c src c₁ →
      Deriv S E P c₁ evid c₂ →
      Deriv S E P c tgt c₂
  | derive {c c' : Ctx} {e₁ e₂ : J} :
      E.Step e₁ e₂ →
      Deriv S E P c e₁ c' →
      Deriv S E P c e₂ c'

/-- Reflection: every tree witnesses the Prop. -/
def Deriv.toEntail {S : System J Ix} {E : EvidenceCalculus S}
    {P : ContextPolicy J Ctx} :
    {c : Ctx} → {j : J} → {c' : Ctx} →
    Deriv S E P c j c' → EEntail S E P c j c'
  | _, _, _, .ax hr => .ax hr
  | _, _, _, .cut r ds de => .cut r ds.toEntail de.toEntail
  | _, _, _, .derive hs d => .derive hs d.toEntail

/-- Reflection: the Prop guarantees a tree exists. -/
theorem deriv_exists {S : System J Ix} {E : EvidenceCalculus S}
    {P : ContextPolicy J Ctx} {c c' : Ctx} {j : J}
    (h : EEntail S E P c j c') :
    Nonempty (Deriv S E P c j c') := by
  induction h with
  | ax hr => exact ⟨.ax hr⟩
  | cut r _ _ ih1 ih2 =>
      exact ih1.elim fun d1 => ih2.elim fun d2 => ⟨.cut r d1 d2⟩
  | derive hs _ ih =>
      exact ih.elim fun d => ⟨.derive hs d⟩

/-- The reflection pair, packaged. -/
theorem eentail_iff_nonempty_deriv {S : System J Ix} {E : EvidenceCalculus S}
    {P : ContextPolicy J Ctx} {c c' : Ctx} {j : J} :
    EEntail S E P c j c' ↔ Nonempty (Deriv S E P c j c') :=
  ⟨deriv_exists, fun ⟨d⟩ => d.toEntail⟩

/-! ## The evidence chain, as data -/

/-- The evidence chain of a tree: each cut's evidence endpoint, spine order.
    THE INVARIANT-TO-BE: v5 normalization must preserve this list. -/
def Deriv.chainOf {S : System J Ix} {E : EvidenceCalculus S}
    {P : ContextPolicy J Ctx} :
    {c : Ctx} → {j : J} → {c' : Ctx} → Deriv S E P c j c' → List J
  | _, _, _, .ax _ => []
  | _, _, _, .cut (evid := e) _ ds de => e :: (ds.chainOf ++ de.chainOf)
  | _, _, _, .derive _ d => d.chainOf

/-! ## Purity: evidence sub-derivations contain no cuts -/

/-- Pure trees: derive-chains over a single read. -/
inductive Pure {S : System J Ix} {E : EvidenceCalculus S}
    {P : ContextPolicy J Ctx} :
    {c : Ctx} → {j : J} → {c' : Ctx} → Deriv S E P c j c' → Prop where
  | ax {c c' : Ctx} {j : J} {hr : P.Reads c j c'} :
      Pure (.ax hr)
  | derive {c c' : Ctx} {e₁ e₂ : J} {hs : E.Step e₁ e₂}
      {d : Deriv S E P c e₁ c'} :
      Pure d → Pure (.derive hs d)

/-- Under the discipline, every evidence-typed tree is pure: a cut concluding
    evidence would need a rule the discipline forbids, and derive steps only
    move between evidence forms. -/
theorem evidence_derivs_pure {S : System J Ix} {E : EvidenceCalculus S}
    {P : ContextPolicy J Ctx}
    (hD : EvidenceNeverConcluded S)
    {c c' : Ctx} {j : J}
    (d : Deriv S E P c j c') :
    IsEvidence S j → Pure d := by
  induction d with
  | ax hr =>
      intro _
      exact Pure.ax
  | cut r ds de ih1 ih2 =>
      intro hj
      obtain ⟨s, t, hr'⟩ := hj
      exact absurd r (hD hr')
  | derive hs d ih =>
      intro hj
      obtain ⟨s, t, hr⟩ := hj
      exact Pure.derive (ih ⟨s, t, E.step_shape hs hr⟩)

/-- Pure trees contribute no chain entries: the chain is exactly the cut
    spine's evidence list. -/
theorem pure_chain_empty {S : System J Ix} {E : EvidenceCalculus S}
    {P : ContextPolicy J Ctx}
    {c c' : Ctx} {j : J} {d : Deriv S E P c j c'}
    (h : Pure d) : d.chainOf = [] := by
  induction h with
  | ax => rfl
  | derive _ ih => exact ih

/-! ## The already-normal theorem -/

/-- Read-rooted normal form, as a predicate on trees: every cut's evidence
    premise is pure (a derive-chain over a read). -/
inductive ReadRooted {S : System J Ix} {E : EvidenceCalculus S}
    {P : ContextPolicy J Ctx} :
    {c : Ctx} → {j : J} → {c' : Ctx} → Deriv S E P c j c' → Prop where
  | ax {c c' : Ctx} {j : J} {hr : P.Reads c j c'} :
      ReadRooted (.ax hr)
  | cut {c c₁ c₂ : Ctx} {src evid tgt : J} {r : S.Rule src evid tgt}
      {ds : Deriv S E P c src c₁} {de : Deriv S E P c₁ evid c₂} :
      ReadRooted ds → Pure de → ReadRooted (.cut r ds de)
  | derive {c c' : Ctx} {e₁ e₂ : J} {hs : E.Step e₁ e₂}
      {d : Deriv S E P c e₁ c'} :
      ReadRooted d → ReadRooted (.derive hs d)

/-- **THE ALREADY-NORMAL THEOREM (the v5 starting point):** under the
    discipline, EVERY derivation tree is read-rooted normal. There is no
    normalization to perform because there are no detours to remove -- the
    discipline made them unstatable. v5's job is to introduce structural
    nodes (which create real detours) and prove normalization returns to this
    class while preserving `chainOf`. -/
theorem all_derivs_read_rooted {S : System J Ix} {E : EvidenceCalculus S}
    {P : ContextPolicy J Ctx}
    (hD : EvidenceNeverConcluded S)
    {c c' : Ctx} {j : J}
    (d : Deriv S E P c j c') :
    ReadRooted d := by
  induction d with
  | ax hr => exact ReadRooted.ax
  | cut r ds de ih1 _ =>
      exact ReadRooted.cut ih1 (evidence_derivs_pure hD de ⟨_, _, r⟩)
  | derive hs d ih => exact ReadRooted.derive ih

end LeanProofs.Scratch.DerivationData
