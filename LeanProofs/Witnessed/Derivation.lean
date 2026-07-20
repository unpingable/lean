/-
  LeanProofs.Witnessed.Derivation — the judgment layer of the witnessed-derivation
  calculus (ratified v1.3; now canonical as `LeanProofs.Witnessed.*`).

  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: STABLE-SURFACE
  This unchanged module is part of the v11 stable paid-recomposition import
  closure. Mathlib-free public surface. In the default build; isolate with
  `lake build Witnessed`. It imports only the Mathlib-free
  `LeanProofs.Witnessed.*` spine.
  v14 intentionally records this source under the `witnessed`,
  `custody-indexed`, and `admissibility-calculus` exact roots.

  The calculus is the inductive judgment `Lift K B c` ("claim `c` is derivable from
  admitted floor `K` through the witnessed-bridge relation `B`"), with two rules:
  `Lift.base` (origin) and `Lift.cross` (one paid bridge step). This file exposes it
  as a judgment and supplies the structural metatheorems not already on the spine:
  composition along a paid path, floor monotonicity, and revocation non-manufacture.

  It renames nothing: `no_free_lift`, `paid_lift_sound`, `PaidFrom` are cited as proof
  terms, not aliased. Schema-level throughout (abstract `Claim`/`Kernel`/`Bridge`/`Sem`),
  so every theorem here is axiom-free — verify with `#print axioms`.
-/

import LeanProofs.Witnessed.NoFreeLift

namespace LeanProofs.Witnessed.Derivation

open LeanProofs.Witnessed.NoFreeLift

variable {Claim : Type}

/-! ## Clause 1 — the explicit judgment form `K ⊢[B] c`

    `Lift K B c` already IS the judgment "claim `c` is derivable from admitted
    floor `K` through the witnessed-bridge relation `B`." We only make it legible
    as a judgment; this is `Lift` under a name, not new content. Its two
    constructors are the two inference rules of the calculus:

      * `Lift.base`  — ORIGIN: a floor claim is derivable with no bridge spend.
      * `Lift.cross` — WITNESSED TRANSITION: extend a derivation across one bridge
                       coordinate (the relation IS the receipt; no free cross-rule).
-/

/-- `Derivable K B c` — claim `c` is derivable from floor `K` via bridge relation
    `B`. Definitionally `Lift K B c`; exposed so the judgment reads as a judgment. -/
abbrev Derivable (K : Claim → Prop) (B : Claim → Claim → Prop) (c : Claim) : Prop :=
  Lift K B c

@[inherit_doc] scoped notation:40 K " ⊢[" B "] " c => Derivable K B c

/-! ## Clause 5 — cut / composition admissibility (the genuine new content)

    The old spine proves soundness (`paid_lift_sound`) and provenance
    (`no_free_lift`), but never states cut: that two derivations concatenate
    without inventing authority. These are the missing lemmas. -/

/-- **derivation_extends_along_paid_path** — a derivation may be extended along
    any chain of paid bridges. (Composition in the reachability form.) -/
theorem derivation_extends_along_paid_path
    {K : Claim → Prop} {B : Claim → Claim → Prop} {c c' : Claim}
    (h : Lift K B c) (hpath : PaidFrom B c c') : Lift K B c' := by
  induction hpath with
  | refl => exact h
  | step _ hb ih => exact Lift.cross ih hb

/-- **cut_admissible** — the real cut: if `c` is derivable from `K`, and `c'` is
    derivable from the singleton context `{c}`, then `c'` is derivable from `K`.
    The intermediate claim `c` is eliminated as a hypothesis without any new
    bridge being invented — authority is not manufactured by the cut. -/
theorem cut_admissible
    {K : Claim → Prop} {B : Claim → Claim → Prop} {c c' : Claim}
    (hc : Lift K B c) (hc' : Lift (· = c) B c') : Lift K B c' := by
  induction hc' with
  | base h => exact h ▸ hc
  | cross _ hb ih => exact Lift.cross ih hb

/-! ## Clause 2/5 (revocation placement) — floor monotonicity

    Where does revocation/expiry live — inside the judgment, or as a separate
    relation? The compiled answer: revocation acts on the FLOOR `K`, not on the
    bridge relation `B`. The judgment is monotone in the floor, and a derivation
    always exhibits a live origin, so removing origins removes derivations.
    (Matches canonical `Admissibility/Derivation.lean`, where the `RevocationStore`
    is a premise feeding the verdict, not an inference rule.) -/

/-- **lift_floor_mono** — widening the floor can only widen the derivable set;
    dually, revoking floor members can only shrink it. Revocation is a floor
    operation. -/
theorem lift_floor_mono
    {K K' : Claim → Prop} {B : Claim → Claim → Prop}
    (hsub : ∀ c, K c → K' c) {c : Claim} (h : Lift K B c) : Lift K' B c := by
  induction h with
  | base hk => exact Lift.base (hsub _ hk)
  | cross _ hb ih => exact Lift.cross ih hb

/-! ## Clause 6 — a non-manufacture theorem -/

/-- **revoked_floor_derives_nothing** — if every origin is revoked (the floor is
    empty), no witnessed derivation survives. Bridges cannot resurrect a revoked
    claim: every derivation traces to a live floor origin (`no_free_lift`). This
    is the schema-level non-manufacture result — the calculus invents no standing
    that the floor did not already authorize. -/
theorem revoked_floor_derives_nothing
    {K : Claim → Prop} {B : Claim → Claim → Prop} {c : Claim}
    (hrevoked : ∀ c₀, ¬ K c₀) (h : Lift K B c) : False :=
  let ⟨_, hk, _⟩ := no_free_lift h
  hrevoked _ hk

/-! ## The assembled metatheory

    NOT new soundness/provenance content — an honest *assembly* that exhibits the
    three contract properties holding jointly of the one judgment. The soundness
    and provenance conjuncts are `paid_lift_sound` / `no_free_lift` APPLIED (used
    as proof terms, not renamed); the cut conjunct is the new lemma above. -/

/-- **witnessed_metatheory** — under a sound floor and valid bridges, the `Lift`
    judgment is simultaneously (a) sound, (b) provenance-normal (every derivation
    factors through an admitted origin and a paid path), and (c) closed under cut.
    That conjunction is the metatheory the successor contract asks for. -/
theorem witnessed_metatheory
    {K : Claim → Prop} {B : Claim → Claim → Prop} {Sem : Claim → Prop}
    (hK : ∀ c, K c → Sem c) (hB : BridgeValid Sem B) :
    (∀ c, Lift K B c → Sem c)
    ∧ (∀ c, Lift K B c → ∃ c₀, K c₀ ∧ PaidFrom B c₀ c)
    ∧ (∀ c c', Lift K B c → PaidFrom B c c' → Lift K B c') :=
  ⟨fun _ h => paid_lift_sound hK hB h,
   fun _ h => no_free_lift h,
   fun _ _ h hp => derivation_extends_along_paid_path h hp⟩

end LeanProofs.Witnessed.Derivation
