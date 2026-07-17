/-
  LeanProofs.Witnessed.Embedding — THE WIRE. Authority ⊕ Freshness embedded into the spine.

  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: STABLE-SURFACE
  Stable modeled embedding. This is the only new trust wiring introduces: a
  concrete `Claim := AuthClaim ⊕ FreshClaim` over `(Nat, <, b - a)`, with
  `Kernel`/`Bridge`/`Sem` instances. Everything here is downstream of the schema
  modules; nothing here flows back up into them.

  The customs office instantiated:
    * `Kernel := Sem` — local admission (authority green / fresh-at-(t,M)).
    * `Bridge` — intra-Freshness carry steps ONLY. None on authority; none across
      the summands. The omission of the cross edge is not an oversight: adding it
      is unsound (`NoFreeLift.naked_lift_unsound`, and the original
      `UnifiedAdmissibilityBreaks.bridged_unsound`).

  The wire proper: `freshness_bridge_valid` discharges the spine's `BridgeValid`
  obligation USING `Freshness.freshness_transport_sound` — the validity is paid,
  not assumed. The capstone `freshness_lift_has_freshness_origin` mechanically
  re-derives "no cross-axis laundering": a lifted freshness claim always
  originates from a freshness kernel claim, never from authority.
-/
import LeanProofs.Witnessed.NoFreeLift
import LeanProofs.Witnessed.AuthorityModel
import LeanProofs.Witnessed.Freshness
import LeanProofs.Witnessed.Coordinates
import LeanProofs.Witnessed.Divergence

namespace LeanProofs.Witnessed.Embedding

-- (sibling namespaces `NoFreeLift`, `Authority`, `Freshness`, `Coordinates`,
-- `Divergence` resolve via the enclosing `LeanProofs.Witnessed` namespace — no `open` needed.)

/-- An authority claim: a verdict triple. -/
structure AuthClaim where
  b : AuthorityModel.BasisVerdict
  p : AuthorityModel.PrecedenceVerdict
  s : AuthorityModel.StandingVerdict

/-- A freshness claim: a credential, an evaluation time, and a budget. -/
structure FreshClaim where
  cred   : Freshness.Cred Nat
  time   : Nat
  budget : Nat

/-- The composed claim space: two kernels, side by side. -/
abbrev Claim := AuthClaim ⊕ FreshClaim

/-- Semantics: authority green, or fresh-at-(time, budget). Model `(Nat,<,b-a)`. -/
def Sem : Claim → Prop
  | Sum.inl a => AuthorityModel.authorityVerdict a.b a.p a.s = AuthorityModel.AuthorityVerdict.authorized
  | Sum.inr f => Freshness.FreshAt (· < ·) Divergence.d f.cred f.time f.budget

/-- Bridge coordinates — two intra-freshness families:
    * **carry-forward** (time transport): same credential, a window transport
      receipt, budget grows by the exact divergence spend. The substantive one.
    * **budget-weakening** (ball relaxation): same credential, same time, a
      larger allowance. Sound and syntactically distinct, but (codex) semantically
      just monotonicity of the same ball — a modest second family, not a new
      kernel interaction. Kept to show the bridge slot takes more than one move.
    Still no authority bridge and no cross-summand bridge. -/
def Bridge : Claim → Claim → Prop
  | Sum.inr f, Sum.inr f' =>
      (f.cred = f'.cred
        ∧ Coordinates.Transport (· < ·) (Freshness.credWindow f.cred) f.time f'.time
        ∧ f'.budget = f.budget + Divergence.d f.time f'.time)
      ∨ (f.cred = f'.cred ∧ f.time = f'.time ∧ f.budget ≤ f'.budget)
  | _, _ => False

/-- **The wire.** The spine's `BridgeValid` obligation, discharged for BOTH
    families: carry-forward by `freshness_transport_sound`, weakening by
    `freshAt_budget_mono`. Both bridges are *paid*, not assumed. -/
theorem freshness_bridge_valid : NoFreeLift.BridgeValid Sem Bridge := by
  intro c c' hSem hB
  cases c with
  | inl a => exact hB.elim
  | inr f =>
    cases c' with
    | inl a => exact hB.elim
    | inr f' =>
      show Freshness.FreshAt (· < ·) Divergence.d f'.cred f'.time f'.budget
      rcases hB with ⟨hcred, htrans, hbud⟩ | ⟨hcred, htime, hbud⟩
      · -- carry-forward
        have key := Freshness.freshness_transport_sound (· < ·) Divergence.d
          (fun _ _ _ h1 h2 => Nat.lt_trans h1 h2) Divergence.d_triangle
          hSem htrans (Nat.le_refl (Divergence.d f.time f'.time))
        rw [← hcred, hbud]
        exact key
      · -- budget-weakening
        rw [← hcred, ← htime]
        exact Freshness.freshAt_budget_mono hSem hbud

/-- The operator's local floor is sound when every admitted claim is true.
    (Distinct from `Sem`: this is the non-trivial `hK` obligation. Setting
    `K := Sem` would make it identity and trivialize soundness — codex caught
    exactly that; we keep `K` abstract so the burden is real.) -/
def EnvSound (K : Claim → Prop) : Prop := ∀ c, K c → Sem c

/-- **embedded_lift_sound.** The customs office is sound GIVEN a sound local
    floor (`hK`) and valid bridges (`freshness_bridge_valid`). The `hK` premise
    is a real obligation, not identity — it carries the local-kernel admissibility
    burden the spine's `paid_lift_sound` demands. -/
theorem embedded_lift_sound {K : Claim → Prop} (hK : EnvSound K)
    {c : Claim} (h : NoFreeLift.Lift K Bridge c) : Sem c :=
  NoFreeLift.paid_lift_sound hK freshness_bridge_valid h

/-! ### The composition capstone: no cross-axis laundering -/

/-- No bridge ever targets an authority claim. -/
theorem no_bridge_into_authority (x : Claim) (a : AuthClaim) : ¬ Bridge x (Sum.inl a) := by
  cases x with
  | inl _ => exact fun h => h.elim
  | inr _ => exact fun h => h.elim

/-- No bridge ever crosses authority → freshness. -/
theorem no_authority_to_freshness_bridge (a : AuthClaim) (f : FreshClaim) :
    ¬ Bridge (Sum.inl a) (Sum.inr f) := fun h => h.elim

/-- **authority_is_conservative.** Authority is bridge-inert: any lift reaching
    an authority claim used no bridge — it is just the local kernel fact `K`.
    (Over abstract `K`, so non-vacuous.) -/
theorem authority_is_conservative {K : Claim → Prop} {a : AuthClaim}
    (h : NoFreeLift.Lift K Bridge (Sum.inl a)) : K (Sum.inl a) := by
  cases h with
  | base hk => exact hk
  | cross _ hb => exact (no_bridge_into_authority _ a hb).elim

/-- A bridge always has freshness on both ends. -/
theorem bridge_both_freshness {x y : Claim} (h : Bridge x y) :
    (∃ f, x = Sum.inr f) ∧ (∃ f', y = Sum.inr f') := by
  cases x with
  | inl _ => exact h.elim
  | inr f =>
    cases y with
    | inl _ => exact h.elim
    | inr f' => exact ⟨⟨f, rfl⟩, ⟨f', rfl⟩⟩

/-- A paid chain reaching a freshness claim must have started at a freshness
    claim — bridges never leave the freshness summand. -/
theorem paidfrom_freshness_origin {c₀ y : Claim}
    (h : NoFreeLift.PaidFrom Bridge c₀ y) : (∃ f, y = Sum.inr f) → ∃ f₀, c₀ = Sum.inr f₀ := by
  induction h with
  | refl => exact fun hy => hy
  | step _hpath hb ih => exact fun _ => ih (bridge_both_freshness hb).1

/-- **freshness_lift_has_freshness_origin** — a lifted freshness claim always
    originates from a freshness kernel claim, via a chain of paid freshness
    bridges. Authority never launders into freshness.

    HONESTY (codex): this is true largely BY DESIGN — `Bridge` is definitionally
    `False` across the summands, and this theorem propagates that choice through
    `no_free_lift`. The non-trivial content is therefore NOT here; it is the
    JUSTIFICATION for the design: adding the cross edge is unsound
    (`NoFreeLift.naked_lift_unsound`, and `UnifiedAdmissibilityBreaks.bridged_unsound`).
    So read this theorem as "the customs office *enforces* the no-cross-edge
    decision," not "the office *discovers* that no cross edge can exist." -/
theorem freshness_lift_has_freshness_origin {K : Claim → Prop} {f : FreshClaim}
    (h : NoFreeLift.Lift K Bridge (Sum.inr f)) :
    ∃ f₀, K (Sum.inr f₀) ∧ NoFreeLift.PaidFrom Bridge (Sum.inr f₀) (Sum.inr f) := by
  obtain ⟨c₀, hk, hpath⟩ := NoFreeLift.no_free_lift h
  obtain ⟨f₀, rfl⟩ := paidfrom_freshness_origin hpath ⟨f, rfl⟩
  exact ⟨f₀, hk, hpath⟩

/-! ### Step 3: the authority↔freshness interaction edge — why it can't be paid

The composition omits the cross edge `authorized ⇒ fresh`. This section shows
that omission is FORCED: the unpaid edge is unsound, and no sound bridge can pay
for it, because authority-green carries no information about time or divergence.
This is the original `bridged_unsound` / "opacity is the fence", now a property
of the wired customs office. -/

/-- The would-be cross calculus: base + an UNPAID `authorized ⇒ fresh` jump. -/
inductive CrossNaked : Claim → Prop
  | base {c} : Sem c → CrossNaked c
  | crossJump {a f} : CrossNaked (Sum.inl a) → CrossNaked (Sum.inr f)

/-- **cross_axis_unpaid_unsound.** A concrete green authority claim and an
    expired freshness claim: the unpaid `authorized ⇒ fresh` jump derives a
    FALSE freshness claim. The interaction edge cannot be free. -/
theorem cross_axis_unpaid_unsound :
    ∃ (a : AuthClaim) (f : FreshClaim),
      Sem (Sum.inl a) ∧ ¬ Sem (Sum.inr f) ∧ CrossNaked (Sum.inr f) := by
  refine ⟨⟨.admissibleBasis, .resolved, .standing⟩, ⟨⟨0, 3, 0⟩, 5, 0⟩, ?_, ?_, ?_⟩
  · exact AuthorityModel.green_triple_authorizes
  · show ¬ Freshness.FreshAt (· < ·) Divergence.d ⟨0, 3, 0⟩ 5 0; decide
  · exact CrossNaked.crossJump
      (CrossNaked.base (c := Sum.inl ⟨.admissibleBasis, .resolved, .standing⟩)
        AuthorityModel.green_triple_authorizes)

/-- **cross_bridge_cannot_be_valid.** Any bridge edge from a green authority
    claim to an unfresh freshness claim FAILS `BridgeValid`: a valid bridge would
    force the freshness claim true, contradicting its unfreshness. -/
theorem cross_bridge_cannot_be_valid
    (B : Claim → Claim → Prop) (a : AuthClaim) (f : FreshClaim)
    (hgreen : Sem (Sum.inl a)) (hunfresh : ¬ Sem (Sum.inr f))
    (hedge : B (Sum.inl a) (Sum.inr f)) :
    ¬ NoFreeLift.BridgeValid Sem B := by
  intro hvalid
  exact hunfresh (hvalid _ _ hgreen hedge)

/-- **valid_cross_bridge_is_redundant** — the OTHER horn (codex's caveat made a
    theorem). A *valid* authority→freshness bridge edge can only target a freshness
    claim that is ALREADY true: authority cannot manufacture freshness it has no
    evidence for, it can at most re-assert freshness that already holds. So a
    sound cross edge adds no reach. -/
theorem valid_cross_bridge_is_redundant
    (B : Claim → Claim → Prop) (hvalid : NoFreeLift.BridgeValid Sem B)
    (a : AuthClaim) (f : FreshClaim)
    (hgreen : Sem (Sum.inl a)) (hedge : B (Sum.inl a) (Sum.inr f)) :
    Sem (Sum.inr f) :=
  hvalid _ _ hgreen hedge

/-- **cross_edge_dichotomy** — step 3, honestly scoped (NOT "unpayable
    universally"; codex flagged that overclaim). The authority→freshness edge
    obeys the original `no_sound_calculus_adds_power` dichotomy, localized:

      * UNPAID — concretely UNSOUND: it reaches a false freshness claim
        (`cross_axis_unpaid_unsound`); and any bridge firing on a green-authority
        / false-freshness pair fails `BridgeValid` (`cross_bridge_cannot_be_valid`).
      * VALID — necessarily REDUNDANT: it can only target already-true freshness
        (`valid_cross_bridge_is_redundant`), so it adds nothing.

    There is no authority→freshness edge that is both sound AND adds freshness
    reach. That — not "no edge exists" — is why the kernels don't interact:
    a sound interaction would be empty, a non-empty one unsound. Opacity is the
    fence, at the embedding level. -/
theorem cross_edge_dichotomy :
    -- unpaid horn: a green authority and a false freshness claim, with any
    -- bridge between them failing validity ...
    (∃ (a : AuthClaim) (f : FreshClaim),
        Sem (Sum.inl a) ∧ ¬ Sem (Sum.inr f)
        ∧ ∀ (B : Claim → Claim → Prop),
            B (Sum.inl a) (Sum.inr f) → ¬ NoFreeLift.BridgeValid Sem B)
    -- ... and valid horn: every valid cross edge from a green authority lands on
    -- an already-true freshness claim (redundant).
    ∧ (∀ (B : Claim → Claim → Prop), NoFreeLift.BridgeValid Sem B →
        ∀ a f, Sem (Sum.inl a) → B (Sum.inl a) (Sum.inr f) → Sem (Sum.inr f)) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨a, f, hg, hnf, _⟩ := cross_axis_unpaid_unsound
    exact ⟨a, f, hg, hnf, fun B hedge => cross_bridge_cannot_be_valid B a f hg hnf hedge⟩
  · exact fun B hvalid a f hg hedge => valid_cross_bridge_is_redundant B hvalid a f hg hedge

end LeanProofs.Witnessed.Embedding
