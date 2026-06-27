/-
  LeanProofs.Witnessed.Normalization — the canonical-form theorem that earns the calculus claim:
  every paid freshness path admits a CANONICAL FORM (a carry segment, then a weakening
  segment).

  Custody class: EXPERIMENTAL-WIRING. NOT in defaultTargets; build with
  `lake build Successor`. The `Wired` spine is untouched. No new axiom, no new
  constructor on the judgment, no assumption that already contains the normal form.

  The hinge is the commutation law `weaken ; carry ⟹ carry ; weaken`
  (`perm_weaken_carry`). It holds under the present rules and needs no divergence
  triangle — only `Nat.add_le_add_right`. So normalization was latent in the existing
  rules, not bolted on.

  Both halves are delivered, so "normal form" is not a lossy summary object:
    forward : every paid path factors as `CChain` then `WChain`
    reverse : every such factored pair is itself a paid path
  i.e. `PaidFrom Bridge (inr f) (inr h) ↔ ∃ g, CChain f g ∧ WChain g h`.

  This is the calculus content; it is independent of the model-admission discipline in
  `Discipline` (it imports only the spine, never the discipline).
-/

import LeanProofs.Witnessed.Embedding

namespace LeanProofs.Witnessed.Normalization

open LeanProofs.Witnessed LeanProofs.Witnessed.NoFreeLift

abbrev FreshClaim := Embedding.FreshClaim

/-! ## The two bridge families, named as step relations (definitionally `Bridge`) -/

/-- Carry-forward: advance time inside the window, budget grows by the exact
    divergence spend. Mirrors the first disjunct of `Embedding.Bridge`. -/
def CarryStep (f f' : FreshClaim) : Prop :=
  f.cred = f'.cred
    ∧ Coordinates.Transport (· < ·) (Freshness.credWindow f.cred) f.time f'.time
    ∧ f'.budget = f.budget + Divergence.d f.time f'.time

/-- Budget-weakening: same time, a larger allowance. Mirrors the second disjunct. -/
def WeakenStep (f f' : FreshClaim) : Prop :=
  f.cred = f'.cred ∧ f.time = f'.time ∧ f.budget ≤ f'.budget

/-- A freshness bridge step is exactly carry ∨ weaken — definitionally
    `Embedding.Bridge` on the freshness summand. -/
def FreshStep (f f' : FreshClaim) : Prop := CarryStep f f' ∨ WeakenStep f f'

theorem freshstep_is_bridge {f f' : FreshClaim} :
    FreshStep f f' ↔ Embedding.Bridge (Sum.inr f) (Sum.inr f') := Iff.rfl

/-! ## The hinge — local permutation `weaken ; carry ⟹ carry ; weaken`

    Same endpoints, no extra budget, credential preserved (no freshness
    manufactured), no contraction/exchange (the path is linear). -/

theorem perm_weaken_carry {f g h : FreshClaim}
    (hw : WeakenStep f g) (hc : CarryStep g h) :
    ∃ g', CarryStep f g' ∧ WeakenStep g' h := by
  obtain ⟨hwc, hwt, hwb⟩ := hw
  obtain ⟨hcc, ⟨hct1, hct2⟩, hcb⟩ := hc
  refine ⟨⟨f.cred, h.time, f.budget + Divergence.d f.time h.time⟩, ⟨rfl, ⟨?_, ?_⟩, rfl⟩, ⟨?_, rfl, ?_⟩⟩
  · -- f.time < h.time
    rw [hwt]; exact hct1
  · -- h.time < (window f.cred).hi
    rw [hwc]; exact hct2
  · -- f.cred = h.cred
    rw [hwc]; exact hcc
  · -- f.budget + d f.time h.time ≤ h.budget
    rw [hcb, hwt]; exact Nat.add_le_add_right hwb _

/-! ## Carry-only and weaken-only chains (reflexive-transitive, cons at front) -/

inductive CChain : FreshClaim → FreshClaim → Prop
  | nil  {f} : CChain f f
  | cons {f g h} : CarryStep f g → CChain g h → CChain f h

inductive WChain : FreshClaim → FreshClaim → Prop
  | nil  {f} : WChain f f
  | cons {f g h} : WeakenStep f g → WChain g h → WChain f h

/-- Append a carry at the end of a carry chain. -/
theorem CChain_snoc {f m m' : FreshClaim} (h : CChain f m) : CarryStep m m' → CChain f m' := by
  induction h with
  | nil => intro s; exact CChain.cons s CChain.nil
  | cons hs _ ih => intro s; exact CChain.cons hs (ih s)

/-- Append a weaken at the end of a weaken chain. -/
theorem WChain_snoc {f m m' : FreshClaim} (h : WChain f m) : WeakenStep m m' → WChain f m' := by
  induction h with
  | nil => intro s; exact WChain.cons s WChain.nil
  | cons hs _ ih => intro s; exact WChain.cons hs (ih s)

/-! ## Bubble a single carry to the front of a weaken chain (uses the hinge) -/

theorem bubble {m g : FreshClaim} (hw : WChain m g) :
    ∀ {h}, CarryStep g h → ∃ m', CarryStep m m' ∧ WChain m' h := by
  induction hw with
  | nil => intro h hc; exact ⟨h, hc, WChain.nil⟩
  | @cons a b c hws _ ih =>
      intro h hc
      obtain ⟨k', hck, hwk⟩ := ih hc
      obtain ⟨m', hcm, hpm⟩ := perm_weaken_carry hws hck
      exact ⟨m', hcm, WChain.cons hpm hwk⟩

/-! ## The path judgment (refl-trans of `FreshStep`, step at end) and front-cons -/

inductive FreshPath : FreshClaim → FreshClaim → Prop
  | refl {f} : FreshPath f f
  | step {f g h} : FreshPath f g → FreshStep g h → FreshPath f h

theorem FreshPath_cons {f g h : FreshClaim} (s : FreshStep f g) (p : FreshPath g h) :
    FreshPath f h := by
  induction p with
  | refl => exact FreshPath.step FreshPath.refl s
  | step _ s' ih => exact FreshPath.step ih s'

theorem FreshPath_trans {f g h : FreshClaim} (p : FreshPath f g) (q : FreshPath g h) :
    FreshPath f h := by
  induction q with
  | refl => exact p
  | step _ s ih => exact FreshPath.step ih s

/-! ## Forward: normalization (carry segment, then weaken segment) -/

theorem normalize {f h : FreshClaim} (p : FreshPath f h) :
    ∃ g, CChain f g ∧ WChain g h := by
  induction p with
  | refl => exact ⟨f, CChain.nil, WChain.nil⟩
  | step _ hstep ih =>
      obtain ⟨m, hcm, hwm⟩ := ih
      rcases hstep with hc | hw
      · obtain ⟨m', hcm', hwm'⟩ := bubble hwm hc
        exact ⟨m', CChain_snoc hcm hcm', hwm'⟩
      · exact ⟨m, hcm, WChain_snoc hwm hw⟩

/-! ## Reverse: a factored pair inhabits the path judgment (no lossy summary) -/

theorem CChain_path {f g : FreshClaim} (h : CChain f g) : FreshPath f g := by
  induction h with
  | nil => exact FreshPath.refl
  | cons hs _ ih => exact FreshPath_cons (Or.inl hs) ih

theorem WChain_path {f g : FreshClaim} (h : WChain f g) : FreshPath f g := by
  induction h with
  | nil => exact FreshPath.refl
  | cons hs _ ih => exact FreshPath_cons (Or.inr hs) ih

theorem chains_to_path {f g h : FreshClaim} (hc : CChain f g) (hw : WChain g h) :
    FreshPath f h :=
  FreshPath_trans (CChain_path hc) (WChain_path hw)

/-! ## Connect to the real judgment: `PaidFrom Embedding.Bridge` on freshness -/

theorem path_to_paidfrom {f h : FreshClaim} (p : FreshPath f h) :
    PaidFrom Embedding.Bridge (Sum.inr f) (Sum.inr h) := by
  induction p with
  | refl => exact PaidFrom.refl
  | step _ s ih => exact PaidFrom.step ih (freshstep_is_bridge.mp s)

theorem paidfrom_to_path_aux {f : FreshClaim} {y : Embedding.Claim}
    (p : PaidFrom Embedding.Bridge (Sum.inr f) y) :
    ∀ {h : FreshClaim}, y = Sum.inr h → FreshPath f h := by
  induction p with
  | refl => intro h he; cases he; exact FreshPath.refl
  | @step z y' p' hb ih =>
      intro h he
      subst he
      obtain ⟨⟨z', hz⟩, _⟩ := Embedding.bridge_both_freshness hb
      subst hz
      exact FreshPath.step (ih rfl) (freshstep_is_bridge.mpr hb)

theorem paidfrom_to_path {f h : FreshClaim}
    (p : PaidFrom Embedding.Bridge (Sum.inr f) (Sum.inr h)) : FreshPath f h :=
  paidfrom_to_path_aux p rfl

/-! ## The capstone — both halves, over the real judgment, no `sorry`, no new axiom -/

/-- **bridge_path_normal_form** — every paid freshness path factors as a carry
    segment followed by a weakening segment, AND every such factored pair is a paid
    path. The forward half is the disputed hinge (`bubble` ∘ `perm_weaken_carry`);
    the reverse keeps the normal form inhabiting the original judgment. -/
theorem bridge_path_normal_form {f h : FreshClaim} :
    PaidFrom Embedding.Bridge (Sum.inr f) (Sum.inr h)
      ↔ ∃ g, CChain f g ∧ WChain g h := by
  constructor
  · intro p; exact normalize (paidfrom_to_path p)
  · rintro ⟨g, hc, hw⟩; exact path_to_paidfrom (chains_to_path hc hw)

/-! ## The two-edge corollary

    A cruder shape of the normal form: every path factors through a *single* `m` as
    exactly two `Bridge` edges. That is the segment form PLUS collapse of each segment
    to one edge. Carries collapse because `d a b = b - a` is additive along strictly
    increasing time (`omega`); weakens collapse by transitivity; degenerate (empty)
    segments pad with a reflexive weaken self-loop. So it is a corollary of the segment
    form, not the prize — the canonical theorem is `bridge_path_normal_form` above. -/

/-- A reflexive weaken self-loop is always a bridge (same cred, time, budget). -/
theorem bridge_refl_weaken (f : FreshClaim) :
    Embedding.Bridge (Sum.inr f) (Sum.inr f) := Or.inr ⟨rfl, rfl, Nat.le_refl _⟩

/-- Two carries compose to one — additivity of `d` along increasing time (`omega`),
    not a strengthened constructor. -/
theorem carrystep_compose {f k g : FreshClaim}
    (h1 : CarryStep f k) (h2 : CarryStep k g) : CarryStep f g := by
  obtain ⟨hc1, ⟨ht1a, _⟩, hb1⟩ := h1
  obtain ⟨hc2, ⟨ht2a, ht2b⟩, hb2⟩ := h2
  refine ⟨hc1.trans hc2, ⟨Nat.lt_trans ht1a ht2a, ?_⟩, ?_⟩
  · rw [hc1]; exact ht2b
  · rw [hb2, hb1]; simp only [Divergence.d]; omega

/-- Two weakens compose to one — transitivity. -/
theorem weakenstep_compose {f k g : FreshClaim}
    (h1 : WeakenStep f k) (h2 : WeakenStep k g) : WeakenStep f g := by
  obtain ⟨c1, t1, b1⟩ := h1; obtain ⟨c2, t2, b2⟩ := h2
  exact ⟨c1.trans c2, t1.trans t2, Nat.le_trans b1 b2⟩

/-- A carry chain collapses to refl or a single carry edge. -/
theorem CChain_collapse {f g : FreshClaim} (h : CChain f g) : f = g ∨ CarryStep f g := by
  induction h with
  | nil => exact Or.inl rfl
  | cons hs _ ih =>
      rcases ih with rfl | hcg
      · exact Or.inr hs
      · exact Or.inr (carrystep_compose hs hcg)

/-- A weaken chain collapses to refl or a single weaken edge. -/
theorem WChain_collapse {f g : FreshClaim} (h : WChain f g) : f = g ∨ WeakenStep f g := by
  induction h with
  | nil => exact Or.inl rfl
  | cons hs _ ih =>
      rcases ih with rfl | hwg
      · exact Or.inr hs
      · exact Or.inr (weakenstep_compose hs hwg)

/-- **bridge_path_two_edge_normal_form** — the cruder corollary: every paid freshness
    path factors through a single intermediate `m` as two `Bridge` edges. Derived from
    the segment form + segment collapse + self-loop padding. No `sorry`, no new axiom,
    no strengthened constructor. -/
theorem bridge_path_two_edge_normal_form {f h : FreshClaim}
    (p : PaidFrom Embedding.Bridge (Sum.inr f) (Sum.inr h)) :
    ∃ m : FreshClaim,
      Embedding.Bridge (Sum.inr f) (Sum.inr m)
        ∧ Embedding.Bridge (Sum.inr m) (Sum.inr h) := by
  obtain ⟨g, hc, hw⟩ := normalize (paidfrom_to_path p)
  rcases CChain_collapse hc with rfl | hcs
  · rcases WChain_collapse hw with rfl | hws
    · exact ⟨f, bridge_refl_weaken f, bridge_refl_weaken f⟩
    · exact ⟨f, bridge_refl_weaken f, Or.inr hws⟩
  · rcases WChain_collapse hw with rfl | hws
    · exact ⟨g, Or.inl hcs, bridge_refl_weaken g⟩
    · exact ⟨g, Or.inl hcs, Or.inr hws⟩

end LeanProofs.Witnessed.Normalization
