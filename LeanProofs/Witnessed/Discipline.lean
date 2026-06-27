/-
  LeanProofs.Witnessed.Discipline — the model-admission discipline for the witnessed-derivation
  calculus (1.3 candidate).

  Custody class: EXPERIMENTAL-WIRING. NOT in defaultTargets; build with
  `lake build Successor`. The `Wired` spine is untouched.

  DOCTRINE (load-bearing, do not let the two layers re-collapse):

    `WitnessedDiscipline` governs which *models* `(Sem, B)` are admitted as adequate
    witnesses. It is NOT part of the derivation calculus whose normalization theorem
    (`Normalization.bridge_path_normal_form`) earns the calculus claim. The calculus
    (`Lift`, cut, transport, normalization) is schematic over any kernel/bridge and
    never imports this file. The discipline is a filter beside the calculus, not a
    premise inside it.

  The discipline is FOUR orthogonal axes (a structure, so a failing instance names
  the axis that broke rather than collapsing to "not disciplined"):

    bridge_valid        permitted transport preserves `Sem`            (about B×Sem)
    semantic_nontrivial `Sem` has both a true and a false claim         (about Sem)
    bridge_selective    from one sound source, an edge is ALLOWED and
                        another admissible target is REFUSED            (about B)
    properly_live       there is a sound NON-identity edge              (about B)

  HISTORY: an earlier draft bundled the semantic question under a relational-sounding
  axis `Discriminating`. The obstruction (`Obstruction`) proved
  `Discriminating` carried no information about `B` beyond `bridge_valid` — it was
  semantic non-triviality in costume. The factorization here is that result paid
  forward: the bridge-teeth (`bridge_selective`) and the semantic-range condition
  (`semantic_nontrivial`) are now separate, honestly named axes.
-/

import LeanProofs.Witnessed.NoFreeLift
import LeanProofs.Witnessed.Embedding

namespace LeanProofs.Witnessed.Discipline

open LeanProofs.Witnessed LeanProofs.Witnessed.NoFreeLift

variable {Claim : Type}

/-! ## Cut — genuine multi-hypothesis cut -/

/-- **cut_admissible_general** — if `K ⊢ c` and `K ∪ {c} ⊢ c'`, then `K ⊢ c'`.
    Real cut: the sub-derivation's context is `K` extended by `c`, not the singleton
    `{c}`; it can start from any `K`-member, so it does not collapse to a path. -/
theorem cut_admissible_general
    {K : Claim → Prop} {B : Claim → Claim → Prop} {c c' : Claim}
    (hc : Lift K B c) (hc' : Lift (fun x => K x ∨ x = c) B c') : Lift K B c' := by
  induction hc' with
  | base h =>
      rcases h with hk | he
      · exact Lift.base hk
      · subst he; exact hc
  | cross _ hb ih => exact Lift.cross ih hb

/-! ## Axis: semantic non-triviality (the renamed honest form of the old discrimination) -/

/-- **SemanticNontrivial** — `Sem` is neither empty nor universal: it admits a true
    claim and refuses a false one. A property of the semantics alone (no `B`). -/
def SemanticNontrivial (Sem : Claim → Prop) : Prop :=
  (∃ c, Sem c) ∧ (∃ c, ¬ Sem c)

/-- The always-true semantics is not nontrivial — no `Sem`-false claim. -/
theorem trivial_sem_not_semanticNontrivial : ¬ SemanticNontrivial (fun _ : Claim => True) := by
  rintro ⟨_, _, hnc⟩; exact hnc trivial

/-! ## Axis: bridge selectivity (the real bridge-teeth) -/

/-- **BridgeSelectiveOnSem** — same-source selectivity among `Sem`-admissible
    endpoints: from one source an edge is ALLOWED and another admissible target is
    REFUSED. The refusal is a fact about `B`, not bought by a `Sem`-false target —
    so this genuinely depends on `B` (see `selective_depends_on_B`). -/
def BridgeSelectiveOnSem (Sem : Claim → Prop) (B : Claim → Claim → Prop) : Prop :=
  ∃ a b c, Sem a ∧ Sem b ∧ Sem c ∧ B a b ∧ ¬ B a c

/-- Trivial semantics + universal bridge has no refused target — not selective. -/
theorem trivial_universal_not_selective :
    ¬ BridgeSelectiveOnSem (fun _ : Claim => True) (fun _ _ => True) := by
  rintro ⟨_, _, _, _, _, _, _, hnac⟩; exact hnac trivial

/-- The dead/empty bridge has no allowed edge — not selective. (Dual of the old
    `Discriminating`, which a dead bridge satisfied.) -/
theorem dead_bridge_not_selective {Sem : Claim → Prop} :
    ¬ BridgeSelectiveOnSem Sem (fun _ _ => False) := by
  rintro ⟨_, _, _, _, _, _, hab, _⟩; exact hab

/-- **selective_depends_on_B** — the teeth are real: the SAME semantics gives a
    selective relation (equality) and a non-selective one (universal). So selectivity
    is NOT a function of `Sem` alone — unlike the old `Discriminating`. -/
theorem selective_depends_on_B :
    BridgeSelectiveOnSem (fun _ : Bool => True) (fun x y => x = y)
      ∧ ¬ BridgeSelectiveOnSem (fun _ : Bool => True) (fun _ _ => True) :=
  ⟨⟨true, true, false, trivial, trivial, trivial, rfl, by decide⟩,
   fun ⟨_, _, _, _, _, _, _, hnac⟩ => hnac trivial⟩

/-! ## Axis: liveness — three separated grades -/

/-- **Live** (weakest) — a sound self-loop; only excludes the empty bridge. -/
def Live (Sem : Claim → Prop) (B : Claim → Claim → Prop) : Prop :=
  ∃ c, Sem c ∧ B c c

/-- **NonemptyBridge** — some edge between sound claims. Empty-bridge exclusion. -/
def NonemptyBridge (Sem : Claim → Prop) (B : Claim → Claim → Prop) : Prop :=
  ∃ c c', Sem c ∧ Sem c' ∧ B c c'

/-- **ProperlyLive** (strongest) — a sound NON-identity edge: real transport, not a
    decorative loop. THIS is what the embedding earns. -/
def ProperlyLive (Sem : Claim → Prop) (B : Claim → Claim → Prop) : Prop :=
  ∃ c c', Sem c ∧ Sem c' ∧ c ≠ c' ∧ B c c'

theorem properlyLive_nonempty {Sem : Claim → Prop} {B : Claim → Claim → Prop}
    (h : ProperlyLive Sem B) : NonemptyBridge Sem B := by
  obtain ⟨c, c', hc, hc', _, hb⟩ := h; exact ⟨c, c', hc, hc', hb⟩

theorem nonemptyBridge_not_empty {Sem : Claim → Prop} {B : Claim → Claim → Prop}
    (hEmpty : ∀ a b, ¬ B a b) : ¬ NonemptyBridge Sem B := by
  rintro ⟨c, c', _, _, hb⟩; exact hEmpty c c' hb

/-! ## Selectivity and liveness are INDEPENDENT (positive vs negative bridge witness)

    `ProperlyLive`: there is at least one real allowed transport (positive witness).
    `BridgeSelectiveOnSem`: there is at least one meaningful refusal among otherwise
    sound claims (negative witness). Neither implies the other — both are required,
    and a future failure names which witness is missing. -/

theorem selective_not_implies_properlyLive :
    BridgeSelectiveOnSem (fun _ : Bool => True) (fun x y => x = y)
      ∧ ¬ ProperlyLive (fun _ : Bool => True) (fun x y => x = y) := by
  refine ⟨⟨true, true, false, trivial, trivial, trivial, rfl, by decide⟩, ?_⟩
  rintro ⟨c, c', _, _, hne, hb⟩; exact hne hb

theorem properlyLive_not_implies_selective :
    ProperlyLive (fun _ : Bool => True) (fun _ _ => True)
      ∧ ¬ BridgeSelectiveOnSem (fun _ : Bool => True) (fun _ _ => True) := by
  refine ⟨⟨true, false, trivial, trivial, by decide, trivial⟩, ?_⟩
  rintro ⟨_, _, _, _, _, _, _, hnac⟩; exact hnac trivial

/-! ## The discipline — four orthogonal named fields -/

/-- **WitnessedDiscipline** — bridges preserve `Sem` (`bridge_valid`), the semantics
    is nontrivial (`semantic_nontrivial`), the bridge makes a real choice within the
    sound region (`bridge_selective`), and it performs real non-identity transport
    (`properly_live`). Four independent obligations; the failing field names the axis. -/
structure WitnessedDiscipline (Sem : Claim → Prop) (B : Claim → Claim → Prop) : Prop where
  bridge_valid        : BridgeValid Sem B
  semantic_nontrivial : SemanticNontrivial Sem
  bridge_selective    : BridgeSelectiveOnSem Sem B
  properly_live       : ProperlyLive Sem B

/-- **trivial_rt_closure_excluded** — the trivial RT-closure that satisfied the first
    (too-weak) bundle fails the discipline, and the diagnostic points at the
    *semantic_nontrivial* axis: `Sem := True` has no false claim. (Axiom-free.) -/
theorem trivial_rt_closure_excluded (B : Claim → Claim → Prop) :
    ¬ WitnessedDiscipline (fun _ => True) B :=
  fun hd => trivial_sem_not_semanticNontrivial hd.semantic_nontrivial

/-- **discipline_metatheory** — under a sound floor and the discipline, the judgment is
    sound and provenance-normal, and the discipline carries its model-admission teeth
    (nontrivial semantics, a real refusal, real transport). -/
theorem discipline_metatheory
    {Kernel : Claim → Prop} {B : Claim → Claim → Prop} {Sem : Claim → Prop}
    (hK : ∀ c, Kernel c → Sem c) (hd : WitnessedDiscipline Sem B) :
    (∀ c, Lift Kernel B c → Sem c)
    ∧ (∀ c, Lift Kernel B c → ∃ c₀, Kernel c₀ ∧ PaidFrom B c₀ c)
    ∧ SemanticNontrivial Sem ∧ BridgeSelectiveOnSem Sem B ∧ ProperlyLive Sem B :=
  ⟨fun _ h => paid_lift_sound hK hd.bridge_valid h,
   fun _ h => no_free_lift h, hd.semantic_nontrivial, hd.bridge_selective, hd.properly_live⟩

/-! ## The real model passes all four axes -/

/-- **embedding_semantic_nontrivial** — a green authority claim is `Sem`-true and an
    expired freshness claim is `Sem`-false. -/
theorem embedding_semantic_nontrivial : SemanticNontrivial Embedding.Sem := by
  obtain ⟨a, f, hsa, hnsf, _⟩ := Embedding.cross_axis_unpaid_unsound
  exact ⟨⟨Sum.inl a, hsa⟩, ⟨Sum.inr f, hnsf⟩⟩

/-- **embedding_is_selective** — same credential component: a forward carry edge
    `(t=5)→(t=10)` is allowed, a backward target `(t=2)` is refused (bridges only go
    forward), all three claims `Sem`-true. Genuine same-source selectivity. -/
theorem embedding_is_selective :
    BridgeSelectiveOnSem Embedding.Sem Embedding.Bridge := by
  refine ⟨Sum.inr ⟨⟨0, 20, 0⟩, 5, 10⟩,
          Sum.inr ⟨⟨0, 20, 0⟩, 10, 10 + Divergence.d 5 10⟩,
          Sum.inr ⟨⟨0, 20, 0⟩, 2, 10⟩, ?_, ?_, ?_, ?_, ?_⟩
  · show (0 < 5 ∧ 5 < 20) ∧ Divergence.d 0 5 ≤ 10
    decide
  · show (0 < 10 ∧ 10 < 20) ∧ Divergence.d 0 10 ≤ 10 + Divergence.d 5 10
    decide
  · show (0 < 2 ∧ 2 < 20) ∧ Divergence.d 0 2 ≤ 10
    decide
  · exact Or.inl ⟨rfl, ⟨by decide, by decide⟩, rfl⟩
  · intro hb
    rcases hb with ⟨_, ⟨hlt, _⟩, _⟩ | ⟨_, hte, _⟩
    · exact absurd hlt (by decide)
    · exact absurd hte (by decide)

/-- **embedding_is_properly_live** — a genuine carry-forward edge between two distinct
    `Sem`-true freshness claims (time 5 → 10). NOT a self-loop. -/
theorem embedding_is_properly_live :
    ProperlyLive Embedding.Sem Embedding.Bridge := by
  let c  : Freshness.Cred Nat := ⟨0, 20, 0⟩
  let f  : Embedding.FreshClaim := ⟨c, 5, 10⟩
  let f' : Embedding.FreshClaim := ⟨c, 10, 10 + Divergence.d 5 10⟩
  refine ⟨Sum.inr f, Sum.inr f', ?_, ?_, ?_, ?_⟩
  · show (0 < 5 ∧ 5 < 20) ∧ Divergence.d 0 5 ≤ 10
    decide
  · show (0 < 10 ∧ 10 < 20) ∧ Divergence.d 0 10 ≤ 10 + Divergence.d 5 10
    decide
  · intro h
    exact absurd (congrArg Embedding.FreshClaim.time (Sum.inr.inj h)) (by decide)
  · exact Or.inl ⟨rfl, ⟨by decide, by decide⟩, rfl⟩

/-- **embedding_is_witnessed** — the real freshness embedding satisfies all four axes:
    valid bridges, nontrivial semantics, a real refusal, and real transport. The
    discipline's admitted class is non-empty. -/
theorem embedding_is_witnessed :
    WitnessedDiscipline Embedding.Sem Embedding.Bridge where
  bridge_valid        := Embedding.freshness_bridge_valid
  semantic_nontrivial := embedding_semantic_nontrivial
  bridge_selective    := embedding_is_selective
  properly_live       := embedding_is_properly_live

end LeanProofs.Witnessed.Discipline
