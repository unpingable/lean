/-
  Admissibility.PathVerdict.Edges  --  the edge layer and the fold tether
  EXTRACTED 2026-07-02 from private skunkworks (formalization/Calculi/
  SeamPathVerdict/), Tier-1 extraction per that repo's publication posture
  table (Path Verdict core + edge fold/tether = the two "Yes" rows; Domains/
  Located are the noted second wave; everything Tier-0 — domain obstruction
  taxonomies, NQ/AG integration, MixedPipeline, weathering ledgers, linear
  spend, nightshift — stays private). Skunkworks provenance: multiple codex
  review passes there; recompiled and axiom-re-attested here on arrival.

  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: STABLE-SURFACE
  This module is part of the exact `LeanProofs.Admissibility.PathVerdict`
  stable root. v13 completes the earlier skunkworks extraction by correcting
  its public path and custody record without changing theorem bodies.

  TIER-1 SCOPE (brutal, binding on any public claim): this proves that
  obstruction is preserved across composition, that authority requires a
  zero-obstruction log, and that folds preserve the authority semantics of
  evaluated edges. It does NOT prove: that any real system emitted correct
  edge verdicts; that NQ/AG/Porter are correct; that an obstruction is
  morally bad or permanently tainted; that remediation is automatic; or that
  collection should be blocked.

  OVERLAP NOTE (C3 hygiene, checked at extraction): the verdict algebra
  (obstruction-log free monoid + fold/tether) is DIFFERENT MACHINERY from
  the resident custody-indexed sequents (derivability walls) and the
  jurisdiction screen (rule-shape inspection) — adjacent doctrine ("no
  laundering by composition"), disjoint proof objects. Any future bridge
  between the two is its own slice, not implied.

  Core proves the verdict algebra: given an obstruction log, composition
  cannot erase obstruction. Complete — but one layer short. It does not yet
  prove that FOLDING a path of evaluated edges into a log preserves authority
  semantics. Without that tether, the diagnostic artifact and the authority
  proof could drift: a fold could hide bad edges and mint a clean verdict.

  This module seals the seam:

  * `fold_append`         — folding respects path concatenation (the fold is a
                            monoid homomorphism into `PathVerdict δ`).
  * `fold_authority_iff`  — **the tether**: the folded verdict is
                            authority-bearing iff every edge in the path was.
                            Checking `obstructions = []` is mathematically
                            equivalent to exhaustive inspection of the path.
  * `authority_append_iff` — the bank-account theorem at the edge layer.
  * `fold_clean_iff_all_bridge` — the anti-laundering lock: a clean verdict
                            cannot be produced by hiding bad edges during fold.

  Note what the fold deliberately loses: `filterMap` strips bridge edges, so a
  composed verdict refuses to tell you how much good stuff happened. It is
  mathematically blind to the volume of clean computation; it tracks only the
  surface area of rot. You cannot recover clean edges from the log. Good — the
  verdict preserves the admissibility boundary, not the whole transcript.
-/

import LeanProofs.Admissibility.PathVerdict.Core

namespace Admissibility.PathVerdict

/-! ## Edges -/

/-- An evaluated edge either bridges (may carry authority) or carries exactly
    one obstruction. There is no third state — "unevaluated" is itself the
    core obstruction `unlabeled`, not a hole in the type. -/
inductive EdgeVerdict (δ : Type) where
  | bridge     : EdgeVerdict δ
  | obstructed : ObstructionKind δ → EdgeVerdict δ
deriving DecidableEq, Repr

/-- The obstruction an edge contributes to the log, if any. -/
def EdgeVerdict.obstruction? {δ : Type} :
    EdgeVerdict δ → Option (ObstructionKind δ)
  | .bridge       => none
  | .obstructed o => some o

/-- Edge-level authority: only a bridge bears it. -/
def EdgeVerdict.AuthorityBearing {δ : Type} : EdgeVerdict δ → Prop
  | .bridge       => True
  | .obstructed _ => False

/-- Path-level authority stated directly over the edges: every edge bridges. -/
def PathAuthorityBearing {δ : Type} (edges : List (EdgeVerdict δ)) : Prop :=
  ∀ e ∈ edges, e.AuthorityBearing

/-- Evaluate a path into its verdict: collect the obstructions, discard the
    bridges. The diagnostic object a runtime actually ships around. -/
def foldToVerdict {δ : Type} (edges : List (EdgeVerdict δ)) : PathVerdict δ :=
  ⟨edges.filterMap EdgeVerdict.obstruction?⟩

/-! ## The fold is a homomorphism -/

/-- Folding respects concatenation: evaluating `p ++ q` is composing the
    evaluations. The runtime may fold segments independently and compose the
    verdicts — no information about obstruction is lost to the seam. -/
theorem fold_append {δ : Type} (p q : List (EdgeVerdict δ)) :
    foldToVerdict (p ++ q) = (foldToVerdict p).compose (foldToVerdict q) := by
  simp [foldToVerdict, PathVerdict.compose]

/-- Folding the empty path yields the clean verdict. -/
theorem fold_nil {δ : Type} :
    foldToVerdict ([] : List (EdgeVerdict δ)) = PathVerdict.clean := rfl

/-! ## The tether -/

/-- Pointwise tether: an edge contributes nothing to the log iff it bears
    authority. The whole fold seal reduces to this case split. -/
theorem obstruction?_eq_none_iff {δ : Type} (e : EdgeVerdict δ) :
    e.obstruction? = none ↔ e.AuthorityBearing := by
  cases e <;> simp [EdgeVerdict.obstruction?, EdgeVerdict.AuthorityBearing]

/-- **The tether theorem.** The folded verdict bears authority iff every edge
    in the path does. This is the hard seal between the diagnostic layer and
    the authority layer: a consumer holding only the `PathVerdict` and
    checking `obstructions = []` has, mathematically, exhaustively inspected
    the path. -/
theorem fold_authority_iff {δ : Type} (edges : List (EdgeVerdict δ)) :
    (foldToVerdict edges).AuthorityBearing ↔ PathAuthorityBearing edges := by
  -- Hand-rolled induction: the simp route detours through core `filterMap`
  -- lemmas that drag in `Quot.sound`, and the repo invariant is propext-only
  -- flagships.
  induction edges with
  | nil =>
      exact ⟨fun _ e he => (nomatch he), fun _ => rfl⟩
  | cons head tail ih =>
      cases head with
      | bridge =>
          constructor
          · intro h e he
            cases he with
            | head => exact trivial
            | tail _ hmem => exact ih.mp h e hmem
          · intro h
            exact ih.mpr fun e he => h e (List.Mem.tail _ he)
      | obstructed o =>
          constructor
          · intro h
            exact absurd
              (show o :: (foldToVerdict tail).obstructions
                    = ([] : List (ObstructionKind δ)) from h)
              (List.cons_ne_nil _ _)
          · intro h
            exact False.elim (h (EdgeVerdict.obstructed o) (List.Mem.head _))

/-- **The bank-account theorem at the edge layer.** The fold of `p ++ q`
    bears authority iff the folds of `p` and `q` both do. A clean suffix
    cannot sanitize a dirty prefix, and conversely. -/
theorem authority_append_iff {δ : Type} (p q : List (EdgeVerdict δ)) :
    (foldToVerdict (p ++ q)).AuthorityBearing ↔
      (foldToVerdict p).AuthorityBearing ∧
      (foldToVerdict q).AuthorityBearing := by
  rw [fold_append]
  exact authority_compose_iff _ _

/-! ## Anti-laundering locks -/

/-- An edge bears authority iff it is literally a bridge. -/
theorem edge_authority_iff_bridge {δ : Type} (e : EdgeVerdict δ) :
    e.AuthorityBearing ↔ e = EdgeVerdict.bridge := by
  cases e <;> simp [EdgeVerdict.AuthorityBearing]

/-- **The lock.** A clean verdict cannot be produced by hiding bad edges
    during fold: the fold is clean iff every edge was a bridge, syntactically.
    This is the theorem that makes the shipped `PathVerdict` trustworthy as a
    proxy for the path it summarizes. -/
theorem fold_clean_iff_all_bridge {δ : Type} (edges : List (EdgeVerdict δ)) :
    (foldToVerdict edges).AuthorityBearing ↔
      ∀ e ∈ edges, e = EdgeVerdict.bridge := by
  rw [fold_authority_iff]
  exact forall₂_congr fun e _ => edge_authority_iff_bridge e

/-- An obstructed edge's obstruction is never dropped by the fold — it
    appears in the shipped log. Positive negative evidence: the receipt of
    the breach survives into the artifact. -/
theorem fold_carries_obstruction {δ : Type} {edges : List (EdgeVerdict δ)}
    {o : ObstructionKind δ} (h : EdgeVerdict.obstructed o ∈ edges) :
    o ∈ (foldToVerdict edges).obstructions := by
  induction edges with
  | nil => cases h
  | cons head tail ih =>
      cases h with
      | head =>
          show o ∈ o :: (foldToVerdict tail).obstructions
          exact List.Mem.head _
      | tail _ hmem =>
          cases head with
          | bridge => exact ih hmem
          | obstructed o' =>
              show o ∈ o' :: (foldToVerdict tail).obstructions
              exact List.Mem.tail _ (ih hmem)

/-- One obstructed edge anywhere in the path kills the folded verdict. The
    edge-layer restatement of `clean_plumbing_cannot_bridge_dirty_seam` from
    the skunkworks first-stratum `PathVerdict` (private, not extracted) — now with the receipt preserved. -/
theorem obstructed_edge_blocks_fold {δ : Type} {edges : List (EdgeVerdict δ)}
    {o : ObstructionKind δ} (h : EdgeVerdict.obstructed o ∈ edges) :
    ¬ (foldToVerdict edges).AuthorityBearing :=
  obstruction_blocks_authority (fold_carries_obstruction h)

/-! ## Instantiation smoke test

    The δ parameter is the whole point of the Core design; one toy domain
    proves the extension seam actually instantiates. Domain obstruction
    vocabularies for real consumers (NQ, AG) live with those consumers, not
    here. -/

namespace Demo

/-- A toy domain vocabulary standing in for an NQ-shaped consumer. -/
inductive ToyObstruction where
  | staleEvidence
  | retiredBasis
deriving DecidableEq, Repr

/-- A domain obstruction blocks authority through the generic law — no
    domain-specific theorem needed. -/
example :
    ¬ (foldToVerdict
        [ EdgeVerdict.bridge,
          EdgeVerdict.obstructed (.domain ToyObstruction.retiredBasis),
          EdgeVerdict.bridge ]).AuthorityBearing := by
  decide

/-- A core obstruction blocks identically in an instantiated domain. -/
example :
    ¬ (foldToVerdict
        [ EdgeVerdict.bridge,
          EdgeVerdict.obstructed
            (.core CoreObstruction.refusedLaundering : ObstructionKind ToyObstruction) ]).AuthorityBearing := by
  decide

/-- All-bridge paths fold clean. -/
example :
    (foldToVerdict
        ([EdgeVerdict.bridge, EdgeVerdict.bridge] :
          List (EdgeVerdict ToyObstruction))).AuthorityBearing := by
  decide

end Demo

end Admissibility.PathVerdict
