/-
  Custody-Class: SCRATCH

  WitnessedResourceSequent -- fenced scratch slice.

  Occurrence-sensitive resource sequents over the Witnessed Derivation Calculus.
  Not imported by `LeanProofs.lean`. Not part of `LeanProofs.Witnessed`.
  Not a public surface and not a promotion claim.

  This is the contrast layer for `LeanProofs.Witnessed.Sequent`: there, a
  context is folded into the persistent WDC floor by membership; here, the input
  list is linear. Claim and bridge formula occurrences can be consumed. Residue
  occurrences cannot.

  Scope fence. This file intentionally has only three formula forms:
  local claims, bridge tokens, and opaque residue. It does not add refusal,
  revocation, custody, freshness, or a formula grammar for authority. Compile is
  contact only.

  `Split` non-determinism (scope fence). `Split consumed residual input` and
  `Consumes token input residual` assert that SOME occurrence-preserving
  interleaving exists, not a canonical/leftmost one. With no `DecidableEq` on
  `Formula`, an input with duplicate-shaped formulas admits several valid
  `(consumed, residual)` pairs, so `Derives.hyp` is an EXISTENCE judgment, not a
  deterministic accounting function. A deterministic, position-pinned checker is a
  separate result (see `WitnessedResourceChecker.lean`, which pins consumption by
  index via `removeAt` and proves it refines `Split`); do not read consumption here
  as canonical.

  Prior art (substrate is well-charted). Persistent floor `K` + linear context
  `Gamma` is the dual-context split (DILL, Barber-Plotkin); threading a residual
  `Delta` as leftover is the Hodas-Miller input/output model of linear context
  management. The persistent floor is the `!`-zone / exponential ("of course")
  modality of linear logic in ordinary vocabulary; `floor` is kept as established
  corpus vocabulary (cite, do not rename). These are citations to make the layer
  legible to proof theorists, not new machinery.

  Mathlib-free: imports only the Mathlib-free Witnessed sequent layer.
-/

import LeanProofs.Witnessed.Sequent

namespace LeanProofs.Scratch.WitnessedResourceSequent

/-! ## Syntax -/

/-- Resource formulas: local claim assumptions, one-use bridge tokens, and opaque
    residue that must survive derivations unchanged. -/
inductive Formula (Claim Residue : Type) where
  | claim : Claim -> Formula Claim Residue
  | bridge : Claim -> Claim -> Formula Claim Residue
  | residue : Residue -> Formula Claim Residue

/-- Linear context. Occurrences matter; no `DecidableEq` is required. -/
abbrev Context (Claim Residue : Type) := List (Formula Claim Residue)

/-! ## Split / consumption -/

/-- `Split consumed residual input` means `input` is an occurrence-preserving
    interleaving of the consumed resources and the residual resources. This is
    the no-`DecidableEq` replacement for deleting a token by equality lookup. -/
inductive Split {α : Type} : List α -> List α -> List α -> Prop where
  | nil : Split [] [] []
  | left {x : α} {consumed residual input : List α} :
      Split consumed residual input ->
        Split (x :: consumed) residual (x :: input)
  | right {x : α} {consumed residual input : List α} :
      Split consumed residual input ->
        Split consumed (x :: residual) (x :: input)

/-- Consuming exactly one token. -/
abbrev Consumes {α : Type} (token : α) (input residual : List α) : Prop :=
  Split [token] residual input

/-- Prefix extra resources on the residual side of a split. This is the local
    accounting move behind admissible resource weakening: the extra resources
    are not consumed; they are carried through. -/
theorem split_residual_prefix
    {α : Type} {consumed residual input : List α}
    (extra : List α)
    (h : Split consumed residual input) :
    Split consumed (extra ++ residual) (extra ++ input) := by
  induction extra with
  | nil =>
      exact h
  | cons x xs ih =>
      exact Split.right ih

/-- Anything consumed by the left side of a split occurred in the original input. -/
theorem mem_input_of_mem_consumed
    {α : Type} {consumed residual input : List α} {x : α}
    (h : Split consumed residual input) :
    x ∈ consumed -> x ∈ input := by
  intro hx
  induction h with
  | nil =>
      cases hx
  | left h ih =>
      cases hx with
      | head =>
          exact List.Mem.head _
      | tail _ hxTail =>
          exact List.Mem.tail _ (ih hxTail)
  | right h ih =>
      exact List.Mem.tail _ (ih hx)

/-- Anything left in the residual side of a split occurred in the original input. -/
theorem mem_input_of_mem_residual
    {α : Type} {consumed residual input : List α} {x : α}
    (h : Split consumed residual input) :
    x ∈ residual -> x ∈ input := by
  intro hx
  induction h with
  | nil =>
      cases hx
  | left h ih =>
      exact List.Mem.tail _ (ih hx)
  | right h ih =>
      cases hx with
      | head =>
          exact List.Mem.head _
      | tail _ hxTail =>
          exact List.Mem.tail _ (ih hxTail)

/-- If an occurrence in the input is not one of the consumed occurrences, it is
    present in the residual output. This is the preservation engine for residue. -/
theorem mem_residual_of_mem_input_not_consumed
    {α : Type} {consumed residual input : List α} {x : α}
    (h : Split consumed residual input)
    (hnot : forall y, y ∈ consumed -> x ≠ y)
    (hin : x ∈ input) :
    x ∈ residual := by
  induction h with
  | nil =>
      cases hin
  | left h ih =>
      cases hin with
      | head =>
          exact False.elim (hnot _ (List.Mem.head _) rfl)
      | tail _ hinTail =>
          exact ih
            (fun y hy => hnot y (List.Mem.tail _ hy))
            hinTail
  | right h ih =>
      cases hin with
      | head =>
          exact List.Mem.head _
      | tail _ hinTail =>
          exact List.Mem.tail _ (ih hnot hinTail)

/-! ## Claim erasure -/

/-- Keep only local claim assumptions, erasing bridge tokens and residue. -/
def claimAssumptions {Claim Residue : Type} :
    Context Claim Residue -> List Claim
  | [] => []
  | Formula.claim c :: rest => c :: claimAssumptions rest
  | Formula.bridge _ _ :: rest => claimAssumptions rest
  | Formula.residue _ :: rest => claimAssumptions rest

theorem claim_mem_claimAssumptions_of_formula_mem
    {Claim Residue : Type} {Gamma : Context Claim Residue} {c : Claim}
    (h : Formula.claim c ∈ Gamma) :
    c ∈ claimAssumptions Gamma := by
  induction Gamma with
  | nil =>
      cases h
  | cons f rest ih =>
      cases f with
      | claim d =>
          simp [claimAssumptions] at h ⊢
          cases h with
          | inl hcd => exact Or.inl hcd
          | inr htail => exact Or.inr (ih htail)
      | bridge _ _ =>
          simp [claimAssumptions] at h ⊢
          exact ih h
      | residue _ =>
          simp [claimAssumptions] at h ⊢
          exact ih h

/-! ## Resource derivations -/

/--
  `Derives K B Gamma c Delta` reads:

    from persistent floor `K` and linear input `Gamma`, derive claim `c`,
    leaving residual context `Delta`.

  `floor` reads from persistent `K` and does not consume linear input.
  `hyp` consumes one local claim occurrence.
  `bridge` first derives `c`, then consumes one bridge token `bridge c c'`.
-/
inductive Derives
    {Claim Residue : Type}
    (K : Claim -> Prop) (B : Claim -> Claim -> Prop) :
    Context Claim Residue -> Claim -> Context Claim Residue -> Prop where
  | floor {Gamma : Context Claim Residue} {c : Claim} :
      K c -> Derives K B Gamma c Gamma
  | hyp {Gamma Delta : Context Claim Residue} {c : Claim} :
      Consumes (Formula.claim c) Gamma Delta ->
        Derives K B Gamma c Delta
  | bridge
      {Gamma Gamma' Delta : Context Claim Residue} {c c' : Claim} :
      Derives K B Gamma c Gamma' ->
        B c c' ->
        Consumes (Formula.bridge c c') Gamma' Delta ->
          Derives K B Gamma c' Delta

/-! ## Certificate shapes -/

/-- The rule a resource receipt claims was applied. This is metadata only; it is
    not a checker and does not construct a `Derives` proof. -/
inductive RuleApplied (Claim : Type) where
  | floor (c : Claim)
  | hyp (c : Claim)
  | bridge (source target : Claim)

/-- Reasons a bridge-spend receipt can be denied. Kept intentionally narrow for
    this scratch slice: bridge validity is separate from spend-token presence. -/
inductive BridgeSpendDenial (Claim : Type) where
  | missingToken (source target : Claim)

/-- Resource derivation certificate shape.

    `input` and `output` record the resource contexts around the step/derivation;
    `consumed` records the formula spent by the step when one was spent; `rule`
    records the rule claimed. The `bridgeSpendDenied` variant records a failed
    bridge spend without pretending to be a checker result. -/
inductive ResourceCertificate (Claim Residue : Type) where
  | applied
      (input output : Context Claim Residue)
      (consumed : Option (Formula Claim Residue))
      (rule : RuleApplied Claim)
  | bridgeSpendDenied
      (input output : Context Claim Residue)
      (consumed : Option (Formula Claim Residue))
      (source target : Claim)
      (denial : BridgeSpendDenial Claim)

/-- Canonical denied-spend receipt for the no-token case. -/
def missingBridgeTokenCertificate
    {Claim Residue : Type}
    (input output : Context Claim Residue)
    (source target : Claim) : ResourceCertificate Claim Residue :=
  ResourceCertificate.bridgeSpendDenied
    input output none source target (BridgeSpendDenial.missingToken source target)

/-- Resource derivations never create residual formulas: every output occurrence
    occurred in the original input. -/
theorem residual_mem_input
    {Claim Residue : Type}
    {K : Claim -> Prop} {B : Claim -> Claim -> Prop}
    {Gamma Delta : Context Claim Residue} {c : Claim}
    (h : Derives K B Gamma c Delta) :
    forall {f : Formula Claim Residue}, f ∈ Delta -> f ∈ Gamma := by
  intro f hf
  induction h with
  | floor _ =>
      exact hf
  | hyp hconsume =>
      exact mem_input_of_mem_residual hconsume hf
  | bridge hder _ hconsume ih =>
      exact ih (mem_input_of_mem_residual hconsume hf)

/-! ## Admissible structural transformations -/

/-- Admissible affine weakening by prefix.

    Extra linear resources may be added to the input only by this proved
    transformation, not by a primitive `Derives` rule. The transformation carries
    the extra resources through untouched, so the output is prefixed by the same
    `extra`. -/
theorem weaken_prefix_admissible
    {Claim Residue : Type}
    {K : Claim -> Prop} {B : Claim -> Claim -> Prop}
    {Gamma Delta : Context Claim Residue} {c : Claim}
    (extra : Context Claim Residue)
    (h : Derives K B Gamma c Delta) :
    Derives K B (extra ++ Gamma) c (extra ++ Delta) := by
  induction h with
  | floor hk =>
      exact Derives.floor hk
  | hyp hconsume =>
      exact Derives.hyp (split_residual_prefix extra hconsume)
  | bridge _ hb hconsume ih =>
      exact Derives.bridge ih hb (split_residual_prefix extra hconsume)

/-! ## Residue preservation -/

private theorem residue_not_consumed_by_claim
    {Claim Residue : Type} (c : Claim) (r : Residue) :
    forall y, y ∈ [Formula.claim c] -> Formula.residue r ≠ y := by
  intro y hy hEq
  simp at hy
  cases hy
  cases hEq

private theorem residue_not_consumed_by_bridge
    {Claim Residue : Type} (c c' : Claim) (r : Residue) :
    forall y, y ∈ [Formula.bridge c c'] -> Formula.residue r ≠ y := by
  intro y hy hEq
  simp at hy
  cases hy
  cases hEq

/-- Residue cannot be consumed by any rule in this scratch system. -/
theorem residue_preserved
    {Claim Residue : Type}
    {K : Claim -> Prop} {B : Claim -> Claim -> Prop}
    {Gamma Delta : Context Claim Residue} {c : Claim} {r : Residue}
    (h : Derives K B Gamma c Delta) :
    Formula.residue r ∈ Gamma -> Formula.residue r ∈ Delta := by
  intro hres
  induction h with
  | floor _ =>
      exact hres
  | hyp hconsume =>
      exact mem_residual_of_mem_input_not_consumed hconsume
        (residue_not_consumed_by_claim _ _)
        hres
  | bridge hder _ hconsume ih =>
      exact mem_residual_of_mem_input_not_consumed hconsume
        (residue_not_consumed_by_bridge _ _ _)
        ih

/-! ## Erasure to ordinary WDC sequents -/

/-- Every resource derivation erases to the ordinary membership-context WDC
    sequent using only the local claim assumptions present in the original
    input context. Bridge tokens are discharged by the resource derivation and
    become ordinary WDC bridge steps. -/
theorem erases_to_sequent
    {Claim Residue : Type}
    {K : Claim -> Prop} {B : Claim -> Claim -> Prop}
    {Gamma Delta : Context Claim Residue} {c : Claim}
    (h : Derives K B Gamma c Delta) :
    LeanProofs.Witnessed.Sequent.Derivable K B (claimAssumptions Gamma) c := by
  induction h with
  | floor hk =>
      exact LeanProofs.Witnessed.Sequent.floor hk
  | hyp hconsume =>
      have hFormula :=
        mem_input_of_mem_consumed hconsume (List.Mem.head _)
      exact LeanProofs.Witnessed.Sequent.hyp
        (claim_mem_claimAssumptions_of_formula_mem hFormula)
  | bridge _ hb _ ih =>
      exact LeanProofs.Witnessed.Sequent.cross ih hb

/-! ## No-contraction specimen -/

/-- With empty persistent floor and empty bridge relation, no derivation can
    start from an empty linear context. -/
theorem empty_input_derives_nothing
    {Claim Residue : Type} {c : Claim} {Delta : Context Claim Residue} :
    ¬ Derives
        (fun _ : Claim => False)
        (fun _ _ : Claim => False)
        ([] : Context Claim Residue) c Delta := by
  intro h
  cases h with
  | floor hk =>
      exact hk
  | hyp hconsume =>
      cases hconsume
  | bridge _ hb _ =>
      exact hb

private theorem claim_eq_of_mem_single_claim
    {Claim Residue : Type} {c c' : Claim}
    (h : Formula.claim c' ∈ ([Formula.claim c] : Context Claim Residue)) :
    c' = c := by
  simp at h
  cases h
  rfl

private theorem bridge_not_mem_single_claim
    {Claim Residue : Type} {a b c : Claim} :
    Formula.bridge a b ∉ ([Formula.claim c] : Context Claim Residue) := by
  intro h
  simp at h

/-- A single local claim assumption can be consumed once. After that use, the
    residual context is empty and the same empty-floor/empty-bridge system cannot
    derive the claim again. This is the minimal no-contraction contrast with the
    membership-context `Witnessed.Sequent` layer. -/
theorem single_claim_does_not_survive_use
    {Claim Residue : Type} (c : Claim) :
    Derives
        (fun _ : Claim => False)
        (fun _ _ : Claim => False)
        ([Formula.claim c] : Context Claim Residue) c [] ∧
    Formula.claim c ∉ ([] : Context Claim Residue) ∧
    ¬ Derives
        (fun _ : Claim => False)
        (fun _ _ : Claim => False)
        ([] : Context Claim Residue) c [] := by
  exact ⟨Derives.hyp (Split.left Split.nil),
    (fun h => nomatch h),
    empty_input_derives_nothing⟩

/-- A valid bridge plus an actual linear bridge token suffices for one crossing.
    The local claim token is consumed first, leaving the bridge token; the bridge
    rule then spends that token and leaves the empty residual context. -/
theorem bridge_token_suffices
    {Claim Residue : Type} {B : Claim -> Claim -> Prop} {c c' : Claim}
    (hb : B c c') :
    Derives
        (fun _ : Claim => False)
        B
        ([Formula.claim c, Formula.bridge c c'] : Context Claim Residue) c' [] :=
  Derives.bridge
    (Derives.hyp (Split.left (Split.right Split.nil)))
    hb
    (Split.left Split.nil)

/-- Bridge validity alone does not grant bridge use. With an empty persistent
    floor and only one local `claim c` token, a distinct `c'` cannot be derived
    to any residual output even if `B c c'` is valid: there is no linear
    `bridge c c'` token to spend. -/
theorem cannot_cross_without_bridge_token_any_delta
    {Claim Residue : Type} {B : Claim -> Claim -> Prop} {c c' : Claim}
    (_hb : B c c') (hne : c ≠ c') :
    forall Delta : Context Claim Residue,
      ¬ Derives
          (fun _ : Claim => False)
          B
          ([Formula.claim c] : Context Claim Residue)
          c'
          Delta := by
  intro Delta h
  cases h with
  | floor hk =>
      exact hk
  | hyp hconsume =>
      have hmem :=
        mem_input_of_mem_consumed hconsume (List.Mem.head _)
      exact hne (claim_eq_of_mem_single_claim hmem).symm
  | bridge hder _ hconsume =>
      have hBridgeInResidual :=
        mem_input_of_mem_consumed hconsume (List.Mem.head _)
      have hBridgeInInput := residual_mem_input hder hBridgeInResidual
      exact bridge_not_mem_single_claim hBridgeInInput

/-- Empty-output specialization of `cannot_cross_without_bridge_token_any_delta`. -/
theorem cannot_cross_without_bridge_token
    {Claim Residue : Type} {B : Claim -> Claim -> Prop} {c c' : Claim}
    (hb : B c c') (hne : c ≠ c') :
    ¬ Derives
        (fun _ : Claim => False)
        B
        ([Formula.claim c] : Context Claim Residue) c' [] :=
  cannot_cross_without_bridge_token_any_delta hb hne []

/-- Ordinary WDC/sequent reachability crosses from `c` to `c'` using bridge
    validity alone; no linear bridge token exists in this forgetful layer. -/
theorem ordinary_crosses_from_valid_bridge
    {Claim : Type} {B : Claim -> Claim -> Prop} {c c' : Claim}
    (hb : B c c') :
    LeanProofs.Witnessed.Sequent.Derivable
      (fun _ : Claim => False)
      B
      [c]
      c' :=
  LeanProofs.Witnessed.Sequent.cross
    (LeanProofs.Witnessed.Sequent.hyp (List.Mem.head _))
    hb

/-- Strictness receipt: ordinary sequent reachability is a forgetful shadow of
    resource executability, not equivalent to it. The ordinary layer can cross
    from `c` to `c'` using `B c c'`; the resource layer cannot execute that
    crossing from only `[claim c]` unless a linear bridge token is present. -/
theorem ordinary_reachability_not_resource_executability_without_token
    {Claim Residue : Type} {B : Claim -> Claim -> Prop} {c c' : Claim}
    (hb : B c c') (hne : c ≠ c') :
    LeanProofs.Witnessed.Sequent.Derivable
      (fun _ : Claim => False)
      B
      [c]
      c'
    ∧
    (forall Delta : Context Claim Residue,
      ¬ Derives
          (fun _ : Claim => False)
          B
          ([Formula.claim c] : Context Claim Residue)
          c'
          Delta) :=
  ⟨ordinary_crosses_from_valid_bridge hb,
   cannot_cross_without_bridge_token_any_delta hb hne⟩

end LeanProofs.Scratch.WitnessedResourceSequent
