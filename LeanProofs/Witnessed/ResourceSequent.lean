/-
  LeanProofs.Witnessed.ResourceSequent -- occurrence-sensitive WDC resources.

  Custody class: ANNEX (Mathlib-free public surface). This promotes the
  compiling scratch resource sequent slice into the canonical Witnessed
  namespace. Claim and bridge resource occurrences can be consumed; residue
  occurrences cannot.

  Scope. This is not full linear logic. It is the canonical resource/no-drop
  slice for WDC: persistent floor `K`, linear input resources, derivations with
  residual output, erasure back to ordinary WDC sequents, and residue
  preservation as the public non-suppression receipt.
-/

import LeanProofs.Witnessed.Sequent

namespace LeanProofs.Witnessed.ResourceSequent

/-! ## Syntax -/

/-- Resource formulas: local claim assumptions, one-use bridge tokens, and opaque
    residue that must survive derivations unchanged. -/
inductive ResourceFormula (Claim Residue : Type) where
  | claim : Claim -> ResourceFormula Claim Residue
  | bridge : Claim -> Claim -> ResourceFormula Claim Residue
  | residue : Residue -> ResourceFormula Claim Residue

/-- Linear context. Occurrences matter; no `DecidableEq` is required. -/
abbrev Context (Claim Residue : Type) := List (ResourceFormula Claim Residue)

/-! ## Split / consumption -/

/-- `Split consumed residual input` means `input` is an occurrence-preserving
    interleaving of the consumed resources and the residual resources. -/
inductive Split {alpha : Type} : List alpha -> List alpha -> List alpha -> Prop where
  | nil : Split [] [] []
  | left {x : alpha} {consumed residual input : List alpha} :
      Split consumed residual input ->
        Split (x :: consumed) residual (x :: input)
  | right {x : alpha} {consumed residual input : List alpha} :
      Split consumed residual input ->
        Split consumed (x :: residual) (x :: input)

/-- Consuming exactly one token. -/
abbrev Consumes {alpha : Type} (token : alpha) (input residual : List alpha) : Prop :=
  Split [token] residual input

/-- Prefix extra resources on the residual side of a split. -/
theorem split_residual_prefix
    {alpha : Type} {consumed residual input : List alpha}
    (extra : List alpha)
    (h : Split consumed residual input) :
    Split consumed (extra ++ residual) (extra ++ input) := by
  induction extra with
  | nil =>
      exact h
  | cons _ _ ih =>
      exact Split.right ih

/-- Anything consumed by the left side of a split occurred in the original input. -/
theorem mem_input_of_mem_consumed
    {alpha : Type} {consumed residual input : List alpha} {x : alpha}
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
    {alpha : Type} {consumed residual input : List alpha} {x : alpha}
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
    {alpha : Type} {consumed residual input : List alpha} {x : alpha}
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
  | ResourceFormula.claim c :: rest => c :: claimAssumptions rest
  | ResourceFormula.bridge _ _ :: rest => claimAssumptions rest
  | ResourceFormula.residue _ :: rest => claimAssumptions rest

theorem claim_mem_claimAssumptions_of_formula_mem
    {Claim Residue : Type} {Gamma : Context Claim Residue} {c : Claim}
    (h : ResourceFormula.claim c ∈ Gamma) :
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

/-- Resource derivations from persistent floor plus linear input, producing a
    residual context. -/
inductive Derives
    {Claim Residue : Type}
    (K : Claim -> Prop) (B : Claim -> Claim -> Prop) :
    Context Claim Residue -> Claim -> Context Claim Residue -> Prop where
  | floor {Gamma : Context Claim Residue} {c : Claim} :
      K c -> Derives K B Gamma c Gamma
  | hyp {Gamma Delta : Context Claim Residue} {c : Claim} :
      Consumes (ResourceFormula.claim c) Gamma Delta ->
        Derives K B Gamma c Delta
  | bridge
      {Gamma Gamma' Delta : Context Claim Residue} {c c' : Claim} :
      Derives K B Gamma c Gamma' ->
        B c c' ->
        Consumes (ResourceFormula.bridge c c') Gamma' Delta ->
          Derives K B Gamma c' Delta

/-! ## Certificate shapes -- DEFERRED, not on the public surface

    A serializable `ResourceCertificate` datatype is intentionally NOT exported
    here. The witnessed object on this surface is the `Checks` relation
    (`ResourceChecker`), which is proved sound and complete against `Derives`; a
    metadata datatype is not validated merely because `Checks` is. Re-introducing
    certificates is a frontier item (see `docs/WITNESSED-FRONTIER-REGISTER.md`):
    admit them only as a proof-carrying `ValidatedResourceCertificate` (a `Checks`
    proof rides along) or as executable data accepted by a Bool checker with a
    soundness/adequacy theorem. Until then the unchecked shape lives in
    `LeanProofs/Scratch/UncheckedResourceCertificate.lean` only (scratch, not on the
    public surface). -/

/-- Resource derivations never create residual formulas. -/
theorem residual_mem_input
    {Claim Residue : Type}
    {K : Claim -> Prop} {B : Claim -> Claim -> Prop}
    {Gamma Delta : Context Claim Residue} {c : Claim}
    (h : Derives K B Gamma c Delta) :
    forall {f : ResourceFormula Claim Residue}, f ∈ Delta -> f ∈ Gamma := by
  intro f hf
  induction h with
  | floor _ =>
      exact hf
  | hyp hconsume =>
      exact mem_input_of_mem_residual hconsume hf
  | bridge hder _ hconsume ih =>
      exact ih (mem_input_of_mem_residual hconsume hf)

/-! ## Admissible structural transformations -/

/-- Admissible affine weakening by prefix. Extra resources are carried through. -/
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
    forall y, y ∈ [ResourceFormula.claim c] -> ResourceFormula.residue r ≠ y := by
  intro y hy hEq
  simp at hy
  cases hy
  cases hEq

private theorem residue_not_consumed_by_bridge
    {Claim Residue : Type} (c c' : Claim) (r : Residue) :
    forall y, y ∈ [ResourceFormula.bridge c c'] -> ResourceFormula.residue r ≠ y := by
  intro y hy hEq
  simp at hy
  cases hy
  cases hEq

/-- Residue cannot be consumed by any rule in this system. -/
theorem residue_preserved
    {Claim Residue : Type}
    {K : Claim -> Prop} {B : Claim -> Claim -> Prop}
    {Gamma Delta : Context Claim Residue} {c : Claim} {r : Residue}
    (h : Derives K B Gamma c Delta) :
    ResourceFormula.residue r ∈ Gamma -> ResourceFormula.residue r ∈ Delta := by
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
    sequent using only the local claim assumptions in the original input. -/
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

/-! ## No-contraction / denial specimens -/

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
    (h : ResourceFormula.claim c' ∈ ([ResourceFormula.claim c] : Context Claim Residue)) :
    c' = c := by
  simp at h
  cases h
  rfl

private theorem bridge_not_mem_single_claim
    {Claim Residue : Type} {a b c : Claim} :
    ResourceFormula.bridge a b ∉ ([ResourceFormula.claim c] : Context Claim Residue) := by
  intro h
  simp at h

/-- A single local claim assumption can be consumed once. -/
theorem single_claim_does_not_survive_use
    {Claim Residue : Type} (c : Claim) :
    Derives
        (fun _ : Claim => False)
        (fun _ _ : Claim => False)
        ([ResourceFormula.claim c] : Context Claim Residue) c [] ∧
    ResourceFormula.claim c ∉ ([] : Context Claim Residue) ∧
    ¬ Derives
        (fun _ : Claim => False)
        (fun _ _ : Claim => False)
        ([] : Context Claim Residue) c [] := by
  exact ⟨Derives.hyp (Split.left Split.nil),
    (fun h => nomatch h),
    empty_input_derives_nothing⟩

/-- A valid bridge plus an actual linear bridge token suffices for one crossing. -/
theorem bridge_token_suffices
    {Claim Residue : Type} {B : Claim -> Claim -> Prop} {c c' : Claim}
    (hb : B c c') :
    Derives
        (fun _ : Claim => False)
        B
        ([ResourceFormula.claim c, ResourceFormula.bridge c c'] : Context Claim Residue)
        c'
        [] :=
  Derives.bridge
    (Derives.hyp (Split.left (Split.right Split.nil)))
    hb
    (Split.left Split.nil)

/-- Bridge validity alone does not grant bridge use. -/
theorem cannot_cross_without_bridge_token_any_delta
    {Claim Residue : Type} {B : Claim -> Claim -> Prop} {c c' : Claim}
    (_hb : B c c') (hne : c ≠ c') :
    forall Delta : Context Claim Residue,
      ¬ Derives
          (fun _ : Claim => False)
          B
          ([ResourceFormula.claim c] : Context Claim Residue)
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
        ([ResourceFormula.claim c] : Context Claim Residue) c' [] :=
  cannot_cross_without_bridge_token_any_delta hb hne []

/-- Ordinary WDC/sequent reachability crosses using bridge validity alone. -/
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
    resource executability, not equivalent to it. -/
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
          ([ResourceFormula.claim c] : Context Claim Residue)
          c'
          Delta) :=
  ⟨ordinary_crosses_from_valid_bridge hb,
   cannot_cross_without_bridge_token_any_delta hb hne⟩

end LeanProofs.Witnessed.ResourceSequent
