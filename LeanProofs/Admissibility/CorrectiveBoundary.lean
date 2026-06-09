/-
  Custody-Class: ANNEX

  Admissibility — Corrective boundary (model-dependence proof).

  Sibling of `Corrective.lean`. The recorded investigative null
  `corrective_then_forward_is_not_monotone` (originally `sorry`-bearing in
  `Corrective.lean`) marks a boundary in the abstract kernel: under the
  kernel's unconstrained `axiom` store ops, the existential is not decided
  by the kernel's assumptions — it is model-dependent, consistent with
  both directions. ("Undecidable" in the meta-logical / recursion-theoretic
  sense is NOT claimed and not proved here.)

  This module proves the model-dependence is GENUINE, not
  vocabulary deficit. We construct a parallel miniature kernel with the
  same shape as the abstract kernel but with concrete, definable types
  for `PolicyStore`, `RevocationStore`, etc., and concrete, parameterized
  store ops. Within the miniature kernel:

    - Identity model (store ops are identity functions): the
      corrective-then-forward existential is FALSE.
    - Witness model (a minimally non-trivial set of store ops + a
      verdict-sensitive `BasisDerivation`): the existential is TRUE.

  We then extract `NondegenerateStoreSemantics` as the abstract predicate
  capturing the three commitments named in
  `papers/working/nondegenerate-store-semantics.md`:

    (3.1) Nontrivial store effects.
    (3.2) Verdict-sensitive derivation.
    (3.3) Mixed-class witness — corrective-then-forward authorizes a
          previously-unauthorized claim.

  Theorem `corrective_then_forward_is_not_monotone_of_nondegenerate` proves
  that any (ops, env) satisfying `NondegenerateStoreSemantics` produces a
  failure of `WeaklyLessPermissive` on a corrective+forward sequence.

  This module does NOT discharge the abstract kernel's recorded null. The
  abstract null persists as a comment-shape in `Corrective.lean` plus the
  CLAIM-REGISTER A1 entry. What this module adds is the positive boundary
  result: the abstract null is a genuine model-dependence boundary, not a
  proof we forgot to write.

  The miniature kernel is intentionally parallel, not derived. The abstract
  kernel uses global `axiom` declarations for stores; we cannot override
  axioms, so we re-create the structure with definable types and carry
  store ops as a `StoreOps` structure. The mirror is structural, not
  inheritance.

  ## Structural mirror — what is preserved and what is collapsed

  The miniature kernel provides *structural evidence* for the abstract
  claim, not a derived theorem about it. The Lean result should not be
  read as a theorem that lifts from `Mini` to the abstract kernel's
  `axiom`-typed stores; the abstract null persists in `Corrective.lean`
  because the abstract layer cannot decide it.

  The mirror is faithful in:
    - `Step` constructor shape and arity (one per mutation kind).
    - Step classification (corrective / forward / neutral) and the
      `IsCorrective` / `IsForward` / `IsNeutral` discipline.
    - Step sequencing via `applyStep` / `applySteps`.
    - WLP-style cross-state comparison via `WeaklyLessPermissive`.
    - The bridge-structure shape (`BasisDerivation` carrying a function
      plus its `revoked_never_admissible` obligation; `DerivationEnv`
      bundling the three derivations; `decideAuthority` as the gate).

  The mirror collapses:
    - `Actor`, `Receipt`, `Gap` to `Unit` (no actor-distinction, no
      receipt schema, no gap schema).
    - `EvidenceStore` and `GapStore` to `Unit` (not exercised by the
      recorded null, which involves only policy and revocation stores).
    - The abstract kernel's `*Standing` predicates are not mirrored
      (the mini's `BasisDerivation` does not depend on standing).

  Within these collapses, the structural claim the mirror exhibits —
  *that the abstract null is genuinely model-dependent* — is honest. A
  reader extending the mirror to test additional dimensions (actors,
  evidence schemas, standing predicates) would re-do the structural
  exhibition for those dimensions; the current mirror does not claim
  to cover them.

  Site 2 finding (orientation): `mixed_class_witness` is intentionally
  conclusion-shaped at the abstract level. The concrete structural
  prerequisite (the corrective doesn't pre-block the forward's
  authorization) is exhibited by `Witness.DoesNotPreBlock`; the abstract
  layer does not claim an env-independent decomposition. *A failed
  patch can be evidence of an honest abstraction boundary.*

  Governor-neutral. Imports `Authority.lean` for the verdict types only.
-/

import LeanProofs.Admissibility.Authority

namespace Admissibility.CorrectiveBoundary

open Admissibility.Authority

/-! ## Miniature kernel

  Concrete payload types and a parameterized store-ops structure mirror the
  abstract kernel's shape. Everything below is definable; nothing depends
  on a global axiom.
-/

namespace Mini

/-- Claim identifiers are natural numbers in this miniature kernel. The
    abstract kernel uses an opaque `axiom AuthorityClaim : Type`. -/
abbrev Claim := Nat

abbrev Actor := Unit
abbrev Receipt := Unit
abbrev Gap := Unit

/-- Policy store: list of claim IDs admitted as bases. -/
abbrev PolicyStore := List Claim

abbrev EvidenceStore := Unit
abbrev GapStore := Unit

/-- Revocation store: list of claim IDs whose basis has been revoked. -/
abbrev RevocationStore := List Claim

/-- A policy update admits a single claim. -/
abbrev PolicyUpdate := Claim

/-- A revocation invalidates a single claim. -/
abbrev Revocation := Claim

/-- Mirror of `Admissibility.StateTransition.GovState`. -/
structure GovState where
  policyStore : PolicyStore
  evidenceStore : EvidenceStore
  gapStore : GapStore
  revocationStore : RevocationStore
deriving Repr

/-- Mirror of `Admissibility.StateTransition.Step`. -/
inductive Step where
  | recordReceipt (r : Receipt)
  | declarePolicyGap (g : Gap)
  | recordRevocation (rv : Revocation)
  | amendPolicy (p : PolicyUpdate)
deriving Repr

/-- Mirror of `Admissibility.Corrective.StepClassification`. -/
inductive StepClassification where
  | corrective
  | forward
  | neutral
deriving DecidableEq, Repr

/-- Mirror of `Admissibility.Corrective.classify`. Same arms as the
    abstract kernel: receipts neutral, gaps and revocations corrective,
    amendments forward. -/
def classify : Step → StepClassification
  | Step.recordReceipt _    => StepClassification.neutral
  | Step.declarePolicyGap _ => StepClassification.corrective
  | Step.recordRevocation _ => StepClassification.corrective
  | Step.amendPolicy _      => StepClassification.forward

def IsCorrective (s : Step) : Prop := classify s = StepClassification.corrective
def IsForward   (s : Step) : Prop := classify s = StepClassification.forward
def IsNeutral   (s : Step) : Prop := classify s = StepClassification.neutral

/-- Store operations carried as a structure. The abstract kernel uses
    global `axiom` declarations for these; here we make them parameters
    so models can vary independently. -/
structure StoreOps where
  applyUpdate      : PolicyStore → PolicyUpdate → PolicyStore
  appendRevocation : RevocationStore → Revocation → RevocationStore
  appendEvidence   : EvidenceStore → Receipt → EvidenceStore
  appendGap        : GapStore → Gap → GapStore

/-- Mirror of `Admissibility.StateTransition.applyStep`, parameterized by
    `StoreOps`. -/
def applyStep (ops : StoreOps) (state : GovState) (step : Step) : GovState :=
  match step with
  | Step.recordReceipt r =>
      { state with evidenceStore := ops.appendEvidence state.evidenceStore r }
  | Step.declarePolicyGap g =>
      { state with gapStore := ops.appendGap state.gapStore g }
  | Step.recordRevocation rv =>
      { state with revocationStore := ops.appendRevocation state.revocationStore rv }
  | Step.amendPolicy p =>
      { state with policyStore := ops.applyUpdate state.policyStore p }

/-- Mirror of `Admissibility.Corrective.applySteps`. -/
def applySteps (ops : StoreOps) : GovState → List Step → GovState
  | Γ, []        => Γ
  | Γ, s :: rest => applySteps ops (applyStep ops Γ s) rest

/-- Mirror of `Admissibility.Derivation.BasisDerivation`. -/
structure BasisDerivation where
  deriveBasis  : GovState → Claim → BasisVerdict
  basisRevoked : GovState → Claim → Prop
  revoked_never_admissible :
    ∀ (state : GovState) (claim : Claim),
      basisRevoked state claim →
        deriveBasis state claim ≠ BasisVerdict.admissibleBasis

/-- Mirror of `Admissibility.Derivation.PrecedenceDerivation`. -/
structure PrecedenceDerivation where
  derivePrecedence : GovState → Claim → PrecedenceVerdict

/-- Mirror of `Admissibility.Derivation.StandingDerivation`. -/
structure StandingDerivation where
  deriveStanding : GovState → Actor → Claim → StandingVerdict

/-- Mirror of `Admissibility.Derivation.DerivationEnv`. -/
structure DerivationEnv where
  basis      : BasisDerivation
  precedence : PrecedenceDerivation
  standing   : StandingDerivation

/-- Mirror of `Admissibility.Derivation.decideAuthority`. -/
def decideAuthority
    (env : DerivationEnv)
    (state : GovState)
    (actor : Actor)
    (claim : Claim) : AuthorityVerdict :=
  authorityVerdict
    (env.basis.deriveBasis state claim)
    (env.precedence.derivePrecedence state claim)
    (env.standing.deriveStanding state actor claim)

/-- Mirror of `Admissibility.Corrective.WeaklyLessPermissive`. -/
def WeaklyLessPermissive
    (env : DerivationEnv) (Γ' Γ : GovState) : Prop :=
  ∀ (a : Actor) (K : Claim),
    decideAuthority env Γ' a K = AuthorityVerdict.authorized →
    decideAuthority env Γ  a K = AuthorityVerdict.authorized

end Mini

/-! ## Identity model — corrective-then-forward IS monotone

  Every store op is the identity. Therefore `applyStep ops Γ s = Γ` for
  every `Γ` and `s`, so any sequence preserves the state exactly, and
  `WeaklyLessPermissive` holds reflexively. The corrective-then-forward
  existential is FALSE in this model: there is no env, Γ, sc, sf for which
  `WeaklyLessPermissive` could fail.

  This is the negative half of the model-dependence claim: vocabulary
  alone does not force non-monotonicity.
-/

namespace Identity

/-- Identity store ops. Every store function returns its first argument. -/
def ops : Mini.StoreOps where
  applyUpdate      := fun s _ => s
  appendRevocation := fun s _ => s
  appendEvidence   := fun s _ => s
  appendGap        := fun s _ => s

/-- Under identity ops, every Step preserves state. -/
theorem applyStep_eq_self (Γ : Mini.GovState) (s : Mini.Step) :
    Mini.applyStep ops Γ s = Γ := by
  cases s <;> rfl

/-- Under identity ops, every step sequence preserves state. -/
theorem applySteps_eq_self (Γ : Mini.GovState) (steps : List Mini.Step) :
    Mini.applySteps ops Γ steps = Γ := by
  induction steps generalizing Γ with
  | nil => rfl
  | cons s rest ih =>
      simp only [Mini.applySteps]
      rw [applyStep_eq_self]
      exact ih Γ

/-- Negative model-dependence half: in the identity model, for any env,
    state, and corrective-then-forward sequence, `WeaklyLessPermissive`
    holds. The recorded null's existential is FALSE here. -/
theorem corrective_then_forward_is_monotone
    (env : Mini.DerivationEnv) (Γ : Mini.GovState)
    (sc sf : Mini.Step)
    (_hc : Mini.IsCorrective sc) (_hf : Mini.IsForward sf) :
    Mini.WeaklyLessPermissive env
      (Mini.applySteps ops Γ [sc, sf]) Γ := by
  rw [applySteps_eq_self]
  intro _ _ h
  exact h

/-- The recorded-null existential, stated for the identity model and
    proved FALSE. -/
theorem corrective_then_forward_is_monotone_universally :
    ∀ (env : Mini.DerivationEnv) (Γ : Mini.GovState)
      (sc sf : Mini.Step),
      Mini.IsCorrective sc → Mini.IsForward sf →
        Mini.WeaklyLessPermissive env
          (Mini.applySteps ops Γ [sc, sf]) Γ :=
  corrective_then_forward_is_monotone

end Identity

/-! ## Witness model — corrective-then-forward IS NOT monotone

  Concrete nondegenerate ops + a verdict-sensitive `BasisDerivation`.
  Exhibits a specific witness `(Γ, sc, sf, K)` for which
  `WeaklyLessPermissive` fails: the corrective-then-forward sequence
  authorizes a claim that was not authorized at `Γ`.

  This is the positive half of the model-dependence claim: even a
  minimal nondegenerate semantics produces non-monotonicity, exhibiting
  the existential the abstract kernel leaves undecided.
-/

namespace Witness

/-- Nondegenerate store ops: amendments and revocations actually
    change their store. -/
def ops : Mini.StoreOps where
  applyUpdate      := fun s p  => p :: s
  appendRevocation := fun s rv => rv :: s
  appendEvidence   := fun s _  => s
  appendGap        := fun s _  => s

/-- Verdict-sensitive basis derivation. A claim's basis is admissible iff
    it has been admitted to `policyStore` and not revoked. The order of
    the conditionals makes `revoked_never_admissible` immediate. -/
def deriveBasis (Γ : Mini.GovState) (K : Mini.Claim) : BasisVerdict :=
  if K ∈ Γ.revocationStore then
    BasisVerdict.noBasis
  else if K ∈ Γ.policyStore then
    BasisVerdict.admissibleBasis
  else
    BasisVerdict.noBasis

/-- Revoked-claim recognition: a claim's basis is revoked iff the claim
    appears in the revocation store. -/
def basisRevoked (Γ : Mini.GovState) (K : Mini.Claim) : Prop :=
  K ∈ Γ.revocationStore

/-- Spec obligation: revoked claims never derive `admissibleBasis`. -/
theorem deriveBasis_revoked_never_admissible
    (Γ : Mini.GovState) (K : Mini.Claim)
    (h : basisRevoked Γ K) :
    deriveBasis Γ K ≠ BasisVerdict.admissibleBasis := by
  -- `basisRevoked Γ K` is definitionally `K ∈ Γ.revocationStore`.
  have h' : K ∈ Γ.revocationStore := h
  unfold deriveBasis
  rw [if_pos h']
  decide

def basis : Mini.BasisDerivation where
  deriveBasis              := deriveBasis
  basisRevoked             := basisRevoked
  revoked_never_admissible := deriveBasis_revoked_never_admissible

/-- Trivial precedence derivation: every claim resolves. Keeps the witness
    proof focused on the basis dimension. -/
def precedence : Mini.PrecedenceDerivation where
  derivePrecedence := fun _ _ => PrecedenceVerdict.resolved

/-- Trivial standing derivation: every actor has standing. Keeps the
    witness proof focused on the basis dimension. -/
def standing : Mini.StandingDerivation where
  deriveStanding := fun _ _ _ => StandingVerdict.standing

def env : Mini.DerivationEnv where
  basis      := basis
  precedence := precedence
  standing   := standing

/-! ### The witness tuple -/

/-- Witness claim. -/
def witnessClaim : Mini.Claim := 1

/-- Initial state: empty policy and revocation stores. -/
def initialState : Mini.GovState :=
  { policyStore     := []
    evidenceStore   := ()
    gapStore        := ()
    revocationStore := [] }

/-- Witness corrective: revoke an unrelated claim. The corrective is
    intentionally not the one being authorized — non-pre-blockage. -/
def witnessCorrective : Mini.Step := Mini.Step.recordRevocation 999

/-- Witness forward: amend policy to admit the witness claim. -/
def witnessForward : Mini.Step := Mini.Step.amendPolicy witnessClaim

/-! ### Verdict computations at the witness -/

theorem witnessCorrective_isCorrective : Mini.IsCorrective witnessCorrective := by
  rfl

theorem witnessForward_isForward : Mini.IsForward witnessForward := by
  rfl

/-! ### Structural condition: corrective does not pre-block the forward

  The witness construction relies on an implicit structural condition:
  the corrective step must not pre-block the claim the forward step is
  meant to authorize. In the concrete witness this is discharged by
  the numeric inequality `999 ≠ 1` — the revocation target is not the
  witness claim.

  Naming the predicate explicitly so the witness's structural
  requirement is visible, not buried in the choice of numerals.
  Site 3 of the 2026-05-08 proof-first scout pass.
-/

/-- A corrective step does not pre-block claim `K`: applying the step
    to a state where `K` is not already revoked leaves `K` unrevoked.
    Scoped locally to the `Witness` namespace's `ops` (the
    nondegenerate store ops); not a generic relation between
    corrective and forward steps. -/
def DoesNotPreBlock (sc : Mini.Step) (K : Mini.Claim) : Prop :=
  ∀ Γ : Mini.GovState,
    K ∉ Γ.revocationStore →
    K ∉ (Mini.applyStep ops Γ sc).revocationStore

/-- The witness corrective (`recordRevocation 999`) does not pre-block
    `witnessClaim` (= 1). Discharge of the structural condition;
    follows from the concrete inequality `999 ≠ 1`. -/
theorem witnessCorrective_doesNotPreBlock_witnessClaim :
    DoesNotPreBlock witnessCorrective witnessClaim := by
  intro Γ hNotIn hIn
  -- `(Mini.applyStep ops Γ witnessCorrective).revocationStore` reduces
  -- definitionally to `999 :: Γ.revocationStore` (via `ops.appendRevocation`).
  rw [show (Mini.applyStep ops Γ witnessCorrective).revocationStore =
        999 :: Γ.revocationStore from rfl, List.mem_cons] at hIn
  rcases hIn with h | h
  · exact absurd h (by decide)
  · exact hNotIn h

/-- At `initialState`, the witness claim is not authorized: nothing in the
    policy store, so basis derives to `noBasis`, so `decideAuthority`
    returns `denied`. -/
theorem decideAuthority_initial_not_authorized :
    Mini.decideAuthority env initialState () witnessClaim ≠
      AuthorityVerdict.authorized := by
  decide

/-- After applying [witnessCorrective, witnessForward] to `initialState`,
    the state's policy store contains `witnessClaim` and its revocation
    store contains only `999` (not the witness). So basis derives to
    `admissibleBasis`, precedence is `resolved`, standing is `standing`,
    and `decideAuthority` returns `authorized`. -/
theorem decideAuthority_after_sequence_authorized :
    Mini.decideAuthority env
      (Mini.applySteps ops initialState
        [witnessCorrective, witnessForward]) ()
      witnessClaim = AuthorityVerdict.authorized := by
  decide

/-- Witness theorem: in the nondegenerate model, there exists a state and
    a corrective-then-forward sequence such that `WeaklyLessPermissive`
    fails. -/
theorem corrective_then_forward_is_not_monotone :
    ∃ (Γ : Mini.GovState) (sc sf : Mini.Step),
      Mini.IsCorrective sc ∧ Mini.IsForward sf ∧
      ¬ Mini.WeaklyLessPermissive env
          (Mini.applySteps ops Γ [sc, sf]) Γ := by
  refine ⟨initialState, witnessCorrective, witnessForward,
          witnessCorrective_isCorrective, witnessForward_isForward, ?_⟩
  intro hwlp
  have hpost := decideAuthority_after_sequence_authorized
  have hpre  := decideAuthority_initial_not_authorized
  exact hpre (hwlp () witnessClaim hpost)

end Witness

/-! ## Abstract `NondegenerateStoreSemantics`

  The three commitments named in `papers/working/nondegenerate-store-semantics.md`
  packaged as a structure carrying independent fields. The general theorem
  proves that any (ops, env) satisfying the structure makes the
  recorded-null existential go through.

  The first two fields, `applyUpdate_nontrivial` and `verdict_sensitive`,
  capture commitments (3.1) and (3.2). They are not redundant with the
  third field — the identity model fails (3.1) and (3.2) immediately,
  exhibiting the dependency. The third field, `mixed_class_witness`,
  captures (3.3) and is essentially the recorded null's existential
  packaged as evidence; the general theorem unwraps it.

  Field dependence is pinned, not asserted. The parametric theorem
  consumes only (3.3). (3.2) is DERIVABLE from (3.3) — see
  `mixed_class_witness_implies_verdict_sensitive` — and is retained as a
  named field for doctrinal legibility, not logical necessity. (3.1) is
  NOT implied by (3.3) — see `PerverseRevocationEnv`, in which a
  corrective step mints authority under identity `applyUpdate` — and
  functions as the model-hygiene commitment that excludes
  revocation-driven laundering models from the "nondegenerate" label.
  The three fields are therefore not a flat list of independent
  prerequisites: (3.1) is independent, (3.2) is entailed, (3.3) is the
  load-bearing witness.
-/

/-- The three nondegeneracy commitments packaged for the parametric
    theorem. Independence of the fields is exhibited by the identity
    model (which fails the first immediately) and the witness model
    (which satisfies all three). -/
structure NondegenerateStoreSemantics
    (ops : Mini.StoreOps) (env : Mini.DerivationEnv) where
  /-- (3.1) Nontrivial store effects: `applyUpdate` is not the identity. -/
  applyUpdate_nontrivial :
    ∃ (s : Mini.PolicyStore) (p : Mini.PolicyUpdate),
      ops.applyUpdate s p ≠ s
  /-- (3.2) Verdict-sensitive derivation: at least one Step changes the
      authority verdict for some claim. -/
  verdict_sensitive :
    ∃ (Γ : Mini.GovState) (s : Mini.Step) (a : Mini.Actor) (K : Mini.Claim),
      Mini.decideAuthority env Γ a K ≠
        Mini.decideAuthority env (Mini.applyStep ops Γ s) a K
  /-- (3.3) Mixed-class witness: a corrective-then-forward sequence
      authorizes a previously-unauthorized claim. Conclusion-shaped at
      this abstract level by design — the structural prerequisite
      (corrective doesn't pre-block the forward's authorization) is
      exhibited concretely by `Witness.DoesNotPreBlock`; the abstract
      layer does not claim an env-independent decomposition. -/
  mixed_class_witness :
    ∃ (Γ : Mini.GovState) (sc sf : Mini.Step)
      (a : Mini.Actor) (K : Mini.Claim),
      Mini.IsCorrective sc ∧ Mini.IsForward sf ∧
      Mini.decideAuthority env Γ a K ≠ AuthorityVerdict.authorized ∧
      Mini.decideAuthority env (Mini.applySteps ops Γ [sc, sf]) a K =
        AuthorityVerdict.authorized

/-! ### General theorem

  The recorded null's existential follows from `NondegenerateStoreSemantics`.
  The proof unwraps `mixed_class_witness` and observes that the failure
  of `WeaklyLessPermissive` is exactly the conjunction of post-authorized
  and pre-not-authorized at the witness `(a, K)`.
-/

/-- Parametric theorem: any `(ops, env)` satisfying
    `NondegenerateStoreSemantics` makes the corrective-then-forward
    existential go through. -/
theorem corrective_then_forward_is_not_monotone_of_nondegenerate
    {ops : Mini.StoreOps} {env : Mini.DerivationEnv}
    (h : NondegenerateStoreSemantics ops env) :
    ∃ (Γ : Mini.GovState) (sc sf : Mini.Step),
      Mini.IsCorrective sc ∧ Mini.IsForward sf ∧
      ¬ Mini.WeaklyLessPermissive env
          (Mini.applySteps ops Γ [sc, sf]) Γ := by
  obtain ⟨Γ, sc, sf, a, K, hc, hf, hpre, hpost⟩ := h.mixed_class_witness
  refine ⟨Γ, sc, sf, hc, hf, ?_⟩
  intro hwlp
  exact hpre (hwlp a K hpost)

/-! ### The witness model satisfies the abstract structure -/

/-- The witness model satisfies all three nondegeneracy commitments.
    Construction proof; each field is discharged with the corresponding
    concrete witness from the `Witness` namespace. -/
theorem witness_satisfies_nondegenerate :
    NondegenerateStoreSemantics Witness.ops Witness.env := by
  refine ⟨?_, ?_, ?_⟩
  · -- (3.1) applyUpdate is non-trivial: applyUpdate [] 1 = [1] ≠ []
    refine ⟨[], 1, ?_⟩
    show (1 :: ([] : List Mini.Claim)) ≠ ([] : List Mini.Claim)
    decide
  · -- (3.2) verdict-sensitive: amending policy with witnessClaim
    -- changes the verdict from denied to authorized.
    refine ⟨Witness.initialState, Witness.witnessForward, (), Witness.witnessClaim, ?_⟩
    intro hcontra
    have hpre := Witness.decideAuthority_initial_not_authorized
    have hpost :
        Mini.decideAuthority Witness.env
          (Mini.applyStep Witness.ops Witness.initialState
            Witness.witnessForward) ()
          Witness.witnessClaim = AuthorityVerdict.authorized := by
      decide
    exact hpre (hcontra ▸ hpost)
  · -- (3.3) mixed-class witness: directly from Witness.
    refine ⟨Witness.initialState, Witness.witnessCorrective, Witness.witnessForward,
            (), Witness.witnessClaim,
            Witness.witnessCorrective_isCorrective,
            Witness.witnessForward_isForward,
            Witness.decideAuthority_initial_not_authorized,
            Witness.decideAuthority_after_sequence_authorized⟩

/-! ### Sanity: the witness model independently exhibits non-monotonicity

  Combining the abstract theorem with the concrete satisfaction proof
  recovers `Witness.corrective_then_forward_is_not_monotone` from the
  abstract path. Useful as a regression check. -/

theorem witness_corrective_then_forward_is_not_monotone_via_abstract :
    ∃ (Γ : Mini.GovState) (sc sf : Mini.Step),
      Mini.IsCorrective sc ∧ Mini.IsForward sf ∧
      ¬ Mini.WeaklyLessPermissive Witness.env
          (Mini.applySteps Witness.ops Γ [sc, sf]) Γ :=
  corrective_then_forward_is_not_monotone_of_nondegenerate
    witness_satisfies_nondegenerate

/-! ## Field dependence — what (3.3) does and does not imply

  `corrective_then_forward_is_not_monotone_of_nondegenerate` consumes
  only `mixed_class_witness`. The other two fields' relationship to (3.3)
  is now pinned instead of asserted:

    - (3.3) → (3.2): provable. A verdict change across a two-step
      sequence pigeonholes onto one of the two steps.
    - (3.3) ↛ (3.1): refuted by `PerverseRevocationEnv` below, where a
      corrective step mints authority under identity `applyUpdate`.

  So (3.2) is a consequence of (3.3) kept as a named field for doctrinal
  legibility, and (3.1) is a genuine independent model-hygiene commitment
  that fences off revocation-driven laundering models — not implied by
  the witness shape.
-/

/-- (3.3) implies (3.2): a mixed-class witness already exhibits verdict
    sensitivity at one of its two steps. Pigeonhole over the intermediate
    state. -/
theorem mixed_class_witness_implies_verdict_sensitive
    {ops : Mini.StoreOps} {env : Mini.DerivationEnv}
    (h : ∃ (Γ : Mini.GovState) (sc sf : Mini.Step)
        (a : Mini.Actor) (K : Mini.Claim),
        Mini.IsCorrective sc ∧ Mini.IsForward sf ∧
        Mini.decideAuthority env Γ a K ≠ AuthorityVerdict.authorized ∧
        Mini.decideAuthority env (Mini.applySteps ops Γ [sc, sf]) a K =
          AuthorityVerdict.authorized) :
    ∃ (Γ : Mini.GovState) (s : Mini.Step)
      (a : Mini.Actor) (K : Mini.Claim),
      Mini.decideAuthority env Γ a K ≠
        Mini.decideAuthority env (Mini.applyStep ops Γ s) a K := by
  obtain ⟨Γ, sc, sf, a, K, _hc, _hf, hpre, hpost⟩ := h
  have hseq :
      Mini.applySteps ops Γ [sc, sf] =
        Mini.applyStep ops (Mini.applyStep ops Γ sc) sf := rfl
  rw [hseq] at hpost
  by_cases hmid :
      Mini.decideAuthority env (Mini.applyStep ops Γ sc) a K =
        Mini.decideAuthority env Γ a K
  · refine ⟨Mini.applyStep ops Γ sc, sf, a, K, ?_⟩
    rw [hpost, hmid]
    exact hpre
  · exact ⟨Γ, sc, a, K, fun hc => hmid hc.symm⟩

/-! ### Counter-model: (3.3) without (3.1)

  Identity `applyUpdate`, nondegenerate `appendRevocation`, and a basis
  derivation that grants `admissibleBasis` exactly when the claim sits in
  the revocation store. `revoked_never_admissible` is discharged
  vacuously by declaring nothing revoked. The corrective step
  `recordRevocation 1` then authorizes claim 1; the forward step is a
  no-op present only to satisfy the witness shape.
-/

namespace PerverseRevocationEnv

/-- Identity policy updates, nondegenerate revocations. Fails (3.1). -/
def ops : Mini.StoreOps where
  applyUpdate      := fun s _  => s
  appendRevocation := fun s rv => rv :: s
  appendEvidence   := fun s _  => s
  appendGap        := fun s _  => s

/-- Perverse basis derivation: revocation-store membership GRANTS basis. -/
def deriveBasis (Γ : Mini.GovState) (K : Mini.Claim) : BasisVerdict :=
  if K ∈ Γ.revocationStore then BasisVerdict.admissibleBasis
  else BasisVerdict.noBasis

def basis : Mini.BasisDerivation where
  deriveBasis              := deriveBasis
  basisRevoked             := fun _ _ => False
  revoked_never_admissible := fun _ _ h => h.elim

def env : Mini.DerivationEnv where
  basis      := basis
  precedence := { derivePrecedence := fun _ _ => PrecedenceVerdict.resolved }
  standing   := { deriveStanding   := fun _ _ _ => StandingVerdict.standing }

def initialState : Mini.GovState :=
  { policyStore := [], evidenceStore := (), gapStore := (),
    revocationStore := [] }

/-- (3.1) fails: applyUpdate is the identity. -/
theorem applyUpdate_trivial :
    ∀ (s : Mini.PolicyStore) (p : Mini.PolicyUpdate),
      ops.applyUpdate s p = s :=
  fun _ _ => rfl

/-- (3.3) holds: recordRevocation 1 (corrective) followed by amendPolicy 1
    (forward, inert) authorizes claim 1 from a state where it was not
    authorized. Corrective step alone mints authority. -/
theorem mixed_class_witness_holds :
    ∃ (Γ : Mini.GovState) (sc sf : Mini.Step)
      (a : Mini.Actor) (K : Mini.Claim),
      Mini.IsCorrective sc ∧ Mini.IsForward sf ∧
      Mini.decideAuthority env Γ a K ≠ AuthorityVerdict.authorized ∧
      Mini.decideAuthority env
        (Mini.applySteps ops Γ
          [Mini.Step.recordRevocation 1, Mini.Step.amendPolicy 1]) a K =
        AuthorityVerdict.authorized := by
  refine ⟨initialState, Mini.Step.recordRevocation 1,
          Mini.Step.amendPolicy 1, (), 1, rfl, rfl, ?_, ?_⟩
  · decide
  · decide

end PerverseRevocationEnv

end Admissibility.CorrectiveBoundary
