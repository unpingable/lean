/-
  Admissibility — Corrective monotonicity (candidate, non-binding).

  Reference: governor doctrine; sibling to
  LeanProofs/Admissibility/Authority.lean (verdict algebra),
  LeanProofs/Admissibility/StateTransition.lean (mutation algebra +
  StepAllowed wrapper),
  LeanProofs/Admissibility/Derivation.lean (decideAuthority bridge),
  LeanProofs/Admissibility/Execution.lean (AuthorizedStep — both
  proofs by construction).

  Pinned thesis:

    Corrective steps are down-edges over the authority surface. They
    may reduce, freeze, fork, expire, invalidate, quarantine or
    require re-entry. They may not mint, widen or refresh authority
    for the same basis K.

    Re-entry is not recovery of authority. It is replacement of a
    failed basis with a newly admissible one through the ordinary
    forward path.

  This module is candidate / non-binding. It earns its keep as an
  enforcement surface: every existing and future Step constructor
  must be classifiable as corrective / forward / neutral, and a
  corrective constructor must not also be authority-granting.
  Adding a new Step constructor without extending `classify` is a
  Lean non-exhaustive-match error; that is the tripwire.

  Vacuity caveat: with the current Step type
  ({recordReceipt, declarePolicyGap, recordRevocation, amendPolicy})
  no constructor is *both* classified corrective *and* able to widen
  AuthorizedSet, so the non-laundering corollary holds trivially.
  That is not a defect — it is exactly the audit. The forcing case
  is whichever future Step constructor first tempts both
  classifications.

  Governor-neutral. Imports only sibling Admissibility modules.
-/

import LeanProofs.Admissibility.Authority
import LeanProofs.Admissibility.StateTransition
import LeanProofs.Admissibility.Derivation

namespace Admissibility.Corrective

open Admissibility.Authority
open Admissibility.StateTransition
open Admissibility.Derivation

/-! ### Step classification — enforcement surface

  Every `Step` constructor must classify as corrective (down-edge),
  forward (up-edge candidate), or neutral (data-only). The `classify`
  function is total; adding a new `Step` constructor without an arm
  here is a Lean error. That is the only mechanism that prevents a
  silently-corrective-and-authority-granting Step from sneaking in.
-/

inductive StepClassification where
  | corrective
  | forward
  | neutral
deriving DecidableEq, Repr

/--
  Concrete classification of the current `Step` constructors.

  - `recordReceipt` — neutral. Evidence ingest; receipts are opaque
    here, so we do not assume they grant or revoke standing on their
    own. If a future receipt schema makes evidence directly
    authority-relevant, this arm must move.
  - `declarePolicyGap` — corrective. Marks scope as having a gap;
    cannot widen authority.
  - `recordRevocation` — corrective. Adds to RevocationStore;
    cannot widen authority.
  - `amendPolicy` — forward. The only constructor that can change
    PolicyStore-derived basis / precedence / standing rules and
    therefore the only one that can grow `AuthorizedSet`.
-/
def classify : Step → StepClassification
  | Step.recordReceipt _    => StepClassification.neutral
  | Step.declarePolicyGap _ => StepClassification.corrective
  | Step.recordRevocation _ => StepClassification.corrective
  | Step.amendPolicy _      => StepClassification.forward

def IsCorrective (s : Step) : Prop :=
  classify s = StepClassification.corrective

def IsForward (s : Step) : Prop :=
  classify s = StepClassification.forward

def IsNeutral (s : Step) : Prop :=
  classify s = StepClassification.neutral

/-! ### Disjointness — corrective is not forward

  Same-type tagging cannot collapse. A constructor cannot be both
  corrective and forward. This is the structural half of "no Step
  may be both corrective and authority-granting"; the semantic half
  is the monotonicity obligation in the next section.

  Operational rule for future Step constructors: if a transition is
  "mostly corrective, but" can mint, widen, bless, promote or restore
  authority, it belongs on the forward side of the split, not in
  `IsCorrective`. The corrective half can be a separate Step.
-/

theorem corrective_not_forward (s : Step) :
    IsCorrective s → ¬ IsForward s := by
  unfold IsCorrective IsForward
  intro hc hf
  rw [hc] at hf
  cases hf

theorem corrective_not_neutral (s : Step) :
    IsCorrective s → ¬ IsNeutral s := by
  unfold IsCorrective IsNeutral
  intro hc hn
  rw [hc] at hn
  cases hn

/-! ### Authorized-set order on `GovState`

  `Γ' ≼ₐ Γ` (relative to a fixed `env`) iff every claim authorized at
  `Γ'` is authorized at `Γ`. Read: `Γ'` is *weakly less permissive*.

  The order fixes `env`. Environment mutation (changing the
  `DerivationEnv` itself) is out of scope for this preorder; that is
  a separate theorem and a separate laundering vector
  ("recover authority by changing the evaluator instead of the
  state"). Open question pinned below.
-/

def WeaklyLessPermissive
    (env : DerivationEnv) (Γ' Γ : GovState) : Prop :=
  ∀ (a : Actor) (K : AuthorityClaim),
    decideAuthority env Γ' a K = AuthorityVerdict.authorized →
    decideAuthority env Γ  a K = AuthorityVerdict.authorized

/-- Reflexive (sanity). -/
theorem weakly_less_permissive_refl
    (env : DerivationEnv) (Γ : GovState) :
    WeaklyLessPermissive env Γ Γ := by
  intro _ _ h; exact h

/-- Transitive (sanity). -/
theorem weakly_less_permissive_trans
    {env : DerivationEnv} {Γ₁ Γ₂ Γ₃ : GovState}
    (h₁₂ : WeaklyLessPermissive env Γ₁ Γ₂)
    (h₂₃ : WeaklyLessPermissive env Γ₂ Γ₃) :
    WeaklyLessPermissive env Γ₁ Γ₃ := by
  intro a K hauth
  exact h₂₃ a K (h₁₂ a K hauth)

/-! ### Monotonicity obligation

  Per kernel house style (cf. `BasisDerivation.revoked_never_admissible`),
  carry the load-bearing law as a proof obligation in a structure that
  concrete derivation environments must discharge at construction
  time. The structure does not assert the law unconditionally; it
  declares the shape any compliant implementation must prove.

  An `env` only earns the corrective-monotonicity guarantee by
  supplying a `CorrectiveMonotone env` value.
-/

/--
  Spec obligation: for any corrective Step `s` and any state `Γ`,
  applying `s` cannot enlarge the set of authorized claims at `Γ`.

  Stated relative to a fixed `env`. Concrete `DerivationEnv`
  implementations discharge this by case-analysis over the corrective
  arms of `classify` plus behavioral laws on the abstract store ops
  (deferred to the Derivation module's TODO list).
-/
structure CorrectiveMonotone (env : DerivationEnv) where
  monotone :
    ∀ (Γ : GovState) (s : Step),
      IsCorrective s →
        WeaklyLessPermissive env (applyStep Γ s) Γ

/-! ### Core theorem (under the obligation) -/

/--
  Corrective steps are down-edges over the authority surface, for any
  `env` that supplies the `CorrectiveMonotone` obligation.
-/
theorem corrective_monotone
    {env : DerivationEnv}
    (cm : CorrectiveMonotone env)
    (Γ : GovState) (s : Step)
    (hc : IsCorrective s) :
    WeaklyLessPermissive env (applyStep Γ s) Γ :=
  cm.monotone Γ s hc

/-! ### Non-laundering corollary

  The contrapositive of monotonicity, restricted to a single claim K.
  Stated as a corollary, not an independent obligation: a corrective
  cannot turn a non-authorized claim into an authorized claim *for the
  same K*.

  Same-K is load-bearing. The theorem says nothing about a fresh
  K' minted through the ordinary forward path; that is re-entry, not
  laundering.
-/

theorem corrective_no_authority_laundering
    {env : DerivationEnv}
    (cm : CorrectiveMonotone env)
    (Γ : GovState) (a : Actor) (K : AuthorityClaim)
    (s : Step) (hc : IsCorrective s)
    (hnotAuth :
      decideAuthority env Γ a K ≠ AuthorityVerdict.authorized) :
    decideAuthority env (applyStep Γ s) a K ≠
      AuthorityVerdict.authorized := by
  intro hauth'
  exact hnotAuth (corrective_monotone cm Γ s hc a K hauth')

/-! ### Sequence composition

  Recovery flows are sequences, not single steps. The composition
  shape is provable from `weakly_less_permissive_trans` plus
  `corrective_monotone`. Eager: the bureaucratic conga line of
  invalidation, quarantine, TTL expiry and re-entry-requirement is
  monotone end-to-end.
-/

noncomputable def applySteps : GovState → List Step → GovState
  | Γ, []       => Γ
  | Γ, s :: rest => applySteps (applyStep Γ s) rest

theorem corrective_sequence_monotone
    {env : DerivationEnv}
    (cm : CorrectiveMonotone env)
    (Γ : GovState) (steps : List Step)
    (hAll : ∀ s ∈ steps, IsCorrective s) :
    WeaklyLessPermissive env (applySteps Γ steps) Γ := by
  induction steps generalizing Γ with
  | nil =>
      exact weakly_less_permissive_refl env Γ
  | cons s rest ih =>
      have hs : IsCorrective s := hAll s (by simp)
      have hrest : ∀ t ∈ rest, IsCorrective t := by
        intro t ht
        exact hAll t (List.mem_cons_of_mem s ht)
      have hstep : WeaklyLessPermissive env (applyStep Γ s) Γ :=
        corrective_monotone cm Γ s hs
      have htail :
          WeaklyLessPermissive env
            (applySteps (applyStep Γ s) rest) (applyStep Γ s) :=
        ih (applyStep Γ s) hrest
      show WeaklyLessPermissive env
        (applySteps (applyStep Γ s) rest) Γ
      exact weakly_less_permissive_trans htail hstep

/-! ### Investigative null shape — mixed-class sequence

  Counterpoint to `corrective_sequence_monotone`. The minimal mixed
  shape is a single corrective followed by a single forward Step.
  Stated using existing vocabulary only — no minted primitives, no
  broadened "boundary".

  Proof is `sorry`. The vocabulary deficit is precise: constructing a
  counterexample env requires that `applyUpdate Γ.policyStore p` actually
  distinguish the post-state from the pre-state for *some* (Γ, p).
  `applyUpdate : PolicyStore → PolicyUpdate → PolicyStore` is an
  unconstrained `axiom` in StateTransition.lean. Under the worst-case
  axiomatization where `applyUpdate` is the identity (and likewise for
  `appendGap`, `appendRevocation`, `appendEvidence`), every Step is
  state-preserving and the existential is provably FALSE. Until a
  behavioral law on the abstract store ops is committed (deferred per
  StateTransition.lean and Derivation.lean TODOs), the kernel is
  consistent with both the existential and its negation.

  This `sorry` is a recorded investigative null, not a deferred proof
  to be eliminated by axiomatizing `applyUpdate` here.
-/
theorem corrective_then_forward_is_not_monotone :
    ∃ (env : DerivationEnv) (Γ : GovState) (sc sf : Step),
      IsCorrective sc ∧ IsForward sf ∧
      ¬ WeaklyLessPermissive env (applySteps Γ [sc, sf]) Γ := by
  sorry

/-! ### Recovery-capable environment — available vs operationally required

  `CorrectiveMonotone env` makes monotonicity *available* to any
  concrete `DerivationEnv` that wants to claim it. Whether it is
  *operationally required* — whether code paths claiming corrective
  recovery must carry the witness — is enforced at the recovery
  surface, not globally.

  `RecoveryEnv` bundles a `DerivationEnv` with its `CorrectiveMonotone`
  witness. Recovery-capable APIs accept `RecoveryEnv`, not raw
  `DerivationEnv`. A caller cannot invoke recovery semantics without
  having constructed (and therefore discharged) the obligation.

  Narrow gate placement: analysis tools, audit tools, and ordinary
  forward-authorization paths still take raw `DerivationEnv`. The
  obligation becomes load-bearing only at the recovery boundary. The
  kernel makes monotonicity expressible; the runtime makes it
  non-optional.
-/

/--
  A recovery-capable derivation environment: an underlying
  `DerivationEnv` together with a discharged `CorrectiveMonotone`
  obligation. Construction requires the witness; no `RecoveryEnv` exists
  without one.
-/
structure RecoveryEnv where
  env : DerivationEnv
  correctiveMonotone : CorrectiveMonotone env

/--
  Recovery-facing applier. The signature requires a `RecoveryEnv`,
  which is the gate: callers cannot reach this entry without supplying
  the monotonicity witness. The body is just `applySteps` — no magic,
  just a wrapper whose *type* enforces the obligation.

  Caller is responsible for the per-step `IsCorrective` proof; this
  applier does not silently accept forward steps.
-/
noncomputable def applyCorrectiveRecovery
    (_renv : RecoveryEnv)
    (Γ : GovState)
    (steps : List Step)
    (_hAll : ∀ s ∈ steps, IsCorrective s) : GovState :=
  applySteps Γ steps

/--
  Recovery is monotone. Boring projection through the `RecoveryEnv`
  bundle plus `corrective_sequence_monotone`.
-/
theorem recovery_monotone
    (renv : RecoveryEnv)
    (Γ : GovState) (steps : List Step)
    (hAll : ∀ s ∈ steps, IsCorrective s) :
    WeaklyLessPermissive renv.env
      (applyCorrectiveRecovery renv Γ steps hAll) Γ := by
  unfold applyCorrectiveRecovery
  exact corrective_sequence_monotone renv.correctiveMonotone Γ steps hAll

/-
  Open questions (pinned — this is candidate / non-binding):

  1. Could a future receipt schema make `recordReceipt` authority-
     relevant? If so, split the transition: `recordReceipt` remains
     neutral ingest, while `admitReceiptAsBasis` or equivalent becomes
     the forward / authority-relevant constructor. Do not let receipt
     persistence and authority admission collapse into one Step.

  2. Re-entry as a Step. The doctrine spine —
     "old K invalidated → fresh K' through normal admissibility path" —
     is currently expressible as a *sequence* of (corrective) +
     (forward) Steps. If `requireReentry` becomes a first-class Step,
     it must be classified corrective (down-edge: marks Γ as requiring
     a fresh basis) and must not by itself create authority. The forward
     half belongs in `amendPolicy`-class constructors.

  3. `fork` vs `promote`. If continuity-fork lands as a Step, it is
     corrective (separation / quarantine). Promotion of a forked lineage
     to authority-bearing must be a *separate* forward Step, never a
     side-effect of the fork. Otherwise "we split the state lineage"
     becomes "and one branch is now blessed because vibes."

  4. `CorrectiveMonotone env` is currently an empty obligation
     vacuously satisfiable for any `env`, because behavioral laws on
     `appendRevocation` and `appendGap` are not yet present in the
     Derivation module. The forcing case for moving the laws out of
     deferred status is the first concrete `BasisDerivation` that
     reads `RevocationStore` — at which point the proof obligation
     bites.

  5. Environment mutation. `WeaklyLessPermissive` fixes `env`. A future
     theorem must address the case where `env` itself changes (e.g.
     replacing a `BasisDerivation`); that is a separate laundering
     vector and a separate proof obligation. Do not silently merge
     into `CorrectiveMonotone`.

  6. Higher-order authorization. The doctrine carve-out
     ("authority-increasing recovery requires a separate higher-order
     authorization path") becomes, in this kernel, simply: the higher-
     order path is a `Step` not classified `corrective`. There is no
     special exception type. If a future construct *needs* an
     in-corrective authority bump, that is the signal to refactor, not
     to add an exception flag.

  7. Typeclass promotion of `CorrectiveMonotone`. Currently kept as an
     explicit-witness structure carried by `RecoveryEnv`. Promoting to
     a typeclass (so any `DerivationEnv` in scope automatically resolves
     a monotonicity instance) is premature while the obligation shape
     is still moving. Reconsider after the first concrete
     `BasisDerivation` reading `RevocationStore` lands and the
     obligation stops being vacuous.
-/

end Admissibility.Corrective
