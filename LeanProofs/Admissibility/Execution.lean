/-
  Admissibility — Execution bridge (Layer 4).

  Reference: governor doctrine; ties together
  LeanProofs/Admissibility/StateTransition.lean (StepAllowed — standing
  to mutate governance state) and
  LeanProofs/Admissibility/Derivation.lean (decideAuthority — basis +
  precedence + invocation standing for an AuthorityClaim).

  The missing product sentence:

    Mutation requires *both* a StepAllowed proof (mutation-side
    standing) AND an authorized AuthorityClaim (admissibility-side
    standing).

  Until this module landed, the kernel proved two separate things:
    - StateTransition: non-policy steps can't mutate PolicyStore;
      StepAllowed gates mutation.
    - Derivation: stale/revoked/etc. claim cannot produce Authorized.
  But not their composition. Without Execution.lean, "stale basis
  cannot bind" is true at the verdict layer but not at the mutation
  layer — a Step could be StepAllowed without its claim being
  Authorized.

  AuthorizedStep is a structure that bundles a Step with *both*
  proofs. By construction, you cannot get one without the other. The
  bridge invariant is then a load-bearing theorem:
  `revoked_basis_cannot_be_authorized_step`.

  Governor-neutral. Imports the three sibling Admissibility modules.
-/

import LeanProofs.Admissibility.Authority
import LeanProofs.Admissibility.StateTransition
import LeanProofs.Admissibility.Derivation

namespace Admissibility.Execution

open Admissibility.Authority
open Admissibility.StateTransition
open Admissibility.Derivation

/-! ### Execution environment -/

/--
  An execution environment carries:
  - a `DerivationEnv` (basis/precedence/standing strategies + their
    spec obligations);
  - a `claimForStep` resolver — how to extract the AuthorityClaim
    that justifies a given Step in a given state for a given actor.

  `claimForStep` is abstract here: concrete AG implementations later
  supply it (e.g. an `amendPolicy p` step resolves to the claim
  whose scope matches `p`'s target/effect).
-/
structure ExecutionEnv where
  derivation : DerivationEnv
  claimForStep : GovState → Actor → Step → AuthorityClaim

/-- Verdict for the AuthorityClaim that justifies a Step. -/
def stepAuthorityVerdict
    (env : ExecutionEnv)
    (state : GovState)
    (actor : Actor)
    (step : Step) : AuthorityVerdict :=
  decideAuthority
    env.derivation
    state
    actor
    (env.claimForStep state actor step)

/-! ### Authorized step — both proofs by construction -/

/--
  An authorized step bundles a Step with *both* permission proofs:
  - `stepAllowed` — mutation-side standing (from StateTransition)
  - `authorityAuthorized` — claim-side admissibility (from Derivation)

  No constructor without both. A caller cannot fabricate an
  `AuthorizedStep` by supplying only one half.
-/
structure AuthorizedStep
    (env : ExecutionEnv)
    (state : GovState)
    (actor : Actor) where
  step : Step
  stepAllowed : StepAllowed state actor step
  authorityAuthorized :
    stepAuthorityVerdict env state actor step =
      AuthorityVerdict.authorized

/--
  Execute an authorized step. The proofs are erased at runtime
  (parametric over them); the underlying mutation is the same
  `applyStep` from StateTransition.lean.
-/
noncomputable def executeAuthorizedStep
    {env : ExecutionEnv}
    {state : GovState}
    {actor : Actor}
    (authorizedStep : AuthorizedStep env state actor) : GovState :=
  applyStep state authorizedStep.step

/-! ### Trivial extraction -/

/-- Extract the claim-side authorization from an AuthorizedStep. -/
theorem authorized_step_requires_authority
    {env : ExecutionEnv}
    {state : GovState}
    {actor : Actor}
    (s : AuthorizedStep env state actor) :
    stepAuthorityVerdict env state actor s.step =
      AuthorityVerdict.authorized :=
  s.authorityAuthorized

/-! ### Load-bearing bridge theorem -/

/--
  If the AuthorityClaim that would justify a Step has its basis
  revoked, then no `AuthorizedStep` for that Step can exist. This is
  the sentence the kernel could not warrant before this module:
  *stale/revoked basis cannot bind at the execution layer*.
-/
theorem revoked_basis_cannot_be_authorized_step
    {env : ExecutionEnv}
    {state : GovState}
    {actor : Actor}
    {step : Step}
    (hrevoked :
      env.derivation.basis.basisRevoked
        state
        (env.claimForStep state actor step)) :
    ¬ ∃ s : AuthorizedStep env state actor, s.step = step := by
  intro h
  rcases h with ⟨s, hstep⟩
  have hauth : stepAuthorityVerdict env state actor step =
      AuthorityVerdict.authorized := by
    rw [← hstep]; exact s.authorityAuthorized
  unfold stepAuthorityVerdict at hauth
  exact revoked_basis_never_authorized
    env.derivation state actor
    (env.claimForStep state actor step)
    hrevoked hauth

/-! ### Lifted store-isolation invariants

  The three negative trapdoor invariants from StateTransition.lean
  lifted through `executeAuthorizedStep`. Even when both layers of
  permission are present, non-amendment steps still cannot mutate
  PolicyStore. Plus the positive witness: amendment still targets
  PolicyStore through the bridge.
-/

theorem authorized_record_receipt_does_not_amend_policy
    {env : ExecutionEnv}
    {state : GovState}
    {actor : Actor}
    (r : Receipt)
    (s : AuthorizedStep env state actor)
    (hstep : s.step = Step.recordReceipt r) :
    (executeAuthorizedStep s).policyStore = state.policyStore := by
  unfold executeAuthorizedStep
  rw [hstep]
  exact record_receipt_does_not_amend_policy state r

theorem authorized_declare_policy_gap_does_not_amend_policy
    {env : ExecutionEnv}
    {state : GovState}
    {actor : Actor}
    (g : Gap)
    (s : AuthorizedStep env state actor)
    (hstep : s.step = Step.declarePolicyGap g) :
    (executeAuthorizedStep s).policyStore = state.policyStore := by
  unfold executeAuthorizedStep
  rw [hstep]
  exact declare_policy_gap_does_not_amend_policy state g

theorem authorized_record_revocation_does_not_amend_policy
    {env : ExecutionEnv}
    {state : GovState}
    {actor : Actor}
    (rv : Revocation)
    (s : AuthorizedStep env state actor)
    (hstep : s.step = Step.recordRevocation rv) :
    (executeAuthorizedStep s).policyStore = state.policyStore := by
  unfold executeAuthorizedStep
  rw [hstep]
  exact record_revocation_does_not_amend_policy state rv

theorem authorized_amend_policy_targets_policy_store
    {env : ExecutionEnv}
    {state : GovState}
    {actor : Actor}
    (p : PolicyUpdate)
    (s : AuthorizedStep env state actor)
    (hstep : s.step = Step.amendPolicy p) :
    (executeAuthorizedStep s).policyStore =
      applyUpdate state.policyStore p := by
  unfold executeAuthorizedStep
  rw [hstep]
  exact amend_policy_targets_policy_store state p

/-
  TODO (deferred):

  - Concrete `claimForStep` resolvers. Tying a Step (e.g.
    `amendPolicy p`) to the AuthorityClaim whose scope justifies it
    requires concrete claim/scope structure — deferred along with
    `AuthorityClaim`'s schema.

  - Symmetric bridge theorems for the other dimensions, when their
    spec obligations are added in Derivation.lean:
      revoked_standing_cannot_be_authorized_step
      conflicting_precedence_cannot_be_authorized_step
      gap_implies_no_authorized_step

  - Bridge between this module's `AuthorizedStep` and a concrete
    governor execution loop (operational scheduler, retry policy,
    etc.). Out of scope for the formal kernel.
-/

end Admissibility.Execution
