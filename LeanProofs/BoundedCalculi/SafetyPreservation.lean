/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: STABLE-SURFACE

  BoundedCalculi.SafetyPreservation -- authorization plus a separate safety
  bridge. Authorization alone is intentionally insufficient.
-/

namespace LeanProofs.BoundedCalculi.SafetyPreservation

/-! ## Environment and judgment -/

structure Env (State Actor Action : Type) where
  run : State -> Action -> State
  allowed : State -> Actor -> Action -> Prop
  value : State -> Nat
  bridge : State -> Action -> Prop
  preserves :
    ∀ (st : State) (act : Action),
      bridge st act -> value st <= value (run st act)

inductive SafeAllowed
    {State Actor Action : Type}
    (E : Env State Actor Action)
    (st : State) (actor : Actor) (action : Action) : Prop where
  | intro :
      E.allowed st actor action ->
      E.bridge st action ->
        SafeAllowed E st actor action

theorem safeAllowed_preserves
    {State Actor Action : Type}
    {E : Env State Actor Action}
    {st : State} {actor : Actor} {action : Action}
    (h : SafeAllowed E st actor action) :
    E.value st <= E.value (E.run st action) := by
  cases h with
  | intro _ hbridge =>
      exact E.preserves st action hbridge

theorem authorization_without_bridge_cannot_be_safeAllowed
    {State Actor Action : Type}
    {E : Env State Actor Action}
    {st : State} {actor : Actor} {action : Action}
    (hauth : E.allowed st actor action)
    (hNoBridge : ¬ E.bridge st action) :
    E.allowed st actor action ∧
      ¬ SafeAllowed E st actor action := by
  refine ⟨hauth, ?_⟩
  intro hsafe
  cases hsafe with
  | intro _ hbridge =>
      exact hNoBridge hbridge

theorem bridge_evidence_is_transition_specific
    {State Actor Action : Type}
    {E : Env State Actor Action}
    {st : State} {actor : Actor} {safeAction otherAction : Action}
    (_hsafe : SafeAllowed E st actor safeAction)
    (hauthOther : E.allowed st actor otherAction)
    (hNoBridgeOther : ¬ E.bridge st otherAction) :
    E.allowed st actor otherAction ∧
      ¬ SafeAllowed E st actor otherAction :=
  authorization_without_bridge_cannot_be_safeAllowed
    hauthOther hNoBridgeOther

/-! ## Trajectories -/

inductive AuthorizedTrajectory
    {State Actor Action : Type}
    (E : Env State Actor Action) :
    State -> State -> Type where
  | nil (st : State) : AuthorizedTrajectory E st st
  | cons {st finish : State}
      (actor : Actor) (action : Action)
      (hauth : E.allowed st actor action)
      (rest : AuthorizedTrajectory E (E.run st action) finish) :
        AuthorizedTrajectory E st finish

inductive BridgedTrajectory
    {State Actor Action : Type}
    (E : Env State Actor Action) :
    State -> State -> Type where
  | nil (st : State) : BridgedTrajectory E st st
  | cons {st finish : State}
      {actor : Actor} {action : Action}
      (hop : SafeAllowed E st actor action)
      (rest : BridgedTrajectory E (E.run st action) finish) :
        BridgedTrajectory E st finish

def BridgedTrajectory.toAuthorizedTrajectory
    {State Actor Action : Type}
    {E : Env State Actor Action} :
    ∀ {start finish : State},
      BridgedTrajectory E start finish ->
        AuthorizedTrajectory E start finish
  | _, _, .nil st => .nil st
  | _, _, .cons (actor := actor) (action := action) hop rest =>
      match hop with
      | SafeAllowed.intro hauth _ =>
          .cons actor action hauth (toAuthorizedTrajectory rest)

theorem bridged_trajectory_preserves
    {State Actor Action : Type}
    {E : Env State Actor Action} :
    ∀ {start finish : State},
      BridgedTrajectory E start finish ->
        E.value start <= E.value finish
  | _, _, .nil _ => Nat.le_refl _
  | _, _, .cons hop rest =>
      Nat.le_trans (safeAllowed_preserves hop)
        (bridged_trajectory_preserves rest)

/- Laundering wall: an authorized path to a value-decreasing endpoint cannot be
   relabeled as a bridged path. The positive trajectory rule preserves value;
   this boundary theorem blocks laundering reachability into safety evidence. -/
theorem value_decrease_blocks_bridged_trajectory
    {State Actor Action : Type}
    {E : Env State Actor Action}
    {start finish : State}
    (hdrop : ¬ (E.value start <= E.value finish)) :
    ¬ Nonempty (BridgedTrajectory E start finish) := by
  rintro ⟨trajectory⟩
  exact hdrop (bridged_trajectory_preserves trajectory)

/-! ## Concrete no-lift specimen -/

inductive ToyState where
  | clean
  | damaged
deriving DecidableEq

inductive ToyActor where
  | operator

inductive ToyAction where
  | damage

def toyRun : ToyState -> ToyAction -> ToyState
  | .clean, .damage => .damaged
  | .damaged, .damage => .damaged

def toyValue : ToyState -> Nat
  | .clean => 1
  | .damaged => 0

def toyEnv : Env ToyState ToyActor ToyAction where
  run := toyRun
  allowed := fun _ _ _ => True
  value := toyValue
  bridge := fun _ _ => False
  preserves := by
    intro _ _ hbridge
    exact False.elim hbridge

def authorized_damage_trajectory :
    AuthorizedTrajectory toyEnv ToyState.clean ToyState.damaged :=
  AuthorizedTrajectory.cons
    ToyActor.operator
    ToyAction.damage
    trivial
    (AuthorizedTrajectory.nil ToyState.damaged)

theorem authorized_trajectory_does_not_imply_bridged_trajectory
    {State Actor Action : Type}
    {E : Env State Actor Action}
    {start finish : State}
    (hauth : AuthorizedTrajectory E start finish)
    (hdrop : ¬ (E.value start <= E.value finish)) :
    Nonempty (AuthorizedTrajectory E start finish) ∧
      ¬ Nonempty (BridgedTrajectory E start finish) :=
  ⟨⟨hauth⟩, value_decrease_blocks_bridged_trajectory hdrop⟩

theorem authorized_trajectory_need_not_lift_to_bridged :
    ∃ (finish : ToyState),
      Nonempty (AuthorizedTrajectory toyEnv ToyState.clean finish) ∧
      ¬ Nonempty (BridgedTrajectory toyEnv ToyState.clean finish) := by
  refine ⟨ToyState.damaged, ?_⟩
  apply authorized_trajectory_does_not_imply_bridged_trajectory
    authorized_damage_trajectory
  change ¬ (toyValue ToyState.clean <= toyValue ToyState.damaged)
  decide

theorem authorized_damage_step_cannot_be_safeAllowed :
    toyEnv.allowed ToyState.clean ToyActor.operator ToyAction.damage ∧
      ¬ SafeAllowed toyEnv ToyState.clean ToyActor.operator ToyAction.damage :=
  authorization_without_bridge_cannot_be_safeAllowed trivial (by intro h; exact h)

end LeanProofs.BoundedCalculi.SafetyPreservation

