/-
  Custody-Class: ANNEX

  BoundedCalculi.TemporalCustody -- execution-time gates for witnessed
  temporal use. Citation-time validity, artifact freshness, epoch liveness,
  replay identity, expiry, and version match remain separate witnesses.
-/

namespace LeanProofs.BoundedCalculi.TemporalCustody

abbrev Time := Nat
abbrev Epoch := Nat
abbrev OperationId := Nat
abbrev Version := Nat

/-! ## Syntax -/

structure WitnessedTime where
  tick : Time

structure Expiry where
  tick : Time

structure Artifact where
  witnessed : WitnessedTime
  expiry : Expiry
  signed : Bool
  version : Version

structure Action where
  artifact : Artifact
  citedAt : Time
  executedAt : Time
  epoch : Epoch
  operation : OperationId
  observedVersion : Version
  versionBoundMutation : Bool

structure Env where
  liveEpoch : Epoch -> Prop
  replaySafe : OperationId -> Prop
  currentVersion : Version

/-! ## Gate predicates -/

def SignedArtifact (a : Action) : Prop :=
  a.artifact.signed = true

def CitationTimeValid (a : Action) : Prop :=
  a.artifact.witnessed.tick <= a.citedAt ∧
  a.citedAt <= a.artifact.expiry.tick

def FreshAtUse (a : Action) : Prop :=
  a.artifact.witnessed.tick <= a.executedAt ∧
  a.executedAt <= a.artifact.expiry.tick

def LiveEpoch (env : Env) (a : Action) : Prop :=
  env.liveEpoch a.epoch

def ReplaySafeOperation (env : Env) (a : Action) : Prop :=
  env.replaySafe a.operation

def VersionMatch (env : Env) (a : Action) : Prop :=
  a.versionBoundMutation = true -> a.observedVersion = env.currentVersion

/-! ## Judgment -/

inductive TemporallyValid (env : Env) : Action -> Prop where
  | checked {a : Action} :
      FreshAtUse a ->
      LiveEpoch env a ->
      ReplaySafeOperation env a ->
      VersionMatch env a ->
        TemporallyValid env a

theorem checked_action_temporally_valid
    {env : Env} {a : Action}
    (hfresh : FreshAtUse a)
    (hepoch : LiveEpoch env a)
    (hreplay : ReplaySafeOperation env a)
    (hversion : VersionMatch env a) :
    TemporallyValid env a :=
  TemporallyValid.checked hfresh hepoch hreplay hversion

/-! ## Required-witness projections -/

theorem temporally_valid_requires_fresh_at_use
    {env : Env} {a : Action}
    (h : TemporallyValid env a) :
    FreshAtUse a := by
  cases h with
  | checked hfresh _ _ _ => exact hfresh

theorem temporally_valid_requires_live_epoch
    {env : Env} {a : Action}
    (h : TemporallyValid env a) :
    LiveEpoch env a := by
  cases h with
  | checked _ hepoch _ _ => exact hepoch

theorem temporally_valid_requires_replay_safe_operation
    {env : Env} {a : Action}
    (h : TemporallyValid env a) :
    ReplaySafeOperation env a := by
  cases h with
  | checked _ _ hreplay _ => exact hreplay

theorem temporally_valid_requires_version_match
    {env : Env} {a : Action}
    (h : TemporallyValid env a) :
    VersionMatch env a := by
  cases h with
  | checked _ _ _ hversion => exact hversion

theorem not_fresh_at_use_blocks_temporal_validity
    {env : Env} {a : Action}
    (hnot : ¬ FreshAtUse a) :
    ¬ TemporallyValid env a := by
  intro h
  exact hnot (temporally_valid_requires_fresh_at_use h)

theorem dead_epoch_blocks_temporal_validity
    {env : Env} {a : Action}
    (hnot : ¬ LiveEpoch env a) :
    ¬ TemporallyValid env a := by
  intro h
  exact hnot (temporally_valid_requires_live_epoch h)

theorem replay_unsafe_blocks_temporal_validity
    {env : Env} {a : Action}
    (hnot : ¬ ReplaySafeOperation env a) :
    ¬ TemporallyValid env a := by
  intro h
  exact hnot (temporally_valid_requires_replay_safe_operation h)

theorem version_mismatch_blocks_temporal_validity
    {env : Env} {a : Action}
    (hnot : ¬ VersionMatch env a) :
    ¬ TemporallyValid env a := by
  intro h
  exact hnot (temporally_valid_requires_version_match h)

theorem any_missing_required_component_blocks_temporal_validity
    {env : Env} {a : Action}
    (hmissing :
      ¬ FreshAtUse a ∨
      ¬ LiveEpoch env a ∨
      ¬ ReplaySafeOperation env a ∨
      ¬ VersionMatch env a) :
    ¬ TemporallyValid env a := by
  intro hvalid
  cases hmissing with
  | inl hnotFresh =>
      exact hnotFresh (temporally_valid_requires_fresh_at_use hvalid)
  | inr rest =>
      cases rest with
      | inl hnotEpoch =>
          exact hnotEpoch (temporally_valid_requires_live_epoch hvalid)
      | inr rest2 =>
          cases rest2 with
          | inl hnotReplay =>
              exact hnotReplay
                (temporally_valid_requires_replay_safe_operation hvalid)
          | inr hnotVersion =>
              exact hnotVersion (temporally_valid_requires_version_match hvalid)

theorem temporally_valid_iff_all_use_time_gates
    {env : Env} {a : Action} :
    TemporallyValid env a ↔
      FreshAtUse a ∧
      LiveEpoch env a ∧
      ReplaySafeOperation env a ∧
      VersionMatch env a := by
  constructor
  · intro h
    exact ⟨temporally_valid_requires_fresh_at_use h,
      temporally_valid_requires_live_epoch h,
      temporally_valid_requires_replay_safe_operation h,
      temporally_valid_requires_version_match h⟩
  · intro h
    exact checked_action_temporally_valid h.1 h.2.1 h.2.2.1 h.2.2.2

theorem citation_signature_freshness_do_not_discharge_epoch_replay_version
    {env : Env} {a : Action}
    (_hcitation : CitationTimeValid a)
    (_hsigned : SignedArtifact a)
    (_hfresh : FreshAtUse a)
    (hmissing :
      ¬ LiveEpoch env a ∨
      ¬ ReplaySafeOperation env a ∨
      ¬ VersionMatch env a) :
    ¬ TemporallyValid env a := by
  exact any_missing_required_component_blocks_temporal_validity
    (Or.inr hmissing)

/-- Laundering wall: citation-time validity and signature do not discharge any
    missing use-time gate. This is the generic replacement for relying on a
    concrete stale-at-execution arithmetic specimen. -/
theorem citation_and_signature_do_not_discharge_missing_use_time_component
    {env : Env} {a : Action}
    (_hcitation : CitationTimeValid a)
    (_hsigned : SignedArtifact a)
    (hmissing :
      ¬ FreshAtUse a ∨
      ¬ LiveEpoch env a ∨
      ¬ ReplaySafeOperation env a ∨
      ¬ VersionMatch env a) :
    ¬ TemporallyValid env a :=
  any_missing_required_component_blocks_temporal_validity hmissing

/-! ## Specimens

  The following concrete actions are examples only. The generic laundering wall
  is `citation_and_signature_do_not_discharge_missing_use_time_component`; the
  arithmetic facts below witness that the wall is nonempty, but they are not the
  central theorem pressure of the module. -/

def permissiveEnv : Env where
  liveEpoch := fun _ => True
  replaySafe := fun _ => True
  currentVersion := 1

def staleAtExecutionAction : Action where
  artifact := {
    witnessed := { tick := 0 }
    expiry := { tick := 10 }
    signed := true
    version := 1
  }
  citedAt := 5
  executedAt := 20
  epoch := 0
  operation := 7
  observedVersion := 1
  versionBoundMutation := true

def deadEpochEnv : Env where
  liveEpoch := fun _ => False
  replaySafe := fun _ => True
  currentVersion := 1

def freshDeadEpochAction : Action where
  artifact := {
    witnessed := { tick := 0 }
    expiry := { tick := 20 }
    signed := true
    version := 1
  }
  citedAt := 1
  executedAt := 5
  epoch := 3
  operation := 8
  observedVersion := 1
  versionBoundMutation := true

def versionMismatchEnv : Env where
  liveEpoch := fun _ => True
  replaySafe := fun _ => True
  currentVersion := 2

def freshVersionMismatchAction : Action where
  artifact := {
    witnessed := { tick := 0 }
    expiry := { tick := 20 }
    signed := true
    version := 1
  }
  citedAt := 1
  executedAt := 5
  epoch := 3
  operation := 9
  observedVersion := 1
  versionBoundMutation := true

def fullyCheckedAction : Action where
  artifact := {
    witnessed := { tick := 0 }
    expiry := { tick := 20 }
    signed := true
    version := 1
  }
  citedAt := 1
  executedAt := 5
  epoch := 3
  operation := 10
  observedVersion := 1
  versionBoundMutation := true

/-! ## Positive path -/

theorem fully_checked_action_temporally_valid :
    TemporallyValid permissiveEnv fullyCheckedAction := by
  refine TemporallyValid.checked ?_ ?_ ?_ ?_
  · unfold FreshAtUse fullyCheckedAction
    decide
  · unfold LiveEpoch permissiveEnv
    trivial
  · unfold ReplaySafeOperation permissiveEnv
    trivial
  · intro _hbound
    unfold fullyCheckedAction permissiveEnv
    rfl

/-! ## Negative no-laundering receipts -/

theorem staleAtExecution_cited_while_valid :
    CitationTimeValid staleAtExecutionAction := by
  unfold CitationTimeValid staleAtExecutionAction
  decide

theorem staleAtExecution_not_temporally_valid :
    ¬ TemporallyValid permissiveEnv staleAtExecutionAction := by
  intro h
  cases h with
  | checked hfresh _ _ _ =>
      exact (by decide : ¬ (20 <= 10)) hfresh.2

theorem citation_time_validity_does_not_imply_execution_admissibility :
    ∃ (env : Env) (a : Action),
      CitationTimeValid a ∧ ¬ TemporallyValid env a :=
  ⟨permissiveEnv,
   staleAtExecutionAction,
   staleAtExecution_cited_while_valid,
   staleAtExecution_not_temporally_valid⟩

theorem fresh_signed_artifact_does_not_imply_live_epoch :
    ∃ (env : Env) (a : Action),
      SignedArtifact a ∧ FreshAtUse a ∧
      ¬ LiveEpoch env a ∧ ¬ TemporallyValid env a := by
  refine ⟨deadEpochEnv, freshDeadEpochAction, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold SignedArtifact freshDeadEpochAction
    rfl
  · unfold FreshAtUse freshDeadEpochAction
    decide
  · unfold LiveEpoch deadEpochEnv
    intro h
    exact h
  · intro h
    cases h with
    | checked _ hepoch _ _ =>
        exact hepoch

theorem fresh_observation_does_not_imply_version_valid_mutation :
    ∃ (env : Env) (a : Action),
      FreshAtUse a ∧ ¬ VersionMatch env a ∧
      ¬ TemporallyValid env a := by
  refine ⟨versionMismatchEnv, freshVersionMismatchAction, ?_, ?_, ?_⟩
  · unfold FreshAtUse freshVersionMismatchAction
    decide
  · unfold VersionMatch versionMismatchEnv freshVersionMismatchAction
    intro h
    exact (by decide : (1 : Nat) ≠ 2) (h rfl)
  · intro h
    cases h with
    | checked _ _ _ hversion =>
        unfold VersionMatch versionMismatchEnv freshVersionMismatchAction at hversion
        exact (by decide : (1 : Nat) ≠ 2) (hversion rfl)

end LeanProofs.BoundedCalculi.TemporalCustody

