/-
  Custody-Class: ANNEX

  BoundedCalculi.BootKernel -- boot stages and baseline settlement (genesis
  calculus, roadmap S7). Release-surface bounded lifecycle calculus (v3.0.0 -
  Bounded Lifecycle Calculi).

  RELEASE-SURFACE, NOT AUTHORITY:
    * NOT imported by promoted kernels (`LeanProofs.lean` untouched).
    * NOT a unified admissibility calculus; no master `Admissible` judgment.
    * NOT runtime authority; boot here is a stage discipline, not a bootloader.
    * NOT sequent composition (custody-indexed sequents are v3.x scratch).
    * The aggregate import (`BoundedCalculi.lean`) proves checkability /
      coexistence only.
  Promoted Scratch -> ANNEX by operator decision 2026-07-01 (v3 release fork).
  Audit trail: docs/CHANGELOG-scratch-campaign.md + .governor/loop.json.

  GOBLIN WARD (read this before reading `capabilities_accumulate`): boot
  capability accumulation is staged/nested monotonicity along a witnessed
  ladder. It is NOT root omnipotence and NOT arbitrary signed operator
  authority -- no signature vocabulary exists in this file, every rung has a
  witness obligation, and `cold_start_single_exit` is the anti-skip wall.
  Accumulation is not escalation.

  Boot ladder: ColdStart -> DiscoveryOnly -> BaselineObserved -> BaselineSettled
  -> TicketMintingEnabled -> ExecutionEnabled.

  Design discipline:
  * Capabilities are per-capability stage predicates (`MayDiscover`,
    `MayMintTicket`, `MayMutate`) and CUMULATIVE along the ladder --
    `capabilities_accumulate` states the nesting explicitly (audit 2026-07-01:
    the first draft claimed "no rank scale"; the nesting is derivable, so it is
    now a documented design fact -- boot is monotone by design). The
    anti-master content is NOT capability independence: it is the anti-skip
    wall, the per-rung witness obligations, and the absence of any vocabulary
    for external/root authority.
  * There is NO signature, operator-token, or root-authority vocabulary in this
    file. The forbidden `RootAuthority signed_by_operator` shortcut is blocked
    by STRUCTURAL ABSENCE: no rule consumes a signature, and the anti-skip wall
    (`cold_start_single_exit`) proves the only exit from cold start is
    discovery -- there is no rule shape a signed root token could ride in on.
  * Settlement is a DISTINCT artifact type from observation
    (`SettlementWitness` vs `Observation`): observations cannot self-settle;
    the settle rule demands a witness that names exactly the observed baseline.

  Load-bearing results:
  * `settled_requires_settlement_witness` -- inductive invariant over ALL boot
    trajectories: every settled-or-later state carries a settlement witness.
    Non-collapse under composition, not a one-step toy.
  * `minting_stage_carries_settlement_witness` -- the capability-custody link:
    no ticket minting without a witnessed settlement.
  * `baseline_observed_does_not_imply_settled` -- reachable observed state with
    `settlement = none` (minimal pair with the settled specimen).
  * `settlement_freezes_baseline` -- no observation can move the baseline after
    settlement (settled baselines do not drift).
  * `cold_start_single_exit` -- anti-skip wall.
  * `discovery_does_not_imply_mutation` / `no_mutation_before_execution_enabled`
    -- discovery-class boot grants no mutation authority.
  * `kernel_boot_does_not_imply_root_omnipotence` -- a fully-booted kernel
    still holds no external claim it was not granted (parametrized non-transfer,
    per the wiring-probe precedent; there is no master judgment to leak into).

  Honesty notes:
  * The safety non-transfer is a product pairing against the REAL
    `SafetyPreservation` toy specimen (as in the wiring probe): it shows
    coexistence; the structural wall is that this file's vocabulary cannot
    state safety at all.
  * `Observation.content : Nat` is a placeholder payload; what counts as a
    discovery-class observation is consumer policy, not this calculus.

  Mathlib-free.
-/

import LeanProofs.BoundedCalculi.SafetyPreservation

namespace LeanProofs.BoundedCalculi.BootKernel

open LeanProofs.BoundedCalculi

/-! ## Stages, artifacts, state -/

inductive BootStage where
  | coldStart
  | discoveryOnly
  | baselineObserved
  | baselineSettled
  | ticketMintingEnabled
  | executionEnabled
  deriving DecidableEq

/-- A discovery-class observation (payload abstracted). -/
structure Observation where
  content : Nat
  deriving DecidableEq

/-- The record a settlement witness settles. -/
structure BaselineRecord where
  observations : List Observation
  deriving DecidableEq

/-- A settlement witness: a DISTINCT artifact type from observation, naming the
    baseline it settles. Observations cannot self-settle. -/
structure SettlementWitness where
  settledBaseline : BaselineRecord
  deriving DecidableEq

structure BootState where
  stage : BootStage
  observed : List Observation
  settlement : Option SettlementWitness

def initialState : BootState :=
  { stage := .coldStart, observed := [], settlement := none }

/-! ## Capabilities (per-capability, no rank scale) -/

def MayDiscover : BootStage → Prop
  | .coldStart => False
  | _ => True

def MayMintTicket : BootStage → Prop
  | .ticketMintingEnabled => True
  | .executionEnabled => True
  | _ => False

def MayMutate : BootStage → Prop
  | .executionEnabled => True
  | _ => False

/-! ## Boot steps and reachability -/

inductive BootStep : BootState → BootState → Prop where
  | beginDiscovery {s : BootState} :
      s.stage = .coldStart →
      BootStep s { s with stage := .discoveryOnly }
  | observe {s : BootState} (o : Observation) :
      (s.stage = .discoveryOnly ∨ s.stage = .baselineObserved) →
      BootStep s { s with stage := .baselineObserved, observed := o :: s.observed }
  | settle {s : BootState} (w : SettlementWitness) :
      s.stage = .baselineObserved →
      w.settledBaseline.observations = s.observed →
      BootStep s { s with stage := .baselineSettled, settlement := some w }
  | enableMinting {s : BootState} :
      s.stage = .baselineSettled →
      BootStep s { s with stage := .ticketMintingEnabled }
  | enableExecution {s : BootState} :
      s.stage = .ticketMintingEnabled →
      BootStep s { s with stage := .executionEnabled }

inductive BootReaches : BootState → BootState → Prop where
  | refl {s : BootState} : BootReaches s s
  | step {s mid final : BootState} :
      BootStep s mid → BootReaches mid final → BootReaches s final

/-! ## Positive paths -/

/-- Kernel boot permits discovery-class capability -- and nothing more yet. -/
theorem boot_permits_discovery :
    BootStep initialState { initialState with stage := .discoveryOnly } ∧
    MayDiscover BootStage.discoveryOnly :=
  ⟨BootStep.beginDiscovery rfl, trivial⟩

def obs0 : Observation := { content := 0 }

def observedState : BootState :=
  { stage := .baselineObserved, observed := [obs0], settlement := none }

/-- Discovery observations contribute to baseline observation. -/
theorem observed_is_reachable : BootReaches initialState observedState :=
  BootReaches.step (BootStep.beginDiscovery rfl)
    (BootReaches.step (BootStep.observe obs0 (Or.inl rfl)) BootReaches.refl)

def settlementW : SettlementWitness :=
  { settledBaseline := { observations := [obs0] } }

def settledState : BootState :=
  { stage := .baselineSettled, observed := [obs0], settlement := some settlementW }

/-- Baseline settlement via a distinct settlement witness naming exactly the
    observed baseline. -/
theorem settled_is_reachable : BootReaches initialState settledState :=
  BootReaches.step (BootStep.beginDiscovery rfl)
    (BootReaches.step (BootStep.observe obs0 (Or.inl rfl))
      (BootReaches.step (BootStep.settle settlementW rfl rfl)
        BootReaches.refl))

def bootedState : BootState :=
  { stage := .executionEnabled, observed := [obs0], settlement := some settlementW }

/-- The full boot: cold start to execution, every rung witnessed. -/
theorem full_boot_reachable : BootReaches initialState bootedState :=
  BootReaches.step (BootStep.beginDiscovery rfl)
    (BootReaches.step (BootStep.observe obs0 (Or.inl rfl))
      (BootReaches.step (BootStep.settle settlementW rfl rfl)
        (BootReaches.step (BootStep.enableMinting rfl)
          (BootReaches.step (BootStep.enableExecution rfl)
            BootReaches.refl))))

/-! ## Non-collapse: discovery grants no mutation -/

theorem discovery_does_not_imply_mutation :
    MayDiscover BootStage.discoveryOnly ∧
    ¬ MayMutate BootStage.discoveryOnly ∧
    ¬ MayMintTicket BootStage.discoveryOnly :=
  ⟨trivial, fun h => h, fun h => h⟩

/-- Mutation authority exists at exactly one stage. -/
theorem no_mutation_before_execution_enabled :
    ∀ st : BootStage, st ≠ .executionEnabled → ¬ MayMutate st := by
  intro st hne
  cases st <;> first
    | exact fun h => h
    | exact fun _ => hne rfl

/-! ## Non-collapse: observed is not settled -/

theorem baseline_observed_does_not_imply_settled :
    BootReaches initialState observedState ∧
    observedState.stage = .baselineObserved ∧
    observedState.settlement = none :=
  ⟨observed_is_reachable, rfl, rfl⟩

/-! ## The settlement-witness invariant (non-collapse under composition) -/

def SettledOrLater : BootStage → Prop
  | .baselineSettled => True
  | .ticketMintingEnabled => True
  | .executionEnabled => True
  | _ => False

/-- The invariant engine: if a state satisfies "settled implies witnessed",
    every state it reaches does too. Induction over arbitrary boot
    trajectories -- the wall survives composition. -/
theorem reaches_preserves_witness_invariant
    {s final : BootState}
    (h : BootReaches s final)
    (hInv : SettledOrLater s.stage → ∃ w, s.settlement = some w) :
    SettledOrLater final.stage → ∃ w, final.settlement = some w := by
  induction h with
  | refl => exact hInv
  | step hstep _ ih =>
      apply ih
      cases hstep with
      | beginDiscovery _ => exact fun hS => hS.elim
      | observe _ _ => exact fun hS => hS.elim
      | settle w _ _ => exact fun _ => ⟨w, rfl⟩
      | enableMinting hstage =>
          exact fun _ => hInv (by rw [hstage]; trivial)
      | enableExecution hstage =>
          exact fun _ => hInv (by rw [hstage]; trivial)

/-- **Settlement requires a witness:** every boot trajectory from cold start
    that reaches a settled-or-later stage carries a settlement witness. There
    is no witness-free path to settlement -- BaselineObserved does not imply
    BaselineSettled at any depth of composition. -/
theorem settled_requires_settlement_witness
    {final : BootState}
    (h : BootReaches initialState final)
    (hstage : SettledOrLater final.stage) :
    ∃ w, final.settlement = some w :=
  reaches_preserves_witness_invariant h (fun hS => hS.elim) hstage

/-- The coverage version of the invariant engine: settled-or-later states carry
    a witness naming EXACTLY the observed baseline (presence + coverage),
    preserved through every later stage. -/
theorem reaches_preserves_coverage_invariant
    {s final : BootState}
    (h : BootReaches s final)
    (hInv : SettledOrLater s.stage →
      ∃ w, s.settlement = some w ∧
        w.settledBaseline.observations = s.observed) :
    SettledOrLater final.stage →
      ∃ w, final.settlement = some w ∧
        w.settledBaseline.observations = final.observed := by
  induction h with
  | refl => exact hInv
  | step hstep _ ih =>
      apply ih
      cases hstep with
      | beginDiscovery _ => exact fun hS => hS.elim
      | observe _ _ => exact fun hS => hS.elim
      | settle w _ hcov => exact fun _ => ⟨w, rfl, hcov⟩
      | enableMinting hstage =>
          exact fun _ => hInv (by rw [hstage]; trivial)
      | enableExecution hstage =>
          exact fun _ => hInv (by rw [hstage]; trivial)

/-- **Settlement coverage:** every reachable settled-or-later state holds a
    witness naming exactly its observed baseline. Not just "a witness exists" --
    the witness is ABOUT the baseline that was actually observed, at every
    depth of composition. -/
theorem settled_witness_covers_observed_baseline
    {final : BootState}
    (h : BootReaches initialState final)
    (hstage : SettledOrLater final.stage) :
    ∃ w, final.settlement = some w ∧
      w.settledBaseline.observations = final.observed :=
  reaches_preserves_coverage_invariant h (fun hS => hS.elim) hstage

/-- Minting capability implies a settled-or-later stage. -/
theorem mayMint_settledOrLater {st : BootStage}
    (h : MayMintTicket st) : SettledOrLater st := by
  cases st <;> first
    | exact h.elim
    | trivial

/-- **The capability-custody link:** no ticket minting without a witnessed
    settlement. Any reachable state whose stage grants `MayMintTicket` holds a
    settlement witness. -/
theorem minting_stage_carries_settlement_witness
    {final : BootState}
    (h : BootReaches initialState final)
    (hmint : MayMintTicket final.stage) :
    ∃ w, final.settlement = some w :=
  settled_requires_settlement_witness h (mayMint_settledOrLater hmint)

/-! ## Settled baselines do not drift -/

/-- **Settlement freezes the baseline:** no step from a settled-or-later state
    changes the observed baseline or the settlement witness. Observation is a
    pre-settlement capability; there is no rule to re-open a settled record. -/
theorem settlement_freezes_baseline
    {s s' : BootState}
    (hstep : BootStep s s')
    (hsettled : SettledOrLater s.stage) :
    s'.observed = s.observed ∧ s'.settlement = s.settlement := by
  cases hstep with
  | beginDiscovery h => rw [h] at hsettled; exact hsettled.elim
  | observe _ hor =>
      cases hor with
      | inl h => rw [h] at hsettled; exact hsettled.elim
      | inr h => rw [h] at hsettled; exact hsettled.elim
  | settle _ hstage _ => rw [hstage] at hsettled; exact hsettled.elim
  | enableMinting _ => exact ⟨rfl, rfl⟩
  | enableExecution _ => exact ⟨rfl, rfl⟩

/-- Boot capabilities accumulate monotonically along the ladder (a booted
    kernel keeps its earlier capabilities). Stated as a theorem so the nesting
    is a documented fact, not a hidden rank (audit-requested honesty,
    2026-07-01). -/
theorem capabilities_accumulate :
    (∀ st : BootStage, MayMutate st → MayMintTicket st) ∧
    (∀ st : BootStage, MayMintTicket st → MayDiscover st) := by
  constructor
  · intro st h
    cases st <;> first | exact h.elim | trivial
  · intro st h
    cases st <;> first | exact h.elim | trivial

/-! ## Trajectory-level freeze (audit-requested, 2026-07-01) -/

/-- A step from a settled-or-later state stays settled-or-later: the ladder
    has no path back below settlement. -/
theorem step_from_settled_stays_settled
    {s s' : BootState}
    (hstep : BootStep s s')
    (hsettled : SettledOrLater s.stage) :
    SettledOrLater s'.stage := by
  cases hstep with
  | beginDiscovery h => rw [h] at hsettled; exact hsettled.elim
  | observe _ hor =>
      cases hor with
      | inl h => rw [h] at hsettled; exact hsettled.elim
      | inr h => rw [h] at hsettled; exact hsettled.elim
  | settle _ hstage _ => rw [hstage] at hsettled; exact hsettled.elim
  | enableMinting _ => trivial
  | enableExecution _ => trivial

/-- **Trajectory-level freeze:** from any settled-or-later state, the ENTIRE
    reachable future preserves the observed baseline and the settlement witness
    -- not just one step. The settled record cannot drift at any depth. -/
theorem reaches_from_settled_freezes_baseline
    {s final : BootState}
    (h : BootReaches s final) :
    SettledOrLater s.stage →
      final.observed = s.observed ∧ final.settlement = s.settlement := by
  induction h with
  | refl => exact fun _ => ⟨rfl, rfl⟩
  | step hstep _ ih =>
      intro hsettled
      have hfreeze := settlement_freezes_baseline hstep hsettled
      have hrest := ih (step_from_settled_stays_settled hstep hsettled)
      exact ⟨hrest.1.trans hfreeze.1, hrest.2.trans hfreeze.2⟩

/-! ## Ladder-entry inversions (audit-requested, 2026-07-01) -/

/-- Settlement is entered only from an observed baseline, and only by the
    settle rule -- so the entering state hands over a witness. -/
theorem settled_entered_only_from_observed
    {s s' : BootState}
    (hstep : BootStep s s')
    (hsettled : s'.stage = .baselineSettled) :
    s.stage = .baselineObserved ∧ ∃ w, s'.settlement = some w := by
  cases hstep with
  | beginDiscovery _ => exact nomatch hsettled
  | observe _ _ => exact nomatch hsettled
  | settle w hstage _ => exact ⟨hstage, w, rfl⟩
  | enableMinting _ => exact nomatch hsettled
  | enableExecution _ => exact nomatch hsettled

/-- Execution is entered only from the minting stage: no rule jumps to the top
    of the ladder. -/
theorem execution_entered_only_from_minting
    {s s' : BootState}
    (hstep : BootStep s s')
    (hexec : s'.stage = .executionEnabled) :
    s.stage = .ticketMintingEnabled := by
  cases hstep with
  | beginDiscovery _ => exact nomatch hexec
  | observe _ _ => exact nomatch hexec
  | settle _ _ _ => exact nomatch hexec
  | enableMinting _ => exact nomatch hexec
  | enableExecution hstage => exact hstage

/-! ## Anti-skip wall (no signed shortcut) -/

/-- **Cold start has a single exit: discovery.** No rule shape exists for a
    root token, operator signature, or any other artifact to skip a booting
    kernel past discovery. The absent `RootAuthority signed_by_operator` is not
    an oversight; this theorem is its refusal. -/
theorem cold_start_single_exit
    {s s' : BootState}
    (hstep : BootStep s s')
    (hcold : s.stage = .coldStart) :
    s'.stage = .discoveryOnly := by
  cases hstep with
  | beginDiscovery _ => rfl
  | observe _ hor =>
      cases hor with
      | inl h => rw [hcold] at h; exact nomatch h
      | inr h => rw [hcold] at h; exact nomatch h
  | settle _ hstage _ => rw [hcold] at hstage; exact nomatch hstage
  | enableMinting hstage => rw [hcold] at hstage; exact nomatch hstage
  | enableExecution hstage => rw [hcold] at hstage; exact nomatch hstage

/-! ## Non-transfer: boot is not omnipotence, settlement is not safety -/

/-- **Kernel boot does not imply root omnipotence** -- schema form. This is the
    parametrized-external-claim SCHEMA (the wiring-probe precedent for a
    forbidden master target): it documents that full boot coexists with any
    unheld external claim, i.e. there is no master judgment here for boot
    authority to leak into. It is deliberately thin (audit 2026-07-01: the
    HARD walls are `cold_start_single_exit`, the witness invariants, and the
    absent root/signature vocabulary -- this theorem just names the absent
    leak target). -/
theorem kernel_boot_does_not_imply_root_omnipotence
    {ExternalClaim : Prop} (hnot : ¬ ExternalClaim) :
    (BootReaches initialState bootedState ∧
      MayMutate bootedState.stage ∧
      MayMintTicket bootedState.stage) ∧
    ¬ ExternalClaim :=
  ⟨⟨full_boot_reachable, trivial, trivial⟩, hnot⟩

/-- Baseline settlement does not imply safety preservation: a settled kernel
    coexists with a real refused safety judgment (product pairing against the
    REAL SafetyPreservation specimen; structurally, this file cannot state
    safety at all). -/
theorem baseline_settled_does_not_imply_safety :
    BootReaches initialState settledState ∧
    ¬ SafetyPreservation.SafeAllowed
        SafetyPreservation.toyEnv
        SafetyPreservation.ToyState.clean
        SafetyPreservation.ToyActor.operator
        SafetyPreservation.ToyAction.damage :=
  ⟨settled_is_reachable,
    SafetyPreservation.authorized_damage_step_cannot_be_safeAllowed.2⟩

end LeanProofs.BoundedCalculi.BootKernel
