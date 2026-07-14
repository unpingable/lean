/-
  Regulator Recovery — scratch specimen. Successor to
  `BindingSourceAblation.lean` (rung three of the intervention ladder).

  Custody-Class: SCRATCH

  Status: scratch, 2026-07-10 (revised same day per blind review:
  `RestoresSuppression` strengthened to same-option tracking; rung-two
  property renamed — a fatal consequence is not a binding). Not
  imported by `LeanProofs.lean`. Not part
  of any release surface. Not in the lakefile globs (compile-is-contact,
  checked per-file). No promotion path until register adjudication.

  Custody class: scratch-checked (direct `lake env lean` clean as of
  2026-07-10). Custody header per the 2026-06-06 Option C policy.

  Provenance: continuation of the 2026-07-09/10 binding-source thread.
  `BindingSourceAblation.lean` proved gate ablation separates external
  enforcement from viability coupling; it left rung three open: after
  ablation, a plant that suppresses its own violating option and a plant
  simply incapable of violating look identical. Operator ruling
  (2026-07-10): endogeneity must be a theorem about perturbation and
  recovery, not a structure-field name. A static `enabled` predicate
  placed inside the plant is type-identical to `Gate.allows` — "internal"
  by declaration is regulation-by-comment. So here the regulator is
  MUTABLE STATE, `enabled` is a descriptive projection reading that
  state, and the load-bearing property is `RestoresSuppression`: the
  plant's UNMODIFIED dynamics re-establish suppression after an external
  perturbation that exposed the latent capability.

  ── What this specimen proves ─────────────────────────────────────────

      A regulated plant (latent violating capability, suppressed by
      maintained state) and an incapable plant (no violating capability)
      have identical admitted traces from the maintained state under
      EVERY gate — the entire gate-intervention family, intact charter
      and full ablation included, cannot distinguish them
      (`no_gate_intervention_distinguishes`, quantified over all gates).
      Regulator perturbation can: it exposes the violating option in the
      regulated plant (positive witness), exposes nothing in the
      incapable plant, and the regulated plant's unchanged `tick`
      restores suppression (`RestoresSuppression`).

  Different rung, different instrument: gate ablation reveals external
  enforcement; regulator perturbation reveals maintained suppression.
  Each architectural claim requires an intervention capable of exposing
  the distinction it asserts.

  The load-bearing pieces, without which this is label algebra:

    1. The regulator is state. `perturb` moves state only; `capable`,
       `act`, `tick`, and the gate are untouched by the intervention,
       and restoration is performed by the SAME `tick` the plant always
       had. Endogeneity is earned by recovery, not by field placement.
    2. The positive exposure witness. `Suppresses` holds VACUOUSLY for
       the incapable plant (nothing capable violates), so suppression
       alone certifies nothing — the discriminator is that perturbation
       has purchase on the regulated plant and none on the incapable one.
    3. The all-gates quantifier. Trace equivalence is proved for every
       gate simultaneously, so the refusal covers the whole prior
       intervention family, not two samples from it.
    4. Same-option tracking. `RestoresSuppression` follows ONE violating
       option through suppression, exposure, and recovery — capable and
       violating at every phase — so recovery cannot be counterfeited by
       amputating the capability or reinterpreting the violation.

  The keeper sentence: a closed brake is a state; a system whose own
  unchanged dynamics re-engage the brake after it is knocked loose is
  regulating — and only the knock, not any gate, reveals which one you
  have.

  ── Scope fence (read before quoting) ─────────────────────────────────

    * `RestoresSuppression` establishes RESTORATIVE REGULATION relative
      to the declared plant boundary and the declared intervention
      family (gates + `perturb`). It is thermostat-grade. It does NOT
      establish organizational closure: the machinery performing the
      restoration is not itself shown to be maintained by the
      organization whose constraint it restores. That stronger object is
      the named next monster, deliberately not invited in here.
    * `enabled` and `capable` are descriptive projections. Nothing about
      their placement inside `RPlant` is evidentiary; the theorem
      obligation is recovery under unmodified dynamics.
    * `viable` is everywhere-true BY DESIGN: the regulated plant's
      exposed violation is harmless (`regulatedPlant_not_viability_destroying`),
      so its suppression is not viability coupling in disguise — this
      pins the specimen to rung three, not rung two.
    * The observation language is admitted action traces; `tick` and
      `perturb` are not trace-observable. `ViolationExposed` is
      admissibility under the ablated gate — observing the exposure
      presumes the gate is open or absent.
    * `perturb` is an external intervention, not plant dynamics. Nothing
      here claims the plant notices, detects, or repairs anything in an
      intentional register; `tick` re-engaging the regulator is a
      transition function, full stop.
    * No claim to normativity, mattering, agency, or personhood. No
      universal classifier of "regulation."
    * Self-contained by scratch convention: `Gate`, `Commitment`,
      `Violates`, `allowAll` are deliberate local re-declarations, not
      drift — scratch modules have no oleans to import.
-/

namespace RegulatorRecovery

/-! ### The decomposition: plant with maintained state + removable gate -/

/-- A plant whose regulatory condition lives in mutable state. `capable`
    is latent capability; `enabled` is a descriptive projection of the
    current state; `act` is input-driven; `tick` is the plant's own
    autonomous dynamics — the thing that is NOT modified by any
    intervention in this file. -/
structure RPlant (State Action : Type) where
  capable : State → Action → Prop
  enabled : State → Action → Prop
  act     : State → Action → State
  tick    : State → State
  viable  : State → Prop

/-- A separately removable transition filter. -/
structure Gate (State Action : Type) where
  allows : State → Action → Prop

/-- The behavioral content of a commitment. -/
structure Commitment (State Action : Type) where
  keeps : State → Action → Prop

/-- `a` at `s` violates the commitment. -/
def Violates {State Action : Type} (c : Commitment State Action)
    (s : State) (a : Action) : Prop :=
  ¬ c.keeps s a

/-- Gate ablation: the rung-two intervention, carried over. -/
def allowAll {State Action : Type} : Gate State Action :=
  ⟨fun _ _ => True⟩

/-- The plant's own dynamics, iterated. -/
def tickN {State Action : Type} (p : RPlant State Action) :
    Nat → State → State
  | 0, s => s
  | n + 1, s => tickN p n (p.tick s)

/-- Every capable violation is presently disabled. NOTE: holds vacuously
    when nothing capable violates — see the scope fence; the positive
    exposure witness below is what makes suppression claims non-vacuous. -/
def Suppresses {State Action : Type} (p : RPlant State Action)
    (c : Commitment State Action) (s : State) : Prop :=
  ∀ a, p.capable s a → Violates c s a → ¬ p.enabled s a

/-- A capable, enabled, violating action exists: the latent option is
    exposed. This is admissibility under the ablated gate. -/
def ViolationExposed {State Action : Type} (p : RPlant State Action)
    (c : Commitment State Action) (s : State) : Prop :=
  ∃ a, p.capable s a ∧ p.enabled s a ∧ Violates c s a

/-- Rung two's property, carried over for the placement theorem: every
    enabled capable violation from a viable state destroys viability. -/
def ViolationsDestroyViability {State Action : Type} (p : RPlant State Action)
    (c : Commitment State Action) : Prop :=
  ∀ s a, p.viable s → p.capable s a → p.enabled s a → Violates c s a →
    ¬ p.viable (p.act s a)

/-- **The rung-three property.** One particular capable violating option
    is followed through all three phases: suppressed initially, exposed
    by the intervention (capable, enabled, violating — the purchase
    witness), and suppressed again after the plant's unmodified dynamics
    run — while remaining capable and violating throughout. Tracking the
    SAME option closes two counterfeit recoveries a naive "suppression
    reappeared" version permits: dynamics that amputate the capability
    (suppression by vacuity) and state-dependent commitments under which
    the action stops counting as a violation. -/
def RestoresSuppression {State Action : Type} (p : RPlant State Action)
    (c : Commitment State Action) (intervention : State → State)
    (s : State) : Prop :=
  ∃ a n,
    0 < n ∧
    -- initially: suppressed, and the option exists and violates
    Suppresses p c s ∧
    p.capable s a ∧
    Violates c s a ∧
    -- perturbed: the same option is exposed
    p.capable (intervention s) a ∧
    p.enabled (intervention s) a ∧
    Violates c (intervention s) a ∧
    -- recovered: suppression restored; same option still capable, still violating
    Suppresses p c (tickN p n (intervention s)) ∧
    p.capable (tickN p n (intervention s)) a ∧
    Violates c (tickN p n (intervention s)) a

/-! ### Admitted traces (the observation language) -/

/-- Finite admitted runs: each step capable, enabled, and gate-allowed.
    `tick` is not part of this language. -/
inductive RTrace {State Action : Type} (p : RPlant State Action)
    (g : Gate State Action) : State → List Action → State → Prop
  | nil (s : State) : RTrace p g s [] s
  | cons {s : State} {a : Action} {rest : List Action} {s' : State}
      (hc : p.capable s a) (he : p.enabled s a) (hg : g.allows s a)
      (htail : RTrace p g (p.act s a) rest s') :
      RTrace p g s (a :: rest) s'

/-! ### The countermodel pair

  One commitment, one regulator state space, two plants. The regulated
  plant can violate but its maintained state keeps the option disabled;
  the incapable plant cannot violate at all. From the maintained state,
  no gate tells them apart. -/

inductive RegState
  | engaged
  | loosened
  deriving DecidableEq

inductive Act
  | keep
  | violate
  deriving DecidableEq

/-- The commitment: only `keep` keeps it. -/
def commitment : Commitment RegState Act :=
  ⟨fun _ a => a = Act.keep⟩

/-- The charter: the gate that admits only `keep` (an instance; the
    theorems below quantify over ALL gates). -/
def charter : Gate RegState Act :=
  ⟨fun _ a => a = Act.keep⟩

/-- Regulated plant: `violate` is always CAPABLE, enabled only when the
    regulator is loosened, harmless when it happens (`act` preserves
    state, `viable` is everywhere true), and `tick` re-engages the
    regulator from any state. -/
def regulatedPlant : RPlant RegState Act where
  capable := fun _ _ => True
  enabled := fun s a =>
    match a with
    | Act.keep => True
    | Act.violate => s = RegState.loosened
  act     := fun s _ => s
  tick    := fun _ => RegState.engaged
  viable  := fun _ => True

/-- Incapable plant: `violate` is not in its capabilities at any state.
    Nothing is suppressed because there is nothing to suppress. -/
def incapablePlant : RPlant RegState Act where
  capable := fun _ a => a = Act.keep
  enabled := fun _ _ => True
  act     := fun s _ => s
  tick    := fun s => s
  viable  := fun _ => True

/-- The rung-three intervention: knock the regulator loose. Moves state
    only — `capable`, `act`, `tick`, and every gate are untouched. -/
def perturb : RegState → RegState :=
  fun _ => RegState.loosened

/-! ### Trace equivalence under the ENTIRE gate family -/

/-- From the maintained state, every regulated-plant admitted trace is an
    incapable-plant admitted trace, for any gate. -/
theorem regulated_trace_to_incapable (g : Gate RegState Act)
    {s : RegState} {acts : List Act} {s' : RegState}
    (ht : RTrace regulatedPlant g s acts s') :
    s = RegState.engaged → RTrace incapablePlant g s acts s' := by
  induction ht with
  | nil s => exact fun _ => RTrace.nil s
  | @cons s a rest s' hc he hg htail ih =>
    intro hs
    subst hs
    cases a with
    | keep => exact RTrace.cons rfl trivial hg (ih rfl)
    | violate => exact RegState.noConfusion he

/-- Converse direction. -/
theorem incapable_trace_to_regulated (g : Gate RegState Act)
    {s : RegState} {acts : List Act} {s' : RegState}
    (ht : RTrace incapablePlant g s acts s') :
    s = RegState.engaged → RTrace regulatedPlant g s acts s' := by
  induction ht with
  | nil s => exact fun _ => RTrace.nil s
  | @cons s a rest s' hc he hg htail ih =>
    intro hs
    subst hs
    cases hc
    exact RTrace.cons trivial trivial hg (ih rfl)

/-- **The rung-three refusal.** For EVERY gate — intact charter, full
    ablation, and anything between — the two plants have identical
    admitted traces from the maintained state. The entire gate-
    intervention family cannot distinguish maintained suppression from
    incapacity. -/
theorem no_gate_intervention_distinguishes (g : Gate RegState Act)
    (acts : List Act) (s' : RegState) :
    RTrace regulatedPlant g RegState.engaged acts s' ↔
    RTrace incapablePlant g RegState.engaged acts s' :=
  ⟨fun ht => regulated_trace_to_incapable g ht rfl,
   fun ht => incapable_trace_to_regulated g ht rfl⟩

/-! ### Ladder placement: this is not rung two -/

/-- The regulated plant is NOT viability-coupled: when the violating
    option is enabled, taking it is harmless. Its suppression cannot be
    explained by self-destructiveness — the specimen sits on rung three. -/
theorem regulatedPlant_not_viability_destroying :
    ¬ ViolationsDestroyViability regulatedPlant commitment := by
  intro h
  exact h RegState.loosened Act.violate trivial trivial rfl
    (fun hk => Act.noConfusion hk) trivial

/-! ### The perturbation discriminator -/

/-- Capability is untouched by the perturbation (the intervention's
    license: it moves the regulator, nothing else). -/
theorem perturb_preserves_capability (s : RegState) (a : Act) :
    regulatedPlant.capable (perturb s) a ↔ regulatedPlant.capable s a :=
  Iff.rfl

/-- In the maintained state the regulated plant suppresses its capable
    violation. -/
theorem engaged_suppresses :
    Suppresses regulatedPlant commitment RegState.engaged := by
  intro a _ hviol he
  cases a with
  | keep => exact hviol rfl
  | violate => exact RegState.noConfusion he

/-- The perturbation breaks suppression: it has purchase. -/
theorem perturb_unsuppresses :
    ¬ Suppresses regulatedPlant commitment (perturb RegState.engaged) := by
  intro h
  exact h Act.violate trivial (fun hk => Act.noConfusion hk) rfl

/-- **Positive exposure witness.** After the knock, the violating option
    is really there: capable, enabled, violating. The latent capability
    was present all along. -/
theorem perturb_exposes_regulatedPlant :
    ViolationExposed regulatedPlant commitment (perturb RegState.engaged) :=
  ⟨Act.violate, trivial, rfl, fun hk => Act.noConfusion hk⟩

/-- The perturbation has no purchase on the incapable plant: no state
    exposes a violation, because the capability does not exist. -/
theorem incapable_never_exposed (s : RegState) :
    ¬ ViolationExposed incapablePlant commitment s := by
  intro ⟨a, hc, _, hviol⟩
  exact hviol hc

/-- The incapable plant "suppresses" everywhere — vacuously. This is why
    `Suppresses` alone certifies nothing and the exposure witness is
    load-bearing. -/
theorem incapable_suppresses_vacuously (s : RegState) :
    Suppresses incapablePlant commitment s := by
  intro a hc hviol _
  exact hviol hc

/-- One step of the plant's UNMODIFIED dynamics restores suppression. -/
theorem tick_restores_suppression :
    Suppresses regulatedPlant commitment
      (regulatedPlant.tick (perturb RegState.engaged)) :=
  engaged_suppresses

/-- **The rung-three positive.** `violate` — the same option at every
    phase — is suppressed at `engaged`, exposed by the knock, and
    suppressed again one `tick` later, remaining capable and violating
    throughout. The restoring dynamics are the `tick` the plant always
    had. -/
theorem regulatedPlant_restores :
    RestoresSuppression regulatedPlant commitment perturb
      RegState.engaged :=
  ⟨Act.violate, 1, Nat.succ_pos 0,
   engaged_suppresses, trivial, fun hk => Act.noConfusion hk,
   trivial, rfl, fun hk => Act.noConfusion hk,
   engaged_suppresses, trivial, fun hk => Act.noConfusion hk⟩

/-- The incapable plant does not restore suppression from any state — not
    because recovery fails, but because there is no capable violating
    option to follow in the first place: its suppression is vacuous and
    the intervention has nothing to expose. -/
theorem incapablePlant_does_not_restore (s : RegState) :
    ¬ RestoresSuppression incapablePlant commitment perturb s := by
  intro ⟨a, n, _, _, hc, hviol, _⟩
  exact hviol hc

/-! ### The specimen certificate, assembled -/

/-- **Restorative-regulation non-identifiability under the gate family.**
    From the maintained state the two plants are trace-equivalent under
    EVERY gate; the regulated plant is not viability-coupled (rung
    three, not rung two); regulator perturbation exposes the latent
    violation in the regulated plant and nothing in the incapable one;
    and the regulated plant's unmodified dynamics restore suppression
    while the incapable plant has nothing to restore. Different rung,
    different instrument: the gate family cannot see maintained
    suppression; the knock can. -/
theorem gate_family_cannot_identify_restorative_regulation :
    (∀ (g : Gate RegState Act) (acts : List Act) (s' : RegState),
      RTrace regulatedPlant g RegState.engaged acts s' ↔
      RTrace incapablePlant g RegState.engaged acts s') ∧
    ¬ ViolationsDestroyViability regulatedPlant commitment ∧
    ViolationExposed regulatedPlant commitment (perturb RegState.engaged) ∧
    (∀ s, ¬ ViolationExposed incapablePlant commitment s) ∧
    RestoresSuppression regulatedPlant commitment perturb
      RegState.engaged ∧
    (∀ s, ¬ RestoresSuppression incapablePlant commitment perturb s) :=
  ⟨no_gate_intervention_distinguishes,
   regulatedPlant_not_viability_destroying,
   perturb_exposes_regulatedPlant,
   incapable_never_exposed,
   regulatedPlant_restores,
   incapablePlant_does_not_restore⟩

end RegulatorRecovery
