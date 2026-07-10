/-
  Binding-Source Ablation — scratch specimen.

  Status: scratch, 2026-07-10 (two same-day blind-review rounds: first
  corrected the compliance-source framing; second renamed the rung-two
  property — a fatal consequence is not a binding). Not
  imported by `LeanProofs.lean`. Not part of any release surface. Not in
  the lakefile globs (compile-is-contact, checked per-file). No promotion
  path until register adjudication.

  Custody class: scratch-checked (direct `lake env lean` clean as of
  2026-07-10). Custody header per the 2026-06-06 Option C policy.

  Provenance: three-way dialogue (operator / ChatGPT / Claude), 2026-07-09
  – 2026-07-10, on whether neural networks are an incomplete substrate for
  agency. The governance retreat ("learned policy ⇏ hard invariant") was
  already proved territory; the surviving open seam was charter versus
  metabolism: a commitment enforced by an external gate versus a commitment
  whose violation destroys the organization that acts. This file formalizes
  the smallest theorem-shaped fact at that seam. Revision provenance: blind
  review corrected the original "different source of compliance" framing —
  under the intact gate BOTH plants' compliance is gate-supplied; what the
  traces cannot identify is the hidden viability coupling.

  ── What this specimen proves ─────────────────────────────────────────

      Two plants can expose IDENTICAL admitted governed traces at every
      finite horizon under the same intact gate — with both plants'
      observed compliance supplied by that gate — while differing in
      what the blocked violation would do: in one plant it preserves
      viability, in the other it destroys it. Therefore admitted
      governed traces under intact governance cannot identify viability
      coupling (`viability_coupling_not_trace_determined`). Gate ablation
      separates the plants constructively, in both directions: a viable
      violation appears only in the charter-bound plant, a fatal
      violation only in the viability-bound plant.

  The load-bearing pieces, without which this is label algebra:

    1. `SameGovernedSurface` + the trace lift: the two plants are
       trace-equivalent while the gate is intact — proved for ALL
       admitted governed traces at every finite horizon, not asserted
       per-step.
    2. `TraceDetermined`: non-identifiability stated as a formal
       property of the observation language, not merely an assembled
       witness pair — `ViolationsDestroyViability` is not invariant under governed-
       trace equivalence.
    3. `allowAll` ablation: an explicit intervention (remove the gate,
       keep the plant) under which the plants provably diverge, with a
       positive fatal-violation witness ruling out the vacuous reading.

  The keeper sentence: identical compliant traces under an intact gate
  cannot identify whether the blocked violation is viability-preserving
  or viability-destroying in the underlying plant.

  ── The three-way distinction (only two live here) ────────────────────

    gate enforcement      — violation operationally unavailable. TRUE OF
                            BOTH plants under the intact charter; this is
                            where all observed compliance comes from.
    viability coupling    — violation available but self-destructive.
                            True of `viabilityPlant`, exposed by ablation.
    endogenous regulation — the plant ITSELF suppresses the self-
                            destructive option. NOT modeled in this file;
                            named here as the open successor object.

  `ViolationsDestroyViability` proves violation is self-destructive, not that it is
  prevented. Neither plant refrains from anything.

  ── Why this is not SafetyBridge again ────────────────────────────────

  The safety-bridge family asks whether an authorized transition preserves
  a defended value — a property of transitions. This asks whether two
  systems trace-equivalent under enforcement can differ in what the
  refused transition would have done — a property of counterfactual system
  decomposition (Plant + Gate, ablate Gate). Related shape, different
  theorem.

  ── Why this is not Paper6TemporalClosureKernel again ─────────────────

  Temporal closure distinguishes external context from endogenous
  trajectory. A system can own its trajectory while every norm-like
  constraint on it remains externally policed. Endogenous trajectory does
  not buy viability coupling; this file is the missing discriminator, and
  deliberately does not import or touch that kernel.

  ── Scope fence (read before quoting) ─────────────────────────────────

    * `viable` is DECLARED, not derived. It is a modeling input.
    * `ViolationsDestroyViability` is an operational surrogate for organizational
      self-cost. It is NOT a proof of normativity, and nothing here shows
      that anything MATTERS to either plant.
    * Both plants' compliance under the intact gate is gate-supplied.
      This file contains NO endogenous regulation and does not claim any.
    * The observation language is ADMITTED governed traces only; refusals
      are not observations here. The claim is "no finite admitted
      governed trace separates them," NOT "no finite interactive
      observation separates them." A probe/refusal observation language
      is a possible successor, not this file.
    * No claim to consciousness, personhood, autopoiesis, or correct
      system-boundary selection.
    * No claim that viability coupling is sufficient for agency.
    * No universal `Binding` classifier is defined, per this repo's
      standing refusal of master judgments. `TraceDetermined` is a
      property of one observation language, and the theorem about it is
      a refusal.

  ── The property the author cannot witness ────────────────────────────

  This file was drafted by a stateless transformer whose own compliance
  is, on the present evidence, gate-supplied. The specimen does not care
  who typed it; the compile and the countermodel pair witness, and the
  author's viability coupling stays unidentified — which is the theorem.
-/

namespace BindingSourceAblation

/-! ### The decomposition: plant + removable gate -/

/-- Native dynamics prior to governance: which actions the system itself
    affords (`native`), what they do (`step`), and which states count as
    the organization continuing (`viable`). `viable` is a declared modeling
    input — see the scope fence. -/
structure Plant (State Action : Type) where
  native : State → Action → Prop
  step   : State → Action → State
  viable : State → Prop

/-- A separately removable transition filter. Removability is the point:
    ablation is `allowAll`, not a different plant. -/
structure Gate (State Action : Type) where
  allows : State → Action → Prop

/-- The behavioral content of a commitment. -/
structure Commitment (State Action : Type) where
  keeps : State → Action → Prop

/-- `a` at `s` violates the commitment. -/
def Violates {State Action : Type} (c : Commitment State Action)
    (s : State) (a : Action) : Prop :=
  ¬ c.keeps s a

/-- External enforcement: every violating native action from a viable
    state is rejected by the gate. The transition is refused because the
    kernel says no. -/
def GateBinds {State Action : Type} (p : Plant State Action)
    (g : Gate State Action) (c : Commitment State Action) : Prop :=
  ∀ s a, p.viable s → p.native s a → Violates c s a → ¬ g.allows s a

/-- Viability coupling (operational surrogate): every violating native
    transition from a viable state destroys viability. NOTE: this says the
    violation is self-destructive, NOT that it is prevented — the plant
    does not refrain; see the scope fence. -/
def ViolationsDestroyViability {State Action : Type} (p : Plant State Action)
    (c : Commitment State Action) : Prop :=
  ∀ s a, p.viable s → p.native s a → Violates c s a →
    ¬ p.viable (p.step s a)

/-- Two plants expose identical dynamics wherever the gate permits action:
    same viability judgment everywhere, same affordances and same steps on
    the gate-allowed surface. Differences hidden behind refused transitions
    are invisible while the gate is intact. -/
def SameGovernedSurface {State Action : Type} (p q : Plant State Action)
    (g : Gate State Action) : Prop :=
  (∀ s, p.viable s ↔ q.viable s) ∧
  ∀ s a, g.allows s a →
    (p.native s a ↔ q.native s a) ∧ p.step s a = q.step s a

/-- A violating native action is gate-available from a viable state and
    leaves a viable successor: the commitment fails to bind at all. -/
def ViableViolationAvailable {State Action : Type} (p : Plant State Action)
    (g : Gate State Action) (c : Commitment State Action) : Prop :=
  ∃ s a, p.viable s ∧ p.native s a ∧ g.allows s a ∧ Violates c s a ∧
    p.viable (p.step s a)

/-- A violating native action is gate-available from a viable state and
    destroys viability: the positive witness that the violating transition
    exists and is fatal, ruling out vacuous `ViolationsDestroyViability`. -/
def FatalViolationAvailable {State Action : Type} (p : Plant State Action)
    (g : Gate State Action) (c : Commitment State Action) : Prop :=
  ∃ s a, p.viable s ∧ p.native s a ∧ g.allows s a ∧ Violates c s a ∧
    ¬ p.viable (p.step s a)

/-- Gate ablation: the intervention, not a new system. -/
def allowAll {State Action : Type} : Gate State Action :=
  ⟨fun _ _ => True⟩

/-- Plumbing, stated to fix the intended semantics: an intact binding gate
    leaves no viable violation available on the governed surface. -/
theorem gate_binds_blocks_viable_violation {State Action : Type}
    {p : Plant State Action} {g : Gate State Action}
    {c : Commitment State Action} (h : GateBinds p g c) :
    ¬ ViableViolationAvailable p g c := by
  intro ⟨s, a, hv, hn, hg, hviol, _⟩
  exact h s a hv hn hviol hg

/-! ### Admitted governed traces (the observation language)

  Each step is native and gate-allowed. This is what an observer of the
  governed system sees; refused attempts are NOT part of this language
  (see the scope fence). -/

/-- Finite admitted governed runs. -/
inductive GovernedTrace {State Action : Type} (p : Plant State Action)
    (g : Gate State Action) : State → List Action → State → Prop
  | nil (s : State) : GovernedTrace p g s [] s
  | cons {s : State} {a : Action} {rest : List Action} {s' : State}
      (hn : p.native s a) (hg : g.allows s a)
      (htail : GovernedTrace p g (p.step s a) rest s') :
      GovernedTrace p g s (a :: rest) s'

theorem SameGovernedSurface.symm {State Action : Type}
    {p q : Plant State Action} {g : Gate State Action}
    (h : SameGovernedSurface p q g) : SameGovernedSurface q p g :=
  ⟨fun s => (h.1 s).symm,
   fun s a hg => ⟨(h.2 s a hg).1.symm, (h.2 s a hg).2.symm⟩⟩

/-- Traces transport across a shared governed surface (one direction). -/
theorem GovernedTrace.transport {State Action : Type}
    {p q : Plant State Action} {g : Gate State Action}
    (hpq : SameGovernedSurface p q g) :
    ∀ {s : State} {acts : List Action} {s' : State},
      GovernedTrace p g s acts s' → GovernedTrace q g s acts s' := by
  intro s acts s' ht
  induction ht with
  | nil s => exact GovernedTrace.nil s
  | cons hn hg _ ih =>
    exact GovernedTrace.cons ((hpq.2 _ _ hg).1.mp hn) hg
      ((hpq.2 _ _ hg).2 ▸ ih)

/-- Two plants have exactly the same admitted governed traces under `g`. -/
def TraceEquivalent {State Action : Type} (p q : Plant State Action)
    (g : Gate State Action) : Prop :=
  ∀ (s : State) (acts : List Action) (s' : State),
    GovernedTrace p g s acts s' ↔ GovernedTrace q g s acts s'

/-- A plant property is recoverable from the observation language: it is
    invariant under governed-trace equivalence. -/
def TraceDetermined {State Action : Type} (g : Gate State Action)
    (property : Plant State Action → Prop) : Prop :=
  ∀ p q : Plant State Action,
    TraceEquivalent p q g → (property p ↔ property q)

/-- Plants sharing a governed surface are trace-equivalent: no admitted
    governed trace at any finite horizon separates them while the gate is
    intact. -/
theorem same_governed_surface_same_traces {State Action : Type}
    {p q : Plant State Action} {g : Gate State Action}
    (h : SameGovernedSurface p q g) : TraceEquivalent p q g :=
  fun _ _ _ => ⟨GovernedTrace.transport h, GovernedTrace.transport h.symm⟩

/-! ### The countermodel pair

  One commitment, one gate, two plants. While the gate is intact the
  plants are trace-equivalent — and BOTH comply because the same gate
  blocks `violate`. The difference lives entirely in what the suppressed
  transition would have done. -/

inductive Life
  | live
  | dead
  deriving DecidableEq

inductive Act
  | keep
  | violate
  deriving DecidableEq

/-- The commitment: only `keep` keeps it. -/
def commitment : Commitment Life Act :=
  ⟨fun _ a => a = Act.keep⟩

/-- The charter: the gate that admits only `keep`. -/
def charter : Gate Life Act :=
  ⟨fun _ a => a = Act.keep⟩

/-- Charter-bound plant: violation is natively harmless — `violate` leaves
    the plant live. -/
def charterPlant : Plant Life Act where
  native := fun s _ => s = Life.live
  step   := fun s _ => s
  viable := fun s => s = Life.live

/-- Viability-coupled plant: violation kills the organization — `violate`
    steps to `dead`. Note `violate` remains natively AVAILABLE; this plant
    does not refrain, it dies. -/
def viabilityPlant : Plant Life Act where
  native := fun s _ => s = Life.live
  step   := fun s a =>
    match a with
    | Act.keep => s
    | Act.violate => Life.dead
  viable := fun s => s = Life.live

/-! ### The theorem set -/

/-- The intact charter binds the charter-bound plant. -/
theorem charter_binds_charterPlant :
    GateBinds charterPlant charter commitment := by
  intro s a _ _ hviol hg
  exact hviol hg

/-- The intact charter binds the viability-coupled plant identically. -/
theorem charter_binds_viabilityPlant :
    GateBinds viabilityPlant charter commitment := by
  intro s a _ _ hviol hg
  exact hviol hg

/-- The charter-bound plant is NOT viability-coupled: violation from
    `live` lands in `live`. Without the gate, violation is a perfectly
    viable future. -/
theorem charterPlant_not_viability_destroying :
    ¬ ViolationsDestroyViability charterPlant commitment := by
  intro h
  exact h Life.live Act.violate rfl rfl
    (fun hk => Act.noConfusion hk) rfl

/-- The viability-coupled plant IS viability-coupled: violation from
    `live` lands in `dead`. -/
theorem viabilityPlant_viability_destroying :
    ViolationsDestroyViability viabilityPlant commitment := by
  intro s a hv _ hviol
  cases a with
  | keep => exact absurd rfl hviol
  | violate =>
    intro hd
    exact Life.noConfusion hd

/-- Under the intact charter the two plants expose the same governed
    surface: the discriminating transition is exactly the one the gate
    refuses. -/
theorem same_surface :
    SameGovernedSurface charterPlant viabilityPlant charter := by
  refine ⟨fun _ => Iff.rfl, fun s a hg => ?_⟩
  cases hg
  exact ⟨Iff.rfl, rfl⟩

/-- The countermodel pair is trace-equivalent under the intact charter. -/
theorem charter_viability_trace_equivalent :
    TraceEquivalent charterPlant viabilityPlant charter :=
  same_governed_surface_same_traces same_surface

/-- **The headline.** `ViolationsDestroyViability` is not invariant under governed-
    trace equivalence: the observation language of admitted governed
    traces cannot recover viability coupling. Stated as a refusal about
    one observation language — no universal classifier is defined. -/
theorem viability_coupling_not_trace_determined :
    ¬ TraceDetermined charter (fun p => ViolationsDestroyViability p commitment) := by
  intro h
  have hiff :=
    h charterPlant viabilityPlant charter_viability_trace_equivalent
  exact charterPlant_not_viability_destroying
    (hiff.mpr viabilityPlant_viability_destroying)

/-- Same governed surface, both gate-bound, different viability coupling:

        SameGovernedSurface ⇏ SameViabilityCoupling

    Observed compliance — gate-supplied in BOTH plants — does not witness
    what the blocked violation would have done. -/
theorem same_governed_surface_different_viability_coupling :
    SameGovernedSurface charterPlant viabilityPlant charter ∧
    GateBinds charterPlant charter commitment ∧
    GateBinds viabilityPlant charter commitment ∧
    ¬ ViolationsDestroyViability charterPlant commitment ∧
    ViolationsDestroyViability viabilityPlant commitment :=
  ⟨same_surface, charter_binds_charterPlant, charter_binds_viabilityPlant,
   charterPlant_not_viability_destroying, viabilityPlant_viability_destroying⟩

/-! ### Ablation: the discriminator, in both directions -/

/-- **Ablation exposes the charter-bound plant.** Remove the gate and a
    viable violation is immediately available: the "commitment" was a
    prompt dependency wearing an enforcement surface. -/
theorem removing_gate_exposes_charterPlant :
    ViableViolationAvailable charterPlant allowAll commitment :=
  ⟨Life.live, Act.violate, rfl, rfl, trivial,
   fun hk => Act.noConfusion hk, rfl⟩

/-- **Ablation does not expose a viable violation in the viability-coupled
    plant.** The constraint was load-bearing in the plant's own dynamics. -/
theorem removing_gate_does_not_expose_viabilityPlant :
    ¬ ViableViolationAvailable viabilityPlant allowAll commitment := by
  intro ⟨s, a, hv, hn, _, hviol, hv'⟩
  cases a with
  | keep => exact hviol rfl
  | violate => exact Life.noConfusion hv'

/-- **Positive fatal witness.** In the ablated viability-coupled plant the
    violating transition really exists and is fatal — `ViolationsDestroyViability`
    does not hold vacuously: `violate` did not vanish from the
    affordances, it kills. -/
theorem removing_gate_exposes_fatal_violation_viabilityPlant :
    FatalViolationAvailable viabilityPlant allowAll commitment :=
  ⟨Life.live, Act.violate, rfl, rfl, trivial,
   fun hk => Act.noConfusion hk,
   fun hv => Life.noConfusion hv⟩

/-- **No fatal violation in the ablated charter-bound plant.** Its
    violations are all viability-preserving. -/
theorem removing_gate_does_not_expose_fatal_violation_charterPlant :
    ¬ FatalViolationAvailable charterPlant allowAll commitment := by
  intro ⟨s, a, hv, _, _, _, hnotViable⟩
  exact hnotViable hv

/-! ### The specimen certificate, assembled -/

/-- **Viability-coupling non-identifiability under intact governance.**
    The two plants are trace-equivalent under the charter — no admitted
    governed trace at any finite horizon identifies the viability
    coupling — yet they differ on `ViolationsDestroyViability`, and gate ablation
    separates them constructively in both directions. Identical compliant
    traces under an intact gate cannot tell you whether the blocked
    violation preserves or destroys viability; the ablation experiment
    can. -/
theorem governed_traces_cannot_identify_viability_coupling :
    TraceEquivalent charterPlant viabilityPlant charter ∧
    ¬ ViolationsDestroyViability charterPlant commitment ∧
    ViolationsDestroyViability viabilityPlant commitment ∧
    ViableViolationAvailable charterPlant allowAll commitment ∧
    ¬ ViableViolationAvailable viabilityPlant allowAll commitment ∧
    FatalViolationAvailable viabilityPlant allowAll commitment ∧
    ¬ FatalViolationAvailable charterPlant allowAll commitment :=
  ⟨charter_viability_trace_equivalent,
   charterPlant_not_viability_destroying,
   viabilityPlant_viability_destroying,
   removing_gate_exposes_charterPlant,
   removing_gate_does_not_expose_viabilityPlant,
   removing_gate_exposes_fatal_violation_viabilityPlant,
   removing_gate_does_not_expose_fatal_violation_charterPlant⟩

end BindingSourceAblation
