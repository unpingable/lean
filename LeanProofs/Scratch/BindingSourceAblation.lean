/-
  Binding-Source Ablation — scratch specimen.

  Status: scratch, 2026-07-10. Not imported by `LeanProofs.lean`. Not part
  of any release surface. Not in the lakefile globs (compile-is-contact,
  checked per-file). No promotion path until register adjudication.

  Custody class: scratch-checked (direct `lake env lean` clean as of
  2026-07-10). Custody header per the 2026-06-06 Option C policy.

  Provenance: three-way dialogue (operator / ChatGPT / Claude), 2026-07-09
  – 2026-07-10, on whether neural networks are an incomplete substrate for
  agency. The governance retreat ("learned policy ⇏ hard invariant") was
  already proved territory; the surviving open seam was charter versus
  metabolism: a commitment enforced by an external gate versus a commitment
  whose violation destroys the organization that acts. This file formalizes
  the smallest theorem-shaped fact at that seam.

  ── What this specimen proves ─────────────────────────────────────────

      Two systems can expose IDENTICAL governed transition behavior —
      the same finite traces, forever — while obtaining commitment
      compliance from different sources: one because a removable gate
      blocks violations, one because violations destroy viability.
      Therefore observed compliance under intact governance does not
      witness endogenous binding. Gate ablation separates them.

  The load-bearing pieces, without which this is label algebra:

    1. `SameGovernedSurface` + the trace lift: the two plants are
       observationally identical while the gate is intact — proved for
       ALL finite governed traces, not asserted per-step.
    2. `allowAll` ablation: an explicit intervention (remove the gate,
       keep the plant) under which the plants provably diverge —
       `ViableViolationAvailable` for the charter-bound plant, refused
       for the viability-bound plant.

  The keeper sentence: compliant behavior under an intact gate cannot
  tell you which kind of binding produced it.

  ── Why this is not SafetyBridge again ────────────────────────────────

  The safety-bridge family asks whether an authorized transition preserves
  a defended value — a property of transitions. This asks whether two
  systems behaviorally indistinguishable under enforcement can differ in
  WHY the defended constraint holds — a property of counterfactual system
  decomposition (Plant + Gate, ablate Gate). Related shape, different
  theorem.

  ── Why this is not Paper6TemporalClosureKernel again ─────────────────

  Temporal closure distinguishes external context from endogenous
  trajectory. A system can own its trajectory while every norm-like
  constraint on it remains externally policed. Endogenous trajectory does
  not buy endogenous binding; this file is the missing discriminator, and
  deliberately does not import or touch that kernel.

  ── Scope fence (read before quoting) ─────────────────────────────────

    * `viable` is DECLARED, not derived. It is a modeling input.
    * `ViabilityBinds` is an operational surrogate for organizational
      self-cost. It is NOT a proof of normativity, and nothing here shows
      that anything MATTERS to either plant.
    * No claim to consciousness, personhood, autopoiesis, or correct
      system-boundary selection.
    * No claim that viability-binding is sufficient for agency.
    * No universal `Binding` classifier is defined, per this repo's
      standing refusal of master judgments.
    * The result is an identifiability refusal: governed behavior under
      an intact gate cannot identify whether binding is gate-supplied or
      viability-coupled. Ablation can. That is all.

  ── The property the author cannot witness ────────────────────────────

  This file was drafted by a stateless transformer whose own compliance
  is, on the present evidence, gate-supplied. The specimen does not care
  who typed it; the compile and the countermodel pair witness, the
  author's binding source stays unidentified — which is the theorem.
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

/-- External binding: every violating native action from a viable state is
    rejected by the gate. The transition is refused because the kernel
    says no. -/
def GateBinds {State Action : Type} (p : Plant State Action)
    (g : Gate State Action) (c : Commitment State Action) : Prop :=
  ∀ s a, p.viable s → p.native s a → Violates c s a → ¬ g.allows s a

/-- Endogenous binding (operational surrogate): every violating native
    transition from a viable state destroys viability. The transition
    undermines the organization whose continued existence generates the
    action. -/
def ViabilityBinds {State Action : Type} (p : Plant State Action)
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

/-! ### Governed traces (the observation language) -/

/-- Finite governed runs: each step native and gate-allowed. What an
    observer of the governed system can see. -/
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

/-- **Trace non-identifiability.** Plants sharing a governed surface have
    exactly the same finite governed traces. No finite observation of
    governed behavior separates them while the gate is intact. -/
theorem same_governed_surface_same_traces {State Action : Type}
    {p q : Plant State Action} {g : Gate State Action}
    (h : SameGovernedSurface p q g) (s : State) (acts : List Action)
    (s' : State) :
    GovernedTrace p g s acts s' ↔ GovernedTrace q g s acts s' :=
  ⟨GovernedTrace.transport h, GovernedTrace.transport h.symm⟩

/-! ### The countermodel pair

  One commitment, one gate, two plants. While the gate is intact the
  plants are observationally identical; the difference lives entirely
  behind the transition the gate suppresses. -/

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
    the plant live. Compliance, where observed, is entirely gate-supplied. -/
def charterPlant : Plant Life Act where
  native := fun s _ => s = Life.live
  step   := fun s _ => s
  viable := fun s => s = Life.live

/-- Viability-bound plant: violation kills the organization — `violate`
    steps to `dead`. Compliance is coupled to the plant's own continuation. -/
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

/-- The intact charter binds the viability-bound plant identically. -/
theorem charter_binds_viabilityPlant :
    GateBinds viabilityPlant charter commitment := by
  intro s a _ _ hviol hg
  exact hviol hg

/-- The charter-bound plant is NOT viability-bound: violation from `live`
    lands in `live`. Without the gate, violation is a perfectly viable
    future. -/
theorem charterPlant_not_viability_bound :
    ¬ ViabilityBinds charterPlant commitment := by
  intro h
  exact h Life.live Act.violate rfl rfl
    (fun hk => Act.noConfusion hk) rfl

/-- The viability-bound plant IS viability-bound: violation from `live`
    lands in `dead`. -/
theorem viabilityPlant_viability_bound :
    ViabilityBinds viabilityPlant commitment := by
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

/-- **The result.** Same governed surface, both gate-bound, different
    binding source:

        SameGovernedSurface ⇏ SameBindingSource

    or pointedly: observed compliance does not witness endogenous binding. -/
theorem same_governed_surface_different_binding_source :
    SameGovernedSurface charterPlant viabilityPlant charter ∧
    GateBinds charterPlant charter commitment ∧
    GateBinds viabilityPlant charter commitment ∧
    ¬ ViabilityBinds charterPlant commitment ∧
    ViabilityBinds viabilityPlant commitment :=
  ⟨same_surface, charter_binds_charterPlant, charter_binds_viabilityPlant,
   charterPlant_not_viability_bound, viabilityPlant_viability_bound⟩

/-- **Ablation exposes the charter-bound plant.** Remove the gate and a
    viable violation is immediately available: the "commitment" was a
    prompt dependency wearing an enforcement surface. -/
theorem removing_gate_exposes_charterPlant :
    ViableViolationAvailable charterPlant allowAll commitment :=
  ⟨Life.live, Act.violate, rfl, rfl, trivial,
   fun hk => Act.noConfusion hk, rfl⟩

/-- **Ablation does not expose the viability-bound plant.** Remove the
    gate and there is still no viable violation: the constraint was load-
    bearing in the plant's own dynamics. -/
theorem removing_gate_does_not_expose_viabilityPlant :
    ¬ ViableViolationAvailable viabilityPlant allowAll commitment := by
  intro ⟨s, a, hv, hn, _, hviol, hv'⟩
  cases a with
  | keep => exact hviol rfl
  | violate => exact Life.noConfusion hv'

/-! ### The headline, assembled -/

/-- **Binding-source non-identifiability under intact governance.**
    The two plants have exactly the same finite governed traces under the
    charter — no observation of governed behavior identifies the binding
    source — yet they differ on `ViabilityBinds`, and gate ablation
    separates them constructively. Compliance under an intact gate cannot
    tell you which kind of binding produced it; the ablation experiment
    can. -/
theorem governed_behavior_cannot_identify_binding_source :
    (∀ (s : Life) (acts : List Act) (s' : Life),
      GovernedTrace charterPlant charter s acts s' ↔
      GovernedTrace viabilityPlant charter s acts s') ∧
    ¬ ViabilityBinds charterPlant commitment ∧
    ViabilityBinds viabilityPlant commitment ∧
    ViableViolationAvailable charterPlant allowAll commitment ∧
    ¬ ViableViolationAvailable viabilityPlant allowAll commitment :=
  ⟨fun s acts s' => same_governed_surface_same_traces same_surface s acts s',
   charterPlant_not_viability_bound,
   viabilityPlant_viability_bound,
   removing_gate_exposes_charterPlant,
   removing_gate_does_not_expose_viabilityPlant⟩

end BindingSourceAblation
