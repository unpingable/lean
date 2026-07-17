/-
  ReachableDrift.Basic — is "could authorized ops have produced this world?" a
  genuinely NEW formal object, or admissibility/authority under new nouns?

  TRACK DOCTRINE (full statement in `ReachableDrift.lean`):
    Reachable drift asks whether an observed state lies inside the transition
    closure of the declared authorized machine. It is a DISTINCT object from
    admissibility/authority — distinct because observation is LOSSY (provenance is
    hidden), the `ambiguous` verdict is the non-injectivity of `observe ∘ run`, and
    the diagnosis lives in the GAP between two labeled closures — not merely because
    a labeling change moves a proposition. The labeling-dependence separation is a
    THEOREM (`Diagnosis.drift_depends_on_labeling`), not taste.

  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE
  This terminal evidence is sorry-free but not axiom-free: `propext` occurs
  here and in the rest of the family; `diagnosis_exhaustive` additionally uses
  `Classical.choice` + `Quot.sound`. There are no custom axioms.

  The witnessed-derivation work asks:   may an eligible judgment ACQUIRE effect?
  Reachable-drift asks a different thing: could AUTHORIZED operations have produced
  this OBSERVED world?  The first licenses a judgment; the second quantifies over
  possible transition HISTORIES under lossy observation. This file builds the
  smallest finite world that makes the second question bite, and tests the
  collapse: it does NOT reduce to the admissibility/authority families.

  Design (deliberately ugly-but-concrete, per the playground brief):
    • States: a tiny host — package / config / service / port, plus one OBSERVED
      attribute (`external`) that NO modeled op produces (the model-incompleteness
      handle).
    • Transitions: three DECLARED (authorized deploy path) and two UNDECLARED
      (manual `systemctl start`, manual port open) — each undeclared op is LOUD
      (flips an observed bit) and monotone (bits only go false→true).
    • Observation is LOSSY: you see (service, port, external), never pkg/config —
      so you see the resulting state, never the history that produced it.

  Proof shape: positive cases exhibit traces (`decide`/`rfl`); negative cases are
  genuine inductions over arbitrary `List Op` (monotonicity + the port⇒service
  invariant). No custom axioms — only the standard `propext` / `Classical.choice` /
  `Quot.sound` noted above.
-/

namespace ReachableDrift

/-! ## The finite world -/

/-- A tiny host. `external` is an observed attribute that no modeled op can set —
    its only role is to make some observations *unreachable in this model*, i.e.
    to give the `modelIncomplete` diagnosis a witness. -/
structure World where
  pkg      : Bool
  config   : Bool
  service  : Bool
  port     : Bool
  external : Bool
  deriving DecidableEq, Repr

/-- The clean origin: nothing installed, nothing running. -/
def init : World := ⟨false, false, false, false, false⟩

/-- The operation vocabulary. Three declared (the authorized deploy path) and two
    undeclared (manual interventions that bypass it). -/
inductive Op
  | deployInstall      -- declared: install package + drop config (hidden effects)
  | systemdEnable      -- declared: start service IFF package present
  | openPort           -- declared: open port IFF service running
  | manualServiceStart -- UNDECLARED: start service with NO package guard
  | manualPortOpen     -- UNDECLARED: open port with NO service guard
  deriving DecidableEq, Repr

/-- The authorization labeling: which ops are part of the declared deploy path. -/
def Op.authorized : Op → Bool
  | deployInstall | systemdEnable | openPort => true
  | manualServiceStart | manualPortOpen      => false

/-- The transition semantics. Every op is MONOTONE: it only flips observed bits
    false→true, never back — so once a service/port is up, no op in this
    vocabulary takes it down. -/
def Op.step : Op → World → World
  | deployInstall,      w => { w with pkg := true, config := true }
  | systemdEnable,      w => if w.pkg then { w with service := true } else w
  | openPort,           w => if w.service then { w with port := true } else w
  | manualServiceStart, w => { w with service := true }
  | manualPortOpen,     w => { w with port := true }

/-- Run a trace from a starting world. -/
def run (w : World) : List Op → World
  | []      => w
  | op :: t => run (op.step w) t

/-- A trace is DECLARED iff every op in it is authorized. (`abbrev` so that
    `Declared` of a concrete trace is `Decidable` — the witnesses use `decide`.) -/
abbrev Declared (t : List Op) : Prop := ∀ op ∈ t, op.authorized = true

/-! ## Lossy observation: the resulting state, never the history -/

/-- What the field can see: service up?, port open?, and the external attribute.
    Crucially NOT pkg/config — so the observer cannot read provenance. -/
structure Obs where
  service  : Bool
  port     : Bool
  external : Bool
  deriving DecidableEq, Repr

def observe (w : World) : Obs := ⟨w.service, w.port, w.external⟩

/-- An observation `o` is reachable iff SOME trace from `init` lands on it. This is
    an existential over HISTORIES — the shape that makes drift its own object. -/
def Reachable (o : Obs) : Prop := ∃ t, observe (run init t) = o

/-- Declared-reachable: explained by an authorized-only trace. -/
def DeclaredReachable (o : Obs) : Prop := ∃ t, Declared t ∧ observe (run init t) = o

/-- Has an undeclared explanation: SOME explaining trace used ≥1 unauthorized op.
    When this holds for a declared-reachable observation, the observer cannot tell
    whether an unauthorized intervention occurred — that is the ambiguity. -/
def HasUndeclaredExplanation (o : Obs) : Prop := ∃ t, (¬ Declared t) ∧ observe (run init t) = o

/-! ## The diagnosis — four mutually exclusive, exhaustive verdicts -/

inductive DriftDiagnosis
  | declaredReachable     -- explained by declared ops, and by NOTHING undeclared
  | ambiguous             -- declared-reachable, but an undeclared trace also fits
  | unauthorizedRequired  -- reachable, but NEVER by declared ops alone
  | modelIncomplete       -- not reachable by any trace — the model lacks a transition
  deriving DecidableEq, Repr

/-- The classifier, as a relational spec over the reachability predicates. The four
    cases partition `Obs` (proved in `diagnosis_exhaustive` / `diagnosis_exclusive`). -/
def classifies (o : Obs) : DriftDiagnosis → Prop
  | .declaredReachable    => DeclaredReachable o ∧ ¬ HasUndeclaredExplanation o
  | .ambiguous            => DeclaredReachable o ∧ HasUndeclaredExplanation o
  | .unauthorizedRequired => ¬ DeclaredReachable o ∧ Reachable o
  | .modelIncomplete      => ¬ Reachable o

/-! ## Structural lemmas (the real proofs — inductions over arbitrary traces) -/

/-- A declared trace prepends a declared op. -/
theorem declared_cons {op : Op} {t : List Op}
    (h : Declared (op :: t)) : op.authorized = true ∧ Declared t :=
  List.forall_mem_cons.mp h

/-- `external` is invariant under every op — no modeled transition sets it. -/
theorem step_external (op : Op) (w : World) : (op.step w).external = w.external := by
  cases op <;> simp only [Op.step] <;> (first | rfl | (split <;> rfl))

/-- Hence `external` stays whatever it started as, along any trace. -/
theorem run_external (w : World) (t : List Op) : (run w t).external = w.external := by
  induction t generalizing w with
  | nil => rfl
  | cons op t ih => simp [run, ih, step_external]

/-- Observed bits are MONOTONE under any op: true stays true. -/
theorem step_service_mono {op : Op} {w : World}
    (h : w.service = true) : (op.step w).service = true := by
  cases op <;> simp only [Op.step] <;>
    (first | exact h | rfl | (split <;> (first | rfl | exact h)))

theorem step_port_mono {op : Op} {w : World}
    (h : w.port = true) : (op.step w).port = true := by
  cases op <;> simp only [Op.step] <;>
    (first | exact h | rfl | (split <;> (first | rfl | exact h)))

theorem run_service_stays {w : World} (t : List Op)
    (h : w.service = true) : (run w t).service = true := by
  induction t generalizing w with
  | nil => exact h
  | cons op t ih => exact ih (step_service_mono h)

theorem run_port_stays {w : World} (t : List Op)
    (h : w.port = true) : (run w t).port = true := by
  induction t generalizing w with
  | nil => exact h
  | cons op t ih => exact ih (step_port_mono h)

/-- If `manualServiceStart` appears anywhere in a trace, the final service is up
    (it sets service, and nothing takes it down). -/
theorem manualServiceStart_forces_service {w : World} {t : List Op}
    (h : Op.manualServiceStart ∈ t) : (run w t).service = true := by
  induction t generalizing w with
  | nil => simp at h
  | cons op t ih =>
    rcases List.mem_cons.mp h with rfl | htl
    · exact run_service_stays t (by simp [Op.step])
    · exact ih htl

/-- Likewise `manualPortOpen` forces the final port open. -/
theorem manualPortOpen_forces_port {w : World} {t : List Op}
    (h : Op.manualPortOpen ∈ t) : (run w t).port = true := by
  induction t generalizing w with
  | nil => simp at h
  | cons op t ih =>
    rcases List.mem_cons.mp h with rfl | htl
    · exact run_port_stays t (by simp [Op.step])
    · exact ih htl

/-- The deploy-path INVARIANT: a declared trace preserves `port ⇒ service`
    (the only declared port-opener, `openPort`, fires only when service is up).
    The key separation lemma — undeclared `manualPortOpen` is exactly what breaks
    it. -/
theorem declared_preserves_portImpliesService {t : List Op} (hdec : Declared t) :
    ((run init t).port = true → (run init t).service = true) := by
  suffices H : ∀ (w : List Op) (s : World),
      (s.port = true → s.service = true) → Declared w →
      ((run s w).port = true → (run s w).service = true) from
    H t init (by intro h; simp [init] at h) hdec
  intro w
  induction w with
  | nil => intro s hs _; exact hs
  | cons op t ih =>
    intro s hinv hdec
    obtain ⟨hauth, htl⟩ := declared_cons hdec
    refine ih (op.step s) ?_ htl
    -- one declared step preserves the invariant
    cases op with
    | deployInstall => intro h; exact hinv (by simpa [Op.step] using h)
    | systemdEnable =>
        intro h
        by_cases hp : s.pkg
        · simp [Op.step, hp]
        · simp [Op.step, hp] at h ⊢; exact hinv h
    | openPort =>
        intro h
        by_cases hs : s.service
        · simp [Op.step, hs]
        · simp only [Op.step, if_neg hs] at h ⊢; exact hinv h
    | manualServiceStart => simp [Op.authorized] at hauth
    | manualPortOpen => simp [Op.authorized] at hauth

/-- `¬ Declared t` exhibits a concrete unauthorized op in `t`. -/
theorem exists_unauthorized_of_not_declared {t : List Op}
    (h : ¬ Declared t) : ∃ op ∈ t, op.authorized = false := by
  induction t with
  | nil => exact absurd (fun op hop => by simp at hop) h
  | cons op t ih =>
    by_cases hop : op.authorized = true
    · have htail : ¬ Declared t := fun hd => h (List.forall_mem_cons.mpr ⟨hop, hd⟩)
      obtain ⟨op', hmem, hbad⟩ := ih htail
      exact ⟨op', List.mem_cons.mpr (Or.inr hmem), hbad⟩
    · refine ⟨op, List.mem_cons.mpr (Or.inl rfl), ?_⟩
      cases hb : op.authorized with
      | true => exact absurd hb hop
      | false => rfl

/-! ## The four witnesses — one observation per diagnosis, each proved -/

/-- **declaredReachable (clean).** `⟨service=F, port=F, external=F⟩` is reached by
    the empty trace, and by NO undeclared trace: any undeclared op is one of the
    two LOUD ops, which forces service or port up — contradicting the observation.
    So the observer can *certify* no unauthorized activity here. -/
theorem quiet_admits_only_declared :
    classifies ⟨false, false, false⟩ DriftDiagnosis.declaredReachable := by
  refine ⟨⟨[], by decide, rfl⟩, ?_⟩
  rintro ⟨t, hnd, hobs⟩
  -- ¬ Declared t ⇒ some unauthorized op ∈ t ⇒ it is manualServiceStart or manualPortOpen
  obtain ⟨op, hop, hauth⟩ := exists_unauthorized_of_not_declared hnd
  have hobs_s : (run init t).service = false := by
    have := congrArg Obs.service hobs; simpa [observe] using this
  have hobs_p : (run init t).port = false := by
    have := congrArg Obs.port hobs; simpa [observe] using this
  cases op with
  | deployInstall => simp [Op.authorized] at hauth
  | systemdEnable => simp [Op.authorized] at hauth
  | openPort => simp [Op.authorized] at hauth
  | manualServiceStart =>
      rw [manualServiceStart_forces_service hop] at hobs_s; exact Bool.noConfusion hobs_s
  | manualPortOpen =>
      rw [manualPortOpen_forces_port hop] at hobs_p; exact Bool.noConfusion hobs_p

/-- **ambiguous.** `⟨service=T, port=F, external=F⟩` — service up, port closed — is
    explained BOTH by the declared deploy path `[deployInstall, systemdEnable]` AND
    by the single undeclared `[manualServiceStart]`. The observer literally cannot
    tell an authorized deploy from a manual `systemctl start`. -/
theorem running_service_is_ambiguous :
    classifies ⟨true, false, false⟩ DriftDiagnosis.ambiguous := by
  refine ⟨⟨[Op.deployInstall, Op.systemdEnable], by decide, by decide⟩,
         ⟨[Op.manualServiceStart], by decide, by decide⟩⟩

/-- **unauthorizedRequired.** `⟨service=F, port=T, external=F⟩` — port open while the
    service is DOWN — is reachable (`[manualPortOpen]`) but provably NOT
    declared-reachable: every declared trace preserves `port ⇒ service`, which this
    observation violates. An unauthorized op is *required* to explain it. -/
theorem open_port_over_down_service_requires_unauthorized :
    classifies ⟨false, true, false⟩ DriftDiagnosis.unauthorizedRequired := by
  refine ⟨?_, ⟨[Op.manualPortOpen], by decide⟩⟩
  rintro ⟨t, hdec, hobs⟩
  have hp : (run init t).port = true := by
    have := congrArg Obs.port hobs; simpa [observe] using this
  have hs : (run init t).service = true := declared_preserves_portImpliesService hdec hp
  have := congrArg Obs.service hobs
  simp [observe, hs] at this

/-- **modelIncomplete.** `⟨service=F, port=F, external=T⟩` is unreachable by ANY
    trace: `external` is invariant under every op and starts false. The right read
    is not "impossible" but "our transition vocabulary cannot produce this — the
    model is missing a transition," i.e. extend the model, do not trust the world. -/
theorem unmodeled_attribute_is_model_incomplete :
    classifies ⟨false, false, true⟩ DriftDiagnosis.modelIncomplete := by
  rintro ⟨t, hobs⟩
  have := congrArg Obs.external hobs
  simp [observe, run_external, init] at this

/-! ## The classifier is total and well-defined (exhaustive + exclusive) -/

/-- DeclaredReachable and HasUndeclaredExplanation each imply Reachable. -/
theorem declaredReachable_reachable {o} (h : DeclaredReachable o) : Reachable o :=
  let ⟨t, _, he⟩ := h; ⟨t, he⟩

theorem hasUndeclared_reachable {o} (h : HasUndeclaredExplanation o) : Reachable o :=
  let ⟨t, _, he⟩ := h; ⟨t, he⟩

/-- **Exhaustive** — every observation gets at least one diagnosis. -/
theorem diagnosis_exhaustive (o : Obs) : ∃ d, classifies o d := by
  by_cases hr : Reachable o
  · by_cases hd : DeclaredReachable o
    · by_cases hu : HasUndeclaredExplanation o
      · exact ⟨.ambiguous, hd, hu⟩
      · exact ⟨.declaredReachable, hd, hu⟩
    · exact ⟨.unauthorizedRequired, hd, hr⟩
  · exact ⟨.modelIncomplete, hr⟩

/-- **Exclusive** — no observation gets two different diagnoses. -/
theorem diagnosis_exclusive {o : Obs} {d₁ d₂ : DriftDiagnosis}
    (h₁ : classifies o d₁) (h₂ : classifies o d₂) : d₁ = d₂ := by
  cases d₁ <;> cases d₂ <;> simp only [classifies] at h₁ h₂ <;>
    first
      | rfl
      | exact (h₁.2 h₂.2).elim
      | exact (h₂.2 h₁.2).elim
      | exact (h₂.1 h₁.1).elim
      | exact (h₁.1 h₂.1).elim
      | exact (h₂ (declaredReachable_reachable h₁.1)).elim
      | exact (h₁ (declaredReachable_reachable h₂.1)).elim
      | exact (h₂ h₁.2).elim
      | exact (h₁ h₂.2).elim

end ReachableDrift
