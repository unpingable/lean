/-
  ReachableDrift.Diagnosis — the computable classifier, its faithfulness proof, and
  the separation theorem.

  Custody-Class: SCRATCH. GREEN surface (sorry-free). NOT axiom-free: `propext`
  throughout; `Classical.choice` + `Quot.sound` reach this module via
  `Basic.diagnosis_exhaustive`. No custom axioms. Not imported by `LeanProofs.lean`.

  Two layers, kept together on purpose:

    SEMANTIC (in `Basic`):  declaredReachable / ambiguous / unauthorizedRequired /
      modelIncomplete, defined over `∃`-quantified transition histories.
    COMPUTABLE (here):  `diagnose : Obs → DriftDiagnosis`, total and decidable,
      PROVEN faithful to the semantic cases (`classifies_diagnose`,
      `diagnose_eq_iff`). The classifier is not heuristic; it is the finite model's
      semantic verdict, computed.

  And the SEPARATION THEOREM: same observed claim + same world / run / observation +
  different transition labeling ⇒ different diagnosis. So drift is not a function of
  the observed claim alone, hence not an admissibility/authority judgment.
-/

import LeanProofs.Scratch.ReachableDrift.Basic

namespace ReachableDrift

/-! ## The three characterizations — reachability collapses to decidable conditions

    In this finite model the otherwise-undecidable `∃ t : List Op` predicates are
    equivalent to decidable conditions on the observation. -/

/-- Reachable ⟺ the observation does not assert the unmodeled attribute. -/
theorem reachable_iff (o : Obs) : Reachable o ↔ o.external = false := by
  constructor
  · rintro ⟨t, hobs⟩
    have := congrArg Obs.external hobs
    simp only [observe, run_external, init] at this
    exact this.symm
  · intro hext
    obtain ⟨s, p, e⟩ := o
    simp only at hext; subst hext
    cases s <;> cases p
    · exact ⟨[], by decide⟩
    · exact ⟨[Op.manualPortOpen], by decide⟩
    · exact ⟨[Op.manualServiceStart], by decide⟩
    · exact ⟨[Op.manualServiceStart, Op.manualPortOpen], by decide⟩

/-- DeclaredReachable ⟺ reachable AND the deploy-path invariant `port ⇒ service`. -/
theorem declaredReachable_iff (o : Obs) :
    DeclaredReachable o ↔ o.external = false ∧ (o.port = true → o.service = true) := by
  constructor
  · rintro ⟨t, hdec, hobs⟩
    refine ⟨?_, ?_⟩
    · have := congrArg Obs.external hobs
      simp only [observe, run_external, init] at this; exact this.symm
    · intro hp
      have hp' : (run init t).port = true := by
        have := congrArg Obs.port hobs; simp only [observe] at this; rw [this]; exact hp
      have hs' := declared_preserves_portImpliesService hdec hp'
      have := congrArg Obs.service hobs; simp only [observe] at this
      rw [← this]; exact hs'
  · rintro ⟨hext, himp⟩
    obtain ⟨s, p, e⟩ := o
    simp only at hext; subst hext
    cases s <;> cases p
    · exact ⟨[], by decide, by decide⟩
    · exact absurd (himp (by decide)) (by decide)
    · exact ⟨[Op.deployInstall, Op.systemdEnable], by decide, by decide⟩
    · exact ⟨[Op.deployInstall, Op.systemdEnable, Op.openPort], by decide, by decide⟩

/-- HasUndeclaredExplanation ⟺ reachable AND at least one observed bit is up (the
    all-quiet observation is the only reachable one with NO undeclared explanation,
    since every undeclared op is loud). -/
theorem hasUndeclared_iff (o : Obs) :
    HasUndeclaredExplanation o ↔ o.external = false ∧ (o.service = true ∨ o.port = true) := by
  constructor
  · rintro ⟨t, hnd, hobs⟩
    refine ⟨?_, ?_⟩
    · have := congrArg Obs.external hobs
      simp only [observe, run_external, init] at this; exact this.symm
    · obtain ⟨op, hop, hauth⟩ := exists_unauthorized_of_not_declared hnd
      cases op with
      | deployInstall => simp [Op.authorized] at hauth
      | systemdEnable => simp [Op.authorized] at hauth
      | openPort => simp [Op.authorized] at hauth
      | manualServiceStart =>
          left
          have hs := manualServiceStart_forces_service (w := init) hop
          have := congrArg Obs.service hobs; simp only [observe] at this
          rw [← this]; exact hs
      | manualPortOpen =>
          right
          have hp := manualPortOpen_forces_port (w := init) hop
          have := congrArg Obs.port hobs; simp only [observe] at this
          rw [← this]; exact hp
  · rintro ⟨hext, hsp⟩
    obtain ⟨s, p, e⟩ := o
    simp only at hext; subst hext
    cases s <;> cases p
    · exact absurd hsp (by decide)
    · exact ⟨[Op.manualPortOpen], by decide, by decide⟩
    · exact ⟨[Op.manualServiceStart], by decide, by decide⟩
    · exact ⟨[Op.manualServiceStart, Op.manualPortOpen], by decide, by decide⟩

/-! ## The total computable classifier -/

/-- `diagnose` — a TOTAL decidable function, no `∃` left. -/
def diagnose (o : Obs) : DriftDiagnosis :=
  if o.external = true then .modelIncomplete
  else if o.port = true ∧ o.service = false then .unauthorizedRequired
  else if o.service = true ∨ o.port = true then .ambiguous
  else .declaredReachable

/-- **classifies_diagnose** — the computable classifier agrees with the semantic
    spec from `Basic`. So `diagnose` is a faithful total decision procedure, not a
    heuristic. -/
theorem classifies_diagnose (o : Obs) : classifies o (diagnose o) := by
  have hR := reachable_iff o
  have hD := declaredReachable_iff o
  have hU := hasUndeclared_iff o
  obtain ⟨s, p, e⟩ := o
  cases e <;> cases p <;> cases s <;>
    simp_all [diagnose, classifies]

/-- The diagnosis is unique-and-computable: `diagnose o` is THE diagnosis. -/
theorem diagnose_eq_iff (o : Obs) (d : DriftDiagnosis) :
    classifies o d ↔ d = diagnose o :=
  ⟨fun h => diagnosis_exclusive h (classifies_diagnose o),
   fun h => h ▸ classifies_diagnose o⟩

/-! ## The separation theorem — drift is NOT a function of the observed claim

    The money result. Admissibility/authority license a judgment over a claim;
    reachable-drift quantifies over LABELED histories. Keep the world, `run`,
    `observe`, and the observed claim byte-identical, change only which transitions
    are blessed, and the diagnosis flips. So no predicate on the observed state
    alone can recover it. -/

/-- Declared-reachability under an ARBITRARY authorization labeling. With
    `auth := Op.authorized` this is exactly `DeclaredReachable`. -/
def DeclaredReachableBy (auth : Op → Bool) (o : Obs) : Prop :=
  ∃ t, (∀ op ∈ t, auth op = true) ∧ observe (run init t) = o

/-- A second labeling that blesses the manual port-open as "declared." Everything
    else — states, semantics, observation — is unchanged. -/
def authLax : Op → Bool
  | Op.manualPortOpen => true
  | op                => op.authorized

/-- **drift_depends_on_labeling** — `⟨service=F, port=T⟩` is `unauthorizedRequired`
    under the strict labeling yet `declaredReachable` under the lax one. Same World,
    same `run`, same `observe`, same observed claim: ONLY the per-transition
    authorization label changed. -/
theorem drift_depends_on_labeling :
    ¬ DeclaredReachableBy Op.authorized ⟨false, true, false⟩
    ∧ DeclaredReachableBy authLax ⟨false, true, false⟩ := by
  refine ⟨?_, ⟨[Op.manualPortOpen], by decide, by decide⟩⟩
  rintro ⟨t, hdec, hobs⟩
  have hp : (run init t).port = true := by
    have := congrArg Obs.port hobs; simpa [observe] using this
  have hs : (run init t).service = true := declared_preserves_portImpliesService hdec hp
  have := congrArg Obs.service hobs
  simp [observe, hs] at this

/-- **labeling_changes_diagnosis** — the separation, stated as the obstruction: the
    declared-reachability verdict of a FIXED observation differs between the two
    labelings. So no function of the observed claim alone (an admissibility/authority
    verdict) can recover it — the discriminating data lives in the transition
    labeling, not the claim. -/
theorem labeling_changes_diagnosis :
    DeclaredReachableBy Op.authorized ⟨false, true, false⟩
      ≠ DeclaredReachableBy authLax ⟨false, true, false⟩ := by
  intro heq
  exact drift_depends_on_labeling.1 (cast heq.symm drift_depends_on_labeling.2)

end ReachableDrift
