/-
  Custody-Class: SCRATCH — compile-is-contact only. Toe tag, not a receipt.

  NOT imported by any aggregator (LeanProofs.lean / Witnessed.lean). NOT in any receipt
  or footprint gate. NOT part of the WDC 2.0 or TaxonomyGraph static-closure custody
  surface. No axiom, no sorry, no `native_decide` (the repo audits scan Scratch source —
  this file stays clean so the full battery stays green).

  Purpose: the dynamic Δh arc, captured at scratch tier. The CONDITIONAL attractor, NOT the
  universal slogan:
    uncorrected, actively-committing detachment under positive rollback burn enters the
    hysteretic state in finite commit time, and is then internally absorbing.

  Non-goals (the fence): no `∀ d ≠ Δh, d ⇝ Δh`; no inference from static graph reachability;
  no rescue edges; no temporal attraction without the dynamics substrate; nothing marked
  SOUND here. Roadmap + guardrails + the stronger (not-yet-built) trace version:
    experiments/persistence_attractor/NOTES.md

  This file only PACKAGES existing PersistenceModel results
  (`commitsToHysteretic_realizes`, `hysteretic_absorbing_internal`) into candidate
  dynamic-Δh statements plus the `HandoffToPersistence` witness. The handoff witness is the
  whole discipline: a `Domain` enters Δh only when SUPPLIED one, never by graph existence.

  Check: cd ~/git/lean && lake env lean LeanProofs/Scratch/PersistenceAttractor.lean
-/

import LeanProofs.PersistenceModel
import LeanProofs.TaxonomyGraph

namespace LeanProofs.Scratch.PersistenceAttractor

/-- A trace of internal-only events (no external repair). -/
def AllInternal (es : List PEvent) : Prop := ∀ e ∈ es, e.isInternal = true

/-- Finite entry: there is some number of commits after which the system is hysteretic. -/
def EventuallyHysteretic (cfg : PConfig) (sys : PSys) : Prop :=
  ∃ n, (run cfg sys (List.replicate n PEvent.commit)).state = .hysteretic

/-- **Finite entry** — detached + positive burn ⇒ eventually hysteretic. Packages
    `commitsToHysteretic_realizes`. -/
theorem eventually_hysteretic_of_detached_commits (cfg : PConfig) (sys : PSys)
    (h_state : sys.state = .detachedShort ∨ sys.state = .detachedWarn)
    (h_burn : cfg.burnRate > 0) : EventuallyHysteretic cfg sys :=
  ⟨commitsToHysteretic cfg.burnRate sys.rollbackCapacity,
   commitsToHysteretic_realizes cfg sys h_state h_burn⟩

/-- **Internal absorption (trace level)** — once hysteretic, an internal-only suffix leaves
    the system UNCHANGED. The single-step `hysteretic_absorbing_internal` is a full equality
    `step … = sys`, lifted over the trace by induction (stronger than state-level). -/
theorem hysteretic_absorbing_trace (cfg : PConfig) :
    ∀ (es : List PEvent) (sys : PSys), sys.state = .hysteretic → AllInternal es →
      run cfg sys es = sys := by
  intro es
  induction es with
  | nil => intro sys _ _; rfl
  | cons e es ih =>
      intro sys hsys hall
      have he : e.isInternal = true := hall e (List.mem_cons.mpr (Or.inl rfl))
      have hstep : step cfg sys e = sys := hysteretic_absorbing_internal cfg sys hsys e he
      have htail : AllInternal es := fun e' he' => hall e' (List.mem_cons.mpr (Or.inr he'))
      show run cfg (step cfg sys e) es = sys
      rw [hstep]
      exact ih sys hsys htail

/-- **The conditional dynamic Δh attractor** — finite entry AND internal absorption
    afterward, under named operational conditions. Not "everything becomes Δh". -/
theorem dynamic_dh_attractor_of_detached_commits (cfg : PConfig) (sys : PSys)
    (h_state : sys.state = .detachedShort ∨ sys.state = .detachedWarn)
    (h_burn : cfg.burnRate > 0) :
    ∃ n,
      (run cfg sys (List.replicate n PEvent.commit)).state = .hysteretic ∧
      ∀ suffix, AllInternal suffix →
        (run cfg (run cfg sys (List.replicate n PEvent.commit)) suffix).state = .hysteretic := by
  refine ⟨commitsToHysteretic cfg.burnRate sys.rollbackCapacity, ?_, ?_⟩
  · exact commitsToHysteretic_realizes cfg sys h_state h_burn
  · intro suffix hsuf
    have hH := commitsToHysteretic_realizes cfg sys h_state h_burn
    rw [hysteretic_absorbing_trace cfg suffix _ hH hsuf]
    exact hH

/-- The handoff witness — the entire discipline. A `Domain` reaches Δh dynamically ONLY when
    supplied this (detached state + positive burn), never by existing in the static graph. -/
structure HandoffToPersistence (d : Domain) where
  cfg : PConfig
  sys : PSys
  detached : sys.state = .detachedShort ∨ sys.state = .detachedWarn
  positiveBurn : cfg.burnRate > 0

/-- The graph→dynamics bridge, one-directional: only a supplied handoff confers the dynamic
    Δh attractor on a domain. -/
theorem domain_enters_dh_of_persistence_handoff (d : Domain) (h : HandoffToPersistence d) :
    ∃ n,
      (run h.cfg h.sys (List.replicate n PEvent.commit)).state = .hysteretic ∧
      ∀ suffix, AllInternal suffix →
        (run h.cfg (run h.cfg h.sys (List.replicate n PEvent.commit)) suffix).state = .hysteretic :=
  dynamic_dh_attractor_of_detached_commits h.cfg h.sys h.detached h.positiveBurn

end LeanProofs.Scratch.PersistenceAttractor
