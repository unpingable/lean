/-
  Custody-Class: UNRATIFIED-CANDIDATE

  LocalBoundary pressure test, concrete instance (2026-07-09). Hostile
  specimen for the merge seam: a two-domain world in which

    WeakMergeAdmissible (= MergeAdmissible minus `left_sound`) ACCEPTS
    a merge that then reaches a NoInternalExternalExposure violation
    in one component step.

  `LocalBoundary.lean` already proves the parametric field-level pressure
  tests (`dropping_left_sound_permits_merged_partition_violation` and its
  right twin) — but those are hypothesis-conditional: IF some component
  locally authorizes a merged-Internal→External exposure, THEN a violation
  is reachable. This file discharges the inhabitation debt: the hypotheses
  are satisfiable by a concrete, four-line configuration, so the parametric
  tests are not vacuous, and `left_sound` is genuinely load-bearing (not
  merely unused). The load-bearing field is NAMED by construction: the
  weakened predicate below drops exactly `left_sound` and nothing else.

  No edits to `LocalBoundary.lean` or `Composition.lean` — the green ANNEX
  aperture is consumed, not mutated. This file does not claim completeness
  of `MergeAdmissible` (the five bad cases remain paper-shaped), does not
  promote the aperture, and is not a step toward a unified calculus.

  Unwired: not imported by `LeanProofs.lean` or any default target.
  Mathlib-reaching (via `Composition`'s Finset config); build directly:
  `lake build LeanProofs.Admissibility.LocalBoundaryPressure`.
-/

import LeanProofs.Admissibility.LocalBoundary

/-!
# LocalBoundary Pressure — concrete escape

The world: two domains, `inside` and `outside`. The merged partition marks
`inside` Internal and `outside` External. The left component's boundary is
fully permissive (it authorizes every edge, including inside→outside); the
right component's boundary is sealed (authorizes nothing).

Then:

- `WeakMergeAdmissible` (right_sound only) holds — vacuously on the right,
  and the left is simply not asked.
- `MergeAdmissible` fails — `left_sound` is refuted by the leak exposure.
- One left component step from the initial configuration lands in a state
  violating `NoInternalExternalExposure` for the merged partition.

So the weakened obligation admits precisely the merge that leaks:
`left_sound` is the field standing between "locally authorized" and
"globally exfiltrated" whenever the LEFT component is the permissive one.
-/

namespace Admissibility.LocalBoundaryPressure

open CrossBoundaryExposure
open Composition
open LocalBoundary

/-- Two domains. `inside` will be merged-Internal, `outside` merged-External. -/
inductive World
  | inside
  | outside
deriving DecidableEq, Repr

/-- One failure kind; the pressure test does not vary it. -/
inductive Leak
  | secret
deriving DecidableEq, Repr

/-- Fully permissive boundary: authorizes every edge. The hostile component. -/
def permissive : Boundary World := { authorized := fun _ _ => true }

/-- Sealed boundary: authorizes nothing. The innocent component. -/
def sealed : Boundary World := { authorized := fun _ _ => false }

/-- The merged partition: inside is Internal, outside is External. -/
def mergedPartition : BoundaryPartition World :=
  { Internal := fun d => d = World.inside
  , External := fun d => d = World.outside }

def lb₁ : LocalBoundary World :=
  { partition := mergedPartition, boundary := permissive }

def lb₂ : LocalBoundary World :=
  { partition := mergedPartition, boundary := sealed }

def lbₘ : LocalBoundary World :=
  { partition := mergedPartition, boundary := sealed }

/-- The exfiltrating exposure: inside → outside. -/
def leak : Exposure World Leak :=
  { origin := World.inside, target := World.outside, failure := Leak.secret }

/-- **The weakened merge predicate**: `MergeAdmissible` with `left_sound`
    dropped and NOTHING else changed. The subject of the pressure test —
    comparing it against `MergeAdmissible` names the load-bearing field
    by construction. -/
structure WeakMergeAdmissible {Domain Failure : Type}
    (lb₁ lb₂ lbₘ : LocalBoundary Domain) : Prop where
  right_sound :
    ∀ e : Exposure Domain Failure,
      LocalAllows lb₂ (Action.expose (Failure := Failure) e) →
      ¬ (lbₘ.partition.Internal e.origin ∧ lbₘ.partition.External e.target)

/-- Every lawful merge is a weak merge — the weakening is genuine, not a
    sideways variant. -/
theorem mergeAdmissible_weakens {Domain Failure : Type}
    {lb₁ lb₂ lbₘ : LocalBoundary Domain}
    (h : MergeAdmissible (Failure := Failure) lb₁ lb₂ lbₘ) :
    WeakMergeAdmissible (Failure := Failure) lb₁ lb₂ lbₘ :=
  ⟨h.right_sound⟩

/-! ## The three facts of the escape -/

/-- 1. The weakened predicate ACCEPTS this merge: the sealed right component
    authorizes nothing, so `right_sound` holds vacuously — and the weakened
    predicate never asks about the permissive left. -/
theorem weak_merge_accepts :
    WeakMergeAdmissible (Failure := Leak) lb₁ lb₂ lbₘ := by
  refine ⟨fun e hAllows => ?_⟩
  simp [LocalAllows, lb₂, sealed] at hAllows

/-- 2. The full predicate REFUSES this merge, and the refutation goes through
    `left_sound` applied to `leak` — the dropped field is exactly the one
    doing the work. -/
theorem merge_admissible_refuses :
    ¬ MergeAdmissible (Failure := Leak) lb₁ lb₂ lbₘ := by
  intro h
  exact h.left_sound leak (by simp [LocalAllows, lb₁, permissive])
    ⟨rfl, rfl⟩

/-- 3. The escape is REACHABLE: one left component step from the initial
    configuration violates the merged-partition invariant. Discharges the
    inhabitation debt of the parametric pressure test in `LocalBoundary`. -/
theorem weakened_merge_allows_exposure_violation :
    ∃ s : SystemState World Leak,
      ComponentReach lb₁ lb₂
        ⟨Process.par (Process.expose leak Process.stop) Process.stop,
          initialConfig World Leak⟩ s ∧
      ¬ NoInternalExternalExposure lbₘ.partition s.config :=
  dropping_left_sound_permits_merged_partition_violation
    (lb₁ := lb₁) (lb₂ := lb₂) (lbₘ := lbₘ) leak
    (by simp [LocalAllows, lb₁, permissive])
    ⟨rfl, rfl⟩

/-- The summary object: the weakened predicate holds AND the violation is
    reachable — in one theorem, so the escape cannot be quoted in halves. -/
theorem weak_merge_is_not_merge :
    WeakMergeAdmissible (Failure := Leak) lb₁ lb₂ lbₘ ∧
    ∃ s : SystemState World Leak,
      ComponentReach lb₁ lb₂
        ⟨Process.par (Process.expose leak Process.stop) Process.stop,
          initialConfig World Leak⟩ s ∧
      ¬ NoInternalExternalExposure lbₘ.partition s.config :=
  ⟨weak_merge_accepts, weakened_merge_allows_exposure_violation⟩

/-! ## Doctrine -/

def doctrine : List String :=
  [ "left_sound is load-bearing: dropping it admits a merge that leaks in one step",
    "the weakened predicate is a genuine weakening (every lawful merge satisfies it) — and that is exactly what is wrong with it",
    "local allows are not enough; every component's authorization must answer to the merged partition",
    "this names one load-bearing field; it does not prove MergeAdmissible complete" ]

-- Runnable demonstrations (the boundary flags behind the escape):
#eval permissive.authorized World.inside World.outside   -- true  (left authorizes the leak)
#eval sealed.authorized World.inside World.outside       -- false (right authorizes nothing)
#eval doctrine

end Admissibility.LocalBoundaryPressure
