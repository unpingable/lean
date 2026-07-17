/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE

  CollapsedSurface — Discrete-finite form of observation-equivalence.

  Companion to LeanProofs/Paper25EpistemicBorderControl.lean (matrix /
  dynamical formulation of observation-equivalence) and to the candidate
  Signal Authority working note (papers/working/signal-authority-candidate.md).

  Establishes the elementary structural result: if a render function from
  a finite set of authority-distinct causes to a finite set of public
  surfaces is non-injective, the surface cannot license cause-specific
  inference. Same shape as Paper 25's `obsEquiv_policy_same`, in discrete
  clothing.

  Specimen (illustrative only, not load-bearing):
    Authority-distinct causes — user-initiated removal, platform enforcement,
    legal restriction, viewer-side filtering, infrastructure failure,
    application bug — collapse to a small set of public UI states
    (`notFound`, `unavailable`). The surface cannot identify which cause
    produced it.

  Scope fence:
    This module is the kernel nub for discrete render collapse. It does
    not model receipts, state-at-time-T, or the full forensic-underdetermination
    claim. Receipt-refinement (the recovery side: `public_receipt_refines_observation`)
    is deferred — see Paper 24's receipt-lineage discussion for the
    semi-formal version.

  Keeper line:
    If two distinct causes render to the same public surface, that
    surface cannot identify either cause.

  Recovery side (deferred, not formalized here):
    A collapsed observation can be broken only by:
      1. preserved history (receipts, lineage, state-at-time-T)
      2. independent measurement (a witness adding rank, not replication)
      3. admissible perturbation (controlled excitation without laundering
         harm or coercion as measurement)
    Preserved-history and independent-measurement cases have partial
    homes in Paper 24's receipt-lineage and Paper 25's Gramian scaling
    respectively. Admissible perturbation is named but not corpus-formal.
    See papers/working/signal-authority-candidate.md §Recovery side.

    This module proves the negative kernel only: a collapsed public
    surface cannot identify cause-specific authority. Receipt-refinement
    and perturbation recovery are intentionally not formalized here.
-/

namespace CollapsedSurface

/-- Authority-distinct causes that can produce a public surface state.
    Discrete and finite by construction; real platforms have larger
    enumerations but the structural claim is unchanged. -/
inductive Cause where
  | userDeleted
  | userDeactivated
  | platformSuspended
  | platformTakedown
  | legalRestriction
  | viewerFilter
  | infraFailure
  | appBug
deriving DecidableEq, Repr

/-- Coarse public surface states (the rendered UI / API response). -/
inductive Surface where
  | live
  | notFound
  | suspended
  | unavailable
deriving DecidableEq, Repr

/-- Illustrative render mapping. Multiple authority-distinct causes collapse
    to the same public surface. The collapse is the structural problem;
    the specific assignments are illustrative only. -/
def render : Cause → Surface
  | .userDeleted        => .notFound
  | .userDeactivated    => .notFound
  | .platformSuspended  => .notFound
  | .platformTakedown   => .notFound
  | .legalRestriction   => .notFound
  | .viewerFilter       => .unavailable
  | .infraFailure       => .unavailable
  | .appBug             => .unavailable

/-- `s` identifies `c` when `c` renders to `s` and is the unique cause
    that does so. Both conjuncts matter: without `render c = s`,
    surfaces with no preimage would vacuously identify any cause. -/
def Identifies (s : Surface) (c : Cause) : Prop :=
  render c = s ∧ ∀ c', render c' = s → c' = c

/-- A surface is collapsed-at when two distinct causes render to it. -/
def CollapsedAt (s : Surface) : Prop :=
  ∃ c₁ c₂ : Cause, c₁ ≠ c₂ ∧ render c₁ = s ∧ render c₂ = s

/-- Kernel lemma: if any cause `c'` distinct from `c` renders to `s`,
    then `s` does not identify `c`. -/
theorem alt_cause_prevents_identification
    {s : Surface} {c c' : Cause}
    (hne : c' ≠ c)
    (hc' : render c' = s) :
    ¬ Identifies s c := by
  intro hid
  exact hne (hid.2 c' hc')

/-- Universal corollary: a collapsed surface identifies no cause. -/
theorem collapsed_surface_not_identified
    {s : Surface} (hcoll : CollapsedAt s) :
    ∀ c, ¬ Identifies s c := by
  intro c hid
  obtain ⟨c₁, c₂, hne, h₁, h₂⟩ := hcoll
  by_cases hc1 : c₁ = c
  · -- c₁ = c; therefore c₂ ≠ c renders to s
    rw [hc1] at hne
    exact (Ne.symm hne) (hid.2 c₂ h₂)
  · -- c₁ ≠ c renders to s
    exact hc1 (hid.2 c₁ h₁)

/-- Concrete instance: `notFound` does not identify `platformSuspended`,
    because `userDeleted` also renders to `notFound`. The platform's
    public UI cannot license the inference "this account was suspended"
    on the basis of the `notFound` surface alone. -/
theorem notFound_does_not_identify_platformSuspended :
    ¬ Identifies Surface.notFound Cause.platformSuspended :=
  alt_cause_prevents_identification
    (c' := Cause.userDeleted)
    (by decide)
    rfl

end CollapsedSurface
