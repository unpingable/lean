/-
  ReachableDrift.FloorBridge — the reach-floor bridge: partial fit, precise
  obstruction.

  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE
  This terminal evidence uses `propext` and no custom axioms.

  Compared to `Run2.ReachFloorCharacterization` (`reachFloor_iff_ancestor_covered`:
  reach-closure IS ancestor coverage by a SINGLE unlabeled `Bridge` closure):

    FITS — `reachable_iff_anyCone`: drift `Reachable` is exactly coverage of an
      observation by the forward cone of `{init}`. Same shape as the reach-floor
      result; the apparatus ports for *reach*.

    DOES NOT FIT — `cone_gap_nonempty` / `drift_needs_two_closures`: the drift
      DIAGNOSIS is the strict GAP between TWO labeled closures (declared ⊆ any). A
      single unlabeled closure like `ReachFloor`/`PaidFrom` has no vocabulary for
      "reachable by the declared sub-relation only," so it characterizes `Reachable`
      but is structurally BLIND to `unauthorizedRequired`. The apparatus does not
      port for *drift* — which is exactly why drift is its own object.
-/

import LeanProofs.ReachableDrift.Basic
import LeanProofs.ReachableDrift.Diagnosis

namespace ReachableDrift

/-- The forward cone: `w'` is reachable from `w` by an `auth`-labeled trace. The
    drift analog of `PaidFrom` (the closure `ReachFloor`/`hfloor` is built on). -/
def ReachesBy (auth : Op → Bool) (w w' : World) : Prop :=
  ∃ t, (∀ op ∈ t, auth op = true) ∧ run w t = w'

/-- **reachable_iff_anyCone** — the FIT. Reachability of an observation IS coverage
    by the forward cone of `{init}` under the all-permissive labeling — the exact
    shape of `reachFloor_iff_ancestor_covered` (origin + closure path → covered). -/
theorem reachable_iff_anyCone (o : Obs) :
    Reachable o ↔ ∃ w, ReachesBy (fun _ => true) init w ∧ observe w = o := by
  constructor
  · rintro ⟨t, hobs⟩; exact ⟨run init t, ⟨t, fun _ _ => rfl, rfl⟩, hobs⟩
  · rintro ⟨w, ⟨t, _, hrun⟩, hobs⟩; exact ⟨t, by rw [hrun]; exact hobs⟩

/-- The declared cone is the same coverage shape under the strict labeling. -/
theorem declaredReachable_iff_declCone (o : Obs) :
    DeclaredReachable o ↔ ∃ w, ReachesBy Op.authorized init w ∧ observe w = o := by
  constructor
  · rintro ⟨t, hdec, hobs⟩; exact ⟨run init t, ⟨t, hdec, rfl⟩, hobs⟩
  · rintro ⟨w, ⟨t, hdec, hrun⟩, hobs⟩; exact ⟨t, hdec, by rw [hrun]; exact hobs⟩

/-- The declared cone is contained in the any-cone (one inclusion). -/
theorem declaredReachable_subset_reachable (o : Obs) :
    DeclaredReachable o → Reachable o := declaredReachable_reachable

/-- **cone_gap_nonempty** — the DOES-NOT-FIT. The inclusion is STRICT: an
    observation reachable but never declared-reachable. The diagnosis lives in this
    gap between two labeled closures — invisible to any single unlabeled closure
    like `ReachFloor`. -/
theorem cone_gap_nonempty :
    ∃ o, Reachable o ∧ ¬ DeclaredReachable o :=
  ⟨⟨false, true, false⟩,
   open_port_over_down_service_requires_unauthorized.2,
   open_port_over_down_service_requires_unauthorized.1⟩

/-- **drift_needs_two_closures** — the bridge verdict in one statement: drift
    reachability is single-closure cone coverage (the `ReachFloor` shape), but the
    declared/undeclared diagnosis is the strict gap between two closures, which a
    single closure cannot express. -/
theorem drift_needs_two_closures :
    (∀ o, Reachable o ↔ ∃ w, ReachesBy (fun _ => true) init w ∧ observe w = o)
    ∧ (∃ o, Reachable o ∧ ¬ DeclaredReachable o) :=
  ⟨reachable_iff_anyCone, cone_gap_nonempty⟩

end ReachableDrift
