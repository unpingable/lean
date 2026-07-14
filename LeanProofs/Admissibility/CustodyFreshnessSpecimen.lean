/-
  Custody-Class: UNRATIFIED-CANDIDATE

  Custody-freshness specimen (2026-07-09). The NQ/Nightshift seam's named
  gap, closed as an anti-free-conversion law:

    fresh-here ≠ fresh-there — "Freshness is not transitive across custody."

  Runtime doctrine (nightshift/docs/working/gaps/GAP-imported-basis-freshness.md,
  crates/nightshiftd/src/freshness.rs):

    "Night Shift may consume NQ findings. It cannot upgrade custody into basis."
    "NQ lifecycle / custody time cannot launder upstream observation time."
    "Clocks are witnesses, not facts. A timestamp is evidence about time,
     not authority over time."
    "If the producer clock is absent or incoherent, freshness is
     unknown / cannot-assess — never inferred from" custody clocks.

  And NQ's verdict rule (nq/docs/operator/VERDICTS.md, `stale_testimony`):
  "Freshness is evaluated against `observed_at`, not `generated_at` or
  ingest time."

  Method (the LocalBoundaryPressure pattern): model BOTH evaluators — the
  lawful one (`freshAt`, producer clock only) and the tempting one
  (`freshByCustody`, "recently checked somewhere") — and prove they come
  apart on concrete witnesses. The laundering is not just absent from the
  lawful evaluator; the wrong evaluator is exhibited and refuted, so the
  temptation has a name and a countermodel.

  Sibling seams cited, not re-proved: single-custody staleness is
  `Freshness` [1.0] / `DeferredWitness` (ANNEX); the two-clock
  observation-vs-discharge gap is `FreshnessDynamicTrace` (ANNEX); custody
  crossing importing testimony-under-cap (not basis) is
  `BridgeCustomsSpecimen`. This file owns exactly the chain-shaped law:
  no sequence of custody hops, however recent, refreshes anything.

  NOT modeled, on purpose: clock skew/coherence checking (stipulated as the
  `Option` producer clock), NQ's basis_state lifecycle (deliberately a
  different cut per NQ's own roadmap), generation counters, transport.

  Unwired: not imported by `LeanProofs.lean` or any default target. Build
  directly: `lake build LeanProofs.Admissibility.CustodyFreshnessSpecimen`.
  Formalization does not wait on runtime adoption. Under the current custody
  fence, ANNEX promotion still requires a runtime artifact to identify the
  named theorems it adopts. Citation names the intended contract; conformance
  still requires a mapping plus runtime evidence or a refinement proof.
-/

/-!
# Custody Freshness Specimen

An observation has a producer clock (`observedAt`, possibly absent). A
derived claim carries the observation plus a custody chain — hops with
their own received/checked timestamps. The lawful evaluator reads the
producer clock and nothing else; the tempting evaluator reads the most
recent custody touch. The theorems: the lawful verdict is invariant under
the chain, hops never refresh, an absent producer clock is never fresh —
and the two evaluators provably disagree on a concrete stale-but-recently-
checked claim, which is exactly the rot ("recently checked somewhere"
becoming "currently valid here") with a type and a countermodel.
-/

namespace Admissibility.CustodyFreshnessSpecimen

abbrev Time    := Nat
abbrev Holder  := String

/-- An upstream observation. `observedAt = none` models an absent or
    incoherent producer clock — the case the runtime says must be
    "unknown / cannot-assess — never inferred." -/
structure Observation where
  observedAt : Option Time
deriving Repr, DecidableEq

/-- One custody hop: a holder received the finding and (perhaps recently)
    checked it. Custody timestamps are evidence about custody, not
    authority over the observation's age. -/
structure CustodyHop where
  holder     : Holder
  receivedAt : Time
  checkedAt  : Time
deriving Repr, DecidableEq

/-- A claim as it arrives downstream: the origin observation plus however
    many custody hops it crossed. -/
structure DerivedClaim where
  origin : Observation
  chain  : List CustodyHop
deriving Repr, DecidableEq

/-! ## The two evaluators -/

/-- The LAWFUL evaluator: fresh iff the PRODUCER clock is present and within
    the window. Custody is not consulted — the theorems below prove that is
    a law, not an accident. -/
def freshAt (window now : Time) (c : DerivedClaim) : Bool :=
  match c.origin.observedAt with
  | some t => decide (now ≤ t + window)
  | none   => false

/-- The most recent custody touch on the chain, if any. -/
def lastCustodyTouch (c : DerivedClaim) : Option Time :=
  (c.chain.map fun h => h.checkedAt).max?

/-- The TEMPTING evaluator — "recently checked somewhere": fresh iff some
    custody touch is within the window. This is the laundering move, given
    a type so it can be refuted by name. It is NOT used by anything. -/
def freshByCustody (window now : Time) (c : DerivedClaim) : Bool :=
  match lastCustodyTouch c with
  | some t => decide (now ≤ t + window)
  | none   => false

/-! ## The laws -/

/-- Positive (so nothing below is vacuous): a claim whose producer clock is
    within the window is fresh, chain or no chain. -/
theorem fresh_origin_is_fresh (window now t : Time) (chain : List CustodyHop)
    (h : now ≤ t + window) :
    freshAt window now { origin := ⟨some t⟩, chain := chain } = true := by
  simp [freshAt, h]

/-- Custody time does not launder observation time: the lawful verdict is
    invariant under the custody chain. `freshAt` is a real evaluator over
    the whole claim — this is the proof it has no input path from custody
    clocks. -/
theorem custody_time_does_not_launder_observation_time
    (window now : Time) (origin : Observation)
    (chain chain' : List CustodyHop) :
    freshAt window now { origin := origin, chain := chain } =
    freshAt window now { origin := origin, chain := chain' } := rfl

/-- Hops never refresh: appending any custody hop — however recent its
    check — cannot flip a stale claim fresh. "Recently checked somewhere"
    is not "currently valid here." -/
theorem hop_does_not_refresh (window now : Time) (c : DerivedClaim)
    (hstale : freshAt window now c = false) (hop : CustodyHop) :
    freshAt window now { c with chain := c.chain ++ [hop] } = false :=
  (custody_time_does_not_launder_observation_time window now c.origin
    (c.chain ++ [hop]) c.chain).trans hstale

/-- An absent producer clock is never fresh — for ANY custody chain. The
    runtime's "unknown / cannot-assess — never inferred from custody
    clocks," as a theorem. -/
theorem absent_producer_clock_never_fresh (window now : Time)
    (chain : List CustodyHop) :
    freshAt window now { origin := ⟨none⟩, chain := chain } = false := rfl

/-! ## The separation witnesses (the two evaluators are different animals) -/

/-- Stale at origin, checked five minutes ago: observed at t=0 with window
    100, now = 1000; a custody hop checked at t=990. -/
def staleButRecentlyChecked : DerivedClaim :=
  { origin := ⟨some 0⟩
  , chain  := [{ holder := "nightshift", receivedAt := 900, checkedAt := 990 }] }

/-- Separation 1: the tempting evaluator says fresh, the lawful one says
    stale — on the same claim. The exact rot, inhabited: custody recency is
    not observation freshness. -/
theorem custody_recency_is_not_freshness :
    freshByCustody 100 1000 staleButRecentlyChecked = true ∧
    freshAt 100 1000 staleButRecentlyChecked = false := by
  constructor <;> decide

/-- No producer clock, impeccable custody paper trail. -/
def clocklessButWellCustodied : DerivedClaim :=
  { origin := ⟨none⟩
  , chain  := [{ holder := "nq", receivedAt := 980, checkedAt := 995 }] }

/-- Separation 2: custody clocks cannot substitute for a missing producer
    clock. The tempting evaluator manufactures freshness from the paper
    trail; the lawful one refuses. -/
theorem custody_cannot_substitute_for_producer_clock :
    freshByCustody 100 1000 clocklessButWellCustodied = true ∧
    freshAt 100 1000 clocklessButWellCustodied = false := by
  constructor <;> decide

/-! ## Doctrine -/

def doctrine : List String :=
  [ "freshness is not transitive across custody — consuming a finding cannot upgrade custody into basis",
    "freshness is evaluated against the producer's observed_at, never against received/checked/ingest time",
    "clocks are witnesses, not facts: a custody timestamp is evidence about custody, not authority over the observation's age",
    "an absent or incoherent producer clock means cannot-assess — never freshness inferred from the paper trail",
    "the tempting evaluator has a name and a countermodel; do not implement it" ]

/-! ## Specimens -/

-- Runnable demonstrations (window 100, now 1000):
#eval freshAt 100 1000 { origin := ⟨some 950⟩, chain := [] }        -- true  (fresh origin)
#eval freshAt 100 1000 staleButRecentlyChecked                      -- false (stale origin)
#eval freshByCustody 100 1000 staleButRecentlyChecked               -- true  (the rot, named)
#eval freshAt 100 1000 clocklessButWellCustodied                    -- false (no producer clock)
#eval freshByCustody 100 1000 clocklessButWellCustodied             -- true  (the rot, again)
#eval freshAt 100 1000
  { origin := ⟨some 0⟩
  , chain := List.replicate 5 { holder := "relay", receivedAt := 999, checkedAt := 999 } }
  -- false (five fresh hops refresh nothing)

#eval doctrine

end Admissibility.CustodyFreshnessSpecimen
