/-
  Custody-Class: ANNEX

  Admissibility — AxisSkew kernel (directional comparison axis).

  Keeper:
    Staleness says the map is old. Skew says which way it lies.

  Tiny sibling module. Formalizes a *directional* relationship between a
  prior claim and an observed claim along an ordered comparison surface,
  distinguishing the case where the prior underclaims observed state
  (lagging) from the case where it overclaims (leading). The split is
  orientation, not verdict — `reverse_lagging_is_leading` makes this
  explicit by proving the classification depends on the (prior, observed)
  argument ordering, not on either value alone.

  Open formal residue:
    Stale-binding is the substrate-rich primitive for the lagging
    direction (caches, hat-x estimates, briefings, P23–P27). The leading
    direction — prior overclaims observed state — has no equivalent
    substrate-general primitive. This module supplies the abstract
    bidirectional kernel; the operator-facing application lives in
    `papers/working/primitives/memory-skew.md`.

  Sibling modules in `LeanProofs/Admissibility/`:
    Freshness    — time-axis specialization. Already encodes both
                   directions on the temporal axis: `NotYetValid`
                   (leading) and `Expired` (lagging).
    Corrective   — corrective transitions; composition with AxisSkew
                   (e.g., "lagging may authorize correction, not
                   mutation") is open formal work. Its statement must
                   specify the bridge from skew to corrective standing.

  Companion working primitive:
    papers/working/primitives/memory-skew.md
    (operator-facing application; stale-binding remains the substrate-
    rich lagging primitive — it does NOT become an instance of AxisSkew,
    it stays parallel, because stale-binding's consequence-window
    machinery is substrate detail the abstract kernel should not absorb)

  Scope fences:
    - Formalizes the *abstract directional split* under a consumer-
      supplied comparison relation. Does NOT pin a five-axis enum
      (recency / completeness / authority / capability / integration);
      that taxonomy is operator-facing and lives in the prose primitive.
    - Does NOT formalize the operational claim "lagging may justify
      correction but not authorize mutation." That theorem would
      compose with Corrective/Authority and may be developed in Scratch
      once its bridge assumptions are stated; no consumer is required.
    - Does NOT pin `Nat` or any concrete rank type. The relation is
      consumer-supplied so domain-specific orderings (partial, preorder,
      lattice, total) can each be its argument.
    - Does NOT call itself a calculus.

  Custody:
    This module is canonical only via its commit hash + lake build proof
    gate. A definition matching this signature elsewhere does not inherit
    the canonical anchoring of this file.
-/

namespace Admissibility.AxisSkew

/-- Directional relationship between a prior claim and an observed
    claim along an ordered comparison surface. The classification
    names *which direction* the prior diverges from observation; it
    does not assign moral status. Orientation, not verdict. -/
inductive Skew where
  /-- Prior underclaims observed: `lt prior observed` holds. -/
  | lagging
  /-- Prior and observed indistinguishable under the supplied relation. -/
  | matched
  /-- Prior overclaims observed: `lt observed prior` holds. -/
  | leading
deriving DecidableEq, Repr

universe u
variable {α : Type u}

/-- Classify the (prior, observed) pair under a supplied comparison
    relation `lt`. The relation is consumer-supplied: time-axis
    consumers may pass `<` on timestamps; authority-axis consumers may
    pass a partial standing order; capability-axis consumers may pass
    a domain-specific lattice's strict order. The kernel proves
    invariants of the *shape* of the classification, not of the
    underlying order. -/
def classifyBy (lt : α → α → Prop) [DecidableRel lt]
    (prior observed : α) : Skew :=
  if lt prior observed then Skew.lagging
  else if lt observed prior then Skew.leading
  else Skew.matched

/-- The classification is functional: a single (prior, observed) pair
    cannot simultaneously be classified both `lagging` and `leading`
    along the same comparison surface. The formal version of
    *a prior cannot both underclaim and overclaim the same observed
    state on the same axis*. -/
theorem not_lagging_and_leading_same_axis
    {lt : α → α → Prop} [DecidableRel lt] (p o : α) :
    ¬ (classifyBy lt p o = Skew.lagging ∧ classifyBy lt p o = Skew.leading) := by
  intro ⟨h1, h2⟩
  rw [h1] at h2
  exact Skew.noConfusion h2

/-- Reflexive case: a value compared to itself classifies as `matched`,
    given that the supplied relation is irreflexive at that point. -/
theorem classify_self
    {lt : α → α → Prop} [DecidableRel lt]
    (s : α) (irrefl : ¬ lt s s) :
    classifyBy lt s s = Skew.matched := by
  unfold classifyBy
  simp [irrefl]

/-- Reversing the (prior, observed) argument order swaps `lagging` and
    `leading`. The orientation theorem: classification is relative to
    argument order, not a property of either value alone. Requires
    asymmetry of the supplied relation — under a symmetric relation,
    `lagging` and `leading` collapse. -/
theorem reverse_lagging_is_leading
    {lt : α → α → Prop} [DecidableRel lt]
    (asymm : ∀ a b, lt a b → ¬ lt b a)
    (p o : α) (h : classifyBy lt p o = Skew.lagging) :
    classifyBy lt o p = Skew.leading := by
  unfold classifyBy at h ⊢
  by_cases hpo : lt p o
  · have hop : ¬ lt o p := asymm p o hpo
    simp [hop, hpo]
  · simp [hpo] at h
    by_cases hop : lt o p
    · simp [hop] at h
    · simp [hop] at h

end Admissibility.AxisSkew
