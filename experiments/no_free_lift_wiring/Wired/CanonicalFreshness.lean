/-
  Wired.CanonicalFreshness — the FULL canonical `Fresh` shape + the adapter.

  Custody class: MODELED KERNEL + ADAPTER. Step 1 of the hardening: stop testing
  on the stripped `FreshAt` and reconstruct the canonical kernel `Fresh` exactly
  (skew on BOTH window edges, the coherence conjunct, and a SYMMETRIC `absSub`
  divergence), then:

    * `canon_fresh_transports`  — the transport framework carries the FULL
      canonical `Fresh`, including coherence (carried free) and skew (in the
      window). Closes the audit's "coherence dropped / skew dropped" gap.
    * `canon_fresh_to_freshAt`  — the adapter: canonical `Fresh` embeds into the
      abstract `Freshness.FreshAt`. The ONE conjunct the abstract model omits is
      coherence (time-independent) — the adapter makes that gap a visible,
      one-line fact instead of an unstated simplification.

  Mirrors the kernel's `Admissibility/Freshness.lean` conjuncts
  (`TemporallyCoherent`, `DivergenceAcceptable`, `WithinValidity`). Concretized
  at `Nat` for closed witnesses (and so `omega` sees the arithmetic — it does not
  unfold a `Time` abbrev); still ModelBound (real `Time` is opaque in the
  kernel), but fidelity is now a checked adapter, not a hand-wave.
-/
import Wired.Coordinates
import Wired.Divergence
import Wired.Freshness

namespace Wired.CanonicalFreshness

/-- Symmetric divergence (the kernel's `absSub` shape). Satisfies triangle.
    `def` over `Nat` directly so `omega` reads the arithmetic. -/
def absSub (a b : Nat) : Nat := (a - b) + (b - a)

theorem absSub_triangle : ∀ a b c, absSub a c ≤ absSub a b + absSub b c := by
  intro a b c
  show (a - c) + (c - a) ≤ ((a - b) + (b - a)) + ((b - c) + (c - b))
  omega

/-! ### Canonical conjuncts (kernel `Freshness.lean`) -/

abbrev TemporallyCoherent (issued expires : Nat) : Prop :=
  issued ≤ expires ∧ ¬ (expires ≤ issued)

def DivergenceAcceptable (now issued maxDiv : Nat) : Prop :=
  absSub now issued ≤ maxDiv

abbrev WithinValidity (now issued expires skew : Nat) : Prop :=
  (issued - skew) ≤ now ∧ now ≤ (expires + skew)

/-- A canonical credential: issued/expires interval plus skew tolerance. -/
structure CanonCred where
  issued  : Nat
  expires : Nat
  skew    : Nat

/-- The full canonical freshness predicate — all three conjuncts. -/
def CanonFresh (c : CanonCred) (now maxDiv : Nat) : Prop :=
  TemporallyCoherent c.issued c.expires ∧
  DivergenceAcceptable now c.issued maxDiv ∧
  WithinValidity now c.issued c.expires c.skew

/-- **canon_fresh_transports** — the FULL canonical `Fresh` transports soundly.
    Coherence carries FREE (time-independent); the window left bound moves by
    transitivity of `≤`; the divergence ball widens by the triangle inequality
    on `absSub`. The allowance grows `maxDiv → maxDiv + S`: same resource meter,
    now on the real shape with skew and coherence present. -/
theorem canon_fresh_transports
    (c : CanonCred) {now₀ now₁ maxDiv S : Nat}
    (h : CanonFresh c now₀ maxDiv)
    (hwin : now₀ ≤ now₁ ∧ now₁ ≤ c.expires + c.skew)
    (hdiv : absSub now₀ now₁ ≤ S) :
    CanonFresh c now₁ (maxDiv + S) := by
  obtain ⟨hcoh, hdacc, hval⟩ := h
  refine ⟨hcoh, ?_, ?_⟩
  · -- divergence ball widens by triangle on absSub
    have h1 : (now₀ - c.issued) + (c.issued - now₀) ≤ maxDiv := hdacc
    have h2 : (now₀ - now₁) + (now₁ - now₀) ≤ S := hdiv
    show (now₁ - c.issued) + (c.issued - now₁) ≤ maxDiv + S
    omega
  · -- window: left bound by transitivity, right bound re-supplied
    exact ⟨Nat.le_trans hval.1 hwin.1, hwin.2⟩

/-- **canon_fresh_to_freshAt** — the adapter. Canonical `Fresh` embeds into the
    abstract `Freshness.FreshAt` over `(≤, absSub)`, mapping the skewed interval
    to the window `[issued - skew, expires + skew]`. The coherence conjunct is
    the ONLY thing dropped (time-independent), making the fidelity gap explicit
    and one line wide. -/
theorem canon_fresh_to_freshAt (c : CanonCred) (now maxDiv : Nat)
    (h : CanonFresh c now maxDiv) :
    Freshness.FreshAt (· ≤ ·) absSub
      ⟨c.issued - c.skew, c.expires + c.skew, c.issued⟩ now maxDiv := by
  obtain ⟨_hcoh, hdacc, hval⟩ := h   -- _hcoh dropped: the explicit fidelity gap
  refine ⟨hval, ?_⟩
  have h1 : (now - c.issued) + (c.issued - now) ≤ maxDiv := hdacc
  show (c.issued - now) + (now - c.issued) ≤ maxDiv
  omega

end Wired.CanonicalFreshness
