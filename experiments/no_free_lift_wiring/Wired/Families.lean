/-
  Wired.Families — multiple bridge families + NON-SUBSIDY between them.

  Custody class: MODELED EMBEDDING (structural). Extends the customs office from
  two summands to SIX bridge families (the queued atlas):

    authority · freshness · standing · custody · contraction · consumer-freshness

  Each family carries its OWN intra-family bridge; the global `Bridge` is
  family-LOCAL by construction (cross-family pairs fall through to `False`). That
  locality is the non-subsidy guarantee:

    * `freshness_bridge_cannot_pay_standing`
    * `standing_bridge_cannot_pay_freshness`
    * `authority_cannot_buy_transport`
    * `transport_cannot_mint_authority`
    * `bridge_is_family_local` (the general form: any bridge keeps the family tag)

  HONESTY: non-subsidy is true by the family-local `Bridge` definition — the
  substantive content is the JUSTIFICATION (cross-family bridges are unsound, the
  kernels share no structure to carry through; cf. `Embedding.cross_edge_dichotomy`
  and `UnifiedAdmissibilityBreaks.bridged_unsound`). Per-family SOUNDNESS is real
  for freshness (`Embedding`/`CanonicalEmbedding`); the other families' intra
  bridges are typed and inhabited here but their `Sem`/`BridgeValid` are not yet
  modeled — stubs, flagged, not claimed.
-/
import Wired.NoFreeLift
import Wired.Authority
import Wired.Freshness
import Wired.Embedding

namespace Wired.Families

-- (`NoFreeLift`, `Authority`, `Freshness`, `Embedding` resolve via `Wired`.)

/-! ### Per-family claim payloads (authority/freshness reuse `Embedding`) -/

/-- Standing: a receiver-relative adoption — evidence adopted BY a consumer. -/
structure StandClaim where
  consumer : Nat
  evidence : Nat

/-- Custody: an item held by a holder; handoff is an authorized transition. -/
structure CustClaim where
  holder : Nat
  item   : Nat

/-- BudgetMonotonicity (budget): a resource budget for an item; spending contracts it. -/
structure ContrClaim where
  item   : Nat
  budget : Nat

/-- Consumer-relative freshness: freshness anchored to a consumer's own clock. -/
structure ConsFreshClaim where
  consumer : Nat
  issued   : Nat
  now      : Nat

/-- The six-family claim space. -/
inductive Claim
  | auth      : Embedding.AuthClaim → Claim
  | fresh     : Embedding.FreshClaim → Claim
  | stand     : StandClaim → Claim
  | cust      : CustClaim → Claim
  | contr     : ContrClaim → Claim
  | consFresh : ConsFreshClaim → Claim

/-- Family tag (for the general family-locality theorem). -/
def family : Claim → Nat
  | .auth _      => 0
  | .fresh _     => 1
  | .stand _     => 2
  | .cust _      => 3
  | .contr _     => 4
  | .consFresh _ => 5

/-- The family-LOCAL bridge. Each constructor pair has its own intra-family move;
    every cross-family pair falls through to `False`. Authority has no case → no
    bridge (bridge-inert). -/
def Bridge : Claim → Claim → Prop
  | Claim.fresh f, Claim.fresh f' =>
      -- carry-forward (time transport, budget widens by the step)
      f.cred = f'.cred ∧ f.time ≤ f'.time ∧ f'.budget = f.budget + (f'.time - f.time)
  | Claim.stand s, Claim.stand s' =>
      -- receiver-relative adoption: stays WITH the consumer (no cross-consumer)
      s.consumer = s'.consumer ∧ s.evidence = s'.evidence
  | Claim.cust c, Claim.cust c' =>
      -- authorized handoff: the item is preserved across a holder change
      c.item = c'.item
  | Claim.contr c, Claim.contr c' =>
      -- contraction: same item, budget only spends DOWN
      c.item = c'.item ∧ c'.budget ≤ c.budget
  | Claim.consFresh f, Claim.consFresh f' =>
      -- re-anchor forward in the SAME consumer's clock
      f.consumer = f'.consumer ∧ f.issued = f'.issued ∧ f.now ≤ f'.now
  | _, _ => False

/-! ### Non-subsidy — the four named guarantees -/

/-- A freshness (transport) bridge cannot pay for standing. -/
theorem freshness_bridge_cannot_pay_standing (f : Embedding.FreshClaim) (s : StandClaim) :
    ¬ Bridge (Claim.fresh f) (Claim.stand s) := fun h => h.elim

/-- A standing (adoption) bridge cannot pay for freshness. -/
theorem standing_bridge_cannot_pay_freshness (s : StandClaim) (f : Embedding.FreshClaim) :
    ¬ Bridge (Claim.stand s) (Claim.fresh f) := fun h => h.elim

/-- Authority cannot buy transport (no authority→freshness bridge). -/
theorem authority_cannot_buy_transport (a : Embedding.AuthClaim) (f : Embedding.FreshClaim) :
    ¬ Bridge (Claim.auth a) (Claim.fresh f) := fun h => h.elim

/-- Transport cannot mint authority (no freshness→authority bridge). -/
theorem transport_cannot_mint_authority (f : Embedding.FreshClaim) (a : Embedding.AuthClaim) :
    ¬ Bridge (Claim.fresh f) (Claim.auth a) := fun h => h.elim

/-- **bridge_is_family_local** — the general non-subsidy law: any bridge keeps
    the family tag. No family's bridge ever pays for another's. -/
theorem bridge_is_family_local {c c' : Claim} (h : Bridge c c') : family c = family c' := by
  cases c <;> cases c' <;> first | rfl | exact h.elim

/-! ### Each family's intra-bridge is inhabited (the families are real, not empty) -/

theorem fresh_bridge_inhabited :
    Bridge (Claim.fresh ⟨⟨0, 10, 0⟩, 3, 5⟩) (Claim.fresh ⟨⟨0, 10, 0⟩, 4, 6⟩) := by
  exact ⟨rfl, by decide, by decide⟩

theorem standing_bridge_inhabited :
    Bridge (Claim.stand ⟨7, 42⟩) (Claim.stand ⟨7, 42⟩) := ⟨rfl, rfl⟩

theorem custody_bridge_inhabited :
    Bridge (Claim.cust ⟨1, 99⟩) (Claim.cust ⟨2, 99⟩) := rfl

theorem contraction_bridge_inhabited :
    Bridge (Claim.contr ⟨5, 100⟩) (Claim.contr ⟨5, 60⟩) := ⟨rfl, by decide⟩

theorem consumer_fresh_bridge_inhabited :
    Bridge (Claim.consFresh ⟨3, 0, 5⟩) (Claim.consFresh ⟨3, 0, 8⟩) := ⟨rfl, rfl, by decide⟩

end Wired.Families
