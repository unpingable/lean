/-
  Wired.CoCompilation — co-compilation marker (imports everything).

  NAME NOTE (de-placarded 2026-06-16): formerly `Wired.Composition`. The old name
  was a placard — it suggested a composition *result*, but this module proves
  nothing about composition: it only imports the tree and witnesses that the whole
  stack co-compiles. The real composition theorem does NOT exist yet; it is the
  open construction ticket in `COMPOSITION-CLASSIFICATION-TARGET.md`. Renamed so
  the next fresh reader infers co-compilation, not a closure result that isn't here.

  Custody class: AGGREGATOR (imports everything). Proves nothing new. Import
  reachability is electrical continuity, NOT custody — see `WIRING-AUDIT.md`.

  What the customs office over Authority ⊕ Freshness gives, all checked upstream:
    * `Embedding.embedded_lift_sound`              — the office is sound.
    * `Embedding.freshness_bridge_valid`           — bridges are paid, not assumed.
    * `Embedding.authority_is_conservative`        — authority is bridge-inert.
    * `Embedding.freshness_lift_has_freshness_origin` — no cross-axis laundering.
    * `Freshness.transport_adds_power`             — freshness transport beats the floor.
    * `Freshness.freshness_decays`                 — the budget meter runs inside.
    * `NoFreeLift.no_bridge_no_lift`               — no bridge context, no lift.
    * `NoFreeLift.naked_lift_unsound`              — unpaid lift is refused.
    * `CarryLaws.transitivity_is_the_cost_of_sound_carry_forward`
    * `CarryLaws.triangle_is_the_cost_of_divergence_transport`

  Hardening layer (each adversarially reviewed; see `WIRING-AUDIT.md`):
    * `CanonicalFreshness.canon_fresh_transports` / `canon_fresh_to_freshAt`
        — transport over the FULL canonical `Fresh` + adapter (codex: real).
    * `CanonicalEmbedding.embedded_canon_sound`
        — a REAL embedding: kernel = canonical `CanonFresh`, bridge = reviewed
          transport, sound via `paid_lift_sound` (codex: all real).
    * `Embedding.cross_edge_dichotomy`
        — authority↔freshness edge is unsound-if-unpaid, redundant-if-valid.
    * `Families.{authority_cannot_buy_transport, transport_cannot_mint_authority,
        freshness_bridge_cannot_pay_standing, standing_bridge_cannot_pay_freshness,
        bridge_is_family_local}` — six-family non-subsidy (structural; the
        authority↔freshness pair also semantically backed).

  The name "calculus" is NOT earned by this co-compilation. The object is a formal
  THEORY of attestation boundaries until the composition-classification gate clears
  (`COMPOSITION-CLASSIFICATION-TARGET.md`, rung 2 of the name ladder). The spine is
  schema-level; the embeddings are ModelBound. `UnifiedAdmissibilityBreaks` proved
  the 1.0 ghost (a roof collapsing the kernels) empty-or-unsound; this is the other
  thing — a floor-plus-paid-bridges discipline — but a discipline is not yet a
  calculus, and a co-compiling tree does not ratify a name.
-/
import Wired.CarryLaws
import Wired.Coordinates
import Wired.Divergence
import Wired.Authority
import Wired.Freshness
import Wired.CanonicalFreshness
import Wired.NoFreeLift
import Wired.Embedding
import Wired.CanonicalEmbedding
import Wired.Families

namespace Wired.CoCompilation

/-- Discoverable marker: the full stack co-compiles. Makes NO substantive claim
    (in particular, no composition result — that theorem is unbuilt); the substance
    is the named theorems re-listed in this module's docstring. -/
theorem modules_cocompile : True := trivial

end Wired.CoCompilation
