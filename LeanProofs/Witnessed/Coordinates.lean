/-
  LeanProofs.Witnessed.Coordinates — the interval/order coordinate.

  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: STABLE-SURFACE
  Abstract stable coordinate, polymorphic over a carrier `Time` and a bare
  relation `before`. The transport
  soundness here consumes ONLY transitivity (`btrans`) — see `LeanProofs.Witnessed.CarryLaws`
  for why that is exactly the cost.
-/
import LeanProofs.Witnessed.CarryLaws

namespace LeanProofs.Witnessed.Coordinates

/-- A `before`-interval. -/
structure Window (Time : Type) where
  lo : Time
  hi : Time

/-- `t` lies inside the interval. -/
abbrev ValidAt {Time : Type} (before : Time → Time → Prop) (w : Window Time) (t : Time) : Prop :=
  before w.lo t ∧ before t w.hi

/-- Transport receipt: `t₁` is after `t₀` and still inside the right edge. -/
abbrev Transport {Time : Type} (before : Time → Time → Prop)
    (w : Window Time) (t₀ t₁ : Time) : Prop :=
  before t₀ t₁ ∧ before t₁ w.hi

/-- Lawful interval transport, using only transitivity of `before`. -/
theorem transport_sound_under_transitive_relation
    {Time : Type} (before : Time → Time → Prop)
    (btrans : ∀ a b c, before a b → before b c → before a c)
    {w : Window Time} {t₀ t₁ : Time}
    (hv : ValidAt before w t₀) (ht : Transport before w t₀ t₁) :
    ValidAt before w t₁ :=
  ⟨btrans _ _ _ hv.1 ht.1, ht.2⟩

end LeanProofs.Witnessed.Coordinates
