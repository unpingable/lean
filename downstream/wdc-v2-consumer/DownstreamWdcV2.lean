/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE

  External downstream receipt for LeanProofs v2.0.0.

  This file intentionally imports only the public `LeanProofs.Witnessed` aggregator from
  the released package dependency. It touches the three v2 normalization receipts a
  downstream user should be able to consume:

    * `AbstractNormalization.normal_form_iff_of_commutes`
    * `Normalization.bridge_path_normal_form`
    * `CommutesNecessity.commutes_is_necessary`
-/

import LeanProofs.Witnessed

namespace DownstreamWdcV2

open LeanProofs.Witnessed.NoFreeLift
open LeanProofs.Witnessed.AbstractNormalization

def Carry (a b : Nat) : Prop := b = a + 1
def Weaken (a b : Nat) : Prop := b = a

theorem downstream_commutes : Commutes Carry Weaken := by
  intro _a b c hw hc
  subst b
  exact ⟨c, hc, rfl⟩

/-- A downstream user can instantiate the model-independent v2 normal-form theorem on
    their own two-family bridge system. -/
example {a c : Nat} :
    PaidFrom (Step Carry Weaken) a c ↔
      ∃ z, Chain Carry a z ∧ Chain Weaken z c :=
  normal_form_iff_of_commutes downstream_commutes

/-- The 1.4 freshness theorem remains available with its original public shape, now as the
    freshness instance of the v2 abstract theorem. -/
example {f h : LeanProofs.Witnessed.Normalization.FreshClaim} :
    PaidFrom LeanProofs.Witnessed.Embedding.Bridge (Sum.inr f) (Sum.inr h) ↔
      ∃ g,
        LeanProofs.Witnessed.Normalization.CChain f g ∧
        LeanProofs.Witnessed.Normalization.WChain g h :=
  LeanProofs.Witnessed.Normalization.bridge_path_normal_form

/-- The necessity counterexample is part of the public WDC surface: the commutation law is
    load-bearing, not decorative. -/
example :
    ∃ (β : Type) (Carry Weaken : β → β → Prop) (a c : β),
      ¬ Commutes Carry Weaken ∧
      PaidFrom (Step Carry Weaken) a c ∧
      ¬ ∃ z, Chain Carry a z ∧ Chain Weaken z c :=
  LeanProofs.Witnessed.CommutesNecessity.commutes_is_necessary

#check LeanProofs.Witnessed.AbstractNormalization.normal_form_iff_of_commutes
#check LeanProofs.Witnessed.Normalization.bridge_path_normal_form
#check LeanProofs.Witnessed.CommutesNecessity.commutes_is_necessary

end DownstreamWdcV2
