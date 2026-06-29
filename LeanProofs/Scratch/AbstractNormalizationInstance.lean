/-
  Custody-Class: SCRATCH — compile-is-contact only.

  Demonstration that the shipped freshness normal form is an INSTANCE of the abstract
  2.0-candidate theorem (`Witnessed/AbstractNormalization.lean`). This file changes
  nothing on the public surface; it shows the abstraction subsumes the model case before
  any refactor of the shipped `Normalization.lean` is ratified.

  The custody/promotion step (NOT done here): rewrite `bridge_path_normal_form`'s proof to
  go through `normal_form_iff_of_commutes`, add `AbstractNormalization` to the Witnessed
  aggregator + footprint gate. That touches the public WDC surface, so it waits for go.
-/

import LeanProofs.Witnessed.Normalization
import LeanProofs.Witnessed.AbstractNormalization

namespace LeanProofs.Scratch.AbstractNormalizationInstance

open LeanProofs.Witnessed.NoFreeLift
open LeanProofs.Witnessed.Normalization
open LeanProofs.Witnessed.AbstractNormalization

/-- The freshness model satisfies the abstract commutation hypothesis: `perm_weaken_carry`
    IS `Commutes CarryStep WeakenStep`. This is the whole content the abstraction needs from
    the model. -/
theorem commutes_carry_weaken : Commutes CarryStep WeakenStep := by
  intro a b c hw hc
  exact perm_weaken_carry hw hc

/-- The freshness normal form, derived end-to-end through the abstract 2.0 theorem — no
    freshness-specific `normalize`/`bubble` proof used, only the commutation instance. The
    shipped `bridge_path_normal_form` is this modulo cosmetic reshaping (`CChain ≅ Chain
    CarryStep`, and `PaidFrom Bridge`-on-Sum ≅ `PaidFrom (Step …)`-on-FreshClaim). -/
theorem fresh_normal_form_via_abstract {f h : FreshClaim} :
    PaidFrom (Step CarryStep WeakenStep) f h ↔
      ∃ z, Chain CarryStep f z ∧ Chain WeakenStep z h :=
  normal_form_iff_of_commutes commutes_carry_weaken

end LeanProofs.Scratch.AbstractNormalizationInstance
