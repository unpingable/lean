/-
  LeanProofs.Witnessed.Examples — gate-4 consumer specimen.

  Purpose: prove the Witnessed Derivation Calculus is usable from OUTSIDE the ported
  cone, through the canonical public surface only. This module imports nothing but the
  `LeanProofs.Witnessed` aggregator — no `experiments/`, no AG internals, no pre-rename
  names. If the promotion were "files moved but not actually a public API," this file
  would not compile.

  Mathlib-free (it consumes a Mathlib-free surface). Not part of the surface itself —
  it is a downstream witness that the surface exists and composes.
-/

import LeanProofs.Witnessed

namespace LeanProofs.Witnessed.Examples

open LeanProofs.Witnessed.NoFreeLift

/-! ### Genuine use: build a derivation and run the public theorems on it. -/

/-- An outside caller can instantiate the abstract calculus concretely:
    claims are `Nat`, the kernel admits `0`, each bridge step adds one. The derivation
    of claim `2` pays two bridge coordinates. -/
example : Lift (· = 0) (fun a b => b = a + 1) 2 :=
  Lift.cross (Lift.cross (Lift.base rfl) rfl) rfl

/-- `no_free_lift` is consumable on caller-supplied data: any lifted claim traces to a
    kernel claim through a chain of paid bridges. -/
example {Kernel : Nat → Prop} {Bridge : Nat → Nat → Prop} {c : Nat}
    (h : Lift Kernel Bridge c) : ∃ c₀, Kernel c₀ ∧ PaidFrom Bridge c₀ c :=
  no_free_lift h

/-- `paid_lift_sound` composes downstream: a sound kernel floor and valid bridges carry
    semantics across the whole derivation. Here exercised through a concrete `Sem`. -/
example {Kernel : Nat → Prop} {Bridge : Nat → Nat → Prop} {c : Nat}
    (hK : ∀ c, Kernel c → True) (hB : BridgeValid (fun _ => True) Bridge)
    (h : Lift Kernel Bridge c) : True :=
  paid_lift_sound hK hB h

/-! ### Name/contract receipts: every frozen v1.3 receipt resolves through the
    canonical surface, including the renamed `discipline_metatheory`
    (was `tightened_metatheory`). A `#check` that elaborates is proof the name and its
    type are exported. -/

#check @LeanProofs.Witnessed.NoFreeLift.paid_lift_sound
#check @LeanProofs.Witnessed.NoFreeLift.no_free_lift
#check @LeanProofs.Witnessed.NoFreeLift.BridgeValid
#check @LeanProofs.Witnessed.Derivation.derivation_extends_along_paid_path
#check @LeanProofs.Witnessed.Derivation.revoked_floor_derives_nothing
#check @LeanProofs.Witnessed.Normalization.bridge_path_normal_form
#check @LeanProofs.Witnessed.Discipline.cut_admissible_general
#check @LeanProofs.Witnessed.Discipline.discipline_metatheory
#check @LeanProofs.Witnessed.Discipline.WitnessedDiscipline
#check @LeanProofs.Witnessed.Embedding.embedded_lift_sound
#check @LeanProofs.Witnessed.AuthorityModel.AuthorityVerdict

end LeanProofs.Witnessed.Examples
