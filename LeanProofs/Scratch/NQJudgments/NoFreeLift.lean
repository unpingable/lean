/-
  NQJudgments.NoFreeLift — the no-free-lift properties, in NQ's register.

  Custody-Class: SCRATCH. SNAPSHOT (NQ state as-inspected 2026-06-18); discharges no
  NQ runtime; not imported by `LeanProofs.lean`. See `NQJudgments-SNAPSHOT-NOTE.md`.
  The (a)/(b)/(d) laws and the two embodied laws below are all AXIOM-FREE.

  Each theorem names the NQ behavior it models:

    (a) testimony ⊬ authority        — can_testify does not grant may_bind.
    (b) admissibility ⊬ authority     — admissible_with_scope does not grant may_bind
                                        ("NQ may NOT mint spendability").
    (d) refused ancestor blocks binding unless an explicit bridge exists
                                        — suppressed_by_ancestor propagation, with the
                                        operator-declaration override as the bridge.
    plus the two laws NQ already embodies in Rust:
      Finding ⊬ Witness(Finding)      — no self-authorization.
      MissingBridge ⟹ Refusal         — refuses rather than fabricates.

  (Property (c), green-check ⊬ new-public-promise, lives in `Standing.lean`.)
-/

import LeanProofs.Scratch.NQJudgments.Basic

namespace NQJudgments

/-! ## (a) testimony ⊬ authority -/

/-- **testimony_not_authority** — a witness can testify (coverage, fresh,
    non-contradictory) yet hold no binding authority: without an operator directive,
    `CanTestify` does not give `MayBind`. -/
theorem testimony_not_authority : ∃ c, CanTestify c ∧ ¬ MayBind c :=
  ⟨⟨true, true, false, false, true, false, false, false, false⟩, by decide⟩

/-! ## (b) admissibility ⊬ authority — NQ may NOT mint spendability -/

/-- **admissibility_not_authority** — a fully admissible-with-scope claim still does
    NOT grant authority. Admitting testimony is not minting a lease. -/
theorem admissibility_not_authority : ∃ c, AdmissibleWithScope c ∧ ¬ MayBind c :=
  ⟨⟨true, true, false, false, true, false, false, false, false⟩, by decide⟩

/-- The same fact as a universal law: binding is impossible without the external
    directive — the authority must come from outside NQ's testimony. -/
theorem binding_requires_external_directive {c : Claim}
    (h : MayBind c) : c.operatorDirective = true := h.2

/-! ## Embodied law: Finding ⊬ Witness(Finding) — no self-authorization -/

/-- **no_self_authorization** — an admissible claim does not authorize itself. The
    binding directive is never derivable from the claim's own testimony; a finding
    may not become the witness that authorized itself. (Universal form of (b).) -/
theorem no_self_authorization {c : Claim}
    (hdir : c.operatorDirective = false) : ¬ MayBind c := by
  rintro ⟨_, h⟩
  exact Bool.noConfusion (h.symm.trans hdir)

/-! ## (d) refused/cannot_testify ancestor blocks binding unless an explicit bridge -/

/-- **refused_ancestor_blocks_binding** — a refused-ancestor claim with NO bridge is
    not admissible, hence cannot bind. Ancestor loss propagates down and blocks the
    descendant; suppression is not clearance. -/
theorem refused_ancestor_blocks_binding {c : Claim}
    (h1 : c.refusedAncestor = true) (h2 : c.operatorAdmission = false) : ¬ MayBind c := by
  rintro ⟨⟨_, _, hstand⟩, _⟩
  rcases hstand with h | h
  · exact Bool.noConfusion (h1.symm.trans h)
  · exact Bool.noConfusion (h.symm.trans h2)

/-- **explicit_bridge_can_rebind** — WITH an explicit operator declaration
    (`operatorAdmission`) re-admitting the refused-ancestor claim, and an operator
    directive, binding becomes possible again. The bridge is the only crossing. -/
theorem explicit_bridge_can_rebind :
    ∃ c, c.refusedAncestor = true ∧ c.operatorAdmission = true ∧ MayBind c :=
  ⟨⟨true, true, false, true, true, true, true, false, false⟩, by decide⟩

/-- **missing_bridge_refuses_not_fabricates** — `MissingBridge ⟹ Refusal`: a refused
    ancestor with no bridge yields non-admission (a refusal), NOT a fabricated
    admission. NQ refuses rather than fakes. -/
theorem missing_bridge_refuses_not_fabricates {c : Claim}
    (h1 : c.refusedAncestor = true) (h2 : c.operatorAdmission = false) :
    ¬ AdmissibleWithScope c := by
  rintro ⟨_, _, hstand⟩
  rcases hstand with h | h
  · exact Bool.noConfusion (h1.symm.trans h)
  · exact Bool.noConfusion (h.symm.trans h2)

/-! ## The layered no-free-lift, assembled

    The three layers are strictly separated: testimony ⊆ admissibility's input, but
    neither testimony nor admissibility reaches authority without the external
    directive, and a refused ancestor severs the chain unless explicitly bridged. -/

/-- **layers_do_not_collapse** — one statement: admissible testimony exists that is
    not authority, and a refused ancestor without bridge is not even admissible. The
    two prohibited collapses (admissibility→authority, refusal→fabrication) both
    hold. -/
theorem layers_do_not_collapse :
    (∃ c, AdmissibleWithScope c ∧ ¬ MayBind c)
    ∧ (∀ c, c.refusedAncestor = true → c.operatorAdmission = false → ¬ AdmissibleWithScope c) :=
  ⟨admissibility_not_authority, fun _ => missing_bridge_refuses_not_fabricates⟩

end NQJudgments
