/-
  Admissibility — Retroactive Legitimation (scratch annex, specimen).

  Status: scratch annex, 2026-06-02. Not imported by `LeanProofs.lean`.
  Not part of any 1.0 surface. No README / PAPER-MAP promotion.

  Slice 1 of the substructural-sequent program (axis 3 of the
  historical maximal-calculus axis map — the unified calculus is the
  refused frame, not a target; see `papers/working/maximal-calculus-refused-map.md`
  and `papers/working/retroactive-legitimation-charter.md`). Working
  name **RetroactiveLegitimation**.

  Headline claim. A witness made valid only by the post-state of an
  operation may be true later, but cannot authorize the operation in
  the pre-state.

  Targets:
    T1  : pre-state valid witness authorizes; admissible transition
          inhabits when pre-state already carries the witness.
    T2  : `install W` produces a post-state in which `W` validates
          the operation (the witness is real later).
    T3  : empty pre-state authorizes no operation.
    T4  : retroactive install on `empty` is not an admissible
          transition, even though the post-state carries the witness.
    T5  : `PostValidated` does not imply `AuthorizedIn`
          (counterexample at `empty`).
    T5' : optional — `PostValidated` does not imply `Transition`.

  Design discipline (per the execution charter):

    - `AuthorizedIn` uses `ValidIn S`, never `ValidIn (apply S O)`.
      The post-state is never consulted by authorization.
    - `Transition` requires pre-state authorization, never post-state.
    - `PostValidated` is a separate predicate so the boundary is
      named — it exists precisely because it differs from
      `AuthorizedIn`.
    - List-backed state. No function-valued state, no `Multiset`,
      no `Finset`, no deduplication that would smuggle exchange or
      contraction (irrelevant to this slice but listed for
      consistency with sibling annexes).
    - No founding-event handling. No protocol / wait. No value
      mutation. No cut. No sequents.
    - No `sorry`, no `admit`, no `True`-shaped placeholders.

  Governor-neutral. Lean core only; no Mathlib, no sibling imports.
-/

namespace Admissibility.RetroactiveLegitimation

/-! ### Witnesses, operations, state -/

/-- Specimen witness type: a tagged `Nat`. The internal shape does
    not matter for the slice; the point is that witnesses are
    individuated and inhabit a `DecidableEq` type. -/
inductive Witness where
  | mk : Nat → Witness
  deriving DecidableEq, Repr

/-- Specimen operation: `install W` installs `W` as a valid witness
    for itself in the post-state. The single-constructor form makes
    the slice's content visible at the smallest specimen. -/
inductive Operation where
  | install : Witness → Operation
  deriving DecidableEq, Repr

/-- State carries a list of (operation, witness) pairs that the
    state currently endorses. List-backed by design — multiplicity
    is preserved (irrelevant here, consistent with siblings). -/
structure State where
  valid : List (Operation × Witness)
  deriving Repr

/-! ### The boundary's two judgments — same shape, different state -/

/-- `ValidIn S O W` says witness `W` is on record as valid for
    operation `O` in state `S`. Pure pre-state predicate when used
    with the pre-state; pure post-state predicate when used with the
    post-state. -/
def ValidIn (S : State) (O : Operation) (W : Witness) : Prop :=
  (O, W) ∈ S.valid

/-- `AuthorizedIn S O` says some witness valid in **state `S`**
    authorizes `O`. Read off `S`, NOT `apply S O`. This is the
    pre-state-anchored authorization predicate; the slice's whole
    point lives in the asymmetry between this and `PostValidated`
    below. -/
def AuthorizedIn (S : State) (O : Operation) : Prop :=
  ∃ W, ValidIn S O W

/-- The specimen's state transition. `install W` adds `(install W, W)`
    to the validity record. The post-state carries every endorsement
    the pre-state did, plus the new self-witness. -/
def apply (S : State) : Operation → State
  | Operation.install W =>
      { valid := (Operation.install W, W) :: S.valid }

/-- A transition `S → S'` via operation `O` is admissible iff:
    (i) `S'` is the operational successor `apply S O`; and
    (ii) `S` already authorizes `O` (pre-state, not post-state).

    Authorization is anchored at `S`. The post-state may contain
    new witnesses, but they do not retroactively license the act
    that produced them. -/
def Transition (S : State) (O : Operation) (S' : State) : Prop :=
  S' = apply S O ∧ AuthorizedIn S O

/-- `PostValidated S O` says some witness valid in the **post-state**
    endorses `O`. This is the *wrong* check for authorization: the
    operation may have installed the very witness that validates it.
    Surfacing this predicate separately is what lets the negative
    headline (T5) say "post-validation does not imply authorization"
    without redefining `AuthorizedIn`. -/
def PostValidated (S : State) (O : Operation) : Prop :=
  ∃ W, ValidIn (apply S O) O W

/-! ### Specimen states -/

/-- The empty state — no witnesses on record. -/
def empty : State := { valid := [] }

/-- The state carrying exactly one endorsement `(O, W)`. Used in
    T1's positive transition. -/
def withWitness (O : Operation) (W : Witness) : State :=
  { valid := [(O, W)] }

/-! ### T1 — positive pre-state authorization

  A pre-existing valid witness authorizes its operation, and a
  concrete admissible transition exists. The second half guards
  against the cheap "no operation is ever admissible" failure
  mode that T4 would otherwise vacuously satisfy.
-/

theorem pre_valid_witness_authorizes
    {S : State} {O : Operation} {W : Witness}
    (h : ValidIn S O W) : AuthorizedIn S O :=
  ⟨W, h⟩

theorem pre_authorized_transition (W : Witness) :
    Transition (withWitness (Operation.install W) W) (Operation.install W)
      (apply (withWitness (Operation.install W) W) (Operation.install W)) := by
  refine ⟨rfl, W, ?_⟩
  show (Operation.install W, W) ∈ (withWitness (Operation.install W) W).valid
  simp [withWitness]

/-! ### T2 — the post-state witness is real

  `install W` produces a post-state in which `W` validates the
  operation. This is the "true later" half of the boundary: we are
  not denying post-state truth.
-/

theorem install_witness_valid_after_apply (W : Witness) :
    ValidIn (apply empty (Operation.install W)) (Operation.install W) W := by
  show (Operation.install W, W) ∈ (apply empty (Operation.install W)).valid
  simp [apply, empty]

theorem post_validated_empty_install (W : Witness) :
    PostValidated empty (Operation.install W) :=
  ⟨W, install_witness_valid_after_apply W⟩

/-! ### T3 — empty pre-state authorizes nothing -/

theorem empty_not_authorized (O : Operation) : ¬ AuthorizedIn empty O := by
  intro h
  obtain ⟨W, hW⟩ := h
  -- hW : ValidIn empty O W = (O, W) ∈ empty.valid = (O, W) ∈ []
  simp [ValidIn, empty] at hW

/-! ### T4 — headline refusal

  The post-state contains a valid witness for `install W` (by T2),
  yet the transition is not admissible because the pre-state did
  not authorize it.

  The proof does not weaken the negative claim — `Transition` is
  refused; we are not refusing some surrogate that happens to fail.
-/

theorem retroactive_install_not_admissible (W : Witness) :
    ¬ Transition empty (Operation.install W) (apply empty (Operation.install W)) := by
  intro h
  exact empty_not_authorized _ h.2

/-! ### T5 — post-validation does not imply authorization

  Counterexample form: `empty` with `install (mk 0)` satisfies
  `PostValidated` (by T2) but not `AuthorizedIn` (by T3). The
  universal claim `PostValidated → AuthorizedIn` therefore fails.

  The negative is narrow on purpose: later evidence can support
  later judgments; it cannot serve as the missing precondition for
  its own enabling transition. (Cf. the charter at
  `papers/working/retroactive-legitimation-charter.md`.)
-/

theorem post_validation_does_not_imply_authorization :
    ¬ ∀ (S : State) (O : Operation), PostValidated S O → AuthorizedIn S O := by
  intro h
  have hpv : PostValidated empty (Operation.install (Witness.mk 0)) :=
    post_validated_empty_install (Witness.mk 0)
  have hauth : AuthorizedIn empty (Operation.install (Witness.mk 0)) :=
    h _ _ hpv
  exact empty_not_authorized _ hauth

/-! ### T5' — optional: post-validation does not imply admissible transition

  Same counterexample, stronger conclusion: post-validation does
  not even license the transition's existence. The proof factors
  through T4.
-/

theorem post_validation_does_not_imply_transition :
    ¬ ∀ (S : State) (O : Operation),
        PostValidated S O → Transition S O (apply S O) := by
  intro h
  have hpv : PostValidated empty (Operation.install (Witness.mk 0)) :=
    post_validated_empty_install (Witness.mk 0)
  have htrans : Transition empty (Operation.install (Witness.mk 0))
      (apply empty (Operation.install (Witness.mk 0))) := h _ _ hpv
  exact retroactive_install_not_admissible (Witness.mk 0) htrans

/-! ### Axiom checks -/

#print axioms pre_valid_witness_authorizes
#print axioms pre_authorized_transition
#print axioms install_witness_valid_after_apply
#print axioms post_validated_empty_install
#print axioms empty_not_authorized
#print axioms retroactive_install_not_admissible
#print axioms post_validation_does_not_imply_authorization
#print axioms post_validation_does_not_imply_transition

end Admissibility.RetroactiveLegitimation
