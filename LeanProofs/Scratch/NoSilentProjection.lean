/-
  Custody-Class: SCRATCH

  NoSilentProjection — scratch kernel (anti-laundering candidate).

  Status: scratch / candidate, 2026-06-05. Not imported by
  `LeanProofs.lean`. Not part of any 1.0 surface. No paper anchor.
  No promotion path. NOT used as discharge for any doctrine.

  Custody: scratch-checked (this file). Drawn from three already-named
  shapes in `~/git/papers/working/bridge-obligation-lattice.md`:
    NoSilentDelegation   ({non-amplification, type-fidelity})
    NoSilentException    ({temporal-bounding, anti-precedent})
    NoSilentProjection   ({non-amplification, type-fidelity, freshness})
  This file checks Projection against Lift and, using the same resident
  obligation table, checks both directions between Deform and Exception.
  The theorem-only additions avoid parallel modules while allowing the
  formal obligation distinctions to lead later code work.

  Filing category (per the doctrine map's Lean filing discipline):
    Fenced scratch proof-of-encodability. Pays its rent by forcing the
    obligation lattice into a typed-Lean shape where the negative
    theorem stack is type-level checkable. NOT category-1
    (public/promoted).

  Design — avoiding the tautology trap:
    Atoms, the family `carries` relation, and the `Converts` relation
    are defined independently. `demands` aliases `carries` per the
    doctrine's obligation-set convention (a family's obligation set is
    what it owes AND what it asks for); the two readings are kept named
    separately to keep theorems directionally legible.

    `CanDischarge` is an inductive with exactly two constructors:
    `direct` (the family carries the atom) and `viaConversion` (the
    family carries some atom `a'` and a `Converts source target a' a`
    witness exists). The `Converts` relation is family-scoped (per the
    doctrine's bridge-family × atom-demand grid) and empty by default;
    silent conversion would require extending `Converts` with an
    explicit constructor declaring the relevant cross-family rule, NOT
    merely declaring it as an axiom. (An axiom inhabiting a `def := False`
    or an empty inductive can leave existing case-analysis proofs
    apparently green while making the system inconsistent invisibly —
    that is the verdict-compression trap. The keystone proof is
    sensitive to *constructor* additions to `Converts`, not to axiom
    inhabitants.) See §Falsifiability witness at the end of this file
    for the strip-and-restore test that demonstrates this.

  Atom spellings adopt the kebab-case identifiers from
  `bridge-obligation-lattice.md` verbatim via Lean's escaped-identifier
  syntax (`«...»`). Changing them requires updating the doctrine file
  first. Doctrine spellings:
    non-amplification, temporal-bounding, type-fidelity,
    freshness, anti-precedent.

  Family obligation sets (from doctrine):
    Deform      : {temporal-bounding, type-fidelity}
    Exception   : {temporal-bounding, anti-precedent}
    Projection  : {non-amplification, type-fidelity, freshness}
    Lift        : {type-fidelity}
-/

namespace Admissibility.Scratch.NoSilentProjection

/-- The five obligation atoms. Spellings adopt the kebab-case
    identifiers from `working/bridge-obligation-lattice.md` verbatim. -/
inductive Atom : Type where
  | «non-amplification»
  | «temporal-bounding»
  | «type-fidelity»
  | freshness
  | «anti-precedent»
  deriving DecidableEq, Repr

open Atom

/-- The four bridge families. -/
inductive Family : Type where
  | Deform
  | Exception
  | Projection
  | Lift
  deriving DecidableEq, Repr

open Family

/-- Per-family obligation set as a Bool-valued predicate. The set is
    what each family carries AND what any bridge claiming to discharge
    it must provide. The two readings (carries / demands) are
    definitionally identified below.

    The table is the full 4 × 5 = 20 cells with NO wildcard. Wildcards
    would silently default new atoms or families to "carried by nobody
    / demanded by nobody" — exactly the class of silent remainder this
    kernel exists to refuse. Adding a sixth atom or fifth family will
    fail Lean's exhaustiveness check and force this table to be
    revisited explicitly. -/
def carriesB : Family → Atom → Bool
  -- Deform: {temporal-bounding, type-fidelity}
  | Deform,     «non-amplification» => false
  | Deform,     «temporal-bounding» => true
  | Deform,     «type-fidelity»     => true
  | Deform,     freshness           => false
  | Deform,     «anti-precedent»    => false
  -- Exception: {temporal-bounding, anti-precedent}
  | Exception,  «non-amplification» => false
  | Exception,  «temporal-bounding» => true
  | Exception,  «type-fidelity»     => false
  | Exception,  freshness           => false
  | Exception,  «anti-precedent»    => true
  -- Projection: {non-amplification, type-fidelity, freshness}
  | Projection, «non-amplification» => true
  | Projection, «temporal-bounding» => false
  | Projection, «type-fidelity»     => true
  | Projection, freshness           => true
  | Projection, «anti-precedent»    => false
  -- Lift: {type-fidelity}
  | Lift,       «non-amplification» => false
  | Lift,       «temporal-bounding» => false
  | Lift,       «type-fidelity»     => true
  | Lift,       freshness           => false
  | Lift,       «anti-precedent»    => false

/-- Family `f` carries atom `a`. -/
def carries (f : Family) (a : Atom) : Prop := carriesB f a = true

/-- Family `f` demands atom `a` of any bridge that would discharge it.
    Definitionally equal to `carries` per the doctrine: a family's
    obligation set is what it owes AND what it asks for. The naming
    split keeps the directional reading legible in theorems below. -/
def demands : Family → Atom → Prop := carries

/-- Family-scoped conversion rule. `Converts source target a' a`
    declares that, when discharging target family `target`'s demand for
    atom `a`, source family `source` may use atom `a'` instead — i.e.,
    carrying `a'` is permitted to stand in for carrying `a` *for that
    specific bridge pair*. Family-scoping is the doctrine's bridge-
    family × atom-demand grid made literal: a rule justified for one
    `(source, target)` pair does not silently leak into another pair.
    Atom-level conversion would be its own laundering channel in a lab
    coat.

    INTENTIONALLY EMPTY (no constructors) in this scratch kernel — the
    kernel refuses silent conversion across any family pair. Any cross-
    family rule must be declared by *extending this inductive with a
    new constructor* (and re-justified at the doctrine layer first).
    Case analysis on a `Converts s t a' a` hypothesis is sensitive to
    the constructor set, so adding even one constructor forces every
    downstream negative theorem that crosses the affected
    `(s, t, a', a)` quadruple to handle a new case it cannot discharge. -/
inductive Converts : Family → Family → Atom → Atom → Prop

/-- `CanDischarge source target a` holds when `source` can discharge
    `target`'s demand for atom `a`, either by carrying `a` directly
    (target irrelevant in this case) or by carrying some atom `a'`
    together with a family-scoped conversion `Converts source target
    a' a`. The two constructors are the only ways to inhabit the
    relation; with `Converts` empty, `viaConversion` is uninhabited and
    the relation collapses to `carries source a`. -/
inductive CanDischarge : Family → Family → Atom → Prop where
  | direct {source target : Family} {a : Atom}
      (h : carries source a) : CanDischarge source target a
  | viaConversion {source target : Family} {a' a : Atom}
      (hc : carries source a')
      (hv : Converts source target a' a) : CanDischarge source target a

/-- Family `source` discharges family `target` iff it can discharge
    every atom in `target`'s demand set, scoped to the `(source, target)`
    pair. -/
def FamilyDischarges (source target : Family) : Prop :=
  ∀ a : Atom, demands target a → CanDischarge source target a

/-! ## Negative theorem stack — Lift cannot silently discharge Projection

    `Lift` carries `{type-fidelity}`. `Projection` demands
    `{non-amplification, type-fidelity, freshness}`. Two demanded atoms
    (`non-amplification` and `freshness`) are neither carried by `Lift`
    nor reachable by conversion (the conversion relation is empty).
    Therefore `Lift` cannot family-discharge `Projection`. -/

/-- `Lift` does not carry `freshness`. -/
theorem lift_does_not_carry_freshness : ¬ carries Lift freshness := by
  intro h
  exact Bool.noConfusion h

/-- `Lift` does not carry `non-amplification`. -/
theorem lift_does_not_carry_non_amplification :
    ¬ carries Lift «non-amplification» := by
  intro h
  exact Bool.noConfusion h

/-- `Lift` cannot discharge `Projection`'s demand for `freshness` —
    neither by carrying it (Lift doesn't) nor by a `Lift → Projection`
    conversion (since `Converts` is empty for that family pair). -/
theorem lift_cannot_discharge_projection_freshness :
    ¬ CanDischarge Lift Projection freshness := by
  intro h
  cases h with
  | direct hc        => exact lift_does_not_carry_freshness hc
  | viaConversion _ hv => cases hv

/-- `Lift` cannot discharge `Projection`'s demand for `non-amplification`. -/
theorem lift_cannot_discharge_projection_non_amplification :
    ¬ CanDischarge Lift Projection «non-amplification» := by
  intro h
  cases h with
  | direct hc        => exact lift_does_not_carry_non_amplification hc
  | viaConversion _ hv => cases hv

/-- Helper: `Projection` demands `freshness`. -/
theorem projection_demands_freshness : demands Projection freshness := by
  show carriesB Projection freshness = true
  rfl

/-- **Keystone negative theorem.** `Lift` cannot family-discharge
    `Projection`. The witness is `freshness`: it is in `Projection`'s
    demand set but `Lift` cannot discharge it. -/
theorem lift_does_not_silently_discharge_projection :
    ¬ FamilyDischarges Lift Projection := by
  intro h
  exact lift_cannot_discharge_projection_freshness
    (h freshness projection_demands_freshness)

/-! ## Paired Exception / Deform separation

    The two families share `temporal-bounding`, but neither discharges the
    other. Deform lacks Exception's `anti-precedent`; Exception lacks Deform's
    `type-fidelity`. Keeping both directions prevents a shared atom from being
    mistaken for family equivalence. -/

theorem deform_does_not_carry_anti_precedent :
    ¬ carries Deform «anti-precedent» := by
  intro h
  exact Bool.noConfusion h

theorem deform_cannot_discharge_exception_anti_precedent :
    ¬ CanDischarge Deform Exception «anti-precedent» := by
  intro h
  cases h with
  | direct hc => exact deform_does_not_carry_anti_precedent hc
  | viaConversion _ conversion => cases conversion

theorem exception_demands_anti_precedent :
    demands Exception «anti-precedent» := by
  rfl

/-- A Deform bridge cannot silently stand in for an Exception bridge. -/
theorem deform_does_not_silently_discharge_exception :
    ¬ FamilyDischarges Deform Exception := by
  intro h
  exact deform_cannot_discharge_exception_anti_precedent
    (h «anti-precedent» exception_demands_anti_precedent)

theorem exception_does_not_carry_type_fidelity :
    ¬ carries Exception «type-fidelity» := by
  intro h
  exact Bool.noConfusion h

theorem exception_cannot_discharge_deform_type_fidelity :
    ¬ CanDischarge Exception Deform «type-fidelity» := by
  intro h
  cases h with
  | direct hc => exact exception_does_not_carry_type_fidelity hc
  | viaConversion _ conversion => cases conversion

theorem deform_demands_type_fidelity :
    demands Deform «type-fidelity» := by
  rfl

/-- An Exception bridge cannot silently stand in for a Deform bridge. -/
theorem exception_does_not_silently_discharge_deform :
    ¬ FamilyDischarges Exception Deform := by
  intro h
  exact exception_cannot_discharge_deform_type_fidelity
    (h «type-fidelity» deform_demands_type_fidelity)

/-! ## Falsifiability witness — strip-and-restore log

    The kernel's load-bearing claim is that the keystone negative
    theorem actually depends on the absence of silent conversion across
    the relevant family pair — that the theorem is not a tautology of
    its own definitions. To witness this, the empty
    `inductive Converts` was temporarily extended 2026-06-05 with the
    *two* constructors needed to fully refute the theorem (not just one
    constructor, which would only break the current proof path while
    leaving the proposition still true via the other missing atom):

    ```lean
    inductive Converts : Family → Family → Atom → Atom → Prop where
      | silent_freshness :
          Converts Lift Projection «type-fidelity» freshness
      | silent_non_amp :
          Converts Lift Projection «type-fidelity» «non-amplification»
    ```

    With both constructors, `Lift` can construct a `CanDischarge Lift
    Projection a` witness for every atom in `Projection`'s demand set
    `{non-amplification, type-fidelity, freshness}`:

    ```text
    type-fidelity       direct (Lift carries it)
    freshness           viaConversion (carries type-fidelity, silent_freshness)
    non-amplification   viaConversion (carries type-fidelity, silent_non_amp)
    ```

    So `FamilyDischarges Lift Projection` is inhabitable, hence
    `¬ FamilyDischarges Lift Projection` is *refutable*, not merely
    proof-broken. Both supporting lemmas fail to prove, with verbatim
    output from `lake build LeanProofs.Scratch.NoSilentProjection`:

    ```text
    error: LeanProofs/Scratch/NoSilentProjection.lean:208:23: unsolved goals
    case viaConversion.silent_freshness
    hc✝ : carries Lift «type-fidelity»
    ⊢ False
    error: LeanProofs/Scratch/NoSilentProjection.lean:216:23: unsolved goals
    case viaConversion.silent_non_amp
    hc✝ : carries Lift «type-fidelity»
    ⊢ False
    ```

    Both constructors were removed and the file restored to its current
    form. `lake build LeanProofs.Scratch.NoSilentProjection` re-run
    confirmed green.

    Interpretation: the keystone negative theorem actually depends on
    the absence of *both* `Lift → Projection` laundering rules. One
    declared rule would break the current proof path while leaving the
    proposition itself still true (via the other missing atom — this
    would be *proof-witness* falsifiability only); two declared rules
    refute the proposition itself.

    Family-scoping matters: under the previous atom-only `Converts :
    Atom → Atom → Prop` signature, a `silent_freshness` rule for one
    bridge pair would silently apply to *every* bridge pair where the
    source carried `type-fidelity`. The family-scoped signature confines
    each declared rule to the specific `(source, target)` pair it was
    justified for.

    The same constructor-sensitivity applies to the paired Exception / Deform
    results above: a declared Deform→Exception conversion to
    `anti-precedent`, or an Exception→Deform conversion to `type-fidelity`,
    would refute the corresponding theorem. -/

end Admissibility.Scratch.NoSilentProjection
