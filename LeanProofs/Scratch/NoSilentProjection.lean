/-
  NoSilentProjection — scratch kernel (anti-laundering candidate).

  Status: scratch / candidate, 2026-06-05. Not imported by
  `LeanProofs.lean`. Not part of any 1.0 surface. No paper anchor.
  No promotion path. NOT used as discharge for any doctrine.

  Custody: scratch-checked (this file). One of three already-named
  candidates in `~/git/papers/working/bridge-obligation-lattice.md`:
    NoSilentDelegation   ({non-amplification, type-fidelity})
    NoSilentException    ({temporal-bounding, anti-precedent})
    NoSilentProjection   ({non-amplification, type-fidelity, freshness})
  This file lifts the Projection family to Lean. The other two remain
  named-not-built per the doctrine file's "no candidate without a
  forcing case" rule. This one is built because Projection's obligation
  set strictly extends Lift's, giving the cleanest first negative
  theorem against an existing artifact (Lift carries only
  `type-fidelity`; Projection demands two atoms — `freshness` and
  `non-amplification` — that Lift does not).

  Filing category (per the doctrine map's Lean filing discipline):
    Fenced scratch proof-of-encodability. Pays its rent by forcing the
    obligation lattice into a typed-Lean shape where the negative
    theorem stack is type-level checkable. NOT category-1
    (public/promoted).

  Design — avoiding the tautology trap:
    Atoms, the family `carries` relation, the family `demands` relation,
    and the `Converts` relation are all defined independently of one
    another. `CanDischarge` is an inductive with exactly two
    constructors: `direct` (the family carries the atom) and
    `viaConversion` (the family carries some atom `a'` and a `Converts
    a' a` witness exists). The `Converts` relation is empty by default;
    silent conversion would require declaring some `Converts a b` axiom
    across the existing family boundaries. The keystone negative
    theorem falsifies under such an axiom — see the §Falsifiability
    witness block at the end of this file.

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
    definitionally identified below. -/
def carriesB : Family → Atom → Bool
  | Deform,     «temporal-bounding» => true
  | Deform,     «type-fidelity»     => true
  | Exception,  «temporal-bounding» => true
  | Exception,  «anti-precedent»    => true
  | Projection, «non-amplification» => true
  | Projection, «type-fidelity»     => true
  | Projection, freshness           => true
  | Lift,       «type-fidelity»     => true
  | _, _ => false

/-- Family `f` carries atom `a`. -/
def carries (f : Family) (a : Atom) : Prop := carriesB f a = true

/-- Family `f` demands atom `a` of any bridge that would discharge it.
    Definitionally equal to `carries` per the doctrine: a family's
    obligation set is what it owes AND what it asks for. The naming
    split keeps the directional reading legible in theorems below. -/
def demands : Family → Atom → Prop := carries

/-- Conversion relation between atoms. INTENTIONALLY EMPTY (no
    constructors) in this scratch kernel — the kernel refuses silent
    conversion across atom boundaries. Any cross-atom equivalence must
    be declared by *extending the inductive with a new constructor*
    (and re-justified at the doctrine layer first). The empty-inductive
    encoding is what makes the falsifiability test load-bearing: case
    analysis on a `Converts a' a` hypothesis is sensitive to the
    constructor set, so adding even one cross-atom constructor forces
    every downstream negative theorem that crosses it to handle a new
    case it cannot discharge. -/
inductive Converts : Atom → Atom → Prop

/-- Family `f` can discharge atom `a` either by carrying it directly or
    by carrying some atom convertible to it. The two constructors are
    the only ways to inhabit `CanDischarge`; with `Converts` empty,
    `viaConversion` is uninhabited and the relation collapses to
    `carries`. -/
inductive CanDischarge : Family → Atom → Prop where
  | direct {f : Family} {a : Atom} (h : carries f a) : CanDischarge f a
  | viaConversion {f : Family} {a' a : Atom}
      (hc : carries f a') (hv : Converts a' a) : CanDischarge f a

/-- Family `source` discharges family `target` iff it can discharge
    every atom in `target`'s demand set. -/
def FamilyDischarges (source target : Family) : Prop :=
  ∀ a : Atom, demands target a → CanDischarge source a

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

/-- `Lift` cannot discharge `freshness` — neither directly nor by
    conversion (since `Converts` is empty). -/
theorem lift_cannot_discharge_freshness :
    ¬ CanDischarge Lift freshness := by
  intro h
  cases h with
  | direct hc        => exact lift_does_not_carry_freshness hc
  | viaConversion _ hv => cases hv

/-- `Lift` cannot discharge `non-amplification` — neither directly nor
    by conversion. -/
theorem lift_cannot_discharge_non_amplification :
    ¬ CanDischarge Lift «non-amplification» := by
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
  exact lift_cannot_discharge_freshness
    (h freshness projection_demands_freshness)

/-! ## Falsifiability witness — strip-and-restore log

    The kernel's load-bearing claim is that the keystone negative
    theorem can fail if a silent conversion is declared. To witness
    this, the empty `inductive Converts` was temporarily extended
    2026-06-05 with a single cross-atom constructor:

    ```lean
    inductive Converts : Atom → Atom → Prop where
      | silent_freshness : Converts «type-fidelity» freshness
    ```

    Under that constructor, the `cases hv` tactic in the
    `viaConversion` branch of `lift_cannot_discharge_freshness` no
    longer produces zero goals. It produces one specialized case where
    `a'` is forced to `«type-fidelity»` (the constructor's domain) and
    `hc : carries Lift «type-fidelity»` is available — both consistent
    facts that leave the goal `False` undischargeable from the
    hypotheses.

    Observed failure (verbatim from `lake build LeanProofs.Scratch.
    NoSilentProjection` with the constructor present):

    ```text
    error: LeanProofs/Scratch/NoSilentProjection.lean:156:23:
      unsolved goals
    case viaConversion.silent_freshness
    hc✝ : carries Lift «type-fidelity»
    ⊢ False
    ```

    The constructor was removed and the file restored to its current
    form. `lake build LeanProofs.Scratch.NoSilentProjection` was re-run
    and confirmed green.

    Interpretation: the keystone negative theorem is not a tautology of
    its own definitions. It depends on `Converts` being constructorless
    over the relevant atom pairs. Declaring *one* cross-family
    conversion breaks the dependent negative theorem in the obligation
    atom that conversion targets — which is the desired falsifiability
    handle. The user's framing applies precisely: *"it can fail if you
    accidentally add a constructor that launders atoms."*

    The same pattern would falsify `NoSilentDelegation` (against
    `non-amplification` or `type-fidelity`) and `NoSilentException`
    (against `temporal-bounding` or `anti-precedent`) once those
    candidates are built. -/

end Admissibility.Scratch.NoSilentProjection
