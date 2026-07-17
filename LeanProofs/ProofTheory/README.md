# ProofTheory island

Custody: **PUBLIC-SHIPPED stable specimen/library**, with audit receipts in a
separate **PUBLIC-EVIDENCE** root. Mathlib-free (own `ProofTheory` `lean_lib`,
build-graph enforced — `lake build ProofTheory` cannot reach Mathlib).
Historically promoted out of `LeanProofs/Scratch/` on 2026-07-06; v13 records
the already-released theorem family under its honest terminal roles.

## Register fence (read this first)

> **This island is proof theory. It is not a governance kernel. It provides a
> referent / specimen / benchmark.**

"Admissible" here has its literal Gentzen meaning — a rule is admissible when
every sequent derivable *with* it is derivable *without* it. This is the
mathematical referent the repo's governance vocabulary borrows from (cut ≈
"intermediate claims can be eliminated when their discharge is real";
weakening ≈ "added context does not forge proof"; contraction ≈ "duplicated
assumptions do not multiply authority"). The rhyme is acknowledged; the
**composition is refused**: nothing here imports or exports `Tier` / `Verdict`
/ `cap`, no typeclass, no unifier. No governance kernel imports these modules,
and none may. Build coverage is **not** governance promotion.

## The three layers

```text
1. MembershipG3   — clean set-like proof-theory specimen;
                    structural rules absorbed by monotonicity
2. TextbookG3ip   — multiplicity-aware, erasing left rules, permutation
                    quotient explicit; contraction real, exchange admissible
3. Equivalence    — the bridge: the specimen corresponds to textbook
                    derivability (not merely cute)
```

## Theorem inventory

**MembershipG3 (Specimen.lean)** — single-succedent intuitionistic
`{atom, ⊥, ∧, ∨, →}`, contexts read by membership/subset, no primitive
structural rules:

| Name | What | Axioms |
|---|---|---|
| `monotone` | Γ ⊆ Δ → Deriv Γ C → Deriv Δ C | none |
| `weaken` / `contract` / `exchange` | corollaries of monotone, size-preserving | none |
| `weakenAppend` / `size_monotone` | append form / exact size preservation | propext |
| `initGen` | general identity from atomic init | none |
| `explode` | ex falso as a transformer | propext, Quot.sound |
| `cut` | **computable cut-free transformer** (deg-primary, size-secondary) | propext, Quot.sound |
| `cutAppend` / `mp` | split-context cut / modus ponens | propext, Quot.sound |
| `consistency` | ⊬ ⊥ at empty context | none |
| `disjunction_property` | ⊢ A∨B ⇒ ⊢A or ⊢B | none |

**TextbookG3ip (TextbookG3ip.lean)** — multiset-faithful G3ip as
lists-quotiented-by-permutation, erasing left rules with
`Γ.Perm (principal :: Δ)` side-conditions (multiplicity real, contraction
NOT absorbed):

| Name | What | Axioms |
|---|---|---|
| `exchangeT` / `sizeT_exchangeT` | exchange admissible, size-preserving | propext |
| `invAnd` / `invOr` / `invImp` | inversion package, size-nonincreasing (subtype-carried bounds) | propext, Quot.sound |
| `ctrInner` / `contractT` | **contraction admissible**, size-nonincreasing, strong induction on size | propext, Quot.sound |
| `consistencyT` | ⊬ ⊥ (textbook side) | propext |
| `disjunction_propertyT` | disjunction property (textbook side) | propext, Quot.sound |

**Equivalence + transport (TextbookG3ip.lean):**

| Name | What | Axioms |
|---|---|---|
| `toDeriv` | textbook → specimen (cheap direction) | propext |
| `toDerivT` | specimen → textbook (pays the contraction bill) | propext, Quot.sound |
| `textbook_iff_membership` | derivability equivalence | propext, Quot.sound |
| `cutT` / `weakenT` / `initGenT` | cut / weakening / identity for textbook G3ip, transported | propext, Quot.sound |

## Footprint claim (honest phrasing)

**Zero user axiom declarations. Everything ≤ {propext, Quot.sound}. Zero
`Classical.choice` — the whole two-calculus development is constructive.**
This is NOT "zero axioms" in the absolute kernel sense: `#print axioms cut`
shows `propext` and `Quot.sound` (the standard core cost of well-founded
recursion). Several names depend on no axioms at all (`monotone`, `weaken`,
`contract`, `exchange`, `initGen`, `consistency`, `disjunction_property`).
Receipts print when the separate evidence target is built:
`lake build ProofTheoryEvidence`.

## Non-claims

- Not a governance kernel; not a doctrine unifier.
- Not Mathlib `Multiset`-typed (List + Perm *is* the multiset with its
  quotient explicit; the island is deliberately Mathlib-free).
- Not height-preserving cut (only the structural rules are size-preserving —
  standard).
- Not proof search; not runtime enforcement; no semantics/completeness.

## Verdict currency

`grep` + `lake build` + `#print axioms`. Never narrative. See `SCARS.md` for
the two core-library constructivity footguns this island caught.
