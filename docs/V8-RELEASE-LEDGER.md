# v8 Release Ledger — Sequent Admissibility Island

> **Historical record.** The candidate label below describes the v8 release
> tree. v13 records the unchanged ProofTheory theorem root as stable and its
> axiom-print audit as public evidence. See
> [`V13-RELEASE-LEDGER.md`](V13-RELEASE-LEDGER.md).

**Release: v8.0.0 — Sequent Admissibility Island** (*A Mathlib-free
proof-theory specimen/library release*). Umbrella: proof-theoretic referent
for the admissibility vocabulary. Prior release: v7.0.0 — Artifact Authority
Profiles.

**Status: PREPPED, awaits operator mint.** All version strings bumped, docs
written, gates re-run green (2026-07-06). At this receipt point, the separate
tag, GitHub-release, and Zenodo-deposit acts remained operator steps and had
not been performed by tooling.

**Why a new major, not folded into v7:** v7 is semantically occupied by
Artifact Authority Profiles (README + `docs/V7-RELEASE-LEDGER.md`, tagged
`v7.0.0`, Zenodo-deposited 2026-07-02). The ProofTheory island is a different
kind of object — literal proof theory, two calculi, an equivalence bridge —
not an increment of the authority-profiles campaign. On this repo's release
constitution ("major proof campaign landed," not library-API semver), a new
proof island is an integer.

**The v8 claim (scoped, exact):** *a single-succedent intuitionistic sequent
calculus in which no structural rule is primitive and all four —
weakening, contraction, exchange, cut — are admissible; and a
multiplicity-faithful textbook presentation proved derivability-equivalent to
it.* In full:

- **MembershipG3 (`Specimen.lean`)** — `{atom, ⊥, ∧, ∨, →}`, single
  succedent, contexts read by membership/subset, NO primitive structural
  rules. One `monotone` theorem (Γ ⊆ Δ) subsumes weakening, contraction, and
  exchange, size-preserving exactly (`size_monotone`). General identity is
  derivable from atomic `init` (`initGen`). `cut` is a **computable cut-free
  transformer** — primary induction on cut-formula degree, secondary on the
  sum of derivation sizes — not an existence claim. Payoffs
  `consistency` and `disjunction_property` fall out as case analyses because
  the system is cut-free by construction (`cut` is a def, so every
  derivation, even one built via `cut`, is cut-free data).
- **TextbookG3ip (`TextbookG3ip.lean`)** — multiset-faithful G3ip rendered as
  lists-quotiented-by-permutation: erasing left rules carry
  `Γ.Perm (principal :: Δ)` side-conditions and consume the principal, so
  multiplicity is real and contraction is NOT absorbed (`impLT` keeps its
  principal in the left premise, per the textbook rule). Exchange is
  admissible and size-preserving (`exchangeT`). The size-nonincreasing
  inversion package (`invAnd`/`invOr`/`invImp`, bounds carried in subtype
  returns) funds **admissible contraction** (`contractT`, strong induction
  on size).
- **Equivalence** — `toDeriv` (textbook → specimen) and `toDerivT` (specimen
  → textbook, which pays the contraction bill — a set→multiset embedding
  *implies* contraction admissibility, no dodge), giving
  `textbook_iff_membership`. Cut, weakening, and general identity for the
  textbook calculus then transport as one-line corollaries (`cutT`,
  `weakenT`, `initGenT`). This DISCHARGES the specimen's original
  `cannot_testify (a)` — "syntactic identity with textbook G3ip unproved" —
  at derivability level.
- **Audit (`Audit.lean`)** — `#print axioms` receipts for every load-bearing
  name, printed on every `lake build ProofTheory`. Footprint drift becomes
  CI-visible, not narrative.

**The v8 non-claims (binding on release notes):**
- **Not a governance kernel, not a doctrine unifier.** "Admissible" is literal
  Gentzen admissibility — the referent the governance vocabulary borrows, not
  a component of it. No `Tier`/`Verdict`/`cap` import or export, no typeclass,
  no unifier. Build coverage is NOT governance promotion; Custody-Class stays
  UNRATIFIED-CANDIDATE.
- **Not Mathlib `Multiset`-typed.** The island is deliberately Mathlib-free;
  `List` + `List.Perm` IS the multiset with its quotient made explicit. A
  Mathlib-Multiset rendition is a possible future rung, not this release.
- **Not height-preserving cut** (only the structural rules are
  size-preserving — standard); **no proof search**; **no semantics /
  completeness**; **no runtime enforcement**.

**Axiom footprint (measured, `Audit.lean`, 2026-07-06):** zero user axiom
declarations; everything ≤ `{propext, Quot.sound}`; **zero
`Classical.choice`** (fully constructive); `monotone` / `weaken` / `contract`
/ `exchange` / `initGen` / `consistency` / `disjunction_property` depend on no
axioms at all.

**Two constructivity scars caught in-release** (`LeanProofs/ProofTheory/SCARS.md`):
core `List.perm_cons_erase` is proved classically (would inject
`Classical.choice` downstream — replaced by a local `permConsErase`); and
`omega` on a **conjunction goal** emits a choice-dependent proof (split to
`exact ⟨by omega, by omega⟩`). Both compile green and look innocent; the
`#print axioms` harness caught both.

**Gate log (2026-07-06):** `lake build` green (8380 jobs); `lake build
ProofTheory` green; no `sorry`/`admit`/`unsafe`/`axiom` declarations under
`LeanProofs/ProofTheory/`; `scripts/audit-axioms.sh` PASS;
`scripts/check-custody-classes.sh` PASS. Island commit `445b175` on `main`;
release-prep commit follows.

**Provenance:** operator-supplied 2026-07-06, downstream of an external
ChatGPT design autopsy that located the correct encoding (derivations as data,
membership rules, explicit size measure, infrastructure lemmas before cut)
but had no compiler; the kernel-checked landing and the textbook equivalence
were done here the same day.
