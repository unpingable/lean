# V16 public formal index

> **Read this if** you need the module map, the nearest named prior art for
> each element, or the complete non-claim ledger — this document is the
> authoritative list of what v16 does not establish.

v16 is **Governed Transition Boundaries**: a generic explicit-factorization
core and a bounded evidence surface. It is public under two registered
evidence targets. It changes no v15 stable root and adds no dependency to any
existing public module.

For the release statement and scope, start with the
[release overview](V16-RELEASE-OVERVIEW.md).

## Primary formal surfaces

| Module | Theorem surface | Public role in v16 |
| --- | --- | --- |
| `GovernedTransitionBoundaries` | `GENERIC-CORE-AGGREGATE` | Root of the generic core. |
| `GovernedTransitionBoundaries.Core` | `GENERIC-EXPLICIT-FACTORIZATION-CORE` | `ExplicitlyFactorsThrough`, `DerivedOnlyFrom`, and the four axiom-free core receipts. Imports only `ViewSemantics.Core`. |
| `GovernedTransitionBoundariesEvidence` | `BOUNDED-EVIDENCE-AGGREGATE` | Root of the bounded evidence surface. |
| `…Evidence.FiniteRepresentation` | `DECLARED-FINITE-COORDINATE-DETERMINACY` | The declared seven-coordinate language, 1,024 sources, 128 selections, and the least-selection results. |
| `…Evidence.JurisdictionBoundary` | `FIXED-POLICY-AUTHORIZATION-REFUSAL-WITNESS` | Computationally sufficient product against a fixed grant-list policy. |
| `…Evidence.ContextBoundary` | `SELECTED-CONTEXT-VALIDATION-WITNESS` | One issued observation record across exactly two use contexts. |
| `…Evidence.RealizabilityBoundary` | `BOUNDED-CAPACITY-REALIZABILITY-WITNESS` | Budget-two fixture; local support records against an uninhabited three-event execution type. |
| `…Evidence.HistoricalBoundary` | `OCCURRENCE-LINK-OBSERVATION-WITNESS` | Two worlds, same present-state view, different occurrence-link Boolean. |
| `…Evidence.GroundingBoundary` | `MODELED-HIDDEN-RELATION-NONIDENTIFIABILITY-WITNESS` | Two worlds agreeing at the admitted acquisition interface. |
| `…Evidence.Qualification` | `SIGNATURE-AND-AXIOM-FOOTPRINT-GATE` | In-tree `#check`/`#print axioms` replay of all 29 receipts. |

Both roots build under the default target and are Mathlib-free.

## Exact scope

### Generic factorization

`ExplicitlyFactorsThrough view target` requires one total decoder correct for
every source. The four receipts are: composition of explicit factorizations;
implication of the public `ViewSemantics.Determines` fibre-constancy relation;
blocking by a target-distinguishing collision; and non-restoration by a
carrier that is deterministic postprocessing of an insufficient view.

The converse is not claimed. For arbitrary types, fibre constancy does not
construct representatives of reachable view fibres or values for unreachable
view outputs. Independent enrichment of a carrier — anything not derived
solely from the coarse view — lies outside the non-restoration theorem's
`DerivedOnlyFrom` hypothesis.

### Declared finite representation

An exhaustive functional-dependency and attribute-selection calculation in one
declared seven-coordinate language:

- the declared source list has length 1,024 and covers every `AnalysisCase`;
  no source-list `Nodup` theorem is claimed;
- the coordinate language contains 128 duplicate-free selections;
- `internalMinimum` is the unique least coordinate selection determining the
  selected five-component `internalTarget` in the declared
  `AtlasSelection.Includes` order;
- exactly two masks in the declared enumeration determine that target, with
  membership, count, and duplicate freedom proved;
- the declared internal carrier explicitly factors the five-target result; and
- no declared selection factors the modeled hidden relation or the combined
  six-target result.

The result is relative to the declared table and coordinate language. It is
not statistical sufficiency, arbitrary-carrier minimality, or a canonical
global semantics, and it establishes no target-independent least
representation.

### Five bounded witnesses

Each witness is one fixture. The fixture bounds the claim.

- **Fixed-policy authorization refusal.** One fixed information product
  computes its selected target while one fixed native grant-list policy
  refuses both inspection and reliance. Not a general authorization theory.
- **Selected-context validation.** One fixed issued observation record does
  not explicitly factor the selected validation target across exactly two use
  contexts. The constructors carry no temporal or prefix order. Not a temporal
  calculus, expiration theorem, revocation theorem, or certificate-lifecycle
  result.
- **Bounded capacity realizability.** In the fixed budget-two fixture,
  proof-carrying support records for each named pair revalidate at the empty
  prefix while the selected three-event execution type is uninhabited. Not
  general amalgamation, CSP consistency, schedulability, or an
  information-loss claim.
- **Occurrence-link observation.** Two modeled worlds have the same selected
  present-state view and different values of one occurrence-link Boolean.
  Endpoint/history separation only — not causality, proof that an event
  occurred, general historical attribution, or a hyperproperty theorem.
- **Modeled hidden-relation nonidentifiability.** Two modeled worlds agree at
  the admitted acquisition interface and differ on one hidden-relation
  Boolean; deterministic postprocessing of that interface cannot restore a
  uniform decoder. Not physical truth, attestation correctness,
  authentication, a trusted-root theorem, or causal identification.

### Transition-relative computation

Some named targets factor through source views carrying transition or history
context even when they do not factor through a selected coarser projection.
"Transition-relative computation" is a bounded program label; the formal
generic core is target-relative functional factorization through selected
source views. It defines no operational semantics and does not claim that all
computation is transition-relative.

## Receipt and axiom accounting

29 gated receipts, replayed by
`scripts/check-governed-transition-boundaries-footprint.sh`:

| Root | Receipts | Axiom-free | `[propext]` | `[propext, Quot.sound]` |
| --- | ---: | ---: | ---: | ---: |
| core | 4 | 4 | 0 | 0 |
| evidence | 25 | 12 | 7 | 6 |
| **Total** | **29** | **16** | **7** | **6** |

Zero `[Classical.choice]`, zero `sorryAx`; both are fail-closed conditions in
the gate. The 29 receipts are the named public surface; the modules carry 21
further supporting lemmas that are not individually pinned.

## Prior-art anchors

The claim is stated as a delta against named established structures, not as an
unanchored result. No novelty or priority is claimed.

| Element | Nearest established structure |
| --- | --- |
| Generic factorization | View determinacy vs. rewriting in databases [1]; quotient and coequalizer factorization as narrower positive controls [2, 3] |
| Declared finite representation | Functional dependency and attribute selection [4, 5]; decision-table/reduct analysis [6] |
| Fixed-policy authorization refusal | Protection-of-information separation [7]; attribute-based and usage control [8, 9]; certificate profiles [10] |
| Selected-context validation | Dynamic authorization and certificate validation [8–10] |
| Bounded capacity realizability | Local consistency vs. global solution in constraint networks [11, 12] |
| Occurrence-link observation | Trace semantics [13]; history variables and refinement mappings [14] |
| Hidden-relation nonidentifiability | Structural identifiability and data fusion [15]; remote attestation as the external trust boundary not modeled here [16, 17] |
| Transition-relative label | Structural operational semantics [18]; trace semantics [13] |

Full citations are in
[`V16-GOVERNED-TRANSITION-BOUNDARIES.md`](V16-GOVERNED-TRANSITION-BOUNDARIES.md#references).

## Explicitly unearned

v16 does not establish a new generic factorization theorem, Hennessy–Milner
characterization, statistical minimal sufficiency, general authorization
theory, temporal validity, general amalgamation, causal attribution,
attestation correctness, universal six-way independence, universal
transition-relative semantics, one canonical global carrier, a
target-independent least representation, arbitrary-carrier minimality,
whole-system or cross-surface composition, research-OS correctness, product
readiness, or external novelty or priority.

## Navigation

Previous:
[`V16-GOVERNED-TRANSITION-BOUNDARIES.md`](V16-GOVERNED-TRANSITION-BOUNDARIES.md)
— per-witness fences and references. Next:
[`V16-RELEASE-LEDGER.md`](V16-RELEASE-LEDGER.md) — release identity and frozen
accounting.
