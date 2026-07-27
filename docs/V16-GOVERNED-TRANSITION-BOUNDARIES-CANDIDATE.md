# Governed transition boundaries — V16 candidate

Candidate published 2026-07-26; not released and not V16 final.

## Thesis

The development combines standard explicit-factorization laws, a bounded
finite coordinate-determinacy result, and five separately scoped native
witnesses concerning authorization, selected-context validation, global route
existence, occurrence-link observation, and modeled hidden-relation
nonidentifiability.

In a declared finite source-and-coordinate language, an explicitly selected
target family has a unique least target-determining coordinate selection in
the declared `AtlasSelection.Includes` order, and the selected internal target
factors through a declared six-field carrier. More generally, if a view maps
two sources to the same value while the selected target distinguishes them,
no total decoder factors the target through that view, and no carrier derived
solely by deterministic postprocessing of the view restores that
factorization.

The generic statements are standard function-factorization and
view-determinacy facts. The finite result is an exhaustive functional-
dependency and attribute-selection calculation. The contribution is their
mechanically checked formal synthesis with the separately scoped native
witnesses below. No novelty or priority is claimed.

## Generic factorization

`ExplicitlyFactorsThrough view target` requires one total decoder that is
correct for every source. Such factorizations compose and imply the public
`LeanProofs.ViewSemantics.Determines` fibre-constancy relation.

The converse is not claimed. For arbitrary types, fibre constancy does not
construct representatives of reachable view fibres or values for unreachable
view outputs. Quotient or coequalizer settings and a surjective view equipped
with a section are positive controls only when their additional lifting data
is actually present.

A target-distinguishing collision blocks explicit factorization.
Consequently, if `coarse` does not explicitly factor `target`, deterministic
postprocessing derived solely from `coarse` cannot restore that factorization.
Independent enrichment is outside this theorem's candidate class.

This is a witnessed total-decoder formulation of standard function
factorization and view-determinacy facts. The closest database distinction is
between view determinacy and rewriting [1]; quotient and coequalizer
factorization are narrower positive controls [2, 3].

## Declared finite representation

The finite result is an exhaustive functional-dependency and attribute-
selection calculation in a declared seven-coordinate language:

- the declared source list has length 1,024 and covers every `AnalysisCase`;
  no source-list `Nodup` theorem is claimed;
- the coordinate language contains 128 duplicate-free selections;
- `internalMinimum` is the unique least coordinate selection determining the
  selected five-component `internalTarget` in the declared
  `AtlasSelection.Includes` order;
- exactly two masks in the declared enumeration determine that target, with
  membership, count, and duplicate freedom all proved;
- the declared internal carrier explicitly factors the five-target result;
  and
- no declared selection factors the modeled hidden relation or combined
  six-target result.

The finite comparison is functional dependency in a fixed table and declared
coordinate language [4, 5], with a close decision-table/reduct analogy [6].
It is not statistical sufficiency, arbitrary-carrier minimality, or a
canonical global semantics.

## Five bounded witnesses

### Fixed-policy authorization refusal

One fixed information product computes its selected target while one fixed
native grant-list policy refuses both inspection and reliance. This is a
fixed-policy authorization-refusal witness, not a general authorization
theory. Access-control and usage-control literature establish the broader
separation between available information and policy-relative authority
[7–10].

### Selected-context validation

One fixed issued observation record does not explicitly factor the selected
validation target across exactly two use contexts. The constructors do not
carry a temporal or prefix order. This is selected-context validation, not a
temporal calculus, expiration theorem, revocation theorem, or general
certificate-lifecycle result. Dynamic authorization and certificate
validation provide the surrounding motivation [8–10].

### Bounded capacity realizability

In the fixed budget-two fixture, proof-carrying support records for each named
pair revalidate at the empty prefix while the selected three-event execution
type is uninhabited. This is a bounded local-versus-global capacity witness,
not a general amalgamation theorem, CSP consistency theorem, schedulability
result, or information-loss claim. The broader local-consistency/global-
solution distinction is established in constraint-network work [11, 12].

### Occurrence-link observation

Two modeled worlds have the same selected present-state view and different
values of one occurrence-link Boolean. This is endpoint/history separation,
not causality, proof that an event occurred, general historical attribution,
or a hyperproperty theorem. Trace semantics and history-variable work provide
the surrounding distinction [13, 14].

### Modeled hidden-relation nonidentifiability

Two modeled worlds agree at the admitted acquisition interface and differ on
one hidden-relation Boolean. Deterministic postprocessing of that interface
cannot restore a uniform decoder for the hidden relation. This is modeled
hidden-relation nonidentifiability, not physical truth, attestation
correctness, authentication, a trusted-root theorem, or causal
identification. Structural identifiability supplies a close comparison [15];
remote-attestation sources delimit the external trust boundary that this
fixture does not model [16, 17].

## Transition-relative computation

Some named targets factor through source views carrying transition or history
context even when they do not factor through a selected coarser projection.
“Transition-relative computation” is a bounded program label; the formal
generic core is target-relative functional factorization through selected
source views. It does not define an operational semantics or claim that all
computation is transition-relative. Operational and trace semantics are the
intellectual neighborhood, not theorem-equivalent instances [13, 18].

## Relation to public V15

Public V15 is a Cross-Calculus Atlas of selected, receipt-indexed
correspondences. It preserves native indices and receipts without selecting a
shared bridge algebra.

This candidate asks which selected targets uniformly factor through which
views. It neither replaces the V15 bridge surfaces nor promotes a shared
cross-calculus semantics. No existing public module depends on this candidate;
its core and bounded evidence are separately rooted as
`GovernedTransitionBoundaries` and
`GovernedTransitionBoundariesEvidence`.

## Explicitly unearned

This candidate does not establish:

- a new generic factorization theorem;
- Hennessy–Milner characterization;
- statistical minimal sufficiency;
- general authorization theory or temporal validity;
- general amalgamation;
- causal attribution or attestation correctness;
- universal six-way independence;
- a universal transition-relative semantics;
- one canonical global carrier;
- a target-independent least representation;
- arbitrary-carrier minimality;
- whole-system or cross-surface composition;
- research-OS correctness;
- product readiness;
- external novelty or priority;
- a V16 release; or
- V16 finality.

## Verification entry points

```text
lake build GovernedTransitionBoundaries
lake build GovernedTransitionBoundariesEvidence
bash scripts/check-governed-transition-boundaries-crossing.sh
bash scripts/check-governed-transition-boundaries-footprint.sh
```

The source-crossing receipt is
[`V16-PUBLIC-SOURCE-CROSSING-RECEIPT_2026-07-26.md`](V16-PUBLIC-SOURCE-CROSSING-RECEIPT_2026-07-26.md).

## References

1. Alan Nash, Luc Segoufin, and Victor Vianu, “Views and Queries:
   Determinacy and Rewriting,” *ACM TODS* 35(3), 2010,
   [doi:10.1145/1806907.1806913](https://doi.org/10.1145/1806907.1806913).
2. Emily Riehl, *Category Theory in Context*, 2016, §3.1.
3. Lean project contributors, [Lean Language Reference:
   Quotients](https://lean-lang.org/doc/reference/latest/The-Type-System/Quotients/),
   source snapshot `94c1e97d48aa0b9b780b80fbb6f817e72182afc1`.
4. William Ward Armstrong, “Dependency Structures of Data Base
   Relationships,” *Information Processing 74*, 1974.
5. Ronald Fagin, “Functional Dependencies in a Relational Database and
   Propositional Logic,” *IBM JRD* 21(6), 1977,
   [doi:10.1147/rd.216.0534](https://doi.org/10.1147/rd.216.0534).
6. Zdzisław Pawlak et al., “Rough Sets,” *CACM* 38(11), 1995,
   [doi:10.1145/219717.219791](https://doi.org/10.1145/219717.219791).
7. Jerome H. Saltzer and Michael D. Schroeder, “The Protection of
   Information in Computer Systems,” *Proceedings of the IEEE* 63(9), 1975,
   [doi:10.1109/PROC.1975.9939](https://doi.org/10.1109/PROC.1975.9939).
8. Vincent C. Hu et al., *Guide to Attribute Based Access Control*, NIST SP
   800-162, 2019 update,
   [doi:10.6028/NIST.SP.800-162](https://doi.org/10.6028/NIST.SP.800-162).
9. Jaehong Park and Ravi Sandhu, “The UCONABC Usage Control Model,” *ACM
   TISSEC* 7(1), 2004,
   [doi:10.1145/984334.984339](https://doi.org/10.1145/984334.984339).
10. D. Cooper et al., [RFC 5280](https://www.rfc-editor.org/rfc/rfc5280),
    2008.
11. Alan K. Mackworth, “Consistency in Networks of Relations,” *Artificial
    Intelligence* 8(1), 1977,
    [doi:10.1016/0004-3702(77)90007-8](https://doi.org/10.1016/0004-3702(77)90007-8).
12. Peter van Beek and Rina Dechter, “On the Minimality and Decomposability of
    Row-Convex Constraint Networks,” *JACM* 42(3), 1995,
    [doi:10.1145/210346.210347](https://doi.org/10.1145/210346.210347).
13. Stephen D. Brookes, C. A. R. Hoare, and A. W. Roscoe, “A Theory of
    Communicating Sequential Processes,” *JACM* 31(3), 1984,
    [doi:10.1145/828.833](https://doi.org/10.1145/828.833).
14. Martin Abadi and Leslie Lamport, “The Existence of Refinement Mappings,”
    *TCS* 82(2), 1991,
    [doi:10.1016/0304-3975(91)90224-P](https://doi.org/10.1016/0304-3975(91)90224-P).
15. Elias Bareinboim and Judea Pearl, “Causal Inference and the Data-Fusion
    Problem,” *PNAS* 113(27), 2016,
    [doi:10.1073/pnas.1510507113](https://doi.org/10.1073/pnas.1510507113).
16. George Coker et al., “Principles of Remote Attestation,” *International
    Journal of Information Security* 10, 2011,
    [doi:10.1007/s10207-011-0124-7](https://doi.org/10.1007/s10207-011-0124-7).
17. H. Birkholz et al., [RFC 9334](https://www.rfc-editor.org/rfc/rfc9334),
    2023.
18. Gordon D. Plotkin, “A Structural Approach to Operational Semantics,”
    *JLAP* 60–61, 2004,
    [doi:10.1016/j.jlap.2004.05.001](https://doi.org/10.1016/j.jlap.2004.05.001).
