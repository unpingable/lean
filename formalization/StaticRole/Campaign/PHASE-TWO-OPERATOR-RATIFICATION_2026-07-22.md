# StaticRole Phase Two — Operator Ratification

## Decision

```text
STATIC-ROLE-PHASE-TWO-RATIFIED
```

Ratification review date: `2026-07-22`

This record ratifies the exact candidate revision, not a branch name:

```text
candidate commit: 0a203e95ddf7f96f9f71a8e9d8b4b60bbde8a349
candidate tree:   5e30ce0d96e058063741df5665070fbb37c61887
candidate parent: 421d5cdb0b14a40c81711ce137a4b47842d8ed39
```

The candidate commit was not amended, squashed, rebased, or otherwise
rewritten during review.

## Four-gate finding

### 1. No hidden destination or selfhood conclusion

`SelfReferenceFrame` contains an abstract reference carrier, an injective node
realization indexed by host and represented center, a functional current
reference section, coordinate laws, and forecast-coordinate soundness.  It has
no primitive same-self, future-self, projected-self, prospective-continuation,
or correct-destination proof field.  `CoherentReferenceAction` contains a
total carry action together with unconditional identity, all-center
composition, and continuation-to-`repBefore`; it contains no R2 or current
section preservation field.

`PreservesCurrentReference` is the derived equality comparing the action's
carried source anchor with the independently supplied destination anchor.
The shared-frame `parityAction`/`fixedAction` pair, and the corresponding
alternate-current-section thought experiment, establish that destination
designation and action transport can vary independently while the frame laws
remain fixed.

### 2. The two actions differ structurally

The positive and negative expansions use the literal same base, information
layer, representation layer, node carrier and coordinates, reference frame,
current-reference section, role atlas, R1 proof, `repBefore`, continuation,
forecast, hosting, and grounding relation.  They differ only in their total
carry functions:

* `parityCarry` flips the two-point reference coordinate on either
  cross-center leg and is identity on equal centers;
* `fixedCarry` is identity on every leg.

Both actions satisfy identity for every center, composition for every center
triple, constructive round-trip and injectivity, and continuation
compatibility.  Neither stores an R2 verdict or a destination exception.  The
negative action reaches an ordinary, coordinate-correct and forecast-grounded
member of the same target fiber, not a failure sentinel.

### 3. The characterization is substantive

The forward implication of
`prospective_de_se_iff_coherent_transport` constructs canonical nodes,
carried-endpoint coherence, represented succession, forecast grounding,
coordinate receipts, endpoint accuracy, and round-trip evidence from R1,
preservation, and the frame/action laws.

The reverse implication combines the carried-endpoint and projected-node
equalities to obtain equality of two realized destination nodes, then uses
`referenceNode_injective` to recover the reference-coordinate equality that
is exactly `PreservesCurrentReference`.  The witness does not contain that
predicate as a field.  Removing injectivity permits distinct reference
coordinates to collapse to one node and prevents this recovery, so the
dependency is load-bearing rather than rhetorical.

### 4. The negative expansion fails only designated-reference preservation

The `fixedAction` expansion retains external role shift, R1 and accurate role
encoding, continuation, current and projected anchors, total lawful action,
round-trip and injectivity, continuation compatibility, forecast hosting,
grounding of both the designated and actually carried target nodes, and every
shared frame law.  Its sole failed R2 conjunct is:

```text
fixedAction.carry false true (coherenceFrame.currentReference false)
  = coherenceFrame.currentReference true
```

which reduces constructively to `false = true`.  No absence of continuation,
forecast, grounding, role accuracy, endpoint structure, or action coherence
contributes to the negative result.

## Hostile, provenance, and transport findings

All ten phase-two hostile cases remain constructive and non-vacuous in their
stated dimension: R1 without coherent transport; continuation without
preservation; anchors without a lawful action; lawful succession without
forecast grounding; grounding without required transport; transport with
inaccurate role encoding; a locally plausible endpoint map without identity
coherence; mnemonic record grounding without R2; R2 with an empty record-token
sort; and R2 without the deliberately separate phase-three uptake placeholder.
The last case is only a boundary marker and introduces no R3 semantics.

Primitive `isSelf` has been removed, no conclusion-equivalent synonym was
found, and arbitrary remoding cannot affect R2.  `traceValid` remains outside
R2.  The surviving provenance theorem is expressly a definitional
nondependence receipt for R1, not a substantive invariance theorem.

`FullSignatureIso` covers the original seven carrier sorts plus reference
coordinates and preserves the complete base, information, representation,
frame, and action signature.  Preservation and reflection are constructive
for `ExternalRoleShift`, `InternalRoleEncoding`,
`PreservesCurrentReference`, `CoherentProspectiveWitness`, the central
characterization predicate, and `ProspectiveDeSeEncoding`.  Reverse witness
transport uses the supplied inverse functions and inverse laws; it assumes no
surjectivity or choice beyond that explicit isomorphism data.

## Constructivity and reproduction

An independent execution of the qualification leaf printed axioms for all 48
listed declarations.  Every declaration reported that it depends on no
axioms: `48/48` axiom-free, with no `Classical.choice`, quotient principle, or
other axiom.  Source inspection also found no `sorry`, `admit`, custom axiom,
`Classical`, `choice`, `Quot`, `native_decide`, unsafe or partial declaration,
Mathlib import, or external dependency.

The exact verification commands and results were:

```text
lake env lean StaticRole/Campaign/Qualification.lean
exit 0; 48/48 declarations printed axiom-free

lake build StaticRole
exit 0; Build completed successfully (23 jobs)

lake build CalculiStable CalculiScratch CalculiAll Calculi
exit 0; Build completed successfully (269 jobs)

python3 scripts/formalization_audit.py check --skip-external --skip-footprints
exit 0; FORMALIZATION AUDIT: PASS (19 checks)

git diff --check
exit 0; no output

git diff --check 421d5cdb0b14a40c81711ce137a4b47842d8ed39 \
  0a203e95ddf7f96f9f71a8e9d8b4b60bbde8a349
exit 0; no output
```

## Ratified boundary

The ratified claim is bounded:

> This specimen formalizes external center-relative temporal roles, internal
> cross-center role encoding, and coherence-grounded prospective de se
> representation through lawful self-reference transport. It does not
> formalize temporal passage, phenomenal experience, consciousness,
> functional uptake, or metaphysical personal identity.

The local `currentReference` section remains supplied model structure; this
ratification does not establish its general semantic adequacy.  The central
finite fixture's `repBefore` relation is deliberately permissive, and the
substantive discrimination is the globally coherent action's alignment with
the independently fixed current-reference section.  No phase-three theory,
public release, or metaphysical identity claim is authorized by this record.

No push, merge to `main`, tag, mint, publication, or release is performed by
this ratification.
