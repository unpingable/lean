# Standing-upgrade block: a worked example

A limited-standing claim attempts to cross into stronger authority. The Admissibility Calculus refuses the move at three layers — verdict, bridge, and execution — and the refusal is by construction, not by policy.

## The scenario

An actor in a governance context wants to amend the active policy. Their basis is self-attested: the only evidence offered is their own claim. They have full mutation standing (the system permits them to issue amendment proposals). They have resolved precedence (no other rule overrides theirs). The only weakness is the basis itself.

## What the kernel sees

The kernel does not evaluate the claim as a whole. It decomposes:

- **Basis verdict** (`Authority.BasisVerdict`) — was the evidence admissible? Possible values: `noBasis`, `advisoryBasis`, `admissibleBasis`.
- **Precedence verdict** (`Authority.PrecedenceVerdict`) — is precedence resolved, incomparable, or conflicting?
- **Standing verdict** (`Authority.StandingVerdict`) — does the actor have invocation standing?

Authorization requires all three green:

```
authorityVerdict admissibleBasis resolved standing = authorized
```

(`authorityVerdict` defined at `LeanProofs/Admissibility/Authority.lean:64`; the iff is `authorized_iff_all_green` at line 107.)

## The basis fails

The derivation environment recognizes the self-cert as revoked. By the spec obligation `BasisDerivation.revoked_never_admissible` (defined at `LeanProofs/Admissibility/Derivation.lean:65`), any claim recognized as revoked cannot derive `admissibleBasis`. So the basis verdict is `noBasis`.

This is not a policy choice. It is a structural property of every `BasisDerivation`: concrete implementations must discharge the obligation at construction time, or they cannot exist as values of the type.

## The verdict layer refuses

`Authority.no_basis_never_authorized` (line 80): for any precedence and standing,

```
authorityVerdict noBasis p s ≠ authorized
```

Even with green precedence and green standing, the kernel will not return `authorized`. The blocking is direct and total.

## The bridge layer refuses

The bridge (`Derivation.lean`) composes the three component derivations into a single `decideAuthority` verdict. `Derivation.revoked_basis_never_authorized` (line 154) lifts the basis-layer refusal through the composition:

```
revoked_basis_never_authorized env state actor claim hrevoked :
  decideAuthority env state actor claim ≠ authorized
```

The actor's claim cannot reach `authorized` at the bridge — the discipline carries from the structure spec to the composed verdict.

## The execution layer refuses

To actually mutate governance state, the actor would need to construct an `Execution.AuthorizedStep` (defined at `LeanProofs/Admissibility/Execution.lean:82`) — a structure requiring *both* `StepAllowed` (mutation-side standing) AND `authorityAuthorized` (claim verdict was `authorized`). Both proofs are required at the structure-literal level; there is no constructor that takes only one.

`Execution.revoked_basis_cannot_be_authorized_step` (line 124) is the load-bearing theorem: if the basis is revoked, no `AuthorizedStep` for that step can exist. By the type system, the mutation cannot be issued.

## The receipt

The specimen `Admissibility.CalculusOne.Examples.SelfCertDenial.specimen_self_cert_denial` (at `LeanProofs/Admissibility/Examples.lean:96`) is the formal demonstration. Reading it shows a concrete derivation environment (`rejectingBasis`) and the one-line proof:

```
revoked_basis_never_authorized env state actor claim trivial
```

That `trivial` discharges `basisRevoked state claim` — because `rejectingBasis.basisRevoked` is the constant `True` predicate. Every claim in this environment is treated as revoked. The blocking theorem does the rest.

## What the example demonstrates

- The kernel refuses self-certification not by adding a "no self-cert" rule, but by requiring evidence-side admissibility *separately* from mutation standing. A claim's author cannot be its own basis without earning admissibility through a separate evidence pathway.
- The refusal cascades through three layers — verdict, bridge, execution — and each layer's refusal is its own named theorem. The same blocker fires at every layer where the claim might be smuggled past.
- The theorem names are the receipt. They are inspectable, citable, and machine-checkable. A reviewer who doubts the refusal can run `lake build` and verify in seconds.

## Variations

The same machinery handles other attempted upgrades. Each is its own named specimen in `Examples.lean`:

- **Conflicting precedence** — `Authority.conflicting_precedence_never_authorized` (line 95); specimen `specimen_conflicting_precedence_denial` (line 108). Two precedence claims oppose each other; the kernel refuses to authorize either without external resolution.
- **Receipt without authority upgrade** — the trapdoor invariant `StateTransition.record_receipt_does_not_amend_policy` (line 112); specimen `specimen_receipt_no_authority_upgrade` (line 119). Recording evidence never moves authority; `recordReceipt` mutates `EvidenceStore` and cannot touch `PolicyStore` by construction.
- **Open finding accounted** — declaring a policy gap mutates `GapStore` only; an advisory basis short-circuits the verdict algebra to `advisory`; specimen `specimen_open_finding_accounted` (line 148). The system progresses by recording the gap, not by authorizing closure on it.

Each is a blocked attempt to cross a boundary the calculus refuses to authorize crossing. The calculus does not adjudicate which side is "right." It refuses to convert a structurally inadmissible claim into an authorized one regardless of how the surrounding context dresses the attempt.
