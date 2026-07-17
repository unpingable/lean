# experiments/ — historical wiring records

This tree now contains the prose/audit record of retired integration
witnesses.  During the v13 custody cleanup, the superseded
`no_free_lift_wiring` Lean project was deleted from live source after its
ratified successor had long since become `LeanProofs.Witnessed.*`.  The exact
project remains recoverable from the v12 tag and Git history.

> The remaining documents are provenance, not current build targets. Their
> historical green receipts do not promote a theorem, attest the current tree,
> or prove runtime conformance.

Current ownership is kept distinct:

| tier | what it is |
| --- | --- |
| `LeanProofs/` | public stable API and terminal public evidence |
| sibling skunkworks | live formal incubation |
| `experiments/` | historical integration/audit prose; non-canonical |

## Historical custody contract

```
Custody-Class:  EXPERIMENTAL-WIRING
Build status:   observed in the archived tree; not live in v13
Citation tier:  non-authoritative integration witness
May cite:       module graph, axiom footprint, counterexamples, audit findings
May NOT cite:   doctrine ratification, runtime admission, canonical surface membership
```

The audit remains beside the ratification and migration records. Git history
supplies the source to which those dated receipts refer.

---

## `no_free_lift_wiring/`

The wired customs-office stack was the promotion provenance for the Witnessed
Derivation Calculus. Its ratification and migration documents remain useful;
its Lean source is no longer a second live implementation.

Two standing fences on interpreting the archive:

1. **The historical wiring was never runtime admission.** Its proofs and build
   receipts do not establish that a consumer conforms.

2. **The atlas correspondence remains unverified.** `ATLAS-MAP.md`
   maps this stack to `~/git/intake-composition-atlas` (a real receipt-enforcing
   linter). That Rosetta is a **candidate correspondence**; whether the atlas
   actually exhibits the mapped behaviors (`fixtures/fail/no-receipt.yaml`,
   `signed_is_not_witnessed`, depth-1 cap) is **not verified from this repo**.
   Treat it as a historical map to chase, not a proven bridge.

New integration experiments should be opened only with an explicit current
purpose and custody plan; live theorem incubation belongs in skunkworks rather
than recreating a second `Scratch/` lane here.
