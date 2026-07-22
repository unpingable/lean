# PJ Tranche B-prime Charter

Date: 2026-07-22

## Authority and boundary

This bounded continuation begins from:

- PJ-A candidate `d634517fc08205758de59466c97f5998f774dabb`, tree
  `c539b62398d30b5d12a40fdffef53eb543305705`;
- PJ-A ratification `d1fad6efc608b7daf3b8a8f47b7f4cfc5a1c249e`, tree
  `706da052cb2dcff572054f686884f92bb43829ad`;
- authoritative PJ-B fast-falsification record
  `a66918dda9dd32892d6275abaa59229633ab3a07`, tree
  `68d7023bfb42a8a08a490ad4419334ccd5b5ca92`;
- frozen PJ-A core SHA-256
  `1d86bee97f92f2644d8605a05d6a31deaa3584f55582d4a09b638718ffff185c`.

`FRONTIER-NOT-COMPOSITIONAL` remains authoritative. This tranche tests only
whether the frozen indexed-judgment core supports an exact native-receipt
anti-minting result. It does not add or rename a common frontier, remaining
obligation, ownership, execution, authority, or testimony theory.

## Exact scientific question

Can independently inhabited source and target judgments, together with raw
bridge-shaped data, produce source-relative target entitlement without the
exact native receipt for that bridge and endpoint pair?

The tested distinction is:

1. independent source evidence;
2. independent target truth;
3. a raw `IndexedJudgmentBridge` value;
4. independently qualified source adapters;
5. exact endpoint-indexed native receipt;
6. `EntitledFrom` carrying source evidence plus that receipt;
7. bounded target consumption through the entitlement's derived
   `targetEvidence`.

Adapter qualification remains an exact campaign-level fidelity fact. It is
not copied into the generic signature as a free `lawful` Boolean or proof
field.

## Stop gate

The only successful disposition is
`READY-FOR-PJ-B-PRIME-RATIFICATION`. It creates a candidate but does not
ratify it or open Tranche C-prime. The required next response is exactly:

```text
RATIFY-PJ-B-PRIME
```
