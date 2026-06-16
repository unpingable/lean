# experiments/ — tracked wiring witnesses

This tree contains **tracked, reproducible integration artifacts** that are
**not imported by the canonical proof surface** (`LeanProofs.lean` / the
`LeanProofs` lib). Each subdirectory is its own Lake project with its own
toolchain pin.

> A successful build under `experiments/` **attests that the wiring checks**.
> It does **not** promote any result into the archive's relied-upon theorem
> surface. Build-exit-0 is attestation of the math, never admission of a world
> claim.

Three tiers, kept distinct:

| tier | what it is |
| --- | --- |
| `LeanProofs/` (canonical) | stable artifacts, importable, cited carefully |
| `experiments/` | integration witnesses — reproducible, tracked, **explicitly non-canonical** |
| `LeanProofs/Scratch/` | working edge, volatile |

## Custody contract for every project under `experiments/`

```
Custody-Class:  EXPERIMENTAL-WIRING
Build status:   observed (reproducible)
Citation tier:  non-authoritative integration witness
May cite:       module graph, axiom footprint, counterexamples, audit findings
May NOT cite:   doctrine ratification, runtime admission, canonical surface membership
```

The audit travels **with** the wiring (e.g. `WIRING-AUDIT.md`,
`RATIFICATION-PENDING.md` next to the code). Without the audit, a wiring witness
reads as a quiet promotion attempt with extra steps.

---

## `no_free_lift_wiring/`

The wired customs-office stack (schema spine + modeled freshness/authority
embeddings), transplanted frozen from the `~/git/playground` sandbox. Schema
theorems are axiom-free even inside the composed build; modeled embeddings carry
exactly `[propext, Quot.sound]` (no import-continuity laundering). It currently
has **no actuator** — pure `lean_lib` of `Prop`s, so it admits nothing
operationally.

Two standing fences for work done here:

1. **Actuators are bench verbs, not admissions.** This is the room where an
   `lean_exe` / `IO` actuator *may* be added to experiment. An actuator here is a
   test-bench verb — it does **not** become an admission or enforcement action,
   and adding one changes nothing about the canonical surface until a human
   admits it. The moment an actuator is wired toward a real consumer, that path
   is subordinated to the receipt gate (proof as input to the gate, never a
   substitute for it).

2. **The atlas correspondence is a candidate, join unverified.** `ATLAS-MAP.md`
   maps this stack to `~/git/intake-composition-atlas` (a real receipt-enforcing
   linter). That Rosetta is a **candidate correspondence**; whether the atlas
   actually exhibits the mapped behaviors (`fixtures/fail/no-receipt.yaml`,
   `signed_is_not_witnessed`, depth-1 cap) is **not verified from this repo**.
   Treat it as a map to chase, not a proven bridge.
