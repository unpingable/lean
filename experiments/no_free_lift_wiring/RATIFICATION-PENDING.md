# Ratification — Pending

**Custody:** decision template, non-binding. Drafted by a model (paper/Lean
Claude); the facts below are Observed (rerunnable); the **decisions are not a
model's to make**. This file exists so the operator can mark the pending boxes
after sleeping on them. No box here is ticked by the drafter.

Self-application (the rule this very file obeys): *a Lean theorem is evidence
into the admission gate, never a receipt that bypasses it; a model may draft the
evidence column, never the ratified one.* There is deliberately **no "Ratified"
column** below — "checks" is a fact a model can assert; "ratified" is a speech
act only the operator can perform.

---

## ATTESTED — Observed, rerunnable (no signature needed)

Independently re-verified this session (`lake build` / `lake env lean`, fresh
`#print axioms` — not relayed):

- [x] **no-free-lift schema** — builds; axiom-free even inside the full wired build
- [x] **carry-law coordinates** — axiom-free
- [x] **wired stack** — builds composed (toolchain 4.29, Mathlib-free), 18 jobs, exit 0;
      **no actuator** (no `lean_exe`/`main`/`#eval`/`extern`/`unsafe`/`IO`);
      no import-continuity laundering (schema stays axiom-free in the composed build);
      modeled embeddings carry exactly the disclosed core axioms `[propext, Quot.sound]`
- [x] **CarryLaws + NoFreeLift (canonical)** — committed (`94df70e`, by the operator),
      custody-class `UNRATIFIED-CANDIDATE`, **unwired** (0 imports in `LeanProofs.lean`)

> Note: "committed" is the routine side of the line — version control is
> attestation. It is **not** promotion. Do not read `94df70e` as ratified.

## NOT ADMITTED — refused until a separate act exists

- [✗] **runtime admission** — there is no actuator; proof ≠ world receipt
- [✗] **kernel collapse** — the dead 1.0 ghost; the schema proves its negation
      (`naked_lift_unsound`, `no_free_lift`)
- [✗] **build / theorem as an admission receipt** — attestation, not admission

## DECISION PENDING — operator's speech act (two INDEPENDENT signatures)

- ( ) **Name.** Use "Admissibility Calculus" to mean *no-free-lift accounting
      over admissibility kernels, with explicit bridge costs and no kernel
      collapse.*
      - Fallback if not today: **"No-Free-Lift: Bridge-Cost Coordinates for
        Admissibility Kernels"** (lets the work stand without spending the word)

- ( ) **Custody.** Promote `Admissibility.CarryLaws` / `Admissibility.NoFreeLift`
      from `UNRATIFIED-CANDIDATE` → wired/ratified surface.
      - **Independent of the Name box.** A yes on the name is *not* a yes here;
        the custody signature is the one that changes what gets relied on.

---

*Open ModelBound residue (from `WIRING-AUDIT.md` §7) is unchanged by any box
above: whether `CanonFresh` is the canonical predicate, whether custody /
contraction get real `Sem` or stay stubs, and non-subsidy being semantically
backed only for authority↔freshness so far.*
