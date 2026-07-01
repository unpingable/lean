# ROADMAP — Bounded Calculi (Lean proof work order)

## 1. Status / custody

- **Candidate Lean roadmap. Documentation only.** No code implementation in this pass.
- **No `.lean` files modified; no promoted kernel or import boundary changed.**
- Does **not** authorize promotion of any scratch / surrogate module.
- Derived from the cross-lane ToolTheory roadmap
  (`~/git/papers/working/tooltheory/roadmap-custody-aware-authority-semantics.md`),
  **narrowed to Lean proof work** — no runtime, no bridge-foundry runtime, no transformer
  horizon. This file answers one question: *what Lean objects should exist, in what order,
  under what custody class, with what non-collapse theorem pressure?*
- **Core invariant:** *No artifact may testify beyond the stage it actually survived.*
- **This roadmap does not make `BoundedCalculi` authority-bearing.** A roadmap is not a
  promotion. Modules are promoted only through the existing repo gates (§4).

## 2. Existing bounded calculi inventory

Live under `LeanProofs/BoundedCalculi/` — all `Custody-Class: ANNEX`, un-wired, green,
axiom-clean (`#print axioms`: 5 zero-axiom, `SurfaceProjection` `propext`), **zero
`True`-shaped theorems** across all six. Local judgment forms and a sample theorem below;
**full strongest/weakest + proof-shape classification is Slice L1 work, not yet done.**

| Module | Local judgment | Blocks | Sample theorem | Surrogate/specimen flag |
|---|---|---|---|---|
| `TemporalCustody.lean` | temporal validity of an action (`WitnessedTime`/`Expiry`/`SignedArtifact`) | "valid then ⇒ valid now" | `checked_action_temporally_valid` (19 thms) | — |
| `SurfaceProjection.lean` | `ProjectionAuthorized` over `Atom`/`Source`/`Use`/`Retains` | "shown/summarized ⇒ authorized" | `retained_witnesses_authorize` (13 thms) | — |
| `RefusalDenial.lean` | `DenialValid` (+ `LegibleFor`) | "silence/displayed refusal ⇒ valid denial" | `signed_denial_valid` (11 thms) | — |
| `BoundaryArtifact.lean` | `MayMint` over `Exposure`/`Boundary` | "internal evidence ⇒ external artifact" | `authorized_exposure_may_mint` (6 thms) | **surrogate** — local `Exposure` stand-in; does NOT testify about `Admissibility.CrossBoundaryExposure` |
| `ObligationResidue.lean` | residue-threaded claim derivation (`claimResource`/`obligationResidue`/`AccountingReceipt`) | "consumed resource ⇒ obligations vanished" | `claim_resource_path_preserves_obligation` (11 thms) | imports `Witnessed.ResourceSequent` |
| `SafetyPreservation.lean` | `SafeAllowed` (auth + safety bridge) over `AuthorizedTrajectory`/`BridgedTrajectory` | "authorized steps ⇒ safe trajectory" | `safeAllowed_preserves` (8 thms) | **specimen** — `ToyState` substrate |
| `BoundedCalculi.lean` | aggregate import | — | — | aggregate ≠ coherence proof (§9) |

**Missing calculus:** Execution Custody (§6) — not built.

## 3. Proof-shape taxonomy (audit labels for L1)

Theorem *count* is not the metric. The metric is whether a module creates reusable
judgment / rule / non-collapse structure. Classify every theorem as one of:

- **positive composition/cut** — a real paid-path or derivation-composition rule.
- **witness dependency** — conclusion genuinely requires a named witness atom.
- **constructor exclusion** — a `¬`-wall proved by exhaustive absence of a constructor.
- **non-collapse under composition** — the wall survives composing derivations, not just a
  one-step toy.
- **definitional/trivial** — holds by `rfl`/unfolding; carries no structure.
- **specimen-backed** — true only for a concrete toy substrate (e.g. `ToyState`).
- **surrogate-only** — testifies about a local stand-in, not the real target object.

A module's strength is its best *non-collapse* / *positive-composition* theorem, minus any
load-bearing reliance on definitional/specimen/surrogate shapes.

## 4. Promotion pressure criteria

A bounded calculus is **not** promotion-ready merely because it compiles. *Compiled ≠
promoted.* Promotion pressure requires, all of:

- a named local judgment form;
- ≥1 nontrivial positive rule (not definitional);
- ≥1 non-collapse theorem that survives composition;
- no load-bearing reliance on unmarked surrogate structures (surrogates must be explicitly
  quarantined, e.g. `BoundaryArtifact`'s `Exposure`, `SafetyPreservation`'s `ToyState`);
- explicit custody header/status;
- axiom audit clean (footprint ≤ `[propext, Quot.sound]`);
- no `sorry` / `admit` / `native_decide`;
- **no import into a promoted kernel without an explicit operator decision**;
- a connected forcing case from existing WDC/Witnessed doctrine.

Promotion is per-module, through these gates — never by roadmap pressure, never by
aggregate import.

## 5. Intercalculus bridge roadmap

**Bridge law:** cross-calculus cut requires explicit bridge evidence. **No bridge composes
transitively by default.** No bridge may erase the refusal/non-authority surface of either
endpoint.

**First candidate bridge: `Temporal → Surface`.** Target theorem shape:

> Temporal validity of a source artifact does not imply projection authorization unless the
> projection retains or explicitly converts the demanded temporal witness atoms.

**Required negative theorem** (the anti-master-turnstile backstop): a `Temporal → Surface`
bridge does **not** imply boundary minting, safety preservation, obligation discharge, or
global admissibility.

## 6. Execution Custody mini-calculus (future Lean scratch)

Distinguish, as separate judgments (do NOT collapse):

`MayAttempt` · `MayCommit` · `CommitAttempted` · `DidExecute` · `DidNotExecute` ·
`CommitUnknown` · `PreservedSafety`.

Required non-collapse theorems:

- `MayAttempt` ⇏ `MayCommit`
- `MayCommit` ⇏ `DidExecute`
- `TicketSpent` ⇏ `DidExecute`
- `CommitAttempted` ⇏ `DidExecute`
- `DidExecute` ⇏ `PreservedSafety`
- `PreservedSafety` ⇏ discharged obligation

Model `ExecutionTicket` as **linear / single-use**, reusing or aligning with
`Witnessed.ResourceSequent`'s `Split`/`Consumes`/residue machinery (a spent ticket is
gone). Same shape as the existing *reachable ≠ executable* strictness result.

## 7. Bootstrap / Genesis scratch roadmap

Future Lean objects: **`BootKernel`**, **`BaselineSettlement`**. Boot stages:

`ColdStart → DiscoveryOnly → BaselineObserved → BaselineSettled → TicketMintingEnabled → ExecutionEnabled`

Required non-collapse theorems:

- `DiscoveryOnly` ⇏ mutation authority
- `BaselineObserved` ⇏ `BaselineSettled`
- `BaselineSettled` ⇏ `SafetyPreserved`
- `KernelBoot` ⇏ root omnipotence

**Avoid any `RootAuthority signed_by_operator` model** — a signed root token is the master
turnstile in a novelty hat.

## 8. CheckpointSettlement scratch roadmap

Future Lean object: **`CheckpointSettlement`**. Compaction must be custody-*preserving*, not
lossy. A checkpoint must preserve: unresolved obligations · unknown commits · refusal
artifacts · schema versions · boundary scopes · open safety questions · digest/Merkle root
(or an abstract coverage witness) · explicit non-authorities.

Required theorem shapes:

- checkpoint settlement preserves live obligations
- checkpoint settlement does not discharge unknown commit
- checkpoint settlement does not upgrade observation to safety
- checkpoint settlement covers only the declared range

## 9. Forbidden moves

- master judgment `Γ ⊢ Admissible(a)`;
- local-judgment → global-authority casts;
- default transitive bridge composition;
- signature / certificate / JWT as semantic authority;
- **aggregate import as proof of calculus coherence**;
- **promotion by compilation alone**;
- treating a surrogate module as testimony about the real target module;
- collapsing attempt / commit / receipt / observed-effect / safety / obligation-discharge.

## 10. Near-term Lean slice order

- **L0** — capture this roadmap. *(this pass)*
- **L1** — bounded-calculi theorem inventory (fill §2's strongest/weakest + §3
  classification per module) and anti-vacuity strengthening of the weakest.
- **L2** — one bridge scratch, `Temporal → Surface` (§5).
- **L3** — prove **no cross-calculus cut without an explicit bridge**.
- **L4** — Execution Custody scratch (§6).
- **L5** — `BootKernel` / `BaselineSettlement` scratch (§7).
- **L6** — `CheckpointSettlement` scratch (§8).

Each slice is fenced ANNEX/SCRATCH until it clears §4; none imports into a promoted kernel
without an operator decision.
