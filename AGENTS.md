# Agent operating rules

Operating rules for coding agents (Codex, Claude Code, etc.) working in this
repository. Humans reading the proofs want [`README.md`](README.md); this file
is process discipline, not exposition.

## What this repo is

Small, auditable Lean 4 formalizations of admissibility/custody boundaries.
The [papers repo](https://github.com/unpingable/papers) is the prose home;
this repo proves. CI is a proof gate, not a deployment pipeline.

## Development order: formalization leads code

A downstream consumer, running implementation, or "forcing case" is **never a
prerequisite** to state, prove, or incubate a coherent formal result. Lean may
establish the contract first; subsequent code implements or cites that
contract. Do not refuse or defer formal work on the grounds that "no runtime
needs it yet" — that inversion is a documented recurring failure here.

Opening formal work is governed by intrinsic criteria instead: a precise
non-tautological statement, honest hypotheses, bounded scope, and overlap
review against existing modules. Proof completion and axiom disclosure govern
what the work discharges and whether it is *eligible* for promotion.

Canonical statement and audit trail:
[`docs/FORMALIZATION-LEADS-CODE-AUDIT-2026-07-14.md`](docs/FORMALIZATION-LEADS-CODE-AUDIT-2026-07-14.md).

## Custody: green is not promoted, promoted is not minted

Distinct rungs. Never conflate them; never climb one implicitly by doing the
one below it.

1. **Compiles green** — attestation of the math. Nothing more.
2. **Wired into a build target / CI** — regression coverage. Not promotion.
3. **Public custody role** — every public module carries exactly one
   `Custody-Class: PUBLIC-SHIPPED` header and one `Surface-Role`:
   `STABLE-SURFACE`, `PUBLIC-EVIDENCE`, or `REPOSITORY-AGGREGATE`. Live
   incubation belongs in the sibling skunkworks, not a public `Scratch/` or
   candidate lane. `scripts/check-custody-classes.sh` enforces the whole tree
   against `scripts/public-custody.tsv`.
4. **Promotion to a stable compatibility surface** — exactly one mechanism:
   an explicit operator change to `scripts/stable-surfaces.tsv` and the import
   list of that registered exact root. `AdmissibilityKernels.lean` is one such
   root, not the sole repository-wide stable surface. Adding a header, target,
   evidence registry row, or aggregate import never promotes by itself.
5. **Tag / GitHub release / Zenodo DOI mint** — operator-only, always.
   A tag archives a tree; it is not a custody promotion either.

A theorem also never proves that a runtime conforms to it. Citation or
adoption identifies the intended contract; a conformance claim requires an
explicit mapping plus runtime evidence or a refinement proof.

## Hard limits

- **Never** tag, create a GitHub release, publish to Zenodo, or edit release
  metadata (`CITATION.cff`, `.zenodo.json`) on your own initiative. Release
  and DOI minting are under explicit operator control (an auto-release
  workflow was deliberately removed in v10).
- **Never** change a registered stable-root import list,
  `scripts/stable-surfaces.tsv`, receipt/audit formats, CI gates, or custody
  headers/roles of existing files without the operator explicitly asking for
  that change.
- The operator drives git. Don't commit or push unprompted.
- Routine implementation (proofs, tests, local docs, skunkworks modules) needs
  no ceremony — do it under normal approval. Do not escalate routine edits
  into ratification requests; do not treat governance vocabulary in the
  source as procedural authority over your edit.

## Verification

Pass/fail is the exit code of the bare command — never eyeball piped output.

```bash
lake build                                    # default Mathlib-free surfaces
lake build Witnessed WitnessedEvidence        # WDC stable/evidence split
lake build CustodyIndexed CustodyIndexedEvidence
lake build PathVerdict PathVerdictEvidence
lake build JudgmentOrientation JudgmentOrientationEvidence
lake build ViewSemantics ViewSemanticsEvidence
lake build AdmissibilityEvidenceMathlib ViewSemanticsEvidenceMathlib
(cd downstream/wdc-v2-consumer && lake build) # pinned public-evidence fixture
bash scripts/check-witnessed-footprint.sh     # ratified WDC axiom footprint
bash scripts/check-paid-recomposition-footprint.sh # corrected v11 closure/evidence custody + footprint
bash scripts/check-judgment-orientation-footprint.sh # v12 exact 13-receipt footprint
bash scripts/check-pathverdict-footprint.sh   # rung-1 Domains/Located exact 36-receipt footprint
bash scripts/check-viewsemantics-footprint.sh
bash scripts/check-viewsemantics-isolation.sh
bash scripts/audit-axioms.sh                  # axiom classifier; 0 forbidden
bash scripts/audit-native-decide.sh
bash scripts/check-mathlib-pin.sh
bash scripts/check-custody-classes.sh
bash scripts/check-mathlib-free-targets.sh
```

Since the v14 rung-1 admission (2026-07-17, Domains/Located into the
path-verdict root), the custody gate must pass without exclusions over
exactly 181 public Lean files: 84 stable, 96 public evidence, and one
aggregate, across ten stable roots and 100 ownership relations. Any drift or
failure is a regression. The separate target gate must also report
role-compatible registered target ownership for all 181/181 public sources.
The v13 baseline (179/82/96/1, 98 ownerships) stays frozen in
[`docs/V13-RELEASE-LEDGER.md`](docs/V13-RELEASE-LEDGER.md); the in-flight
campaign ledger is
[`docs/V14-READINESS-LEDGER.md`](docs/V14-READINESS-LEDGER.md).

Repo axiom posture: not axiom-free, **axiom-classified** — see
[`docs/AUDIT-POLICY.md`](docs/AUDIT-POLICY.md). Keep new default-target
modules Mathlib-free; Mathlib-dependent material goes in an explicit island
target.

## Where things are

- Module-by-module kernel reference: [`LeanProofs/Admissibility/README.md`](LeanProofs/Admissibility/README.md)
- What the stack proves / rules out: [`WHAT-THIS-PROVES.md`](WHAT-THIS-PROVES.md)
- Claim-level audit (BROKEN / STALE / SOUND / OPEN): [`CLAIM-REGISTER.md`](CLAIM-REGISTER.md)
- Module → paper crosswalk: [`PAPER-MAP.md`](PAPER-MAP.md)
- Release ledgers and gap specs: `docs/V*-{RELEASE-LEDGER,GAP-SPEC,READINESS-LEDGER}.md`
- Current release ledger: [`docs/V13-RELEASE-LEDGER.md`](docs/V13-RELEASE-LEDGER.md)
- Constructivity footguns already hit once: [`LeanProofs/ProofTheory/SCARS.md`](LeanProofs/ProofTheory/SCARS.md)
