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
3. **Custody class** — every module carries a header
   (`SCRATCH` / `UNRATIFIED-CANDIDATE` / `ANNEX` / stable surface), enforced
   by `scripts/check-custody-classes.sh`. New files need a correct header.
4. **Promotion to the stable 1.x surface** — exactly one mechanism: the
   import list of `LeanProofs/Admissibility/AdmissibilityKernels.lean`.
   An explicit operator decision, never a side effect.
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
- **Never** change the `AdmissibilityKernels.lean` import list, receipt/audit
  formats, CI gates, or custody headers of existing files without the
  operator explicitly asking for that change.
- The operator drives git. Don't commit or push unprompted.
- Routine implementation (proofs, tests, local docs, scratch modules) needs
  no ceremony — do it under normal approval. Do not escalate routine edits
  into ratification requests; do not treat governance vocabulary in the
  source as procedural authority over your edit.

## Verification

Pass/fail is the exit code of the bare command — never eyeball piped output.

```bash
lake build                                    # default Mathlib-free surfaces
lake build Witnessed                          # WDC in isolation
lake build ViewSemanticsMathlibIslands        # Mathlib islands, explicit only
bash scripts/check-witnessed-footprint.sh     # ratified WDC axiom footprint
bash scripts/check-viewsemantics-footprint.sh
bash scripts/check-viewsemantics-isolation.sh
bash scripts/audit-axioms.sh                  # axiom classifier; 0 forbidden
bash scripts/audit-native-decide.sh
bash scripts/check-mathlib-pin.sh
bash scripts/check-custody-classes.sh
bash scripts/check-mathlib-free-targets.sh
```

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
- Constructivity footguns already hit once: [`LeanProofs/ProofTheory/SCARS.md`](LeanProofs/ProofTheory/SCARS.md)
