# Provenance

This repository is human-directed and materially AI-assisted formal research.
Contribution credit and decision authority are recorded separately. Final
authority over research direction, claim scope, public custody, compatibility
surfaces, naming, and releases rests with the human author and operator. AI
systems made substantial contributions to statements, proofs, countermodels,
reviews, audits, documentation, and integration.

## Human authorship and operator authority

By the operator's account, James Beck defined the research program, selected
the problems and claims to pursue, set the acceptance criteria and scope
fences, and reviewed, revised, accepted, or rejected agent output throughout
development. The operator alone:

- decides whether a proposed statement expresses the intended claim;
- accepts hypotheses, nonclaims, and disclosed axiom footprints;
- changes custody classifications and registered stable surfaces;
- ratifies public theorem-family names; and
- commits, tags, releases, and authorizes DOI deposits.

At the local annotated `v14.0.0` tag, whose target commit is `ff491b8`, all 221
reachable commits list James Beck in Git's Author field. Co-author trailers and
the functional record below identify material AI contributions; they do not
transfer operator authority.

Human review is not proof evidence. Lean's kernel checks elaborated proof terms
against their declared environment. Repository gates separately check scoped
build, axiom-footprint, custody, and target invariants. Operator review governs
admission and the claims the project makes about checked artifacts.

## AI-assisted collaboration

The work was iterative rather than a clean design-then-implementation handoff.
Agents proposed formal shapes, wrote and repaired Lean, constructed adversarial
examples, found false or overbroad statements, ran verification, and helped
maintain the claim and custody records.

### Formalization, proof engineering, and review

Lead sustained collaboration: Codex (OpenAI). The operator attributes the path
through the later formalization campaign, culminating in v14, principally to
Codex. Its material work included theorem and countermodel construction, proof
repair, overlap and scope review, detection of vacuity and overclaim, axiom and
footprint audits, documentation reconciliation, and adversarial review.

The repository preserves only part of that work as explicit attribution. Git
contains the commits `8fd73eb` ("codex-derived work") and `eb1ee75` ("codex
audit of paper repo + other scraps"). The campaign record
[`.governor/loop.json`](.governor/loop.json) names Codex as hybrid builder and
read-only adversarial auditor for the bounded-calculi/v7 work;
[`docs/V9-RELEASE-LEDGER.md`](docs/V9-RELEASE-LEDGER.md) marks multiple formal
artifacts and the Mathlib split as Codex-derived; and
[`experiments/no_free_lift_wiring/WIRING-AUDIT.md`](experiments/no_free_lift_wiring/WIRING-AUDIT.md)
records specific Codex-found counterexamples, scope corrections, and
strengthening requests.

The operator reports additional Codex work in directed sessions and in the
private research/skunkworks campaign. The public repository ties the promoted
sources to reviewed source revisions, but cannot independently allocate every
piece of private work among collaborators. No Codex `Co-Authored-By` trailer is
reachable from the v14 tag; this is functional attribution from the cited
records and operator account, not a claim that Codex alone originated every
v14 definition or theorem.

### Conceptual framing and theorem-shape critique

Lead collaboration: ChatGPT (OpenAI). It materially contributed to the
conceptual and editorial loop: separating claim types, turning prose into
bounded formal questions, proposing theorem shapes and countermodels, and
sharpening hypotheses.

The repository records concrete examples in
[`PAPER-MAP.md`](PAPER-MAP.md) and [`CLAIM-REGISTER.md`](CLAIM-REGISTER.md).
ChatGPT caught the false first form of `commitsToHysteretic_strict_mono`, helped
route the quantitative persistence proof ladder, and sharpened the
witness-invariance boundary. The operator additionally attributes material
contributions to the formalization-leading and runtime-conformance doctrine to
ChatGPT discussions. By the operator's account, these exchanges often shaped a
statement before proof work began and therefore are not well measured by
changed lines.

### Implementation and repository integration

Material collaboration: Claude Code (Anthropic). Through the `v14.0.0` tag,
Git records 34 `Co-Authored-By: Claude Fable 5` trailers and 14
`Co-Authored-By: Claude Opus 4.8 (1M context)` trailers. The Fable-labelled
work is concentrated in the July bounded-calculi, custody-indexed, and v5–v8
campaigns. All 14 commits from the first v14 admission through v14 preparation
carry the Opus trailer.

The v14 integration pass was rapid and required follow-up corrections. The
history preserves that loop: stale target commentary, rung-5 public accounting,
rung-7 axiom partitioning, and description-gate phrasing were corrected before
the final v14 cut. Claude's trailers are evidence of material implementation,
extraction, integration, gate, and documentation work; they are not evidence
of exclusive design ownership, mathematical correctness, or operator
ratification.

## Provenance basis and limits

This is a functional attribution record based on:

- Git authorship, commit messages, and co-author trailers through the local
  annotated `v14.0.0` tag (target commit `ff491b8`);
- [`docs/V14-READINESS-LEDGER.md`](docs/V14-READINESS-LEDGER.md),
  [`docs/V14-RELEASE-LEDGER.md`](docs/V14-RELEASE-LEDGER.md), and
  [`CLAIM-REGISTER.md`](CLAIM-REGISTER.md);
- dated audit, experiment, source-comment, and paper-map records; and
- the operator's documented recollection of directed working sessions.

It is not a complete forensic reconstruction. Chat discussions, rejected
drafts, private research-tree work, and reviews that prevented bad code may not
appear in commit metadata. A commit trailer identifies collaboration on that
commit, not the origin of every contained idea. A model may also have performed
different roles in different sessions. The v14 ledgers record repeated
adversarial review, but do not always identify every reviewing model; unnamed
reviewers are not reconstructed here from inference.

Platform/tool names are used where exact model versions were not preserved.
Exact version labels are repeated only where Git recorded them. The numerical
Git counts above are frozen to the named v14 cut and will not silently describe
later history.

## What this document does not claim

- No exact proportional attribution by token count, elapsed time, theorem
  count, or lines changed.
- No claim that research design, implementation, and review occurred in a
  clean sequence, or that one system originated every result it implemented.
- No claim that a co-author trailer, agent review, or human acceptance proves a
  theorem. The checked term and disclosed axioms govern that question.
- No custody promotion, stable-surface change, naming ratification, tag,
  release, or DOI authority. This file records history; it grants none.
- No runtime-conformance claim. A runtime still requires the explicit mapping
  and evidence described in [`WHAT-THIS-PROVES.md`](WHAT-THIS-PROVES.md).
- No adjudication of legal authorship, copyright ownership, or licensing.
- No complete account of rejected ideas, invisible critique, or footguns
  avoided.

---

This document reflects the repository state and operator record as of
2026-07-20 and may be revised when better evidence appears.
