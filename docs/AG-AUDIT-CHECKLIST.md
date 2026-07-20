# AG audit checklist — v4 screens applied to live governance schemas (F4)

**Status: CANDIDATE checklist, documentation only.** Derived from the proved
v4/post-v4 screens and walls; intended to be APPLIED by the AG session (and/or
codex) to the constellation's real receipt schemas, gate configs, and wire
formats. **No runtime claims**: these are questions the theorems make precise,
not code. A "yes" answer is a smell with a named theorem behind it, not a
conviction — each screen's false-positive/negative caveats are cited.

This is a v4/post-v4 schema-smell checklist, not a v14 conformance checklist.
A full-calculus claim must instead satisfy the exact scope, correspondence-map,
preservation, and transport obligations in
[`../WHAT-THIS-PROVES.md`](../WHAT-THIS-PROVES.md#formal-contract-and-runtime-conformance).

Audience note: written for the agent_gov session (the constellation weaver).
Each item names the Lean object that makes the question precise, so findings
can be traced back to the formal shape.

## 1. Universal evidence currency (`EvidenceCurrencyFree`, `UniversalStamp`)

- Does any single receipt kind in AG's schema fund (i.e., satisfy the evidence
  requirement of) EVERY gate? List each receipt kind × the gates it can
  license. A kind licensing all of them is a `UniversalStamp`.
- Special case (F2, `fluentSystem`): does any *confidence-like, claim-blind*
  signal (model self-report, score without provenance binding, "LGTM"-shaped
  approval) appear as accepted evidence at more than one unrelated gate?
- Caveat: broad-but-not-universal multi-currency evidence passes the formal
  screen; flag it anyway as a judgment call (named false negative).

## 2. Universal crossroads (`MasterFree`, `UniversalCrossroads`)

- In the NQ → nightshift → AG flow (and any other cross-repo lane): is there a
  single index/stage that every artifact class converts INTO and OUT of?
  A hub that mediates every pair is the god-calculus signature.
- Caveat both ways: a benign router with non-composable payloads can trip the
  screen (false positive — check whether the midpoints actually MATCH, per
  `index_connectivity_does_not_imply_derivability`); an evidence-only currency
  hub evades it (false negative — that's check #1's job).

## 3. Midpoint matching (`index_connectivity_does_not_imply_derivability`)

- Where two governance hops are chained on paper (A feeds B, B feeds C): does
  the artifact B *produces* actually match the artifact the second hop
  *consumes*, field for field? Index-level diagrams over-approximate; the
  composite is real only if the midpoint judgments match.

## 4. Provenance rooting (`eentail_iff_read_rooted`, `reliance_roots_in_provenance`)

- For each authority-bearing decision AG records: can the full evidence chain
  be enumerated back to *held* receipts (reads), with one evidence per hop?
  Anything that cannot be so rooted is being treated as derivable authority.
- Fluency check (F2): is any reliance decision rooted in a confidence signal
  rather than a claim-indexed provenance receipt? `Recall ⊬ Reliance`,
  `HighConfidence ⊬ MayRely` — the root must be provenance or an explicit
  assumption, nothing else.

## 5. Refresh and renewal (F1, `refresh_is_inexpressible`)

- Does any workflow "extend" or "refresh" a receipt's validity by
  transformation (re-signing, re-stamping, copying forward) rather than by
  acquiring NEW evidence? Formally inexpressible in the discipline —
  operationally, any such path is a laundering lane.
- Freshness ordering: does every consumer of aged evidence demand at least its
  required remaining validity (`use k` vs `ev r`, `k ≤ r`), or do any gates
  accept born-fresh evidence regardless of elapsed time?

## 6. Burden shedding (F3, `caveat_dropping_is_inexpressible`)

- Do caveats/flags/warnings attached to receipts SURVIVE every transformation
  step (summarization, promotion, relay, compaction)? Any pipeline stage that
  emits a cleaner artifact than it consumed is a caveat-dropping step.
- Caveat-blind demand (named unscreened attack): do any gates accept evidence
  WITHOUT reading its caveat field at all? Burdens are decorative wherever
  demand is caveat-blind.
- Acceptance policy: which gates accept which burdens (`use A`)? Reckless
  breadth of acceptance is consumer policy, not laundering — but it should be
  a DECISION, recorded, not a default.

## 7. Linearity (SEQ2/SEQ3, `one_receipt_cannot_license_two_discharges`)

- Are single-use authorities (tickets, grants, capacity units) consumed
  exactly once per use in the schema — and is the RECEIPT that discharges an
  obligation itself consumed (receipt book), or can one receipt discharge two
  obligations?
- Does linearaccountant's spendability thread match the linear read policy
  (every read consumes; residuals thread; nothing derives free —
  `linear_every_derivation_pays`)?

## 8. Checkpoint/compaction custody (G, `checkpoint_mints_nothing`)

- Do any summarization/compaction/retention jobs drop live obligations,
  unknown commits, refusal artifacts, or non-authorities? Does any compacted
  output contain anything the input lacked (minted resolution/closure)?
- Occurrence check: do duplicate live entries survive with multiplicity, or
  can N obligations collapse to one in a summary
  (`settlement_preserves_live_multiplicity`)?

## Reporting discipline

For each finding: name the schema element, the checklist item, the backing
theorem, and whether the finding is screen-grade (smell) or wall-grade
(the discipline says the path should not exist). File results in AG's own
loop, not here — this repo holds the shapes, not the estate's testimony.
