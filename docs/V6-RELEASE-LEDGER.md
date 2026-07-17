# v6 Release Ledger — Finite Custody Checking

> **Historical record.** The Scratch paths/labels below describe the v6 tree.
> v13 rehomes the unchanged released checker under
> `LeanProofs/CustodyIndexed/`. See
> [`V13-RELEASE-LEDGER.md`](V13-RELEASE-LEDGER.md).

**Release: v6.0.0 — Finite Custody Checking** (*A Lean proof release for
custody-aware authority semantics*). Umbrella: Custody-Aware Authority
Semantics. Prior release: v5.0.0 — Custody-Preserving Normalization.

**The v6 claim (scoped, exact):** for the liberal/linear normalization
skeleton, finite read demands over finite contexts are **checked by a
Lean-native function** returning a typed result — `ok` with a positional
occurrence trace, or a typed **refusal naming an offender** — and the checker
is **sound and complete** for that skeleton: `ok` implies a valid linear
derivation over the given context (with the trace's labels exactly the read
spine, position-distinct, and every trace entry an occurrence of the given
context), refusal implies the offender's total demand genuinely exceeds
supply, and sufficient counts on the finite read support imply acceptance.
The verdict is decided by **finitely many count comparisons** over the read
spine (`firstDeficient_decides_check` + `support_covers_iff_all_covers`) —
the executable finite-support boundary v5 explicitly left unclaimed.
Underneath it, **traced and untraced normalization provably agree**: same
success/failure verdicts, the SAME offender on refusal, residuals equal up to
label projection — tracing is testimony about payment, never a change to who
gets paid (`tracing_preserves_verdicts`). The canonical tagging bridge lifts
any untraced run to a traced run at zero semantic cost. The resident C2
screen layer (`DecidableScreens`) is part of this release surface: every v4
screen has an executable Bool form with a soundness iff against the Prop
screen — screening as computation, soundness as theorem.

**The name:** "Finite", not "Executable" or "Decidable" — the release ships a
Lean-native finite decision procedure with kernel-evaluation demos; it ships
no CLI, no runtime interface, and no literal `Decidable` instances for the
checker (the screen layer's `decide`-based verdicts are its own scoped
mechanism).

**The v6 non-claims (binding on release notes):**
- **Not a CLI, not a runtime checker, not Bridge Foundry, not an artifact
  profiler** — proof discipline only; enforcement and interfaces are the
  NQ/AG lane.
- **Not a derivability decision procedure** — the checker checks a GIVEN
  liberal tree against a context (payment for its reads); it does not search
  for trees, and `Entail`/`EEntail` derivability is not decided.
- **Not a checker for arbitrary or future structural systems** — scoped to
  the current liberal/linear skeleton; node-form linear structural rules and
  a general structural-rule algebra remain named follow-up.
- **Not a master admissibility layer** — nothing in v6 issues authority; the
  checker's `ok` is relative to the resident v5 normalization semantics, no
  more.
- **Offender identity across reporters is NOT claimed** — the traversal
  checker and the counts-only decider may name different offenders (worked
  example in the file header, codex-verified); each offender is separately
  proved a genuine excess witness. Same-offender coherence IS claimed (and
  proved) between traced and untraced normalization.
- Tracing coherence is proof-machinery agreement between THIS twin pair, not
  a claim that instrumentation is semantically inert in general.

**Custody:** all v6 modules are `Custody-Class: SCRATCH` — fenced, not
promoted kernel authority — CI-covered under the `CustodyIndexedSequents`
build target (build coverage ≠ promotion). `LeanProofs.lean` imports none of
them.

**Verification basis:** every module compiles clean (exit-code receipts under
`.governor/verify_receipts/`); zero `sorry`/`admit`/`native_decide`; axiom
footprints attested via `#print axioms` on every new theorem (all ≤
`[propext, Quot.sound]`; several zero-axiom; **no `Classical.choice`
anywhere** — a binding prohibition of the admitted gap spec, swept and
clean). Adversarial audits (codex) per slice: slice 1 first-pass GREEN;
slice 2 first-pass GREEN with its one improvement note (public trace
provenance) closed same-slice. Trail: `.governor/loop.json` +
`docs/CHANGELOG-scratch-campaign.md`.

## The modules

| Module | Load-bearing results | Axioms |
|---|---|---|
| `DecidableScreens` (C2, resident — claimed into the v6 surface) | `DecSystem` (finite Boolean rule table + enumerations); executable screens `universalStampB` / `evidenceCurrencyFreeB` / `crossBridgeB` / `substantiveB` / `universalCrossroadsB` / `masterFreeB`, each with a **soundness iff** against its Prop screen; zoo demos DECIDED by kernel `decide` (hub fails `MasterFree`, sink passes, stamp system fails `EvidenceCurrencyFree`) | kernel `decide` only; no native_decide |
| `TracedCoherence` (v6 slice 1) | **`linearizeT_ok_projects`** / **`linearizeT_forgery_projects`** (traced verdicts project, offender intact); `linearizeT_ok_iff_linearize_ok` / `linearizeT_forgery_iff_linearize_forgery` (the verdict iffs); **`tracing_preserves_verdicts`** (no new accepted/rejected cases); `trace_refines_untraced_run` (residual = label projection, trace labels = read spine); the canonical tagging bridge `tagFrom`/`tagged` + `tagged_unambiguous` + **`untraced_runs_trace_canonically`** (every untraced run lifts, position-distinct trace) — coherence holds over ANY tagged context, no unambiguity hypothesis | ≤ [propext, Quot.sound] |
| `FiniteSupportChecker` (v6 slice 2) | `CheckResult` (ok trace \| refusal offender — no bare Bool on the final surface); `Core.check` (tagged) / `Core.checkCtx` (plain context via the tagging bridge) / `firstDeficient` (counts-only decider, no derivation built); **`check_ok_sound`** / **`checkCtx_ok_sound`** (ok ⇒ valid linear `Deriv` over the given context + read-spine trace + position-distinctness); `checkCtx_trace_entries_from_context` (trace provenance); **`check_refusal_excess`** / `checkCtx_refusal_excess` / `check_refusal_offender_demanded` (refusal ⇒ real excess, genuinely demanded); **`check_complete`** (sufficient counts ⇒ accept: a decision procedure, not a semi-decision); **`firstDeficient_decides_check`** + `support_covers_iff_all_covers` (THE FINITE-SUPPORT DECISION THEOREM); kernel-evaluation demos (paid tree ok with exact trace; free contraction refused; counts decider agrees) | ≤ [propext, Quot.sound] |

## The slogans (theorem-shaped, carried in the files)

- *Normalization cannot forge payment* (v5, inherited).
- *Tracing is testimony about payment, never a change to who gets paid.*
- *Labels explain what was read; occurrence traces prove who paid* (v5,
  now checker-surfaced).
- *Finite checking decides whether payment exists.*
- *Screening as computation, soundness as theorem.*

## Operator acts (not Claude's)

Push the `v6.0.0` tag and author the GitHub release (release creation mints
the DOI), using the claim + non-claims above as the release-note boundary.
The tag exists locally (operator-authorized 2026-07-02); `main` may continue
past it — the tag pins the release surface.
