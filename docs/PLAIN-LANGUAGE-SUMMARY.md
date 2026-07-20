# Plain language summary

**This project investigates a calculus for governed change.**

Many real systems must decide not only *what* may change, but *whether*
that change is justified. This project models that question directly,
using explicit notions of evidence, authority, standing, custody,
obligations, and lawful state transitions. Rather than assuming complete
information, it is designed to reason about action under bounded
knowledge: what may be concluded, what remains unknown, what further
inquiry is admissible, and what obligations remain outstanding.

The Lean formalization machine-checks the stated laws under their disclosed
definitions, hypotheses, and axiom footprints. It is not an implementation of
a particular application, and it is not a theorem-proving exercise for its own
sake: it is a candidate verified foundation intended to support systems such as
operational tooling, governed inquiry, and other evidence-driven workflows.
The Lean is the medium, not the subject.

## Why?

Modern systems often fail not because they lack automation, but because
they cannot distinguish justified action from unjustified action. This
project explores whether that distinction can itself be made explicit
and mechanically verified.

A few recurring failure shapes motivate the work, and each has a formal
counterpart here:

- **Laundering** — an assertion acquires authority it never earned by
  passing through a conversion, summary, or crossing that quietly drops
  the evidence trail. The calculus makes such conversions unrepresentable
  or proves them refused.
- **Stale reliance** — evidence ages out of its license to testify, but
  downstream consumers keep leaning on it. Staleness is modeled as a
  licensing judgment, deliberately distinct from falsity.
- **Endpoint judgment** — a system approves a state because it *looks*
  settled, without asking whether any lawful history could have produced
  it. Several theorems here prove that no endpoint-only check can be a
  faithful judge of lawful history.
- **Re-deciding until convenient** — a checker is invoked repeatedly
  until it yields the desired answer. The crossing layer proves a
  discipline of deciding once, storing both native outcomes, and
  deriving everything downstream from the stored decision.
- **Exceptional-path laundering** — emergency or break-glass authority
  leaks into ordinary authority, or settlement quietly cleans an audit
  trail. The terminal instance proves these separations hold even under
  hostile substitution of origins, labels, and histories.

## What the formal corpus is

The public corpus grew from individual constructions — evidence
weathering, paid recomposition, custody-indexed sequents, judgment
orientation, path verdicts — toward an identifiable research program:
an indexed governed-family calculus in which named families expose their
claims, witnesses, refusals, and books through one shared signature, with
exact (loss-accounted) encodings, indexed comparisons, and composition that
provably cannot mint authority.

The breadth is meant to emerge from the worked examples rather than from
the claims. Every theorem's assumptions are disclosed (the repository is
axiom-classified, not axiom-free), every promoted surface carries its
custody history, and every boundary the formalization does *not* cross —
runtime conformance, attestor honesty, cryptographic claims — is stated
as an explicit nonclaim rather than left to inference. That nonclaim is not a
waiver: a runtime claiming correspondence must declare its exact scope, supply
an exact correspondence map, executable preservation and transport evidence,
and revision-bound qualification receipts showing that every required
distinction survives. A formal refinement proof does not waive those
artifacts.

## Where to go next

- [`WHAT-THIS-PROVES.md`](../WHAT-THIS-PROVES.md) — the technical
  claim-by-claim statement of what the stack proves and rules out.
- [`CLAIM-REGISTER.md`](../CLAIM-REGISTER.md) — the audited claim
  ledger (SOUND / BROKEN / STALE / OPEN), including the v14 campaign
  entries.
- [`V14-READINESS-LEDGER.md`](V14-READINESS-LEDGER.md) — the seven-rung
  Admissibility Calculus promotion campaign, rung by rung, with
  verification receipts.
- [`V14-RELEASE-LEDGER.md`](V14-RELEASE-LEDGER.md) — the released v14
  inventory, current custody accounting, and scope fence.
- [`LeanProofs/Admissibility/README.md`](../LeanProofs/Admissibility/README.md)
  — the module-by-module kernel reference.
