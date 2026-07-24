# Related work: nearest named structures and the deltas

Each core object in this repository has an established neighbor in the
literature. This page names the nearest one, what carries over, and what the
delta is — because "X with governed carriers" is a sharper and more checkable
claim than an unanchored invention, and because a reader who knows the
neighbor should not have to reverse-engineer the difference.

Two rules govern this page. The anchor is an orientation, not a lineage
claim: no entry asserts that a module embeds, extends, or improves the named
theory unless a theorem in the tree does that work. And the delta is the
content: where an entry says "unlike X," the difference is visible in the
Lean types, not in ambition.

## Evidence and judgment

- **`Witness` (claim-indexed, `Type`-valued evidence)** — nearest neighbor:
  proof objects under the Curry–Howard correspondence, and evidence in
  dependent type theory. What carries over: evidence is data, indexed by the
  exact claim it supports. The delta: derivability is not the only gate. A
  witness lives inside a `GovernedFamily` where standing, custody, and spend
  books are separate conditions a valid proof object does not satisfy by
  existing.
- **`Refusal` (structured non-admission)** — nearest neighbor: refusal sets
  in CSP testing theory (Hoare 1985; Roscoe), and typed error values in
  programming practice. What carries over: rejection is first-class semantic
  data, not the absence of success. The delta: a refusal here is
  claim-indexed native evidence returned by a total checker, with laws about
  what it blocks downstream — not a trace-semantics construct and not one
  universal error enum.
- **Hostile countermodels** — nearest neighbor: countermodel construction in
  model theory and the adversarial-example discipline in security proofs.
  What carries over: a failed implication is established by exhibiting a
  model, not by failing to find a proof. The delta: each countermodel is
  co-designed with its calculus so that the plausible neighboring premises
  survive and only the unjustified lift fails; the point is semantic
  separation, not refutation volume.

## Resources and lifecycle

- **`Spend` (one-use resources)** — nearest neighbor: linear logic
  (Girard 1987) and its resource reading. What carries over: some premises
  are consumed, and reuse is the bug. The delta: spend here is a
  family-native book — a permit moves from `availablePermits` to
  `usedPermits` in a specific instance — not a sequent-calculus discipline,
  and no embedding into linear logic is claimed.
- **`Obligation` (opened by action, discharged separately)** — nearest
  neighbor: deontic logic, specifically contrary-to-duty structures
  (Chisholm 1963) where an obligation persists after the act that should
  have discharged it. What carries over: "done" and "owed" are independent
  dimensions. The delta: obligations are type-level objects opened and
  closed by exact witnesses with instance-specific lifecycle laws
  (`commit_opens_exact_obligation`, `settlement_closes_exact_obligation`),
  not modal formulas over a preference ordering.
- **`BreakGlass`** — nearest neighbor: break-glass access control in the
  security literature (optimistic security, Povey 1999; break-glass policy
  models, Brucker–Petritsch 2009). What carries over: exceptional access is
  a designed path with after-the-fact accountability, not a policy bypass.
  The delta: the exceptional path is itself a bounded `GovernedFamily` —
  permit consumption, opened obligation, settlement, and an audit history
  that provably cannot be read back as ordinary or clean.

## Custody, provenance, and history

- **`Custody` (provenance-intactness books)** — nearest neighbor: data
  provenance in databases (provenance semirings, Green–Karvounarakis–Tannen
  2007) and the W3C PROV model. What carries over: where a thing has been is
  trackable structure. The delta: custody is a per-family predicate that
  witnesses must preserve, and the central public results are negative —
  custody does not create authority
  (`custody_does_not_grant_dynamic_authority`) — where provenance systems
  mostly answer positive queries.
- **Stored decisions and replay** — nearest neighbor: memoization and
  idempotency keys in systems practice. What carries over: decide once,
  reuse the record. The delta: the stored pair retains the native witness
  *or refusal*, and downstream projections are derived from that stored
  evidence rather than recomputed — re-deciding until the answer is
  convenient is one of the named failure shapes, not an optimization.

## Authority and transport

- **`Authority` and anti-minting** — nearest contrast: capability systems
  and the object-capability model (Dennis–Van Horn 1966; Miller 2006), which
  readers reach for first. What carries over: authority should be
  unforgeable within the model. The delta is the direction of definition:
  a capability *is* transferable authority, while here authority is
  *defined* as `Nonempty (Witness c)` with no alternative introduction rule,
  and the anti-minting theorem is semantic — at an exactly refuted index
  pair, no receipt-free function produces source-relative entitlement — with
  no cryptographic or transferability claim.
- **Governed Transport (`Span`, lifts, translation, reliance)** — the word
  "span" is used in its elementary sense; no categorical structure is
  claimed, and PJ bridges deliberately lack identity and composition fields.
  The nearest working contrast is refinement mappings and simulation
  relations (Abadi–Lamport 1991): those transport whole-behavior
  correctness, while a GT route transports one artifact under a
  certificate, and the target's decision to *rely* on it is a separate typed
  step that no route supplies for free.

## What the sweep discipline is

Since 2026-07-23 this repository's process requires naming the nearest
established structure when new formal work opens, and stating the
contribution as a delta against it (see
[`AGENTS.md`](../AGENTS.md#development-order-formalization-leads-code)).
Incubating work in the sibling research tree carries its sweep in its
charter; anchors graduate to this page when the work they anchor becomes
public. Prior art on this page is evidence for positioning — it neither
gates what may be formalized nor substitutes for the theorems.
