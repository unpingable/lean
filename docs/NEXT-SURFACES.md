# Next Surfaces — name-early register (post-v7)

**Status: CANDIDATE REGISTER, NON-BINDING.** Filed 2026-07-02 (operator +
ChatGPT noodling, Fable-audited against the resident corpus). A register
entry is a handle for review, not authorization to build. **No version
number past v8 is minted here**; entries carry labels. A label becomes a
version only when its forcing case actually arrives. The goblin stays in
the drywall.

Rule of the register (the forcing sentence): the next surface opens when
the object of analysis stops being *one artifact profile crossing one
bridge* and becomes *a set/registry/graph of profiles and receipts whose
combined coverage may launder authority*.

---

## NEXT-A: Portfolio Custody (the v8 favorite)

**Forcing case (the real one): kernel-AG admission packets.** AG receives
a packet — NQ witness receipt + Porter courier receipt + Claimdocs score +
AG review receipt + bridge receipts (+ WLP envelope parentage) — and asks:
*do these jointly fund this admission?* No single receipt is universal,
but the packet may collectively cover every gate. That is portfolio
territory, and it is the point where v8 stops being theoretical.

**OVERLAP DISCIPLINE (binding on the eventual gap spec — cite, don't
re-derive):** v7 slice 4 already split multi-currency into three faces and
settled two:
- coverage through DERIVATION: **closed** (`derived_evidence_covers_no_more`,
  zero-axiom — coverage is inherited, never minted);
- coverage through CUSTODY: **priced, not an attack**
  (`coverage_costs_receipts` — no bulk discount; broad paid custody is
  wealth, not forgery);
- coverage by DECLARATION: total form screened (`UniversalReceiptFree`);
  graded threshold rejected as FP-riddled.

So NEXT-A's genuine delta is NOT "portfolios might cover a lot" (settled).
It is **obligation-targeting and issuer accounting**:
1. a packet funds only its DECLARED obligation set, scoped to a specific
   admission target (`packet_coverage_funds_only_declared_obligations`);
2. UNUSED coverage does not become ambient authority
   (`unused_coverage_is_inert` — the packet is not a general-purpose
   wallet at the decision surface);
3. missing obligations produce a TYPED refusal naming the missing
   obligation, never "close enough" (the v6 CheckResult pattern applied to
   packets — much of the machinery exists);
4. ISSUER-LEVEL / provenance-correlated accounting (one basis acquiring
   coverage across many acquisitions) — the v7.x remainder named in the
   v7 ledger; needs a provenance model the current skeleton lacks.

**The packet decomposition (the thread, kept whole):** when a real
admission packet arrives, the five things that must be provable —
1. each receipt funds only its declared obligation (HAVE: the
   jurisdiction screen, v7 slice 3);
2. packet coverage is scoped to a SPECIFIC admission target — a packet is
   presented AGAINST a target obligation set, not as general standing
   (NEW: the targeting judgment);
3. unused coverage does not become ambient authority — what the packet
   could fund but was not asked to fund stays inert at the decision
   surface (NEW: the inertness wall; the anti-"lanyard" theorem);
4. parentage/envelope validity does not imply semantic derivability
   (WLP lane — NEXT-B's border, cite not build);
5. missing obligations produce a TYPED refusal naming the missing
   obligation, never "close enough" (the v6 `CheckResult` pattern lifted
   to packets: ok-with-obligation-coverage-map | refusal-with-missing-set).

Theorem-shape sketches (names candidate, not minted):
`packet_coverage_funds_only_declared_obligations`,
`unused_coverage_is_inert`, `packet_parentage_does_not_imply_admission`,
`missing_packet_obligation_returns_typed_refusal`,
`coverage_requires_obligation_partition` (the partition face: coverage
claims decompose per-obligation, no residue funds anything).

The dangerous move it blocks, in one line: *packet covers enough local
gates ⇒ packet is generally admissible* — the artifact-layer god-calculus
wearing a lanyard.

**Lane split:** the packet SPECIMEN comes from AG-Claude (a real admission
packet shape, not an invented one); Lean owns the coverage/targeting
refusal laws. Do not invent AdmissionPacket fields in the Lean lane.

**Title candidates:** "Portfolio Custody" (proof-theory face) /
"Admission Packet Coverage" (AG-forcing face) /
"Coverage-Limited Authority".

---

## NEXT-B: WLP Envelope Graph Noncollapse

**Forcing case:** WLP parent graphs actually entering the Lean proof
surface — and nothing else. Do not wake it for fun; it bites.

Content is already fully named in V7-GAP-SPEC §6 (envelope-not-semantics;
the five non-collapse lines + the one narrow positive:
`wlp_envelope_preserves_declared_payload_and_parent_digests` — that is
WLP's whole job; important, not emperor). The graph-level additions when
forced: `wlp_parent_graph_does_not_imply_profile_derivation`,
`wlp_envelope_validity_does_not_imply_bridge_validity`,
`same_wlp_kind_does_not_imply_same_authority_profile`. Working title if
it ever versions: "Envelope Graph Noncollapse."

The stack position (from the gap spec, repeated because it is the whole
safety argument): WLP sits BELOW the profile — local event → local
payload → WLP envelope → local authority profile → explicit bridges. A
customs form is not citizenship. The safe slogan: *all projects may carry
receipts in WLP envelopes; no project inherits another project's
semantics without a bridge.*

**Overlap note:** parentage-vs-derivability is the derived-relations /
jurisdiction genus one level down (an edge in the parent graph is a
RELATION; relations need their own witnesses — the caught animal's home
turf). The eventual spec should check whether the jurisdiction screen
instantiates over envelope vocabularies before minting anything new.

---

## NEXT-C: Compiled Authority Checker Boundary

**Forcing case:** AG actually wanting to CONSUME checker output (not Lean
wanting to emit it). Until then, v6's boundary holds: Lean-native finite
decision procedure, kernel evaluation only, no interface authority.

When forced, the boundary spec (not necessarily pure Lean): what Lean
proves (`compiled_checker_sound`, `compiled_checker_refusal_correct`,
`bridge_instance_validity_is_checker_derived`), what runtime may execute,
what runtime must NOT claim (`signature_does_not_imply_semantic_validity`
— the doctrine line already exists as *timestamp-signed ≠
timestamp-witnessed*). The smallest runtime prototype shape, per the old
ToolTheory roadmap: artifact + requested use + compiled schema → judgment
or typed refusal. Likely shape: Lean spec + AG/Rust executable witness.
This is the first entry that is explicitly NOT a Lean-lane-only object,
and the boundary question is the v6 naming decision replayed one level
up: Lean-native decidability vs operational checker interface — the v6
answer (name it for what it is, non-claims for the rest) is the template.

---

## NEXT-D: Artifact-Authority Model / Semantics (paper-only lane)

**Forcing case:** wanting the formal note — "what model are these indexed
sequents sound for?" Theorem shapes:
`soundness_against_artifact_authority_model`,
`noncollapse_valid_in_model`,
`bridge_obligation_semantics_preserve_locality`. Academically chewy, a
known time sink, deprioritized by standing decision (chewy-list audit
2026-07-02). Venue posture if ever opened: Zenodo-grade formal note, NOT
a cs.LO submission ambition. This is the only entry with no laundering
move to block — it is legibility work, and it competes with paper-lane
time, not Lean-lane time.

---

## Likely order (sketch, not schedule)

If the forcing cases arrive in their natural order:

    v8 (when kernel-AG brings a packet)  = NEXT-A Portfolio Custody
    later, only if WLP enters the surface = NEXT-B Envelope Graph Noncollapse
    later, only if AG consumes checker output = NEXT-C Checker Boundary
    eventually, paper lane = NEXT-D Model / formal note

But the register is not a queue: an entry opens when ITS forcing case
arrives, not when its predecessor closes. If AG consumption arrives
before packets do, NEXT-C jumps the line. No entry opens on Lean theorem
momentum alone — with one standing exception: **the operator may open an
entry by decision** (the v6 precedent: opened by ratified gap spec, not
by disaster; not every next step needs a forcing event, it needs an
admission). What the register actually forbids is opening one by DRIFT —
sliding into a surface mid-session without a spec. If future-you wants
NEXT-A before AG brings a packet, the price is the same as ever: gap spec
first, overlap discipline cited, synthetic specimen labeled synthetic.

## Provenance

Operator + ChatGPT roadmap noodling, 2026-07-02 (same day v7 spine
completed); Fable overlap-audited against the resident corpus before
filing — in particular NEXT-A's overlap discipline against v7 slice 4's
three-face split, and NEXT-B's derived-relations kinship. ChatGPT's
instinct to defer implementation was kept; its instinct to defer NAMING
was overruled by the operator (name early, ratify lazily — this file is
the naming).

## What none of these are

Not Bridge Foundry. Not the Constellation Custody Protocol. Not JSON
schemas. Not "all tools exchange artifacts now." Runtime gets a version
only when forced by a real AG/NQ/Porter integration need, never by Lean
theorem momentum.
