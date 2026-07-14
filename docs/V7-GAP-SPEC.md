# v7 Gap Spec — Artifact Authority Profiles

**Status: RATIFIED (operator, 2026-07-02),** with the §9 wording amendment
(failure-class grounds, not prior-art grounds) from the ChatGPT co-review.
Local v7 work authorized; slices admitted per §10 first. Drafted 2026-07-02
(Fable, from the operator's post-v6 direction; naming correction over the
earlier "Constellation Custody Protocol" draft — see §7).

## 0. The constitution (binding on every v7 slice)

- **No shared custody language.** The no-unifier result (2026-06-04: five
  fractured relational vocabularies; nothing composes for free) is this
  campaign's constitution, not its obstacle.
- **No master profile.** No profile kind may mediate every artifact
  conversion — the `UniversalCrossroads`/`MasterFree` screen family applies
  at the profile level.
- **No universal artifact authority schema.**
- **Only local artifact profiles plus paid pairwise bridges.**

The earlier name "Constellation Custody Protocol" is retired for release
purposes: "all projects speak the same custody language" is exactly the
sentence the corpus's antibodies exist to refuse (shared language → shared
hub → universal crossroads). It may survive as informal architecture prose;
it may not name a release or a Lean campaign.

## 1. Problem

Artifacts from different projects (NQ probe receipts, Porter courier
receipts, Continuity declaration exports, Claimdocs score receipts, AG
admission/refusal receipts) can LOOK interoperable — similar envelopes,
similar grammar, overlapping metadata. Profile compatibility does not imply
authority conversion. The laundering move v7 blocks: **an artifact valid in
its home project is treated as authority in another project because it
parses.**

## 2. Local profiles

A profile is an artifact kind's LOCAL declaration of what it can testify
to. Candidate fields (design surface, not schema):

- `artifact_kind`, `producer`
- `wlp_receipt_kind` (one field — see §6; the envelope is not the profile)
- `local_payload_schema`
- `stage_survived` (custody-ladder position)
- allowed local uses / forbidden uses
- residue / caveats carried (burden vocabulary, F3 lineage)
- `bridge_obligations_required` for any later-stage or cross-project claim
- explicit `non_authorities` (what this artifact must never be read as)

Profiles are specimens, not instances of a shared type in any semantic
sense: two profiles sharing field NAMES do not thereby share meanings.

## 3. Bridge obligations

Cross-profile movement requires a declared bridge obligation. Bridge
families may share obligation STRUCTURE (the bridge-obligation lattice:
families factor by obligation set, not vocabulary) without creating a
shared vocabulary or a master protocol. A bridge is paid, pairwise, and
explicit; its existence is a claim someone must custody.

## 4. Screens and theorem shapes (Lean lane, when admitted)

Target refusals, in the series' house shape (escalating negative results):

- `profile_does_not_compose_for_free` — profiles for A and B yield no
  authority profile for A→B without a bridge obligation.
- `no_master_profile` — no profile kind mediates every pair (the
  `MasterFree` screen lifted to the profile index).
- `cross_profile_conversion_requires_bridge` — every legal conversion cites
  a declared bridge obligation (rooted-evidence shape: bridges enter only
  by assumption, never synthesized).
- `profile_stage_noncollapse` — a stage-n profile does not authorize stage
  n+1 (custody-ladder noncollapse at the profile level).
- Conditional admissions from the resident escaped-animal ledger:
  - the **relation-promotion screen** (C3 audit 2026-07-02: closure-genus,
    still requiring a precise vocabulary-generic statement and overlap
    review) — v7 profiles supply a local instantiation, not permission to
    formalize the general screen.
  - a **multi-currency coverage screen** (below-universal-threshold
    portfolios acting as de facto universal currency) — name-early
    candidate; false-positive/false-negative analysis before promotion or
    generalization.

## 5. Lane split (binding)

- **Lean owns:** profile laws, non-collapse theorems, the master-profile
  screen, bridge-obligation structure, conversion refusals.
- **AG / constellation owns:** JSON receipt schemas, wire formats, actual
  AG/NQ/Porter/Continuity/Claimdocs artifact exchange, runtime admission
  gates.

Lean does not define the operational constellation; it proves the profile
discipline AG may later consume. Lean may establish those laws before AG
implements them; runtime correspondence remains AG-owned and separately
evidenced.

## 6. WLP: envelope, not semantics

WLP survives v7 as a **receipt envelope / causal-parent wire layer** —
shared syntax, never shared semantics. The safe slogan:

> All projects may carry receipts in WLP envelopes; no project inherits
> another project's semantics without a bridge.

WLP may be shared at the envelope layer (receipt kind, schema version,
issuer, subject, causal parents, hashes, clock basis, payload digest,
custody metadata, seal). WLP must NOT be shared at the semantic authority
layer (what a receipt authorizes, admissibility, bridge validity, profile
composition, boundary crossing).

Doctrine lines (candidate Lean shapes if a v7 slice touches them):

- `wlp_valid_does_not_imply_profile_authority`
- `wlp_parentage_does_not_imply_derivability`
- `wlp_signature_does_not_discharge_bridge_obligation`
- `same_wlp_kind_does_not_imply_same_authority_profile`
- `wlp_transport_does_not_imply_reliance`
- positive, narrow: `wlp_envelope_preserves_declared_payload_and_parent_digests`

WLP sits BELOW the profile in the stack (local event → local payload → WLP
envelope → local authority profile → explicit bridges). A customs form is
not citizenship.

## 7. Risks of unification laundering (why this spec is shaped this way)

- The original draft ("protocol/schema layer… projects speak the same
  custody language") is the god-calculus at the artifact layer; C3-classified
  against the resident kernel: `UniversalCrossroads` shape, refused.
- Residual risk inside THIS framing: (a) profile field names drifting into
  implied shared semantics — the §2 note is binding; (b) the
  bridge-obligation lattice being read as a vocabulary unifier — it factors
  obligations, not meanings; (c) WLP kind names being read as authority
  kinds — §6 lines refuse this; (d) a "profile registry" becoming a master
  index with conversion authority — a registry may enumerate, never mediate.

## 8. Non-goals

- No Constellation Custody Protocol as shared language.
- No master profile; no universal artifact authority schema.
- No runtime claims; no JSON schema implementation in the Lean lane.
- No AG/NQ/Porter integration built from this lane.
- No new screens minted without their own admission (relation-promotion and
  multi-currency remain gated as stated in §4).
- **No profile registry in this campaign.** A registry may enumerate, never
  mediate — and v7 does not build one at all; a registry is how the master
  index sneaks back in wearing a conference lanyard.

## 9. Admissibility verdict (drafting Fable's, non-binding)

**Admissible as a Lean campaign under this framing**, on three conditions:
(1) the constitution in §0 appears in every slice header; (2) the first
slice is the refusal skeleton (§10), not the profile schema — court first,
map later; (3) the wire/schema half is explicitly AG's from day one.

**Runtime correspondence target:** the first real cross-tool consumption event —
e.g. AG wanting to treat an NQ probe receipt as admission evidence, or
Claimdocs scores appearing in an AG decision basis. Such an event validates
the model but is not permission to formalize it; v7 can open on known
failure-class grounds:
parse-implies-authority is already named and caged as the minimal forbidden
specimen. Wire-schema fields remain runtime-owned; an explicitly abstract
formal profile may precede the real artifact.

## 10. Smallest first slice (when ratified)

One Scratch file: profile-indexed system with two artifact kinds + one
declared bridge; prove `profile_does_not_compose_for_free` and
`no_master_profile` for it; FORBIDDEN specimen = the parse-implies-authority
rule (artifact of kind A cited as evidence for a kind-B use with no bridge),
caught by the discipline or the closure genus; true minimal pair. Zoo
registry row on landing. Everything ≤ [propext, Quot.sound].
