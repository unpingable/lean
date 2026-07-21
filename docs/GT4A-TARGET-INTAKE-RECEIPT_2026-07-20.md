# GT-4A target intake receipt

Date: 2026-07-20

Disposition: **PASS — exact packet accepted for target qualification**

## Source authority

| Field | Exact value |
| --- | --- |
| custody activation commit | `71714265062e3b45092c4d79927dfe2ed77dc5fa` |
| activation tree | `71cb93395a369ce4305288e15b55eb724da0814f` |
| activation parent | `b8ba72ced2492e05e0fca09f156bae954a978461` |
| source disposition | `RATIFY-GT-4A-SOURCE` |
| source custody | `ACTIVE` |
| canonical scientific owner | `SKUNKWORKS-ONLY` |
| packet path | `formalization/gt4a-export-packet/` |
| packet-manifest SHA-256 | `203f1b54a02469160aee8771a109db77fb812b5bdecd0036c66d066db570d08a` |
| source archive SHA-256 | `99172d58b497e8ef4d3d5845f7528e96405ba9cfbcc07e292641a5b2003cd005` |

The activation's custody manifest and operator record bind these identities,
the exact packet blobs, ten stable leaves, twelve physical source modules,
704 compiled declarations, the namespace map, exclusions, and sixteen
transfer hostiles.

## Target base

| Field | Exact value |
| --- | --- |
| commit | `b4cafb3b36928d5ede6523a3bd90953430116ae7` |
| tree | `084036c01f97627b79f48b3f9fa1f285779162db` |
| parent | `ff491b808ebeab2a132d9ade46d234cf85dcfbe9` |
| pre-intake tracked worktree/index | clean |
| pre-intake target paths changed | none |

## Intake checks

- Extracted the packet directly from the fixed activation with `git archive`.
- Recomputed the 956-byte canonical manifest digest and all eleven
  SHA-256/byte-count/path rows; the payload totals 7,176,025 bytes.
- Required exactly the eleven payload files plus the two envelope files.
- Inspected the USTAR archive before extraction: twelve sorted, unique, safe
  regular-file members; mode `0644`; uid/gid zero; empty owner names; mtime
  zero; no traversal or duplicate member.
- Matched the archive path set to `source-blobs.tsv`.
- Recomputed every member's Git blob and matched both `source-blobs.tsv` and
  the file at the fixed activation revision.
- Confirmed the source-authorized stable set is exactly `Core`, `Coverage`,
  `Positive`, `Negative`, `Residue`, `Composition`, `Federation`, `Identity`,
  `Coherence`, and `CoverageRepair`.
- Confirmed `Hostile`, `CompositionHostile`, and the exact Identity hostile
  region are evidence, not stable imports.
- Confirmed C01, C02, C03, C04, instance adapters, campaign machinery, and
  source custody tooling are excluded. C03 remains
  `C03-EXCLUDE-PENDING-SEPARATE-GATE`.

No source scientific result was regenerated or improved during intake.

