# GT-4A public compatibility receipt

Date: 2026-07-20

Disposition: **PASS — candidate compatibility established**

## Newly established target facts

- Target and source toolchain bytes agree at SHA-256
  `651c8accb402b0c071cd336e9d3dc0a55516b1bfb434ddc4801f14936785b1d2`.
- `lake build GovernedTransport GovernedTransportEvidence` completed with
  exit code zero (18 jobs).
- The built target environment contains exactly 704 packet-owned
  declarations: 460 stable and 244 evidence.
- Every declaration matches its exact target fully qualified name, owning
  module, kind, canonical universe parameters, normalized type digest,
  normalized body/value digest, declaration-content digest, and axiom set in
  the packet.
- Exact compiled axiom distribution: 679 axiom-free, 16 exactly `[propext]`,
  nine exactly `[Quot.sound]`, zero other or mixed sets, and zero
  `Classical.choice`.
- Stable closure is exactly the ten declared leaves and contains no evidence.
  Evidence closure is exactly the three evidence leaves plus nine stable
  dependencies.
- No new source contains `Calculi.Scratch`, Mathlib, campaign, stage,
  instance-adapter, C01, C02, C03, or C04 imports.
- `bash scripts/check-custody-classes.sh` passed at the candidate accounting:
  216 public sources, 115 stable, 100 evidence, one aggregate, twelve stable
  roots, and 142 ownership relations.
- `bash scripts/check-mathlib-free-targets.sh` passed: 26/26 registered public
  targets and 216/216 public sources are role-compatibly target-owned; both new
  targets are Mathlib-free and default-built.

## Inherited, not re-executed

GT-0 through GT-4A source campaigns, historical printed-receipt production,
source-side hostile science, prior release campaigns, downstream runtime
correspondence, and unrelated version builds were not rerun. Their relevance
is inherited only through the exact source packet and activation identities.

Compatibility is not runtime conformance, empirical validation, endorsement,
canonical ownership transfer, release, or publication.

