# Release process

How a version of this repository becomes a citable release. Reader-facing
documents state release facts and link here; the mechanics live on this page
only.

## Order of operations

1. The tree is positioned as released: version, `date-released`, CHANGELOG
   entry, and README currency all state the release as fact.
2. The annotated tag and GitHub release are built on that tree.
3. The GitHub release creation — not the tag alone — mints the Zenodo version
   DOI and drives the deposit under concept DOI
   [10.5281/zenodo.20369489](https://doi.org/10.5281/zenodo.20369489).
4. The minted version DOI is recorded back into the tree afterward.

The tree leads the release. Zenodo archives the tree as-is, so the tree
carries the release date (an operator decision) but never a predicted version
DOI (a value Zenodo emits). A GitHub release does not by itself prove the
corresponding Zenodo version exists; each is verified independently.

## Verification notes

- Every release-gating check is a bare command whose exit code decides
  pass/fail; the full list is in [`AGENTS.md`](../AGENTS.md#verification).
- GitHub Pages renders `main`'s `README.md`. After a push, the rendered body
  and response headers are verified independently; a stale render is a cache
  fact, not a release fact.
- `git rev-parse HEAD` identifies the exact local source being built when
  reproducing any receipt.

Tags, GitHub releases, and Zenodo deposits are operator-only acts; see the
hard limits in [`AGENTS.md`](../AGENTS.md#hard-limits).
