# V15 DOI preparation record

Date: 2026-07-22

Status: **release metadata positioned; deposit and mint follow from this
tree**.

## The causal chain

The order is fixed, and getting it backwards is a recurring error:

1. **The tree is positioned as released.** Version, release date, changelog
   entry, and README currency all read as though the release has occurred.
2. **The tag and GitHub release are built around that tree.**
3. **The GitHub release creation — not the tag alone — mints the version DOI**
   and drives the Zenodo deposit.

The tree therefore *leads* the release; it cannot trail it. Zenodo archives
this tree, so whatever the tree says about its own release state becomes the
permanent record. A tree that hedges about being released deposits that hedge
forever.

## What may and may not be asserted

The distinction is **who produces the value**, not how certain it is:

- **The operator chooses it → assert it now.** Version `15.0.0`, title, and
  release date `2026-07-22` are operator decisions made true by releasing.
  `CITATION.cff` carries `date-released` before the tag, exactly as every
  prior release did — see `ff491b8` for the v14 precedent.
- **An external service emits it → never guess it.** The version DOI does not
  exist until Zenodo returns it. It must not be guessed, predicted, or copied
  from another release; it is recorded only after the deposit.

Applying the second rule to the first is the error this record previously
made: it withheld `date-released` on the theory that an unreleased tree must
not assert a release date, which inverts step 1 and leaves the tag with
nothing coherent to archive.

## Values

- Software-series concept DOI: `10.5281/zenodo.20369489`.
- Version: `15.0.0`.
- Title: **V15 — Cross-Calculus Atlas**.
- Subtitle: **Receipt-indexed correspondence without a shared bridge
  algebra.**
- Release date: `2026-07-22`.
- Version DOI: **unassigned until Zenodo mints it.**

The concept DOI is preserved because it identifies the software series, not a
v15 deposit. Tagging, creating the GitHub release, and recording the returned
version DOI remain operator acts; none is performed by this metadata commit.
