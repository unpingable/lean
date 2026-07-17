/-
  The proof-theory island -- public aggregator.

  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: STABLE-SURFACE
  Sequent-calculus specimens, Mathlib-free by build-graph enforcement (see
  lakefile.toml, lean_lib ProofTheory). Promoted out of Scratch 2026-07-06
  under the rule: WIRE AS SPECIMEN/LIBRARY, NOT AS DOCTRINE/KERNEL/UNIFIER.
  No governance kernel imports this module and none may; "admissible" here
  is literal Gentzen admissibility -- derivable-about, not derivable-in --
  the mathematical referent the governance vocabulary borrows from. The
  rhyme is acknowledged; the composition stays refused (no-unifier doctrine
  governs).

  Contents:
  - Specimen: single-succedent intuitionistic sequent calculus over
    membership-read List contexts; weakening/contraction/exchange from one
    monotonicity theorem (size-preserving), general identity derivable,
    CUT as a computable derivation transformer. Constructive; footprint
    <= {propext, Quot.sound}.
  - TextbookG3ip: multiset-faithful G3ip (erasing left rules over
    lists-quotiented-by-permutation), size-preserving admissible exchange,
    the size-nonincreasing inversion package, ADMISSIBLE CONTRACTION, the
    derivability equivalence with the Specimen, and cut/weakening/identity
    for textbook G3ip as transport corollaries.
  The separate `LeanProofs.ProofTheory.Evidence` root owns the executable
  axiom-print audit receipts.
-/

import LeanProofs.ProofTheory.MembershipG3.Specimen
import LeanProofs.ProofTheory.MembershipG3.TextbookG3ip
