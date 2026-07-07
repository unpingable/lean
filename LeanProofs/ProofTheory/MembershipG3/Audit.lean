/-
  LeanProofs.ProofTheory.MembershipG3.Audit -- the DMV counter.

  Custody-Class: UNRATIFIED-CANDIDATE
  #print axioms receipts for every load-bearing name in the MembershipG3
  development. This module exists so the audit is part of the BUILD: the
  axiom footprint prints on every `lake build ProofTheory`, and drift is
  visible in CI logs, not in narrative.

  Expected footprint (2026-07-06 baseline):
  - monotone, weaken, contract, exchange, initGen, consistency,
    disjunction_property: NO axioms.
  - cut and everything downstream of well-founded recursion (explode,
    cutAppend, mp, the inversion package, contraction, the equivalence,
    cutT/weakenT): exactly [propext, Quot.sound] -- the standard core
    footprint of WF recursion.
  - NOWHERE: Classical.choice (the development is constructive), sorryAx.

  Honest phrasing rule (anti-pedantry-goblin clause): this development has
  ZERO USER AXIOM DECLARATIONS and the EXPECTED CORE FOOTPRINT ONLY. It is
  not "zero axioms" in the absolute Lean-kernel sense: `#print axioms cut`
  shows propext and Quot.sound, and saying otherwise would be exactly the
  kind of borrowed authority this repo exists to refuse.
-/

import LeanProofs.ProofTheory.MembershipG3.Specimen
import LeanProofs.ProofTheory.MembershipG3.TextbookG3ip

namespace LeanProofs.ProofTheory.MembershipG3

-- Specimen: structural package
#print axioms monotone
#print axioms size_monotone
#print axioms weaken
#print axioms weakenAppend
#print axioms contract
#print axioms exchange
#print axioms initGen
#print axioms explode

-- Specimen: cut and payoffs
#print axioms cut
#print axioms cutAppend
#print axioms cut_admissible
#print axioms consistency
#print axioms disjunction_property
#print axioms mp

-- TextbookG3ip: structural package
#print axioms exchangeT
#print axioms sizeT_exchangeT
#print axioms invAnd
#print axioms invOr
#print axioms invImp
#print axioms contractT

-- TextbookG3ip: equivalence and transported corollaries
#print axioms toDeriv
#print axioms toDerivT
#print axioms textbook_iff_membership
#print axioms cutT
#print axioms weakenT
#print axioms initGenT
#print axioms consistencyT
#print axioms disjunction_propertyT

end LeanProofs.ProofTheory.MembershipG3
