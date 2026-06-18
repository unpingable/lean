/-
  NQJudgments.Standing — standing-auto completeness vs operator-directed contract
  strengthening, and property (c): a green check does not authorize a new promise.

  Custody-Class: SCRATCH. SNAPSHOT (NQ state as-inspected 2026-06-18); discharges no
  NQ runtime; not imported by `LeanProofs.lean`. See `NQJudgments-SNAPSHOT-NOTE.md`.

  The Rosetta stone (two NQ receipts, 2026-06-18, same surface, classified apart):
    • Lane A / STANDING-AUTO: "mechanizes an EXISTING, documented, implemented
      promise ... No new guarantee." Authorized by class membership, no fresh
      operator approval.
    • OPERATOR-DIRECTED: "carries a contract-guarantee STRENGTHENING ... ADDS a
      promise to the public SQL contract ... outside standing-auto." Authorized by
      the operator naming the exact shape in-instruction.

  SCOPE OF WHAT IS PROVED HERE (repair, 2026-06-18): the governing rule
  "a green test does not launder an inadmissible DISPATCH" (loop-protocol.md) is the
  motivating doctrine, but the theorems in this file prove a NEIGHBOURING property:
  green ⊬ a new PUBLIC PROMISE (`green_check_not_new_promise`,
  `green_on_admissible_still_not_new_promise`). The inadmissible-DISPATCH form is NOT
  proved — it would need a `MayDispatch` gate (admissibility ∧ standing), which is
  out of this finite model's scope and deliberately not added. Read these theorems as
  the promise-creation slice of the non-composability, not the dispatch slice.
-/

import LeanProofs.Scratch.NQJudgments.Basic

namespace NQJudgments

/-! ## Standing-auto completeness mechanizes an already-promised contract -/

/-- **standing_auto_requires_already_promised** — Lane A only ever applies to a
    promise already on paper. It cannot manufacture a promise; it mechanizes one. -/
theorem standing_auto_requires_already_promised {c : Claim}
    (h : StandingAutoComplete c) : c.alreadyPromised = true := h.2

/-- **green_completes_already_promised** — the positive standing-auto lane: a green
    check on an already-promised contract IS authorized as completeness repair
    (under standing, no fresh operator approval). -/
theorem green_completes_already_promised {c : Claim}
    (hg : c.greenCheck = true) (hp : c.alreadyPromised = true) : StandingAutoComplete c :=
  ⟨hg, hp⟩

/-! ## (c) a green mechanical check does NOT authorize a new public promise -/

/-- **green_check_not_new_promise** — a passing mechanical check, alone, does not
    authorize creating/expanding a public promise. The green check is an evidence
    verdict; adding a promise is a standing/policy move requiring an operator
    directive. -/
theorem green_check_not_new_promise :
    ∃ c, c.greenCheck = true ∧ ¬ MayAddPublicPromise c :=
  ⟨⟨false, false, false, false, false, false, false, false, true⟩, by decide⟩

/-- **green_on_admissible_still_not_new_promise** — the sharper form: even a green
    check on a fully ADMISSIBLE claim does not authorize a new public promise. "A
    green test does not launder an inadmissible — or here, an unauthorized —
    dispatch." Admissibility + green ⊬ permission to strengthen the contract. -/
theorem green_on_admissible_still_not_new_promise :
    ∃ c, c.greenCheck = true ∧ AdmissibleWithScope c ∧ ¬ MayAddPublicPromise c :=
  ⟨⟨true, true, false, false, true, false, false, true, true⟩, by decide⟩

/-- **adding_a_promise_requires_directive** — universal: any addition of a public
    promise traces back to an operator directive. Naming ≠ authorizing; the green
    check never supplies it. -/
theorem adding_a_promise_requires_directive {c : Claim}
    (h : MayAddPublicPromise c) : c.operatorDirective = true := h

/-! ## The two activities are genuinely distinct -/

/-- **standing_auto_without_directive_adds_no_promise** — the core distinction: the
    loop may mechanize an existing promise under standing (green + already-promised)
    WITHOUT an operator directive, and in doing so adds no new public promise. The
    two lanes do not collapse into each other. -/
theorem standing_auto_without_directive_adds_no_promise {c : Claim}
    (_ : StandingAutoComplete c) (hd : c.operatorDirective = false) :
    ¬ MayAddPublicPromise c := by
  intro h
  exact Bool.noConfusion (h.symm.trans hd)

/-- **distinction_holds** — both directions, assembled: standing-auto can complete
    an existing promise with no directive and no new promise; strengthening a public
    promise always requires the directive. -/
theorem distinction_holds :
    (∃ c, StandingAutoComplete c ∧ c.operatorDirective = false ∧ ¬ MayAddPublicPromise c)
    ∧ (∀ c, MayAddPublicPromise c → c.operatorDirective = true) :=
  ⟨⟨⟨false, false, false, false, false, false, false, true, true⟩, by decide⟩,
   fun _ h => h⟩

end NQJudgments
