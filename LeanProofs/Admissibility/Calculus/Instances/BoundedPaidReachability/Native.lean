/-
  Admissibility.Calculus.Instances.BoundedPaidReachability.Native  --  the
  minimal proof-relevant run/staged-state substrate

  EXTRACTED 2026-07-17 from private skunkworks
  (formalization/Calculi/Scratch/LawfulPaidReachability/Native.lean, the
  one-owner seam created by the rung-3 pre-transfer sanitation move) as
  part of rung 3 of the Admissibility Calculus promotion campaign.
  Operator-ratified 2026-07-17; recompiled and axiom-re-attested here on
  arrival. Normalized-source-equal to its private source after only the
  declared import, namespace, and comment substitutions.

  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: STABLE-SURFACE
  This module is part of the exact `LeanProofs.Admissibility.Calculus`
  stable root. Import-free below Lean core.

  CANONICAL-OWNERSHIP FREEZE (operator-ratified rung-3 native-API pin):
  publishing this module freezes public canonical ownership of the generic
  `Run` trace and the staged `Provenance`, `Resource`, `Warrant`, `State`,
  `Action`, and `Step` vocabulary — the actual native API, not merely the
  theorem name. The advertised theorem surface is exactly one receipt,
  `Staged.Run.occurrence_provenance` (footprint exactly `[propext]`); the
  membership helper is private so the surface stays at one theorem.

  The two edge classes are:

    pay    -- consumes one exact wallet occurrence and discharges it into
              the paid book.
    admit  -- consumes one exact warrant occurrence from the authority book
              and stages the granted resource into the wallet, stamped with
              the warrant's identity as provenance.

  Every enabling premise is an explicit occurrence split of the
  before-state, so no edge exists without its cited pre-state support, and
  `occurrence_provenance` shows every discharged occurrence traces to
  initial inventory or initially held authority.

  Deliberately NOT here (research tree only): occurrence counting,
  append/split trace utilities, per-edge inversion/frame/exactness laws,
  `no_admission_beyond_standing` (whose footprint includes `Quot.sound`),
  saturation, and every campaign module.
-/


namespace Admissibility.Calculus.Instances.BoundedPaidReachability

/-! ## Generic proof-relevant trace layer -/

section Trace

variable {State Action : Type} (Step : State → Action → State → Type)

/-- A lawful run: each hop carries its step receipt, and adjacent boundary
    states agree exactly by construction rather than by side condition. -/
inductive Run : State → List Action → State → Type where
  | nil {s : State} : Run s [] s
  | cons {s mid finish : State} {a : Action} {as : List Action} :
      Step s a mid → Run mid as finish → Run s (a :: as) finish

end Trace

/-! ## The concrete two-book staged calculus -/

namespace Staged

/-- Where a spendable occurrence came from: declared in the initial
    inventory, or staged by a named warrant.  Provenance is identity, not
    decoration: it is what stops basis migration from being erasable. -/
inductive Provenance : Type where
  | initial
  | admitted (warrant : Nat)
deriving DecidableEq, Repr

/-- One spendable occurrence.  The token is what an obligation wants; the
    provenance is which support admitted it. -/
structure Resource (Token : Type) where
  token : Token
  provenance : Provenance
deriving DecidableEq, Repr

/-- One unit of admission authority: the standing to stage exactly one
    occurrence of `grants`.  A warrant is not the resource it grants. -/
structure Warrant (Token : Type) where
  id : Nat
  grants : Token
deriving DecidableEq, Repr

/-- The three books.  They are deliberately separate: wallet is spendable
    inventory, warrants is admission authority, paid is discharged
    obligations.  No law below is allowed to collapse them. -/
structure State (Token : Type) where
  wallet : List (Resource Token)
  warrants : List (Warrant Token)
  paid : List (Resource Token)
deriving DecidableEq, Repr

/-- Action payloads are plain data, independent of any before-state. -/
inductive Action (Token : Type) where
  | admit (warrant : Warrant Token)
  | pay (resource : Resource Token)
deriving DecidableEq, Repr

/-- The only two lawful edges.  Each enabling premise is an explicit
    occurrence split of the before-state, so occurrence-exact consumption
    holds by construction and inversion is elementary.

    `admit` consumes one exact warrant occurrence and stages the granted
    token into the wallet, stamped with the consumed warrant's identity.
    `pay` consumes one exact wallet occurrence and discharges it into the
    paid book.  There is deliberately no edge that creates a warrant, pays
    a warrant, or stages a resource without consuming a warrant. -/
inductive Step (Token : Type) :
    State Token → Action Token → State Token → Type where
  | admit {s : State Token} {w : Warrant Token}
      {pre post : List (Warrant Token)}
      (held : s.warrants = pre ++ w :: post) :
      Step Token s (.admit w)
        { wallet := s.wallet ++ [⟨w.grants, .admitted w.id⟩],
          warrants := pre ++ post,
          paid := s.paid }
  | pay {s : State Token} {r : Resource Token}
      {pre post : List (Resource Token)}
      (held : s.wallet = pre ++ r :: post) :
      Step Token s (.pay r)
        { wallet := pre ++ post,
          warrants := s.warrants,
          paid := s.paid ++ [r] }

/-- Private membership support for the promoted provenance receipt: warrant
    membership only shrinks across any edge.  The residual private Core
    exports its own copy (`Step.warrant_mem_of_after`) for non-promoted
    consumers; keeping this one private keeps the promoted native theorem
    surface at exactly one receipt. -/
private theorem warrantMemOfAfter {Token : Type}
    {s s' : State Token} {a : Action Token}
    (step : Step Token s a s') {w : Warrant Token}
    (mem : w ∈ s'.warrants) : w ∈ s.warrants := by
  cases step with
  | admit held =>
      rw [held]
      rcases List.mem_append.mp mem with inPre | inPost
      · exact List.mem_append.mpr (Or.inl inPre)
      · exact List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ inPost))
  | pay held => exact mem

/-! ### Trace-level support identity -/

namespace Run

open Admissibility.Calculus.Instances.BoundedPaidReachability (Run)

/-- **Support identity.**  Every occurrence present in the final wallet or
    paid book either already existed in the initial books or is stamped
    with the identity of a warrant the initial state already held.  The
    basis of every discharged obligation is traceable to initial standing;
    a synthesized trace cannot silently swap support mid-flight. -/
theorem occurrence_provenance {Token : Type} {s finish : State Token}
    {as : List (Action Token)}
    (run : Run (Step Token) s as finish) (r : Resource Token)
    (present : r ∈ finish.wallet ∨ r ∈ finish.paid) :
    (r ∈ s.wallet ∨ r ∈ s.paid) ∨
      ∃ w, w ∈ s.warrants ∧ r = ⟨w.grants, .admitted w.id⟩ := by
  induction run with
  | nil => exact Or.inl present
  | @cons s mid finish a as step rest ih =>
      rcases ih present with inMid | ⟨w, held, stamped⟩
      · cases step with
        | @admit w pre post held =>
            rcases inMid with inWallet | inPaid
            · rcases List.mem_append.mp inWallet with inOld | inNew
              · exact Or.inl (Or.inl inOld)
              · refine Or.inr ⟨w, ?_, by simpa using inNew⟩
                rw [held]; simp
            · exact Or.inl (Or.inr inPaid)
        | @pay rPaid pre post held =>
            rcases inMid with inWallet | inPaid
            · refine Or.inl (Or.inl ?_)
              rw [held]
              rcases List.mem_append.mp inWallet with inPre | inPost
              · exact List.mem_append.mpr (Or.inl inPre)
              · exact List.mem_append.mpr
                  (Or.inr (List.mem_cons_of_mem _ inPost))
            · rcases List.mem_append.mp inPaid with inOld | inNew
              · exact Or.inl (Or.inr inOld)
              · refine Or.inl (Or.inl ?_)
                rw [held]
                have : r = rPaid := by simpa using inNew
                subst this
                simp
      · exact Or.inr ⟨w, warrantMemOfAfter step held, stamped⟩

end Run

end Staged

#print axioms Staged.Run.occurrence_provenance

end Admissibility.Calculus.Instances.BoundedPaidReachability
