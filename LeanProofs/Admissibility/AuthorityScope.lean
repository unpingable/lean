/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE

  Promoted from `LeanProofs/Scratch/AuthorityScope.lean` (2026-06-27): compiled,
  sorry-free, axiom-free, and public terminal evidence. Signatures are not part of
  the exact 1.0 compatibility claim. Provenance: scratch specimen first graduated
  to the former annex and is now classified honestly as public evidence so the
  scoped conversion receipt is citable as warrant where *standing* (a Boolean held at a
  decision instant) is converted into *authorized use* — anticipated at the point a
  standing layer and an indexer/Spine intersect, where the temptation is to read a bare
  "authorized" flag as a universal key.

  WHAT IS PROMOTED, AND WHAT IS ADDED AT PROMOTION:

    PROMOTED verbatim — the specimen and its existential anti-pope COUNTERMODELS
    (`wrong_useClass_/wrong_scope_/wrong_authority_/expired_/revoked_not_authorized`,
    `conversion_does_not_synthesize_eligibility`, `exact_match_authorizes`). Each refutes
    a specific laundering rule and shows the laws bite without being inert.

    ADDED — the UNIVERSAL anti-pope guarantee (`authorized_exact_match`): authorized ⇒
    the receipt matches on all five axes, is unrevoked, and unexpired. The scratch header
    flagged this as "a cheap follow-up, deliberately NOT added to keep this a faithful
    migration." That reason was migration fidelity — and it lapses at promotion. This seam
    is guarantee-typed: the existentials say "a mismatched receipt fails *somewhere*"; the
    universal says "an authorized crossing names *exactly* its scope, with no adjacent
    leak, conjunctively." Citing-as-warrant wants the universal. So it is added here.

  THE SPECIMEN — the conversion receipt, nailed down (anti-pope).

  A bare `AuthorizesUse : Bool` flag is a UNIVERSAL KEY: a receipt that authorizes
  everything is the exact laundering device a typed authority bridge exists to prevent —
  a tiny pope. This specimen demotes it. The conversion receipt is scoped on five axes —
  WHO (authority), WHAT eligible use (useClass), WHERE (scope), WHEN (expiry), and
  WHETHER it still stands (revoked) — and the anti-pope laws witness the receipt
  authorizes ONLY the exact crossing it names, nothing adjacent.

  Doctrine line (migrated): `AuthorizesUse` is a scoped conversion receipt from eligible
  standing to authorized use. It does not synthesize eligibility, does not generalize
  across use class / scope / time / authority state, and fails under revocation or expiry.

  Everything decidable and axiom-free (verified: every theorem depends on no axioms).

  Corpus placement: a sharp specimen of `SurfaceAuthorization` (authorizing *through* a
  surface ≠ the surface being a universal authority) crossed with the no-universal-key /
  no-laundering family. Sibling public-evidence faces: `Admissibility.DeferredWitness` (temporal
  — signed ≠ witnessed) and `Admissibility.PredicateWitnessSeparation` (projection —
  findability ≠ legitimacy). This is the *scope/conversion-receipt* face: a paid crossing
  authorizes exactly what it names. They do not subsume each other.

  Separate track from `ReachableDrift` — do not blur.
-/

namespace Admissibility.AuthorityScope

/-- What an authorized action is *for*. A promotion receipt is not an execution
    receipt; the ring does not transfer between use classes. -/
inductive UseClass | promotion | execution | rollback
  deriving DecidableEq, Repr

/-- The authority domain the receipt is good within. -/
inductive Scope | alpha | beta
  deriving DecidableEq, Repr

/-- The conversion receipt: `AuthorizesUse(p, α, σ)` made concrete. Carries the
    five scoping coordinates that keep it from being a universal key. -/
structure Receipt where
  authority : Nat        -- WHO issued / which authority is spent
  useClass  : UseClass   -- WHAT eligible use is converted
  scope     : Scope      -- WHERE it is good
  expiresAt : Nat        -- WHEN it lapses
  revoked   : Bool       -- WHETHER it still stands
  deriving DecidableEq, Repr

/-- A concrete request to act: a use of an authority, in a scope, for a class. -/
structure Request where
  authority : Nat
  useClass  : UseClass
  scope     : Scope
  deriving DecidableEq, Repr

/-! ## The scoped conversion judgment -/

/-- **AuthorizesUse** — the receipt converts an eligible judgment into authority
    for `req` at time `now` ONLY IF it matches on all five axes. The five-way
    conjunction is the whole anti-pope discipline; drop any conjunct and the
    receipt starts authorizing things it never named. -/
abbrev AuthorizesUse (r : Receipt) (req : Request) (now : Nat) : Prop :=
  r.authority = req.authority
  ∧ r.useClass = req.useClass
  ∧ r.scope = req.scope
  ∧ r.revoked = false
  ∧ now < r.expiresAt

/-- An item carrying (optionally) its conversion receipt — the refinement of
    `JudgmentFamilies.Item.authorityReceipt : Bool`. -/
structure ScopedItem where
  reliable         : Bool
  disqualifierOpen : Bool
  receipt          : Option Receipt
  deriving DecidableEq, Repr

abbrev Eligible (si : ScopedItem) : Prop :=
  si.reliable = true ∧ si.disqualifierOpen = false

/-- The crossing actually available to an item: it has a receipt AND that receipt
    authorizes the request. No receipt ⇒ no crossing (`none ↦ False`). -/
abbrev Converts (si : ScopedItem) (req : Request) (now : Nat) : Prop :=
  match si.receipt with
  | none   => False
  | some r => AuthorizesUse r req now

/-- Scoped `Authorized` — eligibility AND a matching conversion receipt. -/
abbrev Authorized (si : ScopedItem) (req : Request) (now : Nat) : Prop :=
  Eligible si ∧ Converts si req now

/-! ## The legitimate ascent (the paid crossing still works) -/

/-- The conversion theorem, scoped: eligible + a *matching* receipt ⇒ authorized. -/
theorem authorized_of_eligible {si : ScopedItem} {req : Request} {now : Nat}
    (he : Eligible si) (hc : Converts si req now) : Authorized si req now :=
  ⟨he, hc⟩

/-- Provenance: scoped authority still traces back to eligibility — no free entry. -/
theorem authorized_traces_eligible {si req now} (h : Authorized si req now) :
    Eligible si := h.1

/-! ## The anti-pope laws — the receipt authorizes ONLY what it names -/

/-- **Wrong use class** — a promotion receipt does not authorize an execution. The
    ring does not transfer between use classes. -/
theorem wrong_useClass_not_authorized :
    ∃ (r : Receipt) (req : Request) (now : Nat),
      r.useClass ≠ req.useClass ∧ ¬ AuthorizesUse r req now :=
  ⟨⟨0, .promotion, .alpha, 100, false⟩, ⟨0, .execution, .alpha⟩, 0, by decide, by decide⟩

/-- **Wrong scope** — a receipt good in `alpha` does not reach into `beta`. -/
theorem wrong_scope_not_authorized :
    ∃ (r : Receipt) (req : Request) (now : Nat),
      r.scope ≠ req.scope ∧ ¬ AuthorizesUse r req now :=
  ⟨⟨0, .promotion, .alpha, 100, false⟩, ⟨0, .promotion, .beta⟩, 0, by decide, by decide⟩

/-- **Wrong authority** — one authority's receipt does not authorize another
    authority's request. No cross-domain leak. -/
theorem wrong_authority_not_authorized :
    ∃ (r : Receipt) (req : Request) (now : Nat),
      r.authority ≠ req.authority ∧ ¬ AuthorizesUse r req now :=
  ⟨⟨1, .promotion, .alpha, 100, false⟩, ⟨2, .promotion, .alpha⟩, 0, by decide, by decide⟩

/-- **After expiry** — a matching receipt past its expiry authorizes nothing. -/
theorem expired_not_authorized :
    ∃ (r : Receipt) (req : Request) (now : Nat),
      r.expiresAt ≤ now ∧ ¬ AuthorizesUse r req now :=
  ⟨⟨0, .promotion, .alpha, 10, false⟩, ⟨0, .promotion, .alpha⟩, 10, by decide, by decide⟩

/-- **Revoked** — a revoked receipt, otherwise perfectly matching, authorizes
    nothing. -/
theorem revoked_not_authorized :
    ∃ (r : Receipt) (req : Request) (now : Nat),
      r.revoked = true ∧ ¬ AuthorizesUse r req now :=
  ⟨⟨0, .promotion, .alpha, 100, true⟩, ⟨0, .promotion, .alpha⟩, 0, by decide, by decide⟩

/-- **No retroactive eligibility synthesis** — the headline. A *perfectly valid*
    conversion receipt does NOT manufacture the eligible premise. Authorization
    consumes eligibility; it never produces it. So a fully-authorized crossing on
    an ineligible item is not `Authorized`: the receipt cannot launder standing
    into existence after the fact. -/
theorem conversion_does_not_synthesize_eligibility :
    ∃ (si : ScopedItem) (req : Request) (now : Nat),
      Converts si req now ∧ ¬ Eligible si ∧ ¬ Authorized si req now :=
  ⟨⟨false, false, some ⟨0, .promotion, .alpha, 100, false⟩⟩,
   ⟨0, .promotion, .alpha⟩, 0, by decide, by decide, by decide⟩

/-- The exact-match crossing DOES authorize — the laws above bite only on
    mismatch, not on everything (the receipt is scoped, not inert). -/
theorem exact_match_authorizes :
    Authorized ⟨true, false, some ⟨0, .promotion, .alpha, 100, false⟩⟩
               ⟨0, .promotion, .alpha⟩ 0 := by decide

/-! ## The universal anti-pope guarantee (added at promotion)

The countermodels above each refute one laundering rule. This is the conjunctive
statement they were sampling: an authorized crossing names EXACTLY its scope. No
mismatched, revoked, or expired receipt can ever sit under `Authorized`. This is the
form a consumer cites as warrant — "authorized" is never a universal key. -/

/-- **Authorized ⇒ exact match on all five axes.** From `Authorized si req now` the
    item carries a receipt, and that receipt agrees with the request on authority,
    use class, and scope, is unrevoked, and is unexpired. The contrapositive is every
    anti-pope law at once: any disagreement on any axis (or revocation/expiry) puts the
    crossing outside `Authorized`. -/
theorem authorized_exact_match {si : ScopedItem} {req : Request} {now : Nat}
    (h : Authorized si req now) :
    ∃ r, si.receipt = some r ∧
      r.authority = req.authority ∧
      r.useClass = req.useClass ∧
      r.scope = req.scope ∧
      r.revoked = false ∧
      now < r.expiresAt := by
  obtain ⟨-, hc⟩ := h
  cases hr : si.receipt with
  | none => simp only [Converts, hr] at hc
  | some r =>
      simp only [Converts, hr] at hc
      exact ⟨r, rfl, hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2⟩

/-! ## Doctrine -/

def doctrine : List String :=
  [ "a bare authorized flag is a universal key — a tiny pope; the conversion receipt is scoped on five axes",
    "authorized ⇒ exact match on who / what / where / when / whether (authorized_exact_match) — no adjacent crossing",
    "conversion consumes eligibility, never synthesizes it — no retroactive standing",
    "the paid crossing still works on exact match — scoped, not inert" ]

#eval doctrine

end Admissibility.AuthorityScope
