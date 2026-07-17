/-
  Admissibility.PathVerdict.Core  --  Path Verdict, second stratum: refusal as data
  EXTRACTED 2026-07-02 from private skunkworks (formalization/Calculi/
  SeamPathVerdict/), Tier-1 extraction per that repo's publication posture
  table (Path Verdict core + edge fold/tether = the two "Yes" rows; Domains/
  Located are the noted second wave; everything Tier-0 — domain obstruction
  taxonomies, NQ/AG integration, MixedPipeline, weathering ledgers, linear
  spend, nightshift — stays private). Skunkworks provenance: multiple codex
  review passes there; recompiled and axiom-re-attested here on arrival.

  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: STABLE-SURFACE
  This module is part of the exact `LeanProofs.Admissibility.PathVerdict`
  stable root. v13 completes the earlier skunkworks extraction by correcting
  its public path and custody record without changing theorem bodies.

  TIER-1 SCOPE (brutal, binding on any public claim): this proves that
  obstruction is preserved across composition, that authority requires a
  zero-obstruction log, and that folds preserve the authority semantics of
  evaluated edges. It does NOT prove: that any real system emitted correct
  edge verdicts; that NQ/AG/Porter are correct; that an obstruction is
  morally bad or permanently tainted; that remediation is automatic; or that
  collection should be blocked.

  OVERLAP NOTE (C3 hygiene, checked at extraction): the verdict algebra
  (obstruction-log free monoid + fold/tether) is DIFFERENT MACHINERY from
  the resident custody-indexed sequents (derivability walls) and the
  jurisdiction screen (rule-shape inspection) — adjacent doctrine ("no
  laundering by composition"), disjoint proof objects. Any future bridge
  between the two is its own slice, not implied.

  the skunkworks first-stratum `PathVerdict` (private, not extracted) proves the pure judgment: an inductive `AuthorityBearing`
  whose dirty labels simply have no constructor. Correct, but absence-only — a
  downstream consumer learns "couldn't prove authority" and nothing else. That
  collapse (unlabeled edge / axiom seam / active refusal / Tuesday) is itself a
  laundering surface: the system shrugs "verification unavailable," and the
  cursed green dashboard is born.

  This module is the twin stratum:

    > **Refusal is data. Authority is proof. Composition must preserve both.**

  A `PathVerdict δ` is an accumulated obstruction log — the free monoid over
  `ObstructionKind δ`. Empty log renders clean; authority IS `obstructions = []`.
  No `clean | blocked` split: `blocked []` and `blocked [.bridge]` are garbage
  states we refuse to let Lean represent.

  The obstruction vocabulary splits into a **core kernel** (seam laws shared by
  every domain: unlabeled, axiomToken, sorryToken, refusedLaundering) and a
  **domain parameter** `δ` (NQ gets staleEvidence/retiredBasis, AG gets
  verificationFailed/rationCardExceeded, ...). Not a monolithic enum (junk
  drawer; someone adds `miscFailure`; we all go live in the sea) and not an
  unconstrained parameter (refusedLaundering becomes local folklore). No
  typeclasses: instance search hides exactly the boundary we are forcing into
  the receipt. The quiet part is said loudly in the exported term.

  Design constraints carried as doctrine:
  * `refusedLaundering` is failed admissibility, not moral impurity — repair is
    external (re-evaluate the edge under a richer witness context). The verdict
    algebra must not repair itself: self-healing admissibility is how the
    monster gets tenure.
  * Rendering nuance is policy; authority is invariant. Renderers can decorate;
    they cannot mint admissibility (`render_clean_iff_authority`).
-/

namespace Admissibility.PathVerdict

/-! ## Obstruction vocabulary -/

/-- The core obstruction kernel: seam laws, not domain failures. Shared
    doctrine across every instantiating domain. -/
inductive CoreObstruction where
  | unlabeled
  | axiomToken
  | sorryToken
  | refusedLaundering
deriving DecidableEq, Repr

/-- An obstruction is either core doctrine or domain vocabulary. The sum is
    explicit so the exported term physically carries which stratum was
    breached — `ObstructionKind.core .refusedLaundering` says the quiet part
    loudly. -/
inductive ObstructionKind (δ : Type) where
  | core   : CoreObstruction → ObstructionKind δ
  | domain : δ → ObstructionKind δ
deriving DecidableEq, Repr

/-! ## The verdict: a free monoid over obstructions -/

/-- A path verdict is nothing but its obstruction log. Clean is the empty log;
    there is no separate `clean | blocked` constructor pair, so `blocked []`
    cannot exist. The log is ordered: composition preserves the chronological
    transcript of where admissibility was breached. -/
structure PathVerdict (δ : Type) where
  obstructions : List (ObstructionKind δ)
deriving DecidableEq, Repr

/-- The identity verdict: no obstructions. -/
def PathVerdict.clean {δ : Type} : PathVerdict δ := ⟨[]⟩

/-- Composition accumulates obstructions in order. There is deliberately no
    case analysis here — no branch may inspect, drop, or repair the log. -/
def PathVerdict.compose {δ : Type} (p q : PathVerdict δ) : PathVerdict δ :=
  ⟨p.obstructions ++ q.obstructions⟩

/-- Authority is zero obstruction. Not a judgment with paid paths this time —
    a definitional equation, so the diagnostic artifact and the authority
    proposition cannot drift apart. -/
def PathVerdict.AuthorityBearing {δ : Type} (p : PathVerdict δ) : Prop :=
  p.obstructions = []

/-- Authority is decidable whenever the domain vocabulary is — the admission
    check a runtime performs (`obstructions.isEmpty`) is the real check, not
    an approximation of an undecidable ideal. -/
instance {δ : Type} [DecidableEq δ] (p : PathVerdict δ) :
    Decidable p.AuthorityBearing :=
  inferInstanceAs (Decidable (p.obstructions = []))

/-! ## Monoid receipts -/

theorem clean_compose {δ : Type} (p : PathVerdict δ) :
    PathVerdict.clean.compose p = p := by
  simp [PathVerdict.clean, PathVerdict.compose]

theorem compose_clean {δ : Type} (p : PathVerdict δ) :
    p.compose PathVerdict.clean = p := by
  simp [PathVerdict.clean, PathVerdict.compose]

theorem compose_assoc {δ : Type} (p q r : PathVerdict δ) :
    (p.compose q).compose r = p.compose (q.compose r) := by
  simp [PathVerdict.compose]

/-! ## Positive paid paths -/

/-- The clean verdict is authority-bearing. -/
theorem clean_authority {δ : Type} :
    (PathVerdict.clean : PathVerdict δ).AuthorityBearing := rfl

/-- **The two-way seal.** A composition is authority-bearing iff both parts
    are. Left-to-right is the bite (see the corollaries below); right-to-left
    is the boring "clean plumbing composes" direction. -/
theorem authority_compose_iff {δ : Type} (p q : PathVerdict δ) :
    (p.compose q).AuthorityBearing ↔
      p.AuthorityBearing ∧ q.AuthorityBearing := by
  simp [PathVerdict.AuthorityBearing, PathVerdict.compose]

/-! ## Negative no-laundering receipts -/

/-- Any obstruction in either segment survives composition (left segment). -/
theorem obstruction_survives_left {δ : Type} {p q : PathVerdict δ}
    {o : ObstructionKind δ} (h : o ∈ p.obstructions) :
    o ∈ (p.compose q).obstructions :=
  List.mem_append_left q.obstructions h

/-- Any obstruction in either segment survives composition (right segment). -/
theorem obstruction_survives_right {δ : Type} {p q : PathVerdict δ}
    {o : ObstructionKind δ} (h : o ∈ q.obstructions) :
    o ∈ (p.compose q).obstructions :=
  List.mem_append_right p.obstructions h

/-- One obstruction — any obstruction, core or domain — refutes authority.
    The proof is pleasingly dumb; the modeling is where the cleverness went. -/
theorem obstruction_blocks_authority {δ : Type} {p : PathVerdict δ}
    {o : ObstructionKind δ} (h : o ∈ p.obstructions) :
    ¬ p.AuthorityBearing := by
  intro hp
  have hnil : p.obstructions = [] := hp
  rw [hnil] at h
  cases h

/-- **The bank-account theorem, prefix half.** If the composed path is
    authority-bearing, the prefix already was. A clean suffix cannot sanitize
    a dirty prefix: depositing the cash does not legalize the copper wire. -/
theorem composed_authority_implies_prefix_authority {δ : Type}
    {p q : PathVerdict δ} (h : (p.compose q).AuthorityBearing) :
    p.AuthorityBearing :=
  ((authority_compose_iff p q).mp h).1

/-- **The bank-account theorem, suffix half.** A governor is formally
    forbidden from looking at `p.compose q`, seeing a locally sound `q`, and
    deciding to admit it — but equally, a sound prefix licenses nothing about
    the suffix. -/
theorem composed_authority_implies_suffix_authority {δ : Type}
    {p q : PathVerdict δ} (h : (p.compose q).AuthorityBearing) :
    q.AuthorityBearing :=
  ((authority_compose_iff p q).mp h).2

/-! ## Core-doctrine receipts

    Every obstruction blocks, so these are instances of
    `obstruction_blocks_authority` — but the core kernel earns named receipts:
    they are the shared law every domain imports, not local folklore. -/

/-- A refused-laundering seam survives composition on the left... -/
theorem refused_laundering_survives_compose {δ : Type} {p q : PathVerdict δ}
    (h : ObstructionKind.core CoreObstruction.refusedLaundering
          ∈ p.obstructions) :
    ObstructionKind.core CoreObstruction.refusedLaundering
      ∈ (p.compose q).obstructions :=
  obstruction_survives_left h

/-- ...and blocks authority wherever it lands. Refusal is failed
    admissibility, recorded; nothing downstream may quietly forget it. -/
theorem refused_laundering_blocks_authority {δ : Type} {p : PathVerdict δ}
    (h : ObstructionKind.core CoreObstruction.refusedLaundering
          ∈ p.obstructions) :
    ¬ p.AuthorityBearing :=
  obstruction_blocks_authority h

/-! ## Rendering is projection, not policy -/

/-- The dashboard view. Lean gets the algebra; humans get the string;
    everyone suffers appropriately. -/
def PathVerdict.render {δ : Type} : PathVerdict δ → String
  | ⟨[]⟩     => "clean"
  | ⟨_ :: _⟩ => "blocked"

/-- **Renderers cannot mint admissibility.** The rendered status is a strict
    projection of the verdict: "clean" appears iff authority actually holds.
    An operator cannot argue a claim is "mostly green" past this. -/
theorem render_clean_iff_authority {δ : Type} (p : PathVerdict δ) :
    p.render = "clean" ↔ p.AuthorityBearing := by
  obtain ⟨obs⟩ := p
  cases obs with
  | nil => simp [PathVerdict.render, PathVerdict.AuthorityBearing]
  | cons o rest =>
      simp only [PathVerdict.render, PathVerdict.AuthorityBearing]
      constructor
      · intro h; exact absurd h (by decide)
      · intro h; exact absurd h (List.cons_ne_nil o rest)

end Admissibility.PathVerdict
