/-
  Custody-Class: SCRATCH  —  compile-is-contact only.

  A ToolTheory object — one of the "four flavors of identity" (denial identity) from
  (papers) working/tooltheory/annex-sketch-pack.md sketch 2. The signed-denial witness is
  modeled as an opaque Bool field; real crypto (DNSSEC NSEC / signed `cannot_testify`) is
  substrate, deferred (see annex-sketch-pack + BFT plan) — this specimen proves only the
  separation, not a denial protocol.

  Not doctrine. Not discharge. Not build authorization. Not imported by LeanProofs.lean.
  Formalization does not wait on NQ. Under the current custody fence, promotion
  requires signed NQ `cannot_testify` witnesses as correspondence evidence plus
  operator review; those witnesses do not prove conformance alone.

  FORBIDDEN INFERENCE: "No positive answer arrived, so nonexistence is established."
  Silence (timeout / SERVFAIL / unsigned NXDOMAIN) is absence of information; signed denial
  is positive testimony under scoped authority. Sharpens ConsolidationDenial's silence line.

  Self-contained (no imports). Check: cd ~/git/lean && lake env lean <abs path>.
-/

namespace ToolTheory.Scratch.AuthenticatedDenial

structure Response where
  positiveAnswerArrived : Bool   -- a positive record came back
  signedDenialWitness   : Bool   -- authority-signed proof of absence, within validity window
deriving Repr

/-- Absence is admissible ONLY via an authority-signed denial witness — never from silence. -/
abbrev AdmissiblyAbsent (r : Response) : Prop := r.signedDenialWitness = true

/-- Silence ↛ denial: no positive answer with no signed witness is NOT admissibly absent.
    A timeout/SERVFAIL/unsigned-NXDOMAIN does not establish nonexistence. -/
theorem silence_not_denial :
    ∃ r : Response, r.positiveAnswerArrived = false ∧ ¬ AdmissiblyAbsent r :=
  ⟨{ positiveAnswerArrived := false, signedDenialWitness := false }, rfl, by decide⟩

/-- The paid path: a signed denial witness IS admissible absence (the seam is not inert). -/
theorem signed_denial_is_absence :
    ∃ r : Response, r.signedDenialWitness = true ∧ AdmissiblyAbsent r :=
  ⟨{ positiveAnswerArrived := false, signedDenialWitness := true }, rfl, rfl⟩

/-! ## Collapsed contrast — fold "no answer" into "absent" -/

structure Collapsed where
  positiveAnswerArrived : Bool
deriving Repr

def Collapsed.admissiblyAbsent (c : Collapsed) : Bool := !c.positiveAnswerArrived  -- collapse: silence = denial

/-- Collapse silence into denial and a timeout establishes nonexistence for free — the whole
    laundering the signed-denial discipline exists to refuse. -/
theorem collapsed_silence_means_denial :
    ∀ c : Collapsed, c.positiveAnswerArrived = false → c.admissiblyAbsent = true := by
  intro c h; simp [Collapsed.admissiblyAbsent, h]

def doctrine : List String :=
  [ "no positive answer ↛ established nonexistence — silence is absence of information",
    "signed denial is positive testimony under scoped authority; only it establishes absence",
    "the paid path works: an authority-signed denial within window IS admissible absence",
    "collapse silence into denial and a timeout becomes proof of nonexistence" ]

#eval doctrine

end ToolTheory.Scratch.AuthenticatedDenial
