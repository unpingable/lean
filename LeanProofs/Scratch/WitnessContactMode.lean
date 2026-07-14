/-
  Custody-Class: SCRATCH  —  compile-is-contact only.

  A ToolTheory object — the witness-contact-mode separation. From the menagerie audit's
  candidate #2 (Witness-Contact Typology), reframed: NQ *implements* (wires real contact
  modes — pfSense declared-deny, gateway-vs-path, off-LAN vantage, CGNAT egress, TLS probe,
  resolver sampler), and refers to THIS Lean for the schema. This file PROVES the schema;
  it does not observe the wild. Intake ledger / NQ lane:
    ~/git/playground/wired/NQ-WITNESS-CONTACT-MODE-ATLAS.md

  THE SEAM: different kinds of contact do not testify to the same class of claim. Same
  nominal target, different contact mode, different admissibility — `contact_mode_flips_admissibility`.

  Not doctrine. Not discharge. Not build authorization. Not imported by LeanProofs.lean.
  The `Testifies` wiring below is a CANDIDATE schema; NQ supplies the real relation and the
  worldly specimens. Those specimens can establish runtime correspondence; ANNEX
  promotion is a separate custody decision. This file proves the shape is non-vacuous
  and that the mode-blind collapse launders it.

  Null/absence contact is NOT owned here — `missing ACK ≠ NACK / null ≠ verdict` lives in
  FailureCustodyDisposition.lean. This file owns only the POSITIVE mode distinctions.

  Self-contained (no imports). Check: cd ~/git/lean && lake env lean <abs path>.
-/

namespace ToolTheory.Scratch.WitnessContactMode

inductive ContactMode where
  | declared          -- config / report says X
  | path              -- packet / path behavior says X
  | externalVantage   -- off-LAN witness says X
deriving DecidableEq, Repr

inductive ClaimClass where
  | declaredIntent        -- what the policy is declared to be
  | pathBehavior          -- what the path actually does
  | externalReachability  -- whether the target is reachable from outside
deriving DecidableEq, Repr

/-- Candidate schema: which contact modes can testify to which claim classes. NQ supplies
    the real relation from the wild; this is the shape, not the census. -/
abbrev Testifies : ContactMode → ClaimClass → Prop
  | .declared,        .declaredIntent       => True
  | .path,            .pathBehavior         => True
  | .externalVantage, .pathBehavior         => True
  | .externalVantage, .externalReachability => True
  | _, _                                    => False

/-- A claim about a target, of a given class. -/
structure Claim (Target : Type) where
  target : Target
  cls    : ClaimClass

/-- A claim is admissible under a contact mode iff that mode can testify to its class. Note
    it reads `cls`, never `target` — the target is held fixed; the MODE moves. -/
abbrev Admissible {Target} (m : ContactMode) (c : Claim Target) : Prop :=
  Testifies m c.cls

/-- **contact_mode_flips_admissibility** — the seam. The SAME nominal target and claim,
    contacted two ways, is admissible under one mode and not the other: an external-vantage
    probe testifies to path behavior; a declared-config report does not. -/
theorem contact_mode_flips_admissibility {Target} (t : Target) :
    ∃ (c : Claim Target) (m₁ m₂ : ContactMode),
      Admissible m₁ c ∧ ¬ Admissible m₂ c :=
  ⟨{ target := t, cls := .pathBehavior }, .externalVantage, .declared, trivial, by simp [Admissible, Testifies]⟩

/-- The flip cuts BOTH ways — neither mode dominates; they testify to DIFFERENT classes.
    Declared testifies to intent but not path; external vantage testifies to path but not
    intent. -/
theorem contact_mode_flips_both_ways {Target} (t : Target) :
    (∃ c : Claim Target, Admissible .externalVantage c ∧ ¬ Admissible .declared c) ∧
    (∃ c : Claim Target, Admissible .declared c ∧ ¬ Admissible .externalVantage c) :=
  ⟨⟨{ target := t, cls := .pathBehavior },   trivial, by simp [Admissible, Testifies]⟩,
   ⟨{ target := t, cls := .declaredIntent }, trivial, by simp [Admissible, Testifies]⟩⟩

/-! ## Collapsed contrast — mode-blind contact -/

/-- The collapse: "it was contacted somehow" ⇒ admissible, ignoring the mode. -/
abbrev collapsedAdmissible {Target} (_m : ContactMode) (_c : Claim Target) : Prop := True

/-- Mode-blind contact admits exactly what mode-aware contact refuses: a declared-config
    report passed off as path-behavior testimony. -/
theorem collapsed_admits_what_real_refuses {Target} (t : Target) :
    collapsedAdmissible .declared { target := t, cls := .pathBehavior } ∧
    ¬ Admissible .declared { target := t, cls := .pathBehavior } :=
  ⟨trivial, by simp [Admissible, Testifies]⟩

def doctrine : List String :=
  [ "different kinds of contact do not testify to the same class of claim",
    "same target, different contact mode, different admissibility (contact_mode_flips_admissibility)",
    "the flip cuts both ways: declared ↛ path-behavior, external-vantage ↛ declared-intent",
    "collapse the mode and a config report launders into path-behavior testimony",
    "Lean proves the schema; NQ implements the wild relation and refers here" ]

#eval doctrine

end ToolTheory.Scratch.WitnessContactMode
