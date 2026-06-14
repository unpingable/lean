/-
  Custody-Class: SCRATCH

  NoUniversalRoot — fenced scratch slice, 2026-06-14. Not imported by
  `LeanProofs.lean`. Not part of any 1.0 surface. No paper anchor. No
  promotion path. NOT used as discharge for any doctrine. Compile-is-
  contact only.

  ## The theorem — the publishable observer result

  The capstone of the observer foundation. The clean mathematical form:

      A consumer-relative force field has no consumer-independent section
      unless all consumers agree.

  ("Section" in the bundle sense: a single `GlobalForce : Artifact → Prop`
  that reproduces `Force c` for every consumer `c`. A tiny category-theory
  ghost — a global section of the force bundle — but elementary to prove.)

  The mathematical center (`has_global_section_iff_consumers_agree`):

      A consumer-independent force predicate exists IFF all consumers agree
      on every artifact. Disagreement on even one artifact is exactly what
      destroys the global section.

  Results, abstract over any `Force : Consumer → Artifact → Prop`:

    - `has_global_section_iff_consumers_agree` — the center. Section ⇔
      agreement.
    - `no_global_section_when_consumers_disagree` — the no-go corollary:
      two consumers disagreeing on one artifact ⇒ no global section.
    - `stamped_disagreement_refutes_absolute_stamp` — a stamped artifact
      some consumer honestly refuses kills the absolute-stamp bridge
      (`AbsoluteForceStampBridgePrice`, slice 3) at full generality.
    - `universal_root_licenses_stamp` — the positive exception for
      closed/rooted systems: a universal root licenses AN honest stamp, the
      root-tracking one (`Stamp = Force root`). NOT the only sound stamp —
      smaller stamps, including the empty stamp, are also sound.

  Empty-root caveat (the raccoon ChatGPT found). `UniversalRoot` means
  "every consumer accepts everything the root forces," so a root that
  forces NOTHING is vacuously universal — and licenses only the empty stamp
  (sound, useless). Hence the file name "NoUniversalRoot" is shorthand: the
  precise claim is that an open consumer world has no *forcing* root that is
  universal for a *disputed* artifact
  (`no_forcing_root_for_disputed_artifact`), NOT that no universal root
  exists at all. The genuine no-go is the agreement iff, not the root.

  ## Why this matters for the corpus (and agent_gov)

  agent_gov's "qualified operator" is exactly a genesis root — the single
  consumer all others factor through, where No-Negative-Clearance bottoms
  out in a human. `universal_root_licenses_stamp` says: single-rooted, an
  absolute operator stamp is legitimate. `no_global_section_when_consumers
  _disagree` says: federate agent_gov, introduce a consumer that does not
  share the root, and the stamp loses its global section — the observer
  axis reopens. The concrete `no_forcing_root_for_disputed_artifact` below
  shows that in an OPEN consumer world (one that contains a consumer
  recognizing nothing) no root that forces the disputed artifact is
  universal — the only universal root is the empty one, which licenses
  nothing. Single-root is a property of a closed world, not a fact of the
  artifact.

  ## Standalone

  Abstract theorems are universe-polymorphic over `Force`. The concrete
  capstone uses a local list-recognized model (re-stated, not imported).

  ## Sequence (observer foundation, slice 4 of 4 — capstone)
    1. ConsumerRelativeFreshness
    2. ConsumerRelativeForce
    3. AbsoluteForceStampBridgePrice
    4. NoUniversalRoot                 ← this file

  ## Prior art (read-only, not imported)
    - LeanProofs/Scratch/AbsoluteForceStampBridgePrice.lean  (the bridge this bounds)
    - LeanProofs/Scratch/OperatorBasisGateInput.lean         (qualified-operator = genesis root warrant)
-/

namespace Admissibility.Scratch.NoUniversalRoot

universe u v
variable {Consumer : Type u} {Artifact : Type v}

/-! ## Abstract layer — generic over any consumer-indexed force -/

/-- A consumer-independent "section" of the force bundle: a single
    artifact-level predicate that reproduces every consumer's force
    verdict. -/
def HasGlobalSection (Force : Consumer → Artifact → Prop) : Prop :=
  ∃ G : Artifact → Prop, ∀ (c : Consumer) (a : Artifact), G a ↔ Force c a

/-- All consumers agree: every pair of consumers gives the same force
    verdict for every artifact. -/
def ConsumersAgree (Force : Consumer → Artifact → Prop) : Prop :=
  ∀ (c d : Consumer) (a : Artifact), Force c a ↔ Force d a

/-- `c` factors through `root`: whatever forces `root` forces `c` too
    (root's force propagates down to `c`). -/
def FactorsThrough (Force : Consumer → Artifact → Prop) (c root : Consumer) : Prop :=
  ∀ a, Force root a → Force c a

/-- `root` is a universal root: every consumer factors through it. -/
def UniversalRoot (Force : Consumer → Artifact → Prop) (root : Consumer) : Prop :=
  ∀ c, FactorsThrough Force c root

/-- The absolute-stamp bridge (re-stated from slice 3 at full generality):
    a producer stamp creates force for every consumer. -/
def AllowsAbsoluteForceStamp
    (Stamp : Artifact → Prop) (Force : Consumer → Artifact → Prop) : Prop :=
  ∀ (a : Artifact) (c : Consumer), Stamp a → Force c a

/-- **THE CENTER.** A consumer-independent force predicate exists IFF all
    consumers agree on every artifact. This is the precise observer
    theorem; the universal-root material below is a positive exception, not
    the no-go. -/
theorem has_global_section_iff_consumers_agree
    (Force : Consumer → Artifact → Prop) :
    HasGlobalSection Force ↔ ConsumersAgree Force := by
  constructor
  · rintro ⟨G, hG⟩
    intro c d a
    exact Iff.trans (Iff.symm (hG c a)) (hG d a)
  · intro hagree
    refine ⟨fun a => ∃ c : Consumer, Force c a, ?_⟩
    intro c a
    constructor
    · rintro ⟨d, hd⟩
      exact (hagree d c a).mp hd
    · intro hc
      exact ⟨c, hc⟩

/-- **THE NO-GO COROLLARY.** If two consumers disagree on a single
    artifact, the force bundle has no global section. A consumer-independent
    force verdict cannot exist while consumers genuinely differ. -/
theorem no_global_section_when_consumers_disagree
    (Force : Consumer → Artifact → Prop)
    (h : ∃ (A B : Consumer) (a : Artifact), Force A a ∧ ¬ Force B a) :
    ¬ HasGlobalSection Force := by
  obtain ⟨A, B, a, hA, hB⟩ := h
  rintro ⟨G, hG⟩
  exact hB ((hG B a).mp ((hG A a).mpr hA))

/-- The no-go for the absolute stamp at full generality: if an artifact is
    stamped yet some consumer's honest force refuses it, the absolute-stamp
    bridge cannot hold. -/
theorem stamped_disagreement_refutes_absolute_stamp
    (Force : Consumer → Artifact → Prop) (Stamp : Artifact → Prop)
    (a : Artifact) (B : Consumer)
    (hStamp : Stamp a) (hB : ¬ Force B a) :
    ¬ AllowsAbsoluteForceStamp Stamp Force := by
  intro hbridge
  exact hB (hbridge a B hStamp)

/-- The positive exception: a universal root licenses AN honest absolute
    stamp — namely the stamp that marks exactly what the root forces. NOT
    the only sound stamp: smaller stamps, including the empty stamp, are
    also sound (the empty stamp vacuously, and uselessly). -/
theorem universal_root_licenses_stamp
    (Force : Consumer → Artifact → Prop) (root : Consumer)
    (huniv : UniversalRoot Force root) :
    AllowsAbsoluteForceStamp (Force root) Force := by
  intro a c hroot
  exact huniv c a hroot

/-! ## Concrete capstone — an open consumer world has no *forcing* universal root

  A list-recognized model. The point: as long as the consumer type contains
  a consumer that recognizes nothing, no root that forces the disputed
  artifact is universal (the empty root is vacuously universal, but it
  forces nothing and licenses nothing). Single-root is a property of a
  closed world, not of the artifact. -/

structure CConsumer where
  id : Nat
  recognized : List Nat
  deriving DecidableEq, Repr

structure CArtifact where
  id : Nat
  deriving DecidableEq, Repr

def cForce (c : CConsumer) (a : CArtifact) : Prop := a.id ∈ c.recognized

instance (c : CConsumer) (a : CArtifact) : Decidable (cForce c a) := by
  unfold cForce; infer_instance

def cA : CConsumer := { id := 1, recognized := [7] }
def cB : CConsumer := { id := 2, recognized := [] }   -- recognizes nothing
def cArt : CArtifact := { id := 7 }

/-- The model genuinely contains disagreement. -/
theorem c_disagree :
    ∃ (A B : CConsumer) (a : CArtifact), cForce A a ∧ ¬ cForce B a :=
  ⟨cA, cB, cArt, by decide, by decide⟩

/-- The gem, on the concrete model: no global section exists. -/
theorem concrete_no_global_section : ¬ HasGlobalSection cForce :=
  no_global_section_when_consumers_disagree cForce c_disagree

/-- No *forcing* root is universal in this open world: any root that forces
    `cArt` fails to be universal, because `cB` (which recognizes nothing)
    does not factor through it. (The empty root IS universal here — it just
    forces nothing, so this theorem's hypothesis excludes it.) Single-root
    cannot be asserted for a disputed artifact over an open consumer
    type. -/
theorem no_forcing_root_for_disputed_artifact :
    ∀ root : CConsumer, cForce root cArt → ¬ UniversalRoot cForce root := by
  intro root hroot huniv
  exact (by decide : ¬ cForce cB cArt) (huniv cB cArt hroot)

end Admissibility.Scratch.NoUniversalRoot
