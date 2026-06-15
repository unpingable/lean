/-
  Custody-Class: SCRATCH

  ShardedCustody — fenced scratch slice, 2026-06-14. Not imported by
  `LeanProofs.lean`. Not part of any 1.0 surface. No paper anchor. No
  promotion path. NOT used as discharge for any doctrine. Compile-is-
  contact only. **Doctrine sidecar, NOT a P4 dependency.**

  ## Why this exists (the lawful exception)

  The multigov / NoUniversalRoot slices say plural custody over the SAME
  contested state has no global section. Without modeling sharding, that
  overstates — it reads as "plural resolvers are impossible." The real,
  narrower claim:

      Plural simultaneous resolvers are impossible over the SAME contested
      state, unless there is arbitration/leader election.
      Plural custody over DISJOINT jurisdiction is fine.

  This slice models exactly that discriminator — the jurisdiction theorem —
  and nothing more.

  ## What is NOT modeled (the shiny trap)

  No consensus mechanics. No Paxos/Raft, no log replication, no quorum, no
  failure detector. "Arbitration required" is named as the alternative
  branch; the arbitration MECHANISM is the governor's, not Lean's. This is
  the jurisdiction boundary, not a distributed-systems cathedral.

  ## Rhyme

  `different_roots_on_contested_shard_not_both_admissible` is the
  shard-instance of `NoUniversalRoot`'s pattern: roots ≈ consumers, shards ≈
  artifacts, "both admissible" ≈ a consistent (global) section. It proves the
  not-both-admissible instance — same shape, jurisdiction clothes — not a
  literal `HasGlobalSection` theorem.

  ## Prior art (read-only, not imported)
    - LeanProofs/Scratch/NoUniversalRoot.lean       (no global section under disagreement)
    - LeanProofs/Scratch/DeadlockEscalation.lean    (multigov; this is its lawful-plural exception)

  ## Keeper
    Plural custody is admissible over disjoint jurisdiction, not shared
    contested state. (The ants can stay.)
-/

namespace Admissibility.Scratch.ShardedCustody

/-! ## Vocabulary -/

structure Root where
  id : Nat
  deriving DecidableEq, Repr

structure Shard where
  id : Nat
  deriving DecidableEq, Repr

/-- Each shard has one owning root — its jurisdiction. -/
abbrev Ownership := Shard → Root

/-- A transition is driven by a root and touches a set of shards. -/
structure Transition where
  driver : Root
  touches : List Shard

/-- Jurisdictionally admissible: every shard the transition touches is owned
    by its driver (the driver acts only within its jurisdiction). -/
def Admissible (owner : Ownership) (t : Transition) : Prop :=
  ∀ s ∈ t.touches, owner s = t.driver

/-- A shard is contested by `a` and `b` if both touch it. -/
def Contested (a b : Transition) (s : Shard) : Prop :=
  s ∈ a.touches ∧ s ∈ b.touches

/-- Disjoint touch sets: no shard is contested. -/
def DisjointTouch (a b : Transition) : Prop :=
  ∀ s, ¬ Contested a b s

/-! ## The two general theorems (zero-axiom, pure jurisdiction) -/

/-- **Contested shard requires same root** (or arbitration). If a shard is
    contested by `a` and `b` and BOTH are jurisdiction-admissible, their
    drivers coincide — singular custody / sequencing over shared state. The
    only escape when drivers differ is arbitration (the governor's job,
    not modeled here). -/
theorem contested_shard_requires_same_root
    (owner : Ownership) (a b : Transition) (s : Shard)
    (hc : Contested a b s) (ha : Admissible owner a) (hb : Admissible owner b) :
    a.driver = b.driver :=
  (ha s hc.1).symm.trans (hb s hc.2)

/-- **Different roots on a contested shard ⇒ not both admissible.** Two
    transitions with DIFFERENT drivers cannot both be jurisdiction-admissible
    over a shard they both touch. This is the shard-instance of the
    no-global-section pattern ("no consistent assignment makes both hold");
    it proves exactly `¬ (Admissible a ∧ Admissible b)`, NOT a
    `HasGlobalSection`-style theorem. The escape when drivers differ is
    arbitration — named here, NOT modeled (the mechanism is the governor's). -/
theorem different_roots_on_contested_shard_not_both_admissible
    (owner : Ownership) (a b : Transition) (s : Shard)
    (hc : Contested a b s) (hdiff : a.driver ≠ b.driver) :
    ¬ (Admissible owner a ∧ Admissible owner b) := by
  intro ⟨ha, hb⟩
  exact hdiff (contested_shard_requires_same_root owner a b s hc ha hb)

/-! ## The lawful exception, witnessed — disjoint shards allow parallel custody

  Two DIFFERENT roots, both jurisdiction-admissible, over disjoint shards.
  Plural custody is real when jurisdictions don't overlap. -/

def shardX : Shard := ⟨1⟩
def shardY : Shard := ⟨2⟩
def rootA : Root := ⟨1⟩
def rootB : Root := ⟨2⟩

/-- shardX owned by rootA, everything else by rootB. -/
def owner0 : Ownership := fun s => if s = shardX then rootA else rootB

def tA : Transition := { driver := rootA, touches := [shardX] }
def tB : Transition := { driver := rootB, touches := [shardY] }

theorem tA_admissible : Admissible owner0 tA := by
  intro s hs
  simp only [tA, List.mem_singleton] at hs
  subst hs
  simp [owner0, tA]

theorem tB_admissible : Admissible owner0 tB := by
  intro s hs
  simp only [tB, List.mem_singleton] at hs
  subst hs
  simp [owner0, tB, shardX, shardY]

theorem tA_tB_disjoint : DisjointTouch tA tB := by
  intro s hc
  obtain ⟨hsa, hsb⟩ := hc
  simp only [tA, tB, List.mem_singleton] at hsa hsb
  subst hsa
  simp [shardX, shardY] at hsb

/-- **THE LAWFUL EXCEPTION.** Distinct roots, disjoint shards, both
    admissible simultaneously — plural custody over disjoint jurisdiction. -/
theorem disjoint_shards_allow_parallel_custody :
    tA.driver ≠ tB.driver ∧ DisjointTouch tA tB ∧
    Admissible owner0 tA ∧ Admissible owner0 tB := by
  refine ⟨?_, tA_tB_disjoint, tA_admissible, tB_admissible⟩
  simp [tA, tB, rootA, rootB]

end Admissibility.Scratch.ShardedCustody
