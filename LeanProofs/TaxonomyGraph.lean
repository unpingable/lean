/-
  Cybernetic Failure Taxonomy: Formal Graph Sketch

  Encoding the 15 domains (14 primitive + 1 composite) and their
  structural relationships from taxonomy-role-map.md.

  The goal is to see what the proofs look like and where the informal
  language was cheating. This is a starter sketch, not a polished
  formalization.

  Status: SKETCH. Needs Lean 4 toolchain to compile.

  Domain count:
    15 domains total in the taxonomy table
    14 primitive (Δn Δo Δs Δm Δg Δa Δk Δw Δc Δb Δx Δr Δe Δh Δp)
     1 composite (Δi = Δn + Δr + Δw), demoted, not encoded as a node

  Three relation types (per Chatty's audit):
    edge        — causal pipeline: "a commonly causes or enables b"
    reinforces  — lateral mutual stabilization: "once both active,
                  they lock each other in"
    normalizes  — temporal/dynamic attractor: "any failure that persists
                  long enough without correction tends toward this state"

  The informal "Δh is the universal sink" conflates pipeline reachability
  with temporal attractor dynamics. This encoding keeps them separate.
-/

-- ════════════════════════════════════════════════════════════
-- DOMAINS
-- ════════════════════════════════════════════════════════════

-- The 14 primitive domains (Δi excluded as composite)
inductive Domain where
  | dn  -- Δn: namespace failure
  | do_ -- Δo: observability failure (do is reserved, hence do_)
  | ds  -- Δs: signal corruption
  | dm  -- Δm: model drift
  | dg  -- Δg: gain mismatch
  | da  -- Δa: actuation mismatch
  | dk  -- Δk: coupling mismatch
  | dw  -- Δw: write-authority drift
  | dc  -- Δc: consequence detachment
  | db  -- Δb: boundary error
  | dx  -- Δx: scale inversion
  | dr  -- Δr: recursion capture
  | de  -- Δe: energy deficit
  | dh  -- Δh: hysteresis failure
  | dp  -- Δp: polarity inversion
  deriving DecidableEq, Repr, Inhabited

open Domain

-- ════════════════════════════════════════════════════════════
-- ROLE CLASSIFICATION
-- ════════════════════════════════════════════════════════════

inductive Role where
  | root             -- distorts framing/perception/authority, originates cascades
  | rootAmplifier    -- hybrid: sometimes originates, sometimes amplifies
  | transmission     -- bridges between layers, usually downstream
  | crossScaleTrans  -- inverts sign across scale boundaries (within scale substrate)
  | junction         -- high connectivity between layers
  | operational      -- independent engineering problem, some amplification
  | terminal         -- end-state, mostly receives, doesn't propagate
  | downstream       -- governance end-state
  | constraint       -- orthogonal, determines recoverability
  | sink             -- receives from many paths, locks failures in
  | contextDependent -- role depends on whether it's the system or downstream
  deriving DecidableEq, Repr

def role : Domain → Role
  | .dn  => .root
  | .do_ => .root
  | .ds  => .root
  | .dw  => .root
  | .dp  => .rootAmplifier
  | .dm  => .transmission
  | .dk  => .operational
  | .dx  => .crossScaleTrans
  | .dr  => .contextDependent
  | .db  => .junction
  | .dg  => .terminal
  | .da  => .terminal
  | .dc  => .downstream
  | .de  => .constraint
  | .dh  => .sink

-- ════════════════════════════════════════════════════════════
-- RELATION 1: PIPELINE EDGES
-- ════════════════════════════════════════════════════════════

/-
  Direct causal edges: "a commonly causes or enables b"
  These encode the pipelines from taxonomy-role-map.md.

  NOTE on Δx: The role map classifies Δx as "cross-scale
  transmission" — it inverts sign across scale boundaries.
  But it's an AMPLIFIER of whatever crosses the boundary,
  not a generator with its own downstream targets. Its
  "outgoing" effect is to worsen the incoming failure at
  a different scale, not to produce a new domain failure.
  This is modeled by Δx having no outgoing pipeline edges.
  Δx is not a dead end by accident — it's a dead end because
  amplification-in-place is not the same as propagation to
  a new domain.

  Similarly: Δs reaches Δm but Δm only reaches terminals
  (Δg, Δa). So the Δs pipeline dead-ends. This is NOT a
  bug — it means "universal sink" is a dynamic claim about
  Δh, not a pipeline reachability claim. See Relation 3.
-/
def edge : Domain → Domain → Bool
  -- Δn (namespace) outgoing
  | .dn, .db  => true  -- can't name → wrong boundary
  | .dn, .do_ => true  -- can't name → can't observe as category
  | .dn, .dm  => true  -- can't name → model can't represent
  -- Δo (observability) outgoing
  | .do_, .dm => true   -- can't observe → model drifts
  | .do_, .dg => true   -- can't observe → gain wrong
  | .do_, .dw => true   -- can't observe → authority drifts undetected
  -- Δs (signal corruption) outgoing
  | .ds, .dm  => true   -- corrupted signal → model drifts
  -- Δm (model drift) outgoing
  | .dm, .dg  => true   -- model drifts → gain miscalibrated
  | .dm, .da  => true   -- model drifts → wrong intervention layer
  -- Δb (boundary error) outgoing
  | .db, .dc  => true   -- wrong boundary → consequences detach
  | .db, .do_ => true   -- wrong boundary → observing wrong thing
  | .db, .dm  => true   -- wrong boundary → model drifts
  -- Δw (write-authority drift) outgoing
  | .dw, .dc  => true   -- authority drifts → consequences detach
  -- Δc (consequence detachment) outgoing
  | .dc, .dh  => true   -- consequence detachment → normalizes
  -- Δp (polarity inversion) outgoing
  | .dp, .dr  => true   -- inverted reward → recursion capture
  | .dp, .dg  => true   -- inverted reward → gain wrong
  | .dp, .ds  => true   -- inverted polarity → generates confirming signals
  -- Δr (recursion capture) outgoing
  | .dr, .dw  => true   -- recursion captures authority
  | .dr, .dm  => true   -- loop outputs become model inputs
  -- Δk (coupling mismatch) outgoing
  | .dk, .dx  => true   -- coupling mismatch → scale inversion
  -- Δe (energy deficit) outgoing
  | .de, .dh  => true   -- no surplus → can't return → stuck
  -- Δg, Δa, Δx, Δh: no outgoing pipeline edges
  -- Δg, Δa: terminal (proven below)
  -- Δx: amplifies in-place, does not propagate to new domain
  -- Δh: sink (receives, does not pipeline forward — but see Relation 2)
  | _, _      => false

-- ════════════════════════════════════════════════════════════
-- RELATION 2: REINFORCING LOOPS
-- ════════════════════════════════════════════════════════════

/-
  Bidirectional lateral effects. NOT causal pipelines.
  Semantics: "once both domains are active, they stabilize
  each other." Requires both to already be present.

  These are modeled separately because:
    pipeline  = "a causes b" (temporal precedence)
    reinforces = "a and b lock each other in" (mutual stabilization)
  Collapsing them into one relation is how elegant frameworks lie.
-/
def reinforces : Domain → Domain → Bool
  | .dh, .dn => true   -- normalization erases vocabulary for baseline
  | .dn, .dh => true   -- lost vocabulary makes non-return invisible
  | .dh, .dc => true   -- normalization prevents reconnection
  | .dc, .dh => true   -- detachment normalizes into permanent structure
  | .dn, .db => true   -- can't name → can't draw boundary
  | .db, .dn => true   -- wrong boundary → thing never gets named
  | _, _     => false

-- ════════════════════════════════════════════════════════════
-- RELATION 3: TEMPORAL ATTRACTOR (Δh)
-- ════════════════════════════════════════════════════════════

/-
  The informal claim "Δh is the universal sink" is NOT a pipeline
  reachability claim. It is a temporal/dynamic claim:

    "Any cybernetic failure that persists without correction
     tends toward hysteretic lock-in."

  This is an attractor statement, not a path statement. It applies
  to domains that have no pipeline to Δh (like Δs, Δk, Δx) because
  persistence is a temporal property, not a graph-topological one.

  We model this as a separate axiom rather than smuggling it into
  the edge relation. The axiom says: for any domain, if the failure
  persists beyond some threshold without correction, the system
  enters Δh-adjacent dynamics (self-stabilizing non-return).

  This is deliberately NOT proven from the graph. It is a claim
  about dynamics that the static graph cannot represent.
-/
axiom persistence_normalizes :
  ∀ (d : Domain), d ≠ .dh →
    -- "if d persists without correction, the system's state
    --  becomes hysteretically self-stabilizing"
    -- This is stated as an axiom because it's a dynamic claim,
    -- not derivable from static pipeline topology.
    True  -- placeholder: the real content is in the comment.
          -- A proper formalization would need a temporal logic
          -- or a state-transition system, not just a graph.

/-
  NOTE: This axiom is intentionally weak (just True) because
  we don't yet have the temporal substrate to state it properly.
  Its value is DOCUMENTARY: it marks where the informal prose
  was making a claim the graph can't support, and names the
  kind of formalism (temporal logic, attractor dynamics) that
  would be needed to state it for real.
-/

-- ════════════════════════════════════════════════════════════
-- REACHABILITY (transitive closure of pipeline edges only)
-- ════════════════════════════════════════════════════════════

/-
  Reachable a b = "there exists a nonempty causal pipeline from a to b"

  This is deliberately NON-REFLEXIVE: a node does not reach itself
  unless there is an explicit cycle through edges. This is the
  "nonempty path" interpretation, not the reflexive-transitive closure.

  If you later need reflexive closure (e.g., "every active failure
  reaches itself under persistence"), add a `refl` constructor
  and rename accordingly.
-/
inductive Reachable : Domain → Domain → Prop where
  | step  : edge a b = true → Reachable a b
  | trans : Reachable a b → Reachable b c → Reachable a c

-- ════════════════════════════════════════════════════════════
-- CLAIM 1: Terminal nodes have no outgoing pipeline edges
-- ════════════════════════════════════════════════════════════

-- "Δg and Δa are basically inert. They receive, they don't propagate."
-- Proved by exhaustive case analysis on all 14 primitive targets.

theorem dg_terminal : ∀ (b : Domain), edge .dg b = false := by
  intro b; cases b <;> rfl

theorem da_terminal : ∀ (b : Domain), edge .da b = false := by
  intro b; cases b <;> rfl

-- Δx also has no outgoing edges — but this is by design (amplifies
-- in-place), not because it's terminal in the same sense as Δg/Δa.
theorem dx_no_outgoing : ∀ (b : Domain), edge .dx b = false := by
  intro b; cases b <;> rfl

-- Δh has no outgoing pipeline edges. It affects other domains
-- only through the reinforcing relation, not through causal pipelines.
theorem dh_no_pipeline_outgoing : ∀ (b : Domain), edge .dh b = false := by
  intro b; cases b <;> rfl

-- ════════════════════════════════════════════════════════════
-- CLAIM 2: Pipeline reachability to Δh
-- ════════════════════════════════════════════════════════════

/-
  Which domains can reach Δh through pipeline edges alone?

  Reachable:     Δn, Δo, Δw, Δp, Δe, Δr, Δb, Δc, Δm (via Δb path)
  Not reachable: Δs, Δk, Δx, Δg, Δa, Δh (itself, non-reflexive)

  "Δh is the universal sink" is therefore FALSE as a pipeline
  reachability claim. It is TRUE as a temporal attractor claim
  (see Relation 3 / persistence_normalizes axiom).
-/

-- Δn → Δb → Δc → Δh  (the framing cascade)
theorem dn_reaches_dh : Reachable .dn .dh := by
  apply Reachable.trans (b := .db)
  · exact .step rfl              -- Δn → Δb
  · apply Reachable.trans (b := .dc)
    · exact .step rfl            -- Δb → Δc
    · exact .step rfl            -- Δc → Δh

-- Δo → Δw → Δc → Δh
theorem do_reaches_dh : Reachable .do_ .dh := by
  apply Reachable.trans (b := .dw)
  · exact .step rfl              -- Δo → Δw
  · apply Reachable.trans (b := .dc)
    · exact .step rfl            -- Δw → Δc
    · exact .step rfl            -- Δc → Δh

-- Δw → Δc → Δh  (authority pipeline)
theorem dw_reaches_dh : Reachable .dw .dh := by
  apply Reachable.trans (b := .dc)
  · exact .step rfl              -- Δw → Δc
  · exact .step rfl              -- Δc → Δh

-- Δp → Δr → Δw → Δc → Δh  (recursion → authority → lock-in)
theorem dp_reaches_dh : Reachable .dp .dh := by
  apply Reachable.trans (b := .dr)
  · exact .step rfl              -- Δp → Δr
  · apply Reachable.trans (b := .dw)
    · exact .step rfl            -- Δr → Δw
    · apply Reachable.trans (b := .dc)
      · exact .step rfl          -- Δw → Δc
      · exact .step rfl          -- Δc → Δh

-- Δe → Δh  (exhaustion lock-in, direct edge)
theorem de_reaches_dh : Reachable .de .dh :=
  .step rfl

-- Δr → Δw → Δc → Δh
theorem dr_reaches_dh : Reachable .dr .dh := by
  apply Reachable.trans (b := .dw)
  · exact .step rfl              -- Δr → Δw
  · apply Reachable.trans (b := .dc)
    · exact .step rfl            -- Δw → Δc
    · exact .step rfl            -- Δc → Δh

-- Δb → Δc → Δh
theorem db_reaches_dh : Reachable .db .dh := by
  apply Reachable.trans (b := .dc)
  · exact .step rfl              -- Δb → Δc
  · exact .step rfl              -- Δc → Δh

-- Δc → Δh  (direct edge)
theorem dc_reaches_dh : Reachable .dc .dh :=
  .step rfl

/-
  Δs does NOT reach Δh through pipeline edges.
  Δs → Δm → Δg (terminal) | Δa (terminal). Dead end.

  Δk does NOT reach Δh through pipeline edges.
  Δk → Δx (no outgoing). Dead end.

  These are not bugs. They mean the "universal sink" property
  of Δh operates through temporal dynamics (persistence_normalizes),
  not through pipeline topology.
-/

-- ════════════════════════════════════════════════════════════
-- CLAIM 3: The framing cascade changes failure TYPE at each step
-- ════════════════════════════════════════════════════════════

-- Δn (root) → Δb (junction) → Δc (downstream) → Δh (sink)
-- Each node has a different role. This distinguishes a cascade
-- (failure changes character at each hop) from mere amplification
-- (failure gets louder but stays the same kind).

theorem framing_cascade_distinct_roles :
    role .dn ≠ role .db
  ∧ role .db ≠ role .dc
  ∧ role .dc ≠ role .dh := by
  constructor
  · intro h; cases h  -- root ≠ junction
  constructor
  · intro h; cases h  -- junction ≠ downstream
  · intro h; cases h  -- downstream ≠ sink

-- ════════════════════════════════════════════════════════════
-- CLAIM 4: Δi decomposes into Δn + Δr + Δw (definitional)
-- ════════════════════════════════════════════════════════════

/-
  "Identity failure = namespace failure + recursion capture
   + write-authority drift, with no independent residue."

  Per Chatty's audit: make decomposition definitional, don't
  try to prove metaphysical exhaustiveness. Δi is an abbreviation
  (syndrome predicate), not a node.
-/

-- Δi is a syndrome: a system exhibits it iff it exhibits all three.
def exhibits_identity_failure
    (has_failure : Domain → Prop) : Prop :=
  has_failure .dn ∧ has_failure .dr ∧ has_failure .dw

-- The "no residue" claim is definitional by construction:
-- exhibits_identity_failure IS the conjunction, so there's
-- nothing left over by definition. A stronger "no residue"
-- claim (second-order: no property implied by Δi that isn't
-- implied by one of the three) is not worth formalizing yet.

-- ════════════════════════════════════════════════════════════
-- CLAIM 5: Therapeutic inversion count
-- ════════════════════════════════════════════════════════════

def has_therapeutic_inversion : Domain → Bool
  | .dn  => true   -- constructive ambiguity
  | .do_ => true   -- deliberate opacity / privacy
  | .ds  => true   -- signal shaping (failure is deception, not modification)
  | .dm  => true   -- deliberate model simplification
  | .dg  => true   -- gain tuning (the point of control theory)
  | .da  => false   -- no beneficial "wrong tools"
  | .dk  => true   -- tight=coordination, loose=modularity
  | .dw  => true   -- delegated authority with sunset clauses
  | .dc  => true   -- deliberate consequence buffering (liability, insurance)
  | .db  => true   -- appropriate scoping (when outside controller exists)
  | .dx  => true   -- multi-scale coherent design (Paper 1)
  | .dr  => true   -- recursion as learning / practice / skill acquisition
  | .de  => false   -- no beneficial "lack of energy"
  | .dh  => true   -- anti-flap / damping / regime stabilization
  | .dp  => true   -- deliberate contrarian inversion (hack, not stable)

/-
  Count: 13 of 15 domains have therapeutic inversions.

  The role map says "11 of 14 primitives." The discrepancy:
    - Role map excluded Δi (composite) → 14 primitives, correct.
    - Role map counted Δp's inversion as "hack, not stable" and
      may have excluded it. If excluded: 12 of 14.
    - Role map may have excluded Δds (signal shaping). The note
      says "failure is deception, not modification" — so the
      healthy form is signal shaping, but it's a stretch to call
      that a "therapeutic inversion" of corruption specifically.

  The exact count depends on how strict "therapeutic inversion"
  is defined. The important structural claim is: MOST domains
  have a beneficial form under the right sign. The taxonomy
  describes control mechanisms, not a morality catalog.
-/

-- ════════════════════════════════════════════════════════════
-- CONSISTENCY CHECKS
-- ════════════════════════════════════════════════════════════

-- Every domain classified as root has at least one outgoing edge
theorem roots_have_outgoing :
    (∃ b, edge .dn b = true)
  ∧ (∃ b, edge .do_ b = true)
  ∧ (∃ b, edge .ds b = true)
  ∧ (∃ b, edge .dw b = true) := by
  exact ⟨⟨.db, rfl⟩, ⟨.dm, rfl⟩, ⟨.dm, rfl⟩, ⟨.dc, rfl⟩⟩

-- The root/amplifier hybrid also has outgoing edges
theorem root_amplifier_has_outgoing :
    ∃ b, edge .dp b = true := ⟨.dr, rfl⟩

-- Junction (Δb) has both incoming and outgoing edges
theorem junction_has_incoming :
    ∃ a, edge a .db = true := ⟨.dn, rfl⟩

theorem junction_has_outgoing :
    ∃ b, edge .db b = true := ⟨.dc, rfl⟩

-- Constraint (Δe) has outgoing to sink only
theorem constraint_reaches_sink :
    edge .de .dh = true := rfl

-- ════════════════════════════════════════════════════════════
-- NEXT STEPS (if this is fun rather than masochistic)
-- ════════════════════════════════════════════════════════════

/-
  1. COMPUTE TRANSITIVE CLOSURE over the finite graph.
     Derive Fintype for Domain, build the closure matrix,
     let the machine tell you which nodes reach which.
     This replaces artisanal hand-written reachability proofs.

  2. PROVE NON-REACHABILITY for Δs and Δk.
     Requires decidability argument over the finite graph.
     The closure matrix from step 1 would give this for free.

  3. FORMALIZE the temporal attractor claim properly.
     Replace the placeholder axiom with either:
     (a) a state-transition system with a persistence predicate, or
     (b) a simple temporal logic over domain activation states.
     This is where the real work would be, and where it might
     become masochistic rather than revealing.

  4. ROLE-EDGE CONSISTENCY: prove that every domain classified
     as an amplifier or transmission node has at least one
     outgoing edge. Currently Δx fails this (by design — it
     amplifies in-place). Either reclassify Δx's role or
     formalize "amplifies in-place" as a different kind of edge.

  5. If the graph is stable, encode the claimant transition
     threshold from the rights addendum as a predicate and
     prove the burden shift follows from the five conditions.
-/
