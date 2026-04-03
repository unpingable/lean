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
-- ROLE COHERENCE: Do role labels match graph behavior?
-- ════════════════════════════════════════════════════════════

/-
  Structural predicates for what each role SHOULD mean
  graph-theoretically. If a role label doesn't cash out in
  the edge relation, it's either wrong or smuggling in dynamics
  the static graph can't represent.

  Role          │ Structural requirement
  ──────────────┼──────────────────────────────────────
  root          │ has outgoing, originates cascades
  rootAmplifier │ has outgoing (both originates and amplifies)
  transmission  │ has incoming AND outgoing (bridges)
  crossScaleTrans│ has incoming AND outgoing (bridges across scale)
  junction      │ has incoming AND outgoing (high connectivity)
  operational   │ has outgoing (some amplification)
  terminal      │ NO outgoing (end-state, receives only)
  downstream    │ has incoming (governance end-state)
  sink          │ has incoming, NO outgoing (receives, locks in)
  constraint    │ has outgoing (determines recoverability)
  contextDependent│ has outgoing (at minimum)
-/

-- ── Helper predicates ──────────────────────────────────────

def has_outgoing (d : Domain) : Prop := ∃ b, edge d b = true
def has_incoming (d : Domain) : Prop := ∃ a, edge a d = true
def no_outgoing  (d : Domain) : Prop := ∀ b, edge d b = false

-- ── TERMINALS: no outgoing edges ───────────────────────────

-- Every domain with role=terminal has no outgoing edges.
theorem terminal_role_coherence :
    ∀ d, role d = .terminal → no_outgoing d := by
  intro d h
  cases d <;> simp [role] at h <;> (intro b; cases b <;> rfl)

-- ── SINK: has incoming, no outgoing ────────────────────────

-- Δh is the only sink. It has incoming edges and no outgoing.
theorem sink_role_coherence :
    ∀ d, role d = .sink →
      has_incoming d ∧ no_outgoing d := by
  intro d h
  cases d <;> simp [role] at h
  -- only Δh matches
  constructor
  · exact ⟨.dc, rfl⟩           -- Δc → Δh
  · intro b; cases b <;> rfl    -- no outgoing

-- ── ROOTS: have outgoing edges ─────────────────────────────

-- Every domain with role=root has at least one outgoing edge.
theorem root_role_coherence :
    ∀ d, role d = .root → has_outgoing d := by
  intro d h
  cases d <;> simp [role] at h
  · exact ⟨.db, rfl⟩    -- Δn → Δb
  · exact ⟨.dm, rfl⟩    -- Δo → Δm
  · exact ⟨.dm, rfl⟩    -- Δs → Δm
  · exact ⟨.dc, rfl⟩    -- Δw → Δc

-- ── ROOT-AMPLIFIER: has outgoing ───────────────────────────

theorem root_amplifier_role_coherence :
    ∀ d, role d = .rootAmplifier → has_outgoing d := by
  intro d h
  cases d <;> simp [role] at h
  · exact ⟨.dr, rfl⟩    -- Δp → Δr

-- ── TRANSMISSION: has both incoming and outgoing ───────────

theorem transmission_role_coherence :
    ∀ d, role d = .transmission →
      has_incoming d ∧ has_outgoing d := by
  intro d h
  cases d <;> simp [role] at h
  -- only Δm matches
  constructor
  · exact ⟨.dn, rfl⟩    -- Δn → Δm
  · exact ⟨.dg, rfl⟩    -- Δm → Δg

-- ── JUNCTION: has both incoming and outgoing ───────────────

theorem junction_role_coherence :
    ∀ d, role d = .junction →
      has_incoming d ∧ has_outgoing d := by
  intro d h
  cases d <;> simp [role] at h
  -- only Δb matches
  constructor
  · exact ⟨.dn, rfl⟩    -- Δn → Δb
  · exact ⟨.dc, rfl⟩    -- Δb → Δc

-- ── DOWNSTREAM: has incoming ───────────────────────────────

theorem downstream_role_coherence :
    ∀ d, role d = .downstream → has_incoming d := by
  intro d h
  cases d <;> simp [role] at h
  -- only Δc matches
  exact ⟨.db, rfl⟩      -- Δb → Δc

-- ── CONSTRAINT: has outgoing ───────────────────────────────

theorem constraint_role_coherence :
    ∀ d, role d = .constraint → has_outgoing d := by
  intro d h
  cases d <;> simp [role] at h
  -- only Δe matches
  exact ⟨.dh, rfl⟩      -- Δe → Δh

-- ── OPERATIONAL: has outgoing ──────────────────────────────

theorem operational_role_coherence :
    ∀ d, role d = .operational → has_outgoing d := by
  intro d h
  cases d <;> simp [role] at h
  -- only Δk matches
  exact ⟨.dx, rfl⟩      -- Δk → Δx

-- ── CONTEXT-DEPENDENT: has outgoing ────────────────────────

theorem context_dependent_role_coherence :
    ∀ d, role d = .contextDependent → has_outgoing d := by
  intro d h
  cases d <;> simp [role] at h
  -- only Δr matches
  exact ⟨.dw, rfl⟩      -- Δr → Δw

-- ── CROSS-SCALE TRANSMISSION: THE Δx PROBLEM ──────────────

/-
  crossScaleTrans SHOULD mean: has incoming AND outgoing (bridges
  across scale boundaries). But Δx has NO outgoing pipeline edges.

  This is the role/behavior mismatch. Graph-theoretically, Δx is
  indistinguishable from a terminal: it receives and doesn't
  propagate. The "amplifies in-place" story is an informal claim
  about dynamics, not a graph property.

  We prove the mismatch explicitly rather than hiding it.
-/

-- Δx has incoming edges (structural half is fine)
theorem cross_scale_has_incoming :
    ∀ d, role d = .crossScaleTrans → has_incoming d := by
  intro d h
  cases d <;> simp [role] at h
  -- only Δx matches
  exact ⟨.dk, rfl⟩      -- Δk → Δx

-- Δx has NO outgoing edges (mismatch: "transmission" with nothing to transmit to)
theorem cross_scale_no_outgoing :
    ∀ d, role d = .crossScaleTrans → no_outgoing d := by
  intro d h
  cases d <;> simp [role] at h
  -- only Δx matches
  intro b; cases b <;> rfl

/-
  CONSEQUENCE: In the static pipeline graph, crossScaleTrans is
  structurally identical to terminal. The distinction between
  them exists only in the informal semantics ("amplifies in-place"
  vs "dead end").

  Options:
    (a) Reclassify Δx as terminal — honest about the graph,
        loses the "amplification" semantics.
    (b) Add a new edge type (e.g., amplifies : Domain → Domain → Bool)
        that captures "worsens the incoming failure at a different
        scale" without claiming propagation to a new domain.
    (c) Keep the mismatch documented — the role label is aspirational,
        not structural. Sometimes that's the right answer.

  This is a genuine discovery, not a bug to fix immediately.
-/

-- ── SUMMARY: Role coherence scorecard ──────────────────────

/-
  Role              │ Required        │ Proved    │ Status
  ──────────────────┼─────────────────┼───────────┼────────
  root              │ has outgoing    │ ✓         │ COHERENT
  rootAmplifier     │ has outgoing    │ ✓         │ COHERENT
  transmission      │ in + out        │ ✓         │ COHERENT
  junction          │ in + out        │ ✓         │ COHERENT
  operational       │ has outgoing    │ ✓         │ COHERENT
  terminal          │ no outgoing     │ ✓         │ COHERENT
  downstream        │ has incoming    │ ✓         │ COHERENT
  constraint        │ has outgoing    │ ✓         │ COHERENT
  sink              │ in + no out     │ ✓         │ COHERENT
  contextDependent  │ has outgoing    │ ✓         │ COHERENT
  crossScaleTrans   │ in + out        │ in only   │ MISMATCH
  ──────────────────┴─────────────────┴───────────┴────────

  10/11 roles are structurally coherent.
  1/11 (crossScaleTrans / Δx) has a role/behavior mismatch:
  labeled as transmission but structurally a terminal.
-/

-- ════════════════════════════════════════════════════════════
-- STRUCTURAL CLASSIFICATION (graph-derived, not role-assigned)
-- ════════════════════════════════════════════════════════════

/-
  These predicates describe what the graph DOES, independent of
  the human-assigned role labels. Where they agree with roles,
  the role is earned. Where they disagree (Δx), the graph is
  telling you something the role label isn't.
-/

/-- A domain is structurally terminal if it has no outgoing pipeline edges. -/
def StructurallyTerminal (d : Domain) : Prop := ∀ b, edge d b = false

/-- The terminal set is exactly {Δg, Δa, Δx, Δh}. -/
theorem structurally_terminal_exact (d : Domain) :
    StructurallyTerminal d ↔ (d = .dg ∨ d = .da ∨ d = .dx ∨ d = .dh) := by
  constructor
  · intro h
    cases d with
    | dg  => left; rfl
    | da  => right; left; rfl
    | dx  => right; right; left; rfl
    | dh  => right; right; right; rfl
    -- Non-terminal cases: exhibit a witness edge, contradicting h
    | dn  => exact absurd (h .db)  (by decide)
    | do_ => exact absurd (h .dm)  (by decide)
    | ds  => exact absurd (h .dm)  (by decide)
    | dm  => exact absurd (h .dg)  (by decide)
    | dk  => exact absurd (h .dx)  (by decide)
    | dw  => exact absurd (h .dc)  (by decide)
    | dc  => exact absurd (h .dh)  (by decide)
    | db  => exact absurd (h .dc)  (by decide)
    | dr  => exact absurd (h .dw)  (by decide)
    | de  => exact absurd (h .dh)  (by decide)
    | dp  => exact absurd (h .dr)  (by decide)
  · rintro (rfl | rfl | rfl | rfl) <;> intro b <;> cases b <;> rfl

/-- No structurally terminal domain can reach anything via pipeline edges. -/
theorem terminal_unreachable {d b : Domain}
    (ht : StructurallyTerminal d) (hr : Reachable d b) : False := by
  unfold StructurallyTerminal at ht
  induction hr with
  | step hedge => simp [ht] at hedge
  | trans _ _ ih1 _ => exact ih1 ht

-- ════════════════════════════════════════════════════════════
-- CLOSURE CLASSIFICATION
-- ════════════════════════════════════════════════════════════

/-
  For each non-terminal domain, which terminals can it reach?
  This turns individual reachability lemmas into a structural map.

  Method: forward-closed sets ("pipeline lanes"). If S is closed
  under edge (every successor of an S-member is in S), and a ∈ S,
  then everything reachable from a is in S. Contrapositively:
  if b ∉ S, then a cannot reach b.
-/

/-- Reachability stays inside forward-closed sets. -/
theorem reachable_stays_in_closed {S : Domain → Bool}
    (h_closed : ∀ a b, S a = true → edge a b = true → S b = true)
    {a b : Domain} (ha : S a = true) (hab : Reachable a b) :
    S b = true := by
  induction hab with
  | step hedge => exact h_closed _ _ ha hedge
  | trans _ _ ih1 ih2 => exact ih2 (ih1 ha)

-- ── Forward-closed sets (pipeline lanes) ───────────────────

/-
  Each lane is a forward-closed subset that captures one terminal
  family. Membership + non-membership determines which terminals
  are reachable from which sources.
-/

/-- Signal lane: Δs → Δm → {Δg, Δa}. Does not contain Δh or Δx. -/
private def signalLane : Domain → Bool
  | .ds | .dm | .dg | .da => true
  | _ => false

private theorem signalLane_closed :
    ∀ a b, signalLane a = true → edge a b = true → signalLane b = true := by
  intro a b ha hb
  cases a <;> simp [signalLane] at ha <;> cases b <;> simp_all [signalLane, edge]

/-- Coupling lane: Δk → Δx. Does not contain Δg, Δa, or Δh. -/
private def couplingLane : Domain → Bool
  | .dk | .dx => true
  | _ => false

private theorem couplingLane_closed :
    ∀ a b, couplingLane a = true → edge a b = true → couplingLane b = true := by
  intro a b ha hb
  cases a <;> simp [couplingLane] at ha <;> cases b <;> simp_all [couplingLane, edge]

/-- Authority lane: Δw → Δc → Δh. Does not contain Δg, Δa, or Δx. -/
private def authorityLane : Domain → Bool
  | .dw | .dc | .dh => true
  | _ => false

private theorem authorityLane_closed :
    ∀ a b, authorityLane a = true → edge a b = true → authorityLane b = true := by
  intro a b ha hb
  cases a <;> simp [authorityLane] at ha <;> cases b <;> simp_all [authorityLane, edge]

/-- Energy lane: Δe → Δh. Does not contain Δg, Δa, or Δx. -/
private def energyLane : Domain → Bool
  | .de | .dh => true
  | _ => false

private theorem energyLane_closed :
    ∀ a b, energyLane a = true → edge a b = true → energyLane b = true := by
  intro a b ha hb
  cases a <;> simp [energyLane] at ha <;> cases b <;> simp_all [energyLane, edge]

/-- Complement of {Δk, Δx}. Forward-closed because no edge
    from outside the coupling family points into it. -/
private def notCoupling : Domain → Bool
  | .dk | .dx => false
  | _ => true

private theorem notCoupling_closed :
    ∀ a b, notCoupling a = true → edge a b = true → notCoupling b = true := by
  intro a b ha hb
  cases a <;> simp [notCoupling] at ha <;> cases b <;> simp_all [notCoupling, edge]

-- ── Non-reachability: proved via forward-closed sets ───────

/-
  KEY FALSIFICATION (now formally proved, not just noted):
  Δs and Δk do not reach Δh through pipeline edges.
-/

theorem ds_not_reaches_dh : ¬ Reachable .ds .dh := by
  intro h
  have := reachable_stays_in_closed signalLane_closed (show signalLane .ds = true from rfl) h
  simp [signalLane] at this

theorem dm_not_reaches_dh : ¬ Reachable .dm .dh := by
  intro h
  have := reachable_stays_in_closed signalLane_closed (show signalLane .dm = true from rfl) h
  simp [signalLane] at this

theorem dk_not_reaches_dh : ¬ Reachable .dk .dh := by
  intro h
  have := reachable_stays_in_closed couplingLane_closed (show couplingLane .dk = true from rfl) h
  simp [couplingLane] at this

theorem dk_not_reaches_dg : ¬ Reachable .dk .dg := by
  intro h
  have := reachable_stays_in_closed couplingLane_closed (show couplingLane .dk = true from rfl) h
  simp [couplingLane] at this

theorem dk_not_reaches_da : ¬ Reachable .dk .da := by
  intro h
  have := reachable_stays_in_closed couplingLane_closed (show couplingLane .dk = true from rfl) h
  simp [couplingLane] at this

-- Authority/energy families cannot reach Δg or Δa

theorem dw_not_reaches_dg : ¬ Reachable .dw .dg := by
  intro h
  have := reachable_stays_in_closed authorityLane_closed (show authorityLane .dw = true from rfl) h
  simp [authorityLane] at this

theorem dw_not_reaches_da : ¬ Reachable .dw .da := by
  intro h
  have := reachable_stays_in_closed authorityLane_closed (show authorityLane .dw = true from rfl) h
  simp [authorityLane] at this

theorem dc_not_reaches_dg : ¬ Reachable .dc .dg := by
  intro h
  have := reachable_stays_in_closed authorityLane_closed (show authorityLane .dc = true from rfl) h
  simp [authorityLane] at this

theorem dc_not_reaches_da : ¬ Reachable .dc .da := by
  intro h
  have := reachable_stays_in_closed authorityLane_closed (show authorityLane .dc = true from rfl) h
  simp [authorityLane] at this

theorem de_not_reaches_dg : ¬ Reachable .de .dg := by
  intro h
  have := reachable_stays_in_closed energyLane_closed (show energyLane .de = true from rfl) h
  simp [energyLane] at this

theorem de_not_reaches_da : ¬ Reachable .de .da := by
  intro h
  have := reachable_stays_in_closed energyLane_closed (show energyLane .de = true from rfl) h
  simp [energyLane] at this

/-- No node outside {Δk, Δx} can reach Δx. The coupling family
    is completely isolated from the rest of the graph. -/
theorem not_reaches_dx_from_outside (d : Domain)
    (hd : notCoupling d = true) : ¬ Reachable d .dx := by
  intro h
  have := reachable_stays_in_closed notCoupling_closed hd h
  simp [notCoupling] at this

-- Signal family also cannot reach Δx (via notCoupling)
theorem ds_not_reaches_dx : ¬ Reachable .ds .dx :=
  not_reaches_dx_from_outside .ds rfl

theorem dm_not_reaches_dx : ¬ Reachable .dm .dx :=
  not_reaches_dx_from_outside .dm rfl

-- Authority/energy families cannot reach Δx (via notCoupling)
theorem dw_not_reaches_dx : ¬ Reachable .dw .dx :=
  not_reaches_dx_from_outside .dw rfl

theorem dc_not_reaches_dx : ¬ Reachable .dc .dx :=
  not_reaches_dx_from_outside .dc rfl

theorem de_not_reaches_dx : ¬ Reachable .de .dx :=
  not_reaches_dx_from_outside .de rfl

-- Branching family cannot reach Δx (via notCoupling)
theorem dn_not_reaches_dx : ¬ Reachable .dn .dx :=
  not_reaches_dx_from_outside .dn rfl

theorem do_not_reaches_dx : ¬ Reachable .do_ .dx :=
  not_reaches_dx_from_outside .do_ rfl

theorem db_not_reaches_dx : ¬ Reachable .db .dx :=
  not_reaches_dx_from_outside .db rfl

theorem dp_not_reaches_dx : ¬ Reachable .dp .dx :=
  not_reaches_dx_from_outside .dp rfl

theorem dr_not_reaches_dx : ¬ Reachable .dr .dx :=
  not_reaches_dx_from_outside .dr rfl

-- ── Positive reachability to non-Δh terminals ──────────────

/-
  Which nodes reach Δg and Δa? (Δh reachability already proved
  in CLAIM 2 above.) These complete the closure map.
-/

-- Signal family reaches Δg and Δa
theorem ds_reaches_dg : Reachable .ds .dg :=
  .trans (b := .dm) (.step rfl) (.step rfl)     -- Δs → Δm → Δg

theorem ds_reaches_da : Reachable .ds .da :=
  .trans (b := .dm) (.step rfl) (.step rfl)     -- Δs → Δm → Δa

theorem dm_reaches_dg : Reachable .dm .dg := .step rfl   -- direct
theorem dm_reaches_da : Reachable .dm .da := .step rfl   -- direct

-- Coupling family reaches Δx
theorem dk_reaches_dx : Reachable .dk .dx := .step rfl   -- direct

-- Branching family reaches Δg and Δa
theorem dn_reaches_dg : Reachable .dn .dg :=
  .trans (b := .dm) (.step rfl) (.step rfl)     -- Δn → Δm → Δg

theorem dn_reaches_da : Reachable .dn .da :=
  .trans (b := .dm) (.step rfl) (.step rfl)     -- Δn → Δm → Δa

theorem do_reaches_dg : Reachable .do_ .dg := .step rfl  -- direct edge

theorem do_reaches_da : Reachable .do_ .da :=
  .trans (b := .dm) (.step rfl) (.step rfl)     -- Δo → Δm → Δa

theorem db_reaches_dg : Reachable .db .dg :=
  .trans (b := .dm) (.step rfl) (.step rfl)     -- Δb → Δm → Δg

theorem db_reaches_da : Reachable .db .da :=
  .trans (b := .dm) (.step rfl) (.step rfl)     -- Δb → Δm → Δa

theorem dp_reaches_dg : Reachable .dp .dg := .step rfl   -- direct edge

theorem dp_reaches_da : Reachable .dp .da :=              -- Δp → Δr → Δm → Δa
  .trans (b := .dr) (.step rfl)
    (.trans (b := .dm) (.step rfl) (.step rfl))

theorem dr_reaches_dg : Reachable .dr .dg :=
  .trans (b := .dm) (.step rfl) (.step rfl)     -- Δr → Δm → Δg

theorem dr_reaches_da : Reachable .dr .da :=
  .trans (b := .dm) (.step rfl) (.step rfl)     -- Δr → Δm → Δa

-- ── CLOSURE MAP ────────────────────────────────────────────

/-
  Terminal set: {Δg, Δa, Δx, Δh}
  (proved: structurally_terminal_exact)

  Partition of all 15 domains by terminal reachability:

  ┌───────────────────┬────────────────┬───────────────────────┐
  │ Class             │ Members        │ Terminals reached     │
  ├───────────────────┼────────────────┼───────────────────────┤
  │ isTerminal        │ Δg, Δa, Δx, Δh│ (none — non-reflexive)│
  │ reachesHOnly      │ Δw, Δc, Δe     │ Δh                    │
  │ reachesGAOnly     │ Δs, Δm         │ Δg, Δa                │
  │ reachesXOnly      │ Δk             │ Δx                    │
  │ reachesGAH        │ Δn,Δo,Δb,Δp,Δr │ Δg, Δa, Δh           │
  └───────────────────┴────────────────┴───────────────────────┘

  Every cell in this table is machine-verified:
    • Positive entries by constructing explicit pipeline paths
    • Negative entries by forward-closed set containment
    • Terminal set by structurally_terminal_exact
    • Terminal unreachability by terminal_unreachable

  Structural claims this proves:

  1. The graph has THREE distinct terminal families, not one
     universal sink: {Δg,Δa}, {Δx}, and {Δh}.

  2. No node reaches all four terminals. The coupling family
     {Δk,Δx} is completely isolated from everything else
     (notCoupling is forward-closed). This is a graph partition,
     not an accident.

  3. Five "branching" nodes (Δn,Δo,Δb,Δp,Δr) reach three of
     four terminals. These are the nodes where intervention
     has multiple terminal outcomes — the failure can end as
     gain mismatch, actuation mismatch, OR hysteresis depending
     on which path dominates.

  4. "Δh is the universal sink" is FALSE as static pipeline
     topology. The signal family (Δs,Δm) dead-ends at Δg/Δa.
     The coupling family (Δk) dead-ends at Δx. Neither reaches
     Δh through any pipeline path.

  5. The three terminal families correspond to three distinct
     failure closure modes:
       • Gain/actuation closure (Δg,Δa): calibration failure,
         the system acts on wrong parameters but doesn't lock in
       • Scale closure (Δx): cross-scale inversion, the system
         amplifies failure across boundaries but doesn't propagate
       • Hysteresis closure (Δh): the system normalizes failure
         and can't return to baseline

     This is better than "universal sink" — it's a taxonomy of
     how failures END, not just how they propagate.
-/

-- ════════════════════════════════════════════════════════════
-- NEXT STEPS
-- ════════════════════════════════════════════════════════════

/-
  1. RESOLVE THE Δx QUESTION: reclassify, add amplification
     edge type, or document the mismatch as intentional.
     The closure map works either way — Δx is structurally
     terminal regardless of its role label.

  2. FORMALIZE the temporal attractor claim properly.
     Replace the placeholder axiom with either:
     (a) a state-transition system with a persistence predicate, or
     (b) a simple temporal logic over domain activation states.
     The closure map suggests three attractor basins, not one.

  3. INTERVENTION ANALYSIS: For branching nodes (Δn,Δo,Δb,Δp,Δr),
     which edges determine whether failure ends at Δg/Δa vs Δh?
     These are the structurally critical intervention points.

  4. If the graph is stable, encode the claimant transition
     threshold from the rights addendum as a predicate and
     prove the burden shift follows from the five conditions.
-/
