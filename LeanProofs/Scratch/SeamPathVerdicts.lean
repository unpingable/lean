/-
  Custody-Class: SCRATCH

  SeamPathVerdicts — does an edge-verdict ledger compose along a path without
  laundering local admissibility into trajectory authority?

  Status: fenced scratch. Compile-is-contact only. Not imported by
  `LeanProofs.lean`. Does NOT discharge `SeamEdges`, `ReachabilityClosure`, or the
  bridge-obligation-lattice. It tests one bounded question.

  The gap this probes (a missing joint between two already-open objects):

      WitnessedReachability : paths exist / `PaidFrom` composes (reachability).
      SeamEdges             : individual edges carry verdicts (single crossings).
      <here>                : do edge VERDICTS compose into a PATH verdict?

  The bad inference — the seam-graph form of local-safety laundering:

      edge₁ admissible, edge₂ admissible, …  ⟹  path admissible      -- NO.

  Two halves:

    * Contamination (cheap, operational). Any unlabeled / axiom / sorry edge makes
      the whole path un-labeled. A nonempty list of bare `Cert → Req` functions is
      still not labeled. Laundering re-enters at the worst edge, not the average.

    * The money result (countermodel). Even when EVERY edge is a constructed bridge
      AND each edge satisfies its own LOCAL budget, the path can still violate the
      GLOBAL budget. So per-edge bridges are INGREDIENTS, not a trajectory receipt:
      a path is authority-bearing only through a composition witness (here, the
      global-budget proof), which per-edge witnesses do not supply. This is the
      no-unifier result showing up operationally.

  Deliberately predicate-level: NO new `PathVerdict` enum is minted (that would be
  the retired composition-classifier attractor in a fresh hat). We reuse
  `SeamEdges.EdgeVerdict` by projecting its tag, and reason with predicates.

  Self-contained beyond the SeamEdges import. Check with:
    cd ~/git/lean && lake env lean LeanProofs/Scratch/SeamPathVerdicts.lean
-/

import LeanProofs.Scratch.SeamEdges

namespace Admissibility.Scratch.SeamPathVerdicts

open Admissibility.Scratch.SeamEdges

/-! ## Verdict tag — the type-erased projection of `SeamEdges.EdgeVerdict`

A path is heterogeneously typed (edge i's `Req` is edge i+1's `Cert`), so the
contamination half reasons at the verdict TAG, not the per-edge discipline. `VClass`
is not a new verdict kernel: `EdgeVerdict.vclass` below witnesses that it is exactly
the constructor tag of the existing `SeamEdges.EdgeVerdict`, payload dropped. -/

inductive VClass
  | bridge
  | refusal
  | unlabeled
  | axiomToken
  | sorryToken
  deriving DecidableEq, Repr

/-- `VClass` is the constructor tag of `SeamEdges.EdgeVerdict`; this projection is the
    proof we are reusing that ledger, not re-minting it. -/
def _root_.Admissibility.Scratch.SeamEdges.EdgeVerdict.vclass
    {Cert Req : Type} {D : EdgeDiscipline Cert Req} : EdgeVerdict D → VClass
  | EdgeVerdict.constructedBridge _  => VClass.bridge
  | EdgeVerdict.constructedRefusal _ => VClass.refusal
  | EdgeVerdict.unlabeled            => VClass.unlabeled
  | EdgeVerdict.axiomToken           => VClass.axiomToken
  | EdgeVerdict.sorryToken           => VClass.sorryToken

/-- A tag is *labeled* iff it carries a constructed verdict (bridge or refusal). The
    three token tags are the laundering holes. Mirrors `SeamEdges.AuthorityBearing`
    per edge. -/
def VClass.labeled : VClass → Prop
  | VClass.bridge     => True
  | VClass.refusal    => True
  | VClass.unlabeled  => False
  | VClass.axiomToken => False
  | VClass.sorryToken => False

/-- The tag projection agrees with `SeamEdges.AuthorityBearing`: a verdict is
    authority-bearing exactly when its tag is labeled. Keeps the reuse honest. -/
theorem vclass_labeled_iff_authorityBearing
    {Cert Req : Type} {D : EdgeDiscipline Cert Req} (v : EdgeVerdict D) :
    v.vclass.labeled ↔ AuthorityBearing v := by
  cases v <;> simp [EdgeVerdict.vclass, VClass.labeled, AuthorityBearing]

/-! ## Contamination — the worst edge labels the path -/

/-- A path (as a tag list) is well-labeled iff every edge carries a constructed
    verdict. There is no path-level authority without it. -/
def WellLabeled (p : List VClass) : Prop := ∀ v ∈ p, v.labeled

/-- A single token-tag edge anywhere makes the whole path un-labeled. Laundering
    re-enters at the worst edge. -/
theorem hole_contaminates (p : List VClass)
    (h : ∃ v ∈ p, v = VClass.unlabeled ∨ v = VClass.axiomToken ∨ v = VClass.sorryToken) :
    ¬ WellLabeled p := by
  intro hw
  obtain ⟨v, hmem, hv⟩ := h
  have hl := hw v hmem
  rcases hv with rfl | rfl | rfl <;> exact hl

/-- A nonempty list of bare `Cert → Req` functions is still not a labeled path: each
    bare seam projects to the `unlabeled` tag. (`bareSeamVerdict` is `SeamEdges`'
    "a function is only syntax" verdict.) -/
theorem bare_path_not_wellLabeled
    {Cert Req : Type} {D : EdgeDiscipline Cert Req}
    (fs : List (Cert → Req)) (hne : fs ≠ []) :
    ¬ WellLabeled (fs.map (fun f => (bareSeamVerdict (D := D) f).vclass)) := by
  cases fs with
  | nil => exact absurd rfl hne
  | cons f rest =>
      apply hole_contaminates
      exact ⟨VClass.unlabeled, by simp [bareSeamVerdict, EdgeVerdict.vclass], Or.inl rfl⟩

/-! ## The money result — local budgets do not compose into the global one

A path edge carries its verdict tag and a `cost` (the resource the crossing spends).
`run` threads cumulative cost along the path. `LocalOK` is the per-edge budget the
edge's own bridge would certify; `GlobalOK` is the trajectory budget. The point:
`LocalOK` at every edge does NOT entail `GlobalOK`. -/

structure PEdge where
  tag  : VClass
  cost : Nat

/-- Thread cumulative cost along the path. -/
def run : List PEdge → Nat → Nat
  | [],          s => s
  | e :: rest,   s => run rest (s + e.cost)

/-- Per-edge budget: this single crossing spends at most one unit. -/
def LocalOK (e : PEdge) : Prop := e.cost ≤ 1

/-- Trajectory budget: the whole path spends at most one unit over its start. -/
def GlobalOK (start fin : Nat) : Prop := fin ≤ start + 1

/-- Sanity: the model is not vacuously broken. A single locally-OK edge IS globally
    OK — the gap opens at COMPOSITION (length ≥ 2), not from a degenerate budget. -/
theorem single_local_ok_is_global (e : PEdge) (h : LocalOK e) :
    GlobalOK 0 (run [e] 0) := by
  simpa [run, GlobalOK, LocalOK] using h

/-- **The money theorem.** It is NOT a law that per-edge local budgets entail the
    global budget. Witnessed by two constructed-bridge edges each spending one unit:
    each `LocalOK`, the path spends two, the global budget is one. Per-edge bridges
    are ingredients, not a trajectory receipt. -/
theorem global_not_implied_by_local :
    ¬ ∀ (p : List PEdge) (start : Nat),
        (∀ e ∈ p, LocalOK e) → GlobalOK start (run p start) := by
  intro h
  have hbad : GlobalOK 0 (run [⟨VClass.bridge, 1⟩, ⟨VClass.bridge, 1⟩] 0) := by
    apply h
    intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;> simp [LocalOK]
  simp only [GlobalOK, run] at hbad
  omega

/-- The same failure stated in verdict terms: a path whose every edge is a constructed
    BRIDGE and is locally OK can still violate the global budget. "All green edges"
    does not certify the trajectory. -/
theorem all_bridges_local_ok_not_global :
    ∃ p : List PEdge,
      (∀ e ∈ p, e.tag = VClass.bridge) ∧
      (∀ e ∈ p, LocalOK e) ∧
      ¬ GlobalOK 0 (run p 0) := by
  refine ⟨[⟨VClass.bridge, 1⟩, ⟨VClass.bridge, 1⟩], ?_, ?_, ?_⟩
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;> rfl
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;> simp [LocalOK]
  · intro hbad
    simp only [GlobalOK, run] at hbad
    omega

/-- The positive direction is the witness, and only the witness. A path is globally
    admissible exactly when the trajectory budget is proved — a SEPARATE obligation
    from the per-edge budgets, supplied here as `GlobalOK start (run p start)` itself.
    There is no shortcut from the edge bridges. -/
def PathBridgeWitness (start : Nat) (p : List PEdge) : Prop :=
  GlobalOK start (run p start)

theorem pathBridge_is_the_witness (start : Nat) (p : List PEdge)
    (w : PathBridgeWitness start p) : GlobalOK start (run p start) := w

/-! The compact line:
    *Local bridge receipts are ingredients, not a trajectory receipt.*
    A path is authority-bearing only through a constructed path verdict, never by the
    mere conjunction of authority-bearing edges. -/

end Admissibility.Scratch.SeamPathVerdicts
