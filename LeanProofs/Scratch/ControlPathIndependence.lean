/-
  Custody-Class: SCRATCH  —  compile-is-contact only.

  A ToolTheory object — control-path independence as a basis-revocation candidate. Math
  home: (papers) working/tooltheory/control-path-independence-candidate-2026-05-29.md.
  This SCRATCH specimen builds the non-collapse CORE only (the reachability vocabulary +
  the wiring ↛ standing/coupling projection + the three-obligation InterlockBasis). The
  note's four failure-property theorems (DomesticatedProvisioning / CapturedObserver /
  StuckAtSafe / DecorativeRefusal) are vocabulary-deficient and stay PROSE DEBT — not built
  here, not as `sorry`.

  Not doctrine. Not discharge. Not build authorization. Not imported by LeanProofs.lean.
  Promotion (to `Admissibility.ControlPathIndependence`, a reserved name) requires the
  forcing case: NQ / Wicket / Governor needs to refuse a captured-checker claim.

  THE CUT (three axes, only one architectural): a captured checker — one whose sensing /
  power / logic / refusal path is controlled by the thing it checks — cannot mint an
  admissible check. INDEPENDENCE is decidable from the dependency graph; STANDING (track
  record) and COUPLING (actuator teeth) are NOT — no wiring diagram contains them.

  Self-contained (no imports). Check: cd ~/git/lean && lake env lean <abs path>.
-/

namespace ToolTheory.Scratch.ControlPathIndependence

structure Principal where
  id : Nat
deriving DecidableEq, Repr

structure Component where
  id : Nat
deriving DecidableEq, Repr

/-- Named path kinds — the dependencies that matter, kept separate. -/
inductive PathKind where
  | signal | power | logic | control | ownership
deriving DecidableEq, Repr

/-- The architecture under test. `influences` is a relation (decidable, not definitional):
    the failure mode is precisely a "parallel" principal covertly being the official one. -/
structure Arch where
  official   : Principal
  owner      : Component → Principal
  powered    : Component → Principal
  controls   : Principal → Component → Prop
  flow       : PathKind → Component → Component → Prop
  influences : Principal → Principal → Prop

/-- Reachability over a named path kind. -/
inductive ReachableBy (sys : Arch) (k : PathKind) : Component → Component → Prop where
  | refl  {a}     : ReachableBy sys k a a
  | step  {a b}   : sys.flow k a b → ReachableBy sys k a b
  | trans {a b c} : ReachableBy sys k a b → ReachableBy sys k b c → ReachableBy sys k a c

/-- A component is influenced by the official principal (over the influence relation). -/
def ComponentInfluencedByOfficial (sys : Arch) (c : Component) : Prop :=
  ∃ p, sys.influences sys.official p ∧
       (sys.owner c = p ∨ sys.powered c = p ∨ sys.controls p c)

/-- Independence is a REACHABILITY property, not a local one: every component reachable to
    the target along path kind `k` is uninfluenced by the official principal. -/
def IndependentAt (sys : Arch) (k : PathKind) (target : Component) : Prop :=
  ∀ c, ReachableBy sys k c target → ¬ ComponentInfluencedByOfficial sys c

/-- The basis structure — three obligations, only one architecturally dischargeable. The
    type system PERMITS the split (it does not force a consumer to discharge standing /
    coupled to name them). `standing` / `coupled` are carried as obligations, never given
    a default-`True` placeholder by the kernel. -/
structure InterlockBasis (sys : Arch) (target : Component) where
  independent : IndependentAt sys PathKind.signal target ∧
                IndependentAt sys PathKind.power  target ∧
                IndependentAt sys PathKind.logic  target
  standing : Prop   -- NOT discharged by architecture pathing (track record)
  coupled  : Prop   -- NOT discharged by architecture pathing (actuator teeth)

/-! ## Non-vacuity — independence is achievable, and capture is caught -/

/-- An architecture where the official influences nobody. -/
def independentArch : Arch where
  official   := ⟨0⟩
  owner      := fun _ => ⟨0⟩
  powered    := fun _ => ⟨0⟩
  controls   := fun _ _ => False
  flow       := fun _ _ _ => False
  influences := fun _ _ => False

/-- An architecture where the official influences itself and owns the target. -/
def capturedArch : Arch where
  official   := ⟨0⟩
  owner      := fun _ => ⟨0⟩
  powered    := fun _ => ⟨0⟩
  controls   := fun _ _ => False
  flow       := fun _ _ _ => False
  influences := fun a b => a = b

theorem independentArch_independent (k : PathKind) :
    IndependentAt independentArch k ⟨0⟩ := by
  intro c _ hInf
  obtain ⟨p, hF, _⟩ := hInf
  exact hF

/-- Capture is expressible and bites: the target is owned by an official-influenced
    principal, so it is NOT independent. -/
theorem capture_breaks_independence :
    ¬ IndependentAt capturedArch PathKind.signal ⟨0⟩ := by
  intro hIndep
  exact (hIndep ⟨0⟩ ReachableBy.refl) ⟨capturedArch.official, rfl, Or.inl rfl⟩

/-- The paid path: an `InterlockBasis` is constructible only by ALSO supplying standing and
    coupled (here trivial) — independence alone does not yield one. -/
def demoBasis : InterlockBasis independentArch ⟨0⟩ where
  independent := ⟨independentArch_independent _, independentArch_independent _,
                  independentArch_independent _⟩
  standing := True
  coupled  := True

/-! ## The core non-collapse — wiring ↛ standing / coupling

A world carries out-of-band standing/coupling facts that the wiring diagram (the `Arch`
projection) does not contain. Two worlds with the SAME wiring can differ in standing — so
no function of the architecture recovers it. "Wiring diagrams don't contain track records." -/

structure ArchWorld where
  arch          : Arch
  standingHolds : Bool   -- out-of-band track record — NOT a function of the wiring
  coupledHolds  : Bool   -- out-of-band actuator teeth — NOT a function of the wiring

def ArchWorld.projection (w : ArchWorld) : Arch := w.arch

/-- Two worlds, identical wiring, different standing. -/
theorem wiring_does_not_determine_standing :
    ∃ w₁ w₂ : ArchWorld,
      w₁.projection = w₂.projection ∧ w₁.standingHolds = true ∧ w₂.standingHolds = false :=
  ⟨{ arch := independentArch, standingHolds := true,  coupledHolds := true },
   { arch := independentArch, standingHolds := false, coupledHolds := false }, rfl, rfl, rfl⟩

/-- No function from the architecture recovers standing — the static checker is structurally
    blind to it. (Same shape as the witness-separation no-go, aimed at the wiring diagram.) -/
theorem no_arch_bridge_to_standing :
    ¬ ∃ f : Arch → Bool, ∀ w : ArchWorld, f w.projection = w.standingHolds := by
  rintro ⟨f, hf⟩
  have h1 : f independentArch = true :=
    hf { arch := independentArch, standingHolds := true,  coupledHolds := true }
  have h2 : f independentArch = false :=
    hf { arch := independentArch, standingHolds := false, coupledHolds := false }
  rw [h1] at h2
  exact Bool.noConfusion h2

def doctrine : List String :=
  [ "a captured checker cannot mint an admissible check — independence is a basis-revocation reason",
    "independence is reachability over named path kinds; decidable from the dependency graph",
    "standing (track record) and coupling (actuator teeth) are NOT architectural — wiring ↛ standing",
    "a checker that emits independence:PASS without naming the standing/coupling gaps is the stuck-at-safe failure under test" ]

#eval doctrine

end ToolTheory.Scratch.ControlPathIndependence
