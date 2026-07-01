/-
  The Witnessed Derivation Calculus — public aggregator.

  Ported 2026-06-26 from the ratified experiment surface
  (`experiments/no_free_lift_wiring/`, artifact commit 5eb5629; ratification record
  `RATIFICATION-v1.3.md`). A narrow proof-theoretic calculus for witnessed movement
  across typed boundaries: a defined judgment `Lift` with composition, genuine
  multi-context cut (cut-admissibility), soundness, provenance, non-manufacture, and
  2.0 model-independent normal-form factorization for any bridge system satisfying the
  local commutation law, with the freshness model as the public instance.

  Mathlib-FREE by construction. No module under `LeanProofs/Witnessed/` imports
  Mathlib, so every receipt's axiom footprint stays at core Lean (≤ propext,
  Quot.sound) and is re-attestable in isolation via `lake build Witnessed`
  (enforced by the separate `Witnessed` lean_lib — see lakefile.toml, A1).

  This is NOT a revival of the retired maximal "Admissibility Calculus": its scope is
  witnessed derivation across typed boundaries. The public surface now includes an
  additive positive-formula cut-elimination layer, a Gentzen left/right sequent
  presentation, and a canonical resource/residue no-suppression slice. Model→world transfer, universal normalization, implication,
  full linear logic, and full composition-classification remain fenced (see
  `docs/WITNESSED-FRONTIER-REGISTER.md`). Receipt names are frozen per MIGRATION §C.

  Renames from the experiment surface: `Wired.Authority` → `AuthorityModel` (a study
  copy, NOT the 1.0 `Admissibility.Authority` kernel); `Successor.WitnessedDerivation`
  → `Derivation`; `Successor.Tightened` → `Discipline` (and `tightened_metatheory`
  → `discipline_metatheory`); `Successor.DisciplineObstruction` → `Obstruction`.
-/

-- Spine (No-Free-Lift conservation law and its coordinates)
import LeanProofs.Witnessed.CarryLaws
import LeanProofs.Witnessed.Coordinates
import LeanProofs.Witnessed.Divergence
import LeanProofs.Witnessed.NoFreeLift
import LeanProofs.Witnessed.AbstractNormalization  -- 2.0: model-independent normalization (admitting-class)
import LeanProofs.Witnessed.CommutesNecessity      -- 2.0: the commutation law is load-bearing (necessity)

-- Modeled kernels + the wire (Authority ⊕ Freshness into the spine)
import LeanProofs.Witnessed.Freshness
import LeanProofs.Witnessed.AuthorityModel
import LeanProofs.Witnessed.Embedding

-- The calculus + its model-admission discipline
import LeanProofs.Witnessed.Derivation        -- judgment `Lift`, composition, non-manufacture
import LeanProofs.Witnessed.Sequent           -- contexted sequent presentation over `Lift`
import LeanProofs.Witnessed.Formula           -- positive formulas + explicit-cut elimination
import LeanProofs.Witnessed.Gentzen           -- Gentzen left/right sequent presentation
import LeanProofs.Witnessed.HeadOnlyGentzenCutFailure -- archived: head-only cut-elim fails (motivates the position-general repair)
import LeanProofs.Witnessed.ResourceSequent   -- occurrence-sensitive resources + residue preservation
import LeanProofs.Witnessed.ResourceChecker   -- position-pinned validation relation
import LeanProofs.Witnessed.ResourceCheckerExec -- executable Bool gate over derivation traces (Slice A)
import LeanProofs.Witnessed.LaunderingCorpus   -- named adversarial laundering specimens (Slice C)
import LeanProofs.Witnessed.Normalization      -- normal-form factorization (freshness instance of AbstractNormalization)
import LeanProofs.Witnessed.Discipline         -- four-axis WitnessedDiscipline (was Tightened)
import LeanProofs.Witnessed.AxisIndependence   -- four separating finite models
import LeanProofs.Witnessed.Obstruction        -- annex: retired `Discriminating`, factorization
