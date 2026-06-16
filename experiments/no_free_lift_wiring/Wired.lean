-- Wired — the full attestation-boundary tower (experimental wiring, isolated).
-- Library root: importing this brings the whole wired tower into scope.
-- (Not a calculus until the composition-classification gate clears — see
--  COMPOSITION-CLASSIFICATION-TARGET.md.)
--
-- Tower (acyclic; schema upstream, model downstream):
--   CarryLaws ─┬─ Coordinates ─┐
--              └─ Divergence ──┼─ Freshness ─┐
--   Authority ─────────────────┘             │
--   NoFreeLift ───────────────────────────── Embedding ── CoCompilation
import Wired.CarryLaws
import Wired.Coordinates
import Wired.Divergence
import Wired.Authority
import Wired.Freshness
import Wired.CanonicalFreshness
import Wired.NoFreeLift
import Wired.Embedding
import Wired.CanonicalEmbedding
import Wired.Families
import Wired.Standing
import Wired.Custody
import Wired.BudgetMonotonicity
import Wired.ConsumerFreshness
import Wired.CoCompilation
