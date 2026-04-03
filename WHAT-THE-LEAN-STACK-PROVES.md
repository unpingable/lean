# What the Lean Stack Proves

## The short version

The Δt framework's informal theory contained three category errors where prose was collapsing distinct claim types into single sentences. Machine-checked formalization forced each claim to declare its type, then proved or falsified it on those terms.

Three slogans died. Four corrected statements replaced them. The theory is sharper and says less.

---

## Layer 1: Static Topology (TaxonomyGraph.lean)

### What it proves

The 15-domain cybernetic failure taxonomy has a static pipeline graph with exactly four terminal nodes: Δg (gain mismatch), Δa (actuation mismatch), Δx (scale inversion), and Δh (hysteresis). These organize into three terminal families, not one.

Every non-terminal domain is classified by which terminals it can reach:

- **Δw, Δc, Δe** reach only Δh (governance pipeline)
- **Δs, Δm** reach only Δg/Δa (signal/model pipeline)
- **Δk** reaches only Δx (coupling pipeline, graph-isolated)
- **Δn, Δo, Δb, Δp, Δr** reach both Δg/Δa and Δh (branching precursors)

Role labels are structurally coherent for 10 of 11 roles. One mismatch (Δx labeled "cross-scale transmission" but structurally terminal) is left unresolved as data.

### What it killed

**"Δh is the universal sink."** False as a graph-topological claim. Δs and Δk cannot reach Δh through any pipeline path. The signal family dead-ends at gain/actuation. The coupling family dead-ends at scale inversion.

### What it does NOT prove

- Whether Δh is a temporal attractor (dynamic claim, not a graph property)
- Whether the role labels are "correct" in any domain-external sense
- Whether the edge weights or directions are complete

---

## Layer 2: Branch Selection (BranchSelector.lean)

### What it proves

The branching precursors (Δn, Δo, Δb, Δp, Δr) are dual-channel degraders. Each precursor event burns two budgets simultaneously:

- **model_quality** — when exhausted, closure family is gain/actuation (Δg/Δa)
- **authority_coupling** — when exhausted, closure family is hysteresis (Δh)

Closure family is selected by whichever budget exhausts first. This depends on the interaction of burn profile (which precursor) and pre-existing budget asymmetry (system condition), not on precursor type alone.

The formally verified results:

- Same events on differently damaged systems produce different closure families
- Same system under different burn profiles produces different closure families
- Pre-existing damage can override the nominal tendency of a burn profile (susceptibility/priming)
- Both budgets are monotone non-increasing

### What it killed

**"Precursor type determines closure family."** False. A system with weakened authority coupling is primed for hysteresis regardless of whether the precursor is model-heavy or governance-heavy. The selector is the budget asymmetry, not the event identity.

### What it does NOT prove

- That the burn profiles are empirically calibrated (they reflect graph structure, not measured data)
- What happens after closure is selected (Layer 3 handles this for hysteresis)
- Whether Δg vs Δa selection within the gain/actuation family follows a similar pattern
- Whether simultaneous exhaustion has distinct real-world semantics or is an artifact of toy parameterization

---

## Layer 3: Persistence Dynamics (PersistenceModel.lean)

### What it proves

Once authority-consequence coupling breaks (Δc), hysteresis (Δh) is driven by cumulative rollback depletion under detached commits. The model has five states (aligned, detachedShort, detachedWarn, hysteretic, restructured) and five events (detach, commit, idle, reattach, externalRepair).

The formally verified results:

- Rollback capacity never increases under internal events
- Only detached commits burn capacity; idle detachment does not
- Hysteretic is absorbing for internal events (no internal reattachment works)
- A system can reach hysteretic without ever entering the prolonged-detachment warning state
- External repair exits hysteretic but produces a new regime (restructured), not original baseline
- A restructured system can become hysteretic again, typically faster

### Three-way recovery distinction

| | Mechanism | Result |
|-|-----------|--------|
| **Internally recoverable** | Reattach while capacity remains | Original baseline restored |
| **Externally repairable** | External restructuring | New operational regime, reduced capacity |
| **Locked in** | No internal event exits hysteretic | Requires external intervention |

### What it killed

**"Prolonged contiguous detachment is necessary for reset failure."** False. Repeated short detachment episodes, each individually recoverable, can accumulate into irrecoverability. Episode recoverability does not imply lifetime recoverability.

**"Repair restores baseline."** False. External repair produces RESTRUCTURED, not ALIGNED. The system is operable again but not equally resilient. Repair restores operability, not original rollback margin.

### What it does NOT prove

- That the rollback depletion rate is empirically calibrated
- What external repair concretely consists of (the model treats it as an event, not a process)
- Whether there are conditions under which rollback capacity should regenerate
- Whether the three-way distinction exhausts the possibilities (there may be other recovery modes)

---

## What the stack as a whole says

The informal Δt framework theory was compressing three distinct claim types into single sentences:

1. **Static reachability** (graph property) was conflated with **temporal attractor dynamics** (persistence property) — compressed into "universal sink"
2. **Contiguous duration** was conflated with **cumulative commitment** — compressed into "long enough"
3. **Episode outcome** was conflated with **lifetime trajectory** — compressed into "recoverable"

All three conflations made the theory sound stronger than it was. The formalizations force the distinctions.

The corrected theory has a layered structure:

- The static graph determines **which terminal families are reachable** from a given precursor
- The budget-depletion race determines **which family actually wins** for a given system in a given condition
- The persistence dynamics determine **what happens once authority-consequence coupling breaks**
- External repair determines **what comes after lock-in** (operability without original resilience)

Each layer has its own claim type. Structural claims stay structural. Dynamic claims stay dynamic. Restorative claims stay restorative. They don't get to share a sentence.

---

## The meta-result

Formalization did not confirm the informal theory. It forced the informal theory to stop cheating.

The theory's center of gravity was "Δh captures everything eventually." That was doing three jobs at once: a graph claim, a persistence claim, and a restorative claim. Each job needed a different model. Each model, once built, killed part of the original slogan while sharpening the part that survived.

The machine didn't make the theory more impressive. It made it more honest. That turned out to be the same thing.
