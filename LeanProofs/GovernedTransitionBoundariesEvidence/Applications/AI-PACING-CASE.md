# AI-pacing external-evaluation case

This public-evidence application promotes the bounded instance from private
source commit `3b9a673633b7778d140a2f80f1251913eb35717f`. It models a lab
`L`, external evaluator `E`, evaluator-controlled harness `H`, bounded
evaluation `B` of `M_eval`, finding `R`, later deployment transition `T`,
claim `C`, regulator `G`, and public beneficiary `P`.

## Result

The case is partly derived, partly refused, and partly inexpressible.

The public factorization theorem
`target_collision_blocks_explicit_factorization` does the central work.
The public fixed-policy definitions `ConsumerPolicy` and
`ProductRelianceAuthorized` supply the consumer-indexed reliance check.
`bounded_finding_does_not_transport_to_deployment_claim` gives the same `R`
in two selected deployment contexts while exact standing for `C` differs, so
no uniform decoder from the finding to that target exists.

The remaining promoted instance results are:

- `valid_target_transport_with_unauthorized_reliance_is_refused`: exact
  current support for the selected claim does not override a policy naming a
  different consumer.
- `future_ex_post_residue_cannot_supply_present_reliance`: a finding acquired
  at 200 is future-dated at decision cut 110, cannot support present reliance,
  and constructs `operationalRelianceNotEstablished`.
- `supported_claim_does_not_mint_deployment_authorization`: an admitted
  certification proposal still lacks authorization in an empty authorization
  list.
- `regulator_reliance_does_not_establish_public_authority`: the regulator's
  reliance result is constant while the local beneficiary-selection,
  delegation, and consent target differs.
- `bounded_residue_does_not_establish_access_independence`: the same finding
  occurs with granted/revocable provider-controlled access and with the
  selected compelled-access control.
- `fully_admitted_expressible_fragment`: the narrow positive fragment
  constructs when exact target support, the exact consumer and purpose, and a
  separate deployment authorization are supplied.

These are fixture-level results. They do not say that the evaluator is wrong,
that either access regime is sufficient, or that every deployment claim is
unsupported.

## Exact positive assumptions

The positive fragment assumes the finding's bounded-support bit, exact
artifact identity (`M_deploy := M_eval`), exact deployment dependency, current
evidence (`acquiredAt = 100` at cut 110), the exact consumer with both named
reliance-view grants, the selected certification purpose, and a separately
supplied authorization record. A different artifact is named as
`M_deployChanged`, but the file supplies no relation from `M_eval` to it.

## Expressivity boundary

The current public corpus has no native representation for:

- provider control over granted, revocable, curated, or scheduled API access;
- non-identity transport from an evaluated artifact or interface to a
  deployed artifact or system; or
- authority or reliance exercised by a regulator on behalf of a
  non-consenting beneficiary.

The Lean file uses only local finite coordinates to expose the access and
beneficiary gaps. They are not general-purpose access-governance or
public-representation abstractions. The positive fragment uses identity; it
does not repair the missing cross-artifact relation.

Temporal refusal is not an ordinary unindexed factorization edge. The private
source required Nightshift's explicit acquisition and evaluation times; the
public application retains that explicit comparison in `assessFindingAt`.
Later residue therefore does not become earlier reliance in this fixture, but
no general temporal-standing theorem is claimed.

Repository source-custody metadata is separate from provenance of the finding.
The private source's additional diagnostic-custody auxiliary was not required
for the promoted seven-result surface and is not promoted here.

## Prior-art boundary

Collingridge's dilemma of control is surrounding prior art on the timing of
knowledge and control. Pearl and Bareinboim's causal transportability and
selection-diagram work is surrounding prior art on when evidence from one
setting supports claims in another. No novelty claim is made for those general
governance or transportability problems.

The corpus-specific result is narrower: institutional authority does not mint
missing evidence transport; later residue does not mint earlier reliance
standing; and bounded evidence supports only the targets for which transport
and reliance are independently admitted.
