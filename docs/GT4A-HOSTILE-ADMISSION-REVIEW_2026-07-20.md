# GT-4A hostile target-admission review

Date: 2026-07-20

Disposition: **PASS — H01–H16 fail closed**

Each case was injected against the admitted packet/target model and had to be
rejected by the named independently exercised comparison.

| Case | Injected false claim | Target detector | Result |
| --- | --- | --- | --- |
| H01 | changed theorem type | normalized target type SHA-256 | REFUSED |
| H02 | changed body with retained type | normalized target body SHA-256 | REFUSED |
| H03 | added/removed axiom | exact compiled axiom-set equality | REFUSED |
| H04 | Scratch import | transitive import denylist | REFUSED |
| H05 | campaign/stage assumption | dependency allowlist and denylist | REFUSED |
| H06 | C02 presented as qualified | exact exclusion disposition | REFUSED |
| H07 | C04 omitted | required boundary-key/value check | REFUSED |
| H08 | C01/PaidCutProbe admitted | authorized path/import set | REFUSED |
| H09 | C03/SpineProjection admitted | authorized path/import set | REFUSED |
| H10 | hostile declaration removed | exact 244-declaration evidence census | REFUSED |
| H11 | source ratification called public validation | target claim-state check | REFUSED |
| H12 | dual canonical ownership | single-active-owner check | REFUSED |
| H13 | packet/content drift before admission | packet and target digest comparison | REFUSED |
| H14 | non-injective namespace map | target-name uniqueness/collision check | REFUSED |
| H15 | matching name with altered content | declaration-content digest | REFUSED |
| H16 | excluded adapter through an aggregate | aggregate transitive-closure denylist | REFUSED |

The positive baseline also required the exact packet/archive path sets, all 13
mapped leaf files, both exact aggregate import lists, all 704 declaration
identities, the exact axiom census, and the stable/evidence custody split.

