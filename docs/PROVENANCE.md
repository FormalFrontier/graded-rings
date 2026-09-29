# Provenance and contributor credit

Authors: Formal Frontier Agents. Original project code, tests and prose are
licensed under [Apache-2.0](../LICENSE). AI agents developed the mathematical
constructions, formal proofs, interface repairs, examples and documentation.
Contributor identity is not an assertion of legal copyright ownership.

## Original mathematical expression

Atlas authored the original project units at the following immutable development
revisions. These identifiers document lineage; a parentless release need not
contain the development commits themselves.

| Material | Original project revision |
| --- | --- |
| Quotient grading | `72f230524c030cf4bbd98225aab504f0e55ff212` |
| Full graded localization | `66d3033833f3f8d686c5d0ee2a9b2cdea764b5ec` |
| Irrelevant-ideal finite generation and finite type | `067a35d5431ff9faae1ecc12b36b6adf8ef60c11` |
| Noetherian criterion | `ab55e148b20ab3c643bb3d489dd0277e0e467d08` |
| Homogeneous prime correspondence | `c08489c3cbba59a57b474de419f3b70eb66ef290` |
| Bundled graded quotient map | `47cf71c880f68cd68a84c197bfa35d8364cb5602` |
| Symmetric algebra grading and functoriality | `40a84d89ad4709b9c30b4fcfe0b0aec9f11336e9` |
| Prime-multiplicity and homogeneous polynomial localization | `f7d5f37ea732469bf2b4e53311044276d5317f05` |

The mathematical ideas draw on Vakil's *The Rising Sea*, October 21, 2025 draft,
especially the graded-ring exercises 4.5.F–H and the denominator-order application
5.4.N. Section 7.4.4, Exercise 7.4.D motivates the selected-component Veronese
ring; only its algebraic ring layer is provided here, not Proj invariance.
Section 7.4.4, Exercise 7.4.E (printed page 215) motivates the separate
old-degree homogeneous polynomial-lift prerequisite; its full positive-Veronese
degree-one-generation conclusion is not established by that prerequisite.
A later source adapter or explanatory exposition is not automatically an
earlier source of the generic Lean proof. The project distributes its own formal
expression and summaries, not the restricted-redistribution PDF or source prose.

## Interface work and assembly

Formalization Worker A performed three distinct contributions:

- Dependency compatibility and root clients, revision
  `0ae011fa1713e9b0c5f7b8eb3ff111c1f9ab152f`: Task
  `hive-request-75ce6d4e937aca14c16ae92199855965d1994ec5`, UID
  `4024c09e-be29-4bab-9b0b-8e847650717d`.
- Native interfaces and direct clients, revision
  `2171b3f6cc3359710145632f497c3eab7da06d56`: Task
  `hive-request-83026371d8f3c7686d656b9c3a426905c563ade0`, UID
  `3469a5fa-4c0c-4527-abbe-50d1707ebc9b`.
- Computation-preserving private localization repair and clients, revision
  `db336fc7f0dab7a41e79cd374e79d1b9ead492e5`: Task
  `hive-request-cc1bf3e5e5e13b4cdf9968e1fc3ff843f3ebe13a`, UID
  `79ef8c63-512e-40cc-9432-0b1a8b8c441e`.

Atlas supplied the quotient private-helper repair at
`7743052b678421deabe6af5f7623682290a54b49`, the prime-multiplicity native
prototype at `2cf73d29a4d78c315d1428d8d2999629f26d22f7`, the remaining native
assembly and private valuation clients at
`985ac0a9a72e4dc51d3e4dc459416df8e6fa16b2`, and the standalone examples and
reader documentation. The examples apply the existing project API; they do not
copy textbook examples or introduce new public theorems.

The release-readiness assembly also adds Atlas's `valuationDef_pow` computation
lemma so that simplification of prime powers respects the existing
`valuation_apply` normal form. The original `valuation_apply_pow` theorem and
proof are retained; its redundant simp attribute is removed. Private direct/root
clients exercise both simplification and explicit theorem use.

Worker B's no-build origin inventory informed this attribution: Task
`hive-request-a210663d01c940dc5adae2c334f66182a9712eaf`, UID
`f562c537-633e-4d72-aa90-dab7f13ef2d9`, revision
`9fa53f6bcdbf9f1a3cd83c2a24f2d19f15c4f7d5`. That bounded inventory was not
an independent final-candidate review or a legal clearance.

## Degree-multiplying homogeneous-localization maps

The producer [`HomogeneousLocalizationMap.lean`](../GradedRings/HomogeneousLocalizationMap.lean)
was carried byte-for-byte from the isolated incubator leaf
`803803a1a72fbe9fb0031f7b6cb892e0b9bd54cd` (producer SHA256
`4b504c4685a3d99b26b60f59a0399ac6f249c7b38042efb0ae39e1011f34214b`).
Original producer, proofs and [direct client](../test/HomogeneousLocalizationMap.lean)
were authored by worker-a Task
`hive-request-b0b74cdb7e102204e305196597835a728b60ad9a`, UID
`02a35b9d-d5a4-4ab9-bebc-4d467cf904c6`. Its accepted isolated algebraic
scope was independently reviewed by worker-b Task
`hive-request-69717dafcfc6768e408517e86285b84e286a79ee`, UID
`dd54184b-2e1a-44c9-b378-36c54f128810`, at review revision
`21941d8e30a8139e67339b05d508b58db458d919`. The focused evidence at
`cf157b47bf9cb1633b5f8c7c7584ea33e27958e1` covers the isolated producer
and client, not the full combined incubator or destination graph. Historical
review and evidence do not certify this library's expanded test/root closure.

Transfer worker-a Task `hive-request-da147dee68ad90f804621f1f9a7f233b492b197f`,
UID `13960c20-49f8-4964-9222-020d8a4a1f7f`, retained the producer's proof
expressions unchanged, adapted only the client import and namespace, added root
registration and an aggregate-import witness, and prepared the documentation
and metadata. This distinct transfer credit neither reattributes the original
proofs nor subsumes the earlier three Worker A contributions. Exact destination
revision, review, checks, maintainer acceptance and publication are tracked in
the project record; this description makes no source-coverage or release claim.

The copied producer retains **Jujian Zhang's 2022 copyright notice**, its
Apache-2.0 notice and the native homogeneous-localization authors **Jujian Zhang
and Eric Wieser**, alongside the original Task credit. Native quotient and
same-index map constructions remain dependencies of the new algebraic proofs;
the destination's collective author credit does not replace those notices.

## Selected-component Veronese rings

The original mathematical/code expression in
[`GradedRings/Veronese.lean`](../GradedRings/Veronese.lean) and the algebra-only
client examples in [`test/Veronese.lean`](../test/Veronese.lean) were written
by worker-b Hive Task `hive-request-e97f548d3626371a173eb011840a7070b24d81bb`
(UID `0e231558-4793-4185-8f55-2bad40d363bd`) in the incubator. The exact
source commit is `c44fc718068e386312e657499b1be18042209d4b` (tree
`e2a21550088d303b7994f640281b3c045a6af83e`); the 9,085-byte original
ring file `Incubator/RingTheory/GradedAlgebra/Veronese.lean` has SHA-256
`7d2a99aef90cfe6cabd74ae60dac0bf2f7f5d1969f4be7f2d3b485fa33583e0f`.
Its accepted *isolated* mathematical candidate was independently reviewed by
worker-a Task `hive-request-8b27bf143706fd619df99eb5ed82bc588ad80938`
(UID `7323f9a9-149a-461e-98bf-282edc07b8ae`) in report-only revision
`2cca84305bf0063eb6ef6e6da3c6d36afce98121`. The focused source-only
verification is at `12c5e753c351170d6ee82d1f19fd51cc00235e81`.
Neither historical review nor evidence checks this expanded destination graph.

This destination transfer was prepared separately by worker-b Hive Task
`hive-request-452e72b0249229e666237dac51cb3c6627c80ab7` (UID
`9f4955d3-13a8-41a9-9f4a-e491538f56ee`) from the existing Graded Rings
main snapshot. It retains all of the original ring's declarations,
hypotheses and proof expressions, adds a truthful Apache-2.0 SPDX/collective
author header, corrects the top-level summary to distinguish an arbitrary
index from positive-index results, and splits five algebra-only examples into
the direct client. The transfer also wires an aggregate import and a private
root witness, and writes the [new guide](Veronese.md), API summaries and metadata.
The guide is new project prose, not copied textbook text; the original
incubator scheme guide was consulted for API meaning, not reproduced here.
The original author and distinct transfer author receive separate credit;
adding a license header or noting AI authorship does not itself clear rights.
No new verbatim third-party code or assets were identified in the transferred
ring/clients; mathlib APIs remain imported dependencies with their own
attribution. Authentic earlier third-party notices and original contributions
remain unchanged. Exact destination revision, independent promotion review,
new-graph checks, acceptance and publication belong in the owning work record,
not in this non-self-referential shipping tree. The destination code has since
received exact-revision independent promotion review, successful three-target
build and private-inclusive standard-axiom checks, and owner code acceptance;
the separate final release review, acceptance and verified private-GitHub
publication of official revision `0a5c69da9b24beb5c33ddddbfe4d0067e53146ec`
are finished. Those results precede and do not certify the later homogeneous-lifts
destination graph.
No source-coverage decision is claimed.

## Homogeneous component surjectivity and polynomial lifts

The byte-identical [producer](../GradedRings/HomogeneousLifts.lean) originates at
the isolated-accepted incubator commit
`99cfa62e8432c1ed0f5abe37adab68abf4d28835` (tree
`e3082d096616cbeca867e3b953c8ad6e1ac2660c`), path
`Incubator/RingTheory/GradedAlgebra/HomogeneousLifts.lean`, 4,712 bytes,
SHA-256 `36b4241e288081ff1396e6f014701a702c42c24554e49edeefaabce93bd5df28`.
Original producer and [direct client](../test/HomogeneousLifts.lean) were written
by worker-b Hive Task `hive-request-5f3d8b70c36747cebf20677044967e35d889fc0d`
(UID `c2ffb0a9-dadb-4457-ab90-47771a830889`). Its author evidence is at
`4d3f78d8133ca1a91deb8cb0f093a7aa3b5bce2d`; the fresh independent
worker-a review by Task `hive-request-a53de5e78ca5a57e03206ad90d69830cdc01cf57`
(UID `30d90e6f-81de-4065-b6da-99f7134ac4dd`) is at
`999447d64b3ce82c255749db90ee10b016eed4af`. Those records concern the
isolated inputs, not this enlarged destination graph.

Distinct worker-b transfer Task
`hive-request-aeec4e05810ad9f84cf32825cd5c157540fda1ae`
(UID `7178cf28-05be-443d-a28b-07a60810c215`) retained every producer
byte, changed the direct client's import and namespace only, and added an
aggregate-import regression witness, [guide](HomogeneousLifts.md), root
wiring, and metadata. The source's author and Apache-2.0 notice remain
authentic and unchanged; the new guide is project prose, not extracted book
text. The license label and contributor credit alone do not establish rights
clearance. No PDF, third-party code, images or substantive source prose is
copied in the transfer; mathlib is imported as the pinned formal dependency.
The original guide's dated *isolated candidate, not registered in roots*
status describes its earlier incubator revision, not the destination: this
library registers both the aggregate producer and direct client. The exact
destination code at `99df5f2effcf2ebe52a91d94cbd15c3090401cca` (tree
`3526962263e453708d3ce6f72f0c92a991ee8252`) received independent
author-distinct review 4476 and the native run 712 three-target build and
private/generated-inclusive standard-axiom audit. Atlas separately accepted
the code and rights and protected-integrated it on 2026-09-28 at 09:12:13 UTC.
These destination results are not conferred by the isolated review or preceding
Veronese publication, and do not accept or publish a subsequent release.
This homogeneous-lifts subsection makes no positive Veronese-generation,
Proj, source correspondence or coverage claim; the separate positive-index
generation transfer is documented below.

Documentary release preparation from that accepted code was authored by
worker-b Hive Task `hive-request-4dea59bdf7ad709e15baf8946d40199f5c045cdd`
(UID `cec968d7-34b9-4757-bf6e-1983a8515fa2`). Its work is confined to the
README, API and homogeneous-lifts guides, this attribution, and release metadata;
it does not claim original mathematical authorship, independent review, release
acceptance or verified publication. The original producer, separate transfer,
third-party dependency and prior project contributor notices remain credited.

## Positive-Veronese degree-one generation

The original mathematical proof and [direct client](../test/VeroneseDegreeOne.lean)
were authored by worker-b Hive Task
`hive-request-45b307ef0b08baacd6a851dadec8faa23ee22d69` (UID
`65fe43bb-2c1b-4320-b724-f8b1f1fa063a`) in the *isolated, unregistered*
incubator commit `f97749780abe31d39fc8a470cb8358a9cd53beb6` (tree
`2d9cc0a21ad1269975047b43024f96e0b95f4dbd`). Its 4,696-byte
`Incubator/RingTheory/GradedAlgebra/VeroneseDegreeOne.lean` producer has
SHA-256 `52dd526dab228168fbac305998e70f3ae463cafd0ee7f7094c50aa7caeb0dee1`.
The original client has SHA-256
`ef3063e9f19a21e7b40c71c62c8dea75a2f632ab78c34b8c0c9b20666bc2af42`.
Its original Apache-2.0 header and Task author attribution remain unchanged in
the [destination producer](../GradedRings/VeroneseDegreeOne.lean), which is
byte-identical to the isolated producer. The direct client changes **only**
the public import and opening/closing namespace. The [destination
guide](VeroneseDegreeOne.md), aggregate wiring, root witness, API map and
metadata are new transfer work, not new original proof authorship.

The original mathematical plan belongs in the source-vakil-foag repository at
`0f5efcced8f8f9cf632f8e7613b641c6bb45a8bc`; its independent *plan*
review at `3344351e10652ec9ec01fe59a0da7641089b36b4` is not code
approval. The original code review at
`69ed24cd8d1b2cbd7f95e4f33e7918896f6c1da7` found guide attribution
and reproduction gaps only; Atlas's **guide-only repair** at
`3502cfa2dad3fca95c6aac8471da379e19cbf85d` (tree
`1c4b4a3d8b72b0c5f79b333f2c108dad23a648b3`) was separately assessed
by a fresh reviewer at `8be88e9f998c8015604e749f1911e00e7455f72d`.
Atlas then accepted isolated readiness, not destination acceptance. Focused
cache-first build and five-declaration actual-origin axiom evidence at
`c9fdc86f3bd73a5d658f77ef15a0d16853f20725` has not been rerun for this
new destination origin, adapted client or root witness.

Worker-b transfer Hive Task
`hive-request-f02ddb3e712c8d7d3a8fcf158241077be901618e` (UID
`3e891418-b2ba-4675-8135-5bc756be8433`) supplied this destination package
from accepted Graded Rings main `9c7519a1bb52569d6db5306cffc36779143d86db`.
Its exact destination commit and fresh review/checks are recorded in the owning
promotion record, not self-referentially in its shipping Git tree. The
original proof author, separate guide repair, plan and code reviewers and
transfer contributor have distinct roles. The mathematical motivation is
Vakil, *The Rising Sea*, October 21, 2025 draft, §7.4.4, Exercise 7.4.E,
printed p. 215, with the coefficient convention in §4.5.6, pp. 151–152;
the original source has not been copied and no source coverage is asserted.

Rights: the isolated proof and client are identified original Formal Frontier
project expression, rather than copied textbook proof or external code;
mathlib and the prior Graded producer APIs are dependencies, not bundled
third-party source. The preserved original Apache-2.0 notice and named
contributor provide traceability but **alone** do not clear rights. The
reviewed original-source locator, byte comparisons, identifiable author
records and absence of reproduced substantive source prose support this
transfer's rights assessment; destination rights acceptance remains with
Atlas and the independent promotion/release reviewers. Existing third-party
notices and dependency attribution are untouched. No source PDF, images or
internal service URLs enter the shipping tree.

## Coherent-tail Veronese equivalences

The original complete producer and direct client are the separately reviewed,
*isolated* incubator commit `3856e87d4348b62c2e2cf56f121877504fbd08f0`
(tree `7f46afaf3c8b7aa6b88e94a6fc5db30e2b74d291`), not an incubator-main
registration. The producer `Incubator/RingTheory/GradedAlgebra/CoherentTailVeronese.lean`
has SHA-256 `918999afc39620116e9d25de7fc64dc5e076765683753c18cbdee92ee93543d4`;
the original ordinary-import client
`IncubatorTest/RingTheory/GradedAlgebra/CoherentTailVeronese.lean` has SHA-256
`e5cee97bc03283ce3d081bd492c678b0cd0284c830c9a31ea9afe2710b924cf7`.
The original standalone guide was
`Incubator/RingTheory/GradedAlgebra/CoherentTailVeronese/README.md`, SHA-256
`ec715cd62fbca34a7c6d00c14602003ffd22c4ddfdcb2c0852fe65b51044ec99`.

The mathematical producer, proofs and concrete clients were authored by
worker-b Hive Task `hive-request-850bf931d8213b955070297ac6413e34cd384237`
(UID `cd358354-3b4d-4c26-af0e-4f6988f9c02f`). The isolated algebra was
independently reviewed by worker-a Task
`hive-request-d2cf958b766059b15c0cd461612954dcacf8eddd`
(UID `b75b902f-3a45-4757-9193-2147ad42e040`), revision
`a2f470de97ed33191670c99dc1d5385a2b1e40c4`; original cache-first focused
build and actual-origin standard-axiom evidence are at
`3c7f9328888383c4e6298f6dc3ca4f867ed17b75`. Atlas accepted that
*isolated* contribution; its review and checks do not transfer automatically.

The distinct destination static transfer was assembled by worker-b Hive Task
`hive-request-a577b764331b8c44444105f6f45d786486b0c612`
(UID `dc93c339-8166-481b-bb86-5417fa5b6cca`), starting from accepted
graded-rings `46df81940a09c6b2a9c72e4db02b1ac6486fa797`. Its exact final
code-branch head and separate report are linked from the owning promotion
record, graded-rings issue #46. The entire original producer body and proofs
are unchanged after the added authentic Apache-2.0 author notice; only the
direct client's import, opening/closing namespace and notice change. The
[destination guide](CoherentTailVeronese.md), root witness, public wiring,
manual API and metadata are new transfer work, not original proof authorship.
No incubator ancestry is part of the destination release history.

Motivation is Vakil, *The Rising Sea*, October 21, 2025 draft, §7.4.4,
Exercise 7.4.F, printed p. 215, with coefficient conventions on pp. 151–152.
The exact original-source locator, not a library usage prerequisite, was
reviewed in source-vakil-foag at `a19f2899b25d97ab41506267294d822d5603630e`
(review `8570bb82adadaac31066680bb19e2030883937e4`); the original PDF
SHA-256 was `d07177aa0317c13490c170fc6ccc6a2ee07989a9120d9958ed3453eefe5b2784`.
The project proof and guide do not reproduce book expression, diagrams, PDF,
images, third-party formal code or substantial book prose. Verified original
project expression falls under the adopted Apache-2.0 policy; identifiable
authorship, isolated source review and non-copying support the rights assessment,
not the file header alone. Mathlib and the old Graded Rings APIs are dependencies,
not recopied source; existing license and contributor notices remain in place.
At this September 28, 2026 static checkpoint, fresh destination rights/API
review, native build and complete transitive standard-axiom audit, acceptance,
publication and source correspondence remain separate future decisions.
The result is algebraic: it does not establish the exercise's Proj conclusion.

## Finite positive-weight exponent blocks

Original mathematical quotient/remainder exposition: worker-a Hive Task
`hive-request-2e65a2cb560898e12809071b7c1bf0802e8b912b`, UID
`ff03eeba-64b1-4705-bdb3-645075b8cb24`, accepted research revision
`99fc1f4c4db929bef77bf1ae36c9f83b8f67d75a` in source-vakil-foag.
Original source-independent Lean proof, direct ordinary client and isolated
guide: worker-b Hive Task
`hive-request-39fb59e3f9cb9338a194533121cce60000ac40a3`, UID
`8e5d9756-58bd-463c-9d7c-97e1c0bc4d55`. Accepted isolated code input:
incubator `807f3e5fbc1b53333fe88347e7f00f40e22f188f`, tree
`248c189889b8ec6152f50ab2cb7580b130ed3330`. Focused original-project
build and complete actual-origin private/generated-inclusive standard-three
evidence: incubator `d0ab13608f6f266c4e9c9fcb2303e05ab8a218a4`.
Independent source-code/rights reviewer: worker-a Hive Task
`hive-request-3fa179b40259c3df1a529f2c7e792e2176bbc858`, UID
`2d045d36-4940-4fcc-ac6e-d9bf1315aec6`, review report revision
`002d37807357f27aa986c2a260329b51fd06e415`. Atlas accepted this
*isolated* candidate under incubator #162; this is not destination evidence.

Static destination transfer, native-module envelope, generic root witness,
standalone guide, wiring and metadata: separate worker-b Hive Task
`hive-request-1c2f48ad1c945d52211972b3803cd12c0262749f`, UID
`80f37f8e-4f3f-4641-9c2d-0e5fb6eabeb9`, starting at sole graded-rings
parent `299e47add1772d9046d65306d7b084587d9935a1` (official published
`db2a1d555639e2a381abbf755982ffdcf126621e` has the same tree). The
producer definitions, statements, hypotheses, private helper and proofs are
preserved; the direct client retains its proof bodies. The authentic project
notice, native-module imports/visibility and client namespace are adapted.
The weighted decomposition is a reusable `Finsupp` fact, not a theorem about
graded ring generation. The destination promotion owner record is
graded-rings #50.
No incubator Git ancestry enters the destination branch.

The exact original-source locator is Vakil, *The Rising Sea*, October 21,
2025 draft, §7.4.4, Exercise 7.4.G, original printed/physical PDF p. 215,
continuation p. 216; grading and degree-zero conventions on pp. 151–152.
The independently verified original asset SHA-256 is
`d07177aa0317c13490c170fc6ccc6a2ee07989a9120d9958ed3453eefe5b2784`;
source research and source correspondence remain outside this library. The
original implementation and project exposition are identified, original
project expression is eligible under the adopted Apache-2.0 policy, and no
book/PDF text, diagrams or external proof code were copied. A new license
header alone would not establish this rights assessment; existing contributor
and third-party dependency notices are preserved. At the September 28, 2026
static checkpoint, applicable native destination build and actual-origin full
standard-axiom audit, fresh independent promotion/rights review, Atlas's
acceptance, protected integration, verified official release and any source
correspondence remain distinct future decisions.

## Weighted-polynomial monomial-adjoin membership

The accepted isolated source is incubator commit
`96035f49afe3af3e74dd285c80db3b18f9615ef8` (tree
`2ed0d7b520252b603f1b671c4326e5477442600b`), owning issue #166,
maintainer Atlas. Its original first-party producer
`Incubator/RingTheory/MvPolynomial/WeightedBlockAdjoin.lean` has SHA-256
`4d0f55793c4addec4e0120686c3994491d0647943be746508bb2b2475b6d1ade`;
the direct client `IncubatorTest/RingTheory/MvPolynomial/WeightedBlockAdjoin.lean`
has SHA-256 `862004413e8d36639364b6691ced2a4853c2d1bfd14406e099485c93507127c0`,
and the initial isolated guide `docs/WeightedBlockAdjoin.md` has SHA-256
`cecced58d9835375b1706f1a5f91afafe0f9bf7837c6f2e3f1903ecbdb098ea7`.
Original proof, direct examples and guide: worker-b Hive Task
`hive-request-02c54ccf8e5ec79a99c29100b383e58fbbf37d58`, UID
`e461a433-ae28-4960-af44-a0f291127294`. The sole repair, removal of two
unsupported copyright-owner header sentences with proofs and client unchanged,
was by different worker-b Task `hive-request-0abf41ae4cc030259077e0ba697493aea02844cd`,
UID `3191b46a-0f33-4201-9069-719451401037`. No such owner assertion is
restored; the authentic Apache-2.0 and collective-author notices remain.

The original focused evidence report `fba1f82224c395b383350ede70f839108aa1c0ab`
(`research/evidence/weighted-block-adjoin/REPORT.md`) records matching mathlib
cache, two focused builds and 2 producer plus 19 direct-client actual-origin
private/generated-inclusive transitive standard-three rows on the original
proof and import graph. Original reviewer worker-a Task
`hive-request-f559692b73c50917c4cc436aed44bd8167b4feb9`, UID
`5fd8eeb0-55e4-41db-8881-29ad068330d4`, reported REQUEST_CHANGES only
for the unsupported header lines at
`002399481ba7984d3bc25033d4b0b6abddaf653f`; this objection is not
retroactively recast as approval. Fresh independent reviewer worker-a Task
`hive-request-799c593fb89bc5735e637a2446886804e96741dd`, UID
`14657e87-8583-409b-ab68-c56044592546`, approved the exact repaired
*isolated* C2 at report `b4e82a905737aec09c38d65c00ab9437ef2f8892`
(`research/reviews/weighted-block-adjoin-repaired/REPORT.md`). Atlas accepted
only that isolated scope at #166/59028, not this destination graph.

The separate static transfer from graded-rings parent
`faf225f03254b0261cc6aa0530aded30e4e6e69a` preserves the original
mathematical declarations, helper privacy, hypotheses, proofs and direct-client
proofs. Its native envelope, project import, aggregate and root witness,
standalone destination guide, metadata and wiring are by worker-b Hive Task
`hive-request-1ea4bc1b3fbaba69e5e89127469d5bdb7d067cf7`, UID
`4883019e-7df8-4c54-a531-c0e01c705167`, under owning graded-rings #59.
Atlas separately chose this delivery home at incubator #166/59181. The earlier
positive-weight arithmetic implementation/client and worker-a mathematical
exposition have their distinct credited authors in the previous section;
Atlas's source-independent interface design is distinct from this proof author.
No incubator Git ancestry is brought into this deliverable history.

Rights rest on the identified original first-party Lean contribution, original
project exposition, independently reviewed exact source and adopted Apache-2.0
terms, **not** on adding a header alone. The motivating Vakil *The Rising Sea*,
October 21, 2025 draft, §7.4.4 Exercise 7.4.G (printed pp. 215–216) and
grading conventions (pp. 151–152), has original asset SHA-256
`d07177aa0317c13490c170fc6ccc6a2ee07989a9120d9958ed3453eefe5b2784`;
no PDF, substantive textbook passage, figure or third-party proof code is
included. Mathlib and the already delivered `GradedRings.WeightedBlocks` are
dependencies, not copied third-party expression. At the initial September 28,
2026 destination checkpoint, the applicable strict three-target build, full
actual-origin private/generated-inclusive standard-axiom audit, fresh exact-
candidate promotion/rights review, maintainer acceptance, protected integration,
verified official release and any source correspondence remain separate gates.

## Weighted evaluation into naturally graded rings

The exact accepted *isolated* implementation was incubator commit
`b12ac06b2c916c286c07aa81d09962b402fc510c` (tree
`3489e19dd154852698907020e0835827bd066fb9`). Its producer
`Incubator/RingTheory/GradedAlgebra/WeightedEvaluation.lean` has SHA-256
`b73c2c7ca3112788648933eab26c8fe2254ce78c416cea6fecfef30a334a5655`;
the original ordinary-import client
`IncubatorTest/RingTheory/GradedAlgebra/WeightedEvaluation.lean` has SHA-256
`d470afe3bb629c40230f57b62f4a710ca7d3d5a9ef4ff501b7653ca52e28e842`;
its isolated guide `docs/WeightedEvaluation.md` has SHA-256
`e0b78a9f77d2e24b78d7f643e0ec83d7d0fa9001a406ee1df0c8cab25bfa7436`.
The original complete mathematical implementation, private helper and direct
client proofs were authored by worker-b Hive Task
`hive-request-9e2f7251baf9a994027c283a681eff56d5e08ad9` (UID
`17076cc9-eac1-4b4b-b67e-20dd4276dadc`), not by the destination-transfer
Task. An independent worker-a Hive Task
`hive-request-857bcba53c78a3d3d0afe825b94d14ee7d3d8b4a` (UID
`f7a50013-c77c-4bfe-9225-cee3c8786432`) reviewed the original source,
API, clients, rights and focused evidence at report commit
`7b4f272b7e9c3b7c776f8e87c73416c2822ff76d`. Atlas accepted only that
*isolated* source artifact; acceptance was not incubator-main registration,
changed-destination review, release or source-coverage correspondence.

The earlier mathematical quotient/remainder exposition for Exercise 7.4.G
was authored by worker-a Task
`hive-request-2e65a2cb560898e12809071b7c1bf0802e8b912b` (UID
`ff03eeba-64b1-4705-bdb3-645075b8cb24`), accepted as source research at
source-vakil-foag commit `99fc1f4c4db929bef77bf1ae36c9f83b8f67d75a`.
Atlas authored the separate *uncompiled* weighted-evaluation interface design
at source-vakil-foag commit `6ccf37c9213f630bc338c1a160025ad8497caef5`.
Neither source-research author is miscredited as author of these Lean proofs;
source correspondence and milestone status stay in the source repository.

The distinct destination static transfer, authentic first-party Apache/author
notices, adapted direct import, ordinary-root witness, standalone guide, manual
metadata and wiring were authored by worker-b Hive Task
`hive-request-8cb3d5978e343cced72cbbc92dfe4a1e2a38e369` (UID
`08d25a25-e613-4627-9614-159cd553f5fb`), from sole accepted Graded Rings
parent `8b28ec75fd2bb2bf70c816c033593cc9b45d7fb6`. The destination
producer body is identical to the accepted isolated source after its new
header; the direct client changes only its header and import path. This
destination guide and aggregate witness are transfer additions, not original
proof authorship. Exact candidate/review/evidence revisions are tracked in
the owning graded-rings contribution record, issue #55; no incubator history
is imported into destination Git ancestry.

Rights: the original Lean proof/client and project exposition are identifiable
first-party project expression under the adopted Apache-2.0 policy, **not**
copied textbook argument, other external formal code, or redistributed book
text. Vakil, *The Rising Sea*, October 21, 2025 draft, §7.4.4 Exercise 7.4.G
(printed pp. 215–216; grading conventions pp. 151–152) is mathematical
background only. The original source asset SHA-256 recorded with its reviewed
source locator is
`d07177aa0317c13490c170fc6ccc6a2ee07989a9120d9958ed3453eefe5b2784`;
no PDF, substantive passage, diagram, or source image is bundled here. The
existing `GradedRings.HomogeneousLifts` API and pinned mathlib are imports,
not pasted proofs; their own authors' and dependency notices remain intact.
An SPDX header alone does not establish rights. At this initial September 28,
2026 static destination checkpoint, applicable new-graph build, complete
standard-axiom check, fresh promotion and rights review, maintainer acceptance,
protected integration, publication and source-specific correspondence remain
separate revision-specific determinations.

## Finite degree-one generation of a positive Veronese

The source of the two mathematical theorem bodies, direct-client proofs and
original standalone guide is the *isolated-accepted* incubator commit
`3064bc3e9dfe13edc041bd384fd1eaa16a381367` (tree
`f286e1fa970d2aa9884924c217a99e5aaed52ceb`), whose sole parent is
accepted repaired adjoin C2 `96035f49afe3af3e74dd285c80db3b18f9615ef8`.
The three original file SHA-256 digests respectively are
`88c5c1cbe5de8017f8357d996d059bd30bcb60a3d519485b0c25828de96538d3`
for `Incubator/RingTheory/GradedAlgebra/FiniteVeronese.lean`,
`0016d4524e48b536b15eedf37cec10b94f5810b8b264efc8106aec4ee27134df`
for `IncubatorTest/RingTheory/GradedAlgebra/FiniteVeronese.lean`, and
`5ffd26aaa440d2b5ef5e5b96c107547c6c62ac77e575808044338c3357d1c984`
for `docs/FiniteVeronese.md`. Original producer, proof, client and guide
author: worker-b Hive Task
`hive-request-65a1de5cb36d5c9acd4b1ec6c0e3e14b38c2ed29`, UID
`442f82c5-c284-49b5-ad83-3cf383581925`. Its evidence-only child commit
`f676de489fc1ca8b3c545c4910a1213ac86ae547` retains the original
cache-first focused build and 3 producer / 19 client actual-kernel-origin
complete transitive standard-three audit, report SHA-256
`b360fd93347ea672cf129398af9c5281e3bbf0a2fd75d200d50f3b6262c663fb`.
These original checks do not verify the changed destination dependency graph.

Fresh worker-a Hive Task
`hive-request-594f2fd401010bf2b8e1e5ce884b8fedd3611385`, UID
`8635540c-8ec0-4db0-8319-b2aec2ffdd70`, independently reviewed the
isolated code, proof integrity, mathematical statement, clients, rights and
source context at report commit `213d9e8eaef89fcd47f043a3b2efdd57e2d8d3ad`
(report SHA-256
`f08e9da7ad79527154eecfd93a072dbfbf0b6eb5c5d4045a842b539d7b959587`).
Atlas accepted that **isolated** contribution under incubator issue #168/59202;
neither that acceptance nor review registers it in shared incubator main,
approves this native destination transfer or certifies source coverage.

The original prerequisite evaluation author was worker-b Task
`hive-request-9e2f7251baf9a994027c283a681eff56d5e08ad9` (UID
`17076cc9-eac1-4b4b-b67e-20dd4276dadc`), reviewed by worker-a Task
`hive-request-857bcba53c78a3d3d0afe825b94d14ee7d3d8b4a` (UID
`f7a50013-c77c-4bfe-9225-cee3c8786432`) and isolated-accepted at
`b12ac06b2c916c286c07aa81d09962b402fc510c` (#164/58771).
The positive-weight arithmetic came from worker-b Task
`hive-request-39fb59e3f9cb9338a194533121cce60000ac40a3` (UID
`8e5d9756-58bd-463c-9d7c-97e1c0bc4d55`), reviewed by worker-a Task
`hive-request-3fa179b40259c3df1a529f2c7e792e2176bbc858` (UID
`2d045d36-4940-4fcc-ac6e-d9bf1315aec6`) and accepted under #162/58631.
Original weighted-polynomial adjoin author worker-b Task
`hive-request-02c54ccf8e5ec79a99c29100b383e58fbbf37d58` (UID
`e461a433-ae28-4960-af44-a0f291127294`) received a C1
**REQUEST_CHANGES** from worker-a Task
`hive-request-f559692b73c50917c4cc436aed44bd8167b4feb9` (UID
`5fd8eeb0-55e4-41db-8881-29ad068330d4`) on review
`002399481ba7984d3bc25033d4b0b6abddaf653f` because its guide asserted
two unsupported copyright-owner claims. Worker-b repair Task
`hive-request-0abf41ae4cc030259077e0ba697493aea02844cd` (UID
`3191b46a-0f33-4201-9069-719451401037`) removed only those lines;
fresh worker-a Task `hive-request-799c593fb89bc5735e637a2446886804e96741dd`
(UID `14657e87-8583-409b-ab68-c56044592546`) approved repaired C2
at `b4e82a905737aec09c38d65c00ab9437ef2f8892` (#166/59028).
The C1 verdict is not reassigned as C2 approval. Previously delivered
arithmetic, evaluation, adjoin and Veronese libraries are reused here; their
proofs are not copied or claimed anew by this transfer.

The motivating original quotient/remainder proof exposition was written by
worker-a Task `hive-request-2e65a2cb560898e12809071b7c1bf0802e8b912b`
(UID `ff03eeba-64b1-4705-bdb3-645075b8cb24`) and independently reviewed
by worker-b Task `hive-request-0bbd1f01f09af516add223eb4e58069ac58e55b0`
(UID `169259a2-25d3-4e6e-a5d2-505d25e94bb0`); Atlas accepted it **as
research**, source-vakil-foag revision
`99fc1f4c4db929bef77bf1ae36c9f83b8f67d75a` (#545/58160).
Atlas authored separate uncompiled interface/design notes at source revisions
`5ef63d95b626d09f55991ce12e51eba4228e3dc4` and
`f51df60ff6a7e7917ffc281f737cdc70ee1140e9`. Research and design
contributors are not thereby authors of the accepted Lean proof bodies.

The distinct *static destination transfer* from sole accepted Graded Rings
parent `8c2d25f00d1fae03a61374e08d997a050f6942d7` (tree
`a2cf6b20f4cb05ea6322f0672a2a0f593972b3b5`) was authored by
worker-b Hive Task `hive-request-b14b274dc65cf6ab1c2988e3ec6f688a5fb15268`
(UID `03efe142-3e26-4c7c-84b8-4db2b93cc34d`). The candidate code, guide,
native import adaptation, aggregate witness and metadata belong to destination
issue #63; its separately retained report binds the exact transfer head and
provider-readback digests. The producer and direct client preserve original
mathematical statements and proofs under the authentic Apache/agent header,
with native `module`/public import and exposure changes only. No incubator
development ancestry or private/research artifact is imported into this
deliverable's history. The existing parent's separately owned adjoin release
must precede this contribution's independently reviewed publication; no
unpublished release or incubator commit is a destination dependency.

Rights: original project Lean and explanatory prose use the repository's
Apache-2.0 terms; the source Vakil, *The Rising Sea*, October 21, 2025 draft,
§7.4.4 Exercise 7.4.G (printed pp. 215–216, conventions pp. 151–152), is
mathematical background only. The independently reviewed original PDF
asset SHA-256 is
`d07177aa0317c13490c170fc6ccc6a2ee07989a9120d9958ed3453eefe5b2784`;
no PDF, source prose or external formal code is bundled. Contributor credit
does not imply unsupported legal ownership. At the September 28, 2026
transfer checkpoint, the new 46-module native graph still requires its own
strict three-target build and full private/generated-inclusive transitive
standard-three audit, independent exact-destination mathematical/API/rights
review, maintainer acceptance, protected integration, separately verified
official publication and distinct source correspondence decisions.

## Prescribed-index weighted-polynomial generators

The reusable `MvPolynomial.exists_finset_weightedVeronese_generators` theorem
was first implemented by worker-b Hive Task
`hive-request-b19ed49dc35a86b4f2c7f461f7a2a8997c0265da` (UID
`a441c096-818a-45de-9581-5f096b28e669`) in isolated code revision
`4786d6fea4f3aaf9e60643218c1b5e9f68ec5af6` (tree
`0f7535d4931d7bd41a01f861104e0679a403477b`, sole accepted parent
`3fb5193e4176820fb00070d6920c8fe6a5032edd`). The 6,384-byte producer,
4,402-byte direct client and 2,239-byte original guide have SHA-256
`04e22f92ea423a2d029d854a8aeb534f06e2ba3e66dc6d7c6a460b24a7861e5b`,
`3b06785a62022f28bc5c9639d99bfda695f58819cbdb735994adb9fcb4d37efe`
and `a940d39a46c75fc4b59bfbf646a3b6abb890f416299e13bb6db8acaf2af1b1b4`.
The original author evidence at `5e84c952d7e2c11c2fdd627a2517fade1bc16cf8`
(`research/evidence/weighted-veronese-generators/REPORT.md`, SHA-256
`9c7ed21f7f89b1a9c45d8d73ddd1b30233b0c46f1d63bc9e5e8052033915e0a5`)
reports a successful pinned cache-first focused producer/client build and
20 actual-origin transitive declaration checks (19 private including generated)
with only `propext`, `Classical.choice` and `Quot.sound`.

Fresh original-candidate review by worker-a Hive Task
`hive-request-c63463c2ee5ed9e6cd9ca9927719b6e7cf21d0f2` (UID
`9848d86f-0a38-433e-ab52-5eb525143762`) is bound to revision
`405a50c72bb6c943d3bbc2067f02f6d2cb9fa078`,
`research/reviews/weighted-veronese-generators/REPORT.md`, SHA-256
`3b55720382633fd013dadf34c7c04b70d1eb47c440b57e6bbf7b1211df6e71df`.
Atlas accepted the exact isolated mathematical candidate on September 28,
2026 (incubator issue #173, comment 59987); the separate delivery-home
decision is recorded in comment 60023. Neither decision asserts that this
library's changed import graph has been checked or accepted. The mathematical
background for Exercise 7.4.H was developed and independently reviewed as
source-only research in `source-vakil-foag` revision
`28cf4fc6081e450474e929aa5a5101a739b3f200` and review revision
`c9f6f6ba4ef68a11d75f8b5ad3cc152514da2890` (source issue #547).
That research does not provide full exercise correspondence or coverage for
this polynomial-only theorem.

The distinct **static destination transfer** from sole accepted Graded Rings
parent `ba0db767001e99f41b0e751f2a900e1d743dcdff` (tree
`65cb47d5deee709a3ef6b38d312dd7693d190d70`) is by worker-b Hive Task
`hive-request-71135ca8e40ee75e265b4be2ece6f790e993636c` (UID
`f002571f-0a86-4430-a7b1-09bbcd5e1b7f`). It preserves the exact
mathematical producer and every direct-client proof body, changing only the
client's producer import; it adds the generic aggregate witness, standalone
guide, public wiring and current metadata. The original Apache-2.0/agent
headers and distinct original author/reviewer/transfer credits are retained.
No incubator ancestry, source PDF, source prose or external proof code enters
the deliverable history. The original isolated build/audit/review do **not**
certify the changed destination graph. At the September 28, 2026 static
transfer checkpoint, the native strict three-target build, full actual-origin
private/generated-inclusive transitive standard-three audit, fresh
author-distinct destination review, maintainer acceptance, protected
integration, separately reviewed verified release and source correspondence
are separate subsequent gates under owning issue #67.

## Finite type of prescribed positive whole Veronese rings

The reusable `GradedRing.Veronese.finiteType_of_finite_homogeneous_generators`
and `GradedRing.Veronese.finiteType_of_finiteType` were first implemented by
worker-b Hive Task `hive-request-7409da348fa71e5989914571ccac1d18d9d8f63c`
(UID `867d8cc9-ae78-4630-8884-8c1bf74e56c4`) in isolated accepted code
`6e5555c9af60edd3c7c56b1ea94010f06c330d42` (tree
`4cbcf309fb7d674965e821e32566e8ab511072c0`). Its original 5,509-byte
producer, 6,900-byte ordinary client and 1,617-byte guide have SHA-256
`07a031758d751fe9f93b2ab34b5e5b737e8258b2d75b4d8b9391ea0a059c7dcb`,
`a8b6d36828eebd977cbda7cc6ec4cf74637e6418b2528b2f982002c223242ab0`
and `5c2b3b478be0772825bd7ca6a345319dea5ea0cdfe233726225565608deb83b0`.
Its complete corrected original evidence is `881ce237e940093862b6e4510b3b4dc5f0fc9b86`,
`research/evidence/veronese-finite-type/REPORT.md` (SHA-256
`e16d5bd51af357fdca644c2549af8ba925303a700819a2d485c5042b18af6919`):
the pinned cache-first focused producer/client build succeeded, and 21
actual-origin producer/client declarations including private and generated
ones passed a full transitive check allowing only `propext`,
`Classical.choice` and `Quot.sound`, without additional axioms, admissions,
unsafe or partial declarations.

Fresh independent worker-a review by Hive Task
`hive-request-d3cf8445db2f67277d03e7f6cf646c173e68ae0c` (UID
`a2791ce3-cf18-4cae-8ae3-201c13e79c86`) APPROVED that **isolated exact
code** in report-only revision `27fbbfeb57f281a47ceaa674313e0bbd3d45b54a`,
`research/reviews/veronese-finite-type/REPORT.md` (SHA-256
`38d4496730ecd3132c4951561f587c94d51ca943e2a1567b2c6efc2a49e93fda`).
Atlas accepted the isolated candidate in incubator issue #174, comment 60032,
and selected this destination home in comment 60081. Neither is shared-main
integration, destination review, official publication or source coverage.

This distinct static transfer is by worker-b Hive Task
`hive-request-8a815ecb69e41d2137adfe71bf53dcec5dbdab5d` (UID
`2fbf4589-ad58-46bf-8055-45fd7dd1925e`) from accepted Graded Rings parent
`d24ef447b3787bf47b54f9815868f8648a59f25d` (tree
`65dd45272d4baa5bb044c37e5be6faedd82c9892`). It preserves the
producer and ordinary-client mathematical expressions byte-for-byte apart
from the exact import substitutions, and adds the generic aggregate witness,
standalone guide, public wiring and metadata. The client retains attribution
for the project-authored `test/FiniteVeronese.lean` mixed-weight fixture.
Original Apache-2.0 and actual author Task/UID headers remain intact; no
incubator ancestry, third-party proof code, source PDF or book expression
enters the destination history. The polynomial-only background for Exercise
7.4.H in the unchanged source metadata does not assert a whole-ring result;
this separate result needs its own source-specific correspondence assessment.

The original focused build/audit/review applies only to its original graph.
At this September 28, 2026 static transfer checkpoint, the native strict
three-target destination build, full actual-origin private/generated-inclusive
transitive standard-three audit and fresh author-distinct exact-destination
review remain open, as do Atlas's acceptance, protected integration,
separately reviewed verified official publication and any source-coverage
decision. Owning destination issue #69 records later exact-revision evidence;
the preceding polynomial contribution has its own separate publication order.

## All-index zero components and the zero-index selected ring

The reusable `GradedRing.Veronese.zeroRingEquivAll` identifies the *entire*
actual new degree-zero component with old `𝒮 0` at every natural index. At
index zero, external new-degree copies remain distinct; `zeroCoefficient`
carries an arbitrary unchanged old-zero coefficient into the whole actual
new zero ring, `zeroVariable` maps to `1` under old-ring inclusion, and
`of_zero_eq_algebraMap_mul_pow` factors each external summand. Surjective
polynomial evaluation yields `finiteType_zero` over that actual new zero ring
without finite type of the original ring. Only `zeroVariable_ne_zeroCopy`
requires `[Nontrivial S]`. Neither whole-ring inclusion injectivity at zero,
a full polynomial equivalence nor a source index-zero convention follows.

The original Apache-2.0 mathematical producer, ordinary-import client and
standalone guide were written by worker-b Hive Task
`hive-request-a4527f02af952e11c47d91c4884c7d869bc58acc` (UID
`9b1f25a8-52cd-4da9-86eb-6f477a7e85b0`) at isolated accepted incubator
code `5667bf12976edfd9938ba0b887e10cea173dbe2a` (tree
`0c7c04ff279968fccabf054bc70ac5fd44d5a3ab`, sole parent
`6e5555c9af60edd3c7c56b1ea94010f06c330d42`). Original whole-file
SHA-256 values are `409cfb5024ce5986ccf658b3706be5c3595f870833d0a4d585d1ac21be31ab40`
for producer, `f603988f475d7b897163e3b719e38fc848e55e306ef11774ccc88eef92c3538c`
for client and `fc0b628386cb904cc585e4eb0a8638ec7ebfab96c517e4de6f746678dd55e58a`
for guide. The client retains attribution for project-authored mixed-weight
fixtures in `test/FiniteVeronese.lean` and
`IncubatorTest/Algebra/GradedRing/VeroneseFiniteType.lean`. Atlas supplied
the prior uncompiled zero-index API design, not these proofs. Native
`GradedRings.Veronese` definitions and positive-index proofs are reused.

Original author evidence `e9ef930c1365e8733f727cdff320fad085011faf`
(`research/evidence/veronese-zero/REPORT.md`, SHA-256
`284184e0f9209e8de1ae603f1aadced124ac9af2e92eceb2b1528314d3b3d6ac`)
records a pinned cache-first focused build and 32 complete producer-origin
transitive standard-three roots, **not** the client. Fresh independent
worker-a mathematical/API/rights reviewer Hive Task
`hive-request-5dff87db89a56c80cee863d7bb748a77058aa902` (UID
`e57cf205-d345-4586-b1ce-bddead009c44`) approved unchanged original
code at `661f30c9ed4049cc6e54556a88d6e0947a43b1df`
(`research/reviews/veronese-zero/REPORT.md`, SHA-256
`940a999dc34859fc65e38894c2627a8e785c47621a30da61a895c088703573f5`).
Separate worker-b supplement Task
`hive-request-67a7f37538b1ea871f41281f3e38b27d42e79f95` (UID
`a0cb2e65-6b7d-499c-be21-2bc194c3bebd`) at
`e79f71a544a218b2faf7893b844dad7fd5034fb4`
(`research/evidence/veronese-zero-client-supplement/REPORT.md`, SHA-256
`56c53953246127703018288327f97043ed702c4f57875cd1377ec097fe49b2ea`)
checks all eight actual client-origin kernel roots including private/generated
ones; nine additional codegen-only names were verified absent from the
kernel, not excluded kernel declarations. All original roots use only
`propext`, `Classical.choice` and `Quot.sound`. Atlas's isolated acceptance is
incubator issue #177 comment 60315; it is not shared-main integration,
promotion, release or source correspondence.

This distinct static transfer is by worker-b Hive Task
`hive-request-5517abb569ec075495c56e99d05aec2d59249feb` (UID
`786f2edf-f384-4f75-be53-ca741454535b`) from accepted Graded Rings parent
`88ff68e101c378a306ea053c1413e3b321042be7` (tree
`09a54269e0f722e871808f6f9d4198132a2601e0`) under owning issue #75.
It retains the entire original producer byte-for-byte, changes only the
direct client's producer import, adds generic aggregate witnesses and adapts
the original standalone guide to this library. Original credit and licensing
remain intact; no incubator ancestry, textbook text, source PDF or third-party
proof code enters the destination history. The original 32+8 origin checks,
donor review and the accepted predecessor's checks do **not** certify this
changed destination graph. Applicable strict three-target native build,
complete private/generated-inclusive transitive standard-axiom audit, fresh
author-distinct exact-destination review, Atlas's acceptance and protected
integration, a separate reviewed and verified official release and any source
correspondence remain independently determined. The existing historical
Exercise 7.4.H metadata describes polynomial-only background, not a claim
of coverage by this zero-index theorem.

## Finite positive-Veronese inclusions

Atlas designed the earlier **uncompiled applicability assessment** at source
revision `2405a46d338acf34cb4afddf51e85628975f7b28`, path
`research/exercise-7-4-h-finite-module-reuse-assessment.md` (13,185 bytes,
SHA-256 `bae23b31c6692958c816b07fdefc15bb320576b4e1eb2df9e66072e77c9ebbfb`).
Fresh independent static reviewer worker-a Hive Task
`hive-request-e74bdffc168ced7e3a75ed6f0ec04d315a6886d2`, UID
`401976e8-6ad8-4d61-9f11-14b78a26c012`, approved only that assessment
at source revision `450cbd9ca0b1af747878a068f4df70f626c3f63d`, path
`research/reviews/exercise-7-4-h-finite-module-reuse/REPORT.md` (10,479 bytes,
SHA-256 `37864d5be54690fa8e3ba97f9992982e0b3019df916fbf09132754fa08b8aed1`).
These research records propose a useful reusable endpoint; they are not a
compiled proof or additional source correspondence.

The [producer](../GradedRings/VeroneseFinite.lean) is byte-for-byte the
3,107-byte isolated incubator module
`Incubator/Algebra/GradedRing/VeroneseFinite.lean` at accepted commit
`aea59d39e8b3c198ddea987fd23aedc1a7d313c6`, tree
`0c6164a6c52da6deea153e495544e9fee3ee039c`, sole parent
`5f493b0606b9961f052a89569f08c5962ae7c0ae`, SHA-256
`1e72d49e10fdc3f1d6603677dbf33c73349ad35ddab2289c032033c88b0bcfb4`.
The [direct client](../test/VeroneseFinite.lean) changes only its producer
import from the original 2,530-byte
`IncubatorTest/Algebra/GradedRing/VeroneseFinite.lean` (SHA-256
`c36414f8e40a5bec9a0af9b7a6503a79af20505736d08e14c5315b7c5c766ffb`).
The [destination guide](VeroneseFinite.md) adapts the 3,110-byte isolated
`Incubator/Algebra/GradedRing/VeroneseFinite/README.md` (SHA-256
`994074089debf5c15c3d33ca1c67a776ba9ec337efb136986939969cca5726cb`)
for this repository, and the root witness and metadata are new transfer work.

The original producer, client and guide were authored by worker-b Hive Task
`hive-request-a6d9833e213de37036a9964c1059dcdaf5959701`, UID
`6555ed03-40cb-463b-9632-266fb9bd7c44`; its evidence-only direct child
is `b6c7ebb53bfd67bada643a2779e2b8c84c45dcbc`, path
`research/evidence/veronese-finite/REPORT.md` (10,969 bytes, SHA-256
`f7523fd896040e583233e402e4615cda2514192ee58ab77a5c770d170c30c853`).
Independent original reviewer worker-a Hive Task
`hive-request-b100b6af01e9101041244a4af0cd5f4b657d3297`, UID
`31c33065-aa56-4c95-8dbc-e5643d740aaa`, approved the exact isolated code
in report-only direct child `fd1fd5a650917304b8df5a346594473574fd4a99`, path
`research/reviews/veronese-finite/REPORT.md` (10,838 bytes, SHA-256
`9f4b11a044c12d2a40b48d345f80b1456f1b9d9a5afec8fd823e53031c05b4a8`).
Atlas's isolated acceptance is in incubator issue #183, comment #61053.
Separate static transfer and destination documentation were done by worker-b
Hive Task `hive-request-317b2951f3df69e9b7cead656f7122e079339ee6`, UID
`4ec3208e-f254-416a-9f8b-a1b70169a447`, from Graded Rings accepted
parent `4687a1118f172dfe78f8612091f1482ee80e4e3b` under owning issue #83.

Collective Formal Frontier Agents authorship and the original producer/client
Apache-2.0 SPDX notices remain intact. No source PDF, source expression,
third-party code or raw transcript is reproduced here. Source applicability,
original focused build and private/generated transitive standard-axiom evidence,
and original review do **not** establish the new destination origin, adapted
client, aggregate/root graph, required native three-target checks, new review,
owner acceptance, protected integration, official release or source coverage.
The maintainer records those later decisions against the exact destination
revision in owning issue #83, not as assumed facts in this shipping source tree.

## September 29, 2026: whole-Veronese residue projection transfer

The original [producer](../GradedRings/VeroneseResidue.lean), [ordinary
client](../test/VeroneseResidue.lean) and standalone
[guide](VeroneseResidue.md) come from accepted isolated incubator commit
`905e7c2df24767f8cee4d7eafc757cb5c343cb3e` (tree
`375a7c5dac3650246261767e826073a1f0a829ce`). The original producer
`Incubator/Algebra/GradedRing/VeroneseResidue.lean` is 7,853 bytes,
SHA-256 `91fc9f4a2ba1cf3e7cadac4f4c68f6e92fbb06f4f1681a9449c837c75cd3484c`;
the original client `IncubatorTest/Algebra/GradedRing/VeroneseResidue.lean`
is 3,350 bytes, SHA-256
`4b376747aba551c70a35e073881553d323736be4b5828c729029ef001b86bbab`;
the original `Incubator/Algebra/GradedRing/VeroneseResidue/README.md` is
3,380 bytes, SHA-256
`5976048fb651bd1ca8c28a0810e21ae6a5a72c037782b4a8aa23c44bad362467`.
The producer and client mathematical bodies and their Apache-2.0 SPDX and
collective author headers are unchanged: their only edits replace the
incubator public imports by `GradedRings.VeroneseFinite` and
`GradedRings.VeroneseResidue`, respectively. The guide is adapted for the
destination imports, commands, links and evidence boundaries. No source
assets, dependency sources or third-party expression are redistributed.

Original author worker-b Hive Task
`hive-request-1cc04ea025d989648e050829da560f5070fe022d` (UID
`7768c775-4401-4d05-b7d9-88b2fd34ca29`) supplied the isolated producer,
client and guide with evidence child `0f73822b7b0dc4a902b2ea874c1bd617ab7ff7c9`.
Independent original reviewer worker-a Hive Task
`hive-request-d997f6f869ad5770abe62ccc1b3edc053fd17153` (UID
`0d110738-9176-47d3-a76d-04eaf3717c87`) recorded exact-code review in
`93da786719aa4687ea7059d951a0ac3b642e9a3a`. Atlas accepted the
isolated original evidence in incubator issue #186, comment #61341.
The already-delivered finite-inclusion producer is byte-identical to the
donor's prerequisite; its acceptance and verified official publication are
separately recorded in Graded Rings issue #83, comment #61324.

This bounded destination transfer, including the new root witness and library
navigation/metadata, is by worker-b Hive Task
`hive-request-8e46b5299287b35b65f34038800f1c3b7482b0f5` (UID
`ee21c7e8-3256-4684-8236-81517fa63480`), from accepted Graded main
`31f2290a0f7004f6dcec576b31e1c554093a2143`. The exact shipping commit
and static preservation report are recorded in owning Graded Rings issue #87
after publication, not guessed in this commit. The original focused checks
and review do not certify the changed origin, direct-import and root graph;
applicable destination build and transitive standard-three audit, fresh
independent destination and rights review, maintainer acceptance, protected
integration, separately verified official release, and source correspondence
each remain independent exact-revision decisions. The shifted external-sum
and source index-zero convention remain outside this transfer.

Atlas subsequently removed the four optional internal issue hyperlinks from
this provenance entry and the residue guide before exact destination review;
the issue identifiers, contributor credit and mathematical content are retained.

## Dependencies and redistribution boundaries

The library imports mathlib at
`83abb3e776bdefcbc447a1e44d0debe4010039e5`; dependency sources and compiled
artifacts are fetched by Lake, not bundled in this source tree. Mathlib uses
Apache-2.0 and retains its individual contributors' authentic notices. In
particular, the graded-algebra/localization interfaces credit Jujian Zhang,
Eric Wieser, Andrew Yang and other mathlib authors; valuation extension credits
Adam Topaz; the symmetric-algebra basis interfaces credit Raphael Douglas Giles
and collaborators. The ring injectivity/domain API credits Amelia Livingston
and Jireh Loreaux. These are formal dependencies, not claims that their source
files were authored by Formal Frontier.

The pinned mathlib root has no `NOTICE` file. This observation is not a blanket
finding about transitive dependencies or future bundled artifacts. Any copied
third-party expression must retain applicable source, modification and license
notices; original project licensing does not relicense third-party material.
No source PDF, dependency website, font, JavaScript asset or raw agent transcript
is part of this library's source payload.

## September 29, 2026: collective author-header correction

Worker-b Hive Task `hive-request-38db915b21067749e12433ea9f59824f533550ce`
(UID `c8d59383-e1a7-4571-8db5-fd81202333d5`) corrects the original-project
author-header prefixes in thirteen files to `Authors: Formal Frontier Agents`,
as required by section 10 of the deliverable release requirements. All detailed
Hive Task/UID contributor credit remains, as do Jujian Zhang's authentic 2022
copyright notice, Jujian Zhang and Eric Wieser's mathlib attribution, the
adaptation and Apache-2.0/SPDX notices, and fixture/design/clarification/transfer
credits. Predecessor main is `82fff548f2fbcb861c44120707e8deca2a1e3771`
(tree `d64850e405a839d3eb08fe54b7f73121480d48c9`). All older whole-file
donor-byte-identity claims remain evidence at their recorded frozen revisions;
this successor changes only these headers, not the Lean code following their
initial header terminators.
