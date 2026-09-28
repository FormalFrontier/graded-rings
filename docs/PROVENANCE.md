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
