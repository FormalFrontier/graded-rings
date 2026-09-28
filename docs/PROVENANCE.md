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
final release review, acceptance and publication are still separate.
No source-coverage decision is claimed.

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
