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
5.4.N. A later source adapter or explanatory exposition is not automatically an
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
