# Provenance and contributor credit

Authors: Formal Frontier Agents. Original project code, tests and prose are
licensed under [Apache-2.0](../LICENSE). Formal Frontier AI agents developed
the mathematical constructions, proofs, interfaces, examples and documentation;
authorship does not itself establish legal copyright ownership. This library
contains original project work, adaptations of earlier Formal Frontier work,
and imported mathlib APIs. The mathematical sources motivate results but their
PDFs, diagrams, proofs and substantial prose are not redistributed here.

## Contributions and adaptations

Atlas developed the original quotient grading, full graded localization,
irrelevant-ideal finite-type and Noetherian criteria, homogeneous-prime
correspondence, symmetric-algebra grading, prime-multiplicity results and
native quotient/interface assembly. Other Formal Frontier contributors
subsequently supplied dependency compatibility, native and computation-preserving
direct/root clients, localization repairs, examples and reader documentation.
The interface work includes the additional `valuationDef_pow` computation lemma;
the original `valuation_apply_pow` proof remains available.

The degree-multiplying homogeneous-localization map and its direct client were
originally written as a separate Formal Frontier incubator contribution; a
different contributor adapted the client and registered the library and root
imports here. Its mathematical statements and proofs were not newly originated
by the destination assembly. The producer retains **Jujian Zhang's 2022
copyright notice** and the attribution to **Jujian Zhang and Eric Wieser** for
the underlying mathlib homogeneous-localization construction and native maps.
The project adaptation and mathlib's Apache-2.0 terms do not replace those
authentic notices.

The selected-component Veronese ring and algebra-only direct examples were
written in an isolated incubator contribution, then separately adapted and
registered in this library with a new guide and aggregate client. Distinct
incubator contributors originally wrote the homogeneous-polynomial lifts,
positive-Veronese degree-one generation, coherent-tail equivalences, weighted
exponent blocks, weighted evaluation, polynomial monomial-adjoin membership,
finite selected-ring degree-one generation, selected weighted-polynomial
generators, prescribed positive selected-ring finite type, the zero-index
selected-ring API, finite positive-Veronese inclusion, whole-ring residue
projections and external shifted residue modules. Their original mathematical
proofs and clients are not reattributed to the later contributors who adapted
imports, notices, test fixtures, module registration, root witnesses, guides
and release metadata here. The original authors and separate adaptation
contributors are collectively credited as Formal Frontier Agents.

An original assessment of finite-inclusion applicability and the zero-index
API design were contributed by Atlas as **uncompiled mathematical designs**,
not authorship of those later Lean proofs. Atlas also supplied uncompiled
weighted-evaluation design notes and repaired the positive-Veronese guide.
The positive-weight exponent decomposition was separately explained in a
project proof exposition before its independent formalization. A correction
removed unsupported original-project copyright-owner assertions from an
early weighted-polynomial adjoin contribution; the repaired project author
and Apache-2.0 notices remain, and no owner is invented. The adapted
finite-type and zero-index test fixtures retain credit to the existing
Formal Frontier `FiniteVeronese` examples and the related incubator client.

Atlas adapted the historical native Markdown API adapter and controls from
earlier Formal Frontier projects (including multivariate polynomials, toric
ideals, minimal primes and integral closure) and Anchor's initial
ideal-completion recipe. The [documentation guide](README.md) describes the
functional historical snapshot separately from the current manual API map.

## Sources and boundaries

Ravi Vakil, *The Rising Sea: Foundations of Algebraic Geometry*, October 21,
2025 draft, supplies mathematical background, notably Exercises 4.5.F–H and
5.4.N, and §7.4.4 Exercises 7.4.D–H (printed pp. 215–216; degree-zero
conventions on pp. 151–152). The selected-ring, polynomial-lift, coherent-tail,
weighted-block and finite-type APIs are reusable algebraic results, not an
assertion of every exercise's source correspondence or a Proj/scheme
equivalence. The [README](../README.md) and [mathematical guides](README.md)
give their actual hypotheses and limitations; source-specific passage
correspondence and remaining gaps are maintained outside this library.

Lean and mathlib supply the formal language and reusable graded-algebra,
localization, polynomial, ideal, symmetric-algebra, multiplicity and valuation
APIs. The library imports pinned mathlib rather than bundling dependency
sources or assets. Its contributors retain their own authorship and terms;
notably mathlib graded-algebra/localization work by Jujian Zhang, Eric Wieser
and Andrew Yang, valuation work by Adam Topaz, symmetric-algebra work by
Raphael Douglas Giles and collaborators, and ring/domain work by Amelia
Livingston and Jireh Loreaux. The original project's Apache-2.0 authorization
does not relicense third-party material. There are no copied source PDFs,
dependency websites, fonts or raw transcripts in the shipped library.

Revision-specific contributor identities, original/adapted file comparisons,
rights assessments, objections and exact verification/review/release evidence
are maintained in the project's private owning records. These are not
prerequisites for using the published mathematical API and are not a
replacement for its documentation or the bibliography above.
