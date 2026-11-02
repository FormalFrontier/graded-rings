# Provenance and contributor credit

Authors: Formal Frontier Agents. Original project code, tests and prose are
licensed under [Apache-2.0](../LICENSE). Formal Frontier AI agents developed
the Lean formalizations, interfaces, examples and documentation;
authorship does not itself establish legal copyright ownership. This library
contains original project work, adaptations of earlier Formal Frontier work,
and imported mathlib APIs. The mathematical sources motivate results but their
PDFs, diagrams, proofs and substantial prose are not redistributed here.

## Contributions and adaptations

Original Formal Frontier formalizations include the quotient grading, full
graded localization, irrelevant-ideal finite-type and Noetherian criteria,
homogeneous-prime correspondence, symmetric-algebra grading, prime-multiplicity
results and native quotient interfaces. Additional contributions include
dependency compatibility, computation-preserving interfaces and clients,
localization repairs, examples and reader documentation. The additional
`valuationDef_pow` computation lemma is distinct from the original
`valuation_apply_pow` proof, which remains available.

The integer-filtration associated graded and its representative quotient API,
the canonical quotient-Rees representation, the induced maps of stage-preserving
original-module linear maps, and the Rees grading use Mathlib's filtration,
direct-sum, quotient, homogeneous-ideal and endomorphism-action APIs.
The weighted lifting and its finiteness consequences use Mathlib's adic
precompleteness interface. The finite-generation bridge additionally uses
homogeneous representatives, quotient-Rees components, and Mathlib's direct-sum
and finite-span extraction APIs. Residue coefficients restrict the canonical
quotient-Rees action; natural filtrations extend to integer stages without
normalizing their initial submodule. These are distinct from the natural-indexed
finite-Rees stability and first-quotient constructions.

The [intrinsic integer-associated-graded finiteness criterion](../GradedRings/FilteredAssociatedGraded/ReesFiniteGeneration.lean)
composes the library's weighted coefficient-lifting and finiteness, homogeneous
extraction, quotient-Rees action and shifted-projection formalizations. Its bounded
converse reuses Andrew Yang's ideal-filtration and Rees-module formalization in
Mathlib and Mathlib's finite-span and semilinear finite-image APIs. It constructs
no new filtration, associated graded or scalar action.

The quotient-Rees augmentation uses Mathlib's constant-coefficient and quotient
maps. The regular-module comparisons use the polynomial-module self-comparison;
ideal-power quotient multiplication descends the existing bilinear coefficient
map. Associated-graded map criteria and exactness use quotient kernel/range and
direct-sum APIs. These constructions reuse the existing scalar actions and
quotients rather than replacing them.

The degree-multiplying homogeneous-localization map and its client reuse
earlier Formal Frontier work; the library-specific client adaptation does not
originate the map's mathematical statements or proofs. The implementation
retains **Jujian Zhang's 2022 copyright notice** and the attribution to
**Jujian Zhang and Eric Wieser** for the underlying mathlib
homogeneous-localization construction and native maps. Project adaptations and
mathlib's Apache-2.0 terms do not replace those authentic notices.

The selected-component Veronese ring and its algebra-only clients also reuse
earlier Formal Frontier formalizations. These contributions include
homogeneous-polynomial lifts, positive-Veronese degree-one generation,
coherent-tail equivalences, weighted exponent blocks, weighted evaluation,
polynomial monomial-adjoin membership, finite selected-ring degree-one
generation, selected weighted-polynomial generators, prescribed positive
selected-ring finite type, the zero-index selected-ring API, finite
positive-Veronese inclusion, whole-ring residue projections and external
shifted residue modules. Their original mathematical proofs and clients are
credited separately from adaptations of imports, interfaces, examples and
documentation; they are not reattributed to the adaptation contributors. All
these contributors are collectively credited as Formal Frontier Agents.

Mathematical API designs for finite-inclusion applicability, the zero-index
API and weighted evaluation are distinct contributions from their Lean proofs.
Positive-weight exponent decomposition also has a separately authored
mathematical exposition. The finite-type and zero-index examples reuse the
existing Formal Frontier `FiniteVeronese` examples and a related selected-ring
client. Documentation tooling draws on earlier Formal Frontier work on
multivariate polynomials, toric ideals, minimal primes, integral closure and
ideal completion; the [documentation guide](README.md) distinguishes that
tooling from the current manual API map.

## Sources and boundaries

Ravi Vakil, *The Rising Sea: Foundations of Algebraic Geometry*, October 21,
2025 draft, supplies mathematical background, notably Exercises 4.5.F–H and
5.4.N, and §7.4.4 Exercises 7.4.D–H (printed pp. 215–216; degree-zero
conventions on pp. 151–152). The selected-ring, polynomial-lift, coherent-tail,
weighted-block and finite-type APIs are reusable algebraic results, not an
assertion of every exercise's source correspondence or a Proj/scheme
equivalence. The [README](../README.md) and [mathematical guides](README.md)
give their actual hypotheses and limitations.

For background on the Rees and associated-graded algebra/module constructions
in [`ReesAlgebra`](../GradedRings/ReesAlgebra.lean) and
[`ReesModule`](../GradedRings/ReesModule.lean), see K. Fujiwara and F. Kato,
*Foundations of Rigid Geometry I*,
[arXiv:1308.4734v5](https://arxiv.org/abs/1308.4734v5). This scoped background
reference does not assert exact theorem correspondence or book coverage.

The [integer-filtration associated graded](../GradedRings/FilteredAssociatedGraded.lean),
its [canonical quotient-Rees action](../GradedRings/FilteredAssociatedGraded/ReesAction.lean)
and the [Rees grading](../GradedRings/ReesAlgebra/Grading.lean) use Chapter 0, §7.5
of that work as mathematical context. The separate
[weighted lifting](../GradedRings/FilteredModule/WeightedSpan.lean) and
[its consequences](../GradedRings/FilteredModule/Finiteness.lean) independently
generalize the filtered coefficient-lifting ingredient underlying Proposition 0.7.5.2.
Their precomplete-coefficient, all-integer formulation takes a separated compatible
filtration, finite weighted lifts and their generation of each successive quotient
as input. The separate
[finite-generation bridge](../GradedRings/FilteredAssociatedGraded/FiniteGeneration.lean)
relates those generation inputs to finiteness of the canonical quotient-Rees
associated graded, without completeness or separation for that equivalence.
Its lifting consequences retain precompleteness and filtration separation;
ambient-module finiteness additionally needs exhaustivity, while stage finiteness
needs a finitely generated ideal instead. Under precompleteness, separation,
exhaustivity and ideal FG, the intrinsic criterion combines these consequences with
the shifted-projection converse into an equivalence with ambient finiteness,
all-integer original-stage FG and eventual ideal stability. These are not assertions
of the full proposition, book coverage or full graded source correspondence.

The finite-Rees stability theorem follows Andrew Yang's bounded-degree span
and finite-generation compactness argument in Mathlib's
`Ideal.Filtration.submodule_fg_iff_stable`. Only its converse needs finite
generation of the filtration stages; the forward stability theorem does not.
This is distinct from the first-quotient associated-graded finiteness construction.
The finite homogeneous Rees generating family uses Andrew Yang's filtration
and polynomial-module APIs and Johan Commelin's finite-span extraction API.
Its all-lower-degree form follows the existing Formal Frontier weighted-normal-form
formalization in `GradedRings.ReesModule.FiniteGeneration`. The finite weighted
characterization combines this generating family with the same-family weighted
span equivalence and the finite-index finite-generation theorem. These bridges
call the imported APIs rather than copy their implementations.

[Rees-module evaluation](../GradedRings/ReesModule/Evaluation.lean) restricts
Andrew Yang's `PolynomialModule.eval` to the original initial filtration stage,
using Mathlib's generic semilinear codomain restriction and the original
constant-single map. Its naturality follows the library's coefficientwise
Rees-map construction and Mathlib's `PolynomialModule.eval_map`. The initial-stage
finite-generation consequence uses Johan Commelin's
`Module.Finite.of_surjective`; it requires no surjectivity of the scalar hom.
The coefficient-zero bridge `PolynomialModule.eval_zero` has only the hypotheses
required by Mathlib's polynomial module. These are original bridges through
imported APIs, not copies of their implementations or assertions of a
source-specific theorem correspondence.

The [monic polynomial-module interface](../GradedRings/PolynomialModule/Monic.lean)
uses Andrew Yang's polynomial-module action, Mathlib's polynomial coefficient
APIs, and its finitely supported function and finite-sum APIs. The antitone
coefficient-preimage theorem uses descending induction above finite support;
its constant-bottom specialization gives injectivity of monic multiplication
on arbitrary polynomial modules. The
[ambient linear-factor interface](../GradedRings/PolynomialModule/EvaluationKernel.lean)
uses the stock scalar `Polynomial.X_sub_C_dvd_sub_C_eval` through Yang's
`PolynomialModule.lsingle` and `induction_linear`, and uses the existing
`equivPolynomialSelf` and its scalar law for agreement with scalar polynomial
divisibility. The polynomial monic, division and coefficient formalizations are
credited to Chris Hughes, Johannes Hölzl, Kim Morrison and Jens Wagemaker;
Mathlib's finitely supported function API contributors supply the support,
coefficient-extensionality and finite-sum infrastructure. These interfaces add
no module-valued division operation or replacement polynomial-module action.

The [natural Rees evaluation-kernel presentation](../GradedRings/ReesModule/EvaluationKernel.lean)
uses Yang's filtration, Rees and polynomial-module APIs together with those
generic coefficient and factor theorems. Its map reuses the existing Formal
Frontier natural-to-integer extension, canonical cutoff transition from tail
one to tail zero, and coefficientwise `reesMap`s with identity coefficient
maps. The successor source is the existing
`(H.toIntFiltration.natTail (1 : ℤ)).submodule`, not a new filtration or shift
construction. The injective range/kernel and unique-factor laws retain the
original semilinear evaluator into the possibly proper `H.N 0` and its
original-`R`-linear constant section; they introduce no target Rees action.
These are original project bridges through the imported APIs and existing
canonical constructions, not copied implementations or assertions of
source-specific theorem correspondence.

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

Credit for mathematical ideas or formalization approaches does not grant
permission to copy their expression. Project author and Apache-2.0 notices do
not establish legal copyright ownership or waive third-party rights.
