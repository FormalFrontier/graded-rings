# Graded rings

Reusable Lean constructions for graded rings, their quotients, localizations,
finiteness and prime criteria, symmetric algebras, prime multiplicity, and
selected-component Veronese rings. The headlines below distinguish the
different weighted, finite-type and residue interfaces and their hypotheses;
the [API map and subject guides](docs/README.md) provide detailed navigation.

Authors: Formal Frontier Agents. Original project contributions are licensed
under [Apache-2.0](LICENSE). Atlas is the responsible maintainer on behalf of the
shared source-maintainer team. AI agents authored the mathematics, Lean proofs,
clients and documentation; exact contributions are listed in
[provenance and credits](docs/PROVENANCE.md).

## Headline results

This library presents reusable algebraic APIs. The statements and limitations
below describe the library in this checkout; source-specific correspondence
and book coverage require separate assessment.

- **Quotients and localizations:** [Homogeneous-ideal quotients](GradedRings/Quotient.lean)
  inherit a grading, while [localization](GradedRings/Localization.lean) at
  homogeneous denominators has a full grading and a degree-zero homogeneous-
  fraction equivalence. These constructions allow degenerate commutative rings;
  the localization grading uses a group of degrees. The separate [degree-multiplying
  map](docs/degree-multiplying-homogeneous-localization.md) works for natural
  gradings under explicit degree compatibility of an ordinary ring homomorphism
  and mapped denominators, without requiring a domain or positive factor.
- **Finiteness and prime criteria:** In a naturally graded commutative ring,
  [finite type over degree zero](GradedRings/FiniteType.lean) is equivalent to
  finite generation of the irrelevant ideal; [Noetherianity](GradedRings/Noetherian.lean)
  is equivalent to Noetherianity of degree zero together with that finite
  generation. For an *integer*-graded commutative ring with a positive-degree
  homogeneous unit, [homogeneous primes](GradedRings/HomogeneousPrime.lean)
  correspond to primes of degree zero by contraction and **radical** extension.
- **Symmetric algebras:** The [basis-free grading and graded maps](GradedRings/SymmetricAlgebra.lean)
  are functorial for linear maps over a commutative semiring and arbitrary
  modules; a basis is used only for polynomial-coordinate presentations.
- **Prime multiplicity:** A [multiplicative valuation](GradedRings/PrimeMultiplicity.lean)
  records prime-element multiplicity in a domain with well-founded divisibility.
  Its localization extension requires non-zero-divisor denominators; the
  [homogeneous localization](GradedRings/HomogeneousPrimeMultiplicity.lean) and
  [polynomial irreducibility applications](GradedRings/MvPolynomialAway.lean)
  carry their respective homogeneous-degree and field hypotheses.
- **Selected-component rings:** The [Veronese ring](docs/Veronese.md) selects
  **whole** original components in multiples of `n`; it has an internal
  grading and [degree-zero ring equivalence](docs/VeroneseZero.md) for every
  natural `n`; its whole-ring inclusion is injective when `0 < n`. At `n = 0`,
  its external direct sum is finite type over its actual new degree-zero ring
  without assuming finite type of the original ring. Under the explicit
  old-ring hypothesis
  `Algebra.adjoin (𝒮 0) (𝒮 1 : Set S) = ⊤`, [positive-index degree-one
  generation](docs/VeroneseDegreeOne.md) uses all of the new degree-one
  component over the actual new degree-zero ring, without finite generation.
- **The zero-index selected ring:** The [all-index equivalence and zero-index
  finite-type guide](docs/VeroneseZero.md) distinguishes the external copies
  of old degree zero, places arbitrary coefficients in the entire actual new
  degree-zero component and factors each summand as a power of the new
  degree-one variable. Polynomial evaluation is surjective over that ring,
  without a field, domain, nontriviality or finite-type assumption on `S`.
  Whole-ring inclusion at index zero need not be injective; no polynomial
  equivalence or source index-zero convention is asserted.
- **Finite positive-Veronese generation:** For finitely many strictly
  positive-weight homogeneous generators of the old ring over its actual
  degree zero, [finite selected-ring degree-one generation](docs/FiniteVeronese.md)
  supplies a *finite* generating set in the entire new degree one of a
  positive selected ring over its own degree zero. Native finite type over
  the old degree zero supplies such a family and therefore *some* positive
  selected index. Neither conclusion assumes a field, domain, nontriviality,
  equal weights or Noetherianity, or asserts generation at every index.
- **Coherent high tails:** [The new algebra](docs/CoherentTailVeronese.md)
  packages `TailEquiv 𝒜 ℬ N` with `0 < N`, a ring equivalence of the actual
  degree-zero pieces, additive equivalences for every degree `d ≥ N`, and
  compatibility with coefficient and high-degree products. When `N ≤ n`,
  `selectedRingEquiv` identifies the **entire** selected rings and supplies
  degree-preserving inverse maps; for `0 < n`, `selected_zero` gives the exact
  degree-zero coefficient square. Neither maps on missing original low degrees
  nor a Proj/scheme equivalence follow.
- **Positive-weight exponent blocks:** For any finite index type and strictly
  positive natural weights, [weighted-block decomposition](docs/WeightedBlocks.md)
  splits a finitely supported natural exponent vector of weight `k * D` into
  exactly `k` vectors of weight `D`, whose sum is the **whole input vector**;
  `D = max 1 (Fintype.card ι) * ∏ i, w i` is positive but need not be minimal.
  No coefficient ring, finite-Veronese generation or polynomial factorization
  follows from this combinatorial result alone.
- **Weighted-polynomial monomial adjoin:** Over any commutative semiring,
  [weighted-homogeneous membership](docs/WeightedBlockAdjoin.md) sends every
  polynomial of degree `k * D` for finite indices and positive natural weights
  into the coefficient subalgebra generated by coefficient-one monomials of
  weight `D = Finsupp.weightedBlockSize w`. Coefficients, including at `k = 0`,
  are unrestricted; this is not generation of an entire Veronese ring.
- **Selected weighted-polynomial degrees:** For finite variables, any natural
  weights including zero, any commutative semiring and every prescribed `n > 0`,
  [one finite family](docs/WeightedVeroneseGenerators.md) of homogeneous
  polynomials generates **all** weighted degrees divisible by `n` over the
  entire coefficient semiring. This is selected polynomial-component generation,
  not finite type of a whole selected graded ring or degree-one generation.
- **Prescribed positive whole-ring finite type:** Given a finite homogeneous
  generating family of **arbitrary natural weights** over the entire old
  degree-zero ring, [each prescribed positive selected ring](docs/VeroneseFiniteType.md)
  is finite type over its **entire actual new zero ring**. Native finite type
  of the old ring supplies such a family. No domain, nontriviality, field,
  Noetherianity, positive-weight or equal-weight assumption is needed; neither
  index zero nor degree-one generation at every index follows.
- **Finite positive-Veronese inclusions:** If a naturally graded commutative
  ring is finite type over its **entire old degree-zero ring**, the
  [canonical inclusion](docs/VeroneseFinite.md) from its external selected ring
  at every `n > 0` is finite: the **old ring** is a finite module via that
  inclusion's actual algebra structure. This is not finite type of the
  selected ring over its new zero component, some-index degree-one generation,
  an index-zero statement or, by itself, a residue-module result.
- **Whole-Veronese residue projections:** For `0 < n` and `r < n`, the
  [residue projection](docs/VeroneseResidue.md) is linear over the **entire
  external** selected ring acting on `S` by `inclusion.toAlgebra`. Its range
  consists exactly of elements whose old-degree components outside residue
  `r` vanish; it is a finite module if `S` is finite over that action, in
  particular if `[Algebra.FiniteType (𝒮 0) S]`. This projection module alone
  does not construct the shifted external sum; the sibling module does.
- **Shifted whole-Veronese residue modules:** The [external shifted sum](docs/VeroneseResidueModule.md)
  `⨁ k, 𝒮 (n * k + r)` carries convolution by the **entire** selected ring.
  Coefficient evaluation is linear under the actual `inclusion.toAlgebra` action;
  it is injective for `0 < n` and identifies the projection range for `r < n`.
  Ambient module finiteness or finite type over the **full old zero ring**
  transports to the shifted sum under those positive reduced-index hypotheses.
  No individual-fiber whole-ring action or `n = 0` evaluation bijection is asserted.
- **Weighted evaluation and lifts:** For any naturally graded commutative ring
  and chosen homogeneous elements of arbitrary natural weights (including zero),
  [ordinary polynomial evaluation](docs/WeightedEvaluation.md) preserves weighted
  degrees and commutes with the target's actual homogeneous components. Using
  the actual degree-zero ring as coefficients, it gives a native graded map;
  *only when* the chosen family generates the ring over degree zero does it
  also lift every homogeneous target element. No finite-variable, domain,
  field or nontriviality assumption is needed.

## Mathematical scope

| Module | Main interface and assumptions |
| --- | --- |
| [Quotient](GradedRings/Quotient.lean) | `Ideal.Quotient.gradedRing` equips a quotient by a homogeneous ideal with the image grading. The index is an additive monoid with decidable equality; the coefficient ring is commutative, possibly the zero ring. `gradedRingHom` bundles the quotient map. |
| [Localization](GradedRings/Localization.lean) | `GradedLocalization.gradedRing` grades ordinary localization at a submonoid of homogeneous elements, with an additive commutative **group** of degrees. `homogeneousLocalizationEquivZeroComponent` identifies equal-degree homogeneous fractions with the zero component. No domain or non-zero-divisor hypothesis is imposed on this construction. |
| [HomogeneousLocalizationMap](GradedRings/HomogeneousLocalizationMap.lean) | `HomogeneousLocalization.mapDegreeMul` sends naturally graded homogeneous localizations across an **ordinary** unital ring homomorphism multiplying natural degrees by `d`, given explicit degree compatibility and mapped denominators. It supports arbitrary source charts and restriction along a homogeneous factor, factor-one recovery, identity and composition. No domain, denominator-regularity or positive-`d` assumption. See the [thirteen-name guide](docs/degree-multiplying-homogeneous-localization.md). |
| [HomogeneousLifts](GradedRings/HomogeneousLifts.lean) | `GradedRingHom.surjective_gradedAddHom` sends ambient surjectivity to every whole graded-semiring component. For any nonnegative grading of a commutative ring `S`, `MvPolynomial.exists_isHomogeneous_aeval` lifts `s ∈ 𝒮 m` through evaluation of degree-`m` polynomials with coefficients in the actual `𝒮 0` and all of `𝒮 1` as variables, given exactly `Algebra.adjoin (𝒮 0) (𝒮 1 : Set S) = ⊤`. Degree zero is included; no finite-generation, domain or field assumption. See the [homogeneous-lifts guide](docs/HomogeneousLifts.md). |
| [WeightedEvaluation](GradedRings/WeightedEvaluation.lean) | `MvPolynomial.IsWeightedHomogeneous.aeval_mem`, `weightedAevalGradedHom` and `aeval_weightedHomogeneousComponent` use arbitrary chosen homogeneous elements `x i : 𝒮 (w i)`, arbitrary natural weights and actual degree-zero coefficients without a generation hypothesis; `exists_isWeightedHomogeneous_aeval` additionally requires `Algebra.adjoin (𝒮 0) (Set.range (fun i => (x i : S))) = ⊤`. See the [weighted-evaluation guide](docs/WeightedEvaluation.md). |
| [FiniteType](GradedRings/FiniteType.lean) | `GradedAlgebra.irrelevant_fg_iff_finiteType`: for a naturally graded commutative ring, the irrelevant ideal is finitely generated exactly when the ring is finite type over degree zero. Includes extraction of finite homogeneous ideal generators. |
| [Noetherian](GradedRings/Noetherian.lean) | `isNoetherianRing_iff_gradeZero_and_irrelevant_fg`: Noetherianity is equivalent to Noetherianity of degree zero plus finite generation of the irrelevant ideal. No domain or nontriviality assumption. |
| [HomogeneousPrime](GradedRings/HomogeneousPrime.lean) | In an integer-graded commutative ring with a positive-degree homogeneous unit, `homogeneousPrimeEquivDegreeZeroPrime` identifies homogeneous prime ideals with primes of degree zero. The inverse is **radical extension**, not plain extension. |
| [SymmetricAlgebra](GradedRings/SymmetricAlgebra.lean) | Basis-free grading, `gradedMap` and linear-equivalence functoriality over a commutative **semiring** and arbitrary modules. A basis is needed only for the degree-preserving polynomial-coordinate presentation. |
| [PrimeMultiplicity](GradedRings/PrimeMultiplicity.lean) | For a prime element in a commutative domain with well-founded divisibility, `valuation` sends nonzero `r` to `exp (-multiplicity p r)`. Its extension to localization requires denominators to be non-zero-divisors. |
| [HomogeneousPrimeMultiplicity](GradedRings/HomogeneousPrimeMultiplicity.lean) | Restricts that valuation to degree-zero homogeneous localization. On a nonzero homogeneous numerator over `p^n`, its value is `exp (n - multiplicity p x)`. Degrees form an additive commutative monoid. |
| [MvPolynomialAway](GradedRings/MvPolynomialAway.lean) | Over a field and an arbitrary variable type, bounds multiplicity by homogeneous degree, characterizes units by valuation one, and proves irreducibility at denominator order one for a positive-degree homogeneous prime polynomial. |
| [Veronese](GradedRings/Veronese.lean) | `GradedRing.Veronese.VeroneseRing 𝒮 n` selects the whole old components `𝒮 (n*j)` and has an internal grading for any `n`. The canonical inclusion is injective and identifies the whole degree-zero component when `0 < n`. No finiteness/domain assumption or scheme API. See the [selected-component guide](docs/Veronese.md). |
| [CoherentTailVeronese](GradedRings/CoherentTailVeronese.lean) | `GradedRing.Veronese.CoherentTail.TailEquiv 𝒜 ℬ N` packages an actual degree-zero ring equivalence, additive equivalences in all degrees at least `N > 0`, and compatibility with coefficients and products. For `N ≤ n`, `selectedRingEquiv` identifies the **whole** selected rings; `selectedGradedHom` and its inverse preserve selected degrees, and `selected_zero` commutes with the degree-zero coefficient equivalence when `0 < n`. Arbitrary natural-graded commutative rings, including zero rings, are allowed; no low-degree map is implied. See the [coherent-tail guide](docs/CoherentTailVeronese.md). |
| [WeightedBlocks](GradedRings/WeightedBlocks.lean) | `Finsupp.weightedBlockSize_pos` and `Finsupp.exists_weightedBlocks` give a positive explicit bound and an exact `Fin k` decomposition of whole finitely supported natural vectors for finite indices, positive natural weights and weight `k * weightedBlockSize w`. See the [weighted-block guide](docs/WeightedBlocks.md). |
| [WeightedBlockAdjoin](GradedRings/WeightedBlockAdjoin.lean) | `MvPolynomial.IsWeightedHomogeneous.mem_adjoin_weightedBlockSize`: a polynomial of degree `k * weightedBlockSize w` belongs to the coefficient subalgebra generated by coefficient-one monomials of that block weight, for finite indices, positive natural weights and any commutative semiring; arbitrary coefficients and `k = 0` are included. See the [monomial-adjoin guide](docs/WeightedBlockAdjoin.md). |
| [WeightedVeroneseGenerators](GradedRings/WeightedVeroneseGenerators.lean) | `MvPolynomial.exists_finset_weightedVeronese_generators`: one finite weighted-homogeneous family over any commutative semiring generates every selected polynomial degree `n * j` for prescribed `0 < n`, finite variables and arbitrary natural weights including zero. See the [standalone guide](docs/WeightedVeroneseGenerators.md). |
| [VeroneseFiniteType](GradedRings/VeroneseFiniteType.lean) | `GradedRing.Veronese.finiteType_of_finite_homogeneous_generators` gives finite type of the whole selected ring for **every prescribed** `n > 0` over its actual new zero component, from finite arbitrary-weight homogeneous generators over the entire old zero component. `GradedRing.Veronese.finiteType_of_finiteType` starts from native `Algebra.FiniteType (𝒮 0) S`. See the [standalone guide](docs/VeroneseFiniteType.md). |
| [VeroneseFinite](GradedRings/VeroneseFinite.lean) | `GradedRing.Veronese.inclusion_finite 𝒮 n hn` says the canonical inclusion from the external positive selected ring to `S` is finite for `[Algebra.FiniteType (𝒮 0) S]` and `hn : 0 < n`: the old ring is finite over the selected ring via the actual `inclusion.toAlgebra`. Distinct from finite type of the selected ring over its new zero ring. See the [standalone guide](docs/VeroneseFinite.md). |
| [VeroneseResidue](GradedRings/VeroneseResidue.lean) | `GradedRing.Veronese.residueProjection 𝒮 n r hn hr` projects the old ring onto its degree-`r` residue part, linearly over the whole selected ring through `inclusion.toAlgebra`. `mem_residueProjection_range_iff` characterizes the exact image and `residueProjection_range_finite_of_finiteType` proves its finiteness from old-zero finite type and `inclusion_finite`. See the [standalone guide](docs/VeroneseResidue.md). |
| [VeroneseResidueModule](GradedRings/VeroneseResidueModule.lean) | `GradedRing.Veronese.ResidueModule 𝒮 n r` is the external sum of entire old components `𝒮 (n * k + r)` with the whole selected-ring convolution action. `residueEvaluation` is linear for `inclusion.toAlgebra`, injective at positive `n`, and `residueEvaluationEquiv` identifies the projection range when also `r < n`. `residueModule_finite_of_finiteType` assumes finite type over the full old zero ring. See the [shifted-sum guide](docs/VeroneseResidueModule.md). |
| [VeroneseZero](GradedRings/VeroneseZero.lean) | `GradedRing.Veronese.zeroRingEquivAll` identifies the actual new zero ring with `𝒮 0` for every index. At index zero, `of_zero_eq_algebraMap_mul_pow`, `aeval_zeroVariable_surjective` and `finiteType_zero` prove finite type of the external sum over its entire actual new zero ring, without an old-ring finite-type or nontriviality assumption. Whole-ring inclusion is not asserted injective at zero. See the [standalone guide](docs/VeroneseZero.md). |
| [VeroneseDegreeOne](GradedRings/VeroneseDegreeOne.lean) | `GradedRing.Veronese.adjoin_component_one_eq_top`: if `0 < n` and `Algebra.adjoin (𝒮 0) (𝒮 1 : Set S) = ⊤`, the whole selected ring is generated over its **actual new degree-zero component** by **all** of its new degree-one component. No finite-variable, finite-type, domain, field, reducedness or nontriviality assumption. See the [degree-one-generation guide](docs/VeroneseDegreeOne.md). |
| [FiniteVeronese](GradedRings/FiniteVeronese.lean) | `GradedRing.Veronese.exists_finite_degree_one_generators` gives finite whole-ring generation over the actual new zero component from a finite positive-weight homogeneous generating family over the old zero component; `exists_positive_finite_degree_one_generators` instead starts from native `Algebra.FiniteType (𝒮 0) S` and obtains some positive index. See the [finite-generation guide](docs/FiniteVeronese.md). |

The full localized ring and its degree-zero subring are different objects.
The degree-multiplying map is distinct from this same-ring localization grading;
`d = 0` still requires an explicit degree-compatibility witness, and the chart
element need not be homogeneous for the restriction square. It does not construct
a Proj or scheme map.
The polynomial results do not identify a general graded ring with a polynomial
ring, and the valuation results do not apply to arbitrary rings with zero divisors.
The positive-Veronese result is algebraic generation, not a coefficient-
regrouping theorem or a chart/scheme equivalence. Coherent high tails induce
equivalent selected rings without extending the equivalence to missing low
degrees or asserting a geometric equivalence. No claim about complete
coverage of a mathematical book follows from this API.

The [current manual API map](docs/API.md) and [subject-guide index](docs/README.md)
cover these production leaves. The [historical 104-declaration native snapshot](docs/API-initial-snapshot.md)
applies only to an earlier 28-module tree; see the documentation index for its
exact original public checkout, limits and separately pinned reproduction recipe.

## Build and use

Install the exact toolchain in `lean-toolchain`: Lean `v4.34.0-rc2`.
The sole direct dependency is mathlib at
`83abb3e776bdefcbc447a1e44d0debe4010039e5`; `lake-manifest.json` freezes
all nine resolved Git dependencies. From a checkout, obtain matching compiled
mathlib artifacts **before** building:

```sh
lake exe cache get
lake --wfail build
```

Do not replace the manifest or substitute a moving mathlib branch. The default
build includes the aggregate library, all twenty-nine regression-test modules and
the four stored examples. Named targets are also available:

```sh
lake --wfail build GradedRings GradedRingsTests GradedRingsExamples
lake --wfail build QuotientLocalization FinitenessAndPrimes Symmetric Multiplicity
```

All 58 shipped Lean modules use Lean's native module system. A downstream native
module can ordinary-import `GradedRings` for the full API, or a subject leaf
such as `GradedRings.HomogeneousLifts`, `GradedRings.HomogeneousLocalizationMap`, `GradedRings.Quotient`,
`GradedRings.Veronese`, `GradedRings.CoherentTailVeronese`,
`GradedRings.WeightedBlocks`, `GradedRings.WeightedBlockAdjoin`,
`GradedRings.WeightedEvaluation`,
`GradedRings.FiniteVeronese`,
`GradedRings.WeightedVeroneseGenerators`,
`GradedRings.VeroneseFiniteType`, `GradedRings.VeroneseFinite`,
`GradedRings.VeroneseResidue`, `GradedRings.VeroneseResidueModule`,
`GradedRings.VeroneseZero`,
`GradedRings.VeroneseDegreeOne` or
`GradedRings.SymmetricAlgebra`. Public imports
re-export the intended interfaces. The selected-ring leaf also exports its
named technical grading and reindexing helpers; clients do not need to rely on
them for the main API.
Clients do not need `import all` or access to private names.

The quotient, localization and prime-multiplicity tests compare full public
constructions with their original constructions by Lean-private ordinary-import
`rfl` equalities. This checks computation as well as availability of theorem
names. Ordinary builds check proofs; named axiom prints in tests/examples
complement, but do not replace, the complete transitive standard-axiom audit
including private and generated declarations. No separate stored-proof replay
is required.

## Historical observed build resources

A Linux preparation run configured with `LAKE_JOBS=1` and `LEAN_NUM_THREADS=1`
fetched the matching mathlib cache in about 95 seconds. With that cache present,
rebuilding the library and clients after attribution-header changes, and checking
all default targets, took about 30 seconds; the largest child-process RSS was
approximately 1.16 GiB. The
1811-job Lake summary includes reused dependencies and replayed messages, not
1811 freshly compiled modules. Four examples had already been compiled before
that changed-header run. These are observations, not a cold-build benchmark or
hardware-independent promise. Network/cache availability affects elapsed time.

The run had a 23 GiB aggregate runtime limit. Actual concurrent process and
thread counts were not measured; the configured environment variables are not
evidence of an enforced one-job or one-thread cap.
Child RSS is not the process group's or container's total peak; the lifetime
cgroup peak includes earlier work. Leave headroom for Lake, dependencies and
documentation generation. Do not infer a minimum-memory guarantee from these
measurements. Exact raw receipts belong to the revision-specific evidence packet.

## Complete examples

Each link is a complete native module with its imports, hypotheses, private
example declarations and axiom prints, compiled by `GradedRingsExamples`.
Examples are usage demonstrations, not additional public API.

- [Quotient and localization](examples/QuotientLocalization.lean): quotient-map
  multiplication, recombination of the quotient grading, homogeneous-fraction
  degree membership and the degree-zero equivalence round trip.
- [Finiteness and primes](examples/FinitenessAndPrimes.lean): derive finite type
  and Noetherianity from an irrelevant-ideal generating set, extract positive
  homogeneous generators, and contract after radical extension of a prime.
- [Symmetric algebras](examples/Symmetric.lean): map a product of generators by a
  linear map, preserve homogeneous degree in basis coordinates, and return through
  the inverse coordinate map. The coefficient semiring need not be a field.
- [Multiplicity](examples/Multiplicity.lean): evaluate products of prime powers,
  recognize a unit at maximal numerator multiplicity, and use denominator order
  one to force a unit factor. This file uses the aggregate import.

## Proof ideas

A homogeneous quotient decomposes by projecting the original components:
homogeneity makes the decomposition vanish on the ideal, so it descends.
For localization, project a numerator into the degree shifted by its denominator;
the localization relation makes the result independent of representatives, even
when denominators are zero divisors.

Finite generation of the irrelevant ideal yields positive-degree homogeneous
generators. Strong induction on degree turns ideal generation into algebra
generation over degree zero. The Noetherian criterion then combines this with
the degree-zero Noetherian and finite-type results in mathlib.

For integer-graded prime correspondence, powers of a positive-degree homogeneous
unit move suitable powers of homogeneous elements to degree zero. This explains
why radical extension, rather than unmodified extension, is the inverse.

The symmetric algebra's universal property sends degree-one generators into
their direct sum, giving the basis-free grading and its functorial maps.
In a homogeneous polynomial localization, total degree bounds prime multiplicity;
order zero forces the remaining numerator to be a nonzero scalar, hence a unit.
Additivity of denominator order then makes an order-one element irreducible.

## References and artifact status

Ravi Vakil, *The Rising Sea: Foundations of Algebraic Geometry*, October 21, 2025
draft, exercises around 4.5.F–H and 5.4.N motivate several constructions.
Section 7.4.4, Exercise 7.4.D motivates the selected-component Veronese ring;
this library supplies its algebraic ring layer, not the Proj isomorphism.
Section 7.4.4, Exercise 7.4.E (printed page 215; degree-zero coefficient
convention in §4.5.6, pp. 151–152) motivates homogeneous polynomial lifts
and positive-Veronese degree-one generation under old-ring generation. The
library does not supply coefficient regrouping, chart/Proj invariance or
a source-specific correspondence decision.
The basis-free symmetric algebra also supports projective-space applications.
These are mathematical references; no source PDF, figures or substantial source
prose is distributed. Detailed source correspondence and gaps are maintained
outside this reusable library.

Lean and mathlib supply the foundational APIs; original expression, authentic
notices and distinct contributor/adaptation roles are summarized in
[provenance](docs/PROVENANCE.md). This checkout contains the original project
contributions and the subsequently accepted and officially published
Veronese-related modules, including whole-ring residue projections and
shifted external sums. Mathematical claims are limited by the hypotheses
above: in particular, neither coherent-tail equivalence nor exponent blocks
establish a Proj/scheme result or source-specific exercise completion.
Revision-specific proof, rights, review and official-release decisions are
recorded in the project's owning records, separately from source coverage.
