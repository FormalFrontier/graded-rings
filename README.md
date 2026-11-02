# Graded rings

Reusable Lean constructions for graded rings, quotients and localizations,
finiteness and primes, symmetric algebras, prime multiplicity, and
selected-component Veronese rings. Start with the mathematics below; use the
[canonical API map](docs/API.md#production-modules) for modules, interfaces and
detailed hypotheses, or the [subject guides](docs/README.md) for focused clients.

Authors: Formal Frontier Agents. Original project contributions are licensed
under [Apache-2.0](LICENSE). AI agents authored the mathematics, Lean proofs,
clients and documentation; exact contributions are listed in
[provenance and credits](docs/PROVENANCE.md).

## Headline results

These are reusable algebraic APIs, not claims of source-specific correspondence
or complete book coverage. Selected-ring and evaluation results below concern
**naturally graded commutative rings** unless another base is stated. Old and new
degree-zero coefficients mean the **entire actual components**, not a smaller
chosen coefficient ring.

- **Quotients and localizations.** For commutative rings,
  [homogeneous-ideal quotients](GradedRings/Quotient.lean) inherit the image grading
  for additive-monoid degrees with decidable equality. [Full localization](GradedRings/Localization.lean)
  at homogeneous denominators uses an additive commutative **group** of degrees;
  its degree-zero component is equivalent to equal-degree homogeneous fractions.
  Both allow zero rings without a domain assumption; localization also permits
  zero-divisor denominators.
- **Localization maps and reducedness.** The [degree-multiplying map](docs/degree-multiplying-homogeneous-localization.md)
  uses natural gradings, an ordinary unital ring homomorphism, explicit degree
  compatibility and mapped denominators. Even factor zero requires its degree
  witness; source charts may be arbitrary, but restriction factors are homogeneous.
  Separately, [homogeneous localization preserves reducedness](GradedRings/HomogeneousLocalizationReduced.lean)
  for a **reduced commutative ring**, additive commutative **monoid** degrees with
  decidable equality and any denominator submonoid. Neither interface requires
  a domain, regular denominators or nontriviality; the map needs no positive factor.
- **Finiteness and primes.** In a naturally graded commutative ring,
  [finite type over old degree zero](GradedRings/FiniteType.lean) is equivalent to
  finite generation of the irrelevant ideal; [Noetherianity](GradedRings/Noetherian.lean)
  is equivalent to that finite generation plus Noetherian degree zero.
  For an **integer**-graded commutative ring with a positive-degree homogeneous
  unit, [homogeneous primes](GradedRings/HomogeneousPrime.lean) correspond to
  degree-zero primes by contraction and **radical** extension.
- **Finite Rees modules and stable filtrations.** For any ideal `I` in a commutative
  ring `R` and any `R`-module `M`, with independent universes, an
  [`I`-filtration with finitely generated Rees module](GradedRings/ReesModule.lean)
  is stable: `I • F.N n = F.N (n + 1)` for all sufficiently large `n`.
  Neither `I`, the stages, nor `M` need be finitely generated. This uses the existing
  natural-number filtration and polynomial Rees-module constructions.
- **Integer-filtered associated gradeds and Rees actions.** Over a commutative ring `R`,
  for an antitone family of submodules of an `R`-module `M`,
  `F.N : ℤ → Submodule R M` with `I • F.N n ≤ F.N (n + 1)`, the
  [integer associated graded](GradedRings/FilteredAssociatedGraded.lean) is the
  direct sum of `F.N n` modulo the next stage inside it. It retains the original
  componentwise `R`-module structure and has a surjective coefficientwise
  representative map, with next-stage kernel and a first-isomorphism comparison.
  No finiteness, exhaustivity, separatedness, lower bound or normalization at
  degree zero is required. The [Rees grading](GradedRings/ReesAlgebra/Grading.lean)
  gives the polynomial Rees algebra its degree grading and its coefficient-ideal
  quotient the image grading. On the same associated-graded carrier, the
  [canonical representation](GradedRings/FilteredAssociatedGraded/ReesAction.lean)
  constructs an action of `C = reesAlgebra I ⧸ I.map (algebraMap R (reesAlgebra I))`.
  Constants act by the original `R`-action, and `I` annihilates the carrier.
  For `q : ℕ`, `a ∈ I ^ q` and `m ∈ F.N n`, the class of `aX^q` sends the
  class of `m` to the class of `a • m` in degree `n + q`.
- **Residue-linear integer graded pieces.** For the same arbitrary ideal-compatible
  integer filtration, the [original pieces](GradedRings/FilteredAssociatedGraded/Pieces.lean)
  carry named `R ⧸ I`-module structures compatible with their original `R` actions.
  Insertion and projection are residue-linear for the whole associated graded's
  existing residue action, with the same functions, representative formulas and
  finite reconstruction. Piece modules and towers are activated locally rather
  than registered globally. No residue action on the stages or ambient stage
  quotients, finiteness or degree-zero normalization is required.
- **Maps of integer-filtered associated gradeds.** An original-`R`-linear map
  preserving every stage of two integer filtrations induces a
  [canonical quotient-Rees-linear map](GradedRings/FilteredAssociatedGraded/Map.lean).
  It sends each homogeneous representative to its image, preserves the original
  `R` action, and respects identities and composition. For `f : M →ₗ[R] N` with
  filtrations `F` and `H`, it is injective exactly when, for every `n : ℤ` and
  `x ∈ F.N n`, membership `f x ∈ H.N (n + 1)` implies `x ∈ F.N (n + 1)`.
  It is surjective exactly when `H.N n ≤ (F.N n).map f ⊔ H.N (n + 1)` for every
  integer `n`. Thus stagewise pullback equality `F.N n = (H.N n).comap f` gives
  injectivity, and stagewise image equality `(F.N n).map f = H.N n` gives
  surjectivity, without ambient injectivity or surjectivity of `f` or normalization
  at degree zero. A module equivalence carrying
  each filtration stage onto the corresponding stage induces a quotient-Rees-linear
  equivalence, compatibly with inverses, identities and composition. The modules have
  independent universes; no finiteness, exhaustivity, separatedness or lower bound is
  required.
- **Exactness of integer associated graded maps.** For compatible original
  linear maps `f : M →ₗ[R] N` and `g : N →ₗ[R] P`, the image of the first
  canonical quotient-Rees-linear associated graded map equals the kernel of the
  second exactly when, for every integer `n` and `y ∈ H.N n`, membership
  `g y ∈ K.N (n + 1)` is equivalent to
  `y ∈ (F.N n).map f ⊔ H.N (n + 1)`. The ambient composite need not vanish.
  An ambient exact pair with strict stage images induces an exact pair, without
  ambient injectivity or surjectivity. The three module universes are independent;
  no finiteness, exhaustivity, separatedness, completeness or degree bound is needed.
- **Ideal-power quotients and coefficient multiplication.** For any ideal `I` of a
  commutative ring `R` and every natural degree `q`, the
  [quotient of `I ^ q` by its ideal multiple](GradedRings/ReesAlgebra/QuotientPieces.lean)
  has an `R`-linear comparison `quotientMonomialEquiv` with the degree-`q` component
  of the coefficient-ideal quotient of the Rees algebra. The denominator is exactly
  the next ideal power, viewed inside `I ^ q`. On these same quotient modules,
  [coefficient multiplication](GradedRings/ReesAlgebra/PowerQuotientMultiplication.lean)
  `powerQuotientMul` is bilinear over `R ⧸ I`; `powerQuotientMul_mk` sends `[a]`
  and `[b]` to `[a * b]` in degree `q + r`. Multiplication is commutative and
  associative under the degree-sum identifications,
  with the class of `1` in degree zero as a two-sided unit. The quotient monomial
  maps preserve this multiplication and send that class of `1` to the quotient
  Rees unit. No finiteness, Noetherianity, nontriviality or positive-degree
  assumption is needed.
- **Weighted generation of integer filtrations.** For a separated, antitone
  integer-indexed filtration satisfying `I • F n ≤ F (n + 1)` over an
  `I`-adically **precomplete** commutative coefficient ring,
  [finite degree-weighted lifts generating the successive quotients](GradedRings/FilteredModule/WeightedSpan.lean)
  generate every stage with coefficients in `I ^ ((n - d i).toNat)`.
  Ring, module and finite indexing type have independent universes; the family
  may be empty and the degrees may be negative. The
  [finiteness consequences](GradedRings/FilteredModule/Finiteness.lean) keep
  their extra hypotheses separate: eventual stability needs none, finiteness
  of the original module needs exhaustivity, and finite generation of every
  stage needs `I.FG`. The equality and ambient finiteness require neither
  `I.FG` nor a Hausdorff coefficient ring. This independently generalizes the
  filtered lifting ingredient underlying Fujiwara--Kato, *Foundations of Rigid
  Geometry I*, Proposition 0.7.5.2; it is not the full proposition or a full
  associated-graded construction.
- **Finite integer associated gradeds and weighted generators.** For the
  [canonical quotient-Rees action](GradedRings/FilteredAssociatedGraded/FiniteGeneration.lean),
  finiteness of the whole integer associated graded is equivalent to finite
  homogeneous original-module lifts generating every successive quotient with
  ideal-power weights. This algebraic equivalence needs no completeness,
  separation, exhaustivity or finiteness of the ideal. Over an ideal-adically
  precomplete coefficient ring, separation gives exact weighted descriptions
  in every integer degree and eventual stability. Exhaustivity additionally
  gives finiteness of the original module; `I.FG` instead gives finite generation
  of every stage, without exhaustivity. Degree-zero normalization and a lower
  grading bound are not required, and the generator family may be empty.
- **Associated graded modules from the first quotient.** For any ideal `I` in a
  commutative ring `R` and any `R`-module `M`, with independent universes,
  [the Rees-quotient associated graded module](GradedRings/ReesModule.lean) `G`
  is finite over `C = B / IB`, where `B = reesAlgebra I`, whenever
  `Q = M / IM` is finite over `R / I`. The canonical map `C ⊗[R/I] Q → G` is
  surjective, **not generally an isomorphism**. More generally, for a subideal
  `K ≤ I` with `IⁿM = KⁿM + Iⁿ⁺¹M` for **every** natural `n`, the canonical
  `reesAlgebra K ⊗[R] Q → G` is surjective without a finiteness hypothesis,
  and `Q` finite over `R / I` makes `G` finite over `reesAlgebra K`, with **no
  finite-generation assumption on K**. If `Q` is Noetherian over `R` and `K` is finitely
  generated, then `G` is Noetherian over `C`. None of these results requires
  finiteness of the original `M`, Noetherianity of `R`, or finite generation of `I`.
- **Quotient Rees augmentation.** For any ideal `I` of a commutative ring `R`,
  [constant coefficient](GradedRings/ReesAlgebra/Augmentation.lean) induces an
  `R/I`-algebra homomorphism from `C = reesAlgebra I / I·reesAlgebra I` to `R/I`.
  The composite `C → R/I → C` is the degree-zero projection, and the image of
  `R/I → C` is exactly the degree-zero component. No finiteness or nontriviality
  assumption is needed; this does not identify the whole ring `C` with `R/I`.
- **The regular associated graded module.** For any ideal `I` of a commutative ring
  `R`, the [regular associated graded module](GradedRings/AssociatedGradedRegular.lean)
  `Ideal.AssociatedGradedModule I R` is canonically free of rank one over
  `C = reesAlgebra I / I·reesAlgebra I`. The equivalence `regularEquiv` sends
  `c` to `c • regularUnit`, where the generator is the degree-zero unit class.
  Rees-representative and every-coefficient formulas, unique scalar expressions,
  and linear-map extensionality expose this comparison without unfolding its
  quotients. No finiteness, completeness, separatedness or nontriviality is assumed.
- **Symmetric algebras and first order.** [Basis-free grading and graded maps](GradedRings/SymmetricAlgebra.lean)
  are functorial for arbitrary modules over a commutative **semiring**; only
  polynomial coordinates need a basis. Over a commutative **ring**, for any
  module `M`, the [augmentation-square quotient and conormal](GradedRings/SymmetricAlgebraSquareZero.lean)
  give `SymmetricAlgebra R M ⧸ augmentationIdeal² ≃ₐ[R] TrivSqZeroExt R M` and
  `augmentationIdeal.Cotangent ≃ₗ[R] M`, without freeness, projectivity or finiteness.
  Generator formulas, ideal transport and both whole-map naturalities use
  `open scoped TrivSqZeroExt` and the released `coherent-modules` kernel
  equivalence. The quotient's image cotangent ideal corresponds to
  `TrivSqZeroExt.kerIdeal`, not the original augmentation ideal; no scheme or sheaf comparison.
- **Prime multiplicity.** A [multiplicative valuation](GradedRings/PrimeMultiplicity.lean)
  measures a prime element in a commutative domain with well-founded divisibility;
  extension to localization requires non-zero-divisor denominators. Its
  [homogeneous restriction](GradedRings/HomogeneousPrimeMultiplicity.lean) uses
  additive commutative monoid degrees. The [polynomial applications](GradedRings/MvPolynomialAway.lean)
  work over a **field**, with arbitrary variables; irreducibility at denominator
  order one uses a positive-degree homogeneous prime polynomial.
- **Whole selected rings, including index zero.** The [Veronese ring](docs/Veronese.md)
  is the external sum of **whole** old components in multiples of `n`, with a
  native grading for every natural `n`. Its [actual zero ring](docs/VeroneseZero.md)
  is equivalent to old degree zero at every index; whole-ring inclusion is
  injective for `n > 0`, but need not be at zero. At zero, old-zero copies occupy
  separate external summands: each factors as a power of the new degree-one variable
  with its arbitrary coefficient in the entire new zero ring. Polynomial
  evaluation is surjective, hence that external sum is finite type over its new
  zero ring, without old-ring finite type, field, domain or nontriviality.
  No polynomial equivalence or source index-zero convention is asserted.
- **Evaluation and homogeneous lifts.** [Weighted evaluation](docs/WeightedEvaluation.md)
  at chosen homogeneous elements of arbitrary natural weights, **including zero**,
  preserves degrees, is a native graded map and commutes with actual components.
  Only lifting **every** homogeneous target element requires the chosen family
  to generate over old degree zero. The [degree-one specialization](docs/HomogeneousLifts.md)
  uses all of `𝒮 1` and exactly `Algebra.adjoin (𝒮 0) (𝒮 1 : Set S) = ⊤`,
  including degree-zero targets. No finite-variable, domain, field or
  nontriviality assumption is needed.
- **Degree-one generation: all versus finite.** Under that old degree-one
  generation hypothesis, [every positive selected index](docs/VeroneseDegreeOne.md)
  is generated by **all** new degree one over its entire actual new zero ring,
  without finite generation. A finite **positive-weight** homogeneous generating
  family over old zero instead gives a [finite new degree-one family](docs/FiniteVeronese.md)
  at `D = Finsupp.weightedBlockSize w`; native old-zero finite type gives **some**
  positive index. These need no field, domain, nontriviality, equal weights or
  Noetherianity; the finite-family conclusions are not all-index claims.
- **Positive-weight blocks and monomial adjoin.** For finite indices and strictly
  positive natural weights, [exponent decomposition](docs/WeightedBlocks.md)
  recovers a whole finitely supported natural exponent vector of weight `k * D`
  as **exactly `k`** weight-`D` blocks, with positive, not necessarily minimal
  `D = max 1 (Fintype.card ι) * ∏ i, w i`. Over any commutative **semiring**,
  [monomial-adjoin membership](docs/WeightedBlockAdjoin.md) puts weight-`k * D`
  polynomials in the coefficient subalgebra generated by coefficient-one
  weight-`D` monomials, including arbitrary coefficients and `k = 0`.
  Neither result alone gives polynomial factorization or whole-ring generation.
- **Selected weighted-polynomial components.** For finite variables, arbitrary
  natural weights **including zero**, any commutative **semiring**, and each
  prescribed `n > 0`, [one finite homogeneous family](docs/WeightedVeroneseGenerators.md)
  generates **all** polynomial degrees divisible by `n` over the entire
  coefficient semiring—not whole selected-ring finite type or degree-one generation.
- **Finite type at each positive index.** Finite homogeneous generators of
  arbitrary natural weights over entire old zero, or native old-zero finite
  type, make [every prescribed positive whole selected ring](docs/VeroneseFiniteType.md)
  finite type over its **entire actual new zero ring**. No domain, nontriviality,
  field, Noetherianity, positive or equal weights are required. This is distinct
  from index-zero finite type and from degree-one generation at every index.
- **Finite inclusion and whole-ring residue modules.** Under old-zero finite
  type, the [inclusion at each `n > 0`](docs/VeroneseFinite.md) makes the **old ring**
  finite over the whole external selected ring via the actual `inclusion.toAlgebra`.
  For `n > 0`, `r < n`, the [residue projection](docs/VeroneseResidue.md) is linear
  for that same action and has exactly the elements supported in residue `r`
  as its range. Ambient module finiteness makes this image finite; old-zero
  finite type suffices. The [shifted sum](docs/VeroneseResidueModule.md)
  `⨁ k, 𝒮 (n * k + r)` has whole selected-ring convolution; coefficient evaluation
  is linear and injective for `n > 0` and **any** `r`, and identifies the projection
  range when also `r < n`. Ambient finiteness, or full old-zero finite type,
  transports under those positive reduced-index bounds. No individual-fiber
  whole-ring action, arbitrary-submodule finiteness or zero-index bijection follows.
- **Coherent high tails.** [Tail equivalence](docs/CoherentTailVeronese.md) requires
  `N > 0`, an actual zero-ring equivalence, additive equivalences in **all**
  degrees at least `N`, and coefficient/high-product compatibility. For `N ≤ n`
  it identifies the **entire** selected rings with native degree-preserving
  inverse maps; for `n > 0`, `selected_zero` is the exact coefficient square.
  No maps across missing original low degrees or Proj/scheme equivalence follow.

## Find an interface

The [canonical module/interface map](docs/API.md#production-modules) merges
precise assumptions with declaration names and direct imports. Its
[scope distinctions](docs/API.md#scope-distinctions) separate full localizations
from degree-zero pieces, polynomial components from whole selected rings, and
algebraic results from geometric claims. The [subject guides](docs/README.md)
provide focused explanations and clients.

## Build and use

Install the exact toolchain in `lean-toolchain`: Lean `v4.34.0-rc2`.
The direct dependencies are mathlib at
`83abb3e776bdefcbc447a1e44d0debe4010039e5` and the released
`coherent-modules` at `1dfe73a0d8d506a7871d5393e274582d36161265`;
`lake-manifest.json` freezes all ten resolved Git dependencies. From a checkout, obtain matching compiled
mathlib artifacts **before** building:

```sh
lake exe cache get
lake --wfail build
```

Do not replace the manifest or substitute a moving mathlib branch. The default
build includes the aggregate library, all regression-test modules and
the four stored examples. Named targets are also available:

```sh
lake --wfail build GradedRings GradedRingsTests GradedRingsExamples
lake --wfail build QuotientLocalization FinitenessAndPrimes Symmetric Multiplicity
```

All shipped Lean modules use Lean's module system. Ordinary-import
`GradedRings` for the full API, or a `GradedRings.<Leaf>` module from the
[API map](docs/API.md#production-modules). Public imports re-export the intended
interfaces; clients need neither `import all` nor private names. The selected-ring
leaf also exports its named technical grading and reindexing helpers, but the main
API does not require clients to use them.

The quotient, localization and prime-multiplicity tests compare full public
constructions with their original constructions by Lean-private ordinary-import
`rfl` equalities. This checks computation as well as availability of theorem
names. Ordinary builds check proofs; named axiom prints in tests/examples
complement, but do not replace, the complete transitive standard-axiom audit
including private and generated declarations.

### Build resources

Build time and memory depend on the targets, cache state, network and hardware.
These instructions specify neither a cold-build time nor a minimum-memory
guarantee. Leave headroom for Lake, dependencies and documentation generation;
`LAKE_JOBS` and `LEAN_NUM_THREADS` settings alone should not be treated as enforced
aggregate process, thread or memory bounds.

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

The [API guide](docs/API.md#proof-ideas) outlines the quotient/localization,
finite-generation, Noetherian, prime-correspondence and symmetric-algebra arguments.

## References and credit

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

Lean and mathlib supply the foundational APIs. Authentic notices and distinct
contributor/adaptation roles are summarized in
[provenance and credits](docs/PROVENANCE.md).

## Natural filtrations and their integer extensions

`GradedRings.FilteredAssociatedGraded.Adic` extends an ideal-compatible natural
filtration `F` of an `R`-module to an integer filtration with stage
`F.N (Int.toNat n)`. Every nonpositive stage remains `F.N 0`; the construction
does not require the filtration to start at the whole module. Its least-extension
property compares stagewise inclusions with arbitrary integer filtrations.

At every natural degree, including zero, the associated graded piece is canonically
`R`-linearly equivalent to the quotient of `F.N q` by the pullback of `F.N (q+1)`.
This equivalence preserves quotient representatives. Negative pieces of these
extensions vanish, while general integer filtrations may have nonzero negative
pieces. The ideal-adic extension specializes the stable filtration of the whole
module and has stages `I ^ (Int.toNat n) • ⊤`.
