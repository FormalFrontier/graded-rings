# Graded rings

Reusable Lean constructions for graded quotients and localizations,
degree-multiplying homogeneous-localization maps, finiteness, homogeneous prime
ideals, symmetric algebras, selected-component Veronese rings and
prime-multiplicity valuations.

Authors: Formal Frontier Agents. Original project contributions are licensed
under [Apache-2.0](LICENSE). Atlas is the responsible maintainer on behalf of the
shared source-maintainer team. AI agents authored the mathematics, Lean proofs,
clients and documentation; exact contributions are listed in
[provenance and credits](docs/PROVENANCE.md).

## Mathematical scope

| Module | Main interface and assumptions |
| --- | --- |
| [Quotient](GradedRings/Quotient.lean) | `Ideal.Quotient.gradedRing` equips a quotient by a homogeneous ideal with the image grading. The index is an additive monoid with decidable equality; the coefficient ring is commutative, possibly the zero ring. `gradedRingHom` bundles the quotient map. |
| [Localization](GradedRings/Localization.lean) | `GradedLocalization.gradedRing` grades ordinary localization at a submonoid of homogeneous elements, with an additive commutative **group** of degrees. `homogeneousLocalizationEquivZeroComponent` identifies equal-degree homogeneous fractions with the zero component. No domain or non-zero-divisor hypothesis is imposed on this construction. |
| [HomogeneousLocalizationMap](GradedRings/HomogeneousLocalizationMap.lean) | `HomogeneousLocalization.mapDegreeMul` sends naturally graded homogeneous localizations across an **ordinary** unital ring homomorphism multiplying natural degrees by `d`, given explicit degree compatibility and mapped denominators. It supports arbitrary source charts and restriction along a homogeneous factor, factor-one recovery, identity and composition. No domain, denominator-regularity or positive-`d` assumption. See the [thirteen-name guide](docs/degree-multiplying-homogeneous-localization.md). |
| [FiniteType](GradedRings/FiniteType.lean) | `GradedAlgebra.irrelevant_fg_iff_finiteType`: for a naturally graded commutative ring, the irrelevant ideal is finitely generated exactly when the ring is finite type over degree zero. Includes extraction of finite homogeneous ideal generators. |
| [Noetherian](GradedRings/Noetherian.lean) | `isNoetherianRing_iff_gradeZero_and_irrelevant_fg`: Noetherianity is equivalent to Noetherianity of degree zero plus finite generation of the irrelevant ideal. No domain or nontriviality assumption. |
| [HomogeneousPrime](GradedRings/HomogeneousPrime.lean) | In an integer-graded commutative ring with a positive-degree homogeneous unit, `homogeneousPrimeEquivDegreeZeroPrime` identifies homogeneous prime ideals with primes of degree zero. The inverse is **radical extension**, not plain extension. |
| [SymmetricAlgebra](GradedRings/SymmetricAlgebra.lean) | Basis-free grading, `gradedMap` and linear-equivalence functoriality over a commutative **semiring** and arbitrary modules. A basis is needed only for the degree-preserving polynomial-coordinate presentation. |
| [PrimeMultiplicity](GradedRings/PrimeMultiplicity.lean) | For a prime element in a commutative domain with well-founded divisibility, `valuation` sends nonzero `r` to `exp (-multiplicity p r)`. Its extension to localization requires denominators to be non-zero-divisors. |
| [HomogeneousPrimeMultiplicity](GradedRings/HomogeneousPrimeMultiplicity.lean) | Restricts that valuation to degree-zero homogeneous localization. On a nonzero homogeneous numerator over `p^n`, its value is `exp (n - multiplicity p x)`. Degrees form an additive commutative monoid. |
| [MvPolynomialAway](GradedRings/MvPolynomialAway.lean) | Over a field and an arbitrary variable type, bounds multiplicity by homogeneous degree, characterizes units by valuation one, and proves irreducibility at denominator order one for a positive-degree homogeneous prime polynomial. |
| [Veronese](GradedRings/Veronese.lean) | `GradedRing.Veronese.VeroneseRing 𝒮 n` selects the whole old components `𝒮 (n*j)` and has an internal grading for any `n`. The canonical inclusion is injective and identifies the whole degree-zero component when `0 < n`. No finiteness/domain assumption or scheme API. See the [selected-component guide](docs/Veronese.md). |

The full localized ring and its degree-zero subring are different objects.
The degree-multiplying map is distinct from this same-ring localization grading;
`d = 0` still requires an explicit degree-compatibility witness, and the chart
element need not be homogeneous for the restriction square. It does not construct
a Proj or scheme map.
The polynomial results do not identify a general graded ring with a polynomial
ring, and the valuation results do not apply to arbitrary rings with zero divisors.
No claim about complete coverage of a mathematical book follows from this API.

The [current hand-maintained API map](docs/API.md) links the original leaves and
the localization and Veronese guides. The [initial native 104-declaration snapshot](docs/API-initial-snapshot.md)
applies only to the earlier 28-module tree; see [documentation reproduction](docs/README.md)
for its exact inputs, limits and separately pinned generator.

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
build includes the aggregate library, all sixteen regression-test modules and
the four stored examples. Named targets are also available:

```sh
lake --wfail build GradedRings GradedRingsTests GradedRingsExamples
lake --wfail build QuotientLocalization FinitenessAndPrimes Symmetric Multiplicity
```

All 32 shipped Lean modules use Lean's native module system. A downstream native
module can ordinary-import `GradedRings` for the full API, or a subject leaf
such as `GradedRings.HomogeneousLocalizationMap`, `GradedRings.Quotient`,
`GradedRings.Veronese` or `GradedRings.SymmetricAlgebra`. Public imports
re-export the intended interfaces. The selected-ring leaf also exports its
named technical grading and reindexing helpers; clients do not need to rely on
them for the main API.
Clients do not need `import all` or access to private names.

The quotient, localization and prime-multiplicity tests compare full public
constructions with their original constructions by private ordinary-import
`rfl` equalities. This checks computation as well as availability of theorem
names. Named axiom prints in tests/examples complement, but do not replace,
the release's separate complete private/stored-body proof audit.

## Observed build resources

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
The basis-free symmetric algebra also supports projective-space applications.
These are mathematical references; no source PDF, figures or substantial source
prose is distributed. Detailed source correspondence and gaps are maintained
outside this reusable library.

Lean and mathlib supply the underlying formal language and foundational APIs.
See [provenance](docs/PROVENANCE.md) for the original project expression and
subsequent interface work. Revision-specific mathematical, proof, rights and
release decisions are recorded separately; this documentation is not itself
a certificate of acceptance or publication.
