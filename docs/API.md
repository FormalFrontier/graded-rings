# Public API map

This is a **hand-maintained map** of the current library, not a new native
doc-gen4 run, a complete declaration listing or a proof certificate. Import
`GradedRings` for the entire public interface, or import an individual
`GradedRings.<Leaf>` module. For exact mathematical hypotheses and practical
clients, see the [mathematical overview](../README.md), the
[degree-multiplying localization guide](degree-multiplying-homogeneous-localization.md),
the [selected-component Veronese guide](Veronese.md), and the
[documentation notes](README.md).

The [initial native snapshot](API-initial-snapshot.md) displays 104 declarations
from the original nine production leaves and the then-current 28-module
checkout. Its [unchanged manifest](api-manifest.json) authenticates **that
archived file**, not this map or the expanded library; historical source-line
links are accurate in the original revision, not necessarily here.

## Production modules

| Direct import | Main public interface |
| --- | --- |
| [`GradedRings.Quotient`](../GradedRings/Quotient.lean) | `Ideal.Quotient.gradedRing` and `gradedRingHom` for homogeneous-ideal quotients. |
| [`GradedRings.Localization`](../GradedRings/Localization.lean) | `GradedLocalization.gradedRing` for same-ring ordinary localization and `homogeneousLocalizationEquivZeroComponent` for its degree-zero component. Degrees form an additive commutative group. |
| [`GradedRings.HomogeneousLocalizationMap`](../GradedRings/HomogeneousLocalizationMap.lean) | `HomogeneousLocalization.mapDegreeMul` for ordinary ring homomorphisms multiplying natural degrees, with arbitrary source chart restriction compatibility, factor-one, identity and composition laws. See the [thirteen-name guide](degree-multiplying-homogeneous-localization.md). |
| [`GradedRings.FiniteType`](../GradedRings/FiniteType.lean) | `GradedAlgebra.irrelevant_fg_iff_finiteType` and homogeneous finite-generator extraction. |
| [`GradedRings.Noetherian`](../GradedRings/Noetherian.lean) | `GradedAlgebra.isNoetherianRing_iff_gradeZero_and_irrelevant_fg`. |
| [`GradedRings.HomogeneousPrime`](../GradedRings/HomogeneousPrime.lean) | `GradedRing.homogeneousPrimeEquivDegreeZeroPrime` by contraction and radical extension. |
| [`GradedRings.SymmetricAlgebra`](../GradedRings/SymmetricAlgebra.lean) | `SymmetricAlgebra.gradedAlgebra`, `gradedMap` and polynomial-coordinate maps. |
| [`GradedRings.PrimeMultiplicity`](../GradedRings/PrimeMultiplicity.lean) | `PrimeMultiplicity.valuation` and `localizationValuation` under stated domain and denominator hypotheses. |
| [`GradedRings.HomogeneousPrimeMultiplicity`](../GradedRings/HomogeneousPrimeMultiplicity.lean) | `HomogeneousLocalization.awayPrimeMultiplicityValuation`. |
| [`GradedRings.MvPolynomialAway`](../GradedRings/MvPolynomialAway.lean) | Homogeneous polynomial multiplicity bound, unit criterion and irreducibility application. |
| [`GradedRings.Veronese`](../GradedRings/Veronese.lean) | `GradedRing.Veronese.VeroneseRing` and its whole selected-degree `component`; `inclusion`, `inclusion_injective` for positive index, `subring` as its exact range, and `zeroRingEquiv` for positive index. See the [guide](Veronese.md). |

The degree-multiplying map module does **not** replace the existing same-ring grading or
zero-component equivalence. For natural gradings `𝒜`, `ℬ` of arbitrary
commutative rings, its ordinary unital `f : A →+* B` must satisfy
`hdeg : ∀ n a, a ∈ 𝒜 n → f a ∈ ℬ (d * n)` and the arbitrary submonoids must
satisfy `hPQ : P ≤ Q.comap f`. This includes `d = 0` only when `hdeg` is
provided; no domain, regular-denominator or positive-scaling assumption is
added. The source chart element need not be homogeneous for
`Away.mapDegreeMul_awayMap`; only the multiplicative restriction factor does.

The thirteen exposed names under `HomogeneousLocalization` are:

| Construction | Associated laws |
| --- | --- |
| `NumDenSameDeg.mapDegreeMul` | Equal-degree numerator/denominator representatives are sent to degree `d * c.deg`. |
| `mapDegreeMulFun` | `val_mapDegreeMulFun` relates the quotient function to ordinary `IsLocalization.map`. |
| `mapDegreeMul` | `mapDegreeMul_mk` and `val_mapDegreeMul` give the fraction and ordinary-localization formulas. |
| `Away.mapDegreeMul` | `Away.mapDegreeMul_mk` and `Away.mapDegreeMul_awayMap` give the chart formula and arbitrary-source-chart restriction square. |
| Factor-one, identity, composition | `mapDegreeMul_one`, `Away.mapDegreeMul_one`, `mapDegreeMul_id`, `mapDegreeMul_comp` (composed factor `e * d`). |

## Aggregate, clients and examples

[`GradedRings`](../GradedRings.lean) publicly imports all eleven production leaves.
The default test target registers sixteen private regression clients, including
the [direct map client](../test/HomogeneousLocalizationMap.lean) and
[direct Veronese client](../test/Veronese.lean), and the
[aggregate-import witness](../test/RootClient.lean). Four standalone
[examples](../examples/) remain registered. These clients and examples
are not extra advertised public interfaces. For old native displayed types
and docstrings, consult the separately labeled initial snapshot; its 104
names are not a count of the current public API.
