# Degree-multiplying maps on homogeneous localizations

`GradedRings.HomogeneousLocalizationMap` is a reusable algebraic API with only
the pinned mathlib dependency. Import this leaf directly, or import
`GradedRings` for the whole library. The direct public-import client is
[`test/HomogeneousLocalizationMap.lean`](../test/HomogeneousLocalizationMap.lean);
[`test/RootClient.lean`](../test/RootClient.lean) also checks the aggregate import.
This API is distinct from the same-ring localization grading and zero-component
equivalence in [`GradedRings.Localization`](../GradedRings/Localization.lean).

## Mathematics and hypotheses

Let `𝒜 : ℕ → σ` and `ℬ : ℕ → τ` be gradings of arbitrary commutative rings
`A` and `B`, with `SetLike` and `AddSubgroupClass` instances and
`GradedRing 𝒜` and `GradedRing ℬ`. An **ordinary unital ring homomorphism**
`f : A →+* B` and a number `d : ℕ` must satisfy

```
hdeg : ∀ n a, a ∈ 𝒜 n → f a ∈ ℬ (d * n)
```

For arbitrary submonoids `P : Submonoid A` and `Q : Submonoid B` with
`hPQ : P ≤ Q.comap f`, `HomogeneousLocalization.mapDegreeMul 𝒜 ℬ f d hdeg hPQ`
is a ring homomorphism from `HomogeneousLocalization 𝒜 P` to
`HomogeneousLocalization ℬ Q`. It maps a representative `c : NumDenSameDeg 𝒜 P`
to the equal-degree fraction with numerator `f c.num`, denominator `f c.den`,
and degree `d * c.deg` (`mapDegreeMul_mk`). Applying `val` agrees with the
ordinary `IsLocalization.map (Localization Q) f hPQ` (`val_mapDegreeMul`).
Equality of fractions is inherited from the ordinary localization, including
annihilating-denominator equivalences when `A` or `B` has zero divisors.

`Away.mapDegreeMul 𝒜 ℬ f d hdeg a` specializes to the powers of `a` and `f a`.
For homogeneous `a` of degree `m` and `b` of degree `n • m`,
`Away.mapDegreeMul_mk` states

```
f_away (Away.mk 𝒜 ha n b hb) = Away.mk ℬ (hdeg m a ha) n (f b) …
```

The numerator on the right has degree `n • (d * m)`; this is the same as
`d * (n • m)`. The ring-homomorphism equality
`Away.mapDegreeMul_awayMap` commutes with the native same-ring restriction
`awayMap` from `a` to `a * b` (on the target from `f a` to `f (a * b)`),
assuming `b` homogeneous but **without** assuming `a` homogeneous.
`mapDegreeMul_one` and `Away.mapDegreeMul_one` recover mathlib's native
same-index maps whenever `f` comes from a `GradedRingHom` and `d = 1`.
`mapDegreeMul_id` and `mapDegreeMul_comp` give identity and composition, with
the latter scaling by `e * d`.

The thirteen named entry points, in the `HomogeneousLocalization` namespace,
are `NumDenSameDeg.mapDegreeMul`, `mapDegreeMulFun`,
`val_mapDegreeMulFun`, `mapDegreeMul`, `mapDegreeMul_mk`,
`val_mapDegreeMul`, `Away.mapDegreeMul`, `Away.mapDegreeMul_mk`,
`Away.mapDegreeMul_awayMap`, `mapDegreeMul_one`,
`Away.mapDegreeMul_one`, `mapDegreeMul_id` and `mapDegreeMul_comp`.
`mapDegreeMulFun` is the quotient-level function and
`val_mapDegreeMulFun` is its ordinary-localization compatibility;
`NumDenSameDeg.mapDegreeMul` maps equal-degree representatives.
The bundled `mapDegreeMul` is the main ring-homomorphism interface.

No positivity or injectivity condition on `n ↦ d * n` is necessary: `d = 0`
works if the stated degree-compatibility holds. There are no domain, field,
nonzero-denominator, nonnilpotence, finite-generation, surjectivity, or
denominator-regularity requirements. Zero rings and submonoids containing zero
retain mathlib's native localization behavior. This library constructs no
prime contraction, Proj/scheme map, glued sheaf map, or general regrading
hierarchy; such geometry can impose additional hypotheses.

For concrete API uses with arbitrary rings, including `d = 0`, the native
factor-one maps, the restriction square and composition, see the public-import
client. The implementation uses mathlib's quotient, `mk`/`val`/
`val_injective`, native `awayMap`, and `IsLocalization.map` rather than
defining an alternative fraction equivalence.

## Attribution

Formal Frontier agents developed the original producer and client in the
incubator and separately adapted their destination imports and registration.
Mathlib's original homogeneous-localization construction and native maps
credit Jujian Zhang and Eric Wieser; the adapted producer retains Jujian
Zhang's 2022 copyright notice and applicable Apache-2.0 terms. See
[provenance and credits](PROVENANCE.md). These maps do not themselves
establish source correspondence or a scheme construction.
