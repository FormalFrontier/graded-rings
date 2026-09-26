# Generated API reference

Public API of graded-rings: 104 declarations across nine production leaves.
The aggregate module, fourteen tests and four examples add no public declarations.
Existing absent docstrings are stated explicitly, not synthesized by this renderer.

Signatures below are native doc-gen4 display signatures with all displayed implicit
arguments retained, not declarations with proof bodies. Short names use the source
namespace and imports; universe parameters are arbitrary. Module documentation
is extracted verbatim from the exact source. All source links are relative to this
checkout. See [generation and provenance](README.md), [exact input manifest](api-manifest.json)
and the [mathematical overview](../README.md).

## Module `GradedRings`

> No module docstring is supplied in this source; see the linked module.

[Module source](../GradedRings.lean)

## Module `GradedRings.FiniteType`

> # Finite type and the irrelevant ideal
>
> This file characterizes finite type over the degree-zero piece of a naturally
> graded commutative ring in terms of finite generation of its irrelevant ideal.
> It also supplies a general finite homogeneous generating-set lemma for
> finitely generated homogeneous ideals.

[Module source](../GradedRings/FiniteType.lean)

### HomogeneousIdeal.exists_finset_span_eq_of_fg

```lean
theorem HomogeneousIdeal.exists_finset_span_eq_of_fg {A : Type u} [CommRing A] {σ : Type v} [SetLike σ A] [AddSubgroupClass σ A] {ι : Type w} [DecidableEq ι] [AddMonoid ι] (𝒜 : ι → σ) [GradedRing 𝒜] (I : HomogeneousIdeal 𝒜) (hI : I.toIdeal.FG) : ∃ (s : Finset A), Ideal.span ↑s = I.toIdeal ∧ ∀ x ∈ s, SetLike.IsHomogeneousElem 𝒜 x
```

A finitely generated homogeneous ideal admits a finite set of homogeneous
ideal generators.

[Source](../GradedRings/FiniteType.lean#L31) (line 31).

### GradedAlgebra.irrelevant_exists_finset_span_eq_of_fg

```lean
theorem GradedAlgebra.irrelevant_exists_finset_span_eq_of_fg {A : Type u} [CommRing A] {σ : Type v} [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] (h : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.FG) : ∃ (s : Finset A), Ideal.span ↑s = (HomogeneousIdeal.irrelevant 𝒜).toIdeal ∧ ∀ x ∈ s, ∃ n > 0, x ∈ 𝒜 n
```

If the irrelevant ideal is finitely generated, it has a finite set of
strictly positive-degree homogeneous generators.

[Source](../GradedRings/FiniteType.lean#L63) (line 63).

### GradedAlgebra.finiteType_of_irrelevant_fg

```lean
theorem GradedAlgebra.finiteType_of_irrelevant_fg {A : Type u} [CommRing A] {σ : Type v} [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] (h : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.FG) : Algebra.FiniteType (↥(𝒜 0)) A
```

Finite generation of the irrelevant ideal implies finite type over the
degree-zero piece. The proof uses strong induction on homogeneous degree and
does not require a domain or nontriviality assumption.

[Source](../GradedRings/FiniteType.lean#L92) (line 92).

### GradedAlgebra.irrelevant_le_span_of_adjoin_eq_top

```lean
theorem GradedAlgebra.irrelevant_le_span_of_adjoin_eq_top {A : Type u} [CommRing A] {σ : Type v} [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] (s : Set A) (hhom : ∀ x ∈ s, ∃ (n : ℕ), n ≠ 0 ∧ x ∈ 𝒜 n) (hgen : Algebra.adjoin (↥(𝒜 0)) s = ⊤) : (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤ Ideal.span s
```

Positive-degree homogeneous algebra generators span the irrelevant ideal
as an ideal.

[Source](../GradedRings/FiniteType.lean#L139) (line 139).

### GradedAlgebra.irrelevant_fg_of_finiteType

```lean
theorem GradedAlgebra.irrelevant_fg_of_finiteType {A : Type u} [CommRing A] {σ : Type v} [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] [Algebra.FiniteType (↥(𝒜 0)) A] : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.FG
```

Finite type over the degree-zero piece implies finite generation of the
irrelevant ideal.

[Source](../GradedRings/FiniteType.lean#L171) (line 171).

### GradedAlgebra.irrelevant_fg_iff_finiteType

```lean
theorem GradedAlgebra.irrelevant_fg_iff_finiteType {A : Type u} [CommRing A] {σ : Type v} [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.FG ↔ Algebra.FiniteType (↥(𝒜 0)) A
```

For a naturally graded commutative ring, the irrelevant ideal is finitely
generated if and only if the ring is of finite type over its degree-zero
piece.

[Source](../GradedRings/FiniteType.lean#L184) (line 184).

## Module `GradedRings.HomogeneousPrime`

> # Homogeneous prime ideals and the degree-zero component
>
> This file relates homogeneous prime ideals in an integer-graded commutative
> ring to prime ideals of its degree-zero component when the ring contains a
> positive-degree homogeneous unit. The inverse to contraction is radical
> extension; the radical cannot in general be omitted.

[Module source](../GradedRings/HomogeneousPrime.lean)

### GradedRing.inv_mem_of_isUnit

```lean
theorem GradedRing.inv_mem_of_isUnit {A : Type u} [CommRing A] {σ : Type v} [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℤ → σ) [GradedRing 𝒜] {d : ℤ} {u : A} (hu : u ∈ 𝒜 d) (hu' : IsUnit u) : ↑hu'.unit⁻¹ ∈ 𝒜 (-d)
```

The inverse selected from a homogeneous unit of degree `d` is homogeneous
of degree `-d`.

[Source](../GradedRings/HomogeneousPrime.lean#L30) (line 30).

### GradedRing.unit_zpow_mem

```lean
theorem GradedRing.unit_zpow_mem {A : Type u} [CommRing A] {σ : Type v} [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℤ → σ) [GradedRing 𝒜] {d : ℤ} (u : Aˣ) (hu : ↑u ∈ 𝒜 d) (n : ℤ) : ↑(u ^ n) ∈ 𝒜 (n * d)
```

An integer power of a homogeneous unit of degree `d` is homogeneous of
degree `n * d`.

[Source](../GradedRings/HomogeneousPrime.lean#L54) (line 54).

### GradedRing.degreeZeroProjection

```lean
def GradedRing.degreeZeroProjection {A : Type u} [CommRing A] {σ : Type v} [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℤ → σ) [GradedRing 𝒜] : A →ₗ[↥(𝒜 0)] ↥(𝒜 0)
```

Projection onto the degree-zero component, linear over that component.

[Source](../GradedRings/HomogeneousPrime.lean#L76) (line 76).

### GradedRing.degreeZeroProjection_surjective

```lean
theorem GradedRing.degreeZeroProjection_surjective {A : Type u} [CommRing A] {σ : Type v} [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℤ → σ) [GradedRing 𝒜] : Function.Surjective ⇑(degreeZeroProjection 𝒜)
```

Projection onto degree zero is surjective.

[Source](../GradedRings/HomogeneousPrime.lean#L86) (line 86).

### GradedRing.comap_map_degreeZero

```lean
theorem GradedRing.comap_map_degreeZero {A : Type u} [CommRing A] {σ : Type v} [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℤ → σ) [GradedRing 𝒜] (q : Ideal ↥(𝒜 0)) : Ideal.comap (algebraMap (↥(𝒜 0)) A) (Ideal.map (algebraMap (↥(𝒜 0)) A) q) = q
```

Extending an ideal from the degree-zero component and contracting it back
recovers the original ideal.

[Source](../GradedRings/HomogeneousPrime.lean#L92) (line 92).

### GradedRing.map_degreeZero_isHomogeneous

```lean
theorem GradedRing.map_degreeZero_isHomogeneous {A : Type u} [CommRing A] {σ : Type v} [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℤ → σ) [GradedRing 𝒜] (q : Ideal ↥(𝒜 0)) : Ideal.IsHomogeneous 𝒜 (Ideal.map (algebraMap (↥(𝒜 0)) A) q)
```

The extension of a degree-zero ideal is homogeneous.

[Source](../GradedRings/HomogeneousPrime.lean#L112) (line 112).

### GradedRing.radical_map_degreeZero_isPrime

```lean
theorem GradedRing.radical_map_degreeZero_isPrime {A : Type u} [CommRing A] {σ : Type v} [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℤ → σ) [GradedRing 𝒜] {d : ℤ} (u : Aˣ) (hu : ↑u ∈ 𝒜 d) (hd : 0 < d) (q : Ideal ↥(𝒜 0)) (hq : q.IsPrime) : (Ideal.map (algebraMap (↥(𝒜 0)) A) q).radical.IsPrime
```

The radical extension of a prime ideal from degree zero is prime when the
graded ring contains a positive-degree homogeneous unit.

[Source](../GradedRings/HomogeneousPrime.lean#L172) (line 172).

### GradedRing.radical_map_comap_degreeZero

```lean
theorem GradedRing.radical_map_comap_degreeZero {A : Type u} [CommRing A] {σ : Type v} [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℤ → σ) [GradedRing 𝒜] {d : ℤ} (u : Aˣ) (hu : ↑u ∈ 𝒜 d) (hd : 0 < d) (P : Ideal A) (hPprime : P.IsPrime) (hPhom : Ideal.IsHomogeneous 𝒜 P) : (Ideal.map (algebraMap (↥(𝒜 0)) A) (Ideal.comap (algebraMap (↥(𝒜 0)) A) P)).radical = P
```

A homogeneous prime ideal is the radical extension of its contraction to
degree zero when the graded ring contains a positive-degree homogeneous unit.

[Source](../GradedRings/HomogeneousPrime.lean#L214) (line 214).

### GradedRing.homogeneousPrimeEquivDegreeZeroPrime

```lean
def GradedRing.homogeneousPrimeEquivDegreeZeroPrime {A : Type u} [CommRing A] {σ : Type v} [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℤ → σ) [GradedRing 𝒜] {d : ℤ} (u : Aˣ) (hu : ↑u ∈ 𝒜 d) (hd : 0 < d) : { P : Ideal A // P.IsPrime ∧ Ideal.IsHomogeneous 𝒜 P } ≃ { q : Ideal ↥(𝒜 0) // q.IsPrime }
```

If an integer-graded commutative ring has a positive-degree homogeneous
unit, contraction to degree zero and radical extension are inverse on prime
ideals and homogeneous prime ideals.

[Source](../GradedRings/HomogeneousPrime.lean#L244) (line 244).

## Module `GradedRings.HomogeneousPrimeMultiplicity`

> # Prime multiplicity on homogeneous localizations
>
> The prime-multiplicity valuation on an ordinary localization restricts to its
> degree-zero homogeneous subring.  On a homogeneous fraction `x / p ^ n`, its
> value is `exp (n - multiplicity p x)`.

[Module source](../GradedRings/HomogeneousPrimeMultiplicity.lean)

### HomogeneousLocalization.awayPrimeMultiplicityValuation

```lean
noncomputable def HomogeneousLocalization.awayPrimeMultiplicityValuation {A : Type u_1} {ι : Type u_2} {σ : Type u_3} [CommRing A] [IsDomain A] [WfDvdMonoid A] [SetLike σ A] [AddSubgroupClass σ A] [AddCommMonoid ι] [DecidableEq ι] (𝒜 : ι → σ) [GradedRing 𝒜] {p : A} (hp : Prime p) : Valuation (Away 𝒜 p) (WithZero (Multiplicative ℤ))
```

The prime-multiplicity valuation on the degree-zero homogeneous
localization away from a prime element.

[Source](../GradedRings/HomogeneousPrimeMultiplicity.lean#L33) (line 33).

### HomogeneousLocalization.isDomain_away

```lean
theorem HomogeneousLocalization.isDomain_away {A : Type u_1} {ι : Type u_2} {σ : Type u_3} [CommRing A] [IsDomain A] [SetLike σ A] [AddSubgroupClass σ A] [AddCommMonoid ι] [DecidableEq ι] (𝒜 : ι → σ) [GradedRing 𝒜] {p : A} (hp : Prime p) : IsDomain (Away 𝒜 p)
```

A homogeneous localization away from a prime in a domain is itself a
domain.  This is kept as an explicit construction because the nonzeroness of
the powers submonoid depends on the supplied primality proof.

[Source](../GradedRings/HomogeneousPrimeMultiplicity.lean#L42) (line 42).

### HomogeneousLocalization.awayPrimeMultiplicityValuation_mk

```lean
theorem HomogeneousLocalization.awayPrimeMultiplicityValuation_mk {A : Type u_1} {ι : Type u_2} {σ : Type u_3} [CommRing A] [IsDomain A] [WfDvdMonoid A] [SetLike σ A] [AddSubgroupClass σ A] [AddCommMonoid ι] [DecidableEq ι] (𝒜 : ι → σ) [GradedRing 𝒜] {p : A} {d : ι} (hp : Prime p) (hf : p ∈ 𝒜 d) (n : ℕ) (x : A) (hx : x ∈ 𝒜 (n • d)) (hx0 : x ≠ 0) : (awayPrimeMultiplicityValuation 𝒜 hp) (Away.mk 𝒜 hf n x hx) = WithZero.exp (↑n - ↑(multiplicity p x))
```

No declaration docstring is supplied in this source.

[Source](../GradedRings/HomogeneousPrimeMultiplicity.lean#L52) (line 52).

## Module `GradedRings.Localization`

> # Graded localizations
>
> This file constructs the natural grading on an ordinary localization at a
> submonoid of homogeneous elements.  A fraction with numerator of degree
> `i + j` and denominator of degree `j` belongs to the degree-`i` component.
>
> Public constructions retain their ordinary computational interface. The private
> membership proof stays private and is inlined where exposed data require it.

[Module source](../GradedRings/Localization.lean)

### GradedLocalization.component

```lean
def GradedLocalization.component {A : Type u} [CommRing A] {ι : Type v} [DecidableEq ι] [AddCommGroup ι] {σ : Type w} [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ι → σ) [GradedRing 𝒜] (M : Submonoid A) (i : ι) : AddSubgroup (Localization M)
```

The degree-`i` component of the localization at a homogeneous submonoid.
An element belongs to it when it has a representative `a / b` with `a` of
degree `i + j` and `b` of degree `j` for some `j`.

[Source](../GradedRings/Localization.lean#L34) (line 34).

### GradedLocalization.mk_mem_component

```lean
theorem GradedLocalization.mk_mem_component {A : Type u} [CommRing A] {ι : Type v} [DecidableEq ι] [AddCommGroup ι] {σ : Type w} [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ι → σ) [GradedRing 𝒜] (M : Submonoid A) {i j : ι} (a : ↥(𝒜 (i + j))) (b : ↥(𝒜 j)) (hb : ↑b ∈ M) : Localization.mk ↑a ⟨↑b, hb⟩ ∈ component 𝒜 M i
```

No declaration docstring is supplied in this source.

[Source](../GradedRings/Localization.lean#L63) (line 63).

### GradedLocalization.algebraMap_mem_component

```lean
theorem GradedLocalization.algebraMap_mem_component {A : Type u} [CommRing A] {ι : Type v} [DecidableEq ι] [AddCommGroup ι] {σ : Type w} [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ι → σ) [GradedRing 𝒜] (M : Submonoid A) {i : ι} {a : A} (ha : a ∈ 𝒜 i) : (algebraMap A (Localization M)) a ∈ component 𝒜 M i
```

No declaration docstring is supplied in this source.

[Source](../GradedRings/Localization.lean#L68) (line 68).

### GradedLocalization.componentGradedMonoid

```lean
instance GradedLocalization.componentGradedMonoid {A : Type u} [CommRing A] {ι : Type v} [DecidableEq ι] [AddCommGroup ι] {σ : Type w} [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ι → σ) [GradedRing 𝒜] (M : Submonoid A) : SetLike.GradedMonoid (component 𝒜 M)
```

The localized components are closed under graded multiplication.

[Source](../GradedRings/Localization.lean#L76) (line 76).

### GradedLocalization.zeroComponent

```lean
def GradedLocalization.zeroComponent {A : Type u} [CommRing A] {ι : Type v} [DecidableEq ι] [AddCommGroup ι] {σ : Type w} [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ι → σ) [GradedRing 𝒜] (M : Submonoid A) : Subring (Localization M)
```

The degree-zero localized component as a subring of the ordinary
localization.

[Source](../GradedRings/Localization.lean#L93) (line 93).

### GradedLocalization.toZeroComponent

```lean
def GradedLocalization.toZeroComponent {A : Type u} [CommRing A] {ι : Type v} [DecidableEq ι] [AddCommGroup ι] {σ : Type w} [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ι → σ) [GradedRing 𝒜] (M : Submonoid A) : HomogeneousLocalization 𝒜 M →+* ↥(zeroComponent 𝒜 M)
```

The natural map from the homogeneous localization to the degree-zero
component of the ordinary localization.

[Source](../GradedRings/Localization.lean#L116) (line 116).

### GradedLocalization.toZeroComponent_injective

```lean
theorem GradedLocalization.toZeroComponent_injective {A : Type u} [CommRing A] {ι : Type v} [DecidableEq ι] [AddCommGroup ι] {σ : Type w} [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ι → σ) [GradedRing 𝒜] (M : Submonoid A) : Function.Injective ⇑(toZeroComponent 𝒜 M)
```

No declaration docstring is supplied in this source.

[Source](../GradedRings/Localization.lean#L143) (line 143).

### GradedLocalization.toZeroComponent_surjective

```lean
theorem GradedLocalization.toZeroComponent_surjective {A : Type u} [CommRing A] {ι : Type v} [DecidableEq ι] [AddCommGroup ι] {σ : Type w} [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ι → σ) [GradedRing 𝒜] (M : Submonoid A) : Function.Surjective ⇑(toZeroComponent 𝒜 M)
```

No declaration docstring is supplied in this source.

[Source](../GradedRings/Localization.lean#L149) (line 149).

### GradedLocalization.homogeneousLocalizationEquivZeroComponent

```lean
noncomputable def GradedLocalization.homogeneousLocalizationEquivZeroComponent {A : Type u} [CommRing A] {ι : Type v} [DecidableEq ι] [AddCommGroup ι] {σ : Type w} [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ι → σ) [GradedRing 𝒜] (M : Submonoid A) : HomogeneousLocalization 𝒜 M ≃+* ↥(zeroComponent 𝒜 M)
```

The degree-zero part of the full graded localization agrees with mathlib's
`HomogeneousLocalization`.  The forward map is induced by
`HomogeneousLocalization.val`.

[Source](../GradedRings/Localization.lean#L161) (line 161).

### GradedLocalization.projectionFun

```lean
noncomputable def GradedLocalization.projectionFun {A : Type u} [CommRing A] {ι : Type v} [DecidableEq ι] [AddCommGroup ι] {σ : Type w} [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ι → σ) [GradedRing 𝒜] (M : Submonoid A) (hM : M ≤ SetLike.homogeneousSubmonoid 𝒜) (i : ι) (x : Localization M) : Localization M
```

The degree-`i` part of a localized fraction.  A denominator degree is
chosen, and the numerator is projected to degree `i` plus that denominator
degree.  The localization relation makes the result independent of the
chosen representative, even when homogeneous denominators are zero divisors.

[Source](../GradedRings/Localization.lean#L171) (line 171).

### GradedLocalization.projectionFun_mk

```lean
theorem GradedLocalization.projectionFun_mk {A : Type u} [CommRing A] {ι : Type v} [DecidableEq ι] [AddCommGroup ι] {σ : Type w} [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ι → σ) [GradedRing 𝒜] (M : Submonoid A) (hM : M ≤ SetLike.homogeneousSubmonoid 𝒜) (i : ι) {a : A} {s : ↥M} {j : ι} (hs : ↑s ∈ 𝒜 j) : projectionFun 𝒜 M hM i (Localization.mk a s) = Localization.mk (↑(((DirectSum.decompose 𝒜) a) (i + j))) s
```

No declaration docstring is supplied in this source.

[Source](../GradedRings/Localization.lean#L195) (line 195).

### GradedLocalization.projection

```lean
noncomputable def GradedLocalization.projection {A : Type u} [CommRing A] {ι : Type v} [DecidableEq ι] [AddCommGroup ι] {σ : Type w} [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ι → σ) [GradedRing 𝒜] (M : Submonoid A) (hM : M ≤ SetLike.homogeneousSubmonoid 𝒜) (i : ι) : Localization M →+ Localization M
```

Projection onto degree `i` in a localization at homogeneous elements.

[Source](../GradedRings/Localization.lean#L207) (line 207).

### GradedLocalization.projection_mem_component

```lean
theorem GradedLocalization.projection_mem_component {A : Type u} [CommRing A] {ι : Type v} [DecidableEq ι] [AddCommGroup ι] {σ : Type w} [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ι → σ) [GradedRing 𝒜] (M : Submonoid A) (hM : M ≤ SetLike.homogeneousSubmonoid 𝒜) (i : ι) (x : Localization M) : (projection 𝒜 M hM i) x ∈ component 𝒜 M i
```

No declaration docstring is supplied in this source.

[Source](../GradedRings/Localization.lean#L230) (line 230).

### GradedLocalization.projection_eq_self_of_mem

```lean
theorem GradedLocalization.projection_eq_self_of_mem {A : Type u} [CommRing A] {ι : Type v} [DecidableEq ι] [AddCommGroup ι] {σ : Type w} [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ι → σ) [GradedRing 𝒜] (M : Submonoid A) (hM : M ≤ SetLike.homogeneousSubmonoid 𝒜) (i : ι) {x : Localization M} (hx : x ∈ component 𝒜 M i) : (projection 𝒜 M hM i) x = x
```

No declaration docstring is supplied in this source.

[Source](../GradedRings/Localization.lean#L239) (line 239).

### GradedLocalization.projection_eq_zero_of_mem

```lean
theorem GradedLocalization.projection_eq_zero_of_mem {A : Type u} [CommRing A] {ι : Type v} [DecidableEq ι] [AddCommGroup ι] {σ : Type w} [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ι → σ) [GradedRing 𝒜] (M : Submonoid A) (hM : M ≤ SetLike.homogeneousSubmonoid 𝒜) {i k : ι} (hik : i ≠ k) {x : Localization M} (hx : x ∈ component 𝒜 M k) : (projection 𝒜 M hM i) x = 0
```

No declaration docstring is supplied in this source.

[Source](../GradedRings/Localization.lean#L247) (line 247).

### GradedLocalization.projection_coe

```lean
theorem GradedLocalization.projection_coe {A : Type u} [CommRing A] {ι : Type v} [DecidableEq ι] [AddCommGroup ι] {σ : Type w} [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ι → σ) [GradedRing 𝒜] (M : Submonoid A) (hM : M ≤ SetLike.homogeneousSubmonoid 𝒜) (i : ι) (z : DirectSum ι fun (k : ι) => ↥(component 𝒜 M k)) : (projection 𝒜 M hM i) ((DirectSum.coeAddMonoidHom (component 𝒜 M)) z) = ↑(z i)
```

No declaration docstring is supplied in this source.

[Source](../GradedRings/Localization.lean#L257) (line 257).

### GradedLocalization.coe_injective

```lean
theorem GradedLocalization.coe_injective {A : Type u} [CommRing A] {ι : Type v} [DecidableEq ι] [AddCommGroup ι] {σ : Type w} [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ι → σ) [GradedRing 𝒜] (M : Submonoid A) (hM : M ≤ SetLike.homogeneousSubmonoid 𝒜) : Function.Injective ⇑(DirectSum.coeAddMonoidHom (component 𝒜 M))
```

No declaration docstring is supplied in this source.

[Source](../GradedRings/Localization.lean#L275) (line 275).

### GradedLocalization.coe_surjective

```lean
theorem GradedLocalization.coe_surjective {A : Type u} [CommRing A] {ι : Type v} [DecidableEq ι] [AddCommGroup ι] {σ : Type w} [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ι → σ) [GradedRing 𝒜] (M : Submonoid A) (hM : M ≤ SetLike.homogeneousSubmonoid 𝒜) : Function.Surjective ⇑(DirectSum.coeAddMonoidHom (component 𝒜 M))
```

No declaration docstring is supplied in this source.

[Source](../GradedRings/Localization.lean#L310) (line 310).

### GradedLocalization.isInternal

```lean
theorem GradedLocalization.isInternal {A : Type u} [CommRing A] {ι : Type v} [DecidableEq ι] [AddCommGroup ι] {σ : Type w} [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ι → σ) [GradedRing 𝒜] (M : Submonoid A) (hM : M ≤ SetLike.homogeneousSubmonoid 𝒜) : DirectSum.IsInternal (component 𝒜 M)
```

The localized homogeneous components form an internal direct sum.

[Source](../GradedRings/Localization.lean#L319) (line 319).

### GradedLocalization.decomposition

```lean
noncomputable def GradedLocalization.decomposition {A : Type u} [CommRing A] {ι : Type v} [DecidableEq ι] [AddCommGroup ι] {σ : Type w} [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ι → σ) [GradedRing 𝒜] (M : Submonoid A) (hM : M ≤ SetLike.homogeneousSubmonoid 𝒜) : DirectSum.Decomposition (component 𝒜 M)
```

The natural direct-sum decomposition of a localization at homogeneous
elements.

[Source](../GradedRings/Localization.lean#L323) (line 323).

### GradedLocalization.gradedRing

```lean
noncomputable def GradedLocalization.gradedRing {A : Type u} [CommRing A] {ι : Type v} [DecidableEq ι] [AddCommGroup ι] {σ : Type w} [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ι → σ) [GradedRing 𝒜] (M : Submonoid A) (hM : M ≤ SetLike.homogeneousSubmonoid 𝒜) : GradedRing (component 𝒜 M)
```

The natural grading on an ordinary localization at a homogeneous
submonoid.

[Source](../GradedRings/Localization.lean#L330) (line 330).

## Module `GradedRings.MvPolynomialAway`

> # Homogeneous localization of multivariate polynomial rings
>
> For a nonconstant homogeneous prime polynomial, prime multiplicity of a
> homogeneous numerator is bounded by the denominator exponent.  This is the
> degree estimate underlying reduced denominators in the homogeneous
> localization away from that polynomial.

[Module source](../GradedRings/MvPolynomialAway.lean)

### MvPolynomial.multiplicity_le_of_isHomogeneous

```lean
theorem MvPolynomial.multiplicity_le_of_isHomogeneous {k : Type u_1} {ι : Type u_2} [Field k] {p x : MvPolynomial ι k} {d n : ℕ} (hp : Prime p) (hpHom : p.IsHomogeneous d) (hd : d ≠ 0) (hxHom : x.IsHomogeneous (n * d)) (hx0 : x ≠ 0) : multiplicity p x ≤ n
```

A nonconstant homogeneous prime cannot occur in a homogeneous polynomial
of degree `n * d` with multiplicity greater than `n`.

[Source](../GradedRings/MvPolynomialAway.lean#L34) (line 34).

### MvPolynomial.exists_eq_pow_mul_C_of_multiplicity_eq

```lean
theorem MvPolynomial.exists_eq_pow_mul_C_of_multiplicity_eq {k : Type u_1} {ι : Type u_2} [Field k] {p x : MvPolynomial ι k} {d n : ℕ} (hp : Prime p) (hpHom : p.IsHomogeneous d) (hxHom : x.IsHomogeneous (n * d)) (hx0 : x ≠ 0) (hm : multiplicity p x = n) : ∃ (c : k), c ≠ 0 ∧ x = p ^ n * C c
```

If the multiplicity reaches the degree bound, the remaining factor is a
nonzero coefficient.

[Source](../GradedRings/MvPolynomialAway.lean#L49) (line 49).

### MvPolynomial.homogeneousAwayCoefficientHom

```lean
noncomputable def MvPolynomial.homogeneousAwayCoefficientHom {k : Type u_1} {ι : Type u_2} [Field k] (p : MvPolynomial ι k) : k →+* HomogeneousLocalization.Away (homogeneousSubmodule ι k) p
```

Coefficients map naturally to any degree-zero homogeneous localization of
a multivariate polynomial ring.

[Source](../GradedRings/MvPolynomialAway.lean#L77) (line 77).

### MvPolynomial.isUnit_away_mk_of_multiplicity_eq

```lean
theorem MvPolynomial.isUnit_away_mk_of_multiplicity_eq {k : Type u_1} {ι : Type u_2} [Field k] {p x : MvPolynomial ι k} {d n : ℕ} (hp : Prime p) (hpHom : p.IsHomogeneous d) (hxHom : x.IsHomogeneous (n * d)) (hx0 : x ≠ 0) (hm : multiplicity p x = n) : IsUnit (HomogeneousLocalization.Away.mk (homogeneousSubmodule ι k) hpHom n x hxHom)
```

A homogeneous fraction whose numerator contains the full possible power
of the homogeneous prime is a unit.

[Source](../GradedRings/MvPolynomialAway.lean#L90) (line 90).

### MvPolynomial.one_le_awayPrimeMultiplicityValuation

```lean
theorem MvPolynomial.one_le_awayPrimeMultiplicityValuation {k : Type u_1} {ι : Type u_2} [Field k] {p : MvPolynomial ι k} {d : ℕ} (hp : Prime p) (hpHom : p.IsHomogeneous d) (hd : d ≠ 0) {z : HomogeneousLocalization.Away (homogeneousSubmodule ι k) p} (hz : z ≠ 0) : 1 ≤ (HomogeneousLocalization.awayPrimeMultiplicityValuation (homogeneousSubmodule ι k) hp) z
```

Every nonzero element of the degree-zero homogeneous localization has
prime-multiplicity valuation at least one (equivalently, nonnegative
denominator order).

[Source](../GradedRings/MvPolynomialAway.lean#L116) (line 116).

### MvPolynomial.exists_awayPrimeMultiplicityValuation_eq_exp_nat

```lean
theorem MvPolynomial.exists_awayPrimeMultiplicityValuation_eq_exp_nat {k : Type u_1} {ι : Type u_2} [Field k] {p : MvPolynomial ι k} {d : ℕ} (hp : Prime p) (hpHom : p.IsHomogeneous d) (hd : d ≠ 0) {z : HomogeneousLocalization.Away (homogeneousSubmodule ι k) p} (hz : z ≠ 0) : ∃ (q : ℕ), (HomogeneousLocalization.awayPrimeMultiplicityValuation (homogeneousSubmodule ι k) hp) z = WithZero.exp ↑q
```

The valuation of a nonzero homogeneous-localization element is an
exponential of a natural-number denominator order.

[Source](../GradedRings/MvPolynomialAway.lean#L141) (line 141).

### MvPolynomial.awayPrimeMultiplicityValuation_eq_one_iff_isUnit

```lean
theorem MvPolynomial.awayPrimeMultiplicityValuation_eq_one_iff_isUnit {k : Type u_1} {ι : Type u_2} [Field k] {p : MvPolynomial ι k} {d : ℕ} (hp : Prime p) (hpHom : p.IsHomogeneous d) (hd : d ≠ 0) {z : HomogeneousLocalization.Away (homogeneousSubmodule ι k) p} : (HomogeneousLocalization.awayPrimeMultiplicityValuation (homogeneousSubmodule ι k) hp) z = 1 ↔ IsUnit z
```

In the degree-zero homogeneous localization away from a nonconstant prime
polynomial, valuation one characterizes units.

[Source](../GradedRings/MvPolynomialAway.lean#L166) (line 166).

### MvPolynomial.irreducible_of_awayPrimeMultiplicityValuation_eq_exp_one

```lean
theorem MvPolynomial.irreducible_of_awayPrimeMultiplicityValuation_eq_exp_one {k : Type u_1} {ι : Type u_2} [Field k] {p : MvPolynomial ι k} {d : ℕ} (hp : Prime p) (hpHom : p.IsHomogeneous d) (hd : d ≠ 0) {z : HomogeneousLocalization.Away (homogeneousSubmodule ι k) p} (hzVal : (HomogeneousLocalization.awayPrimeMultiplicityValuation (homogeneousSubmodule ι k) hp) z = WithZero.exp 1) : Irreducible z
```

Denominator order one implies irreducibility in the degree-zero
homogeneous localization away from a nonconstant homogeneous prime.

[Source](../GradedRings/MvPolynomialAway.lean#L222) (line 222).

## Module `GradedRings.Noetherian`

> # Noetherianity and the irrelevant ideal
>
> This file characterizes Noetherian naturally graded commutative rings using
> Noetherianity of the degree-zero piece and finite generation of the irrelevant
> ideal.

[Module source](../GradedRings/Noetherian.lean)

### GradedAlgebra.irrelevant_fg_of_isNoetherianRing

```lean
theorem GradedAlgebra.irrelevant_fg_of_isNoetherianRing {A : Type u} [CommRing A] {σ : Type v} [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] [IsNoetherianRing A] : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.FG
```

A Noetherian naturally graded ring has finitely generated irrelevant
ideal.

[Source](../GradedRings/Noetherian.lean#L28) (line 28).

### GradedAlgebra.isNoetherianRing_of_gradeZero_of_irrelevant_fg

```lean
theorem GradedAlgebra.isNoetherianRing_of_gradeZero_of_irrelevant_fg {A : Type u} [CommRing A] {σ : Type v} [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] [IsNoetherianRing ↥(𝒜 0)] (h : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.FG) : IsNoetherianRing A
```

If the degree-zero piece is Noetherian and the irrelevant ideal is
finitely generated, then the whole naturally graded ring is Noetherian.

[Source](../GradedRings/Noetherian.lean#L34) (line 34).

### GradedAlgebra.isNoetherianRing_iff_gradeZero_and_irrelevant_fg

```lean
theorem GradedAlgebra.isNoetherianRing_iff_gradeZero_and_irrelevant_fg {A : Type u} [CommRing A] {σ : Type v} [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] : IsNoetherianRing A ↔ IsNoetherianRing ↥(𝒜 0) ∧ (HomogeneousIdeal.irrelevant 𝒜).toIdeal.FG
```

A naturally graded commutative ring is Noetherian exactly when its
degree-zero piece is Noetherian and its irrelevant ideal is finitely
generated.

[Source](../GradedRings/Noetherian.lean#L43) (line 43).

## Module `GradedRings.PrimeMultiplicity`

> # Prime-multiplicity valuations
>
> This file packages the multiplicity of a prime element in a domain with
> well-founded divisibility as an integer-valued valuation.  Unlike the
> `ℕ∞`-valued additive valuation `multiplicity_addValuation`, this valuation has
> a group-valued nonzero part and therefore extends across localizations.

[Module source](../GradedRings/PrimeMultiplicity.lean)

### PrimeMultiplicity.valuationDef

```lean
noncomputable def PrimeMultiplicity.valuationDef {R : Type u_1} [CommRing R] (p r : R) : WithZero (Multiplicative ℤ)
```

The multiplicative value attached to prime multiplicity on the original
domain.  A nonzero element `r` is sent to `exp (-multiplicity p r)`.

[Source](../GradedRings/PrimeMultiplicity.lean#L31) (line 31).

### PrimeMultiplicity.valuationDef_zero

```lean
theorem PrimeMultiplicity.valuationDef_zero {R : Type u_1} [CommRing R] (p : R) : valuationDef p 0 = 0
```

No declaration docstring is supplied in this source.

[Source](../GradedRings/PrimeMultiplicity.lean#L39) (line 39).

### PrimeMultiplicity.valuationDef_one

```lean
theorem PrimeMultiplicity.valuationDef_one {R : Type u_1} [CommRing R] [IsDomain R] {p : R} (hp : Prime p) : valuationDef p 1 = 1
```

No declaration docstring is supplied in this source.

[Source](../GradedRings/PrimeMultiplicity.lean#L44) (line 44).

### PrimeMultiplicity.valuationDef_of_ne_zero

```lean
theorem PrimeMultiplicity.valuationDef_of_ne_zero {R : Type u_1} [CommRing R] (p : R) {r : R} (hr : r ≠ 0) : valuationDef p r = WithZero.exp (-↑(multiplicity p r))
```

No declaration docstring is supplied in this source.

[Source](../GradedRings/PrimeMultiplicity.lean#L51) (line 51).

### PrimeMultiplicity.valuationDef_pow

```lean
theorem PrimeMultiplicity.valuationDef_pow {R : Type u_1} [CommRing R] [IsDomain R] {p : R} (hp : Prime p) (n : ℕ) : valuationDef p (p ^ n) = WithZero.exp (-↑n)
```

A prime power has multiplicity equal to its exponent. This is the
simp-normal-form computation rule after `valuation_apply` unfolds the bundled
valuation.

[Source](../GradedRings/PrimeMultiplicity.lean#L56) (line 56).

### PrimeMultiplicity.valuationDef_mul

```lean
theorem PrimeMultiplicity.valuationDef_mul {R : Type u_1} [CommRing R] [IsDomain R] [WfDvdMonoid R] {p : R} (hp : Prime p) (x y : R) : valuationDef p (x * y) = valuationDef p x * valuationDef p y
```

No declaration docstring is supplied in this source.

[Source](../GradedRings/PrimeMultiplicity.lean#L65) (line 65).

### PrimeMultiplicity.min_multiplicity_le_multiplicity_add

```lean
theorem PrimeMultiplicity.min_multiplicity_le_multiplicity_add {R : Type u_1} [CommRing R] [IsDomain R] [WfDvdMonoid R] {p : R} (hp : Prime p) {x y : R} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x + y ≠ 0) : min (multiplicity p x) (multiplicity p y) ≤ multiplicity p (x + y)
```

No declaration docstring is supplied in this source.

[Source](../GradedRings/PrimeMultiplicity.lean#L78) (line 78).

### PrimeMultiplicity.valuationDef_add_le_max

```lean
theorem PrimeMultiplicity.valuationDef_add_le_max {R : Type u_1} [CommRing R] [IsDomain R] [WfDvdMonoid R] {p : R} (hp : Prime p) (x y : R) : valuationDef p (x + y) ≤ max (valuationDef p x) (valuationDef p y)
```

No declaration docstring is supplied in this source.

[Source](../GradedRings/PrimeMultiplicity.lean#L90) (line 90).

### PrimeMultiplicity.valuation

```lean
noncomputable def PrimeMultiplicity.valuation {R : Type u_1} [CommRing R] [IsDomain R] [WfDvdMonoid R] {p : R} (hp : Prime p) : Valuation R (WithZero (Multiplicative ℤ))
```

The integer-valued multiplicative valuation associated to a prime element
in a domain with well-founded divisibility.

[Source](../GradedRings/PrimeMultiplicity.lean#L103) (line 103).

### PrimeMultiplicity.valuation_apply

```lean
theorem PrimeMultiplicity.valuation_apply {R : Type u_1} [CommRing R] [IsDomain R] [WfDvdMonoid R] {p : R} (hp : Prime p) (r : R) : (valuation hp) r = valuationDef p r
```

No declaration docstring is supplied in this source.

[Source](../GradedRings/PrimeMultiplicity.lean#L112) (line 112).

### PrimeMultiplicity.valuation_apply_of_ne_zero

```lean
theorem PrimeMultiplicity.valuation_apply_of_ne_zero {R : Type u_1} [CommRing R] [IsDomain R] [WfDvdMonoid R] {p : R} (hp : Prime p) {r : R} (hr : r ≠ 0) : (valuation hp) r = WithZero.exp (-↑(multiplicity p r))
```

No declaration docstring is supplied in this source.

[Source](../GradedRings/PrimeMultiplicity.lean#L117) (line 117).

### PrimeMultiplicity.valuation_apply_pow

```lean
theorem PrimeMultiplicity.valuation_apply_pow {R : Type u_1} [CommRing R] [IsDomain R] [WfDvdMonoid R] {p : R} (hp : Prime p) (n : ℕ) : (valuation hp) (p ^ n) = WithZero.exp (-↑n)
```

No declaration docstring is supplied in this source.

[Source](../GradedRings/PrimeMultiplicity.lean#L121) (line 121).

### PrimeMultiplicity.valuation_ne_zero

```lean
theorem PrimeMultiplicity.valuation_ne_zero {R : Type u_1} [CommRing R] [IsDomain R] [WfDvdMonoid R] {p : R} (hp : Prime p) {r : R} (hr : r ≠ 0) : (valuation hp) r ≠ 0
```

No declaration docstring is supplied in this source.

[Source](../GradedRings/PrimeMultiplicity.lean#L126) (line 126).

### PrimeMultiplicity.localizationValuation

```lean
noncomputable def PrimeMultiplicity.localizationValuation {R : Type u_1} [CommRing R] [IsDomain R] [WfDvdMonoid R] {p : R} {S : Submonoid R} {B : Type u_2} [CommRing B] [Algebra R B] [IsLocalization S B] (hp : Prime p) (hS : S ≤ nonZeroDivisors R) : Valuation B (WithZero (Multiplicative ℤ))
```

Extend prime multiplicity to a localization whose denominators are
non-zero-divisors.

[Source](../GradedRings/PrimeMultiplicity.lean#L134) (line 134).

### PrimeMultiplicity.localizationValuation_mk'

```lean
theorem PrimeMultiplicity.localizationValuation_mk' {R : Type u_1} [CommRing R] [IsDomain R] [WfDvdMonoid R] {p : R} {S : Submonoid R} {B : Type u_2} [CommRing B] [Algebra R B] [IsLocalization S B] (hp : Prime p) (hS : S ≤ nonZeroDivisors R) (x : R) (y : ↥S) : (localizationValuation hp hS) (IsLocalization.mk' B x y) = (valuation hp) x * ((valuation hp) ↑y)⁻¹
```

No declaration docstring is supplied in this source.

[Source](../GradedRings/PrimeMultiplicity.lean#L144) (line 144).

### PrimeMultiplicity.powers_le_nonZeroDivisors

```lean
theorem PrimeMultiplicity.powers_le_nonZeroDivisors {R : Type u_1} [CommRing R] [IsDomain R] {p : R} (hp : Prime p) : Submonoid.powers p ≤ nonZeroDivisors R
```

No declaration docstring is supplied in this source.

[Source](../GradedRings/PrimeMultiplicity.lean#L153) (line 153).

### PrimeMultiplicity.awayValuation

```lean
noncomputable def PrimeMultiplicity.awayValuation {R : Type u_1} [CommRing R] [IsDomain R] [WfDvdMonoid R] {p : R} (hp : Prime p) {B : Type u_3} [CommRing B] [Algebra R B] [IsLocalization.Away p B] : Valuation B (WithZero (Multiplicative ℤ))
```

The prime-multiplicity valuation on a localization away from the prime.

[Source](../GradedRings/PrimeMultiplicity.lean#L159) (line 159).

### PrimeMultiplicity.awayValuation_mk'

```lean
theorem PrimeMultiplicity.awayValuation_mk' {R : Type u_1} [CommRing R] [IsDomain R] [WfDvdMonoid R] {p : R} (hp : Prime p) {B : Type u_3} [CommRing B] [Algebra R B] [IsLocalization.Away p B] (x : R) (y : ↥(Submonoid.powers p)) : (awayValuation hp) (IsLocalization.mk' B x y) = (valuation hp) x * ((valuation hp) ↑y)⁻¹
```

No declaration docstring is supplied in this source.

[Source](../GradedRings/PrimeMultiplicity.lean#L164) (line 164).

### PrimeMultiplicity.awayValuation_mk_pow_of_ne_zero

```lean
theorem PrimeMultiplicity.awayValuation_mk_pow_of_ne_zero {R : Type u_1} [CommRing R] [IsDomain R] [WfDvdMonoid R] {p : R} (hp : Prime p) {B : Type u_3} [CommRing B] [Algebra R B] [IsLocalization.Away p B] (x : R) (hx : x ≠ 0) (n : ℕ) : (awayValuation hp) (IsLocalization.mk' B x ⟨p ^ n, ⋯⟩) = WithZero.exp (↑n - ↑(multiplicity p x))
```

No declaration docstring is supplied in this source.

[Source](../GradedRings/PrimeMultiplicity.lean#L172) (line 172).

## Module `GradedRings.Quotient`

> # Quotients of graded rings
>
> This file equips the quotient of a commutative graded ring by a homogeneous
> ideal with the grading whose degree-`i` component is the image of the original
> degree-`i` component.
>
> Public data definitions retain their ordinary computational interface. The two
> private construction helpers stay private: their necessary bodies are inlined
> at exposed use sites, with private equalities to the original constructions.

[Module source](../GradedRings/Quotient.lean)

### Ideal.Quotient.gradedComponent

```lean
def Ideal.Quotient.gradedComponent {A : Type u} [CommRing A] {ι : Type v} {σ : Type w} [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ι → σ) (I : Ideal A) (i : ι) : AddSubgroup (A ⧸ I)
```

The degree-`i` component of the quotient grading is the image of the
original degree-`i` component under the quotient map.

[Source](../GradedRings/Quotient.lean#L43) (line 43).

### Ideal.Quotient.gradedRingHom

```lean
def Ideal.Quotient.gradedRingHom {A : Type u} [CommRing A] {ι : Type v} {σ : Type w} [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ι → σ) (I : Ideal A) : 𝒜 →+*ᵍ gradedComponent 𝒜 I
```

The quotient map as a graded ring homomorphism for the image grading on the quotient.

[Source](../GradedRings/Quotient.lean#L58) (line 58).

### Ideal.Quotient.gradedRingHom_apply

```lean
theorem Ideal.Quotient.gradedRingHom_apply {A : Type u} [CommRing A] {ι : Type v} {σ : Type w} [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ι → σ) (I : Ideal A) (x : A) : (gradedRingHom 𝒜 I) x = (mk I) x
```

No declaration docstring is supplied in this source.

[Source](../GradedRings/Quotient.lean#L64) (line 64).

### Ideal.Quotient.gradedRingHom_toRingHom

```lean
theorem Ideal.Quotient.gradedRingHom_toRingHom {A : Type u} [CommRing A] {ι : Type v} {σ : Type w} [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ι → σ) (I : Ideal A) : ↑(gradedRingHom 𝒜 I) = mk I
```

No declaration docstring is supplied in this source.

[Source](../GradedRings/Quotient.lean#L69) (line 69).

### Ideal.Quotient.gradedRingHom_surjective

```lean
theorem Ideal.Quotient.gradedRingHom_surjective {A : Type u} [CommRing A] {ι : Type v} {σ : Type w} [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ι → σ) (I : Ideal A) : Function.Surjective ⇑(gradedRingHom 𝒜 I)
```

The graded quotient map is surjective on the underlying rings.

[Source](../GradedRings/Quotient.lean#L74) (line 74).

### Ideal.Quotient.gradedComponentGradedMonoid

```lean
instance Ideal.Quotient.gradedComponentGradedMonoid {A : Type u} [CommRing A] {ι : Type v} [DecidableEq ι] [AddMonoid ι] {σ : Type w} [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ι → σ) [GradedRing 𝒜] (I : Ideal A) : SetLike.GradedMonoid (gradedComponent 𝒜 I)
```

The image components of a quotient are closed under graded multiplication.

[Source](../GradedRings/Quotient.lean#L78) (line 78).

### Ideal.Quotient.gradedComponentMap

```lean
def Ideal.Quotient.gradedComponentMap {A : Type u} [CommRing A] {ι : Type v} {σ : Type w} [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ι → σ) (I : Ideal A) (i : ι) : ↥(𝒜 i) →+ ↥(gradedComponent 𝒜 I i)
```

The additive map from an original graded component to its image in the quotient.

[Source](../GradedRings/Quotient.lean#L93) (line 93).

### Ideal.Quotient.gradedDecomposePre

```lean
def Ideal.Quotient.gradedDecomposePre {A : Type u} [CommRing A] {ι : Type v} [DecidableEq ι] [AddMonoid ι] {σ : Type w} [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ι → σ) [GradedRing 𝒜] (I : Ideal A) : A →+ DirectSum ι fun (i : ι) => ↥(gradedComponent 𝒜 I i)
```

Decompose an element of the original ring and map each component to the quotient.

[Source](../GradedRings/Quotient.lean#L99) (line 99).

### Ideal.Quotient.gradedDecompose

```lean
def Ideal.Quotient.gradedDecompose {A : Type u} [CommRing A] {ι : Type v} [DecidableEq ι] [AddMonoid ι] {σ : Type w} [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ι → σ) [GradedRing 𝒜] (I : Ideal A) (hI : IsHomogeneous 𝒜 I) : A ⧸ I →+ DirectSum ι fun (i : ι) => ↥(gradedComponent 𝒜 I i)
```

Decompose a quotient class into the images of its homogeneous components.

[Source](../GradedRings/Quotient.lean#L115) (line 115).

### Ideal.Quotient.gradedDecompose_mk

```lean
theorem Ideal.Quotient.gradedDecompose_mk {A : Type u} [CommRing A] {ι : Type v} [DecidableEq ι] [AddMonoid ι] {σ : Type w} [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ι → σ) [GradedRing 𝒜] (I : Ideal A) (hI : IsHomogeneous 𝒜 I) (x : A) : (gradedDecompose 𝒜 I hI) ((mk I) x) = (gradedDecomposePre 𝒜 I) x
```

No declaration docstring is supplied in this source.

[Source](../GradedRings/Quotient.lean#L135) (line 135).

### Ideal.Quotient.coe_gradedDecomposePre

```lean
theorem Ideal.Quotient.coe_gradedDecomposePre {A : Type u} [CommRing A] {ι : Type v} [DecidableEq ι] [AddMonoid ι] {σ : Type w} [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ι → σ) [GradedRing 𝒜] (I : Ideal A) (x : A) : (DirectSum.coeAddMonoidHom (gradedComponent 𝒜 I)) ((gradedDecomposePre 𝒜 I) x) = (mk I) x
```

No declaration docstring is supplied in this source.

[Source](../GradedRings/Quotient.lean#L140) (line 140).

### Ideal.Quotient.gradedDecompose_leftInverse

```lean
theorem Ideal.Quotient.gradedDecompose_leftInverse {A : Type u} [CommRing A] {ι : Type v} [DecidableEq ι] [AddMonoid ι] {σ : Type w} [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ι → σ) [GradedRing 𝒜] (I : Ideal A) (hI : IsHomogeneous 𝒜 I) : Function.LeftInverse ⇑(DirectSum.coeAddMonoidHom (gradedComponent 𝒜 I)) ⇑(gradedDecompose 𝒜 I hI)
```

Recombining the quotient decomposition gives the original quotient class.

[Source](../GradedRings/Quotient.lean#L152) (line 152).

### Ideal.Quotient.gradedDecompose_rightInverse

```lean
theorem Ideal.Quotient.gradedDecompose_rightInverse {A : Type u} [CommRing A] {ι : Type v} [DecidableEq ι] [AddMonoid ι] {σ : Type w} [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ι → σ) [GradedRing 𝒜] (I : Ideal A) (hI : IsHomogeneous 𝒜 I) : Function.RightInverse ⇑(DirectSum.coeAddMonoidHom (gradedComponent 𝒜 I)) ⇑(gradedDecompose 𝒜 I hI)
```

Decomposing a direct sum of quotient components gives the original sum.

[Source](../GradedRings/Quotient.lean#L160) (line 160).

### Ideal.Quotient.gradedDecomposition

```lean
def Ideal.Quotient.gradedDecomposition {A : Type u} [CommRing A] {ι : Type v} [DecidableEq ι] [AddMonoid ι] {σ : Type w} [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ι → σ) [GradedRing 𝒜] (I : Ideal A) (hI : IsHomogeneous 𝒜 I) : DirectSum.Decomposition (gradedComponent 𝒜 I)
```

The natural direct-sum decomposition of a quotient by a homogeneous ideal.

[Source](../GradedRings/Quotient.lean#L181) (line 181).

### Ideal.Quotient.gradedRing

```lean
def Ideal.Quotient.gradedRing {A : Type u} [CommRing A] {ι : Type v} [DecidableEq ι] [AddMonoid ι] {σ : Type w} [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ι → σ) [GradedRing 𝒜] (I : Ideal A) (hI : IsHomogeneous 𝒜 I) : GradedRing (gradedComponent 𝒜 I)
```

The natural grading on the quotient by a homogeneous ideal.

[Source](../GradedRings/Quotient.lean#L189) (line 189).

## Module `GradedRings.SymmetricAlgebra`

> # The natural grading on a symmetric algebra
>
> This file equips `SymmetricAlgebra R M` with its basis-free grading by total degree.  The
> degree-`n` component is the `n`-th power of the range of the canonical linear map
> `SymmetricAlgebra.ι R M`.

[Module source](../GradedRings/SymmetricAlgebra.lean)

### SymmetricAlgebra.homogeneousSubmodule

```lean
abbrev SymmetricAlgebra.homogeneousSubmodule {R : Type u} {M : Type v} [CommSemiring R] [AddCommMonoid M] [Module R M] (n : ℕ) : Submodule R (SymmetricAlgebra R M)
```

The degree-`n` part of a symmetric algebra: the `n`-th power of the submodule spanned by
its canonical generators.

[Source](../GradedRings/SymmetricAlgebra.lean#L30) (line 30).

### SymmetricAlgebra.GradedAlgebra.ι

```lean
def SymmetricAlgebra.GradedAlgebra.ι (R : Type u) (M : Type v) [CommSemiring R] [AddCommMonoid M] [Module R M] : M →ₗ[R] DirectSum ℕ fun (n : ℕ) => ↥(homogeneousSubmodule n)
```

A version of `SymmetricAlgebra.ι` with codomain the direct sum of the natural degree
components.

[Source](../GradedRings/SymmetricAlgebra.lean#L37) (line 37).

### SymmetricAlgebra.GradedAlgebra.ι_apply

```lean
theorem SymmetricAlgebra.GradedAlgebra.ι_apply (R : Type u) (M : Type v) [CommSemiring R] [AddCommMonoid M] [Module R M] (m : M) : (ι R M) m = (DirectSum.of (fun (n : ℕ) => ↥(homogeneousSubmodule n)) 1) ⟨(SymmetricAlgebra.ι R M) m, ⋯⟩
```

No declaration docstring is supplied in this source.

[Source](../GradedRings/SymmetricAlgebra.lean#L48) (line 48).

### SymmetricAlgebra.gradedAlgebra

```lean
instance SymmetricAlgebra.gradedAlgebra {R : Type u} {M : Type v} [CommSemiring R] [AddCommMonoid M] [Module R M] : GradedAlgebra homogeneousSubmodule
```

The symmetric algebra is naturally graded by powers of the range of its canonical
degree-one generators.

[Source](../GradedRings/SymmetricAlgebra.lean#L59) (line 59).

### SymmetricAlgebra.map

```lean
def SymmetricAlgebra.map {R : Type u} {M : Type v} [CommSemiring R] [AddCommMonoid M] [Module R M] {N : Type w} [AddCommMonoid N] [Module R N] (f : M →ₗ[R] N) : SymmetricAlgebra R M →ₐ[R] SymmetricAlgebra R N
```

The algebra map on symmetric algebras induced by a linear map.

[Source](../GradedRings/SymmetricAlgebra.lean#L94) (line 94).

### SymmetricAlgebra.map_ι_apply

```lean
theorem SymmetricAlgebra.map_ι_apply {R : Type u} {M : Type v} [CommSemiring R] [AddCommMonoid M] [Module R M] {N : Type w} [AddCommMonoid N] [Module R N] (f : M →ₗ[R] N) (m : M) : (map f) ((ι R M) m) = (ι R N) (f m)
```

No declaration docstring is supplied in this source.

[Source](../GradedRings/SymmetricAlgebra.lean#L99) (line 99).

### SymmetricAlgebra.map_id

```lean
theorem SymmetricAlgebra.map_id {R : Type u} {M : Type v} [CommSemiring R] [AddCommMonoid M] [Module R M] : map LinearMap.id = AlgHom.id R (SymmetricAlgebra R M)
```

No declaration docstring is supplied in this source.

[Source](../GradedRings/SymmetricAlgebra.lean#L104) (line 104).

### SymmetricAlgebra.map_comp

```lean
theorem SymmetricAlgebra.map_comp {R : Type u} {M : Type v} [CommSemiring R] [AddCommMonoid M] [Module R M] {N : Type w} [AddCommMonoid N] [Module R N] {P : Type u_1} [AddCommMonoid P] [Module R P] (g : N →ₗ[R] P) (f : M →ₗ[R] N) : map (g ∘ₗ f) = (map g).comp (map f)
```

No declaration docstring is supplied in this source.

[Source](../GradedRings/SymmetricAlgebra.lean#L110) (line 110).

### SymmetricAlgebra.map_mem_homogeneousSubmodule

```lean
theorem SymmetricAlgebra.map_mem_homogeneousSubmodule {R : Type u} {M : Type v} [CommSemiring R] [AddCommMonoid M] [Module R M] {N : Type w} [AddCommMonoid N] [Module R N] (f : M →ₗ[R] N) {n : ℕ} {x : SymmetricAlgebra R M} (hx : x ∈ homogeneousSubmodule n) : (map f) x ∈ homogeneousSubmodule n
```

A linear map sends every homogeneous component of the source symmetric algebra into the
component of the same degree in the target.

[Source](../GradedRings/SymmetricAlgebra.lean#L118) (line 118).

### SymmetricAlgebra.gradedMap

```lean
def SymmetricAlgebra.gradedMap {R : Type u} {M : Type v} [CommSemiring R] [AddCommMonoid M] [Module R M] {N : Type w} [AddCommMonoid N] [Module R N] (f : M →ₗ[R] N) : homogeneousSubmodule →ₐᵍ[R] homogeneousSubmodule
```

The functorial map on symmetric algebras, bundled as a degree-preserving algebra map.

[Source](../GradedRings/SymmetricAlgebra.lean#L132) (line 132).

### SymmetricAlgebra.gradedMap_apply

```lean
theorem SymmetricAlgebra.gradedMap_apply {R : Type u} {M : Type v} [CommSemiring R] [AddCommMonoid M] [Module R M] {N : Type w} [AddCommMonoid N] [Module R N] (f : M →ₗ[R] N) (x : SymmetricAlgebra R M) : (gradedMap f) x = (map f) x
```

No declaration docstring is supplied in this source.

[Source](../GradedRings/SymmetricAlgebra.lean#L140) (line 140).

### SymmetricAlgebra.congr

```lean
def SymmetricAlgebra.congr {R : Type u} {M : Type v} [CommSemiring R] [AddCommMonoid M] [Module R M] {N : Type w} [AddCommMonoid N] [Module R N] (e : M ≃ₗ[R] N) : SymmetricAlgebra R M ≃ₐ[R] SymmetricAlgebra R N
```

A linear equivalence induces an algebra equivalence of symmetric algebras.

[Source](../GradedRings/SymmetricAlgebra.lean#L145) (line 145).

### SymmetricAlgebra.congr_apply

```lean
theorem SymmetricAlgebra.congr_apply {R : Type u} {M : Type v} [CommSemiring R] [AddCommMonoid M] [Module R M] {N : Type w} [AddCommMonoid N] [Module R N] (e : M ≃ₗ[R] N) (x : SymmetricAlgebra R M) : (congr e) x = (map ↑e) x
```

No declaration docstring is supplied in this source.

[Source](../GradedRings/SymmetricAlgebra.lean#L156) (line 156).

### SymmetricAlgebra.congr_symm_apply

```lean
theorem SymmetricAlgebra.congr_symm_apply {R : Type u} {M : Type v} [CommSemiring R] [AddCommMonoid M] [Module R M] {N : Type w} [AddCommMonoid N] [Module R N] (e : M ≃ₗ[R] N) (x : SymmetricAlgebra R N) : (congr e).symm x = (map ↑e.symm) x
```

No declaration docstring is supplied in this source.

[Source](../GradedRings/SymmetricAlgebra.lean#L161) (line 161).

### SymmetricAlgebra.equivMvPolynomial_mem_homogeneousSubmodule

```lean
theorem SymmetricAlgebra.equivMvPolynomial_mem_homogeneousSubmodule {R : Type u} {M : Type v} [CommSemiring R] [AddCommMonoid M] [Module R M] {I : Type w} (b : Module.Basis I R M) {n : ℕ} {x : SymmetricAlgebra R M} (hx : x ∈ homogeneousSubmodule n) : (equivMvPolynomial b) x ∈ MvPolynomial.homogeneousSubmodule I R n
```

A basis presentation of a symmetric algebra preserves total degree.

[Source](../GradedRings/SymmetricAlgebra.lean#L176) (line 176).

### SymmetricAlgebra.equivMvPolynomial_symm_mem_homogeneousSubmodule

```lean
theorem SymmetricAlgebra.equivMvPolynomial_symm_mem_homogeneousSubmodule {R : Type u} {M : Type v} [CommSemiring R] [AddCommMonoid M] [Module R M] {I : Type w} (b : Module.Basis I R M) {n : ℕ} {p : MvPolynomial I R} (hp : p ∈ MvPolynomial.homogeneousSubmodule I R n) : (equivMvPolynomial b).symm p ∈ homogeneousSubmodule n
```

The inverse of a basis presentation of a symmetric algebra also preserves total degree.

[Source](../GradedRings/SymmetricAlgebra.lean#L208) (line 208).

### SymmetricAlgebra.equivMvPolynomialGradedHom

```lean
noncomputable def SymmetricAlgebra.equivMvPolynomialGradedHom {R : Type u} {M : Type v} [CommSemiring R] [AddCommMonoid M] [Module R M] {I : Type w} (b : Module.Basis I R M) : homogeneousSubmodule →ₐᵍ[R] MvPolynomial.homogeneousSubmodule I R
```

A basis presentation of a symmetric algebra, bundled as a degree-preserving algebra map.

[Source](../GradedRings/SymmetricAlgebra.lean#L232) (line 232).

### SymmetricAlgebra.equivMvPolynomialGradedHom_apply

```lean
theorem SymmetricAlgebra.equivMvPolynomialGradedHom_apply {R : Type u} {M : Type v} [CommSemiring R] [AddCommMonoid M] [Module R M] {I : Type w} (b : Module.Basis I R M) (x : SymmetricAlgebra R M) : (equivMvPolynomialGradedHom b) x = (equivMvPolynomial b) x
```

No declaration docstring is supplied in this source.

[Source](../GradedRings/SymmetricAlgebra.lean#L240) (line 240).

### SymmetricAlgebra.equivMvPolynomialSymmGradedHom

```lean
noncomputable def SymmetricAlgebra.equivMvPolynomialSymmGradedHom {R : Type u} {M : Type v} [CommSemiring R] [AddCommMonoid M] [Module R M] {I : Type w} (b : Module.Basis I R M) : MvPolynomial.homogeneousSubmodule I R →ₐᵍ[R] homogeneousSubmodule
```

The inverse basis presentation, bundled as a degree-preserving algebra map.

[Source](../GradedRings/SymmetricAlgebra.lean#L246) (line 246).

### SymmetricAlgebra.equivMvPolynomialSymmGradedHom_apply

```lean
theorem SymmetricAlgebra.equivMvPolynomialSymmGradedHom_apply {R : Type u} {M : Type v} [CommSemiring R] [AddCommMonoid M] [Module R M] {I : Type w} (b : Module.Basis I R M) (p : MvPolynomial I R) : (equivMvPolynomialSymmGradedHom b) p = (equivMvPolynomial b).symm p
```

No declaration docstring is supplied in this source.

[Source](../GradedRings/SymmetricAlgebra.lean#L254) (line 254).

## Module `FinitenessAndPrimes`

> # Finite generation and contraction of homogeneous primes
>
> For a natural-number grading, finite generation of the irrelevant ideal supplies
> finite type over degree zero and, with a Noetherian degree-zero ring, Noetherianity.
> The separate integer-graded example needs a positive-degree homogeneous unit;
> the inverse to prime contraction uses radical extension, not plain extension.

[Module source](../examples/FinitenessAndPrimes.lean)

## Module `Multiplicity`

> # Prime powers and denominator order
>
> Prime multiplicity gives a multiplicative integer-valued valuation. The
> polynomial application uses a nonconstant homogeneous prime over a field.
> Its coordinate type need not be finite. These examples use the aggregate import.

[Module source](../examples/Multiplicity.lean)

## Module `QuotientLocalization`

> # Quotient and degree-zero localization examples
>
> The quotient example recombines the homogeneous decomposition. The localization
> example identifies mathlib's equal-degree fractions with the zero component of
> the full localization. Neither construction requires a domain.

[Module source](../examples/QuotientLocalization.lean)

## Module `Symmetric`

> # Basis-free functoriality and polynomial coordinates
>
> These examples work over a commutative semiring and arbitrary modules. A basis
> is required only for the coordinate presentation, not for the grading or map.

[Module source](../examples/Symmetric.lean)

## Module `Axioms`

> No module docstring is supplied in this source; see the linked module.

[Module source](../test/Axioms.lean)

## Module `FiniteType`

> No module docstring is supplied in this source; see the linked module.

[Module source](../test/FiniteType.lean)

## Module `HomogeneousPrime`

> No module docstring is supplied in this source; see the linked module.

[Module source](../test/HomogeneousPrime.lean)

## Module `InterfaceClient`

> No module docstring is supplied in this source; see the linked module.

[Module source](../test/InterfaceClient.lean)

## Module `Localization`

> No module docstring is supplied in this source; see the linked module.

[Module source](../test/Localization.lean)

## Module `LocalizationInterface`

> # Ordinary direct-import reduction checks for graded localization

[Module source](../test/LocalizationInterface.lean)

## Module `LocalizationRootInterface`

> # Ordinary aggregate-import reduction checks for graded localization

[Module source](../test/LocalizationRootInterface.lean)

## Module `Noetherian`

> No module docstring is supplied in this source; see the linked module.

[Module source](../test/Noetherian.lean)

## Module `PrimeInterface`

> # Ordinary native direct-import prime-multiplicity construction checks

[Module source](../test/PrimeInterface.lean)

## Module `PrimeRootInterface`

> # Ordinary native aggregate-import prime-multiplicity construction checks

[Module source](../test/PrimeRootInterface.lean)

## Module `Quotient`

> # Private generic and zero-ring checks of the quotient grading

[Module source](../test/Quotient.lean)

## Module `QuotientInterface`

> # Ordinary direct-import reduction checks for the quotient grading

[Module source](../test/QuotientInterface.lean)

## Module `QuotientRootInterface`

> # Ordinary aggregate-import reduction checks for the quotient grading

[Module source](../test/QuotientRootInterface.lean)

## Module `RootClient`

> No module docstring is supplied in this source; see the linked module.

[Module source](../test/RootClient.lean)
