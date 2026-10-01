# Finite positive Veronese inclusions

Import `GradedRings.VeroneseFinite` (or the aggregate `GradedRings`) to use
`GradedRing.Veronese.inclusion_finite`. For `𝒮 : ℕ → σ` grading a commutative ring
`S`, its public signature is:

```lean
theorem GradedRing.Veronese.inclusion_finite
    {S : Type*} [CommRing S] {σ : Type*} [SetLike σ S]
    [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮]
    (n : ℕ) (hn : 0 < n) [Algebra.FiniteType (𝒮 0) S] :
    (GradedRing.Veronese.inclusion 𝒮 n).Finite
```

Here `𝒮 0` is the **whole original degree-zero ring**, not the zero component
of the selected ring. `RingHom.Finite` uses the **actual inclusion's**
`RingHom.toAlgebra` module structure: `S` is finite as a module over the
external selected-component ring `⨁ j : ℕ, 𝒮 (n * j)`. This is distinct from
[`finiteType_of_finiteType`](VeroneseFiniteType.md), which makes the selected
ring finite type over its *own* degree-zero ring; it is also distinct from
finite degree-one generation at only some selected index.

## Proof and boundaries

Native graded finite-type extraction gives a finite family of homogeneous
algebra generators over `𝒮 0`. For a generator `x` of old degree `d`, its
`n`th power belongs to `𝒮 (n * d)`, so `exists_component` lifts this power to
the selected ring. Its image is integral over the new base, hence `x` itself
is integral because `n > 0`. Each old degree-zero coefficient likewise lifts
through the new degree-zero component. An explicit induction on the old
adjoin proves that the same family generates over the selected ring; no scalar
tower or definitional identification of the two bases is assumed. Native
finite integral adjoin makes the top submodule finitely generated.

The theorem allows empty homogeneous generating families, arbitrary and
nonconstant degree-zero coefficients, `n = 1`, zero rings and nilpotents;
it assumes neither Noetherianity, a domain, a field nor generation in degree
one. The power-lifting step applies to **homogeneous generators**, not
inhomogeneous elements: an arbitrary inhomogeneous `x` need not have `x ^ n`
in the selected image. The theorem requires `0 < n`; the degree-zero
selection need not give a finite inclusion (consider `ℤ[X]` over `ℤ`).
This finite-inclusion module itself supplies no residue-class projection;
the separate [whole-Veronese residue guide](VeroneseResidue.md) describes
that projection and its finite image. This module supplies no index-zero
result or geometric Proj application.

## Build and provenance

From the Graded Rings project root with `leanprover/lean4:v4.34.0-rc2` and
the committed `lake-manifest.json` (mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5`), fetch the matching mathlib
cache **successfully before any build**. Do not fall back to a full mathlib
source rebuild if the cache fetch fails; diagnose and report the blocker.
Both Lean modules set `warningAsError true`. Focused and full commands are:

```sh
lake exe cache get
lake --wfail build GradedRings.VeroneseFinite
lake --wfail build VeroneseFinite
lake --wfail build GradedRings GradedRingsTests GradedRingsExamples
```

The [direct client](../test/VeroneseFinite.lean) ordinary-imports the producer
and tests generic use, the inclusion-induced module structure, empty generation,
whole-zero and zero-ring boundaries, `n = 1`, and nilpotent inputs. The
[aggregate client](../test/RootClient.lean) checks public re-export.
The original proof, direct client and guide were written by Formal Frontier
agents; another contributor adapted their imports and guide for this library.
Atlas contributed an earlier uncompiled applicability assessment, not the
Lean proof. The source-specific correspondence of this theorem requires a
separate decision; see [provenance and credits](PROVENANCE.md).
