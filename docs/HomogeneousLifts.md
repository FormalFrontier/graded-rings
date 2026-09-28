# Homogeneous polynomial lifts

Import `GradedRings.HomogeneousLifts` for the four public declarations below, or
`GradedRings` for the aggregate API. The producer imports mathlib only; its
results do not require another Formal Frontier library or any source-research
repository.

## Componentwise surjectivity

`GradedRingHom.surjective_gradedAddHom 𝒜 ℬ f hf i` says that an ambient-surjective
graded semiring map `f : 𝒜 →+*ᵍ ℬ` induces a surjective additive map on the
**entire** homogeneous component of degree `i`. The source and target can be
graded semirings over a common additive index monoid with decidable equality,
with the `SetLike`, `AddSubmonoidClass`, and `GradedRing` instances in the Lean
signature. It does not assume that the chosen target element already has a
homogeneous ambient preimage. One can lift it in the whole ring and project
that preimage to degree `i` with `DirectSum.decompose`.

## Evaluation and lifts

Let `S` be an arbitrary commutative ring with a nonnegative grading
`𝒮 : ℕ → σ`, `SetLike σ S`, `AddSubgroupClass σ S`, and `GradedRing 𝒮`.
Coefficients of the polynomial ring are the **actual degree-zero subtype**
`𝒮 0`; its algebra map to `S` is inclusion. Variables are indexed by **every
element** of the degree-one subtype `𝒮 1` and evaluate to their underlying
elements in `S`.

- `MvPolynomial.isHomogeneous_aeval_degreeOne 𝒮 hp` proves that evaluating a
  polynomial homogeneous of degree `m` lands in `𝒮 m`.
- `MvPolynomial.aevalDegreeOneGradedHom 𝒮` packages this evaluation as a graded
  homomorphism from the naturally graded multivariate polynomial ring to `𝒮`.
- `MvPolynomial.exists_isHomogeneous_aeval 𝒮 hgen hs` gives a **homogeneous**
  polynomial preimage of `s` in degree `m`, under exactly these hypotheses:

```lean
hgen : Algebra.adjoin (𝒮 0) (𝒮 1 : Set S) = ⊤
hs : s ∈ 𝒮 m
```

Its conclusion supplies `p : MvPolynomial (𝒮 1) (𝒮 0)` with
`p.IsHomogeneous m` and
`MvPolynomial.aeval (fun a : 𝒮 1 => (a : S)) p = s`.
The hypothesis is algebra generation of the whole ring over degree zero, **not**
homogeneous surjectivity assumed in advance. The polynomial evaluation range
is the stated adjoin; the componentwise-surjectivity theorem then extracts the
homogeneous lift. Degree `m = 0` is included. There is no finite generating-set,
finite-type, field, domain, reducedness, nontriviality, or Noetherian assumption.
The theorem does not claim that `S` is itself a polynomial ring.

The [direct client](../test/HomogeneousLifts.lean) checks a graded-map
application, arbitrary-degree lifts, constants in degree zero, and free
multivariate polynomials over an arbitrary commutative ring and variable type.
For the latter it **proves** the adjoin hypothesis by polynomial induction;
it does not silently assume it. Its four anonymous examples are elaborated
usage checks, not additional named public or persisted client declarations.
The [aggregate-import client](../test/RootClient.lean) also applies the lift
with precisely its stated hypotheses.

## Reproduction and limits

The repository pins Lean `v4.34.0-rc2`, mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5` and a resolved Lake
manifest. Fetch the matching mathlib cache before any build:

```sh
lake exe cache get
lake --wfail build GradedRings GradedRingsTests GradedRingsExamples
```

The exact destination code at `99df5f2effcf2ebe52a91d94cbd15c3090401cca`
passed native run 712 (all three targets and a complete private/generated-
inclusive standard-axiom audit), received independent code approval 4476,
and was accepted and protected-integrated by the maintainer on 2026-09-28 at
09:12:13 UTC. Those code results are not review, acceptance or verified
publication of the subsequent documentary release candidate. Neither this
degree-preserving lift nor the
[selected-component ring](Veronese.md) proves degree-one generation of a
positive Veronese subring, coefficient regrouping, a Proj equivalence, or
source coverage.
