# Coherent tails and Veronese ring equivalences

Import `GradedRings.CoherentTailVeronese` directly, or import `GradedRings` for
the aggregate API. In
`GradedRing.Veronese.CoherentTail`, `TailEquiv 𝒜 ℬ N` packages data for arbitrary
natural-number gradings of two commutative rings (with `SetLike`,
`AddSubgroupClass` and `GradedRing` instances):

* `positive : 0 < N`;
* `zero : 𝒜 0 ≃+* ℬ 0`, an equivalence of the **actual** degree-zero rings;
* `high d hd : 𝒜 d ≃+ ℬ d` for each `hd : N ≤ d`;
* `coeff`, compatibility with multiplication by an element of `𝒜 0` on the
  left, using the actual graded-ring products;
* `product`, compatibility of products of elements in degrees `d,k ≥ N`.

For `hNn : N ≤ n`, `E.selectedRingEquiv n hNn` identifies the **entire**
published `GradedRing.Veronese.VeroneseRing 𝒜 n` with
`GradedRing.Veronese.VeroneseRing ℬ n`. Its map sends the zeroth summand through
`zero` and the positive `j`th summand through `high (n * j)`. The API includes
`selectedRingHom_of`, `selectedRingHomSymm_of`, both corresponding
`selectedRingEquiv` summand evaluations, native `selectedGradedHom` and
`selectedGradedHomSymm`, and the two graded inverse-composition laws. With
`hn : 0 < n`, `selected_zero n hNn hn` states the exact identity of ring homs

```lean
(zeroRingEquiv ℬ n hn).toRingHom.comp
    (GradedRingHom.gradedZeroRingHom (E.selectedGradedHom n hNn)) =
  E.zero.toRingHom.comp (zeroRingEquiv 𝒜 n hn).toRingHom
```

The lift uses `DirectSum.toSemiring`, `DirectSum.toSemiring_of` and
`DirectSum.ringHom_ext`; degree preservation uses the published `component` and
`mem_component_iff`. The inverse ring hom is derived from the component
equivalences, not from separately assumed inverse multiplication laws. The
coefficient law for right multiplication follows from commutativity.
The component rings and grading carriers can inhabit separate universes.

The [direct ordinary-import client](../test/CoherentTailVeronese.lean) imports
the producer normally. One client takes `ℤ[t]` and the *inherited graded subring*
whose degree-one projection is zero. Its degree-zero and degree-at-least-two
components are identified with those of `ℤ[t]`; `missingLinearSelected`
constructs their `n = N = 2` equivalence. `missingLinear_no_extension` proves
that **no graded ring homomorphism** extending these high-component identities
exists: the image of `t` must vanish, while that of `t²` must not. This does not
assert equality with a generated-subring presentation. Further clients verify
the nonidentity degree-zero swap on `(ZMod 4 × ZMod 4)[t]`, its exact zero-component
square and both graded inverse laws, and an identity-tail client for `ZMod 1`
without `Nontrivial` assumptions.

From the graded-rings root, with pinned Lean `v4.34.0-rc2`, mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5` and the committed
`lake-manifest.json`:

```sh
lake exe cache get
lake --wfail build GradedRings GradedRingsTests GradedRingsExamples
```

Successfully fetch the matching mathlib cache **before** building. The
aggregate publicly imports this leaf, and the test target registers its
direct client.

This algebra supplies neither maps on missing low degrees nor coefficient
regrouping, Proj, chart or scheme equivalences. The mathematical motivation is
Ravi Vakil, *The Rising Sea: Foundations of Algebraic Geometry*, October 21,
2025 draft, §7.4.4, Exercise 7.4.F, printed p. 215 (coefficient conventions
pp. 151–152); no book expression is copied and no source correspondence or
coverage is asserted. Source research is not needed to use this API.
Formal Frontier agents contributed the original proof/client and a separate
destination adaptation; see [provenance and credits](PROVENANCE.md).
