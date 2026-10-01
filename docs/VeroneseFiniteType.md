# Finite type of prescribed positive Veronese rings

Import `GradedRings.VeroneseFiniteType` directly, or import the public aggregate
`GradedRings`. For a naturally graded commutative ring `S` with components `𝒮`,
both public theorems conclude, for **every independently prescribed** `n` with
`0 < n`:

```lean
Algebra.FiniteType (GradedRing.Veronese.component 𝒮 n 0)
  (GradedRing.Veronese.VeroneseRing 𝒮 n)
```

- `GradedRing.Veronese.finiteType_of_finite_homogeneous_generators` assumes a
  finite family `x : ∀ i : ι, 𝒮 (w i)` of arbitrary natural weights and
  `Algebra.adjoin (𝒮 0) (Set.range (fun i => (x i : S))) = ⊤`.
- `GradedRing.Veronese.finiteType_of_finiteType` assumes native
  `[Algebra.FiniteType (𝒮 0) S]` and extracts a suitable finite homogeneous
  generating family.

The first proof uses the finite weighted-polynomial family from
`GradedRings.WeightedVeroneseGenerators`, evaluates at the chosen homogeneous
elements, and lifts evaluations to the selected components. It transports
**arbitrary** old-degree-zero coefficients via `zeroRingEquiv`, transfers
polynomial adjoin membership, and uses positive-index `inclusion_injective`
and direct-sum induction to obtain finite generation of the *whole* selected
ring over its **entire actual new degree-zero ring**. Generator weights may be
zero; no field, domain, nontriviality, Noetherianity or equal-weight hypothesis
is needed. This does not assert finite generation in new degree one at every
index or any result at `n = 0`.

The [ordinary direct-import client](../test/VeroneseFiniteType.lean) tests
mixed `0,2,3` weights, a nonconstant old-degree-zero coefficient, transport
of the whole old zero component, prescribed index `4`, native finite type at
index `1`, empty variables, `ZMod 1` and zero divisors in `ZMod 4`. Its
mixed-weight fixture adapts the original project-authored
[`test/FiniteVeronese.lean`](../test/FiniteVeronese.lean), as credited in the
client header. The [generic aggregate-root witness](../test/RootClient.lean)
checks public export without narrowing the theorem's hypotheses.

## Reproduction and status

The project pins Lean `v4.34.0-rc2` and mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5`. Install the pinned
toolchain and fetch the matching mathlib cache **before** building all three
strict native targets from the project root:

```sh
lake exe cache get
lake --wfail build GradedRings GradedRingsTests GradedRingsExamples
```

The original project producer, direct client and guide were contributed by
Formal Frontier agents; separate contributors adapted the native imports,
client fixture and registration. The mixed-weight fixture credits its source
in the client header. This whole-ring theorem has stronger scope than the
polynomial-only selected-generator lemma; neither alone establishes a
source-specific exercise correspondence. No textbook expression, PDF or
third-party proof code is bundled. See [provenance and credits](PROVENANCE.md).
