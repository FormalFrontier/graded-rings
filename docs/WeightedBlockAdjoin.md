# Weighted-homogeneous membership in a monomial adjoin

Import `GradedRings.WeightedBlockAdjoin`, or import the aggregate `GradedRings`.
For a finite index type `ι`, a commutative semiring `R`, and strictly positive
natural weights `w : ι → ℕ`, put `D := Finsupp.weightedBlockSize w` and let `T`
be the image of `{d : ι →₀ ℕ | Finsupp.weight w d = D}` under
`d ↦ MvPolynomial.monomial d (1 : R)`. The theorem
`MvPolynomial.IsWeightedHomogeneous.mem_adjoin_weightedBlockSize w hw k hp`
proves `p ∈ Algebra.adjoin R T` when
`hp : p.IsWeightedHomogeneous w (k * D)`. For example:

```lean
have hmem : p ∈ Algebra.adjoin R
    ((fun d : ι →₀ ℕ => MvPolynomial.monomial d (1 : R)) ''
      {d | Finsupp.weight w d = Finsupp.weightedBlockSize w}) :=
  MvPolynomial.IsWeightedHomogeneous.mem_adjoin_weightedBlockSize w hw k hp
```

The proof uses [`Finsupp.exists_weightedBlocks`](WeightedBlocks.md) to express
each relevant exponent as a sum of exactly `k` exponent vectors of weight `D`.
Mathlib's `MvPolynomial.monomial_sum_index` writes a monomial with an arbitrary
coefficient `r` as `MvPolynomial.C r` times the product of its coefficient-one
block monomials. The coefficient stays in the base subalgebra when `k = 0` and
the product is empty. Weighted-homogeneous induction then gives membership
for sums. `D` is an explicit positive bound, not necessarily the least one.

There is no integral-domain, field, nontriviality, inhabited-index, ring-negation
or unit-weight hypothesis. The result covers the zero semiring, nilpotent
coefficients and empty index types. It **requires positive weights**; it does
not cover zero weights. This is membership in a concrete coefficient
subalgebra, not polynomial factorization, graded evaluation, generation of an
entire Veronese ring or a Proj statement.

The [direct ordinary-import client](../test/WeightedBlockAdjoin.lean) retains
examples with mixed weights `2, 3`, arbitrary coefficients and `k = 0`, an empty
index type, `ℕ`, `ZMod 1`, nilpotents in `ZMod 4`, and finiteness of the native
weight-fiber monomial image. The [aggregate-import witness](../test/RootClient.lean)
checks the public root. Neither client depends on private producer declarations.

## Reproduction and status

This deliverable pins Lean `v4.34.0-rc2` and mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5`. After installing the pinned
toolchain, first run `lake exe cache get` and verify it succeeds, then build
the default three targets with
`lake --wfail build GradedRings GradedRingsTests GradedRingsExamples`.
These are reproduction instructions, **not** a report of executing a build.
At the initial September 28, 2026 static promotion checkpoint, the accepted
isolated source has focused build and complete actual-origin private/generated
standard-axiom evidence, but no applicable destination native three-target
build/audit or independent destination review has yet been claimed. Later
candidate-specific evidence and decisions belong in the owning issue #59;
that dated checkpoint is not a perpetual status assertion.

Original producer, direct client and initial guide: worker-b Hive Task
`hive-request-02c54ccf8e5ec79a99c29100b383e58fbbf37d58`, UID
`e461a433-ae28-4960-af44-a0f291127294`, accepted isolated incubator code
`96035f49afe3af3e74dd285c80db3b18f9615ef8`. The separate two-header
rights repair is worker-b Task `hive-request-0abf41ae4cc030259077e0ba697493aea02844cd`,
UID `3191b46a-0f33-4201-9069-719451401037`. Fresh exact-successor source
review: worker-a Task `hive-request-799c593fb89bc5735e637a2446886804e96741dd`,
UID `14657e87-8583-409b-ab68-c56044592546`. This distinct destination
transfer, native envelope, root witness and guide are by worker-b Task
`hive-request-1ea4bc1b3fbaba69e5e89127469d5bdb7d067cf7`, UID
`4883019e-7df8-4c54-a531-c0e01c705167`. The earlier weighted-block
arithmetic and mathematical exposition have separate authors; see
[provenance](PROVENANCE.md). These original project contributions use the
repository's Apache-2.0 terms; no textbook source, PDF or third-party proof
code is redistributed here. Source correspondence remains a separate decision.
