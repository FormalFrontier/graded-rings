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
The original proof, direct client and guide are Formal Frontier
contributions; separate contributors removed unsupported copyright-owner
assertions without changing the proofs, and adapted the native imports and
root witness. The earlier weighted-block arithmetic and exposition have
separate contributors; see [provenance and credits](PROVENANCE.md). This
project work is under Apache-2.0; no textbook PDF, substantive source prose
or third-party proof code is bundled. Source correspondence is separate.
