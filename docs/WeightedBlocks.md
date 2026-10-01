# Positive-weight blocks of finitely supported vectors

Import `GradedRings.WeightedBlocks` directly, or import `GradedRings` for the
whole library. The API uses mathlib's `Finsupp.weight` for
`f : ι →₀ ℕ`, without defining another weighted-degree operation. No
coefficient ring or graded-algebra instance is required.

For `[Fintype ι]` and `w : ι → ℕ`,
`Finsupp.weightedBlockSize w` is the explicit natural number

```text
max 1 (Fintype.card ι) * ∏ i, w i.
```

If `hw : ∀ i, 0 < w i`, `Finsupp.weightedBlockSize_pos w hw` makes this
bound strictly positive. The factor `max 1` also handles the empty index
type. This is **not generally a minimal block weight**.

For `k : ℕ`, `f : ι →₀ ℕ` and the exact equation
`hf : Finsupp.weight w f = k * Finsupp.weightedBlockSize w`, the theorem
`Finsupp.exists_weightedBlocks w hw k f hf` returns

```lean
∃ blocks : Fin k → (ι →₀ ℕ),
  (∑ j, blocks j) = f ∧
    ∀ j, Finsupp.weight w (blocks j) = Finsupp.weightedBlockSize w
```

The block count is **exactly** `k`. Their sum is the entire input vector,
coordinate by coordinate, not merely a vector with the same total weight.
A generic client can write:

```lean
obtain ⟨blocks, hsum, hweight⟩ :=
  Finsupp.exists_weightedBlocks w hw k f hf
```

The proof uses `P = ∏ i, w i`, `r = Fintype.card ι` and, for a nonempty
index type, `b i = P / w i`. Quotient/remainder decomposition separates
each `f i` into `f i % b i` and `f i / b i` copies of `b i`;
each quotient token has weight `P`, while the total remainder weight is
strictly less than `r * P`. Its divisibility by `P` gives a remainder count
`m < r`. Mathlib's `Finsupp.exists_le_degree_eq` chooses `r - m` tokens,
yielding a coordinatewise subvector of weight `r * P`. Subtract the first
block and induct on `k`. The helper remains private to the producer module.

For `k = 0`, strictly positive weights force `f = 0`; at `k = 1` the
whole vector forms a block. If `ι` is empty, the block size is `1` and
the weight equation is satisfiable only when `k = 0`. Zero weights are
outside the hypotheses: a nonzero weight-zero vector would invalidate the
zero-block conclusion. No finite-Veronese ring generation, weighted
polynomial evaluation or factorization, minimality, or Proj statement
follows from this vector decomposition alone.

The [ordinary-import client](../test/WeightedBlocks.lean) covers mixed
weights `2,3` and the vector `(6,4)` of weight `24 = 2 * 12`, alongside
one/zero-block, empty-index, singleton and unit-weight cases. The
[aggregate-root client](../test/RootClient.lean) uses both the positive-size
and exact-block theorems for arbitrary finite indices and positive weights.

## Verification and attribution

In the pinned Lean `v4.34.0-rc2` and mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5` environment, fetch the
matching mathlib cache *before* the destination's native three-target build:

```sh
lake exe cache get
lake build GradedRings GradedRingsTests GradedRingsExamples
```

The mathematical quotient/remainder exposition, original Lean
producer/client, and later adaptation and root witness were distinct Formal
Frontier contributions; the adaptation does not originate the earlier proof.
See [provenance and credits](PROVENANCE.md). This combinatorial theorem does
not itself establish source correspondence or whole-ring finite generation.
