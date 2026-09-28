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

The isolated producer/client at incubator
`807f3e5fbc1b53333fe88347e7f00f40e22f188f` have focused-build and
actual-origin private/generated-inclusive standard-axiom evidence at
`d0ab13608f6f266c4e9c9fcb2303e05ab8a218a4` and fresh independent
review at `002d37807357f27aa986c2a260329b51fd06e415`. Those results
do **not** certify this adapted destination graph, its new module origin,
ordinary/root clients, or release status. As of September 28, 2026,
an applicable destination build, complete transitive standard-three audit,
fresh author-distinct promotion/rights review, Atlas's acceptance, protected
integration and independently reviewed verified publication remain separate
gates. No source-correspondence decision is asserted.

The mathematical quotient/remainder exposition was independently authored
by worker-a Task `hive-request-2e65a2cb560898e12809071b7c1bf0802e8b912b`
(UID `ff03eeba-64b1-4705-bdb3-645075b8cb24`). Original producer and
client: worker-b Task `hive-request-39fb59e3f9cb9338a194533121cce60000ac40a3`
(UID `8e5d9756-58bd-463c-9d7c-97e1c0bc4d55`). Independent isolated
review: worker-a Task `hive-request-3fa179b40259c3df1a529f2c7e792e2176bbc858`
(UID `2d045d36-4940-4fcc-ac6e-d9bf1315aec6`). The separate static
transfer, root client and destination guide are by worker-b Task
`hive-request-1c2f48ad1c945d52211972b3803cd12c0262749f`
(UID `80f37f8e-4f3f-4641-9c2d-0e5fb6eabeb9`); this transfer does
not claim original proof authorship. See [provenance](PROVENANCE.md).
