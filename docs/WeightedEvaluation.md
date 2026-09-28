# Weighted evaluation into a graded ring

Import `GradedRings.WeightedEvaluation` directly, or import `GradedRings` for
the aggregate public API. Given a commutative ring `S`, a natural internal
grading `𝒮 : ℕ → σ` with `[SetLike σ S] [AddSubgroupClass σ S]` and
`[GradedRing 𝒮]`, arbitrary variables `ι` and weights `w : ι → ℕ`, choose
homogeneous elements `x : ∀ i : ι, 𝒮 (w i)`. Polynomial coefficients are in
**the actual degree-zero ring `𝒮 0`**, using its canonical algebra map into
`S`. No finiteness, nonemptiness, strictly-positive-weight, domain, field,
reducedness, or nontriviality assumption is needed; zero weights and the zero
ring are allowed.

## Public interface

- `MvPolynomial.IsWeightedHomogeneous.aeval_mem 𝒮 w x hp`: when
  `hp : p.IsWeightedHomogeneous w n`, ordinary evaluation
  `MvPolynomial.aeval (fun i => (x i : S)) p` belongs to `𝒮 n`.
- `MvPolynomial.weightedAevalGradedHom 𝒮 w x`: ordinary polynomial evaluation,
  bundled as the native graded ring homomorphism
  `(MvPolynomial.weightedHomogeneousSubmodule (𝒮 0) w) →+*ᵍ 𝒮`.
- `MvPolynomial.aeval_weightedHomogeneousComponent 𝒮 w x n p`: evaluation
  commutes with extraction of the weighted polynomial component and the
  target's **actual** graded component:

  ```lean
  MvPolynomial.aeval (fun i => (x i : S))
      (MvPolynomial.weightedHomogeneousComponent w n p) =
    (DirectSum.decompose 𝒮
      (MvPolynomial.aeval (fun i => (x i : S)) p) n : S)
  ```

- `MvPolynomial.exists_isWeightedHomogeneous_aeval 𝒮 w x hgen hs`:
  for `hs : s ∈ 𝒮 n`, provides a weighted-homogeneous degree-`n` polynomial
  evaluating to `s`, **only** with the additional genuine hypothesis
  `hgen : Algebra.adjoin (𝒮 0) (Set.range (fun i => (x i : S))) = ⊤`.

The first three results require **no** generation or surjectivity assumption.
For the last result, `hgen` gives ambient surjectivity of ordinary `aeval`,
and component surjectivity gives the homogeneous lift. This extends the
degree-one lift interface of `GradedRings.HomogeneousLifts` to any chosen
homogeneous generator family and natural weights; it does not assume all of
degree one as the chosen variables.

## Clients and limits

The [ordinary direct-import client](../test/WeightedEvaluation.lean) checks
mixed weights `0, 2, 3` in `MvPolynomial (Fin 3) ℤ`, including a nonzero
degree-five mixed monomial and a degree-zero variable. It proves by polynomial
induction that the chosen `X i` genuinely generate the target over its
**actual** zero component before invoking the lift. Further clients use an
infinite variable type, an empty family with a proof that evaluation is
**not** surjective, and the zero ring `ZMod 1`. The
[aggregate-import witness](../test/RootClient.lean) uses component naturality
through ordinary `import GradedRings`. The private helpers and anonymous
examples are regression clients, not additional public promises.

This API does not supply scalar transport between arbitrary coefficient
rings, a finite or positive-weight hypothesis, finite Veronese generation,
coefficient regrouping, polynomial factorization, Proj or source-specific
correspondence. In particular, finite positive-weight blocks in
`GradedRings.WeightedBlocks` are a separate arithmetic result and are not
used as a new premise or conclusion here.

## Reproduction and status

Use this repository's committed `lean-toolchain`, `lakefile.toml` and
`lake-manifest.json` (Lean `v4.34.0-rc2`, direct mathlib revision
`83abb3e776bdefcbc447a1e44d0debe4010039e5`). Fetch the matching
precompiled mathlib cache **before** any build, then build all three native
targets, including the direct client, the aggregate root and examples:

```sh
elan toolchain install leanprover/lean4:v4.34.0-rc2
lake exe cache get
lake --wfail build GradedRings GradedRingsTests GradedRingsExamples
```

At this initial September 28, 2026 *static destination-transfer* checkpoint,
the isolated incubator implementation had separately accepted focused builds,
a complete 27-actual-origin standard-axiom inventory including private and
generated declarations, and independent review. Neither that evidence nor
this guide proves the **changed destination graph** builds or has only the
standard three transitive axioms; applicable destination checks, independent
promotion/rights review, maintainer acceptance, protected integration,
verified official publication and source correspondence are distinct later
decisions. Consult the exact revision-specific contribution records for later
outcomes rather than treating this dated note as a live status indicator.
