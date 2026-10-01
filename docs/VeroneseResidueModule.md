# Shifted Veronese residue modules

Import `GradedRings.VeroneseResidueModule` (or the aggregate `GradedRings`).
Let `S` be a commutative ring with a natural grading `𝒮 : ℕ → σ`,
`[SetLike σ S]`, `[AddSubgroupClass σ S]` and `[GradedRing 𝒮]`.
The whole external Veronese ring
`V = GradedRing.Veronese.VeroneseRing 𝒮 n` has coefficients `𝒮 (n * i)`;
`GradedRing.Veronese.ResidueModule 𝒮 n r` is the external direct sum of
the *entire* components `𝒮 (n * k + r)`. Its `Module V` instance uses
convolution: pure elements of degrees `i` and `k` multiply in degree `i + k`.
It does not assign a whole-`V` action to an individual old component.
The [projection guide](VeroneseResidue.md) describes the separate linear filter
whose range this external sum identifies with under positive reduced indices.

## API

- `of_smul_of_residue 𝒮 n r i k a b` computes the action on pure summands.
- `residueEvaluation 𝒮 n r` sums coefficients in `S`; its target is a `V`-module
  **via `(GradedRing.Veronese.inclusion 𝒮 n).toAlgebra`**, not another action.
  `residueEvaluation_of` evaluates a pure summand.
- `residueEvaluation_injective 𝒮 n r hn` requires only `hn : 0 < n`.
- `residueEvaluation_range_eq 𝒮 n r hn hr` identifies its image with the actual
  `(GradedRing.Veronese.residueProjection 𝒮 n r hn hr).range`, for
  `hr : r < n`. `residueEvaluationEquiv` is the resulting `V`-linear
  equivalence; `residueEvaluationEquiv_apply` identifies its forward map with
  coefficient evaluation.
- `residueModule_finite 𝒮 n r hn hr` uses `[Module.Finite V S]` for the
  canonical action. `residueModule_finite_of_finiteType 𝒮 n r hn hr` assumes
  `[Algebra.FiniteType (𝒮 0) S]` over the **full old degree-zero ring**, then
  transports finite generation from the projection's range.

The action and evaluation exist for all `n, r`. Injectivity is asserted only
for positive `n`; range equality, equivalence and finiteness transport additionally
require `r < n`. In particular the API assigns no shifted bijection at `n = 0`
or full-image assertion at `r ≥ n`. It requires no field, domain, nontriviality,
Noetherianity or degree-one generation hypothesis; finiteness is for this
specific linear image, not for arbitrary submodules. The [ordinary direct
client](../test/VeroneseResidueModule.lean) covers the action, evaluation,
equivalence, finiteness, the `n = 1, r = 0` boundary and a subsingleton ring;
the [aggregate-import witness](../test/RootClient.lean) uses the public
finite-type theorem.

## Reproduction and credit

Use `leanprover/lean4:v4.34.0-rc2` and this repository's exact manifest. Fetch
the matching precompiled mathlib cache **before** compilation:

```sh
lake exe cache get
lake --wfail build GradedRings.VeroneseResidueModule
lake --wfail build VeroneseResidueModule
lake --wfail build GradedRings GradedRingsTests GradedRingsExamples
```

Formal Frontier agents wrote the original producer, client and guide;
separate contributors adapted the project imports and root client here.
The pre-existing finite-inclusion and projection prerequisites have their
own [provenance](PROVENANCE.md). This library needs no unpublished research
to use, and its results do not by themselves establish source coverage.
