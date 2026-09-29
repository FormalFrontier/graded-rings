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

The original producer, client and guide were contributed by Formal Frontier
Agents, worker-b Task `hive-request-539a2511a0bca4739462d02431a6ec346c5da7cd`
(UID `e2df94a3-48e1-48bf-bafd-edd6b9e26b8f`); worker-a Task
`hive-request-9ef93ac5c57ff1a133ea796c0ba9bb66c0db6d9c` (UID
`04976027-c3cd-413a-96f0-40eb1b037e64`) independently reviewed that
isolated donor. The pre-existing projection and finite-inclusion APIs are
credited in [provenance](PROVENANCE.md). This destination transfer, with only
producer/client project imports changed, is by worker-b Task
`hive-request-2ef3a15beb11b4464a1cefb5ccabc924598a7976` (UID
`87e25bcb-68f4-44a4-9c46-dfdf33c005da`). At the initial September 29,
2026 static-transfer checkpoint, the changed destination module origins,
aggregate/import graph, private declarations and root client had **not** yet
received destination build/axiom evidence or an independent destination review;
donor evidence and review do not supply either. Later review, owner acceptance,
release and verified publication are distinct exact-revision decisions. This
library and guide are usable without source-repository notes or source-specific
conventions; source correspondence and coverage are not claimed.
