# Residue projections over the whole Veronese ring

Import `GradedRings.VeroneseResidue` (or the aggregate `GradedRings`). For a
naturally graded commutative ring `S`, a family `𝒮 : ℕ → σ` with
`[SetLike σ S]`, `[AddSubgroupClass σ S]` and `[GradedRing 𝒮]`, choose
`n : ℕ` with `0 < n` and `r : ℕ` with `r < n`. The scalar ring is the
**whole external** `GradedRing.Veronese.VeroneseRing 𝒮 n = ⨁ i : ℕ, 𝒮 (n * i)`.
On `S` use exactly the action induced by
`(GradedRing.Veronese.inclusion 𝒮 n).toAlgebra`.

## Public declarations

- `GradedRing.Veronese.residueProjectionAdd 𝒮 n r : S →+ S` transports
  `DFinsupp.filterAddMonoidHom` through `DirectSum.decomposeAddEquiv 𝒮`.
- `GradedRing.Veronese.residueProjection 𝒮 n r hn hr` is the same filter as
  `S →ₗ[VeroneseRing 𝒮 n] S` under the canonical algebra action. Its application
  agrees with the additive version by `residueProjection_apply`.
- `residueProjection_of_mem` gives `P x = if d % n = r then x else 0` for
  `x ∈ 𝒮 d`; `residueProjection_idempotent` gives `P (P x) = P x`.
- `mem_residueProjection_range_iff` characterizes its range submodule exactly:
  `x ∈ P.range ↔ ∀ d, d % n ≠ r → DirectSum.decompose 𝒮 x d = 0`.
- `residueProjection_range_finite` derives `Module.Finite V P.range` from
  `Module.Finite V S` for this same scalar action.
  `residueProjection_range_finite_of_finiteType` instead assumes only
  `[Algebra.FiniteType (𝒮 0) S]`, obtains ambient finiteness from the existing
  [`inclusion_finite 𝒮 n hn`](VeroneseFinite.md), and applies native
  `Module.Finite.range`.

The supporting declarations `residueProjectionAdd_of_mem`,
`decompose_residueProjectionAdd`, `residueProjectionAdd_idempotent`,
`residueProjectionAdd_eq_iff`, `residueProjectionAdd_inclusion_mul`, and
`residueProjection_apply` give the componentwise and scalar-compatibility laws.
The proof of linearity inducts on pure selected scalars and then on the old
homogeneous decomposition of `S`. A scalar of degree `n * i` sends an old
degree-`d` element to degree `n * i + d`, whose remainder is still `d % n`.
The coordinatewise filter proves idempotence and the fixed-point/range law;
the finite range is a **linear image**, not an arbitrary submodule of a finite
module. No individual old homogeneous fiber is assigned a whole-Veronese
module action.

The API needs no field, domain, nontriviality, Noetherianity, degree-one
generation or constant degree-zero ground ring. The [ordinary direct
client](../test/VeroneseResidue.lean) checks `n = 1, r = 0` (the projection is
the identity), a subsingleton/zero-ring boundary, homogeneous and range laws,
linearity and the finite-type consequence. The [aggregate-root
client](../test/RootClient.lean) checks public import and the finite-type
consequence. This projection module itself does not construct shifted external
residue sums or their evaluation equivalence: the separate
[shifted-residue module](../GradedRings/VeroneseResidueModule.lean) and
[guide](VeroneseResidueModule.md) construct those for positive reduced indices.
Neither supplies a convention for evaluation injectivity at `n = 0`.

## Reproduction and provenance

Use the repository-pinned Lean toolchain and dependency manifest; fetch the
matching mathlib cache successfully **before** any build:

```sh
lake exe cache get
lake --wfail build GradedRings.VeroneseResidue
lake --wfail build VeroneseResidue
lake --wfail build GradedRings GradedRingsTests GradedRingsExamples
```

The original project producer, client and guide were authored by Formal
Frontier agents; a separate contributor adapted the imports and guide for
this library. Its finite-inclusion prerequisite is independently supplied by
`GradedRings.VeroneseFinite`. The mathematics and examples above do not imply
source correspondence or book coverage. See [provenance and credits](PROVENANCE.md).
