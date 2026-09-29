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
consequence. This module does not construct shifted external residue sums,
their evaluation equivalence, or a convention for `n = 0`.

## Reproduction and provenance

Use the repository-pinned Lean toolchain and dependency manifest; fetch the
matching mathlib cache successfully **before** any build:

```sh
lake exe cache get
lake --wfail build GradedRings.VeroneseResidue
lake --wfail build VeroneseResidue
lake --wfail build GradedRings GradedRingsTests GradedRingsExamples
```

The original producer, ordinary client and guide were written by Formal
Frontier Agents, worker-b Task
`hive-request-1cc04ea025d989648e050829da560f5070fe022d` (UID
`7768c775-4401-4d05-b7d9-88b2fd34ca29`), under Apache-2.0; the original
independent reviewer was worker-a Task
`hive-request-d997f6f869ad5770abe62ccc1b3edc053fd17153` (UID
`0d110738-9176-47d3-a76d-04eaf3717c87`). The pre-existing
`VeroneseFinite` inclusion/finiteness proof is credited to Task
`hive-request-a6d9833e213de37036a9964c1059dcdaf5959701` (UID
`6555ed03-40cb-463b-9632-266fb9bd7c44`); its independent reviewer was
Task `hive-request-b100b6af01e9101041244a4af0cd5f4b657d3297` (UID
`31c33065-aa56-4c95-8dbc-e5643d740aaa`). The original residue donor is
incubator commit `905e7c2df24767f8cee4d7eafc757cb5c343cb3e`; its
original review and focused checks apply only there. The September 29, 2026
static destination transfer is by worker-b Task
`hive-request-8e46b5299287b35b65f34038800f1c3b7482b0f5` (UID
`ee21c7e8-3256-4684-8236-81517fa63480`); donor hashes are recorded in
[provenance](PROVENANCE.md), and the exact shipping revision in the
owning Graded Rings issue #87.
At that initial static-transfer checkpoint, the new import/root graph still
required its own checks, independent review and acceptance. Destination revision
`0b6938c383e40a402187a1dee67784666f897eb5` subsequently passed native run #962
(build and complete transitive standard-axiom audit, including private/generated
declarations) and independent destination review #4808, and received maintainer
acceptance in issue #87, comment #61553. Release review, protected release
integration and verified official publication are separate decisions recorded
in that owning issue; this checkpoint does not assert their completion. Neither
this guide nor the code implies source correspondence or coverage. The
mathematical library and guide need neither source assets nor unpublished
research to be used.
