<!--
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-->

# Zero-index selected-component rings

Import `GradedRings.VeroneseZero` directly, or `GradedRings` for the full
library. For a commutative ring `S` with a natural `GradedRing 𝒮`, these results
require no finite-type, domain, Noetherian, nontriviality or positive-index
hypothesis:

- `GradedRing.Veronese.zeroRingEquivAll 𝒮 n` identifies the entire new
  degree-zero component of the selected direct sum with the entire old
  degree-zero ring for **every** `n : ℕ`. Its underlying map is the existing
  `zeroRingHom`; `zeroRingEquivAll_apply` computes it using `inclusion`, and
  `zeroRingEquivAll_eq_zeroRingEquiv` recovers the original positive-index API.
- At `n = 0`, `VeroneseRing 𝒮 0` is the **external** direct sum of a separate
  copy of `𝒮 0` in every new degree. `zeroVariable 𝒮` is the degree-one copy
  of `1`; `zeroCoefficient 𝒮 j a` places the same underlying old coefficient
  `a : 𝒮 (0 * j)` in the *actual* new degree-zero ring.
  `of_zero_eq_algebraMap_mul_pow` expresses the `j`th summand as its coefficient
  times `(zeroVariable 𝒮) ^ j` via the actual algebra map.
- `aeval_zeroVariable_surjective` makes polynomial evaluation over that actual
  degree-zero ring surjective; `finiteType_zero` establishes
  `Algebra.FiniteType (component 𝒮 0 0) (VeroneseRing 𝒮 0)` without assuming
  finite type of `S`. A full polynomial equivalence is **not** asserted.

Fixed-summand injectivity proves the all-index degree-zero equivalence without
using the false whole-ring inclusion injectivity at index zero. Direct-sum
homogeneous multiplication gives the power formula and monomial factorization;
direct-sum induction then reduces surjectivity to polynomial monomials. The
canonical `inclusion 𝒮 0` sends `zeroVariable` to `1`, not `0`. With a nontrivial
old ring, `zeroVariable_ne_zeroCopy` distinguishes new degrees zero and one,
even though the inclusion identifies them. The zero-ring case remains valid for
the finite-type and equivalence results. The collapsed image in `S` is a
different object from this external sum.

In the pinned library project, fetch the matching mathlib cache first, then
build all three strict native targets:

```sh
lake exe cache get
lake --wfail build GradedRings GradedRingsTests GradedRingsExamples
```

The [ordinary direct-import client](../test/VeroneseZero.lean) uses arbitrary
coefficients, a mixed-weight grading, zero divisors and the zero ring; the
[aggregate-root client](../test/RootClient.lean) checks the generic API.
The direct client adapts Formal Frontier `GradedRings/test/FiniteVeronese.lean`
and `IncubatorTest/Algebra/GradedRing/VeroneseFiniteType.lean` fixtures.
Formal Frontier agents wrote the original producer, client and guide;
separate contributors adapted the imports. Atlas designed an earlier
uncompiled zero-index API, not these Lean proofs. See
[provenance and credits](PROVENANCE.md). No source PDF or third-party proof
code is bundled; source correspondence is a separate decision.
