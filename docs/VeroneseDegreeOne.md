<!--
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
Documentation clarification: Atlas
Destination adaptation: Formal Frontier Agents
-->

# Degree-one generation of positive Veronese rings

Import `GradedRings.VeroneseDegreeOne` directly, or `GradedRings` for the whole
library. This module publicly imports
[`GradedRings.Veronese`](Veronese.md) and
[`GradedRings.HomogeneousLifts`](HomogeneousLifts.md). Its
[direct client](../test/VeroneseDegreeOne.lean) and the
[aggregate-import witness](../test/RootClient.lean) use ordinary imports.

For any commutative ring `S`, component representation `σ` with
`[SetLike σ S] [AddSubgroupClass σ S]`, natural grading `𝒮 : ℕ → σ` with
`[GradedRing 𝒮]`, positive index `n` and generation of the old ring over its
actual degree-zero component by its **entire** degree-one component, the theorem
`GradedRing.Veronese.adjoin_component_one_eq_top 𝒮 n hn hgen` states:

```lean
hn : 0 < n
hgen : Algebra.adjoin (𝒮 0) (𝒮 1 : Set S) = ⊤
-- conclusion:
Algebra.adjoin (GradedRing.Veronese.component 𝒮 n 0)
  (GradedRing.Veronese.component 𝒮 n 1 :
    Set (GradedRing.Veronese.VeroneseRing 𝒮 n)) = ⊤
```

The selected ring is the **whole** direct sum `⨁ j : ℕ, 𝒮 (n * j)`, not a
definition by algebra generators. Its scalar ring is the **actual new**
`component 𝒮 n 0` (equivalent to `𝒮 0` when `0 < n`); its generators are
**all** of the new `component 𝒮 n 1`, corresponding to the whole old `𝒮 n`.
The theorem requires neither finite variables nor chosen finite generators,
finite type, a domain, a field, reducedness, `Nontrivial`, or an extra
block-generation premise. It makes no `n = 0` assertion and does not supply
coefficient regrouping, Proj/chart invariance, a scheme equivalence or
source-specific correspondence.

## Proof and clients

The proof uses `MvPolynomial (𝒮 1) (𝒮 0)`, taking every old degree-one
element as a variable, possibly infinitely many. Homogeneous polynomial
lifts supplied by `MvPolynomial.exists_isHomogeneous_aeval` follow from exactly
`hgen`; the homogeneous-submodule power identity and `pow_mul` identify
degree `n*j` with a power of the degree-`n` submodule. Power induction carries
all old scalars through `zeroRingEquiv.symm` and the actual old/new algebra
maps, and sends entire degree-`n` factors to the new component one via
`isHomogeneous_aeval_degreeOne` and `exists_component`. Finally
`inclusion_of`, `inclusion_injective` and `DirectSum.induction_on` cover every
summand of the selected ring. No new polynomial-extraction construction is
needed.

The five direct-client examples check generic `n = 1` and `n = 2`, compatibility
of old and new degree-zero scalars, and free two-variable polynomials over
`ZMod 4` (including nilpotents) and `ZMod 1` (the zero ring). The polynomial
clients **prove** their old-ring generation hypothesis by induction; they do
not assume the desired selected-ring conclusion. The
[selected-ring guide](Veronese.md) covers the unconditional ring construction;
the [homogeneous-lifts guide](HomogeneousLifts.md) explains the lifting input.

## Reproduction and status

This destination checkout pins Lean `leanprover/lean4:v4.34.0-rc2` and mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5`; its sole direct Lake
requirement is mathlib, and `lake-manifest.json` fixes nine resolved packages.
In a checkout of this candidate, retain all checked-in pins. Run from the
project root:

```sh
elan toolchain install leanprover/lean4:v4.34.0-rc2
lake exe cache get
LEAN_NUM_THREADS=2 lake --wfail build GradedRings GradedRingsTests GradedRingsExamples
```

The matching mathlib cache fetch must succeed **before** the build; diagnose
failure rather than silently compiling all of mathlib. A successful build checks
proofs but does not replace the complete transitive standard-axiom audit,
including private and generated declarations.

## Mathematical and contributor provenance

Motivation: Ravi Vakil, *The Rising Sea: Foundations of Algebraic Geometry*,
October 21, 2025 draft, §7.4.4, Exercise 7.4.E, printed page 215; its
generation-over-degree-zero convention appears in §4.5.6, pp. 151–152.
This is mathematical motivation, not source coverage, and no book text is
reproduced. Formal Frontier agents wrote the original proof and direct clients;
separate contributors adapted the import/namespace and destination guide
without originating the proof. Atlas clarified the guide, not the Lean proof.
See [provenance and credits](PROVENANCE.md).
