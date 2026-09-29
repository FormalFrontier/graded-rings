<!--
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents (Hive Task hive-request-45b307ef0b08baacd6a851dadec8faa23ee22d69,
  UID 65fe43bb-2c1b-4320-b724-f8b1f1fa063a)
Documentation clarification: Atlas, 2026-09-28
Destination adaptation: Hive Task hive-request-f02ddb3e712c8d7d3a8fcf158241077be901618e,
  UID 3e891418-b2ba-4675-8135-5bc756be8433
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
failure rather than silently compiling all of mathlib. The build is only one
part of validation: strict native CI must also inventory all actual-origin
public, private and generated declarations and audit their transitive axioms.
The transfer author prepared the initial destination candidate without running
these commands. Exact destination code
`d14e0ae469b2b13d004bb9ef192ec452a5465760` subsequently passed native
three-target build and complete private/generated-inclusive standard-axiom
run 727 on 2026-09-28 at 10:32 UTC. The accepted isolated computation at
evidence commit
`c9fdc86f3bd73a5d658f77ef15a0d16853f20725` concerns the original
producer/client origins, not the new destination, aggregate root or adapted
client; run 727 supplies the separate destination evidence. Applicable
destination evidence and independent promotion review are required for
maintainer acceptance. The revision-specific review, acceptance, release
publication and source-correspondence decisions are recorded separately;
a computational pass does not itself supply them.

## Mathematical and contributor provenance

Motivation: Ravi Vakil, *The Rising Sea: Foundations of Algebraic Geometry*,
October 21, 2025 draft, §7.4.4, Exercise 7.4.E, printed page 215; its
generation-over-degree-zero convention appears in §4.5.6, pp. 151–152.
The source citation identifies a motivation, not source coverage, and no book
text is reproduced here. The original project mathematical expression and
direct clients were authored by Hive Task
`hive-request-45b307ef0b08baacd6a851dadec8faa23ee22d69` (UID
`65fe43bb-2c1b-4320-b724-f8b1f1fa063a`) in isolated commit
`f97749780abe31d39fc8a470cb8358a9cd53beb6`; Atlas corrected the
isolated guide at `3502cfa2dad3fca95c6aac8471da379e19cbf85d`.
The author's mathematical research used a source-vakil-foag proof plan at
`0f5efcced8f8f9cf632f8e7613b641c6bb45a8bc` and its independent **plan**
review at `3344351e10652ec9ec01fe59a0da7641089b36b4`. The original
**code** review at `69ed24cd8d1b2cbd7f95e4f33e7918896f6c1da7` and
fresh **guide-only** review at `8be88e9f998c8015604e749f1911e00e7455f72d`
supported Atlas's isolated-readiness acceptance; none reviews this transfer.
The transfer Task `hive-request-f02ddb3e712c8d7d3a8fcf158241077be901618e`
(UID `3e891418-b2ba-4675-8135-5bc756be8433`) copied the producer bytes,
adapted the client import/namespace and wrote this destination guide and
wiring; it did not originate the proof. See [provenance and rights](PROVENANCE.md).
