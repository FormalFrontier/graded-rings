/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import Mathlib.RingTheory.LocalProperties.Reduced

/-!
# Reduced homogeneous localizations

The homogeneous localization of a reduced commutative ring is reduced, for a
grading by any additive commutative monoid with decidable equality and any
denominator submonoid. The proof uses the injective canonical map into the
ordinary localization. No denominator-regularity or nontriviality assumption is needed.

## References

The proof uses Mathlib's `isReduced_localizationPreserves` (Andrew Yang),
`isReduced_of_injective` (Oliver Nash), and the homogeneous-localization
construction and `HomogeneousLocalization.val_injective` (Jujian Zhang and
Eric Wieser).
-/

@[expose] public section

universe u v w

namespace HomogeneousLocalization

/-- Homogeneous localization preserves reducedness for a grading by any
commutative additive monoid. -/
instance isReduced {A : Type u} {σ : Type v} {ι : Type w}
    [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    [AddCommMonoid ι] [DecidableEq ι] (𝒜 : ι → σ) [GradedRing 𝒜]
    (S : Submonoid A) [IsReduced A] : IsReduced (HomogeneousLocalization 𝒜 S) :=
  _root_.isReduced_of_injective
    (algebraMap (HomogeneousLocalization 𝒜 S) (Localization S))
    (val_injective (𝒜 := 𝒜) S)

end HomogeneousLocalization
