/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import GradedRings.Quotient
import GradedRings.Localization

/-! # Quotient and degree-zero localization examples

The quotient example recombines the homogeneous decomposition. The localization
example identifies mathlib's equal-degree fractions with the zero component of
the full localization. Neither construction requires a domain.
-/

namespace GradedRingsExamples.QuotientLocalization

noncomputable section

universe u v w

section Quotient

variable {A : Type u} [CommRing A]
variable {ι : Type v} [AddMonoid ι] [DecidableEq ι]
variable {σ : Type w} [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ι → σ) [GradedRing 𝒜] (I : Ideal A)

omit [AddMonoid ι] [DecidableEq ι] [GradedRing 𝒜] in
private theorem quotient_product (a b : A) :
    Ideal.Quotient.gradedRingHom 𝒜 I (a * b) =
      Ideal.Quotient.mk I a * Ideal.Quotient.mk I b := by
  simp

private theorem quotient_recombines (hI : I.IsHomogeneous 𝒜) (q : A ⧸ I) :
    DirectSum.coeAddMonoidHom (Ideal.Quotient.gradedComponent 𝒜 I)
      (Ideal.Quotient.gradedDecompose 𝒜 I hI q) = q :=
  Ideal.Quotient.gradedDecompose_leftInverse 𝒜 I hI q

end Quotient

section Localization

variable {A : Type u} [CommRing A]
variable {ι : Type v} [AddCommGroup ι] [DecidableEq ι]
variable {σ : Type w} [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ι → σ) [GradedRing 𝒜] (M : Submonoid A)

private theorem degree_zero_roundtrip (x : HomogeneousLocalization 𝒜 M) :
    (GradedLocalization.homogeneousLocalizationEquivZeroComponent 𝒜 M).symm
      (GradedLocalization.homogeneousLocalizationEquivZeroComponent 𝒜 M x) = x :=
  (GradedLocalization.homogeneousLocalizationEquivZeroComponent 𝒜 M).symm_apply_apply x

private theorem fraction_has_declared_degree {i j : ι}
    (a : 𝒜 (i + j)) (b : 𝒜 j) (hb : (b : A) ∈ M) :
    Localization.mk (a : A) ⟨(b : A), hb⟩ ∈
      GradedLocalization.component (𝒜 := 𝒜) M i :=
  GradedLocalization.mk_mem_component 𝒜 M a b hb

end Localization

#print axioms quotient_product
#print axioms quotient_recombines
#print axioms degree_zero_roundtrip
#print axioms fraction_has_declared_degree

end

end GradedRingsExamples.QuotientLocalization
