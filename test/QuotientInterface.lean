/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import GradedRings.Quotient

/-! # Ordinary direct-import reduction checks for the quotient grading -/

namespace GradedRingsTest.QuotientInterface

open DirectSum

universe u v w

variable {A : Type u} [CommRing A]
variable {ι : Type v} [DecidableEq ι] [AddMonoid ι]
variable {σ : Type w} [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ι → σ) [GradedRing 𝒜] (I : Ideal A)

omit [DecidableEq ι] [AddMonoid ι] [GradedRing 𝒜] in
private theorem componentMembership (i : ι) (q : A ⧸ I) :
    q ∈ Ideal.Quotient.gradedComponent 𝒜 I i ↔
      ∃ a, a ∈ 𝒜 i ∧ Ideal.Quotient.mk I a = q :=
  Iff.rfl

omit [DecidableEq ι] [AddMonoid ι] [GradedRing 𝒜] in
private theorem homReduction :
    (Ideal.Quotient.gradedRingHom 𝒜 I).toRingHom = Ideal.Quotient.mk I :=
  rfl

omit [DecidableEq ι] [AddMonoid ι] [GradedRing 𝒜] in
private theorem componentMapReduction (i : ι) (a : 𝒜 i) :
    (Ideal.Quotient.gradedComponentMap 𝒜 I i a : A ⧸ I) = Ideal.Quotient.mk I a :=
  rfl

private theorem preDecompositionReduction :
    Ideal.Quotient.gradedDecomposePre 𝒜 I =
      (DirectSum.map (Ideal.Quotient.gradedComponentMap 𝒜 I)).comp
        (DirectSum.decomposeAddEquiv 𝒜).toAddMonoidHom :=
  rfl

private theorem quotientReduction (hI : I.IsHomogeneous 𝒜) (a : A) :
    Ideal.Quotient.gradedDecompose 𝒜 I hI (Ideal.Quotient.mk I a) =
      Ideal.Quotient.gradedDecomposePre 𝒜 I a :=
  rfl

private theorem decompositionReduction (hI : I.IsHomogeneous 𝒜) :
    (Ideal.Quotient.gradedDecomposition 𝒜 I hI).decompose' =
      Ideal.Quotient.gradedDecompose 𝒜 I hI :=
  rfl

private theorem gradedRingReduction (hI : I.IsHomogeneous 𝒜) :
    (Ideal.Quotient.gradedRing 𝒜 I hI).toDecomposition =
      Ideal.Quotient.gradedDecomposition 𝒜 I hI :=
  rfl

end GradedRingsTest.QuotientInterface
