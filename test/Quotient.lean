/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GradedRings.Quotient
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! # Private generic and zero-ring checks of the quotient grading -/

set_option warningAsError true

noncomputable section

namespace GradedRingsTest

open DirectSum

universe u v w

variable {A : Type u} [CommRing A]
variable {ι : Type v} [DecidableEq ι] [AddMonoid ι]
variable {σ : Type w} [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ι → σ) [GradedRing 𝒜]
variable (I : Ideal A)

private theorem quotient_component_graded_monoid :
    SetLike.GradedMonoid (Ideal.Quotient.gradedComponent 𝒜 I) := inferInstance

omit [DecidableEq ι] [AddMonoid ι] [GradedRing 𝒜] in
private theorem quotient_hom_underlying :
    (Ideal.Quotient.gradedRingHom 𝒜 I).toRingHom = Ideal.Quotient.mk I :=
  Ideal.Quotient.gradedRingHom_toRingHom 𝒜 I

omit [DecidableEq ι] [AddMonoid ι] [GradedRing 𝒜] in
private theorem quotient_hom_surjective : Function.Surjective (Ideal.Quotient.gradedRingHom 𝒜 I) :=
  Ideal.Quotient.gradedRingHom_surjective 𝒜 I

@[instance_reducible] private def quotient_graded_ring (hI : I.IsHomogeneous 𝒜) :
    GradedRing (Ideal.Quotient.gradedComponent 𝒜 I) :=
  Ideal.Quotient.gradedRing 𝒜 I hI

private def quotient_decomposition (hI : I.IsHomogeneous 𝒜) :
    (A ⧸ I) ≃+* ⨁ i, Ideal.Quotient.gradedComponent 𝒜 I i := by
  letI := Ideal.Quotient.gradedRing 𝒜 I hI
  exact DirectSum.decomposeRingEquiv (Ideal.Quotient.gradedComponent 𝒜 I)

private theorem quotient_decompose_left_inverse (hI : I.IsHomogeneous 𝒜) (q : A ⧸ I) :
    DirectSum.coeAddMonoidHom (Ideal.Quotient.gradedComponent 𝒜 I)
        (Ideal.Quotient.gradedDecompose 𝒜 I hI q) = q :=
  Ideal.Quotient.gradedDecompose_leftInverse 𝒜 I hI q

private theorem quotient_decompose_right_inverse (hI : I.IsHomogeneous 𝒜)
    (x : ⨁ i, Ideal.Quotient.gradedComponent 𝒜 I i) :
    Ideal.Quotient.gradedDecompose 𝒜 I hI
        (DirectSum.coeAddMonoidHom (Ideal.Quotient.gradedComponent 𝒜 I) x) = x :=
  Ideal.Quotient.gradedDecompose_rightInverse 𝒜 I hI x

section ZeroRing

local instance :
    GradedRing (MvPolynomial.homogeneousSubmodule (Fin 1) (ZMod 1)) :=
  MvPolynomial.gradedAlgebra

@[instance_reducible] private def zero_ring_quotient_grading :
    GradedRing (Ideal.Quotient.gradedComponent
      (MvPolynomial.homogeneousSubmodule (Fin 1) (ZMod 1))
      (⊥ : Ideal (MvPolynomial (Fin 1) (ZMod 1)))) :=
  Ideal.Quotient.gradedRing _ _ (Ideal.IsHomogeneous.bot _)

omit [CommRing A] in
/-- The graded quotient map is surjective also over the trivial ring. -/
public theorem zero_ring_quotient_surjective : Function.Surjective (Ideal.Quotient.gradedRingHom
    (MvPolynomial.homogeneousSubmodule (Fin 1) (ZMod 1))
    (⊥ : Ideal (MvPolynomial (Fin 1) (ZMod 1)))) :=
  Ideal.Quotient.gradedRingHom_surjective _ _

end ZeroRing

end GradedRingsTest
