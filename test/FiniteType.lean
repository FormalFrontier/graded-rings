/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GradedRings.FiniteType
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

set_option warningAsError true

noncomputable section

namespace GradedRingsTest

universe u v

variable {A : Type u} [CommRing A]
variable {σ : Type v} [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

private theorem homogeneous_generators (I : HomogeneousIdeal 𝒜) (hI : I.toIdeal.FG) :
    ∃ s : Finset A, Ideal.span (s : Set A) = I.toIdeal ∧
      ∀ x ∈ s, SetLike.IsHomogeneousElem 𝒜 x :=
  HomogeneousIdeal.exists_finset_span_eq_of_fg 𝒜 I hI

private theorem irrelevant_positive_generators (h : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.FG) :
    ∃ s : Finset A,
      Ideal.span (s : Set A) = (HomogeneousIdeal.irrelevant 𝒜).toIdeal ∧
      ∀ x ∈ s, ∃ n > 0, x ∈ 𝒜 n :=
  GradedAlgebra.irrelevant_exists_finset_span_eq_of_fg 𝒜 h

private theorem finite_type_of_irrelevant_fg (h : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.FG) :
    Algebra.FiniteType (𝒜 0) A :=
  GradedAlgebra.finiteType_of_irrelevant_fg 𝒜 h

private theorem irrelevant_fg_of_finite_type [Algebra.FiniteType (𝒜 0) A] :
    (HomogeneousIdeal.irrelevant 𝒜).toIdeal.FG :=
  GradedAlgebra.irrelevant_fg_of_finiteType 𝒜

private theorem irrelevant_fg_iff_finite_type :
    (HomogeneousIdeal.irrelevant 𝒜).toIdeal.FG ↔ Algebra.FiniteType (𝒜 0) A :=
  GradedAlgebra.irrelevant_fg_iff_finiteType 𝒜

section ZeroRing

local instance :
    GradedRing (MvPolynomial.homogeneousSubmodule (Fin 1) (ZMod 1)) :=
  MvPolynomial.gradedAlgebra

/-- The polynomial algebra over the trivial ring is finite type over its degree-zero part. -/
public theorem zero_ring_finite_type : Algebra.FiniteType
    ((MvPolynomial.homogeneousSubmodule (Fin 1) (ZMod 1)) 0)
    (MvPolynomial (Fin 1) (ZMod 1)) :=
  GradedAlgebra.finiteType_of_irrelevant_fg _ ⟨∅, by
    ext x
    simp [Subsingleton.elim x 0]⟩

end ZeroRing

section PolynomialRing

local instance :
    GradedRing (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ) :=
  MvPolynomial.gradedAlgebra

private theorem polynomial_ring_irrelevant_fg :
    (HomogeneousIdeal.irrelevant
      (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ)).toIdeal.FG :=
  Ideal.fg_of_isNoetherianRing _

private theorem polynomial_ring_finite_type : Algebra.FiniteType
    ((MvPolynomial.homogeneousSubmodule (Fin 2) ℤ) 0)
    (MvPolynomial (Fin 2) ℤ) :=
  GradedAlgebra.finiteType_of_irrelevant_fg _ (Ideal.fg_of_isNoetherianRing _)

end PolynomialRing

end GradedRingsTest
