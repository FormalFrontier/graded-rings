/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GradedRings.Noetherian
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

set_option warningAsError true

noncomputable section

namespace GradedRingsTest

universe u v

variable {A : Type u} [CommRing A]
variable {σ : Type v} [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

private theorem irrelevant_fg_of_noetherian [IsNoetherianRing A] :
    (HomogeneousIdeal.irrelevant 𝒜).toIdeal.FG :=
  GradedAlgebra.irrelevant_fg_of_isNoetherianRing 𝒜

private theorem noetherian_of_irrelevant_fg [IsNoetherianRing (𝒜 0)]
    (h : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.FG) :
    IsNoetherianRing A :=
  GradedAlgebra.isNoetherianRing_of_gradeZero_of_irrelevant_fg 𝒜 h

private theorem noetherian_iff :
    IsNoetherianRing A ↔
      IsNoetherianRing (𝒜 0) ∧
        (HomogeneousIdeal.irrelevant 𝒜).toIdeal.FG :=
  GradedAlgebra.isNoetherianRing_iff_gradeZero_and_irrelevant_fg 𝒜

section ZeroRing

local instance :
    GradedRing (MvPolynomial.homogeneousSubmodule (Fin 1) (ZMod 1)) :=
  MvPolynomial.gradedAlgebra

/-- A polynomial algebra over the trivial ring is Noetherian. -/
public theorem zero_ring_noetherian : IsNoetherianRing (MvPolynomial (Fin 1) (ZMod 1)) :=
  (GradedAlgebra.isNoetherianRing_iff_gradeZero_and_irrelevant_fg
    (MvPolynomial.homogeneousSubmodule (Fin 1) (ZMod 1))).mpr
    ⟨inferInstance, ⟨∅, by
      ext x
      simp [Subsingleton.elim x 0]⟩⟩

end ZeroRing

section PolynomialRing

local instance :
    GradedRing (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ) :=
  MvPolynomial.gradedAlgebra

private theorem polynomial_ring_noetherian_and_fg :
    IsNoetherianRing
        ((MvPolynomial.homogeneousSubmodule (Fin 2) ℤ) 0) ∧
      (HomogeneousIdeal.irrelevant
        (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ)).toIdeal.FG :=
  (GradedAlgebra.isNoetherianRing_iff_gradeZero_and_irrelevant_fg
    (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ)).mp (by infer_instance)

end PolynomialRing

end GradedRingsTest
