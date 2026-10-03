/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import GradedRings.FiniteType
import GradedRings.HomogeneousPrime
import GradedRings.Noetherian
public import GradedRings.SymmetricAlgebra

set_option warningAsError true

noncomputable section

namespace GradedRingsTest.InterfaceClient

universe u v w x

section SymmetricAlgebra

variable {R : Type u} {M : Type v} {N : Type w}
variable [CommSemiring R] [AddCommMonoid M] [Module R M]
variable [AddCommMonoid N] [Module R N]

@[instance_reducible] private def symmetric_grading :
    GradedAlgebra (SymmetricAlgebra.homogeneousSubmodule (R := R) (M := M)) :=
  SymmetricAlgebra.gradedAlgebra

private def symmetric_graded_map (f : M →ₗ[R] N) :
    SymmetricAlgebra.homogeneousSubmodule (R := R) (M := M) →ₐᵍ[R]
      SymmetricAlgebra.homogeneousSubmodule (R := R) (M := N) :=
  SymmetricAlgebra.gradedMap f

private theorem symmetric_graded_map_reduces (f : M →ₗ[R] N)
    (s : SymmetricAlgebra R M) :
    SymmetricAlgebra.gradedMap f s = SymmetricAlgebra.map f s :=
  rfl

/-- The symmetric-algebra map agrees with its universal-property lift. -/
public theorem symmetric_map_reduces (f : M →ₗ[R] N) :
    SymmetricAlgebra.map f = SymmetricAlgebra.lift (SymmetricAlgebra.ι R N ∘ₗ f) :=
  rfl

private theorem symmetric_component_reduces (n : ℕ) :
    SymmetricAlgebra.homogeneousSubmodule (R := R) (M := M) n =
      LinearMap.range (SymmetricAlgebra.ι R M) ^ n :=
  rfl

variable {I : Type x}

attribute [local instance] MvPolynomial.gradedAlgebra

private theorem basis_coordinate_degree (b : Module.Basis I R M) {n : ℕ}
    {s : SymmetricAlgebra R M}
    (hs : s ∈ SymmetricAlgebra.homogeneousSubmodule (R := R) (M := M) n) :
    SymmetricAlgebra.equivMvPolynomial b s ∈
      MvPolynomial.homogeneousSubmodule I R n :=
  SymmetricAlgebra.equivMvPolynomial_mem_homogeneousSubmodule b hs

private theorem basis_graded_map_reduces (b : Module.Basis I R M)
    (s : SymmetricAlgebra R M) :
    SymmetricAlgebra.equivMvPolynomialGradedHom b s =
      SymmetricAlgebra.equivMvPolynomial b s :=
  rfl

end SymmetricAlgebra

section FiniteTypeAndNoetherian

variable {A : Type u} [CommRing A]
variable {σ : Type v} [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

private theorem finite_type_of_irrelevant_fg
    (h : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.FG) :
    Algebra.FiniteType (𝒜 0) A :=
  GradedAlgebra.finiteType_of_irrelevant_fg 𝒜 h

private theorem noetherian_criterion :
    IsNoetherianRing A ↔
      IsNoetherianRing (𝒜 0) ∧
        (HomogeneousIdeal.irrelevant 𝒜).toIdeal.FG :=
  GradedAlgebra.isNoetherianRing_iff_gradeZero_and_irrelevant_fg 𝒜

end FiniteTypeAndNoetherian

section HomogeneousPrime

variable {A : Type u} [CommRing A]
variable {σ : Type v} [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℤ → σ) [GradedRing 𝒜]

private theorem projection_reduces (a : A) :
    ((GradedRing.degreeZeroProjection 𝒜) a : A) =
      (DirectSum.decompose 𝒜 a 0 : A) :=
  rfl

private def degree_zero_prime_equiv {d : ℤ} (u : Aˣ)
    (hu : (u : A) ∈ 𝒜 d) (hd : 0 < d) :
    {P : Ideal A // P.IsPrime ∧ P.IsHomogeneous 𝒜} ≃
      {q : Ideal (𝒜 0) // q.IsPrime} :=
  GradedRing.homogeneousPrimeEquivDegreeZeroPrime 𝒜 u hu hd

private theorem degree_zero_prime_equiv_reduces {d : ℤ} (u : Aˣ)
    (hu : (u : A) ∈ 𝒜 d) (hd : 0 < d)
    (P : {P : Ideal A // P.IsPrime ∧ P.IsHomogeneous 𝒜}) :
    ((GradedRing.homogeneousPrimeEquivDegreeZeroPrime 𝒜 u hu hd) P).1 =
      P.1.comap (algebraMap (𝒜 0) A) :=
  rfl

private theorem radical_extension_prime {d : ℤ} (u : Aˣ)
    (hu : (u : A) ∈ 𝒜 d) (hd : 0 < d)
    (q : Ideal (𝒜 0)) (hq : q.IsPrime) :
    (q.map (algebraMap (𝒜 0) A)).radical.IsPrime :=
  GradedRing.radical_map_degreeZero_isPrime 𝒜 u hu hd q hq

end HomogeneousPrime

end GradedRingsTest.InterfaceClient
