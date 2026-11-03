/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GradedRings.ReesModule.ConstantCoeff
public import GradedRings.ReesModule.PrincipalPolynomialSemilinear
public import CoherentModules.LinearAlgebra.TensorProduct.Noetherian
public import Mathlib.Algebra.Polynomial.Module.TensorProduct
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# Noetherianity of associated graded modules

Noetherianity over the quotient Rees algebra implies Noetherianity of the
degree-zero quotient over the coefficient ring. For a principal ideal, the
converse holds without any regularity assumption.
-/

@[expose] public section

universe u v

open Polynomial TensorProduct

namespace Ideal.AssociatedGradedModule

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

section Quotient

variable (I : Ideal R)

local notation "B" => reesAlgebra I
local notation "J" => I.map (algebraMap R B)
local notation "C" => B ⧸ J
local notation "Q" => M ⧸ (I • (⊤ : Submodule R M))

/-- Noetherianity of the associated graded module over the quotient Rees algebra
implies Noetherianity of the degree-zero quotient over the coefficient ring. -/
theorem isNoetherian_quotient [IsNoetherian C (Ideal.AssociatedGradedModule I M)] :
    IsNoetherian R Q := by
  let : RingHomSurjective (Ideal.reesQuotientConstantCoeff I) :=
    ⟨Ideal.reesQuotientConstantCoeff_surjective I⟩
  have hQ : IsNoetherian (R ⧸ I) Q :=
    isNoetherian_of_surjective (constantCoeff I M)
      (LinearMap.range_eq_top.mpr (constantCoeff_surjective I M))
  let : RingHomSurjective (Ideal.Quotient.mk I) :=
    ⟨Ideal.Quotient.mk_surjective⟩
  let e : Q →ₛₗ[Ideal.Quotient.mk I] Q :=
    { toFun := id
      map_add' := fun _ _ => rfl
      map_smul' := fun r q => by
        change (r • q : Q) = algebraMap R (R ⧸ I) r • q
        exact (IsScalarTower.algebraMap_smul (R ⧸ I) r q).symm }
  have he : Function.Bijective e :=
    ⟨fun _ _ h => h, fun q => ⟨q, rfl⟩⟩
  exact (LinearMap.isNoetherian_iff_of_bijective e he).mpr hQ

end Quotient

section Principal

variable (a : R)

local notation "I" => Ideal.span (Singleton.singleton a : Set R)
local notation "B" => reesAlgebra I
local notation "J" => Ideal.map (algebraMap R B) I
local notation "C" => B ⧸ J
local notation "G" => Ideal.AssociatedGradedModule I M
local notation "Q" => M ⧸ (I • (⊤ : Submodule R M))

/-- For a principal ideal, Noetherianity of the degree-zero quotient implies
Noetherianity of the associated graded module over the quotient Rees algebra. -/
theorem isNoetherian_principal [IsNoetherian R Q] : IsNoetherian C G := by
  let : Algebra.EssFiniteType R R[X] :=
    Algebra.EssFiniteType.of_finiteType (R := R) (S := R[X])
  let : IsNoetherian R[X] (R[X] ⊗[R] Q) :=
    Algebra.EssFiniteType.isNoetherian_tensorProduct
      (R := R) (S := R[X]) (M := Q)
  let : IsNoetherian R[X] (PolynomialModule R Q) :=
    isNoetherian_of_linearEquiv
      (PolynomialModule.polynomialTensorProductLEquivPolynomialModule (R := R) (M := Q))
  let : RingHomSurjective (Ideal.principalReesQuotientHom a) :=
    ⟨Ideal.surjective_principalReesQuotientHom a⟩
  exact isNoetherian_of_surjective (principalPolynomialHomSemilinear (M := M) a)
    (LinearMap.range_eq_top.mpr (principalPolynomialHomSemilinear_surjective (M := M) a))

/-- For a principal ideal, the associated graded module is Noetherian over the
quotient Rees algebra if and only if its degree-zero quotient is Noetherian over
the coefficient ring. -/
theorem isNoetherian_principal_iff : IsNoetherian C G ↔ IsNoetherian R Q := by
  constructor
  · intro h
    let := h
    exact isNoetherian_quotient (M := M) I
  · intro h
    let := h
    exact isNoetherian_principal (M := M) a

end Principal

end Ideal.AssociatedGradedModule
