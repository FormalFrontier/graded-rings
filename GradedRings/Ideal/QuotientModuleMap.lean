/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Module.Submodule.Pointwise
public import Mathlib.Algebra.Module.Submodule.RestrictScalars
public import GradedRings.ReesAlgebra.QuotientPieces
public import GradedRings.ReesModule.Map

/-!
# Linear maps on quotient modules

An `R`-linear map induces an `R ⧸ I`-linear map between the quotients by
`I • ⊤`. The induced map uses the canonical quotient module structures.
-/

@[expose] public section

universe u v w x

namespace Ideal

variable {R : Type u} [CommRing R]
variable (I : Ideal R)
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]
variable {P : Type x} [AddCommGroup P] [Module R P]

/-- The map on quotient modules induced by an `R`-linear map, linear over `R ⧸ I`. -/
noncomputable def quotientModuleMap (f : M →ₗ[R] N) :
    (M ⧸ (I • (⊤ : Submodule R M))) →ₗ[R ⧸ I]
      (N ⧸ (I • (⊤ : Submodule R N))) :=
  LinearMap.extendScalarsOfSurjectiveEquiv (R := R) (S := R ⧸ I)
    Ideal.Quotient.mk_surjective
    ((I • (⊤ : Submodule R M)).mapQ (I • (⊤ : Submodule R N)) f
      (Submodule.smul_top_le_comap_smul_top I f))

/-- Restricting the scalars of the induced map recovers the usual quotient map. -/
theorem quotientModuleMap_restrictScalars (f : M →ₗ[R] N) :
    (quotientModuleMap I f).restrictScalars R =
      (I • (⊤ : Submodule R M)).mapQ (I • (⊤ : Submodule R N)) f
        (Submodule.smul_top_le_comap_smul_top I f) := by
  rfl

@[simp]
theorem quotientModuleMap_mk (f : M →ₗ[R] N) (m : M) :
    quotientModuleMap I f
        (Submodule.Quotient.mk m : M ⧸ (I • (⊤ : Submodule R M))) =
      (Submodule.Quotient.mk (f m) : N ⧸ (I • (⊤ : Submodule R N))) := by
  rfl

@[simp]
theorem quotientModuleMap_id :
    quotientModuleMap I (LinearMap.id : M →ₗ[R] M) =
      (LinearMap.id : (M ⧸ (I • (⊤ : Submodule R M))) →ₗ[R ⧸ I]
        (M ⧸ (I • (⊤ : Submodule R M)))) := by
  apply LinearMap.ext
  intro q
  induction q using Submodule.Quotient.induction_on with
  | H m => rfl

@[simp]
theorem quotientModuleMap_comp (f : M →ₗ[R] N) (g : N →ₗ[R] P) :
    quotientModuleMap I (g.comp f) =
      (quotientModuleMap I g).comp (quotientModuleMap I f) := by
  apply LinearMap.ext
  intro q
  induction q using Submodule.Quotient.induction_on with
  | H m => rfl

end Ideal
