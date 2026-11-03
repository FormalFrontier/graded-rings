/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GradedRings.ReesModule.PrincipalPolynomial
public import GradedRings.ReesModule.Map
public import GradedRings.Ideal.QuotientModuleMap

/-!
# Naturality of principal polynomial coordinates

The principal polynomial homomorphism commutes pointwise with the associated-graded map
induced by an `R`-linear map. No regularity hypothesis on the generator or the
modules is needed.
-/

@[expose] public section

universe u v w

namespace Ideal.AssociatedGradedModule

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

/-- Principal polynomial coordinates commute with the maps induced by an `R`-linear map. -/
theorem principalPolynomialHom_natural (a : R) (f : M →ₗ[R] N)
    (p : PolynomialModule (R ⧸ Ideal.span ({a} : Set R))
      (M ⧸ (Ideal.span ({a} : Set R) • (⊤ : Submodule R M)))) :
    map (Ideal.span ({a} : Set R)) f (principalPolynomialHom (M := M) a p) =
      principalPolynomialHom (M := N) a
        (PolynomialModule.map (R ⧸ Ideal.span ({a} : Set R))
          (Ideal.quotientModuleMap (Ideal.span ({a} : Set R)) f) p) := by
  induction p using PolynomialModule.induction_linear with
  | zero => simp only [map_zero]
  | add p p' hp hp' => simp only [map_add, hp, hp']
  | single q z =>
      refine Submodule.Quotient.induction_on
        (Ideal.span ({a} : Set R) • (⊤ : Submodule R M)) z ?_
      intro m
      simp only [PolynomialModule.map_single, Ideal.quotientModuleMap_mk,
        principalPolynomialHom_single, map_mk, LinearMap.map_smul]

end Ideal.AssociatedGradedModule
