/-
Copyright (c) 2026 Formal Frontier. All rights reserved.
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier
-/
module

public import GradedRings.ReesModule.PrincipalPolynomial

/-!
# The principal polynomial map over the original scalar ring

For a principal ideal `I = (a)`, the coefficient-linear polynomial map is defined
on polynomials over `R ⧸ I`. This file regards the same coefficients as a
polynomial module over `R` and restricts the existing map to the original
`R`-actions. The value is exactly the old polynomial map applied after changing
only the scalar-ring tag of the polynomial coefficients.

The map is surjective without a regularity assumption on `a` or on the module.
-/

@[expose] public section

universe u v

namespace Ideal.AssociatedGradedModule

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

variable (a : R)

local notation "I" => Ideal.span (Singleton.singleton a : Set R)
local notation "A" => R ⧸ I
local notation "Q" => M ⧸ (I • (⊤ : Submodule R M))
local notation "G" => Ideal.AssociatedGradedModule I M

/-- The principal polynomial map, linear for the original `R`-actions. Its value
is the existing quotient-ring-linear map on the same coefficient sequence. -/
noncomputable def principalPolynomialHomRestrictScalars :
    PolynomialModule R Q →ₗ[R] G :=
  ((principalPolynomialHom (M := M) a).restrictScalars R).comp
    ((PolynomialModule.coeffLinearEquiv A R).symm.toLinearMap.comp
      (PolynomialModule.coeffLinearEquiv R R).toLinearMap)

/-- Restricting scalars does not change the prescribed polynomial-map value. -/
@[simp]
theorem principalPolynomialHomRestrictScalars_apply (p : PolynomialModule R Q) :
    principalPolynomialHomRestrictScalars a p =
      principalPolynomialHom a (PolynomialModule.ofCoeff A p.coeff) := rfl

/-- The underlying function is the fixed coefficient-retagging forward map. -/
theorem principalPolynomialHomRestrictScalars_coe :
    (principalPolynomialHomRestrictScalars (M := M) a : PolynomialModule R Q → G) =
      fun p => principalPolynomialHom a (PolynomialModule.ofCoeff A p.coeff) := rfl

/-- Evaluation on a coefficient sequence is independent of the polynomial's
scalar-ring tag. -/
@[simp]
theorem principalPolynomialHomRestrictScalars_ofCoeff (c : ℕ →₀ Q) :
    principalPolynomialHomRestrictScalars a (PolynomialModule.ofCoeff R c) =
      principalPolynomialHom a (PolynomialModule.ofCoeff A c) := rfl

/-- Changing a quotient-ring polynomial to an `R`-polynomial before applying the
restricted map recovers the original polynomial map. -/
@[simp]
theorem principalPolynomialHomRestrictScalars_ofCoeff_coeff
    (p : PolynomialModule A Q) :
    principalPolynomialHomRestrictScalars a (PolynomialModule.ofCoeff R p.coeff) =
      principalPolynomialHom a p := by
  rw [principalPolynomialHomRestrictScalars_ofCoeff, PolynomialModule.ofCoeff_coeff]

/-- Equal coefficient sequences give exactly the same forward-map value over
`R` and over the quotient ring. -/
theorem principalPolynomialHomRestrictScalars_eq_of_coeff_eq
    (p : PolynomialModule R Q) (q : PolynomialModule A Q) (h : p.coeff = q.coeff) :
    principalPolynomialHomRestrictScalars a p = principalPolynomialHom a q := by
  rw [principalPolynomialHomRestrictScalars_apply, h, PolynomialModule.ofCoeff_coeff]

/-- Changing only the coefficient-ring tag commutes with the polynomial
variable, for the existing polynomial-module actions. -/
theorem principalPolynomialHomRestrictScalars_retag_X_smul
    (p : PolynomialModule R Q) :
    PolynomialModule.ofCoeff A (((Polynomial.X : Polynomial R) • p).coeff) =
      (Polynomial.X : Polynomial A) • PolynomialModule.ofCoeff A p.coeff := by
  apply PolynomialModule.ext
  ext n
  simp only [← Polynomial.monomial_one_one_eq_X,
    PolynomialModule.monomial_smul_apply, one_smul]

/-- A singleton with a represented coefficient maps to the original Rees-module
singleton class with its principal-ideal weight. -/
theorem principalPolynomialHomRestrictScalars_single (q : ℕ) (m : M) :
    principalPolynomialHomRestrictScalars a
        (PolynomialModule.single R q (Submodule.Quotient.mk m : Q)) =
      mk I M
        ⟨PolynomialModule.single R q (a ^ q • m),
          single_mem I M q (a ^ q • m) (by
            apply Submodule.smul_mem_smul
            · rw [Ideal.span_singleton_pow]
              exact Ideal.subset_span (by simp)
            · exact Submodule.mem_top)⟩ := by
  simpa only [principalPolynomialHomRestrictScalars_apply,
    PolynomialModule.coeff_single, PolynomialModule.ofCoeff_single] using
    principalPolynomialHom_single (M := M) a q m

/-- The exact coefficient-retagging formula respects the original `R`-action on
the associated graded module. -/
theorem principalPolynomialHomRestrictScalars_smul (r : R)
    (p : PolynomialModule R Q) :
    principalPolynomialHom a (PolynomialModule.ofCoeff A (r • p).coeff) =
      r • principalPolynomialHom a (PolynomialModule.ofCoeff A p.coeff) :=
  (principalPolynomialHomRestrictScalars (M := M) a).map_smul r p

/-- The original-ring-linear principal polynomial map is unconditionally
surjective. -/
theorem principalPolynomialHomRestrictScalars_surjective :
    Function.Surjective (principalPolynomialHomRestrictScalars (M := M) a) := by
  intro z
  obtain ⟨p, hp⟩ := principalPolynomialHom_surjective (M := M) a z
  refine ⟨PolynomialModule.ofCoeff R p.coeff, ?_⟩
  simpa only [principalPolynomialHomRestrictScalars_ofCoeff_coeff] using hp

end Ideal.AssociatedGradedModule
