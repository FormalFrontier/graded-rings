/-
Copyright (c) 2026 Formal Frontier. All rights reserved.
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier
-/
module

public import GradedRings.ReesModule.PrincipalPolynomialRestrictScalars
public import GradedRings.ReesModule.PrincipalPolynomialShift

/-!
# The semilinear principal polynomial map

For a principal ideal `I = (a)`, the principal polynomial map from
`PolynomialModule R (M ⧸ I • ⊤)` to the associated graded module is semilinear
for `Ideal.principalReesQuotientHom a`. The target retains its action by the
quotient of the Rees algebra. No polynomial-ring action on the target is needed.

The underlying function is the existing principal polynomial map over `R ⧸ I`,
after retagging the coefficients. Surjectivity therefore requires no regularity
assumption on `a` or on `M`.
-/

@[expose] public section

universe u v

namespace Ideal.AssociatedGradedModule

open Polynomial

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

variable (a : R)

local notation "I" => Ideal.span (Singleton.singleton a : Set R)
local notation "A" => R ⧸ I
local notation "Q" => M ⧸ (I • (⊤ : Submodule R M))
local notation "G" => Ideal.AssociatedGradedModule I M

private theorem principalPolynomialHomRestrictScalars_C_smul (r : R)
    (p : PolynomialModule R Q) :
    principalPolynomialHomRestrictScalars a ((Polynomial.C r : R[X]) • p) =
      Ideal.principalReesQuotientHom a (Polynomial.C r) •
        principalPolynomialHomRestrictScalars a p := by
  calc
    principalPolynomialHomRestrictScalars a ((Polynomial.C r : R[X]) • p) =
        principalPolynomialHomRestrictScalars a (r • p) :=
      congrArg (principalPolynomialHomRestrictScalars (M := M) a)
        (IsScalarTower.algebraMap_smul R[X] r p)
    _ = r • principalPolynomialHomRestrictScalars a p :=
      (principalPolynomialHomRestrictScalars (M := M) a).map_smul r p
    _ = Ideal.principalReesQuotientHom a (Polynomial.C r) •
        principalPolynomialHomRestrictScalars a p := by
      rw [Ideal.principalReesQuotientHom_C, IsScalarTower.algebraMap_smul]

private theorem principalPolynomialHomRestrictScalars_X_smul
    (p : PolynomialModule R Q) :
    principalPolynomialHomRestrictScalars a ((Polynomial.X : R[X]) • p) =
      Ideal.principalReesQuotientHom a Polynomial.X •
        principalPolynomialHomRestrictScalars a p := by
  simp only [principalPolynomialHomRestrictScalars_apply,
    principalPolynomialHomRestrictScalars_retag_X_smul,
    principalPolynomialHom_X_smul, Ideal.principalReesQuotientHom_X]

private theorem principalPolynomialHomRestrictScalars_X_pow_smul (n : ℕ)
    (p : PolynomialModule R Q) :
    principalPolynomialHomRestrictScalars a ((Polynomial.X : R[X]) ^ n • p) =
      Ideal.principalReesQuotientHom a ((Polynomial.X : R[X]) ^ n) •
        principalPolynomialHomRestrictScalars a p := by
  induction n generalizing p with
  | zero => simp only [pow_zero, map_one, one_smul]
  | succ n ih =>
    simp only [pow_succ', mul_smul, principalPolynomialHomRestrictScalars_X_smul,
      ih, map_mul]

private theorem principalPolynomialHomRestrictScalars_polynomial_smul
    (f : R[X]) (p : PolynomialModule R Q) :
    principalPolynomialHomRestrictScalars a (f • p) =
      Ideal.principalReesQuotientHom a f • principalPolynomialHomRestrictScalars a p := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg =>
    simp only [add_smul, map_add, hf, hg]
  | monomial n r =>
    simp only [← Polynomial.C_mul_X_pow_eq_monomial, mul_smul,
      principalPolynomialHomRestrictScalars_C_smul,
      principalPolynomialHomRestrictScalars_X_pow_smul, map_mul]

/-- The principal polynomial map, semilinear for the canonical map from `R[X]`
to the quotient of the Rees algebra. Its underlying function is the principal
polynomial map over `R ⧸ (a)`, with unchanged coefficients. -/
noncomputable def principalPolynomialHomSemilinear :
    PolynomialModule R Q →ₛₗ[Ideal.principalReesQuotientHom a] G where
  toFun := principalPolynomialHomRestrictScalars a
  map_add' := (principalPolynomialHomRestrictScalars (M := M) a).map_add
  map_smul' := by
    exact principalPolynomialHomRestrictScalars_polynomial_smul a

/-- The semilinear map has the prescribed coefficient-retagging value. -/
@[simp]
theorem principalPolynomialHomSemilinear_apply (p : PolynomialModule R Q) :
    principalPolynomialHomSemilinear a p =
      principalPolynomialHom a (PolynomialModule.ofCoeff A p.coeff) := rfl

/-- Passing to the semilinear map does not change the underlying function. -/
theorem principalPolynomialHomSemilinear_coe :
    (principalPolynomialHomSemilinear (M := M) a : PolynomialModule R Q → G) =
      principalPolynomialHomRestrictScalars a := rfl

/-- The additive map is the original scalar-restricted principal polynomial map. -/
@[simp]
theorem principalPolynomialHomSemilinear_toAddHom :
    (principalPolynomialHomSemilinear (M := M) a).toAddHom =
      (principalPolynomialHomRestrictScalars (M := M) a).toAddHom := rfl

/-- On a singleton, only the scalar ring of the polynomial module is retagged. -/
@[simp]
theorem principalPolynomialHomSemilinear_single (q : ℕ) (m : Q) :
    principalPolynomialHomSemilinear a (PolynomialModule.single R q m) =
      principalPolynomialHom a (PolynomialModule.single A q m) := by
  rw [principalPolynomialHomSemilinear_apply, PolynomialModule.coeff_single,
    PolynomialModule.ofCoeff_single]

/-- Every associated graded class is in the image of the semilinear principal
polynomial map, without a regularity assumption. -/
theorem principalPolynomialHomSemilinear_surjective :
    Function.Surjective (principalPolynomialHomSemilinear (M := M) a) :=
  principalPolynomialHomRestrictScalars_surjective (M := M) a

end Ideal.AssociatedGradedModule
