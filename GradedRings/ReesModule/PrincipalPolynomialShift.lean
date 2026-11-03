/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GradedRings.ReesModule.PrincipalPolynomial
public import GradedRings.ReesAlgebra.PrincipalQuotient
public import GradedRings.ReesModule.QuotientAction

/-!
# The principal polynomial map and the degree-one action

The existing principal polynomial map intertwines multiplication by `X` with the
original Rees-quotient action of the principal degree-one generator. This does not
require regularity of the generator on the ring or on the module.
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
local notation "B" => reesAlgebra I
local notation "J" => Ideal.map (algebraMap R B) I
local notation "C" => B ⧸ J
local notation "S" => Ideal.Filtration.submodule (Ideal.stableFiltration I (⊤ : Submodule R M))
local notation "G" => Ideal.AssociatedGradedModule I M

/-- Multiplication by `X` before the principal polynomial map is the original
Rees-quotient action of the class of `a * X` after the map. -/
@[simp] theorem principalPolynomialHom_X_smul (p : PolynomialModule A Q) :
    principalPolynomialHom a ((Polynomial.X : Polynomial A) • p) =
      (Ideal.Quotient.mk J (Ideal.principalReesGenerator a) : C) •
        principalPolynomialHom a p := by
  induction p using PolynomialModule.induction_linear with
  | zero => simp only [smul_zero, map_zero]
  | add p q hp hq => simp only [smul_add, map_add, hp, hq]
  | single n q =>
    refine Submodule.Quotient.induction_on (I • (⊤ : Submodule R M)) q ?_
    intro m
    have hX :
        (Polynomial.X : Polynomial A) •
            PolynomialModule.single A n (Submodule.Quotient.mk m : Q) =
          PolynomialModule.single A (n + 1) (Submodule.Quotient.mk m : Q) := by
      rw [← Polynomial.monomial_one_one_eq_X, PolynomialModule.monomial_smul_single,
        one_smul, Nat.add_comm 1 n]
    rw [hX, principalPolynomialHom_single, principalPolynomialHom_single]
    change (Submodule.Quotient.mk _ : G) =
      (Ideal.Quotient.mk J (Ideal.principalReesGenerator a) : C) •
        (Submodule.Quotient.mk _ : G)
    rw [reesQuotient_mk_smul I]
    apply congrArg (Submodule.Quotient.mk : S → G)
    apply Subtype.ext
    change PolynomialModule.single R (n + 1) (a ^ (n + 1) • m) =
      (Ideal.principalReesGenerator a : Polynomial R) •
        PolynomialModule.single R n (a ^ n • m)
    rw [Ideal.coe_principalReesGenerator, Polynomial.C_mul_X_eq_monomial,
      PolynomialModule.monomial_smul_single, Nat.add_comm 1 n, pow_succ', mul_smul]

end Ideal.AssociatedGradedModule
