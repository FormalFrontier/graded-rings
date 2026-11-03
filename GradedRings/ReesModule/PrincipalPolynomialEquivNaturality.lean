/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GradedRings.ReesModule.PrincipalPolynomialNaturality

/-!
# Naturality of principal polynomial coordinates

Principal polynomial coordinate equivalences intertwine the maps induced by linear maps
of the original modules. The one-sided formulas require regularity of the generator only
on the module whose coordinate equivalence occurs.
-/

@[expose] public section

universe u v w

namespace Ideal.AssociatedGradedModule

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]
variable (a : R)

local notation "I" => Ideal.span (Singleton.singleton a : Set R)
local notation "A" => R ⧸ I
local notation "Qₘ" => M ⧸ (I • (⊤ : Submodule R M))

/-- Source principal coordinates commute with the induced map, without a regularity
hypothesis on the target. -/
theorem principalPolynomialEquiv_natural_left (f : M →ₗ[R] N)
    (hM : IsSMulRegular M a) (p : PolynomialModule A Qₘ) :
    map I f (principalPolynomialEquiv (M := M) a hM p) =
      principalPolynomialHom (M := N) a
        (PolynomialModule.map A (Ideal.quotientModuleMap I f) p) := by
  simpa only [principalPolynomialEquiv_apply] using
    principalPolynomialHom_natural a f p

/-- Inverse target coordinates recover the induced polynomial map, without a regularity
hypothesis on the source. -/
theorem principalPolynomialEquiv_symm_map_hom (f : M →ₗ[R] N)
    (hN : IsSMulRegular N a) (p : PolynomialModule A Qₘ) :
    (principalPolynomialEquiv (M := N) a hN).symm
        (map I f (principalPolynomialHom (M := M) a p)) =
      PolynomialModule.map A (Ideal.quotientModuleMap I f) p := by
  rw [principalPolynomialHom_natural a f p]
  simpa only [principalPolynomialEquiv_apply] using
    (principalPolynomialEquiv (M := N) a hN).symm_apply_apply
      (PolynomialModule.map A (Ideal.quotientModuleMap I f) p)

/-- Principal polynomial coordinate equivalences are natural in linear maps. -/
theorem principalPolynomialEquiv_natural (f : M →ₗ[R] N)
    (hM : IsSMulRegular M a) (hN : IsSMulRegular N a)
    (p : PolynomialModule A Qₘ) :
    map I f (principalPolynomialEquiv (M := M) a hM p) =
      principalPolynomialEquiv (M := N) a hN
        (PolynomialModule.map A (Ideal.quotientModuleMap I f) p) := by
  simpa only [principalPolynomialEquiv_apply] using
    principalPolynomialHom_natural a f p

/-- The inverses of principal polynomial coordinate equivalences are natural in linear maps. -/
theorem principalPolynomialEquiv_symm_natural (f : M →ₗ[R] N)
    (hM : IsSMulRegular M a) (hN : IsSMulRegular N a)
    (z : Ideal.AssociatedGradedModule I M) :
    (principalPolynomialEquiv (M := N) a hN).symm (map I f z) =
      PolynomialModule.map A (Ideal.quotientModuleMap I f)
        ((principalPolynomialEquiv (M := M) a hM).symm z) := by
  apply (principalPolynomialEquiv (M := N) a hN).injective
  simpa only [LinearEquiv.apply_symm_apply] using
    principalPolynomialEquiv_natural a f hM hN
      ((principalPolynomialEquiv (M := M) a hM).symm z)

end Ideal.AssociatedGradedModule
