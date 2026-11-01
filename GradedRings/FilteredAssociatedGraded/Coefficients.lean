/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GradedRings.FilteredAssociatedGraded.ReesAction
public import Mathlib.Algebra.Algebra.Tower

/-!
# Residue coefficients on integer associated graded modules

The quotient Rees action on an integer-filtered associated graded module
restricts along the canonical coefficient map from `R ⧸ I`. Residue-class
representatives act by the original `R`-module structure. Scalar towers record
compatibility with both `R` and the quotient Rees algebra, giving access to the
generic algebra-map and commuting-scalar identities.

The construction retains every integer degree and requires no finiteness,
exhaustivity, separatedness or lower bound on the filtration.

## References

* `Ideal.IntFiltration.moduleReesQuotient` and
  `Ideal.IntFiltration.scalarTowerCoefficients` for the quotient Rees action
  and its compatibility with the original scalars.
* Mathlib's `Module.compHom`, `IsScalarTower.of_algebraMap_smul`,
  `IsScalarTower.to₁₂₄` and `algebraMap_smul` for scalar restriction and coherence.
-/

@[expose] public section

universe u v

namespace Ideal.IntFiltration

variable {R : Type u} [CommRing R] {I : Ideal R}
variable {M : Type v} [AddCommGroup M] [Module R M] (F : I.IntFiltration M)

local notation "Q" => R ⧸ I
local notation "B" => reesAlgebra I
local notation "J" => I.map (algebraMap R B)
local notation "C" => B ⧸ J
local notation "G" => F.AssociatedGraded

/-- The coefficient quotient acts on the associated graded
by restriction of the quotient Rees action. -/
noncomputable instance moduleQuotient : Module Q G :=
  letI : Module C G := F.moduleReesQuotient
  Module.compHom G (algebraMap Q C)

/-- Residue coefficients and the quotient Rees action form a scalar tower. -/
instance isScalarTowerQuotientReesQuotient : IsScalarTower Q C G :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

/-- The original scalars act through the residue coefficient quotient. -/
instance isScalarTowerQuotient : IsScalarTower R Q G :=
  IsScalarTower.to₁₂₄ R Q C G

/-- A residue-class coefficient acts by its representative under the original scalar action. -/
@[simp]
theorem quotient_mk_smul (r : R) (x : G) :
    (Ideal.Quotient.mk I r : Q) • x = r • x :=
  algebraMap_smul Q r x

end Ideal.IntFiltration
