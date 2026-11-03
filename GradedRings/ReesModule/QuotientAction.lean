/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GradedRings.ReesModule.Map

/-!
# Scalar multiplication on associated graded representatives

The associated graded module is a quotient of the Rees module. Its existing action
by the quotient of the Rees algebra is characterized on quotient representatives by
`Ideal.AssociatedGradedModule.reesQuotient_mk_smul`.
-/

@[expose] public section

universe u v

namespace Ideal.AssociatedGradedModule

variable {R : Type u} [CommRing R] (I : Ideal R)
variable {M : Type v} [AddCommGroup M] [Module R M]

local notation "B" => reesAlgebra I
local notation "J" => I.map (algebraMap R B)
local notation "C" => B ⧸ J
local notation "S" => Ideal.Filtration.submodule (I.stableFiltration (⊤ : Submodule R M))

/-- Multiplication by a Rees algebra class on an associated graded class is induced
by the original action on Rees module representatives. -/
@[simp] theorem reesQuotient_mk_smul (b : B) (s : S) :
    (Ideal.Quotient.mk J b : C) •
        (Submodule.Quotient.mk s : Ideal.AssociatedGradedModule I M) =
      Submodule.Quotient.mk (b • s) := by
  change (algebraMap B C b) •
      (Submodule.Quotient.mk s : Ideal.AssociatedGradedModule I M) = _
  rw [IsScalarTower.algebraMap_smul]
  rfl

end Ideal.AssociatedGradedModule
