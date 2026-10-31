/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import GradedRings

/-!
# A Noetherian associated graded module from its first quotient
-/

open Ideal
open scoped TensorProduct

universe u v

namespace GradedRingsTests.ReesModule

variable {R : Type u} [CommRing R] (I : Ideal R)
variable (M : Type v) [AddCommGroup M] [Module R M]

local notation "A" => R ⧸ I
local notation "B" => reesAlgebra I
local notation "C" => B ⧸ (I.map (algebraMap R B))
local notation "Q" => M ⧸ (I • (⊤ : Submodule R M))
local notation "G" => Ideal.AssociatedGradedModule I M

example [IsNoetherianRing C] [Module.Finite A Q] : IsNoetherian C G := by
  let : Module.Finite C G :=
    Ideal.AssociatedGradedModule.finite_of_finite_quotient I M
  infer_instance

example (r : R) (g : G) : (Ideal.Quotient.mk I r : A) • g = r • g := by
  exact Ideal.AssociatedGradedModule.residue_smul I M r g

example (c : C) (q : Q) :
    ((Ideal.AssociatedGradedModule.characteristic I M).restrictScalars A)
      (c ⊗ₜ[A] q) = c • Ideal.AssociatedGradedModule.degreeZero I M q := by
  exact Ideal.AssociatedGradedModule.characteristic_tmul I M c q

end GradedRingsTests.ReesModule
