/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import GradedRings

/-!
# Finite Rees modules and associated graded modules
-/

open Ideal
open scoped TensorProduct

universe u v

namespace GradedRingsTests.ReesModule

variable {R : Type u} [CommRing R] (I : Ideal R)
variable (M : Type v) [AddCommGroup M] [Module R M]

/-- The finite-module formulation gives the power-tail criterion; with finite stages,
the converse is precisely the reverse implication of the filtration finiteness theorem. -/
private theorem finite_rees_iff_pow_smul (F : I.Filtration M) (hStages : ∀ i, (F.N i).FG) :
    Module.Finite (reesAlgebra I) F.submodule ↔
      ∃ n₀, ∀ n ≥ n₀, F.N n = I ^ (n - n₀) • F.N n₀ := by
  constructor
  · intro hF
    exact (F.stable_of_submodule_fg (Module.Finite.iff_fg.mp hF)).exists_pow_smul_eq_of_ge
  · intro hF
    exact Module.Finite.iff_fg.mpr ((F.submodule_fg_iff_stable hStages).mpr
      ((Ideal.Filtration.stable_iff_exists_pow_smul_eq_of_ge (F := F)).mpr hF))

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
