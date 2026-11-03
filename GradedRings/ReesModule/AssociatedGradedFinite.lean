/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GradedRings.ReesModule.TensorProduct
public import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Finiteness of associated graded modules

The associated graded module over the quotient Rees algebra is finitely generated
if and only if the degree-zero quotient is finitely generated over the coefficient ring.
-/

@[expose] public section

universe u v

namespace Ideal.AssociatedGradedModule

variable {R : Type u} [CommRing R] (I : Ideal R)
variable (M : Type v) [AddCommGroup M] [Module R M]

local notation "B" => reesAlgebra I
local notation "J" => Ideal.map (algebraMap R B) I
local notation "C" => B ⧸ J
local notation "G" => Ideal.AssociatedGradedModule I M
local notation "Q" => M ⧸ (I • (⊤ : Submodule R M))

/-- The associated graded module over the quotient Rees algebra is finitely generated
exactly when the degree-zero quotient is finitely generated over the coefficient ring. -/
theorem finite_iff : Module.Finite C G ↔ Module.Finite R Q := by
  constructor
  · intro h
    let : Module.Finite C G := h
    let : Module.Finite (R ⧸ I) Q :=
      Module.Finite.of_surjective (constantCoeff I M) (constantCoeff_surjective I M)
    exact Module.Finite.trans (R := R) (R ⧸ I) Q
  · intro h
    let : Module.Finite R Q := h
    exact Module.Finite.of_surjective (tensorProductTo I M) (tensorProductTo_surjective I M)

end Ideal.AssociatedGradedModule
