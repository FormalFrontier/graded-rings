/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import GradedRings.SymmetricAlgebra

/-! # Basis-free functoriality and polynomial coordinates

These examples work over a commutative semiring and arbitrary modules. A basis
is required only for the coordinate presentation, not for the grading or map.
-/

namespace GradedRingsExamples.Symmetric

noncomputable section

universe u v w x

variable {R : Type u} [CommSemiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]
variable {N : Type w} [AddCommMonoid N] [Module R N]

private theorem map_product_of_generators (f : M →ₗ[R] N) (m₁ m₂ : M) :
    SymmetricAlgebra.gradedMap f
      (SymmetricAlgebra.ι R M m₁ * SymmetricAlgebra.ι R M m₂) =
    SymmetricAlgebra.ι R N (f m₁) * SymmetricAlgebra.ι R N (f m₂) := by
  simp

variable {I : Type x}

attribute [local instance] MvPolynomial.gradedAlgebra

private theorem coordinates_preserve_degree (basis : Module.Basis I R M)
    {n : ℕ} {s : SymmetricAlgebra R M}
    (hs : s ∈ SymmetricAlgebra.homogeneousSubmodule (R := R) (M := M) n) :
    SymmetricAlgebra.equivMvPolynomialGradedHom basis s ∈
      MvPolynomial.homogeneousSubmodule I R n ∧
    SymmetricAlgebra.equivMvPolynomialSymmGradedHom basis
      (SymmetricAlgebra.equivMvPolynomialGradedHom basis s) = s := by
  refine ⟨SymmetricAlgebra.equivMvPolynomial_mem_homogeneousSubmodule basis hs, ?_⟩
  exact (SymmetricAlgebra.equivMvPolynomial basis).symm_apply_apply s

#print axioms map_product_of_generators
#print axioms coordinates_preserve_degree

end

end GradedRingsExamples.Symmetric
