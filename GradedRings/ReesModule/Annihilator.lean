/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GradedRings.ReesModule.Evaluation

/-!
# Coefficientwise annihilation of Rees modules

An element of a Rees algebra annihilates the Rees module of a filtration exactly when
all its coefficients annihilate the initial stage. The proof uses Mathlib's coefficient
formulas for scalar multiplication in polynomial modules.
-/

@[expose] public section

universe u v

open scoped Polynomial

namespace Ideal.Filtration

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
variable {I : Ideal R} (H : I.Filtration M)

/-- Coercing scalar multiplication on a Rees module gives polynomial scalar multiplication. -/
private theorem coe_smul_submodule (b : reesAlgebra I) (y : H.submodule) :
    ((b • y : H.submodule) : PolynomialModule R M) =
      (b : R[X]) • (y : PolynomialModule R M) := rfl

/-- A Rees-algebra element annihilates the Rees module exactly when every coefficient
annihilates the initial stage of the filtration over the original ring. -/
theorem mem_annihilator_submodule_iff (b : reesAlgebra I) :
    b ∈ Module.annihilator (reesAlgebra I) H.submodule ↔
      ∀ n : ℕ, (b : R[X]).coeff n ∈ Module.annihilator R (H.N 0) := by
  constructor
  · intro hb n
    rw [Module.mem_annihilator]
    intro x
    apply Subtype.ext
    have hzero : b • H.single0 x = 0 :=
      (Module.mem_annihilator.mp hb) (H.single0 x)
    have hcoeff := congrArg
      (fun y : H.submodule => (y : PolynomialModule R M).coeff n) hzero
    simpa only [H.coe_smul_submodule, H.coe_single0, PolynomialModule.smul_single_apply,
      Nat.zero_le, ite_true, Nat.sub_zero, Submodule.coe_smul, Submodule.coe_zero,
      PolynomialModule.coeff_zero, Finsupp.zero_apply] using hcoeff
  · intro hb
    rw [Module.mem_annihilator]
    intro y
    apply Subtype.ext
    rw [H.coe_smul_submodule, Submodule.coe_zero]
    apply PolynomialModule.coeff_injective
    ext n
    rw [PolynomialModule.smul_apply, PolynomialModule.coeff_zero, Finsupp.zero_apply]
    apply Finset.sum_eq_zero
    intro p _
    have hy : (y : PolynomialModule R M).coeff p.2 ∈ H.N 0 :=
      H.antitone (Nat.zero_le p.2) ((H.mem_submodule _).mp y.property p.2)
    exact congrArg (fun x : H.N 0 => (x : M))
      ((Module.mem_annihilator.mp (hb p.1))
        ⟨(y : PolynomialModule R M).coeff p.2, hy⟩)

end Ideal.Filtration
