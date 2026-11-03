/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.ReesAlgebra

/-!
# Rees subalgebras

For an ideal `I` in a commutative semiring `R`, `I.reesSubalgebra` consists of the
polynomials whose coefficient of degree `n` belongs to `I ^ n`. Constants belong
to this subalgebra, and a monomial of degree `n` belongs exactly when its
coefficient lies in `I ^ n`.

Over a commutative ring, `I.reesSubalgebra` agrees with Mathlib's `reesAlgebra I`.
The coefficient condition and the ring-valued construction follow Mathlib.

## References

* Mathlib, `Mathlib.RingTheory.ReesAlgebra`.
-/

@[expose] public section

open Polynomial

universe u

namespace Ideal

section CommSemiring

variable {R : Type u} [CommSemiring R]

/-- The subalgebra of polynomials whose coefficient of degree `n` lies in `I ^ n`. -/
def reesSubalgebra (I : Ideal R) : Subalgebra R R[X] where
  carrier := {p : R[X] | ∀ n : ℕ, p.coeff n ∈ I ^ n}
  mul_mem' := by
    intro p q hp hq n
    rw [Polynomial.coeff_mul]
    refine (I ^ n).sum_mem fun ij hij => ?_
    have hij' : ij.1 + ij.2 = n := Finset.mem_antidiagonal.mp hij
    rw [← hij', Ideal.IsTwoSided.pow_add]
    exact Ideal.mul_mem_mul (hp ij.1) (hq ij.2)
  one_mem' := by
    intro n
    rw [Polynomial.coeff_one]
    split_ifs with h
    · subst n
      simp only [pow_zero, Ideal.one_eq_top, Submodule.mem_top]
    · exact (I ^ n).zero_mem
  add_mem' := by
    intro p q hp hq n
    rw [Polynomial.coeff_add]
    exact (I ^ n).add_mem (hp n) (hq n)
  zero_mem' := by
    intro n
    simp
  algebraMap_mem' := by
    intro r n
    change (Polynomial.C r).coeff n ∈ I ^ n
    cases n <;> simp [Ideal.one_eq_top]

/-- Membership in the Rees subalgebra is the coefficientwise ideal-power condition. -/
theorem mem_reesSubalgebra_iff (I : Ideal R) (p : R[X]) :
    p ∈ I.reesSubalgebra ↔ ∀ n : ℕ, p.coeff n ∈ I ^ n := by
  exact Iff.rfl

/-- Every coefficient of a polynomial in the Rees subalgebra lies in its ideal power. -/
theorem coeff_mem_reesSubalgebra (I : Ideal R) (p : I.reesSubalgebra) (n : ℕ) :
    (p : R[X]).coeff n ∈ I ^ n := by
  exact p.property n

/-- A monomial belongs to the Rees subalgebra exactly when its coefficient lies in the
corresponding ideal power. -/
@[simp] theorem monomial_mem_reesSubalgebra_iff (I : Ideal R) (n : ℕ) (r : R) :
    Polynomial.monomial n r ∈ I.reesSubalgebra ↔ r ∈ I ^ n := by
  rw [mem_reesSubalgebra_iff]
  constructor
  · intro h
    simpa only [Polynomial.coeff_monomial_same] using h n
  · intro hr m
    by_cases h : m = n
    · subst m
      simpa only [Polynomial.coeff_monomial_same] using hr
    · rw [Polynomial.coeff_monomial_of_ne r h]
      exact (I ^ m).zero_mem

/-- The scalar map into the Rees subalgebra becomes the constant polynomial map. -/
@[simp] theorem coe_algebraMap_reesSubalgebra (I : Ideal R) (r : R) :
    ((algebraMap R ↥(I.reesSubalgebra) r) : R[X]) = Polynomial.C r := by
  rw [Subalgebra.coe_algebraMap, Polynomial.algebraMap_eq]

/-- The degree-one polynomials in the Rees subalgebra recover the original ideal. -/
@[simp] theorem C_mul_X_mem_reesSubalgebra_iff (I : Ideal R) (r : R) :
    Polynomial.C r * Polynomial.X ∈ I.reesSubalgebra ↔ r ∈ I := by
  rw [Polynomial.C_mul_X_eq_monomial, monomial_mem_reesSubalgebra_iff, pow_one]

end CommSemiring

section CommRing

variable {R : Type u} [CommRing R]

/-- Over a commutative ring, the coefficient-power subalgebra is Mathlib's Rees algebra. -/
theorem reesSubalgebra_eq_reesAlgebra (I : Ideal R) :
    I.reesSubalgebra = _root_.reesAlgebra I := by
  apply Subalgebra.ext
  intro p
  exact (mem_reesSubalgebra_iff I p).trans (_root_.mem_reesAlgebra_iff I p).symm

end CommRing

end Ideal
