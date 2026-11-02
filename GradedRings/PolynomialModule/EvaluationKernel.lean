/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Polynomial.Module.Basic
import Mathlib.Algebra.Polynomial.Div

/-!
# Evaluation kernels of polynomial modules

For a module over a commutative ring, evaluation at any scalar has kernel the
image of multiplication by `X - C r`. No regularity of the scalar or finiteness
of the coefficient module is required. For coefficients in the ring itself,
`equivPolynomialSelf` identifies the factor-existence statement with polynomial
divisibility.

The proof transports the scalar factor identity on each monomial to a constant
module-valued polynomial and uses linear induction. It does not construct a
module-valued division operation.

## References

This file uses Andrew Yang's polynomial-module formalization in Mathlib,
especially `lsingle`, `induction_linear`, `eval_smul`, and `equivPolynomialSelf`.
The scalar factor theorem comes from the polynomial monic and division
formalizations of Chris Hughes, Johannes Hölzl, Kim Morrison, and Jens Wagemaker.
-/

@[expose] public section

universe u v

namespace PolynomialModule

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

/-- Subtracting the constant evaluation makes a polynomial module element a
multiple of the corresponding linear factor. -/
private theorem exists_smul_X_sub_C_eq_sub_lsingle_eval
    (r : R) (p : PolynomialModule R M) :
    ∃ q : PolynomialModule R M,
      (Polynomial.X - Polynomial.C r) • q = p - lsingle R 0 (eval r p) := by
  induction p using induction_linear with
  | zero => exact ⟨0, by simp⟩
  | add p q hp hq =>
    obtain ⟨p', hp'⟩ := hp
    obtain ⟨q', hq'⟩ := hq
    refine ⟨p' + q', ?_⟩
    rw [smul_add, hp', hq', map_add, (lsingle R 0).map_add]
    exact sub_add_sub_comm _ _ _ _
  | single n m =>
    obtain ⟨q, hq⟩ := Polynomial.X_sub_C_dvd_sub_C_eval
      (p := Polynomial.monomial n (1 : R)) (a := r)
    refine ⟨q • lsingle R 0 m, ?_⟩
    rw [← mul_smul, ← hq, sub_smul, ← Polynomial.monomial_zero_left,
      monomial_smul_lsingle, monomial_smul_lsingle]
    simp only [Nat.add_zero, one_smul, Polynomial.eval_monomial, one_mul, eval_single]
    rfl

/-- Evaluation at `r` vanishes precisely on the multiples of `X - C r` in the
polynomial module. -/
theorem eval_eq_zero_iff_exists_smul_X_sub_C (r : R) (p : PolynomialModule R M) :
    eval r p = 0 ↔ ∃ q : PolynomialModule R M,
      (Polynomial.X - Polynomial.C r) • q = p := by
  constructor
  · intro hp
    obtain ⟨q, hq⟩ := exists_smul_X_sub_C_eq_sub_lsingle_eval r p
    exact ⟨q, by simpa only [hp, map_zero, sub_zero] using hq⟩
  · rintro ⟨q, rfl⟩
    simp only [eval_smul, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C, sub_self, zero_smul]

/-- Under `equivPolynomialSelf`, existence of a module-valued linear factor is
exactly the scalar polynomial divisibility statement. -/
theorem exists_smul_X_sub_C_eq_iff_dvd (r : R) (p : PolynomialModule R R) :
    (∃ q : PolynomialModule R R, (Polynomial.X - Polynomial.C r) • q = p) ↔
      (Polynomial.X - Polynomial.C r) ∣ equivPolynomialSelf p := by
  constructor
  · rintro ⟨q, hq⟩
    refine ⟨equivPolynomialSelf q, ?_⟩
    simpa only [(equivPolynomialSelf (R := R)).map_smul, smul_eq_mul] using
      congrArg (equivPolynomialSelf (R := R)) hq.symm
  · rintro ⟨q, hq⟩
    refine ⟨equivPolynomialSelf.symm q, ?_⟩
    apply (equivPolynomialSelf (R := R)).injective
    simpa only [(equivPolynomialSelf (R := R)).map_smul,
      LinearEquiv.apply_symm_apply, smul_eq_mul] using hq.symm

end PolynomialModule
