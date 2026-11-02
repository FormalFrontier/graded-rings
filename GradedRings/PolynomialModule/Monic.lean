/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Polynomial.Module.Basic
import Mathlib.Order.Interval.Finset.Nat

/-!
# Monic multiplication on polynomial modules

For an antitone family `P` of submodules, multiplication by a monic polynomial `g`
transports the coefficient condition at stage `n + g.natDegree` to the condition at
stage `n`. In particular, monic polynomials act injectively on polynomial modules.
No nontriviality or regularity assumption on the coefficient ring or module is needed.

The proof uses the coefficient formula for the polynomial-module action and descending
induction above the finite support of the source coefficients.

## References

This file uses Andrew Yang's polynomial-module formalization, the polynomial coefficient
API developed by Chris Hughes, Johannes Hölzl, Kim Morrison and Jens Wagemaker, and
Mathlib's finitely supported function and finite-sum APIs.
-/

@[expose] public section

universe u v

namespace PolynomialModule

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

/-- Multiplication by a monic polynomial shifts an antitone coefficient condition by
its natural degree. This includes monic constants and the zero coefficient ring. -/
theorem monic_smul_coeff_mem_iff (P : ℕ → Submodule R M) (hP : Antitone P)
    (g : Polynomial R) (hg : g.Monic) (q : PolynomialModule R M) :
    (∀ n, (g • q).coeff n ∈ P n) ↔ ∀ n, q.coeff n ∈ P (n + g.natDegree) := by
  classical
  constructor
  · intro h
    apply Nat.strong_decreasing_induction
    · refine ⟨q.coeff.support.sup id, ?_⟩
      intro n hn
      have hzero : q.coeff n = 0 := by
        apply Finsupp.notMem_support_iff.mp
        intro hnmem
        exact (not_le_of_gt hn) (Finset.le_sup (f := id) hnmem)
      rw [hzero]
      exact (P _).zero_mem
    · intro n ih
      have hlead : (g.natDegree, n) ∈ Finset.antidiagonal (n + g.natDegree) := by
        simp only [Finset.mem_antidiagonal, Nat.add_comm]
      have hrest :
          (∑ ij ∈ (Finset.antidiagonal (n + g.natDegree)).erase (g.natDegree, n),
            g.coeff ij.1 • q.coeff ij.2) ∈ P (n + g.natDegree) := by
        apply (P _).sum_mem
        rintro ⟨i, j⟩ hij
        have hij' : i + j = n + g.natDegree :=
          Finset.mem_antidiagonal.mp (Finset.mem_erase.mp hij).2
        by_cases hi : g.natDegree < i
        · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hi, zero_smul]
          exact (P _).zero_mem
        · have hj : n < j := by
            by_contra hnj
            have hi' : i = g.natDegree := by omega
            have hj' : j = n := by omega
            subst i
            subst j
            exact (Finset.mem_erase.mp hij).1 rfl
          exact (P _).smul_mem _ (hP (by omega : n + g.natDegree ≤ j + g.natDegree)
            (ih j hj))
      have hcoeff : (g • q).coeff (n + g.natDegree) =
          q.coeff n +
            ∑ ij ∈ (Finset.antidiagonal (n + g.natDegree)).erase (g.natDegree, n),
              g.coeff ij.1 • q.coeff ij.2 := by
        rw [smul_apply, ← Finset.add_sum_erase _ _ hlead]
        simp only [hg.coeff_natDegree, one_smul]
      have hm := h (n + g.natDegree)
      rw [hcoeff] at hm
      simpa only [add_sub_cancel_right] using (P _).sub_mem hm hrest
  · intro h n
    rw [smul_apply]
    apply (P n).sum_mem
    rintro ⟨i, j⟩ hij
    have hij' : i + j = n := Finset.mem_antidiagonal.mp hij
    by_cases hi : g.natDegree < i
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hi, zero_smul]
      exact (P n).zero_mem
    · exact (P n).smul_mem _ (hP (by omega : n ≤ j + g.natDegree) (h j))

/-- A monic polynomial acts injectively on the polynomial module of any module. -/
theorem monic_smul_injective (g : Polynomial R) (hg : g.Monic) :
    Function.Injective (fun q : PolynomialModule R M ↦ g • q) := by
  intro p q hpq
  change g • p = g • q at hpq
  have hzero : g • (p - q) = 0 := by rw [smul_sub, hpq, sub_self]
  have hmem : ∀ n, (g • (p - q)).coeff n ∈ (⊥ : Submodule R M) := by
    intro n
    simp [hzero]
  have hcoeff := (monic_smul_coeff_mem_iff (fun _ ↦ (⊥ : Submodule R M))
    (fun _ _ _ ↦ le_rfl) g hg (p - q)).mp hmem
  apply sub_eq_zero.mp
  apply coeff_injective
  ext n
  simpa using hcoeff n

end PolynomialModule
