/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import GradedRings.ReesAlgebra.PowerQuotientMultiplication
import Mathlib.Tactic.NormNum

/-!
# Integer ideal-power quotient multiplication

The classes of `2` multiply to the nonzero class of `4` in the degree-two
power quotient for `(2)`. The degree-zero quotient for the zero ideal is
also nonzero.
-/

open reesAlgebra

private abbrev twoIdeal : Ideal ℤ := Ideal.span {(2 : ℤ)}

private def two : ↥(twoIdeal ^ 1) :=
  ⟨2, by norm_num [twoIdeal, Ideal.mem_span_singleton]⟩

private def four : ↥(twoIdeal ^ 2) :=
  ⟨4, by norm_num [twoIdeal, Ideal.span_singleton_pow, Ideal.mem_span_singleton]⟩

-- This proof involves only the denominator equality and ideal membership, not multiplication.
private theorem positive_target_nonzero :
    (Submodule.Quotient.mk four : powerQuotient twoIdeal 2) ≠ 0 := by
  intro h
  have hmem := (Submodule.Quotient.mk_eq_zero _).mp h
  rw [← powerQuotient_denominator_eq] at hmem
  change (4 : ℤ) ∈ twoIdeal ^ (2 + 1) at hmem
  norm_num [twoIdeal, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hmem

-- This checks the concrete multiplication value, independently of its law statements.
example :
    powerQuotientMul twoIdeal 1 1
        (Submodule.Quotient.mk two) (Submodule.Quotient.mk two) =
      (Submodule.Quotient.mk four : powerQuotient twoIdeal 2) ∧
      (Submodule.Quotient.mk four : powerQuotient twoIdeal 2) ≠ 0 := by
  constructor
  · rw [powerQuotientMul_mk]
    rfl
  · exact positive_target_nonzero

example :
    (Submodule.Quotient.mk ⟨(1 : ℤ), by simp⟩ : powerQuotient (⊥ : Ideal ℤ) 0) ≠ 0 := by
  intro h
  have hmem := (Submodule.Quotient.mk_eq_zero _).mp h
  rw [← powerQuotient_denominator_eq] at hmem
  change (1 : ℤ) ∈ (⊥ : Ideal ℤ) ^ (0 + 1) at hmem
  norm_num at hmem
