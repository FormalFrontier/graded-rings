/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GradedRings.WeightedVeroneseGenerators
import Mathlib.Data.ZMod.Basic

set_option warningAsError true

namespace WeightedVeroneseGeneratorsClient

open MvPolynomial

private def unequalWeights : Fin 2 → ℕ := ![2, 3]

private theorem integerSelectedDegrees :
    ∃ T : Finset (MvPolynomial (Fin 2) ℤ),
      (∀ p ∈ T, ∃ j, p.IsWeightedHomogeneous unequalWeights (4 * j)) ∧
      (X (0 : Fin 2) ^ 2 : MvPolynomial (Fin 2) ℤ) ∈ Algebra.adjoin ℤ (T : Set _) ∧
      (C (7 : ℤ) * X (1 : Fin 2) ^ 4 + X (0 : Fin 2) ^ 6 :
        MvPolynomial (Fin 2) ℤ) ∈ Algebra.adjoin ℤ (T : Set _) ∧
      (X (0 : Fin 2) ^ 2 : MvPolynomial (Fin 2) ℤ) ≠ 0 := by
  obtain ⟨T, hhom, hmem⟩ :=
    exists_finset_weightedVeronese_generators (R := ℤ) unequalWeights 4 (by decide)
  refine ⟨T, hhom, ?_, ?_, ?_⟩
  · apply hmem 1
    simpa [unequalWeights] using
      (isWeightedHomogeneous_X (R := ℤ) unequalWeights (0 : Fin 2)).pow 2
  · apply hmem 3
    have hfirst : (C (7 : ℤ) * X (1 : Fin 2) ^ 4 :
        MvPolynomial (Fin 2) ℤ).IsWeightedHomogeneous unequalWeights (4 * 3) := by
      simpa [unequalWeights] using
        ((isWeightedHomogeneous_X (R := ℤ) unequalWeights (1 : Fin 2)).pow 4).C_mul 7
    have hsecond : (X (0 : Fin 2) ^ 6 : MvPolynomial (Fin 2) ℤ).IsWeightedHomogeneous
        unequalWeights (4 * 3) := by
      simpa [unequalWeights] using
        (isWeightedHomogeneous_X (R := ℤ) unequalWeights (0 : Fin 2)).pow 6
    exact hfirst.add hsecond
  · simp [X_pow_eq_monomial, monomial_eq_zero]

private theorem arbitraryCoefficients {R : Type*} [CommSemiring R] (coefficient : R) :
    ∃ T : Finset (MvPolynomial (Fin 2) R),
      (∀ p ∈ T, ∃ j, p.IsWeightedHomogeneous unequalWeights (4 * j)) ∧
      (C coefficient * X (0 : Fin 2) ^ 2 : MvPolynomial (Fin 2) R) ∈
        Algebra.adjoin R (T : Set _) := by
  obtain ⟨T, hhom, hmem⟩ :=
    exists_finset_weightedVeronese_generators (R := R) unequalWeights 4 (by decide)
  refine ⟨T, hhom, hmem 1 _ ?_⟩
  simpa [unequalWeights] using
    ((isWeightedHomogeneous_X (R := R) unequalWeights (0 : Fin 2)).pow 2).C_mul
      coefficient

private theorem zeroWeight :
    ∃ T : Finset (MvPolynomial (Fin 1) ℕ),
      (∀ p ∈ T, ∃ j, p.IsWeightedHomogeneous (fun _ => 0) (4 * j)) ∧
      (X (0 : Fin 1) ^ 7 : MvPolynomial (Fin 1) ℕ) ∈ Algebra.adjoin ℕ (T : Set _) := by
  obtain ⟨T, hhom, hmem⟩ :=
    exists_finset_weightedVeronese_generators (R := ℕ) (fun _ : Fin 1 => 0) 4 (by decide)
  refine ⟨T, hhom, hmem 0 _ ?_⟩
  convert (isWeightedHomogeneous_X (R := ℕ) (fun _ : Fin 1 => 0) (0 : Fin 1)).pow 7
    using 1

/-- For no variables, constant polynomials are generated at every selected degree. -/
public theorem emptyVariables {R : Type*} [CommSemiring R] :
    ∃ T : Finset (MvPolynomial Empty R),
      (∀ p ∈ T, ∃ j, p.IsWeightedHomogeneous (fun i => Empty.elim i) (4 * j)) ∧
      ∀ p : MvPolynomial Empty R, p ∈ Algebra.adjoin R (T : Set _) := by
  obtain ⟨T, hhom, hmem⟩ :=
    exists_finset_weightedVeronese_generators (R := R) (fun i : Empty => Empty.elim i)
      4 (by decide)
  refine ⟨T, hhom, ?_⟩
  intro p
  apply hmem 0
  simpa using isWeightedHomogeneous_of_isEmpty (R := R)
    (fun i : Empty => Empty.elim i) p

private theorem indexOne :
    ∃ T : Finset (MvPolynomial (Fin 2) ℕ),
      (∀ p ∈ T, ∃ j, p.IsWeightedHomogeneous unequalWeights (1 * j)) ∧
      (X (1 : Fin 2) : MvPolynomial (Fin 2) ℕ) ∈ Algebra.adjoin ℕ (T : Set _) := by
  obtain ⟨T, hhom, hmem⟩ :=
    exists_finset_weightedVeronese_generators (R := ℕ) unequalWeights 1 (by decide)
  refine ⟨T, hhom, hmem 3 _ ?_⟩
  simpa [unequalWeights] using
    isWeightedHomogeneous_X (R := ℕ) unequalWeights (1 : Fin 2)

private theorem zeroRing :
    ∃ T : Finset (MvPolynomial (Fin 1) (ZMod 1)),
      (∀ p ∈ T, ∃ j, p.IsWeightedHomogeneous (fun _ => 2) (4 * j)) ∧
      (X (0 : Fin 1) ^ 2 : MvPolynomial (Fin 1) (ZMod 1)) ∈
        Algebra.adjoin (ZMod 1) (T : Set _) := by
  obtain ⟨T, hhom, hmem⟩ :=
    exists_finset_weightedVeronese_generators (R := ZMod 1)
      (fun _ : Fin 1 => 2) 4 (by decide)
  refine ⟨T, hhom, hmem 1 _ ?_⟩
  convert (isWeightedHomogeneous_X (R := ZMod 1) (fun _ : Fin 1 => 2) (0 : Fin 1)).pow 2
    using 1

end WeightedVeroneseGeneratorsClient
