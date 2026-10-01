/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import GradedRings.FiniteVeronese
import Mathlib.Data.ZMod.Basic

set_option warningAsError true

noncomputable section

namespace FiniteVeroneseClient

private def ambientWeights : Fin 3 → ℕ := ![0, 2, 3]
private def weights : Fin 2 → ℕ := ![2, 3]
private theorem weights_pos : ∀ i, 0 < weights i := by decide
private theorem weights_succ (i : Fin 2) : weights i = ambientWeights i.succ := by
  fin_cases i <;> decide

private abbrev Target (R : Type*) [CommRing R] := MvPolynomial (Fin 3) R
private abbrev Grading (R : Type*) [CommRing R] :=
  MvPolynomial.weightedHomogeneousSubmodule R ambientWeights

private noncomputable instance (R : Type*) [CommRing R] : GradedAlgebra (Grading R) :=
  MvPolynomial.weightedGradedAlgebra R ambientWeights

private noncomputable def generators (R : Type*) [CommRing R]
    (i : Fin 2) : Grading R (weights i) :=
  ⟨MvPolynomial.X i.succ, by
    rw [weights_succ]
    exact MvPolynomial.isWeightedHomogeneous_X R ambientWeights i.succ⟩

private theorem degree_zero_variable (R : Type*) [CommRing R] :
    (MvPolynomial.X (0 : Fin 3) : Target R) ∈ Grading R 0 := by
  simpa [ambientWeights] using
    (MvPolynomial.isWeightedHomogeneous_X R ambientWeights (0 : Fin 3))

private theorem generators_generate (R : Type*) [CommRing R] :
    Algebra.adjoin (Grading R 0)
      (Set.range (fun i : Fin 2 => (generators R i : Target R))) = ⊤ := by
  let U := Algebra.adjoin (Grading R 0)
    (Set.range (fun i : Fin 2 => (generators R i : Target R)))
  have hC (r : R) : (MvPolynomial.C r : Target R) ∈ U := by
    have hr : (MvPolynomial.C r : Target R) ∈ Grading R 0 :=
      MvPolynomial.isWeightedHomogeneous_C ambientWeights r
    simpa only [SetLike.GradeZero.algebraMap_apply] using
      U.algebraMap_mem (⟨MvPolynomial.C r, hr⟩ : Grading R 0)
  have hXzero : (MvPolynomial.X (0 : Fin 3) : Target R) ∈ U := by
    simpa only [SetLike.GradeZero.algebraMap_apply] using
      U.algebraMap_mem (⟨MvPolynomial.X 0, degree_zero_variable R⟩ : Grading R 0)
  have hXpositive (i : Fin 2) : (MvPolynomial.X i.succ : Target R) ∈ U :=
    Algebra.subset_adjoin ⟨i, rfl⟩
  apply top_unique
  intro p _
  induction p using MvPolynomial.induction_on with
  | C r => exact hC r
  | add p q hp hq => exact U.add_mem (hp (by simp)) (hq (by simp))
  | mul_X p i hp =>
      by_cases hi : i = 0
      · subst i
        exact U.mul_mem (hp (by simp)) hXzero
      · obtain ⟨j, rfl⟩ := Fin.exists_succ_eq_of_ne_zero hi
        exact U.mul_mem (hp (by simp)) (hXpositive j)

private theorem degree_zero_variable_nonconstant (r : ℤ) :
    (MvPolynomial.X (0 : Fin 3) : Target ℤ) ≠ MvPolynomial.C r := by
  intro h
  have hcoeff := congrArg (fun p : Target ℤ =>
    p.coeff (Finsupp.single (0 : Fin 3) 1)) h
  have hsingle : (Finsupp.single (0 : Fin 3) 1 : Fin 3 →₀ ℕ) ≠ 0 := by simp
  rw [MvPolynomial.coeff_C_of_ne_zero hsingle] at hcoeff
  norm_num at hcoeff

example : ∃ T : Set (GradedRing.Veronese.VeroneseRing (Grading ℤ)
      (Finsupp.weightedBlockSize weights)), T.Finite ∧
    T ⊆ (GradedRing.Veronese.component (Grading ℤ)
      (Finsupp.weightedBlockSize weights) 1 : Set _) ∧
    Algebra.adjoin (GradedRing.Veronese.component (Grading ℤ)
      (Finsupp.weightedBlockSize weights) 0) T = ⊤ :=
  GradedRing.Veronese.exists_finite_degree_one_generators
    (Grading ℤ) weights weights_pos (generators ℤ) (generators_generate ℤ)

example (r : Grading ℤ 0) (n : ℕ) (hn : 0 < n) :
    GradedRing.Veronese.inclusion (Grading ℤ) n
      (algebraMap (GradedRing.Veronese.component (Grading ℤ) n 0)
        (GradedRing.Veronese.VeroneseRing (Grading ℤ) n)
          ((GradedRing.Veronese.zeroRingEquiv (Grading ℤ) n hn).symm r)) =
        (r : Target ℤ) := by
  change GradedRing.Veronese.inclusion (Grading ℤ) n
    (((GradedRing.Veronese.zeroRingEquiv (Grading ℤ) n hn).symm r :
      GradedRing.Veronese.component (Grading ℤ) n 0) :
        GradedRing.Veronese.VeroneseRing (Grading ℤ) n) = (r : Target ℤ)
  rw [← GradedRing.Veronese.zeroRingEquiv_apply (Grading ℤ) n hn]
  simp only [RingEquiv.apply_symm_apply]

private theorem finite_type_input : Algebra.FiniteType (Grading ℤ 0) (Target ℤ) :=
  ⟨Subalgebra.fg_def.mpr
    ⟨Set.range (fun i : Fin 2 => (generators ℤ i : Target ℤ)), Set.finite_range _,
      generators_generate ℤ⟩⟩

example : ∃ n : ℕ, 0 < n ∧ ∃ T : Set
      (GradedRing.Veronese.VeroneseRing (Grading ℤ) n), T.Finite ∧
    T ⊆ (GradedRing.Veronese.component (Grading ℤ) n 1 : Set _) ∧
      Algebra.adjoin (GradedRing.Veronese.component (Grading ℤ) n 0) T = ⊤ := by
  have : Algebra.FiniteType (Grading ℤ 0) (Target ℤ) := finite_type_input
  exact GradedRing.Veronese.exists_positive_finite_degree_one_generators (Grading ℤ)

private abbrev EmptyTarget := MvPolynomial Empty ℤ
private abbrev EmptyGrading :=
  MvPolynomial.weightedHomogeneousSubmodule ℤ (fun _ : Empty => 1)
private noncomputable instance : GradedAlgebra EmptyGrading :=
  MvPolynomial.weightedGradedAlgebra ℤ (fun _ : Empty => 1)
private def emptyGenerators (i : Empty) : EmptyGrading 1 := i.elim

private theorem empty_generators_generate :
    Algebra.adjoin (EmptyGrading 0)
      (Set.range (fun i : Empty => (emptyGenerators i : EmptyTarget))) = ⊤ := by
  let U := Algebra.adjoin (EmptyGrading 0)
    (Set.range (fun i : Empty => (emptyGenerators i : EmptyTarget)))
  apply top_unique
  intro p _
  have hp : p ∈ EmptyGrading 0 :=
    MvPolynomial.isWeightedHomogeneous_of_isEmpty ℤ (fun _ : Empty => 1) p
  simpa only [SetLike.GradeZero.algebraMap_apply] using
    U.algebraMap_mem (⟨p, hp⟩ : EmptyGrading 0)

example : Finsupp.weightedBlockSize (fun _ : Empty => 1) = 1 := by
  simp [Finsupp.weightedBlockSize]

example : ∃ T : Set (GradedRing.Veronese.VeroneseRing EmptyGrading
      (Finsupp.weightedBlockSize (fun _ : Empty => 1))), T.Finite ∧
    T ⊆ (GradedRing.Veronese.component EmptyGrading
      (Finsupp.weightedBlockSize (fun _ : Empty => 1)) 1 : Set _) ∧
    Algebra.adjoin (GradedRing.Veronese.component EmptyGrading
      (Finsupp.weightedBlockSize (fun _ : Empty => 1)) 0) T = ⊤ :=
  GradedRing.Veronese.exists_finite_degree_one_generators EmptyGrading
    (fun _ : Empty => 1) (fun i => i.elim) emptyGenerators empty_generators_generate

example : Subsingleton (Target (ZMod 1)) := inferInstance

example : ∃ T : Set (GradedRing.Veronese.VeroneseRing (Grading (ZMod 1))
      (Finsupp.weightedBlockSize weights)), T.Finite ∧
    T ⊆ (GradedRing.Veronese.component (Grading (ZMod 1))
      (Finsupp.weightedBlockSize weights) 1 : Set _) ∧
    Algebra.adjoin (GradedRing.Veronese.component (Grading (ZMod 1))
      (Finsupp.weightedBlockSize weights) 0) T = ⊤ :=
  GradedRing.Veronese.exists_finite_degree_one_generators
    (Grading (ZMod 1)) weights weights_pos
    (generators (ZMod 1)) (generators_generate (ZMod 1))

example : (2 : ZMod 4) * 2 = 0 ∧
    ∃ T : Set (GradedRing.Veronese.VeroneseRing (Grading (ZMod 4))
      (Finsupp.weightedBlockSize weights)), T.Finite ∧
    T ⊆ (GradedRing.Veronese.component (Grading (ZMod 4))
      (Finsupp.weightedBlockSize weights) 1 : Set _) ∧
    Algebra.adjoin (GradedRing.Veronese.component (Grading (ZMod 4))
      (Finsupp.weightedBlockSize weights) 0) T = ⊤ := by
  exact ⟨by decide, GradedRing.Veronese.exists_finite_degree_one_generators
    (Grading (ZMod 4)) weights weights_pos
    (generators (ZMod 4)) (generators_generate (ZMod 4))⟩

end FiniteVeroneseClient
