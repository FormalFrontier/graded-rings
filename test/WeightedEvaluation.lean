/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GradedRings.WeightedEvaluation

@[expose] public section

namespace WeightedEvaluationClient

private def weights (i : Fin 3) : ℕ := if i = 0 then 0 else if i = 1 then 2 else 3

private abbrev Target := MvPolynomial (Fin 3) ℤ

private abbrev Grading := MvPolynomial.weightedHomogeneousSubmodule ℤ weights

private noncomputable instance : GradedAlgebra Grading :=
  MvPolynomial.weightedGradedAlgebra ℤ weights

private noncomputable def generators (i : Fin 3) : Grading (weights i) :=
  ⟨MvPolynomial.X i, MvPolynomial.isWeightedHomogeneous_X ℤ weights i⟩

example (p : MvPolynomial (Fin 3) (Grading 0)) :
    MvPolynomial.weightedAevalGradedHom Grading weights generators p =
      MvPolynomial.aeval (fun i => (generators i : Target)) p := rfl

example : MvPolynomial.aeval (fun i => (generators i : Target))
    (MvPolynomial.X (1 : Fin 3) * MvPolynomial.X (2 : Fin 3) :
      MvPolynomial (Fin 3) (Grading 0)) ∈ Grading 5 := by
  apply MvPolynomial.IsWeightedHomogeneous.aeval_mem Grading weights generators
  simpa [weights] using
    (MvPolynomial.isWeightedHomogeneous_X (R := Grading 0) weights (1 : Fin 3)).mul
      (MvPolynomial.isWeightedHomogeneous_X (R := Grading 0) weights (2 : Fin 3))

example : MvPolynomial.aeval (fun i => (generators i : Target))
    (MvPolynomial.X (0 : Fin 3) : MvPolynomial (Fin 3) (Grading 0)) ∈ Grading 0 := by
  apply MvPolynomial.IsWeightedHomogeneous.aeval_mem Grading weights generators
  simpa [weights] using
    (MvPolynomial.isWeightedHomogeneous_X (R := Grading 0) weights (0 : Fin 3))

example (p : MvPolynomial (Fin 3) (Grading 0)) :
    MvPolynomial.aeval (fun i => (generators i : Target))
      (MvPolynomial.weightedHomogeneousComponent weights 5 p) =
      (DirectSum.decompose Grading
        (MvPolynomial.aeval (fun i => (generators i : Target)) p) 5 : Target) :=
  MvPolynomial.aeval_weightedHomogeneousComponent Grading weights generators 5 p

private theorem generators_generate :
    Algebra.adjoin (Grading 0) (Set.range (fun i => (generators i : Target))) = ⊤ := by
  simp only [generators]
  set generated := Algebra.adjoin (Grading 0) (Set.range (MvPolynomial.X : Fin 3 → Target))
  rw [← top_le_iff]
  intro p _
  have hC (r : ℤ) : (MvPolynomial.C r : Target) ∈ generated := by
    have hr : (MvPolynomial.C r : Target) ∈ Grading 0 :=
      MvPolynomial.isWeightedHomogeneous_C weights r
    simpa only [SetLike.GradeZero.algebraMap_apply] using
      (generated.algebraMap_mem (⟨MvPolynomial.C r, hr⟩ : Grading 0))
  induction p using MvPolynomial.induction_on with
  | C r => exact hC r
  | add p q hp hq => exact generated.add_mem (hp (by simp)) (hq (by simp))
  | mul_X p i hp =>
      exact generated.mul_mem (hp (by simp)) (Algebra.subset_adjoin (Set.mem_range_self i))

example (s : Target) (hs : s ∈ Grading 5) :
    ∃ p : MvPolynomial (Fin 3) (Grading 0),
      p.IsWeightedHomogeneous weights 5 ∧
        MvPolynomial.aeval (fun i => (generators i : Target)) p = s :=
  MvPolynomial.exists_isWeightedHomogeneous_aeval
    Grading weights generators generators_generate hs

private def infiniteWeights (i : ℕ) : ℕ :=
  if i = 0 then 0 else if i = 1 then 2 else if i = 2 then 3 else i + 1

private abbrev InfiniteTarget := MvPolynomial ℕ ℤ
private abbrev InfiniteGrading :=
  MvPolynomial.weightedHomogeneousSubmodule ℤ infiniteWeights

private noncomputable instance : GradedAlgebra InfiniteGrading :=
  MvPolynomial.weightedGradedAlgebra ℤ infiniteWeights

private noncomputable def infiniteGenerators (i : ℕ) : InfiniteGrading (infiniteWeights i) :=
  ⟨MvPolynomial.X i, MvPolynomial.isWeightedHomogeneous_X ℤ infiniteWeights i⟩

example : MvPolynomial.aeval (fun i => (infiniteGenerators i : InfiniteTarget))
    (MvPolynomial.X 1 * MvPolynomial.X 2 :
      MvPolynomial ℕ (InfiniteGrading 0)) ∈ InfiniteGrading 5 := by
  apply MvPolynomial.IsWeightedHomogeneous.aeval_mem
    InfiniteGrading infiniteWeights infiniteGenerators
  simpa [infiniteWeights] using
    (MvPolynomial.isWeightedHomogeneous_X (InfiniteGrading 0) infiniteWeights 1).mul
      (MvPolynomial.isWeightedHomogeneous_X (InfiniteGrading 0) infiniteWeights 2)

example (p : MvPolynomial ℕ (InfiniteGrading 0)) :
    MvPolynomial.aeval (fun i => (infiniteGenerators i : InfiniteTarget))
      (MvPolynomial.weightedHomogeneousComponent infiniteWeights 5 p) =
      (DirectSum.decompose InfiniteGrading
        (MvPolynomial.aeval (fun i => (infiniteGenerators i : InfiniteTarget)) p) 5 :
        InfiniteTarget) :=
  MvPolynomial.aeval_weightedHomogeneousComponent
    InfiniteGrading infiniteWeights infiniteGenerators 5 p

private def absent (i : Empty) : Grading (0 : ℕ) := i.elim

example (p : MvPolynomial Empty (Grading 0)) :
    MvPolynomial.aeval (fun i : Empty => (absent i : Target))
      (MvPolynomial.weightedHomogeneousComponent (fun _ : Empty => 0) 0 p) =
      (DirectSum.decompose Grading
        (MvPolynomial.aeval (fun i : Empty => (absent i : Target)) p) 0 : Target) :=
  MvPolynomial.aeval_weightedHomogeneousComponent
    Grading (fun _ : Empty => 0) absent 0 p

example : ¬ Function.Surjective
    (MvPolynomial.aeval (fun i : Empty => (absent i : Target)) :
      MvPolynomial Empty (Grading 0) →ₐ[Grading 0] Target) := by
  intro hsurj
  obtain ⟨p, hp⟩ := hsurj (MvPolynomial.X (1 : Fin 3) : Target)
  have heval : MvPolynomial.aeval (fun i : Empty => (absent i : Target)) p ∈ Grading 0 :=
    (MvPolynomial.isWeightedHomogeneous_of_isEmpty (Grading 0) (fun _ : Empty => 0) p).aeval_mem
      Grading (fun _ : Empty => 0) absent
  rw [hp] at heval
  have hnonzero : (MvPolynomial.X (1 : Fin 3) : Target).coeff
      (Finsupp.single (1 : Fin 3) 1) ≠ 0 := by simp
  have hweight := heval hnonzero
  norm_num [weights, Finsupp.weight_single] at hweight

private abbrev ZeroTarget := MvPolynomial (Fin 1) (ZMod 1)
private abbrev ZeroGrading :=
  MvPolynomial.weightedHomogeneousSubmodule (ZMod 1) (fun _ : Fin 1 => 2)

private noncomputable instance : GradedAlgebra ZeroGrading :=
  MvPolynomial.weightedGradedAlgebra (ZMod 1) (fun _ : Fin 1 => 2)

example : Subsingleton ZeroTarget := inferInstance

private noncomputable def zeroGenerators (i : Fin 1) : ZeroGrading 2 :=
  ⟨MvPolynomial.X i, MvPolynomial.isWeightedHomogeneous_X
    (ZMod 1) (fun _ : Fin 1 => 2) i⟩

example (p : MvPolynomial (Fin 1) (ZeroGrading 0)) :
    MvPolynomial.aeval (fun i : Fin 1 => (zeroGenerators i : ZeroTarget))
      (MvPolynomial.weightedHomogeneousComponent (fun _ : Fin 1 => 2) 2 p) =
      (DirectSum.decompose ZeroGrading
        (MvPolynomial.aeval (fun i : Fin 1 => (zeroGenerators i : ZeroTarget)) p) 2 :
          ZeroTarget) := by
  exact MvPolynomial.aeval_weightedHomogeneousComponent
    ZeroGrading (fun _ : Fin 1 => 2) zeroGenerators 2 p

end WeightedEvaluationClient
