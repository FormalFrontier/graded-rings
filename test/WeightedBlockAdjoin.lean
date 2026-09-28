/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
module

import GradedRings.WeightedBlockAdjoin
import Mathlib.Data.ZMod.Basic

set_option warningAsError true

namespace WeightedBlockAdjoinClient

open MvPolynomial

private def mixedWeights : Fin 2 → ℕ := ![2, 3]

private theorem mixedWeights_pos : ∀ i, 0 < mixedWeights i := by decide

private noncomputable def firstExponent : Fin 2 →₀ ℕ :=
  Finsupp.single 0 6 + Finsupp.single 1 4

private noncomputable def secondExponent : Fin 2 →₀ ℕ :=
  Finsupp.single 0 3 + Finsupp.single 1 6

private theorem firstExponent_weight :
    Finsupp.weight mixedWeights firstExponent =
      2 * Finsupp.weightedBlockSize mixedWeights := by
  norm_num [firstExponent, mixedWeights, Finsupp.weightedBlockSize,
    Finsupp.weight_single, Fin.prod_univ_two]

private theorem secondExponent_weight :
    Finsupp.weight mixedWeights secondExponent =
      2 * Finsupp.weightedBlockSize mixedWeights := by
  norm_num [secondExponent, mixedWeights, Finsupp.weightedBlockSize,
    Finsupp.weight_single, Fin.prod_univ_two]

private noncomputable def mixedSum {R : Type*} [CommSemiring R] (a b : R) :
    MvPolynomial (Fin 2) R :=
  monomial firstExponent a + monomial secondExponent b

private theorem mixedSum_mem {R : Type*} [CommSemiring R] (a b : R) :
    mixedSum a b ∈ Algebra.adjoin R
      ((fun d : Fin 2 →₀ ℕ => monomial d (1 : R)) ''
        {d | Finsupp.weight mixedWeights d = Finsupp.weightedBlockSize mixedWeights}) := by
  apply IsWeightedHomogeneous.mem_adjoin_weightedBlockSize mixedWeights mixedWeights_pos 2
  exact (isWeightedHomogeneous_monomial mixedWeights firstExponent a firstExponent_weight).add
    (isWeightedHomogeneous_monomial mixedWeights secondExponent b secondExponent_weight)

private theorem zero_blocks_arbitrary_coefficients {ι R : Type*}
    [Fintype ι] [CommSemiring R] (w : ι → ℕ) (hw : ∀ i, 0 < w i) (a : R) :
    (C a : MvPolynomial ι R) ∈ Algebra.adjoin R
      ((fun d : ι →₀ ℕ => monomial d (1 : R)) ''
        {d | Finsupp.weight w d = Finsupp.weightedBlockSize w}) := by
  apply IsWeightedHomogeneous.mem_adjoin_weightedBlockSize w hw 0
  simpa using isWeightedHomogeneous_C w a

private theorem empty_indices_constant {R : Type*} [CommSemiring R] (a : R) :
    (C a : MvPolynomial PEmpty R) ∈ Algebra.adjoin R
      ((fun d : PEmpty →₀ ℕ => monomial d (1 : R)) ''
        {d | Finsupp.weight (fun _ : PEmpty => 1) d =
          Finsupp.weightedBlockSize (fun _ : PEmpty => 1)}) := by
  exact zero_blocks_arbitrary_coefficients (fun _ : PEmpty => 1) (by intro i; exact i.elim) a

private theorem empty_indices_zero {R : Type*} [CommSemiring R] (k : ℕ) :
    (0 : MvPolynomial PEmpty R) ∈ Algebra.adjoin R
      ((fun d : PEmpty →₀ ℕ => monomial d (1 : R)) ''
        {d | Finsupp.weight (fun _ : PEmpty => 1) d =
          Finsupp.weightedBlockSize (fun _ : PEmpty => 1)}) := by
  apply IsWeightedHomogeneous.mem_adjoin_weightedBlockSize (fun _ : PEmpty => 1)
    (by intro i; exact i.elim) k
  exact isWeightedHomogeneous_zero R _ _

private theorem natural_coefficients :
    mixedSum (7 : ℕ) 11 ∈ Algebra.adjoin ℕ
      ((fun d : Fin 2 →₀ ℕ => monomial d (1 : ℕ)) ''
        {d | Finsupp.weight mixedWeights d = Finsupp.weightedBlockSize mixedWeights}) :=
  mixedSum_mem 7 11

private theorem zero_ring_coefficients :
    mixedSum (0 : ZMod 1) 0 ∈ Algebra.adjoin (ZMod 1)
      ((fun d : Fin 2 →₀ ℕ => monomial d (1 : ZMod 1)) ''
        {d | Finsupp.weight mixedWeights d = Finsupp.weightedBlockSize mixedWeights}) :=
  mixedSum_mem 0 0

private theorem nilpotent_coefficients :
    (2 : ZMod 4) * 2 = 0 ∧
      mixedSum (2 : ZMod 4) 2 ∈ Algebra.adjoin (ZMod 4)
        ((fun d : Fin 2 →₀ ℕ => monomial d (1 : ZMod 4)) ''
          {d | Finsupp.weight mixedWeights d = Finsupp.weightedBlockSize mixedWeights}) := by
  exact ⟨by decide, mixedSum_mem 2 2⟩

private theorem finite_generator_image {ι R : Type*}
    [Fintype ι] [CommSemiring R] (w : ι → ℕ) (hw : ∀ i, 0 < w i) :
    Set.Finite ((fun d : ι →₀ ℕ => monomial d (1 : R)) ''
      {d | Finsupp.weight w d = Finsupp.weightedBlockSize w}) := by
  exact (Finsupp.finite_of_nat_weight_eq w (fun i => Nat.ne_of_gt (hw i)) _).image _

end WeightedBlockAdjoinClient
