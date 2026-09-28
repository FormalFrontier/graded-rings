/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import GradedRings.WeightedBlocks

set_option warningAsError true

namespace GradedRingsTest.WeightedBlocks

private def mixedWeights : Fin 2 → ℕ := ![2, 3]

private theorem mixedWeights_pos : ∀ i, 0 < mixedWeights i := by
  decide

private noncomputable def mixedVector : Fin 2 →₀ ℕ :=
  Finsupp.single 0 6 + Finsupp.single 1 4

private theorem mixedVector_weight :
    Finsupp.weight mixedWeights mixedVector =
      2 * Finsupp.weightedBlockSize mixedWeights := by
  norm_num [mixedVector, mixedWeights, Finsupp.weightedBlockSize,
    Finsupp.weight_single, Fin.prod_univ_two]

private theorem mixedVector_two_blocks :
    ∃ blocks : Fin 2 → (Fin 2 →₀ ℕ),
      (∑ j, blocks j) = mixedVector ∧
        ∀ j, Finsupp.weight mixedWeights (blocks j) = 12 := by
  obtain ⟨blocks, hsum, hweight⟩ :=
    Finsupp.exists_weightedBlocks mixedWeights mixedWeights_pos 2 mixedVector
      mixedVector_weight
  refine ⟨blocks, hsum, ?_⟩
  intro j
  simpa [mixedWeights, Finsupp.weightedBlockSize, Fin.prod_univ_two]
    using hweight j

private theorem one_block (f : Fin 2 →₀ ℕ)
    (hf : Finsupp.weight mixedWeights f = Finsupp.weightedBlockSize mixedWeights) :
    ∃ blocks : Fin 1 → (Fin 2 →₀ ℕ),
      (∑ j, blocks j) = f ∧
        ∀ j, Finsupp.weight mixedWeights (blocks j) =
          Finsupp.weightedBlockSize mixedWeights := by
  exact Finsupp.exists_weightedBlocks mixedWeights mixedWeights_pos 1 f (by simpa using hf)

private theorem zero_blocks :
    ∃ blocks : Fin 0 → (Fin 2 →₀ ℕ),
      (∑ j, blocks j) = 0 ∧
        ∀ j, Finsupp.weight mixedWeights (blocks j) =
          Finsupp.weightedBlockSize mixedWeights := by
  exact Finsupp.exists_weightedBlocks mixedWeights mixedWeights_pos 0 0 (by simp)

private theorem empty_indices :
    ∃ blocks : Fin 0 → (PEmpty →₀ ℕ),
      (∑ j, blocks j) = 0 ∧
        ∀ j, Finsupp.weight (fun i : PEmpty => isEmptyElim i) (blocks j) =
          Finsupp.weightedBlockSize (fun i : PEmpty => isEmptyElim i) := by
  exact Finsupp.exists_weightedBlocks (fun i : PEmpty => isEmptyElim i)
    (fun i => isEmptyElim i) 0 0 (by simp)

private theorem empty_indices_positive (f : PEmpty →₀ ℕ) :
    Finsupp.weight (fun i : PEmpty => isEmptyElim i) f ≠
      Finsupp.weightedBlockSize (fun i : PEmpty => isEmptyElim i) := by
  have hf : f = 0 := by
    ext i
    exact isEmptyElim i
  simp [hf, Finsupp.weightedBlockSize]

private theorem singleton_blocks :
    ∃ blocks : Fin 3 → (PUnit →₀ ℕ),
      (∑ j, blocks j) = Finsupp.single PUnit.unit 3 ∧
        ∀ j, Finsupp.weight (fun _ : PUnit => 5) (blocks j) =
          Finsupp.weightedBlockSize (fun _ : PUnit => 5) := by
  apply Finsupp.exists_weightedBlocks (fun _ : PUnit => 5)
    (by intro _; norm_num) 3 (Finsupp.single PUnit.unit 3)
  norm_num [Finsupp.weight_single, Finsupp.weightedBlockSize]

private theorem equal_unit_weights :
    ∃ blocks : Fin 2 → (Fin 3 →₀ ℕ),
      (∑ j, blocks j) = (Finsupp.single 0 3 + Finsupp.single 1 3) ∧
        ∀ j, Finsupp.weight (fun _ : Fin 3 => 1) (blocks j) =
          Finsupp.weightedBlockSize (fun _ : Fin 3 => 1) := by
  apply Finsupp.exists_weightedBlocks (fun _ : Fin 3 => 1)
    (by intro _; norm_num) 2 (Finsupp.single 0 3 + Finsupp.single 1 3)
  norm_num [Finsupp.weight_single, Finsupp.weightedBlockSize]

end GradedRingsTest.WeightedBlocks
