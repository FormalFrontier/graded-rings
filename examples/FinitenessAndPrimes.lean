/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import GradedRings.Noetherian
import GradedRings.HomogeneousPrime

/-! # Finite generation and contraction of homogeneous primes

For a natural-number grading, finite generation of the irrelevant ideal supplies
finite type over degree zero and, with a Noetherian degree-zero ring, Noetherianity.
The separate integer-graded example needs a positive-degree homogeneous unit;
the inverse to prime contraction uses radical extension, not plain extension.
-/

namespace GradedRingsExamples.FinitenessAndPrimes

universe u v

section Finiteness

variable {A : Type u} [CommRing A]
variable {σ : Type v} [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

private theorem noetherian_and_finite_type [IsNoetherianRing (𝒜 0)]
    (h : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.FG) :
    IsNoetherianRing A ∧ Algebra.FiniteType (𝒜 0) A :=
  ⟨GradedAlgebra.isNoetherianRing_of_gradeZero_of_irrelevant_fg 𝒜 h,
    GradedAlgebra.finiteType_of_irrelevant_fg 𝒜 h⟩

private theorem positive_generators [Algebra.FiniteType (𝒜 0) A] :
    ∃ s : Finset A,
      Ideal.span (s : Set A) = (HomogeneousIdeal.irrelevant 𝒜).toIdeal ∧
      ∀ x ∈ s, ∃ n > 0, x ∈ 𝒜 n :=
  GradedAlgebra.irrelevant_exists_finset_span_eq_of_fg 𝒜
    (GradedAlgebra.irrelevant_fg_of_finiteType 𝒜)

end Finiteness

section Primes

variable {A : Type u} [CommRing A]
variable {σ : Type v} [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℤ → σ) [GradedRing 𝒜]

private theorem prime_roundtrip {d : ℤ} (unit : Aˣ)
    (hu : (unit : A) ∈ 𝒜 d) (hd : 0 < d)
    (q : {q : Ideal (𝒜 0) // q.IsPrime}) :
    GradedRing.homogeneousPrimeEquivDegreeZeroPrime 𝒜 unit hu hd
      ((GradedRing.homogeneousPrimeEquivDegreeZeroPrime 𝒜 unit hu hd).symm q) = q :=
  (GradedRing.homogeneousPrimeEquivDegreeZeroPrime 𝒜 unit hu hd).apply_symm_apply q

end Primes

#print axioms noetherian_and_finite_type
#print axioms positive_generators
#print axioms prime_roundtrip

end GradedRingsExamples.FinitenessAndPrimes
