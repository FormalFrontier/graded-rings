/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier contributors (Hive Task hive-request-5f3d8b70c36747cebf20677044967e35d889fc0d,
  UID c2ffb0a9-dadb-4457-ab90-47771a830889)
-/
module

public import GradedRings.HomogeneousLifts

@[expose] public section

set_option warningAsError true

namespace GradedRingsTest.HomogeneousLifts

variable {A B σ τ : Type*} [CommRing A] [CommRing B]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]

example (f : 𝒜 →+*ᵍ ℬ) (hf : Function.Surjective f) (m : ℕ) :
    Function.Surjective (f.gradedAddHom m) :=
  f.surjective_gradedAddHom 𝒜 ℬ hf m

variable {S υ : Type*} [CommRing S] [SetLike υ S] [AddSubgroupClass υ S]
  (𝒮 : ℕ → υ) [GradedRing 𝒮]

example {m : ℕ} {s : S} (hs : s ∈ 𝒮 m)
    (hgen : Algebra.adjoin (𝒮 0) (𝒮 1 : Set S) = ⊤) :
    ∃ p : MvPolynomial (𝒮 1) (𝒮 0), p.IsHomogeneous m ∧
      MvPolynomial.aeval (fun a : 𝒮 1 => (a : S)) p = s :=
  MvPolynomial.exists_isHomogeneous_aeval 𝒮 hgen hs

example (s : 𝒮 0) :
    ∃ p : MvPolynomial (𝒮 1) (𝒮 0), p.IsHomogeneous 0 ∧
      MvPolynomial.aeval (fun a : 𝒮 1 => (a : S)) p = (s : S) := by
  refine ⟨MvPolynomial.C s, MvPolynomial.isHomogeneous_C _ _, ?_⟩
  simp [SetLike.GradeZero.algebraMap_apply]

section FreePolynomial

variable {R I : Type*} [CommRing R]

private theorem free_polynomial_generated :
    letI : GradedAlgebra (MvPolynomial.homogeneousSubmodule I R) :=
      MvPolynomial.gradedAlgebra
    Algebra.adjoin (MvPolynomial.homogeneousSubmodule I R 0)
      (MvPolynomial.homogeneousSubmodule I R 1 : Set (MvPolynomial I R)) = ⊤ := by
  classical
  let _ : GradedAlgebra (MvPolynomial.homogeneousSubmodule I R) :=
    MvPolynomial.gradedAlgebra
  apply top_unique
  intro p _
  induction p using MvPolynomial.induction_on with
  | C r =>
    have hr : MvPolynomial.C r ∈ MvPolynomial.homogeneousSubmodule I R 0 :=
      MvPolynomial.isHomogeneous_C _ _
    simpa only [SetLike.GradeZero.algebraMap_apply] using
      (Algebra.adjoin (MvPolynomial.homogeneousSubmodule I R 0)
        (MvPolynomial.homogeneousSubmodule I R 1 : Set (MvPolynomial I R))).algebraMap_mem
          ⟨MvPolynomial.C r, hr⟩
  | add p q hp hq => exact Subalgebra.add_mem _ (hp (by trivial)) (hq (by trivial))
  | mul_X p i hp =>
    exact Subalgebra.mul_mem _ (hp (by trivial))
      (Algebra.subset_adjoin (MvPolynomial.isHomogeneous_X R i))

example {m : ℕ} {p : MvPolynomial I R} (hp : p.IsHomogeneous m) :
    ∃ q : MvPolynomial (MvPolynomial.homogeneousSubmodule I R 1)
        (MvPolynomial.homogeneousSubmodule I R 0), q.IsHomogeneous m ∧
      MvPolynomial.aeval (fun a : MvPolynomial.homogeneousSubmodule I R 1 =>
        (a : MvPolynomial I R)) q = p := by
  let _ : GradedAlgebra (MvPolynomial.homogeneousSubmodule I R) :=
    MvPolynomial.gradedAlgebra
  exact MvPolynomial.exists_isHomogeneous_aeval
    (MvPolynomial.homogeneousSubmodule I R) free_polynomial_generated hp

end FreePolynomial

end GradedRingsTest.HomogeneousLifts
