/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier contributor (Hive Task hive-request-45b307ef0b08baacd6a851dadec8faa23ee22d69,
  UID 65fe43bb-2c1b-4320-b724-f8b1f1fa063a)
-/
module

public import GradedRings.VeroneseDegreeOne
public import Mathlib.Data.ZMod.Basic

@[expose] public section

set_option warningAsError true

namespace GradedRingsTest.VeroneseDegreeOne

open GradedRing.Veronese

universe u v

variable {S : Type u} [CommRing S] {σ : Type v} [SetLike σ S]
  [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮]

example (hgen : Algebra.adjoin (𝒮 0) (𝒮 1 : Set S) = ⊤) :
    Algebra.adjoin (component 𝒮 1 0)
      (component 𝒮 1 1 : Set (VeroneseRing 𝒮 1)) = ⊤ :=
  adjoin_component_one_eq_top 𝒮 1 (by decide) hgen

example (hgen : Algebra.adjoin (𝒮 0) (𝒮 1 : Set S) = ⊤) :
    Algebra.adjoin (component 𝒮 2 0)
      (component 𝒮 2 1 : Set (VeroneseRing 𝒮 2)) = ⊤ :=
  adjoin_component_one_eq_top 𝒮 2 (by decide) hgen

example (n : ℕ) (hn : 0 < n) (r : 𝒮 0) :
    inclusion 𝒮 n (algebraMap (component 𝒮 n 0) (VeroneseRing 𝒮 n)
      ((zeroRingEquiv 𝒮 n hn).symm r)) = algebraMap (𝒮 0) S r := by
  rw [SetLike.GradeZero.algebraMap_apply, ← zeroRingEquiv_apply 𝒮 n hn]
  simp only [RingEquiv.apply_symm_apply, SetLike.GradeZero.algebraMap_apply]

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

example :
    letI : GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin 2) (ZMod 4)) :=
      MvPolynomial.gradedAlgebra
    Algebra.adjoin
    (component (MvPolynomial.homogeneousSubmodule (Fin 2) (ZMod 4)) 2 0)
    (component (MvPolynomial.homogeneousSubmodule (Fin 2) (ZMod 4)) 2 1 :
      Set (VeroneseRing (MvPolynomial.homogeneousSubmodule (Fin 2) (ZMod 4)) 2)) =
      ⊤ := by
  let _ : GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin 2) (ZMod 4)) :=
    MvPolynomial.gradedAlgebra
  exact adjoin_component_one_eq_top _ 2 (by decide)
    (free_polynomial_generated (I := Fin 2) (R := ZMod 4))

example :
    letI : GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin 2) (ZMod 1)) :=
      MvPolynomial.gradedAlgebra
    Algebra.adjoin
    (component (MvPolynomial.homogeneousSubmodule (Fin 2) (ZMod 1)) 2 0)
    (component (MvPolynomial.homogeneousSubmodule (Fin 2) (ZMod 1)) 2 1 :
      Set (VeroneseRing (MvPolynomial.homogeneousSubmodule (Fin 2) (ZMod 1)) 2)) =
      ⊤ := by
  let _ : GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin 2) (ZMod 1)) :=
    MvPolynomial.gradedAlgebra
  exact adjoin_component_one_eq_top _ 2 (by decide)
    (free_polynomial_generated (I := Fin 2) (R := ZMod 1))

end FreePolynomial

end GradedRingsTest.VeroneseDegreeOne
