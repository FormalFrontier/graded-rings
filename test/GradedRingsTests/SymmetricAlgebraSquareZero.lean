/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GradedRings.SymmetricAlgebraSquareZero
public import Mathlib.Algebra.Module.PUnit
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.RingTheory.Finiteness.Cardinality

/-!
# First-order symmetric-algebra quotient examples

These computations exercise zero modules and zero rings, a nonfree torsion
module, and a free module on infinitely many generators.
-/

set_option warningAsError true

@[expose] public section

open scoped TrivSqZeroExt

namespace GradedRingsTests.SymmetricAlgebraSquareZero

section MapInterface

variable {R : Type*} {M : Type*} {N : Type*}
  [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

private theorem generic_quotient_product
    (x y : SymmetricAlgebra R M ⧸
      (SymmetricAlgebra.augmentationIdeal (R := R) (M := M)) ^ 2) :
    SymmetricAlgebra.squareZeroQuotientEquiv (R := R) (M := M) (x * y) =
      SymmetricAlgebra.squareZeroQuotientEquiv (R := R) (M := M) x *
        SymmetricAlgebra.squareZeroQuotientEquiv (R := R) (M := M) y :=
  (SymmetricAlgebra.squareZeroQuotientEquiv (R := R) (M := M)).map_mul x y

private theorem generic_ideal_image
    (x : (SymmetricAlgebra.augmentationIdeal (R := R) (M := M)).cotangentIdeal) :
    SymmetricAlgebra.squareZeroQuotientEquiv (R := R) (M := M) x ∈
      TrivSqZeroExt.kerIdeal R M := by
  have mapped : SymmetricAlgebra.squareZeroQuotientEquiv (R := R) (M := M) x ∈
      Ideal.map (SymmetricAlgebra.squareZeroQuotientEquiv
        (R := R) (M := M)).toRingHom
        (SymmetricAlgebra.augmentationIdeal (R := R) (M := M)).cotangentIdeal :=
    Ideal.mem_map_of_mem _ x.property
  rw [SymmetricAlgebra.squareZeroQuotientEquiv_cotangentIdeal] at mapped
  exact mapped

private theorem generic_whole_map (f : M →ₗ[R] N)
    (x : SymmetricAlgebra R M ⧸
      (SymmetricAlgebra.augmentationIdeal (R := R) (M := M)) ^ 2) :
    (TrivSqZeroExt.map f)
      (SymmetricAlgebra.squareZeroQuotientEquiv (R := R) (M := M) x) =
        SymmetricAlgebra.squareZeroQuotientEquiv (R := R) (M := N)
          (SymmetricAlgebra.squareZeroQuotientMap f x) := by
  exact (congrArg (fun g => g x)
    (SymmetricAlgebra.squareZeroQuotientEquiv_naturality f)).symm

private theorem integer_quotient_product
    (x y : SymmetricAlgebra ℤ ℤ ⧸
      (SymmetricAlgebra.augmentationIdeal (R := ℤ) (M := ℤ)) ^ 2) :
    SymmetricAlgebra.squareZeroQuotientEquiv (R := ℤ) (M := ℤ) (x * y) =
      SymmetricAlgebra.squareZeroQuotientEquiv (R := ℤ) (M := ℤ) x *
        SymmetricAlgebra.squareZeroQuotientEquiv (R := ℤ) (M := ℤ) y :=
  (SymmetricAlgebra.squareZeroQuotientEquiv (R := ℤ) (M := ℤ)).map_mul x y

private theorem integer_ideal_image
    (x : (SymmetricAlgebra.augmentationIdeal (R := ℤ) (M := ℤ)).cotangentIdeal) :
    SymmetricAlgebra.squareZeroQuotientEquiv (R := ℤ) (M := ℤ) x ∈
      TrivSqZeroExt.kerIdeal ℤ ℤ := by
  have mapped : SymmetricAlgebra.squareZeroQuotientEquiv (R := ℤ) (M := ℤ) x ∈
      Ideal.map (SymmetricAlgebra.squareZeroQuotientEquiv
        (R := ℤ) (M := ℤ)).toRingHom
        (SymmetricAlgebra.augmentationIdeal (R := ℤ) (M := ℤ)).cotangentIdeal :=
    Ideal.mem_map_of_mem _ x.property
  rw [SymmetricAlgebra.squareZeroQuotientEquiv_cotangentIdeal] at mapped
  exact mapped

private theorem integer_whole_map
    (x : SymmetricAlgebra ℤ ℤ ⧸
      (SymmetricAlgebra.augmentationIdeal (R := ℤ) (M := ℤ)) ^ 2) :
    (TrivSqZeroExt.map ((2 : ℤ) • LinearMap.id))
      (SymmetricAlgebra.squareZeroQuotientEquiv (R := ℤ) (M := ℤ) x) =
        SymmetricAlgebra.squareZeroQuotientEquiv (R := ℤ) (M := ℤ)
          (SymmetricAlgebra.squareZeroQuotientMap ((2 : ℤ) • LinearMap.id) x) := by
  exact (congrArg (fun g => g x)
    (SymmetricAlgebra.squareZeroQuotientEquiv_naturality
      ((2 : ℤ) • LinearMap.id))).symm

end MapInterface

section ZeroModule

variable {R : Type*} [CommRing R]

theorem zero_cotangent
    (x : (SymmetricAlgebra.augmentationIdeal (R := R) (M := PUnit)).Cotangent) :
    x = 0 :=
  (SymmetricAlgebra.augmentationCotangentEquiv (R := R) (M := PUnit)).injective
    (Subsingleton.elim _ _)

private theorem zero_module_only_scalars
    (x : SymmetricAlgebra R PUnit ⧸
      (SymmetricAlgebra.augmentationIdeal (R := R) (M := PUnit)) ^ 2) :
    ∃ r : R,
      x = (SymmetricAlgebra.squareZeroQuotientEquiv (R := R) (M := PUnit)).symm
        (TrivSqZeroExt.inl r) := by
  let comparison := SymmetricAlgebra.squareZeroQuotientEquiv (R := R) (M := PUnit)
  refine ⟨(comparison x).fst, comparison.injective ?_⟩
  rw [comparison.apply_symm_apply]
  exact TrivSqZeroExt.ext rfl (Subsingleton.elim _ _)

end ZeroModule

private theorem zero_ring_projection
    (x : SymmetricAlgebra (ZMod 1) PUnit) :
    TrivSqZeroExt.fstHom (ZMod 1) (ZMod 1) PUnit
      (SymmetricAlgebra.squareZeroQuotientEquiv (R := ZMod 1) (M := PUnit)
        (Ideal.Quotient.mk _ x)) = 0 := by
  exact Subsingleton.elim _ _

private def torsionClass :
    SymmetricAlgebra ℤ (ZMod 2) ⧸
      (SymmetricAlgebra.augmentationIdeal (R := ℤ) (M := ZMod 2)) ^ 2 :=
  Ideal.Quotient.mk _ (SymmetricAlgebra.ι ℤ (ZMod 2) 1)

private theorem torsionClass_ne_zero : torsionClass ≠ 0 := by
  intro equality
  let comparison := SymmetricAlgebra.squareZeroQuotientEquiv (R := ℤ) (M := ZMod 2)
  have scalarZero : comparison.symm (TrivSqZeroExt.inr (0 : ZMod 2)) = 0 := by simp
  have scalarOne : comparison.symm (TrivSqZeroExt.inr (1 : ZMod 2)) = torsionClass := by
    simp [torsionClass, comparison]
  have imageEquality : TrivSqZeroExt.inr (1 : ZMod 2) =
      TrivSqZeroExt.inr (0 : ZMod 2) :=
    comparison.symm.injective (scalarOne.trans (equality.trans scalarZero.symm))
  have one_ne_zero : (1 : ZMod 2) ≠ 0 := by decide
  exact one_ne_zero (congrArg TrivSqZeroExt.snd imageEquality)

private theorem torsionClass_sq_zero : torsionClass * torsionClass = 0 := by
  change Ideal.Quotient.mk _
    (SymmetricAlgebra.ι ℤ (ZMod 2) 1 * SymmetricAlgebra.ι ℤ (ZMod 2) 1) = 0
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  change (SymmetricAlgebra.ι ℤ (ZMod 2) 1 * SymmetricAlgebra.ι ℤ (ZMod 2) 1) ∈
    (SymmetricAlgebra.augmentationIdeal (R := ℤ) (M := ZMod 2)) ^ 2
  rw [pow_two]
  exact Ideal.mul_mem_mul
      (SymmetricAlgebra.ι_mem_augmentationIdeal (1 : ZMod 2))
      (SymmetricAlgebra.ι_mem_augmentationIdeal (1 : ZMod 2))

private theorem torsionClass_two_smul : (2 : ℤ) • torsionClass = 0 := by
  rw [two_smul]
  change Ideal.Quotient.mk _ (SymmetricAlgebra.ι ℤ (ZMod 2) (1 : ZMod 2)) +
    Ideal.Quotient.mk _ (SymmetricAlgebra.ι ℤ (ZMod 2) (1 : ZMod 2)) = 0
  rw [← (Ideal.Quotient.mk _).map_add,
    ← (SymmetricAlgebra.ι ℤ (ZMod 2)).map_add]
  have torsion : (1 : ZMod 2) + 1 = 0 := by decide
  simp [torsion]

private noncomputable def infiniteClass (index : ℕ) :
    SymmetricAlgebra ℤ (ℕ →₀ ℤ) ⧸
      (SymmetricAlgebra.augmentationIdeal (R := ℤ) (M := ℕ →₀ ℤ)) ^ 2 :=
  Ideal.Quotient.mk _
    (SymmetricAlgebra.ι ℤ (ℕ →₀ ℤ) (Finsupp.single index 1))

private theorem infiniteClass_distinct : infiniteClass 0 ≠ infiniteClass 1 := by
  intro equality
  have imageEquality := congrArg
    (fun value : TrivSqZeroExt ℤ (ℕ →₀ ℤ) => value.snd)
    (congrArg (SymmetricAlgebra.squareZeroQuotientEquiv (R := ℤ) (M := ℕ →₀ ℤ))
      equality)
  have coordinateEquality := congrArg (fun value : ℕ →₀ ℤ => value 0)
    (by simpa [infiniteClass] using imageEquality)
  norm_num at coordinateEquality

private theorem infiniteClass_product_zero : infiniteClass 0 * infiniteClass 1 = 0 := by
  change Ideal.Quotient.mk _
    (SymmetricAlgebra.ι ℤ (ℕ →₀ ℤ) (Finsupp.single 0 1) *
      SymmetricAlgebra.ι ℤ (ℕ →₀ ℤ) (Finsupp.single 1 1)) = 0
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  change (SymmetricAlgebra.ι ℤ (ℕ →₀ ℤ) (Finsupp.single 0 1) *
      SymmetricAlgebra.ι ℤ (ℕ →₀ ℤ) (Finsupp.single 1 1)) ∈
    (SymmetricAlgebra.augmentationIdeal (R := ℤ) (M := ℕ →₀ ℤ)) ^ 2
  rw [pow_two]
  exact Ideal.mul_mem_mul
      (SymmetricAlgebra.ι_mem_augmentationIdeal (Finsupp.single 0 1 : ℕ →₀ ℤ))
      (SymmetricAlgebra.ι_mem_augmentationIdeal (Finsupp.single 1 1 : ℕ →₀ ℤ))

private theorem infinitely_many_generators : ¬ Module.Finite ℤ (ℕ →₀ ℤ) :=
  Module.not_finite_of_infinite_basis (Finsupp.basisSingleOne (R := ℤ))

end GradedRingsTests.SymmetricAlgebraSquareZero

end
