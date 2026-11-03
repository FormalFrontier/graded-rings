/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GradedRings.ReesModule.ConstantCoeff
public import GradedRings.ReesModule.QuotientAction
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Tensor products and degree zero of an associated graded module

The constant Rees-module singleton induces an `R`-linear map from `M ⧸ (I • ⊤)`
to the associated graded module. Taking the degree-zero coefficient is a left
inverse to this map. Scalar multiplication by the quotient Rees algebra then
induces a linear map from its tensor product with `M ⧸ (I • ⊤)` to the associated
graded module. This tensor map is surjective: Rees monomials acting on constants
generate every homogeneous singleton.

All maps use the Rees-module representatives and the quotient Rees action on the
associated graded module.
-/

@[expose] public section

universe u v

open scoped TensorProduct

namespace Ideal.AssociatedGradedModule

variable {R : Type u} [CommRing R] (I : Ideal R)
variable (M : Type v) [AddCommGroup M] [Module R M]

local notation "B" => reesAlgebra I
local notation "J" => Ideal.map (algebraMap R B) I
local notation "C" => B ⧸ J
local notation "S" => Ideal.Filtration.submodule (I.stableFiltration (⊤ : Submodule R M))
local notation "G" => Ideal.AssociatedGradedModule I M
local notation "Q" => M ⧸ (I • (⊤ : Submodule R M))

/-- The degree-zero map from the coefficient quotient to the associated graded
module, induced by constant Rees-module singletons. -/
noncomputable def constant : Q →ₗ[R] G := by
  let f : M →ₗ[R] G :=
    ((mk I M).restrictScalars R).comp
      (LinearMap.codRestrict (Submodule.restrictScalars R S)
        (PolynomialModule.lsingle R 0)
        (fun m => single_mem I M 0 m (by simp)))
  refine (I • (⊤ : Submodule R M)).liftQ f ?_
  apply Submodule.smul_le.mpr
  intro r hr m _
  change f (r • m) = 0
  rw [map_smul]
  have hrC : algebraMap R C r = 0 := by
    rw [IsScalarTower.algebraMap_apply R B C]
    change Ideal.Quotient.mk J (algebraMap R B r) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hr)
  calc
    r • f m = (algebraMap R C r) • f m :=
      (IsScalarTower.algebraMap_smul C r (f m)).symm
    _ = 0 := by
      rw [hrC]
      exact zero_smul C (f m)

/-- A represented coefficient class maps to the class of its constant singleton. -/
@[simp]
theorem constant_mk (m : M) :
    constant I M (Submodule.Quotient.mk m : Q) =
      mk I M ⟨PolynomialModule.single R 0 m, single_mem I M 0 m (by simp)⟩ := by
  rfl

/-- The degree-zero coefficient is a left inverse to the constant map. -/
@[simp]
theorem constantCoeff_constant (q : Q) :
    constantCoeff I M (constant I M q) = q := by
  refine Submodule.Quotient.induction_on (I • (⊤ : Submodule R M)) q ?_
  intro m
  rw [constant_mk]
  exact constantCoeff_single_zero I M m

/-- The quotient Rees algebra acts on degree-zero classes to give a linear map
from its tensor product with the coefficient quotient to the associated graded
module. -/
noncomputable def tensorProductTo : C ⊗[R] Q →ₗ[C] G :=
  TensorProduct.AlgebraTensorModule.lift
    { toFun := fun c =>
        { toFun := fun q => c • constant I M q
          map_add' := fun q q' => by
            rw [map_add, smul_add]
          map_smul' := fun r q => by
            rw [map_smul]
            exact smul_comm c r (constant I M q) }
      map_add' := fun c d =>
        LinearMap.ext fun q => add_smul c d (constant I M q)
      map_smul' := fun c d =>
        LinearMap.ext fun q => mul_smul c d (constant I M q) }

/-- On a pure tensor, the tensor map is scalar multiplication of a degree-zero
class. -/
@[simp]
theorem tensorProductTo_tmul (c : C) (q : Q) :
    tensorProductTo I M (c ⊗ₜ[R] q) = c • constant I M q := by
  rfl

/-- The tensor map on a pure tensor with a represented coefficient class. -/
theorem tensorProductTo_tmul_mk (c : C) (m : M) :
    tensorProductTo I M (c ⊗ₜ[R] (Submodule.Quotient.mk m : Q)) =
      c • mk I M
        ⟨PolynomialModule.single R 0 m, single_mem I M 0 m (by simp)⟩ := by
  rw [tensorProductTo_tmul, constant_mk]

/-- With both factors represented, the tensor map is induced by the Rees
algebra action on the constant Rees-module singleton. -/
theorem tensorProductTo_mk_tmul_mk (b : B) (m : M) :
    tensorProductTo I M
        ((Ideal.Quotient.mk J b : C) ⊗ₜ[R] (Submodule.Quotient.mk m : Q)) =
      mk I M (b •
        (⟨PolynomialModule.single R 0 m, single_mem I M 0 m (by simp)⟩ : S)) := by
  rw [tensorProductTo_tmul_mk]
  change (algebraMap B C b) • mk I M
      (⟨PolynomialModule.single R 0 m, single_mem I M 0 m (by simp)⟩ : S) = _
  rw [IsScalarTower.algebraMap_smul]
  exact ((mk I M).map_smul b
    (⟨PolynomialModule.single R 0 m, single_mem I M 0 m (by simp)⟩ : S)).symm

/-- A Rees monomial acting on a represented constant gives the class of the
corresponding singleton. -/
theorem tensorProductTo_monomial_tmul_mk (n : ℕ) (a : R) (ha : a ∈ I ^ n) (m : M) :
    tensorProductTo I M
        ((Ideal.Quotient.mk J
          ⟨Polynomial.monomial n a, reesAlgebra.monomial_mem.mpr ha⟩ : C) ⊗ₜ[R]
          (Submodule.Quotient.mk m : Q)) =
      mk I M ⟨PolynomialModule.single R n (a • m),
        single_mem I M n (a • m) (Submodule.smul_mem_smul ha (by simp))⟩ := by
  rw [tensorProductTo_mk_tmul_mk]
  apply congrArg (mk I M)
  apply Subtype.ext
  change Polynomial.monomial n a • PolynomialModule.single R 0 m =
    PolynomialModule.single R n (a • m)
  rw [PolynomialModule.monomial_smul_single, Nat.add_zero]

private theorem mk_single_mem_range_tensorProductTo
    (n : ℕ) (m : M) (hm : m ∈ (I ^ n) • (⊤ : Submodule R M)) :
    mk I M ⟨PolynomialModule.single R n m, single_mem I M n m hm⟩ ∈
      LinearMap.range (tensorProductTo I M) := by
  refine Submodule.smul_induction_on' hm ?_ ?_
  · intro a ha m _
    refine ⟨(Ideal.Quotient.mk J
      ⟨Polynomial.monomial n a, reesAlgebra.monomial_mem.mpr ha⟩ : C) ⊗ₜ[R]
        (Submodule.Quotient.mk m : Q), ?_⟩
    exact tensorProductTo_monomial_tmul_mk I M n a ha m
  · intro x hx y hy hxrange hyrange
    have hsum :
        (⟨PolynomialModule.single R n (x + y),
          single_mem I M n (x + y) (add_mem hx hy)⟩ : S) =
        (⟨PolynomialModule.single R n x, single_mem I M n x hx⟩ : S) +
          ⟨PolynomialModule.single R n y, single_mem I M n y hy⟩ := by
      apply Subtype.ext
      exact (PolynomialModule.lsingle R n).map_add x y
    rw [hsum, map_add]
    exact (LinearMap.range (tensorProductTo I M)).add_mem hxrange hyrange

private theorem mk_mem_range_tensorProductTo (p : S) :
    mk I M p ∈ LinearMap.range (tensorProductTo I M) := by
  classical
  have hp (n : ℕ) : (p : PolynomialModule R M).coeff n ∈
      (I ^ n) • (⊤ : Submodule R M) :=
    ((I.stableFiltration (⊤ : Submodule R M)).mem_submodule _).1 p.property n
  let s : ℕ → S := fun n =>
    ⟨PolynomialModule.single R n ((p : PolynomialModule R M).coeff n),
      single_mem I M n ((p : PolynomialModule R M).coeff n) (hp n)⟩
  have hsum : (∑ n ∈ (p : PolynomialModule R M).coeff.support, s n) = p := by
    apply Subtype.ext
    change (Submodule.subtype S) (∑ n ∈ (p : PolynomialModule R M).coeff.support, s n) =
      (p : PolynomialModule R M)
    rw [map_sum]
    change (∑ n ∈ (p : PolynomialModule R M).coeff.support,
      PolynomialModule.single R n ((p : PolynomialModule R M).coeff n)) =
        (p : PolynomialModule R M)
    apply PolynomialModule.coeff_injective
    rw [PolynomialModule.coeff_sum]
    simpa only [PolynomialModule.coeff_single, Finsupp.sum] using
      (Finsupp.sum_single ((p : PolynomialModule R M).coeff))
  rw [← hsum, map_sum]
  exact (LinearMap.range (tensorProductTo I M)).sum_mem fun n _ =>
    mk_single_mem_range_tensorProductTo I M n ((p : PolynomialModule R M).coeff n) (hp n)

/-- The associated graded module is generated over the quotient Rees algebra by
its represented degree-zero classes. Equivalently, the canonical tensor map is
surjective for every ideal and every module. -/
theorem tensorProductTo_surjective : Function.Surjective (tensorProductTo I M) := by
  intro z
  change z ∈ LinearMap.range (tensorProductTo I M)
  induction z using Submodule.Quotient.induction_on with
  | H p =>
      rw [show (Submodule.Quotient.mk p : G) = mk I M p from (mk_apply I M p).symm]
      exact mk_mem_range_tensorProductTo I M p

end Ideal.AssociatedGradedModule
