/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GradedRings.FilteredAssociatedGraded.Coefficients
public import GradedRings.ReesAlgebra.PowerQuotientAlgebra

/-!
# The ideal-power quotient algebra acting on an associated graded module

The direct sum of the ideal-power quotients acts on the associated graded of an
integer-indexed ideal-compatible filtration. The action is restriction of the
quotient Rees action along `reesAlgebra.powerQuotientSumAlgEquiv`. It retains the
associated graded carrier, additive group and original actions of `R`, `R ⧸ I`
and the quotient Rees algebra.

The whole-scalar computation and the homogeneous insertion computation describe
the action without unfolding its construction. On representatives, a coefficient
in degree `q` sends degree `n` to degree `n + q`. The coefficient actions of `R`
and `R ⧸ I` form scalar towers with this action.

Quotient-Rees-linear maps between associated gradeds commute with these scalars.
The existing maps and linear equivalences can therefore use Mathlib's
`restrictScalars` constructors, retaining their forward and inverse functions.

## Implementation notes

The only module construction is Mathlib's `Module.compHom`; no new multiplication
or endomorphism representation is constructed. No normalization of the filtration
or restriction on its integer degrees is imposed.

## References

* Mathlib's `Module.compHom`, `IsScalarTower.of_algebraMap_smul`,
  `LinearMap.CompatibleSMul` and scalar-restriction constructors.
* K. Fujiwara and F. Kato, *Foundations of Rigid Geometry I*, arXiv:1308.4734v5,
  Chapter 0, §7.5, for the quotient-Rees description of the associated graded action.
-/

@[expose] public section

universe u v w

namespace Ideal.IntFiltration

variable {R : Type u} [CommRing R] {I : Ideal R}
variable {M : Type v} [AddCommGroup M] [Module R M] (F : I.IntFiltration M)

local notation "A" => R ⧸ I
local notation "C" => reesAlgebra I ⧸ I.map (algebraMap R (reesAlgebra I))
local notation "D" => reesAlgebra.powerQuotientSum I
local notation "G" => F.AssociatedGraded

/-- The ideal-power quotient sum acts by restriction of the quotient Rees action. -/
noncomputable instance modulePowerQuotientSum : Module D G :=
  Module.compHom F.AssociatedGraded (reesAlgebra.powerQuotientSumAlgEquiv I).toRingHom

/-- Every scalar acts through its image in the quotient Rees algebra. -/
theorem powerQuotientSum_smul (d : D) (x : G) :
    d • x = (reesAlgebra.powerQuotientSumAlgEquiv I d : C) • x :=
  rfl

section ScalarRestriction

variable {N : Type w} [AddCommGroup N] [Module R N] (H : I.IntFiltration N)

/-- Quotient-Rees-linear maps between associated gradeds commute with ideal-power scalars. -/
instance compatibleSMulPowerQuotientSum :
    LinearMap.CompatibleSMul G H.AssociatedGraded D C where
  map_smul L d x := by
    rw [F.powerQuotientSum_smul, H.powerQuotientSum_smul]
    exact L.map_smul (reesAlgebra.powerQuotientSumAlgEquiv I d) x

end ScalarRestriction

/-- A homogeneous coefficient insertion acts by its quotient monomial. -/
@[simp]
theorem powerQuotientSum_of_smul (q : ℕ) (a : reesAlgebra.powerQuotient I q) (x : G) :
    (DirectSum.of (reesAlgebra.powerQuotient I) q a : D) • x =
      reesAlgebra.quotientMonomial I q a • x := by
  rw [F.powerQuotientSum_smul, reesAlgebra.powerQuotientSumAlgEquiv_of]

/-- A homogeneous coefficient representative multiplies representatives and shifts degree. -/
theorem powerQuotientSum_of_mk_smul_single
    (q : ℕ) (n : ℤ) (a : ↥(I ^ q)) (m : F.N n) :
    (DirectSum.of (reesAlgebra.powerQuotient I) q (Submodule.Quotient.mk a) : D) •
        F.single n m =
      F.single (n + (q : ℤ))
        ⟨(a : R) • (m : M),
          F.pow_smul_le q n (Submodule.smul_mem_smul a.property m.property)⟩ := by
  rw [F.powerQuotientSum_of_smul, reesAlgebra.quotientMonomial_mk]
  exact F.monomial_smul_single q n a m

/-- Original coefficient constants act by the original `R` action. -/
theorem powerQuotientSum_algebraMap_smul (r : R) (x : G) :
    algebraMap R D r • x = r • x := by
  have h : reesAlgebra.powerQuotientSumAlgEquiv I (algebraMap R D r) =
      algebraMap R C r := by
    calc
      reesAlgebra.powerQuotientSumAlgEquiv I (algebraMap R D r) =
          reesAlgebra.powerQuotientSumAlgEquiv I (r • (1 : D)) := by
        rw [Algebra.algebraMap_eq_smul_one]
      _ = reesAlgebra.powerQuotientSumLinearEquiv I (r • (1 : D)) := by
        rw [reesAlgebra.powerQuotientSumAlgEquiv_apply,
          reesAlgebra.powerQuotientSumLinearEquivQuotient_apply]
      _ = r • (1 : C) := by
        rw [map_smul, reesAlgebra.powerQuotientSumLinearEquiv_map_one]
      _ = algebraMap R C r := (Algebra.algebraMap_eq_smul_one r).symm
  rw [F.powerQuotientSum_smul, h]
  exact algebraMap_smul C r x

/-- Residue coefficient constants act by the original `R ⧸ I` action. -/
theorem powerQuotientSum_quotient_algebraMap_smul (a : A) (x : G) :
    algebraMap A D a • x = a • x := by
  rw [F.powerQuotientSum_smul, (reesAlgebra.powerQuotientSumAlgEquiv I).commutes a]
  exact algebraMap_smul C a x

/-- The original coefficient action forms a scalar tower with the ideal-power quotient action. -/
instance isScalarTowerPowerQuotientSum : IsScalarTower R D G :=
  IsScalarTower.of_algebraMap_smul (F.powerQuotientSum_algebraMap_smul)

/-- The residue coefficient action forms a scalar tower with the ideal-power quotient action. -/
instance isScalarTowerQuotientPowerQuotientSum : IsScalarTower A D G :=
  IsScalarTower.of_algebraMap_smul (F.powerQuotientSum_quotient_algebraMap_smul)

end Ideal.IntFiltration
