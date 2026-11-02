/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GradedRings.ReesAlgebra.PowerQuotientMultiplication
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.Ring.TransferInstance

/-!
# The algebra of ideal-power quotients

The direct sum of the ideal-power quotients is compared with the quotient Rees
algebra by sending a coefficient class in degree `q` to its quotient monomial.
Its ring structure is pulled back through this additive comparison, retaining
the original direct-sum additive group and its original `R` and `R ⧸ I` modules.
The algebra structures use these original scalar actions.

## Implementation notes

The additive comparison is the stock componentwise additive equivalence followed
by recomposition for the existing quotient grading. Only multiplication, one,
natural powers and natural/integer casts are pulled back. The injective ring
constructor keeps the original addition, zero, negation, subtraction and natural
and integer multiples. `Algebra.ofModule` uses the original module actions.
No component of the quotient grading is required to be an `R ⧸ I` module.

## References

* Mathlib's direct-sum congruence and additive decomposition equivalences.
* Mathlib's `Function.Injective.commRing`, `Algebra.ofModule` and
  `AlgEquiv.ofLinearEquiv`.
* K. Fujiwara and F. Kato, *Foundations of Rigid Geometry I*, arXiv:1308.4734v5,
  Chapter 0, §7.5, for the quotient-Rees presentation of the associated graded.
-/

@[expose] public section

universe u

open scoped DirectSum

namespace reesAlgebra

variable {R : Type u} [CommRing R] (I : Ideal R)

local notation "A" => R ⧸ I
local notation "C" => reesAlgebra I ⧸ I.map (algebraMap R (reesAlgebra I))

/-- The direct sum of the ideal-power quotients, with its original componentwise modules. -/
abbrev powerQuotientSum := ⨁ q : ℕ, powerQuotient I q

/-- The additive comparison obtained from the component equivalences and quotient grading. -/
noncomputable def powerQuotientSumAddEquiv : powerQuotientSum I ≃+ C :=
  (DirectSum.congrAddEquiv fun q => (quotientMonomialEquiv I q).toAddEquiv).trans
    (DirectSum.decomposeAddEquiv (quotientHomogeneousComponent I)).symm

/-- The additive comparison sends a homogeneous coefficient class to its quotient monomial. -/
@[simp]
theorem powerQuotientSumAddEquiv_of (q : ℕ) (x : powerQuotient I q) :
    powerQuotientSumAddEquiv I (DirectSum.of (powerQuotient I) q x) =
      quotientMonomial I q x := by
  change (DirectSum.decompose (quotientHomogeneousComponent I)).symm
    (DirectSum.map (fun q => (quotientMonomialEquiv I q).toAddEquiv.toAddMonoidHom)
      (DirectSum.of (powerQuotient I) q x)) = _
  rw [DirectSum.map_of, DirectSum.decompose_symm_of]
  exact coe_quotientMonomialEquiv I q x

/-- The inverse additive comparison recovers a homogeneous coefficient class. -/
@[simp]
theorem powerQuotientSumAddEquiv_symm_quotientMonomial
    (q : ℕ) (x : powerQuotient I q) :
    (powerQuotientSumAddEquiv I).symm (quotientMonomial I q x) =
      DirectSum.of (powerQuotient I) q x := by
  rw [← powerQuotientSumAddEquiv_of I q x]
  exact (powerQuotientSumAddEquiv I).symm_apply_apply _

/-- The inverse additive comparison decomposes into the existing quotient components
and applies the inverse component equivalence in each degree. -/
theorem powerQuotientSumAddEquiv_symm_apply (c : C) :
    (powerQuotientSumAddEquiv I).symm c =
      (DirectSum.congrAddEquiv fun q => (quotientMonomialEquiv I q).symm.toAddEquiv)
        (DirectSum.decomposeAddEquiv (quotientHomogeneousComponent I) c) := by
  rfl

private theorem powerQuotientSumAddEquiv_map_smul (r : R) (x : powerQuotientSum I) :
    powerQuotientSumAddEquiv I (r • x) = r • powerQuotientSumAddEquiv I x := by
  induction x using DirectSum.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | of q x =>
    rw [← DirectSum.of_smul, powerQuotientSumAddEquiv_of,
      powerQuotientSumAddEquiv_of, map_smul]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

/-- The original-`R` comparison sending each coefficient class to its quotient monomial. -/
@[no_expose]
noncomputable def powerQuotientSumLinearEquiv : powerQuotientSum I ≃ₗ[R] C :=
  { powerQuotientSumAddEquiv I with
    map_smul' := powerQuotientSumAddEquiv_map_smul I }

private theorem powerQuotientSumLinearEquiv_apply_proof (x : powerQuotientSum I) :
    powerQuotientSumLinearEquiv I x = powerQuotientSumAddEquiv I x :=
  rfl

/-- The linear comparison has the same underlying function as the additive comparison. -/
theorem powerQuotientSumLinearEquiv_apply (x : powerQuotientSum I) :
    powerQuotientSumLinearEquiv I x = powerQuotientSumAddEquiv I x :=
  powerQuotientSumLinearEquiv_apply_proof I x

/-- The inverse linear comparison has the same function as the inverse additive comparison. -/
theorem powerQuotientSumLinearEquiv_symm_apply (c : C) :
    (powerQuotientSumLinearEquiv I).symm c = (powerQuotientSumAddEquiv I).symm c := by
  apply (powerQuotientSumLinearEquiv I).injective
  rw [LinearEquiv.apply_symm_apply, powerQuotientSumLinearEquiv_apply,
    AddEquiv.apply_symm_apply]

/-- The original-scalar comparison has the prescribed value on a homogeneous insertion. -/
@[simp]
theorem powerQuotientSumLinearEquiv_of (q : ℕ) (x : powerQuotient I q) :
    powerQuotientSumLinearEquiv I (DirectSum.of (powerQuotient I) q x) =
      quotientMonomial I q x := by
  rw [powerQuotientSumLinearEquiv_apply, powerQuotientSumAddEquiv_of]

/-- The inverse comparison recovers a homogeneous coefficient class. -/
@[simp]
theorem powerQuotientSumLinearEquiv_symm_quotientMonomial
    (q : ℕ) (x : powerQuotient I q) :
    (powerQuotientSumLinearEquiv I).symm (quotientMonomial I q x) =
      DirectSum.of (powerQuotient I) q x := by
  rw [powerQuotientSumLinearEquiv_symm_apply,
    powerQuotientSumAddEquiv_symm_quotientMonomial]

/-- The same comparison, linear for the original residue-coefficient action on the whole sum. -/
noncomputable def powerQuotientSumLinearEquivQuotient : powerQuotientSum I ≃ₗ[A] C :=
  letI : IsScalarTower R A C := inferInstance
  LinearEquiv.extendScalarsOfSurjective (R := R) (S := A)
    Ideal.Quotient.mk_surjective (powerQuotientSumLinearEquiv I)

/-- Extending scalars does not change the comparison function. -/
theorem powerQuotientSumLinearEquivQuotient_apply (x : powerQuotientSum I) :
    powerQuotientSumLinearEquivQuotient I x = powerQuotientSumLinearEquiv I x := by
  rfl

/-- Extending scalars does not change the inverse comparison function. -/
theorem powerQuotientSumLinearEquivQuotient_symm_apply (c : C) :
    (powerQuotientSumLinearEquivQuotient I).symm c =
      (powerQuotientSumLinearEquiv I).symm c := by
  apply (powerQuotientSumLinearEquivQuotient I).injective
  rw [LinearEquiv.apply_symm_apply, powerQuotientSumLinearEquivQuotient_apply,
    LinearEquiv.apply_symm_apply]

/-- The quotient-Rees ring structure pulled back while retaining the original additive group. -/
noncomputable instance instCommRingPowerQuotientSum : CommRing (powerQuotientSum I) :=
  -- Use one existing quotient-Rees ring to infer all its operation projections.
  letI : CommRing C := inferInstance
  let e := powerQuotientSumAddEquiv I
  letI : Mul (powerQuotientSum I) := e.toEquiv.mul
  letI : One (powerQuotientSum I) := e.toEquiv.one
  letI : Pow (powerQuotientSum I) ℕ := e.toEquiv.pow ℕ
  letI : NatCast (powerQuotientSum I) := ⟨fun n => e.symm (n : C)⟩
  letI : IntCast (powerQuotientSum I) := ⟨fun n => e.symm (n : C)⟩
  { e.injective.commRing e
      (map_zero e)
      (e.apply_symm_apply 1)
      (map_add e)
      (fun _ _ => e.apply_symm_apply _)
      (map_neg e)
      (map_sub e)
      (fun n x => map_nsmul e n x)
      (fun n x => map_zsmul e n x)
      (fun _ _ => e.apply_symm_apply _)
      (fun n => e.apply_symm_apply (n : C))
      (fun n => e.apply_symm_apply (n : C)) with
    toAddCommGroup := inferInstanceAs (AddCommGroup (⨁ q : ℕ, powerQuotient I q)) }

private theorem powerQuotientSumAddEquiv_map_one : powerQuotientSumAddEquiv I 1 = 1 :=
  (powerQuotientSumAddEquiv I).apply_symm_apply 1

private theorem powerQuotientSumAddEquiv_map_mul (x y : powerQuotientSum I) :
    powerQuotientSumAddEquiv I (x * y) =
      powerQuotientSumAddEquiv I x * powerQuotientSumAddEquiv I y :=
  (powerQuotientSumAddEquiv I).apply_symm_apply _

/-- The original-scalar comparison preserves the transported unit. -/
@[simp]
theorem powerQuotientSumLinearEquiv_map_one : powerQuotientSumLinearEquiv I 1 = 1 := by
  rw [powerQuotientSumLinearEquiv_apply]
  exact powerQuotientSumAddEquiv_map_one I

/-- The original-scalar comparison preserves the transported multiplication. -/
theorem powerQuotientSumLinearEquiv_map_mul (x y : powerQuotientSum I) :
    powerQuotientSumLinearEquiv I (x * y) =
      powerQuotientSumLinearEquiv I x * powerQuotientSumLinearEquiv I y := by
  simp only [powerQuotientSumLinearEquiv_apply]
  exact powerQuotientSumAddEquiv_map_mul I x y

/-- The residue-scalar comparison preserves the transported unit. -/
@[simp]
theorem powerQuotientSumLinearEquivQuotient_map_one :
    powerQuotientSumLinearEquivQuotient I 1 = 1 := by
  rw [powerQuotientSumLinearEquivQuotient_apply, powerQuotientSumLinearEquiv_map_one]

/-- The residue-scalar comparison preserves the transported multiplication. -/
theorem powerQuotientSumLinearEquivQuotient_map_mul (x y : powerQuotientSum I) :
    powerQuotientSumLinearEquivQuotient I (x * y) =
      powerQuotientSumLinearEquivQuotient I x * powerQuotientSumLinearEquivQuotient I y := by
  simp only [powerQuotientSumLinearEquivQuotient_apply, powerQuotientSumLinearEquiv_map_mul]

/-- The coefficient algebra structure using the original componentwise `R` action. -/
noncomputable instance instAlgebraPowerQuotientSumCoefficients : Algebra R (powerQuotientSum I) :=
  Algebra.ofModule
    (by
      intro r x y
      apply (powerQuotientSumLinearEquiv I).injective
      simpa only [powerQuotientSumLinearEquiv_map_mul, map_smul] using
        smul_mul_assoc r (powerQuotientSumLinearEquiv I x) (powerQuotientSumLinearEquiv I y))
    (by
      intro r x y
      apply (powerQuotientSumLinearEquiv I).injective
      simpa only [powerQuotientSumLinearEquiv_map_mul, map_smul] using
        mul_smul_comm r (powerQuotientSumLinearEquiv I x) (powerQuotientSumLinearEquiv I y))

/-- The residue-coefficient algebra structure using the original componentwise quotient action. -/
noncomputable instance instAlgebraPowerQuotientSumQuotient : Algebra A (powerQuotientSum I) :=
  Algebra.ofModule
    (by
      intro a x y
      apply (powerQuotientSumLinearEquivQuotient I).injective
      simpa only [powerQuotientSumLinearEquivQuotient_map_mul, map_smul] using
        smul_mul_assoc a (powerQuotientSumLinearEquivQuotient I x)
          (powerQuotientSumLinearEquivQuotient I y))
    (by
      intro a x y
      apply (powerQuotientSumLinearEquivQuotient I).injective
      simpa only [powerQuotientSumLinearEquivQuotient_map_mul, map_smul] using
        mul_smul_comm a (powerQuotientSumLinearEquivQuotient I x)
          (powerQuotientSumLinearEquivQuotient I y))

/-- The ideal-power quotient sum is the quotient Rees algebra over the residue coefficient ring.

This is the quotient-Rees presentation of the associated graded algebra in Fujiwara–Kato,
*Foundations of Rigid Geometry I*, Chapter 0, §7.5. -/
@[no_expose]
noncomputable def powerQuotientSumAlgEquiv : powerQuotientSum I ≃ₐ[A] C :=
  AlgEquiv.ofLinearEquiv (powerQuotientSumLinearEquivQuotient I)
    (powerQuotientSumLinearEquivQuotient_map_one I)
    (powerQuotientSumLinearEquivQuotient_map_mul I)

private theorem powerQuotientSumAlgEquiv_apply_proof (x : powerQuotientSum I) :
    powerQuotientSumAlgEquiv I x = powerQuotientSumLinearEquivQuotient I x :=
  rfl

/-- The algebra comparison has the same underlying function as the residue-linear comparison. -/
theorem powerQuotientSumAlgEquiv_apply (x : powerQuotientSum I) :
    powerQuotientSumAlgEquiv I x = powerQuotientSumLinearEquivQuotient I x :=
  powerQuotientSumAlgEquiv_apply_proof I x

/-- The inverse algebra comparison has the same function as the inverse residue-linear
comparison. -/
theorem powerQuotientSumAlgEquiv_symm_apply (c : C) :
    (powerQuotientSumAlgEquiv I).symm c =
      (powerQuotientSumLinearEquivQuotient I).symm c := by
  apply (powerQuotientSumAlgEquiv I).injective
  rw [AlgEquiv.apply_symm_apply, powerQuotientSumAlgEquiv_apply,
    LinearEquiv.apply_symm_apply]

/-- The quotient Rees algebra expressed as the direct sum of ideal-power quotients. -/
noncomputable def quotientReesEquivPowerQuotientSum : C ≃ₐ[A] powerQuotientSum I :=
  (powerQuotientSumAlgEquiv I).symm

/-- The quotient Rees comparison has the same function as the inverse additive comparison. -/
theorem quotientReesEquivPowerQuotientSum_apply_eq_addEquiv_symm (c : C) :
    quotientReesEquivPowerQuotientSum I c = (powerQuotientSumAddEquiv I).symm c := by
  change (powerQuotientSumAlgEquiv I).symm c = _
  rw [powerQuotientSumAlgEquiv_symm_apply,
    powerQuotientSumLinearEquivQuotient_symm_apply, powerQuotientSumLinearEquiv_symm_apply]

/-- The algebra comparison sends a homogeneous insertion to its quotient monomial. -/
@[simp]
theorem powerQuotientSumAlgEquiv_of (q : ℕ) (x : powerQuotient I q) :
    powerQuotientSumAlgEquiv I (DirectSum.of (powerQuotient I) q x) =
      quotientMonomial I q x := by
  rw [powerQuotientSumAlgEquiv_apply, powerQuotientSumLinearEquivQuotient_apply,
    powerQuotientSumLinearEquiv_of]

/-- The inverse algebra comparison sends a quotient monomial to its coefficient insertion. -/
@[simp]
theorem quotientReesEquivPowerQuotientSum_quotientMonomial
    (q : ℕ) (x : powerQuotient I q) :
    quotientReesEquivPowerQuotientSum I (quotientMonomial I q x) =
      DirectSum.of (powerQuotient I) q x := by
  rw [quotientReesEquivPowerQuotientSum_apply_eq_addEquiv_symm,
    powerQuotientSumAddEquiv_symm_quotientMonomial]

/-- The inverse algebra comparison decomposes into quotient components and recovers their
coefficient classes. -/
theorem quotientReesEquivPowerQuotientSum_apply (c : C) :
    quotientReesEquivPowerQuotientSum I c =
      (DirectSum.congrAddEquiv fun q => (quotientMonomialEquiv I q).symm.toAddEquiv)
        (DirectSum.decomposeAddEquiv (quotientHomogeneousComponent I) c) := by
  rw [quotientReesEquivPowerQuotientSum_apply_eq_addEquiv_symm,
    powerQuotientSumAddEquiv_symm_apply]

/-- The unit is the class of one inserted in degree zero. -/
theorem powerQuotientSum_one_eq_of :
    (1 : powerQuotientSum I) = DirectSum.of (powerQuotient I) 0
      (Submodule.Quotient.mk (⟨1, by simp⟩ : ↥(I ^ 0))) := by
  apply (powerQuotientSumAlgEquiv I).injective
  rw [map_one, powerQuotientSumAlgEquiv_of, quotientMonomial_one]

/-- Homogeneous multiplication is the concrete multiplication of coefficient classes. -/
theorem powerQuotientSum_of_mul_of (q r : ℕ)
    (x : powerQuotient I q) (y : powerQuotient I r) :
    (DirectSum.of (powerQuotient I) q x : powerQuotientSum I) *
        DirectSum.of (powerQuotient I) r y =
      DirectSum.of (powerQuotient I) (q + r) (powerQuotientMul I q r x y) := by
  apply (powerQuotientSumAlgEquiv I).injective
  simp only [map_mul, powerQuotientSumAlgEquiv_of, quotientMonomial_powerQuotientMul]

end reesAlgebra
