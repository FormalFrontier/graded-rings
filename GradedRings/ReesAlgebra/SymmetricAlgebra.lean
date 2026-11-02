/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GradedRings.ReesAlgebra.Generation
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic

/-!
# The symmetric algebra map to the quotient Rees algebra

The degree-one quotient monomial induces a map from its symmetric algebra to the
quotient Rees algebra. Its composite with augmentation is evaluation at zero.
-/

@[expose] public section

namespace reesAlgebra

universe u

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- The canonical map from the symmetric algebra of the degree-one power quotient
to the quotient Rees algebra. -/
noncomputable def symmetricAlgebraHom :
    SymmetricAlgebra (R ⧸ I) (powerQuotient I 1) →ₐ[R ⧸ I]
      (reesAlgebra I ⧸ I.map (algebraMap R (reesAlgebra I))) :=
  SymmetricAlgebra.lift (R := R ⧸ I) (M := powerQuotient I 1)
    (A := reesAlgebra I ⧸ I.map (algebraMap R (reesAlgebra I)))
    ((quotientMonomial I 1).extendScalarsOfSurjective Ideal.Quotient.mk_surjective :
      powerQuotient I 1 →ₗ[R ⧸ I]
        (reesAlgebra I ⧸ I.map (algebraMap R (reesAlgebra I))))

/-- The symmetric algebra map sends each degree-one generator to its quotient monomial. -/
@[simp]
theorem symmetricAlgebraHom_ι (x : powerQuotient I 1) :
    symmetricAlgebraHom I (SymmetricAlgebra.ι (R ⧸ I) (powerQuotient I 1) x) =
      quotientMonomial I 1 x := by
  simp only [symmetricAlgebraHom, SymmetricAlgebra.lift_ι_apply,
    LinearMap.extendScalarsOfSurjective_apply]

/-- Augmentation of the symmetric algebra map is evaluation at zero. -/
theorem augmentation_comp_symmetricAlgebraHom :
    (augmentation I).comp (symmetricAlgebraHom I) =
      SymmetricAlgebra.algebraMapInv (R := R ⧸ I) (M := powerQuotient I 1) := by
  apply SymmetricAlgebra.algHom_ext
  apply LinearMap.ext
  intro x
  change augmentation I
      (symmetricAlgebraHom I (SymmetricAlgebra.ι (R ⧸ I) (powerQuotient I 1) x)) =
    SymmetricAlgebra.algebraMapInv
      (SymmetricAlgebra.ι (R ⧸ I) (powerQuotient I 1) x)
  rw [symmetricAlgebraHom_ι, SymmetricAlgebra.algebraMapInv_ι]
  have hx : quotientMonomial I 1 x ∈ quotientHomogeneousComponent I 1 := by
    simpa only [coe_quotientMonomialEquiv] using (quotientMonomialEquiv I 1 x).property
  apply augmentation_eq_zero_of_mem_quotientHomogeneousComponent (I := I)
  all_goals try exact hx
  all_goals decide

/-- The augmentation of an image is the zero-evaluation of the symmetric algebra element. -/
@[simp]
theorem augmentation_symmetricAlgebraHom
    (x : SymmetricAlgebra (R ⧸ I) (powerQuotient I 1)) :
    augmentation I (symmetricAlgebraHom I x) = SymmetricAlgebra.algebraMapInv x :=
  DFunLike.congr_fun (augmentation_comp_symmetricAlgebraHom I) x

/-- The canonical map from the symmetric algebra of the degree-one power quotient
to the quotient Rees algebra is surjective. -/
theorem surjective_symmetricAlgebraHom :
    Function.Surjective (symmetricAlgebraHom I) := by
  apply (AlgHom.range_eq_top (symmetricAlgebraHom I)).mp
  apply top_unique
  rw [← adjoin_quotientHomogeneousComponent_one I]
  apply Algebra.adjoin_le
  intro c hc
  refine ⟨SymmetricAlgebra.ι (R ⧸ I) (powerQuotient I 1)
    ((quotientMonomialEquiv I 1).symm ⟨c, hc⟩), ?_⟩
  change symmetricAlgebraHom I
    (SymmetricAlgebra.ι (R ⧸ I) (powerQuotient I 1)
      ((quotientMonomialEquiv I 1).symm ⟨c, hc⟩)) = c
  rw [symmetricAlgebraHom_ι, ← coe_quotientMonomialEquiv]
  exact congrArg Subtype.val ((quotientMonomialEquiv I 1).apply_symm_apply ⟨c, hc⟩)

end reesAlgebra
