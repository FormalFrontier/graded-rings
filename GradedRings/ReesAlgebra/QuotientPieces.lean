/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GradedRings.ReesAlgebra.Grading
public import GradedRings.ReesModule
public import GradedRings.ReesModule.Regular
public import Mathlib.Algebra.Algebra.Tower

/-!
# Ideal-power quotients and quotient Rees components

The quotient of `I ^ q` by its ideal multiple maps to the quotient Rees algebra
by sending the class of `a` to the class of `a X^q`. Its image is the degree-`q`
component of the existing quotient grading. This component inherits coefficients
in `R ⧸ I` from the ambient quotient Rees algebra, and the comparison is linear
over these residue coefficients.

## Implementation notes

The monomial kernel identification transports the coefficientwise singleton
criterion in `Ideal.AssociatedGradedModule` along
`Ideal.Filtration.regularReesEquiv`. The residue-coefficient component is obtained
from its `R`-submodule by `Submodule.orderIsoOfAlgebraMapSurjective`, so its carrier
is unchanged. Its module structure is inherited from the ambient quotient Rees
algebra. `LinearEquiv.extendScalarsOfSurjective` upgrades the original comparison
without changing either of its functions. No new quotient scalar action or
quotient grading is introduced.

## References

* Mathlib's quotient linear maps and linear equivalences onto ranges.
* `Ideal.AssociatedGradedModule` for coefficientwise quotient-Rees kernels.
* K. Fujiwara and F. Kato, *Foundations of Rigid Geometry I*, arXiv:1308.4734v5,
  Chapter 0, §7.5, for the Rees-quotient presentation of the associated graded.
-/

@[expose] public section

universe u

namespace reesAlgebra

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- The quotient of the `q`th ideal power by its ideal multiple. -/
abbrev powerQuotient (q : ℕ) :=
  ↥(I ^ q) ⧸ (I • (⊤ : Submodule R ↥(I ^ q)))

/-- The ideal multiple of `I ^ q` is its next power, viewed inside `I ^ q`. -/
theorem powerQuotient_denominator_eq (q : ℕ) :
    Submodule.comap (I ^ q).subtype (I ^ (q + 1) : Submodule R R) =
      I • (⊤ : Submodule R ↥(I ^ q)) := by
  ext a
  change (a : R) ∈ I ^ (q + 1) ↔ a ∈ I • (⊤ : Submodule R ↥(I ^ q))
  rw [Submodule.mem_smul_top_iff, Ideal.smul_eq_mul, ← pow_succ']

/-- The quotient component, viewed as the image of an `R`-submodule. -/
noncomputable def quotientComponentSubmodule (q : ℕ) :
    Submodule R (reesAlgebra I ⧸ I.map (algebraMap R (reesAlgebra I))) :=
  (homogeneousComponent I q).map
    (Ideal.Quotient.mkₐ R (I.map (algebraMap R (reesAlgebra I)))).toLinearMap

/-- Forgetting scalars on the image submodule recovers the quotient grading component. -/
theorem quotientComponentSubmodule_toAddSubgroup (q : ℕ) :
    (quotientComponentSubmodule I q).toAddSubgroup = quotientHomogeneousComponent I q :=
  rfl

/-- A quotient Rees component is an `R`-module through its image submodule. -/
noncomputable instance instModuleQuotientHomogeneousComponent (q : ℕ) :
    Module R (quotientHomogeneousComponent I q) :=
  inferInstanceAs (Module R (quotientComponentSubmodule I q))

/-- A monomial belongs to the extended ideal exactly when its coefficient is in the next power. -/
theorem monomial_mem_extendedIdeal_iff (q : ℕ) (a : ↥(I ^ q)) :
    monomial I q a ∈ I.map (algebraMap R (reesAlgebra I)) ↔
      (a : R) ∈ I ^ (q + 1) := by
  let B := reesAlgebra I
  let J : Ideal B := I.map (algebraMap R B)
  let N := Ideal.Filtration.submodule (I.stableFiltration (⊤ : Submodule R R))
  let e : B ≃ₗ[B] N := Ideal.Filtration.regularReesEquiv I
  have ha : (a : R) ∈ I ^ q • (⊤ : Submodule R R) := by
    simpa only [Ideal.smul_eq_mul, Ideal.mul_top] using a.property
  let p : N := ⟨PolynomialModule.single R q (a : R),
    Ideal.AssociatedGradedModule.single_mem I R q (a : R) ha⟩
  -- Identify the monomial through the polynomial value of the regular-module bridge.
  have hep : e (monomial I q a) = p := by
    apply Subtype.ext
    apply PolynomialModule.equivPolynomialSelf.injective
    change PolynomialModule.equivPolynomialSelf
        (Ideal.Filtration.regularReesEquiv I (monomial I q a) : PolynomialModule R R) =
      PolynomialModule.equivPolynomialSelf (PolynomialModule.single R q (a : R))
    rw [Ideal.Filtration.equivPolynomialSelf_regularReesEquiv_apply,
      PolynomialModule.equivPolynomialSelf_apply_eq,
      PolynomialModule.equivPolynomial_single, coe_monomial]
  -- A linear equivalence carries an ideal multiple of the regular module to the same
  -- ideal multiple of its target; only the generic submodule map API is needed.
  have hmap : Submodule.map e.toLinearMap (J : Submodule B B) =
      J • (⊤ : Submodule B N) := by
    calc
      _ = Submodule.map e.toLinearMap (J • (⊤ : Submodule B B)) := by
        rw [Ideal.smul_eq_mul, Ideal.mul_top]
      _ = _ := by rw [Submodule.map_smul'', Submodule.map_top, e.range]
  calc
    monomial I q a ∈ J ↔ e (monomial I q a) ∈ J • (⊤ : Submodule B N) := by
      rw [← hmap, Submodule.mem_map_equiv, e.symm_apply_apply]
    _ ↔ (a : R) ∈ I ^ (q + 1) • (⊤ : Submodule R R) := by
      rw [hep]
      exact Ideal.AssociatedGradedModule.single_mem_ideal_smul_iff I R q (a : R) ha
    _ ↔ (a : R) ∈ I ^ (q + 1) := by
      rw [Ideal.smul_eq_mul, Ideal.mul_top]

/-- The ideal multiple of the coefficient module is killed by the quotient monomial map. -/
theorem quotientMonomial_denominator_le_ker (q : ℕ) :
    I • (⊤ : Submodule R ↥(I ^ q)) ≤
      LinearMap.ker
        ((Ideal.Quotient.mkₐ R (I.map (algebraMap R (reesAlgebra I)))).toLinearMap.comp
          (monomial I q)) := by
  rw [← powerQuotient_denominator_eq]
  intro a ha
  rw [LinearMap.mem_ker, LinearMap.comp_apply]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr ((monomial_mem_extendedIdeal_iff I q a).mpr ha)

/-- The quotient monomial map sends a coefficient class to its monomial class. -/
noncomputable def quotientMonomial (q : ℕ) :
    powerQuotient I q →ₗ[R]
      (reesAlgebra I ⧸ I.map (algebraMap R (reesAlgebra I))) :=
  (I • (⊤ : Submodule R ↥(I ^ q))).liftQ
    ((Ideal.Quotient.mkₐ R (I.map (algebraMap R (reesAlgebra I)))).toLinearMap.comp
      (monomial I q))
    (quotientMonomial_denominator_le_ker I q)

/-- The quotient monomial map has the prescribed value on each representative. -/
@[simp]
theorem quotientMonomial_mk (q : ℕ) (a : ↥(I ^ q)) :
    quotientMonomial I q (Submodule.Quotient.mk a) =
      Ideal.Quotient.mk (I.map (algebraMap R (reesAlgebra I))) (monomial I q a) :=
  rfl

/-- Residue scalars on coefficient classes act through coefficient scalars on monomial classes. -/
theorem quotientMonomial_smul_mk (q : ℕ) (r : R) (a : ↥(I ^ q)) :
    quotientMonomial I q
        ((Ideal.Quotient.mk I r : R ⧸ I) • (Submodule.Quotient.mk a : powerQuotient I q)) =
      r • quotientMonomial I q (Submodule.Quotient.mk a) := by
  rw [Module.Quotient.mk_smul_mk]
  exact (quotientMonomial I q).map_smul r (Submodule.Quotient.mk a)

/-- The coefficient-to-monomial quotient map is injective. -/
theorem quotientMonomial_injective (q : ℕ) :
    Function.Injective (quotientMonomial I q) := by
  apply (injective_iff_map_eq_zero (quotientMonomial I q)).mpr
  intro x hx
  induction x using Submodule.Quotient.induction_on with
  | H a =>
    rw [quotientMonomial_mk] at hx
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    rw [← powerQuotient_denominator_eq]
    exact (monomial_mem_extendedIdeal_iff I q a).mp (Ideal.Quotient.eq_zero_iff_mem.mp hx)

/-- The image of the quotient monomial map is the image of the homogeneous Rees component. -/
theorem quotientMonomial_range (q : ℕ) :
    LinearMap.range (quotientMonomial I q) = quotientComponentSubmodule I q := by
  have hrange : LinearMap.range (monomial I q) = homogeneousComponent I q := by
    ext p
    exact (mem_homogeneousComponent_iff I q p).symm
  rw [quotientMonomial, Submodule.range_liftQ, LinearMap.range_comp, hrange]
  rfl

/-- The quotient of consecutive ideal powers is equivalent to its quotient Rees component. -/
noncomputable def quotientMonomialEquiv (q : ℕ) :
    powerQuotient I q ≃ₗ[R] quotientHomogeneousComponent I q :=
  (LinearEquiv.ofInjective (quotientMonomial I q) (quotientMonomial_injective I q)).trans
    (LinearEquiv.ofEq _ _ (quotientMonomial_range I q))

/-- The comparison has the quotient monomial map as its ambient value. -/
@[simp]
theorem coe_quotientMonomialEquiv (q : ℕ) (a : powerQuotient I q) :
    (quotientMonomialEquiv I q a :
      reesAlgebra I ⧸ I.map (algebraMap R (reesAlgebra I))) = quotientMonomial I q a :=
  rfl

/-- The comparison sends a coefficient representative to the class of its Rees monomial. -/
@[simp]
theorem quotientMonomialEquiv_mk (q : ℕ) (a : ↥(I ^ q)) :
    (quotientMonomialEquiv I q (Submodule.Quotient.mk a) :
      reesAlgebra I ⧸ I.map (algebraMap R (reesAlgebra I))) =
        Ideal.Quotient.mk (I.map (algebraMap R (reesAlgebra I))) (monomial I q a) :=
  rfl

/-!
## Residue coefficients on quotient components

Surjectivity of `R → R ⧸ I` makes every quotient component stable under the
ambient residue scalars. Restriction of scalars recovers its `R`-submodule,
and the inherited action extends its original `R`-module structure. The
residue-linear comparison retains the original forward and inverse functions.
-/

section Coefficients

/-- The quotient homogeneous component as a residue-coefficient submodule of the
existing quotient Rees algebra, with the same carrier as its `R`-submodule. -/
noncomputable def quotientComponentSubmoduleCoefficients (q : ℕ) :
    Submodule (R ⧸ I) (reesAlgebra I ⧸ I.map (algebraMap R (reesAlgebra I))) :=
  (Submodule.orderIsoOfAlgebraMapSurjective
    (R := R) (S := R ⧸ I)
    (M := reesAlgebra I ⧸ I.map (algebraMap R (reesAlgebra I)))
    Ideal.Quotient.mk_surjective).symm (quotientComponentSubmodule I q)

/-- Restricting the residue-coefficient component recovers the original image submodule. -/
@[simp]
theorem quotientComponentSubmoduleCoefficients_restrictScalars (q : ℕ) :
    (quotientComponentSubmoduleCoefficients I q).restrictScalars R =
      quotientComponentSubmodule I q := by
  exact (Submodule.orderIsoOfAlgebraMapSurjective
    (R := R) (S := R ⧸ I)
    (M := reesAlgebra I ⧸ I.map (algebraMap R (reesAlgebra I)))
    Ideal.Quotient.mk_surjective).apply_symm_apply (quotientComponentSubmodule I q)

/-- The existing quotient homogeneous component inherits residue scalars from
its submodule of the ambient quotient Rees algebra. -/
noncomputable instance instModuleQuotientHomogeneousComponentCoefficients (q : ℕ) :
    Module (R ⧸ I) (quotientHomogeneousComponent I q) :=
  inferInstanceAs (Module (R ⧸ I) (quotientComponentSubmoduleCoefficients I q))

/-- Residue scalars on a quotient homogeneous component extend its original `R`-module. -/
instance instIsScalarTowerQuotientHomogeneousComponentCoefficients (q : ℕ) :
    IsScalarTower R (R ⧸ I) (quotientHomogeneousComponent I q) := by
  refine ⟨fun r a x => ?_⟩
  apply Subtype.ext
  exact smul_assoc r a (x : reesAlgebra I ⧸ I.map (algebraMap R (reesAlgebra I)))

/-- Coercion to the quotient Rees algebra preserves residue scalar multiplication. -/
@[simp]
theorem coe_smul_quotientHomogeneousComponent (q : ℕ) (a : R ⧸ I)
    (x : quotientHomogeneousComponent I q) :
    ((SMul.smul a x : quotientHomogeneousComponent I q) :
      reesAlgebra I ⧸ I.map (algebraMap R (reesAlgebra I))) =
        a • (x : reesAlgebra I ⧸ I.map (algebraMap R (reesAlgebra I))) :=
  rfl

/-- Multiplication by a residue representative agrees with the unchanged `R`-action. -/
@[simp]
theorem quotientHomogeneousComponent_mk_smul (q : ℕ) (r : R)
    (x : quotientHomogeneousComponent I q) :
    @SMul.smul (R ⧸ I) (quotientHomogeneousComponent I q)
        (instModuleQuotientHomogeneousComponentCoefficients I q).toSMul
        (Ideal.Quotient.mk I r) x =
      @SMul.smul R (quotientHomogeneousComponent I q)
        (instModuleQuotientHomogeneousComponent I q).toSMul r x := by
  apply Subtype.ext
  exact algebraMap_smul (R ⧸ I) r
    (x : reesAlgebra I ⧸ I.map (algebraMap R (reesAlgebra I)))

/-- The coefficient quotient is residue-linearly equivalent to the unchanged
quotient homogeneous component, by upgrading the original `R`-linear comparison. -/
noncomputable def quotientMonomialEquivCoefficients (q : ℕ) :
    powerQuotient I q ≃ₗ[R ⧸ I] quotientHomogeneousComponent I q :=
  (quotientMonomialEquiv I q).extendScalarsOfSurjective
    (show Function.Surjective (algebraMap R (R ⧸ I)) from Ideal.Quotient.mk_surjective)

/-- The residue-linear comparison has the same forward function as the original comparison. -/
@[simp]
theorem quotientMonomialEquivCoefficients_apply (q : ℕ) (a : powerQuotient I q) :
    quotientMonomialEquivCoefficients I q a = quotientMonomialEquiv I q a := by
  exact LinearEquiv.extendScalarsOfSurjective_apply _ _ a

/-- Restricting the residue-linear comparison gives the original `R`-linear equivalence. -/
@[simp]
theorem quotientMonomialEquivCoefficients_restrictScalars (q : ℕ) :
    (quotientMonomialEquivCoefficients I q).restrictScalars R =
      quotientMonomialEquiv I q := by
  apply LinearEquiv.ext
  intro a
  exact quotientMonomialEquivCoefficients_apply I q a

/-- The residue-linear comparison has the same inverse function as the original comparison. -/
@[simp]
theorem quotientMonomialEquivCoefficients_symm_apply (q : ℕ)
    (x : quotientHomogeneousComponent I q) :
    (quotientMonomialEquivCoefficients I q).symm x =
      (quotientMonomialEquiv I q).symm x := by
  simp only [quotientMonomialEquivCoefficients,
    LinearEquiv.extendScalarsOfSurjective_symm,
    LinearEquiv.extendScalarsOfSurjective_apply]

/-- A coefficient representative maps to its original quotient Rees monomial class. -/
theorem quotientMonomialEquivCoefficients_mk (q : ℕ) (a : ↥(I ^ q)) :
    (quotientMonomialEquivCoefficients I q (Submodule.Quotient.mk a) :
      reesAlgebra I ⧸ I.map (algebraMap R (reesAlgebra I))) =
        Ideal.Quotient.mk (I.map (algebraMap R (reesAlgebra I))) (monomial I q a) := by
  rw [quotientMonomialEquivCoefficients_apply]
  exact quotientMonomialEquiv_mk I q a

end Coefficients

end reesAlgebra
