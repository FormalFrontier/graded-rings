/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GradedRings.ReesAlgebra.Grading
public import GradedRings.ReesModule
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# The augmentation of the quotient Rees algebra

Constant coefficient followed by reduction modulo `I` descends to the quotient
of `reesAlgebra I` by the extension of `I`. The resulting map is an algebra
homomorphism over `R ⧸ I`. On a quotient representative it returns the residue
of the constant coefficient, and it vanishes on every positive homogeneous
component. Composing it with the coefficient map is the degree-zero projection;
the image of the coefficient map is exactly the degree-zero component.

## References

* Mathlib's `Polynomial.constantCoeff` and `Ideal.Quotient.lift` supply the
  coefficient map and its descent to the quotient; `GradedRing.projZeroRingHom`
  supplies the degree-zero projection.
* `GradedRings.ReesAlgebra.Grading` supplies the Rees monomials and the quotient
  homogeneous components used by the computation lemmas.
-/

@[expose] public section

universe u

namespace reesAlgebra

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- The coefficient map sends a residue representative to the class of its Rees scalar. -/
theorem algebraMap_quotient_mk (r : R) :
    algebraMap (R ⧸ I) (reesAlgebra I ⧸ I.map (algebraMap R (reesAlgebra I)))
        (Ideal.Quotient.mk I r) =
      Ideal.Quotient.mk (I.map (algebraMap R (reesAlgebra I)))
        (algebraMap R (reesAlgebra I) r) := by
  change algebraMap (R ⧸ I)
      (reesAlgebra I ⧸ I.map (algebraMap R (reesAlgebra I)))
      (algebraMap R (R ⧸ I) r) =
    algebraMap (reesAlgebra I)
      (reesAlgebra I ⧸ I.map (algebraMap R (reesAlgebra I)))
      (algebraMap R (reesAlgebra I) r)
  rw [← IsScalarTower.algebraMap_apply R (R ⧸ I)
      (reesAlgebra I ⧸ I.map (algebraMap R (reesAlgebra I))),
    ← IsScalarTower.algebraMap_apply R (reesAlgebra I)
      (reesAlgebra I ⧸ I.map (algebraMap R (reesAlgebra I)))]

/-- The constant-coefficient augmentation of the quotient Rees algebra over `R ⧸ I`. -/
noncomputable def augmentation :
    (reesAlgebra I ⧸ I.map (algebraMap R (reesAlgebra I))) →ₐ[R ⧸ I] (R ⧸ I) where
  toRingHom :=
    Ideal.Quotient.lift (I.map (algebraMap R (reesAlgebra I)))
      ((Ideal.Quotient.mk I).comp
        ((Polynomial.constantCoeff (R := R)).comp (reesAlgebra I).val.toRingHom))
      (by
        intro b hb
        have hker : I.map (algebraMap R (reesAlgebra I)) ≤
            RingHom.ker ((Ideal.Quotient.mk I).comp
              ((Polynomial.constantCoeff (R := R)).comp (reesAlgebra I).val.toRingHom)) := by
          rw [Ideal.map_le_iff_le_comap]
          intro r hr
          change Ideal.Quotient.mk I ((Polynomial.C r).coeff 0) = 0
          simpa only [Polynomial.coeff_C_zero] using (Ideal.Quotient.eq_zero_iff_mem.mpr hr)
        exact hker hb)
  commutes' := by
    intro a
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [algebraMap_quotient_mk]
    change Ideal.Quotient.mk I ((Polynomial.C r).coeff 0) =
      algebraMap (R ⧸ I) (R ⧸ I) (Ideal.Quotient.mk I r)
    rw [Polynomial.coeff_C_zero, Algebra.algebraMap_self_apply]

/-- On quotient representatives, augmentation is the residue of the constant coefficient. -/
@[simp]
theorem augmentation_mk (b : reesAlgebra I) :
    augmentation I (Ideal.Quotient.mk (I.map (algebraMap R (reesAlgebra I))) b) =
      Ideal.Quotient.mk I ((b : Polynomial R).coeff 0) :=
  rfl

/-- A quotient Rees monomial augments to its coefficient in degree zero and to zero otherwise. -/
theorem augmentation_mk_monomial (q : ℕ) (a : ↥(I ^ q)) :
    augmentation I
        (Ideal.Quotient.mk (I.map (algebraMap R (reesAlgebra I))) (monomial I q a)) =
      if q = 0 then Ideal.Quotient.mk I (a : R) else 0 := by
  rw [augmentation_mk, coe_monomial, Polynomial.coeff_monomial]
  by_cases hq : q = 0
  · simp only [hq, ite_true]
  · simp only [hq, ite_false, map_zero]

/-- Augmentation vanishes on every positive homogeneous component of the quotient Rees algebra. -/
theorem augmentation_eq_zero_of_mem_quotientHomogeneousComponent
    {q : ℕ} (hq : 0 < q)
    {c : reesAlgebra I ⧸ I.map (algebraMap R (reesAlgebra I))}
    (hc : c ∈ quotientHomogeneousComponent I q) :
    augmentation I c = 0 := by
  obtain ⟨b, hb, rfl⟩ := (mem_quotientHomogeneousComponent_iff I q c).mp hc
  obtain ⟨a, rfl⟩ := (mem_homogeneousComponent_iff I q b).mp hb
  rw [augmentation_mk_monomial, ite_eq_right (ne_of_gt hq)]

/-- Composing augmentation with the coefficient map gives the degree-zero projection. -/
theorem algebraMap_augmentation
    (c : reesAlgebra I ⧸ I.map (algebraMap R (reesAlgebra I))) :
    algebraMap (R ⧸ I)
        (reesAlgebra I ⧸ I.map (algebraMap R (reesAlgebra I)))
        (augmentation I c) =
      GradedRing.projZeroRingHom (quotientHomogeneousComponent I) c := by
  classical
  refine DirectSum.Decomposition.inductionOn (quotientHomogeneousComponent I) ?_ ?_ ?_ c
  · simp only [map_zero]
  · rintro q ⟨x, hx⟩
    obtain ⟨b, hb, rfl⟩ := (mem_quotientHomogeneousComponent_iff I q x).mp hx
    obtain ⟨a, rfl⟩ := (mem_homogeneousComponent_iff I q b).mp hb
    by_cases hq : q = 0
    · subst q
      rw [augmentation_mk_monomial, ite_eq_left rfl, algebraMap_quotient_mk,
        GradedRing.projZeroRingHom_apply,
        DirectSum.decompose_of_mem_same _ hx, monomial_zero]
    · rw [augmentation_mk_monomial, ite_eq_right hq, map_zero,
        GradedRing.projZeroRingHom_apply,
        DirectSum.decompose_of_mem_ne _ hx hq]
  · intro x y hx hy
    simp only [map_add, hx, hy]

/-- The degree-zero quotient Rees component is exactly the image of the coefficient map. -/
theorem coe_quotientHomogeneousComponent_zero :
    ((quotientHomogeneousComponent I 0 :
        AddSubgroup (reesAlgebra I ⧸ I.map (algebraMap R (reesAlgebra I)))) :
        Set (reesAlgebra I ⧸ I.map (algebraMap R (reesAlgebra I)))) =
      Set.range (algebraMap (R ⧸ I)
        (reesAlgebra I ⧸ I.map (algebraMap R (reesAlgebra I)))) := by
  apply Set.ext
  intro c
  constructor
  · intro hc
    refine ⟨augmentation I c, ?_⟩
    calc
      algebraMap (R ⧸ I)
          (reesAlgebra I ⧸ I.map (algebraMap R (reesAlgebra I)))
          (augmentation I c) =
          GradedRing.projZeroRingHom (quotientHomogeneousComponent I) c :=
        algebraMap_augmentation I c
      _ = (GradedRing.projZeroRingHom' (quotientHomogeneousComponent I) c :
          reesAlgebra I ⧸ I.map (algebraMap R (reesAlgebra I))) :=
        (GradedRing.coe_projZeroRingHom'_apply (quotientHomogeneousComponent I) c).symm
      _ = c := congrArg
        (fun z : quotientHomogeneousComponent I 0 =>
          (z : reesAlgebra I ⧸ I.map (algebraMap R (reesAlgebra I))))
        (GradedRing.projZeroRingHom'_apply_coe (quotientHomogeneousComponent I)
          (⟨c, hc⟩ : quotientHomogeneousComponent I 0))
  · rintro ⟨a, rfl⟩
    have hs : augmentation I
        (algebraMap (R ⧸ I)
          (reesAlgebra I ⧸ I.map (algebraMap R (reesAlgebra I))) a) = a := by
      simpa only [Algebra.algebraMap_self_apply] using (augmentation I).commutes a
    have hm : (GradedRing.projZeroRingHom' (quotientHomogeneousComponent I)
        (algebraMap (R ⧸ I)
          (reesAlgebra I ⧸ I.map (algebraMap R (reesAlgebra I))) a) :
        reesAlgebra I ⧸ I.map (algebraMap R (reesAlgebra I))) ∈
        quotientHomogeneousComponent I 0 :=
      (GradedRing.projZeroRingHom' (quotientHomogeneousComponent I)
        (algebraMap (R ⧸ I)
          (reesAlgebra I ⧸ I.map (algebraMap R (reesAlgebra I))) a)).property
    rw [GradedRing.coe_projZeroRingHom'_apply,
      ← algebraMap_augmentation I
        (algebraMap (R ⧸ I)
          (reesAlgebra I ⧸ I.map (algebraMap R (reesAlgebra I))) a), hs] at hm
    exact hm

end reesAlgebra
