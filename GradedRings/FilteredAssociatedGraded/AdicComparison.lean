/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GradedRings.FilteredAssociatedGraded.Adic
public import GradedRings.FilteredAssociatedGraded.ReesAction
public import GradedRings.ReesModule
public import GradedRings.AssociatedGradedRegular

/-!
# The ideal-adic associated graded comparison

The associated graded module of the canonical integer ideal-adic filtration is
canonically linearly equivalent to the quotient of the Rees module by the extended
ideal. The comparison inserts stage representatives as polynomial singletons. It
uses the original module structures and the canonical quotient Rees actions on
both sides. Its inverse is characterized by the existing coefficient and stage
comparison maps; negative integer components vanish.

No finiteness, Noetherianity, completeness or separatedness hypothesis is needed.

## References

* K. Fujiwara and F. Kato, *Foundations of Rigid Geometry I*, arXiv:1308.4734v5,
  Chapter 0, §7.5, for the ideal-adic associated graded and its Rees presentation.
* Mathlib's quotient linear maps and direct-sum universal property supply the
  descent and assembly maps.
* `GradedRings.ReesModule` supplies the coefficient kernel, stage comparison,
  and finite polynomial-module expansion used in the proofs.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe uR uM

open scoped BigOperators

namespace Ideal

variable {R : Type uR} [CommRing R]
variable (I : Ideal R) (M : Type uM) [AddCommGroup M] [Module R M]

local notation "B" => reesAlgebra I
local notation "J" => I.map (algebraMap R B)
local notation "C" => B ⧸ J
local notation "G" => Ideal.AssociatedGradedModule I M
local notation "F" => I.adicIntFiltration M

/-- The single polynomial with its coefficient in the corresponding ideal-power stage. -/
private noncomputable def adicSingleton (q : ℕ) :
    ↥(I ^ q • (⊤ : Submodule R M)) →ₗ[R]
      ↥((I.stableFiltration (⊤ : Submodule R M)).submodule) where
  toFun m :=
    ⟨PolynomialModule.single R q (m : M),
      AssociatedGradedModule.single_mem I M q (m : M) m.property⟩
  map_add' x y := Subtype.ext (PolynomialModule.single_add q (x : M) (y : M))
  map_smul' r x := Subtype.ext (PolynomialModule.single_smul q r (x : M))

/-- A stage representative inserted in the existing Rees-module quotient. -/
private noncomputable def adicSingletonClass (q : ℕ) :
    ↥(I ^ q • (⊤ : Submodule R M)) →ₗ[R] G :=
  ((AssociatedGradedModule.mk I M).restrictScalars R).comp (adicSingleton I M q)

private theorem adicSingletonClass_denominator_le_ker (q : ℕ) :
    (I ^ (q + 1) • (⊤ : Submodule R M)).comap
        (I ^ q • (⊤ : Submodule R M)).subtype ≤
      LinearMap.ker (adicSingletonClass I M q) := by
  intro m hm
  change (Submodule.Quotient.mk (adicSingleton I M q m) : G) = 0
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  exact (AssociatedGradedModule.single_mem_ideal_smul_iff I M q (m : M) m.property).mpr hm

/-- The natural-degree piece map obtained by descending the singleton map. -/
private noncomputable def adicPositivePieceClass (q : ℕ) :
    (F).GradedPiece (q : ℤ) →ₗ[R] G :=
  (((I ^ (q + 1) • (⊤ : Submodule R M)).comap
      (I ^ q • (⊤ : Submodule R M)).subtype).liftQ
        (adicSingletonClass I M q)
        (adicSingletonClass_denominator_le_ker I M q)).comp
    (I.adicGradedPieceEquiv M q).toLinearMap

/-- The integer-degree piece maps, without reindexing the direct sum. -/
private noncomputable def adicPieceClass : (n : ℤ) → (F).GradedPiece n →ₗ[R] G
  | .ofNat q => adicPositivePieceClass I M q
  | .negSucc _ => 0

/-- The original-ring linear comparison defined directly from the integer direct sum. -/
@[no_expose]
noncomputable def adicAssociatedGradedMapR : (F).AssociatedGraded →ₗ[R] G :=
  (F).lift (adicPieceClass I M)

private theorem adicAssociatedGradedMapR_single (q : ℕ)
    (m : ↥(I ^ q • (⊤ : Submodule R M))) :
    adicAssociatedGradedMapR I M ((F).single (q : ℤ) m) =
      AssociatedGradedModule.mk I M (adicSingleton I M q m) := by
  calc
    adicAssociatedGradedMapR I M ((F).single (q : ℤ) m) =
        adicPieceClass I M (q : ℤ) ((F).cl (q : ℤ) m) :=
      (F).lift_inclusion (adicPieceClass I M) (q : ℤ) ((F).cl (q : ℤ) m)
    _ = _ := rfl

private theorem adicSingle_eq_zero_of_neg (n : ℤ) (hn : n < 0) (m : (F).N n) :
    (F).single n m = 0 := by
  let := I.adicIntFiltration_gradedPiece_subsingleton M n hn
  rw [IntFiltration.single_apply, Subsingleton.elim ((F).cl n m) 0, map_zero]

private theorem coefficient_adicAssociatedGradedMapR (q : ℕ) (x : (F).AssociatedGraded) :
    AssociatedGradedModule.coefficient I M q (adicAssociatedGradedMapR I M x) =
      ((AssociatedGradedModule.stageComparison I M q
        (Submodule.quotEquivOfEq _ _
          (AssociatedGradedModule.stage_denominator_eq I M q)
          (I.adicGradedPieceEquiv M q ((F).component (q : ℤ) x)))) :
        M ⧸ (I ^ (q + 1) • (⊤ : Submodule R M))) := by
  let e := (I.adicGradedPieceEquiv M q).trans
    ((Submodule.quotEquivOfEq _ _
      (AssociatedGradedModule.stage_denominator_eq I M q)).trans
        (AssociatedGradedModule.stageComparison I M q))
  let rhs : (F).AssociatedGraded →ₗ[R]
      M ⧸ (I ^ (q + 1) • (⊤ : Submodule R M)) :=
    ((I ^ q • (⊤ : Submodule R M)).map
      (I ^ (q + 1) • (⊤ : Submodule R M)).mkQ).subtype.comp
        (e.toLinearMap.comp ((F).component (q : ℤ)))
  have h : (AssociatedGradedModule.coefficient I M q).comp
      (adicAssociatedGradedMapR I M).toAddMonoidHom = rhs.toAddMonoidHom := by
    apply DirectSum.addHom_ext
    intro n z
    obtain ⟨m, rfl⟩ := (F).cl_surjective n z
    change AssociatedGradedModule.coefficient I M q
        (adicAssociatedGradedMapR I M ((F).single n m)) =
      (e ((F).component (q : ℤ) ((F).single n m)) :
        M ⧸ (I ^ (q + 1) • (⊤ : Submodule R M)))
    cases n with
    | ofNat j =>
        erw [adicAssociatedGradedMapR_single, AssociatedGradedModule.mk_apply,
          AssociatedGradedModule.coefficient_mk]
        by_cases hjq : j = q
        · subst j
          change ↥((F).N (q : ℤ)) at m
          erw [(F).component_single (q : ℤ) (m : (F).N (q : ℤ))]
          suffices hdiag :
              (Submodule.Quotient.mk (m : M) :
                M ⧸ (I ^ (q + 1) • (⊤ : Submodule R M))) =
                ((AssociatedGradedModule.stageComparison I M q
                  ((Submodule.quotEquivOfEq
                    ((I ^ (q + 1) • (⊤ : Submodule R M)).comap
                      (I ^ q • (⊤ : Submodule R M)).subtype)
                    (I • (⊤ : Submodule R ↥(I ^ q • (⊤ : Submodule R M))))
                    (AssociatedGradedModule.stage_denominator_eq I M q))
                    (I.adicGradedPieceEquiv M q ((F).cl (q : ℤ) m)))) :
                  M ⧸ (I ^ (q + 1) • (⊤ : Submodule R M))) by
            simpa [e, adicSingleton] using hdiag
          let mp : ↥(I ^ q • (⊤ : Submodule R M)) := m
          have hcl := (F).cl_apply (q : ℤ) m
          have hadic : I.adicGradedPieceEquiv M q ((F).cl (q : ℤ) m) =
              (Submodule.Quotient.mk mp :
                ↥(I ^ q • (⊤ : Submodule R M)) ⧸
                  (I ^ (q + 1) • (⊤ : Submodule R M)).comap
                    (I ^ q • (⊤ : Submodule R M)).subtype) :=
            (congrArg (I.adicGradedPieceEquiv M q) hcl).trans
              (I.adicGradedPieceEquiv_apply_mk M q mp)
          have hquot := Submodule.quotEquivOfEq_mk
            (p := (I ^ (q + 1) • (⊤ : Submodule R M)).comap
              (I ^ q • (⊤ : Submodule R M)).subtype)
            (p' := I • (⊤ : Submodule R ↥(I ^ q • (⊤ : Submodule R M))))
            (AssociatedGradedModule.stage_denominator_eq I M q) mp
          have hstage :
              ((AssociatedGradedModule.stageComparison I M q
                (Submodule.Quotient.mk mp)) :
                  M ⧸ (I ^ (q + 1) • (⊤ : Submodule R M))) =
                Submodule.Quotient.mk (m : M) :=
            AssociatedGradedModule.stageComparison_mk I M q mp
          erw [hadic, hquot, hstage]
        · have hcast : (q : ℤ) ≠ (j : ℤ) := by
            intro hcast
            exact hjq (Int.ofNat_inj.mp hcast.symm)
          erw [(F).component_single_of_ne (j : ℤ) (q : ℤ) hcast, map_zero]
          simp [adicSingleton, PolynomialModule.coeff_single, hjq]
    | negSucc j =>
        rw [adicSingle_eq_zero_of_neg I M _ (by simp)]
        simp
  exact DFunLike.congr_fun h x

private theorem adicAssociatedGradedMapR_monomial_single (i : ℕ) (a : ↥(I ^ i))
    (n : ℤ) (m : (F).N n) :
    adicAssociatedGradedMapR I M
        ((Ideal.Quotient.mk J (reesAlgebra.monomial I i a) : C) • (F).single n m) =
      (Ideal.Quotient.mk J (reesAlgebra.monomial I i a) : C) •
        adicAssociatedGradedMapR I M ((F).single n m) := by
  cases n with
  | ofNat j =>
      rw [IntFiltration.monomial_smul_single]
      have hdegree : Int.ofNat j + (i : ℤ) = ((i + j : ℕ) : ℤ) := by
        change (j : ℤ) + (i : ℤ) = ((i + j : ℕ) : ℤ)
        simp only [Nat.cast_add, add_comm]
      have hsmul :
          (a : R) • (m : M) ∈ (F).N (Int.ofNat j + (i : ℤ)) :=
        (F).pow_smul_le i (Int.ofNat j)
          (Submodule.smul_mem_smul a.property m.property)
      have hnat :
          (a : R) • (m : M) ∈ (F).N ((i + j : ℕ) : ℤ) := by
        rw [← hdegree]
        exact hsmul
      have hsingle (s t : ℤ) (h : s = t)
          (hs : (a : R) • (m : M) ∈ (F).N s)
          (ht : (a : R) • (m : M) ∈ (F).N t) :
          (F).single s ⟨(a : R) • (m : M), hs⟩ =
            (F).single t ⟨(a : R) • (m : M), ht⟩ := by
        subst t
        rfl
      rw [hsingle _ _ hdegree hsmul hnat]
      erw [adicAssociatedGradedMapR_single, adicAssociatedGradedMapR_single,
        AssociatedGradedModule.quotient_smul_mk]
      exact congrArg (AssociatedGradedModule.mk I M)
        (AssociatedGradedModule.monomial_smul_single I M (i := i) (j := j)
          (a : R) (m : M) a.property m.property).symm
  | negSucc j =>
      rw [adicSingle_eq_zero_of_neg I M _ (by simp)]
      simp

private theorem adicAssociatedGradedMapR_monomial_smul (i : ℕ) (a : ↥(I ^ i))
    (x : (F).AssociatedGraded) :
    adicAssociatedGradedMapR I M
        ((Ideal.Quotient.mk J (reesAlgebra.monomial I i a) : C) • x) =
      (Ideal.Quotient.mk J (reesAlgebra.monomial I i a) : C) •
        adicAssociatedGradedMapR I M x := by
  classical
  let c : C := Ideal.Quotient.mk J (reesAlgebra.monomial I i a)
  have h (n : ℤ) (z : (F).GradedPiece n) :
      adicAssociatedGradedMapR I M (c • (F).inclusion n z) =
        c • adicAssociatedGradedMapR I M ((F).inclusion n z) := by
    obtain ⟨m, rfl⟩ := (F).cl_surjective n z
    exact adicAssociatedGradedMapR_monomial_single I M i a n m
  calc
    adicAssociatedGradedMapR I M (c • x) =
        adicAssociatedGradedMapR I M
          (c • ∑ n ∈ (F).support x, (F).inclusion n ((F).component n x)) :=
      congrArg (fun y => adicAssociatedGradedMapR I M (c • y))
        ((F).sum_support_inclusion x).symm
    _ = ∑ n ∈ (F).support x,
        adicAssociatedGradedMapR I M (c • (F).inclusion n ((F).component n x)) := by
      simp only [Finset.smul_sum, map_sum]
    _ = ∑ n ∈ (F).support x,
        c • adicAssociatedGradedMapR I M ((F).inclusion n ((F).component n x)) :=
      Finset.sum_congr rfl (fun n _ => h n ((F).component n x))
    _ = c • adicAssociatedGradedMapR I M
        (∑ n ∈ (F).support x, (F).inclusion n ((F).component n x)) := by
      simp only [Finset.smul_sum, map_sum]
    _ = c • adicAssociatedGradedMapR I M x :=
      congrArg (fun y => c • adicAssociatedGradedMapR I M y) ((F).sum_support_inclusion x)

private theorem adicAssociatedGradedMapR_smul (c : C) (x : (F).AssociatedGraded) :
    adicAssociatedGradedMapR I M (c • x) = c • adicAssociatedGradedMapR I M x := by
  classical
  refine Quotient.inductionOn' c ?_
  intro b
  change adicAssociatedGradedMapR I M
      ((Ideal.Quotient.mk J b : C) • x) =
    (Ideal.Quotient.mk J b : C) • adicAssociatedGradedMapR I M x
  have hcoeff : ∀ i : ℕ, (b : Polynomial R).coeff i ∈ I ^ i := by
    exact b.property
  have hb : b = ∑ i ∈ (b : Polynomial R).support,
      reesAlgebra.monomial I i
        ⟨(b : Polynomial R).coeff i, hcoeff i⟩ := by
    apply Subtype.ext
    simpa using (b : Polynomial R).as_sum_support
  have hbC : (Ideal.Quotient.mk J b : C) =
      ∑ i ∈ (b : Polynomial R).support,
        (Ideal.Quotient.mk J
          (reesAlgebra.monomial I i
            ⟨(b : Polynomial R).coeff i, hcoeff i⟩) : C) := by
    simpa only [map_sum] using congrArg (Ideal.Quotient.mk J) hb
  rw [hbC]
  simp only [map_sum, Finset.sum_smul]
  exact Finset.sum_congr rfl (fun i _ =>
    adicAssociatedGradedMapR_monomial_smul I M i
      ⟨(b : Polynomial R).coeff i, hcoeff i⟩ x)

/-- The same direct comparison function, linear for the two fixed quotient Rees actions. -/
noncomputable def adicAssociatedGradedMap : (F).AssociatedGraded →ₗ[C] G where
  toFun := adicAssociatedGradedMapR I M
  map_add' := (adicAssociatedGradedMapR I M).map_add
  map_smul' := by
    intro c x
    exact adicAssociatedGradedMapR_smul I M c x

/-- Restricting the quotient Rees linear comparison recovers its original-ring map. -/
theorem adicAssociatedGradedMap_restrictScalars :
    (adicAssociatedGradedMap I M).restrictScalars R = adicAssociatedGradedMapR I M := by
  rfl

/-- The comparison sends a homogeneous stage class to the corresponding single class. -/
theorem adicAssociatedGradedMap_single (q : ℕ)
    (m : ↥(I ^ q • (⊤ : Submodule R M))) :
    adicAssociatedGradedMap I M ((F).single (q : ℤ) m) =
      AssociatedGradedModule.mk I M
        ⟨PolynomialModule.single R q (m : M),
          AssociatedGradedModule.single_mem I M q (m : M) m.property⟩ := by
  exact adicAssociatedGradedMapR_single I M q m

/-- Each coefficient is the image of the corresponding integer component under the
existing stage comparison; the final coercion is only into the ambient quotient. -/
theorem coefficient_adicAssociatedGradedMap (q : ℕ) (x : (F).AssociatedGraded) :
    AssociatedGradedModule.coefficient I M q (adicAssociatedGradedMap I M x) =
      ((AssociatedGradedModule.stageComparison I M q
        (Submodule.quotEquivOfEq _ _
          (AssociatedGradedModule.stage_denominator_eq I M q)
          (I.adicGradedPieceEquiv M q ((F).component (q : ℤ) x)))) :
        M ⧸ (I ^ (q + 1) • (⊤ : Submodule R M))) := by
  exact coefficient_adicAssociatedGradedMapR I M q x

/-- The comparison vanishes on inclusions in negative degrees. -/
theorem adicAssociatedGradedMap_inclusion_of_neg (n : ℤ) (hn : n < 0)
    (z : (F).GradedPiece n) :
    adicAssociatedGradedMap I M ((F).inclusion n z) = 0 := by
  let := I.adicIntFiltration_gradedPiece_subsingleton M n hn
  rw [Subsingleton.elim z 0, map_zero, map_zero]

private theorem adicAssociatedGradedMap_injective :
    Function.Injective (adicAssociatedGradedMap I M) := by
  intro x y hxy
  apply (F).associatedGraded_ext
  intro n
  cases n with
  | ofNat q =>
      apply (I.adicGradedPieceEquiv M q).injective
      apply (Submodule.quotEquivOfEq _ _
        (AssociatedGradedModule.stage_denominator_eq I M q)).injective
      apply (AssociatedGradedModule.stageComparison I M q).injective
      apply Subtype.ext
      exact (coefficient_adicAssociatedGradedMap I M q x).symm.trans
        ((congrArg (AssociatedGradedModule.coefficient I M q) hxy).trans
          (coefficient_adicAssociatedGradedMap I M q y))
  | negSucc j =>
      let := I.adicIntFiltration_gradedPiece_subsingleton M (Int.negSucc j) (by simp)
      exact Subsingleton.elim _ _

private theorem adicSingleton_sum
    (p : ↥((I.stableFiltration (⊤ : Submodule R M)).submodule)) :
    (∑ q ∈ (p : PolynomialModule R M).coeff.support,
      adicSingleton I M q ⟨(p : PolynomialModule R M).coeff q, p.property q⟩) = p := by
  classical
  symm
  apply Subtype.ext
  rw [Submodule.coe_sum]
  change (p : PolynomialModule R M) =
    ∑ q ∈ (p : PolynomialModule R M).coeff.support,
      PolynomialModule.single R q ((p : PolynomialModule R M).coeff q)
  calc
    (p : PolynomialModule R M) = PolynomialModule.ofCoeff R
        ((p : PolynomialModule R M).coeff.sum Finsupp.single) := by
      rw [Finsupp.sum_single, PolynomialModule.ofCoeff_coeff]
    _ = _ := PolynomialModule.ofCoeff_finsuppSum _ _

private theorem adicAssociatedGradedMap_sum_single
    (p : ↥((I.stableFiltration (⊤ : Submodule R M)).submodule)) :
    adicAssociatedGradedMap I M
        (∑ q ∈ (p : PolynomialModule R M).coeff.support,
          (F).single (q : ℤ) ⟨(p : PolynomialModule R M).coeff q, p.property q⟩) =
      AssociatedGradedModule.mk I M p := by
  classical
  simp only [map_sum]
  calc
    (∑ q ∈ (p : PolynomialModule R M).coeff.support,
        adicAssociatedGradedMap I M
          ((F).single (q : ℤ) ⟨(p : PolynomialModule R M).coeff q, p.property q⟩)) =
      ∑ q ∈ (p : PolynomialModule R M).coeff.support,
        AssociatedGradedModule.mk I M
          (adicSingleton I M q ⟨(p : PolynomialModule R M).coeff q, p.property q⟩) := by
            apply Finset.sum_congr rfl
            intro q _
            exact adicAssociatedGradedMap_single I M q
              ⟨(p : PolynomialModule R M).coeff q, p.property q⟩
    _ = AssociatedGradedModule.mk I M p := by
      rw [← map_sum, adicSingleton_sum]

private theorem adicAssociatedGradedMap_surjective :
    Function.Surjective (adicAssociatedGradedMap I M) := by
  classical
  intro g
  induction g using Submodule.Quotient.induction_on with
  | H p =>
      exact ⟨∑ q ∈ (p : PolynomialModule R M).coeff.support,
        (F).single (q : ℤ) ⟨(p : PolynomialModule R M).coeff q, p.property q⟩,
        adicAssociatedGradedMap_sum_single I M p⟩

/-- The ideal-adic integer associated graded and the existing coefficient quotient,
with their original modules and fixed quotient Rees actions. -/
noncomputable def adicAssociatedGradedEquiv : (F).AssociatedGraded ≃ₗ[C] G :=
  LinearEquiv.ofBijective (adicAssociatedGradedMap I M)
    (by exact ⟨adicAssociatedGradedMap_injective I M, adicAssociatedGradedMap_surjective I M⟩)

/-- The equivalence has the direct comparison as its underlying linear map. -/
theorem adicAssociatedGradedEquiv_toLinearMap :
    (adicAssociatedGradedEquiv I M).toLinearMap = adicAssociatedGradedMap I M := by
  rfl

/-- Each natural-degree component of the inverse is the existing stage comparison
applied backwards to the corresponding coefficient image. -/
theorem adicAssociatedGradedEquiv_symm_component_nat (q : ℕ) (g : G) :
    (F).component (q : ℤ) ((adicAssociatedGradedEquiv I M).symm g) =
      (I.adicGradedPieceEquiv M q).symm
        ((Submodule.quotEquivOfEq _ _
          (AssociatedGradedModule.stage_denominator_eq I M q)).symm
          ((AssociatedGradedModule.stageComparison I M q).symm
            ⟨AssociatedGradedModule.coefficient I M q g,
              AssociatedGradedModule.coefficient_mem I M q g⟩)) := by
  apply (I.adicGradedPieceEquiv M q).injective
  apply (Submodule.quotEquivOfEq _ _
    (AssociatedGradedModule.stage_denominator_eq I M q)).injective
  apply (AssociatedGradedModule.stageComparison I M q).injective
  apply Subtype.ext
  simp only [LinearEquiv.apply_symm_apply]
  have hmap : adicAssociatedGradedMap I M ((adicAssociatedGradedEquiv I M).symm g) = g :=
    (adicAssociatedGradedEquiv I M).apply_symm_apply g
  exact (coefficient_adicAssociatedGradedMap I M q
    ((adicAssociatedGradedEquiv I M).symm g)).symm.trans
      (congrArg (AssociatedGradedModule.coefficient I M q) hmap)

/-- Every negative-degree component of the inverse vanishes for the canonical adic
integer filtration. -/
theorem adicAssociatedGradedEquiv_symm_component_of_neg (n : ℤ) (hn : n < 0) (g : G) :
    (F).component n ((adicAssociatedGradedEquiv I M).symm g) = 0 := by
  let := I.adicIntFiltration_gradedPiece_subsingleton M n hn
  exact Subsingleton.elim _ _

/-- The inverse is finite reconstruction from the polynomial coefficients of a
representative; no choice of a scalar action is involved. -/
theorem adicAssociatedGradedEquiv_symm_mk
    (p : ↥((I.stableFiltration (⊤ : Submodule R M)).submodule)) :
    (adicAssociatedGradedEquiv I M).symm (AssociatedGradedModule.mk I M p) =
      ∑ q ∈ (p : PolynomialModule R M).coeff.support,
        (F).single (q : ℤ)
          ⟨(p : PolynomialModule R M).coeff q, p.property q⟩ := by
  classical
  apply (adicAssociatedGradedEquiv I M).injective
  rw [LinearEquiv.apply_symm_apply]
  exact (adicAssociatedGradedMap_sum_single I M p).symm

/-- In the regular specialization, the degree-zero unit maps to the existing regular
unit class, allowing composition with the existing regular linear equivalence. -/
theorem adicAssociatedGradedMap_regularUnit :
    adicAssociatedGradedMap I R
        ((I.adicIntFiltration R).single 0
          ⟨1, Ideal.mem_adicIntFiltration_N_of_nonpos I R 0 (le_refl 0) 1⟩) =
      AssociatedGradedModule.regularUnit I := by
  exact adicAssociatedGradedMap_single I R 0
    ⟨1, Ideal.mem_adicIntFiltration_N_of_nonpos I R 0 (le_refl 0) 1⟩

end Ideal
