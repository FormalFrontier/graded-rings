/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GradedRings.FilteredAssociatedGraded.AdicMap
public import GradedRings.FilteredAssociatedGraded.AdicComparison
public import GradedRings.ReesModule.Map

/-!
# Naturality of the ideal-adic associated graded comparison

The canonical comparison from the integer ideal-adic associated graded to the
quotient Rees module is natural for every original-ring linear map. Both routes
are linear for the existing quotient Rees actions. The map on the quotient Rees
module is its independently defined coefficientwise polynomial map, not a
comparison conjugate.

The forward square is checked on homogeneous stage representatives: in natural
degrees both routes give the same polynomial singleton class, and in negative
degrees the source pieces vanish. The inverse square follows from the forward
one and the inverse identities of the existing equivalences. No finiteness,
completeness, separatedness or nontriviality assumption is needed.

## References

* `GradedRings.FilteredAssociatedGraded.AdicComparison` supplies the comparison
  and its homogeneous representative formula.
* `GradedRings.ReesModule.Map` supplies the coefficientwise quotient Rees map.
* The original-linear extensionality API of
  `GradedRings.FilteredAssociatedGraded` reduces the square to representatives.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v w

namespace Ideal

variable {R : Type u} [CommRing R] (I : Ideal R)
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

local notation "Fₘ" => I.adicIntFiltration M

/-- In every natural degree the forward route has the original old singleton class. -/
theorem adicAssociatedGradedEquiv_hom_single (f : M →ₗ[R] N) (q : ℕ)
    (m : ↥(I ^ q • (⊤ : Submodule R M))) :
    adicAssociatedGradedEquiv I N
        (adicAssociatedGradedHom I f ((Fₘ).single (q : ℤ) m)) =
      AssociatedGradedModule.mk I N
        ⟨PolynomialModule.single R q (f (m : M)),
          AssociatedGradedModule.single_mem I N q (f (m : M))
            (Submodule.smul_top_le_comap_smul_top (I ^ q) f m.property)⟩ := by
  exact (congrArg (adicAssociatedGradedEquiv I N)
    (adicAssociatedGradedHom_single I f (q : ℤ) m)).trans
      (adicAssociatedGradedMap_single I N q
        ⟨f (m : M), Submodule.smul_top_le_comap_smul_top (I ^ q) f m.property⟩)

/-- The canonical adic comparison is natural for original-ring linear maps. -/
theorem adicAssociatedGradedEquiv_naturality (f : M →ₗ[R] N) :
    (adicAssociatedGradedEquiv I N).toLinearMap.comp
        (adicAssociatedGradedHom I f) =
      (AssociatedGradedModule.map I f).comp
        (adicAssociatedGradedEquiv I M).toLinearMap := by
  apply LinearMap.restrictScalars_injective R
  apply (Fₘ).linearMap_ext
  intro n m
  simp only [LinearMap.restrictScalars_apply, LinearMap.comp_apply,
    adicAssociatedGradedEquiv_toLinearMap]
  cases n with
  | ofNat q =>
      exact (adicAssociatedGradedEquiv_hom_single I f q m).trans
        ((AssociatedGradedModule.map_single I f q (m : M) m.property).symm.trans
          (congrArg (AssociatedGradedModule.map I f)
            (adicAssociatedGradedMap_single I M q m).symm))
  | negSucc k =>
      have hs : (Fₘ).single (Int.negSucc k) m = 0 := by
        let := I.adicIntFiltration_gradedPiece_subsingleton M (Int.negSucc k) (by simp)
        rw [IntFiltration.single_apply,
          Subsingleton.elim ((Fₘ).cl (Int.negSucc k) m) 0, map_zero]
      simp only [hs, map_zero]

/-- The inverse comparisons form the inverse natural square. -/
theorem adicAssociatedGradedEquiv_symm_naturality (f : M →ₗ[R] N) :
    (adicAssociatedGradedEquiv I N).symm.toLinearMap.comp
        (AssociatedGradedModule.map I f) =
      (adicAssociatedGradedHom I f).comp
        (adicAssociatedGradedEquiv I M).symm.toLinearMap := by
  apply LinearMap.ext
  intro z
  apply (adicAssociatedGradedEquiv I N).injective
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearEquiv.apply_symm_apply] using
      (LinearMap.congr_fun (adicAssociatedGradedEquiv_naturality I f)
        ((adicAssociatedGradedEquiv I M).symm z)).symm

end Ideal
