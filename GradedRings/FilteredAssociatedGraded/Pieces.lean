/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GradedRings.FilteredAssociatedGraded.Coefficients

/-!
# Residue coefficients on integer graded pieces

For an ideal-compatible integer filtration, each original graded piece is a
module over `R ⧸ I`. Insertion into and projection from the associated graded
are linear for these coefficients and the whole module's quotient Rees action
restricted to `R ⧸ I`. Their underlying functions and original `R`-linear maps
are unchanged. Representative formulas and finite reconstruction describe their
use without unfolding the constructions.

## Implementation notes

The piece module and its scalar tower are named non-instance data. For scalar
notation on a piece, locally activate `F.moduleQuotientGradedPiece n`, and for
scalar restriction also `F.isScalarTowerQuotientGradedPiece n`. When activating
the family for all degrees, first pin the whole module to `F.moduleQuotient`:
the generic direct-sum module otherwise provides another whole-module dictionary.
The bundled maps below explicitly use `F.moduleQuotient` and require no such
activation by their callers. No residue action on the stages or ambient stage
quotients is asserted; `F.cl n` remains an original-`R`-linear map.

## References

* Mathlib's `Function.Injective.module` pulls the module laws back along the
  original additive inclusion, with scalar multiplication given by projection
  of the whole action.
* Mathlib's `LinearMap.extendScalarsOfSurjective` upgrades the original linear
  maps without changing their functions.
-/

@[expose] public section

universe u v

noncomputable section

namespace Ideal.IntFiltration

variable {R : Type u} [CommRing R] {I : Ideal R}
variable {M : Type v} [AddCommGroup M] [Module R M] (F : I.IntFiltration M)

local notation "A" => R ⧸ I
local notation "G" => F.AssociatedGraded

/-- The whole residue module used before introducing the piece scalar multiplication. -/
local instance : Module A G := F.moduleQuotient

/-- Residue coefficients on an original graded piece, obtained by projecting the
whole associated-graded action after insertion. This is named non-instance data. -/
@[instance_reducible]
noncomputable def moduleQuotientGradedPiece (n : ℤ) : Module A (F.GradedPiece n) := by
  letI : SMul A (F.GradedPiece n) :=
    ⟨fun a z => F.component n (a • F.inclusion n z)⟩
  exact Function.Injective.module A (F.inclusion n).toAddMonoidHom
    (F.inclusion_injective n) (by
      intro a z
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
      change F.inclusion n
        (F.component n ((Ideal.Quotient.mk I r : A) • F.inclusion n z)) =
          (Ideal.Quotient.mk I r : A) • F.inclusion n z
      rw [F.quotient_mk_smul, map_smul, F.component_inclusion, map_smul])

attribute [local instance] moduleQuotientGradedPiece

/-- Piece scalar multiplication is projection of the whole action on its insertion. -/
theorem gradedPiece_smul_def (n : ℤ) (a : A) (z : F.GradedPiece n) :
    a • z = F.component n (a • F.inclusion n z) := rfl

/-- A residue coefficient acts on the piece by its original scalar representative. -/
@[simp]
theorem quotient_mk_smul_gradedPiece (n : ℤ) (r : R) (z : F.GradedPiece n) :
    (Ideal.Quotient.mk I r : A) • z = r • z := by
  rw [gradedPiece_smul_def, F.quotient_mk_smul, map_smul, F.component_inclusion]

/-- The piece's residue action is compatible with its original `R` action.
This is a named non-instance scalar tower. -/
theorem isScalarTowerQuotientGradedPiece (n : ℤ) :
    IsScalarTower R A (F.GradedPiece n) :=
  IsScalarTower.of_algebraMap_smul fun r z => F.quotient_mk_smul_gradedPiece n r z

attribute [local instance] isScalarTowerQuotientGradedPiece

/-- Residue-linear insertion with the original inclusion as its underlying function
and `F.moduleQuotient` as its whole-module structure. -/
noncomputable def inclusionQuotient (n : ℤ) :
    @LinearMap A A _ _ (RingHom.id A) (F.GradedPiece n) G _ _
      (F.moduleQuotientGradedPiece n) F.moduleQuotient := by
  exact LinearMap.extendScalarsOfSurjective
    (by
      intro a
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
      exact ⟨r, rfl⟩) (F.inclusion n)

/-- Residue-linear projection with the original component as its underlying function
and `F.moduleQuotient` as its whole-module structure. -/
noncomputable def componentQuotient (n : ℤ) :
    @LinearMap A A _ _ (RingHom.id A) G (F.GradedPiece n) _ _
      F.moduleQuotient (F.moduleQuotientGradedPiece n) := by
  exact LinearMap.extendScalarsOfSurjective
    (by
      intro a
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
      exact ⟨r, rfl⟩) (F.component n)

/-- Residue-linear insertion has the same value as original-linear insertion. -/
@[simp]
theorem inclusionQuotient_apply (n : ℤ) (z : F.GradedPiece n) :
    F.inclusionQuotient n z = F.inclusion n z := rfl

/-- Residue-linear projection has the same value as original-linear projection. -/
@[simp]
theorem componentQuotient_apply (n : ℤ) (x : G) :
    F.componentQuotient n x = F.component n x := rfl

/-- Restriction of residue-linear insertion recovers the original bundled `R`-linear map. -/
@[simp]
theorem inclusionQuotient_restrictScalars (n : ℤ) :
    (F.inclusionQuotient n).restrictScalars R = F.inclusion n := rfl

/-- Restriction of residue-linear projection recovers the original bundled `R`-linear map. -/
@[simp]
theorem componentQuotient_restrictScalars (n : ℤ) :
    (F.componentQuotient n).restrictScalars R = F.component n := rfl

/-- Insertion followed by projection to the same degree recovers the piece. -/
theorem componentQuotient_inclusionQuotient (n : ℤ) (z : F.GradedPiece n) :
    F.componentQuotient n (F.inclusionQuotient n z) = z :=
  F.component_inclusion n z

/-- Insertion has zero projection in every other degree. -/
theorem componentQuotient_inclusionQuotient_of_ne (n k : ℤ) (h : k ≠ n)
    (z : F.GradedPiece n) :
    F.componentQuotient k (F.inclusionQuotient n z) = 0 :=
  F.component_inclusion_of_ne n k h z

/-- Inserting a stage class gives its homogeneous representative insertion. -/
theorem inclusionQuotient_cl (n : ℤ) (m : F.N n) :
    F.inclusionQuotient n (F.cl n m) = F.single n m := rfl

/-- Projection of a homogeneous representative to its own degree gives its piece class. -/
theorem componentQuotient_single (n : ℤ) (m : F.N n) :
    F.componentQuotient n (F.single n m) = F.cl n m :=
  F.component_single n m

/-- Projection of a homogeneous representative to another degree vanishes. -/
theorem componentQuotient_single_of_ne (n k : ℤ) (h : k ≠ n) (m : F.N n) :
    F.componentQuotient k (F.single n m) = 0 :=
  F.component_single_of_ne n k h m

/-- A residue representative acts on a stage class by the original stage scalar action.
The class map is still `R`-linear; its source is not given residue scalars. -/
theorem cl_quotient_mk_smul (n : ℤ) (r : R) (m : F.N n) :
    (Ideal.Quotient.mk I r : A) • F.cl n m = F.cl n (r • m) := by
  rw [F.quotient_mk_smul_gradedPiece, map_smul]

/-- Finite reconstruction using residue-linear insertion and projection and the original support. -/
theorem sum_support_inclusionQuotient (x : G) :
    ∑ n ∈ F.support x, F.inclusionQuotient n (F.componentQuotient n x) = x := by
  simpa only [inclusionQuotient_apply, componentQuotient_apply] using F.sum_support_inclusion x

/-- The whole residue action is componentwise for the named piece actions. -/
theorem component_quotient_smul (n : ℤ) (a : A) (x : G) :
    F.component n (a • x) = a • F.component n x :=
  (F.componentQuotient n).map_smul a x

end Ideal.IntFiltration

end
