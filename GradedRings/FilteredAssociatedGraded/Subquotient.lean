/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GradedRings.FilteredAssociatedGraded.Map

/-!
# Associated graded modules of induced submodules and quotients

For an integer filtration `F` on an `R`-module `M` and a submodule `S`, the
filtration on `S` is the pullback `F.comap S.subtype`, and the filtration on
`M ⧸ S` is the image `F.image S.mkQ`. The former is the induced filtration,
not an intrinsic ideal-adic filtration on `S`.

The canonical associated graded maps form an exact pair. The map from the
induced submodule filtration is injective, and the map onto the image filtration
is surjective. Quotienting the middle associated graded by the range of the
first map identifies it with the associated graded of the filtered quotient.
This equivalence and the associated quotient universal property are linear over
the Rees algebra modulo the extension of `I`.

All whole associated graded modules carry their canonical quotient Rees actions.
Individual graded pieces, their insertions and their projections retain their
original `R`-linear structures; positive-degree Rees scalars can change degree.
No finiteness, degree-zero normalization, exhaustivity, separatedness,
completeness or degree bound is required.

## References

* Mathlib's `Function.Exact.linearEquivOfSurjective` for the quotient by the
  range of the first map in an exact pair with surjective second map.
* Mathlib's submodule-quotient universal property.
-/

@[expose] public section

universe u v w

namespace Ideal.IntFiltration

variable {R : Type u} [CommRing R] {I : Ideal R}
variable {M : Type v} [AddCommGroup M] [Module R M]
variable (F : I.IntFiltration M) (S : Submodule R M)

local notation "B" => reesAlgebra I
local notation "J" => I.map (algebraMap R B)
local notation "C" => B ⧸ J

/-- The canonical maps from the induced submodule filtration and onto the image
quotient filtration are exact at the middle associated graded module. -/
theorem map_subtype_exact_map_mkQ :
    Function.Exact
      ((F.comap S.subtype).map F S.subtype (fun _ => le_rfl))
      (F.map (F.image S.mkQ) S.mkQ
        (fun _ => Submodule.map_le_iff_le_comap.mp le_rfl)) := by
  exact (F.comap S.subtype).map_exact_of_strict F S.subtype
    (F.image S.mkQ) S.mkQ (LinearMap.exact_subtype_mkQ S)
    (fun n => by
      rw [comap_N, Submodule.map_comap_subtype, Submodule.range_subtype])
    (fun n => by
      rw [image_N, Submodule.range_mkQ, top_inf_eq])

/-- The associated graded of the filtered quotient is the quotient of the middle
associated graded by the image of the induced submodule's associated graded. -/
noncomputable def subquotientEquiv :
    (F.AssociatedGraded ⧸ LinearMap.range
      ((F.comap S.subtype).map F S.subtype (fun _ => le_rfl))) ≃ₗ[C]
        (F.image S.mkQ).AssociatedGraded :=
  (F.map_subtype_exact_map_mkQ S).linearEquivOfSurjective
    (F.map_image_surjective S.mkQ)

/-- The subquotient equivalence sends a quotient class to its image under the
canonical associated graded quotient map. -/
@[simp]
theorem subquotientEquiv_mk (z : F.AssociatedGraded) :
    F.subquotientEquiv S (Submodule.Quotient.mk z) =
      F.map (F.image S.mkQ) S.mkQ
        (fun _ => Submodule.map_le_iff_le_comap.mp le_rfl) z := by
  exact Submodule.liftQ_apply _ _ (h := (F.map_subtype_exact_map_mkQ S · |>.mpr)) z

/-- On a homogeneous representative, the subquotient equivalence applies the
original quotient projection without changing the integer degree. -/
theorem subquotientEquiv_mk_single (n : ℤ) (m : F.N n) :
    F.subquotientEquiv S (Submodule.Quotient.mk (F.single n m)) =
      (F.image S.mkQ).single n
        ⟨S.mkQ (m : M), Submodule.mem_map.mpr ⟨(m : M), m.property, rfl⟩⟩ := by
  rw [subquotientEquiv_mk, map_single]

/-- The inverse subquotient equivalence takes a projected homogeneous
representative to the quotient class of its original representative. -/
theorem subquotientEquiv_symm_single (n : ℤ) (m : F.N n) :
    (F.subquotientEquiv S).symm
      ((F.image S.mkQ).single n
        ⟨S.mkQ (m : M), Submodule.mem_map.mpr ⟨(m : M), m.property, rfl⟩⟩) =
      Submodule.Quotient.mk (F.single n m) := by
  exact (F.subquotientEquiv S).symm_apply_eq.mpr
    (F.subquotientEquiv_mk_single S n m).symm

/-- A quotient-Rees-linear map killing the image of the induced submodule's
associated graded factors uniquely through the associated graded quotient map. -/
theorem existsUnique_lift_map_mkQ
    {T : Type w} [AddCommGroup T] [Module C T]
    (a : F.AssociatedGraded →ₗ[C] T)
    (ha : a.comp
      ((F.comap S.subtype).map F S.subtype (fun _ => le_rfl)) = 0) :
    ∃! b : (F.image S.mkQ).AssociatedGraded →ₗ[C] T,
      b.comp (F.map (F.image S.mkQ) S.mkQ
        (fun _ => Submodule.map_le_iff_le_comap.mp le_rfl)) = a := by
  let aQ := (LinearMap.range
    ((F.comap S.subtype).map F S.subtype (fun _ => le_rfl))).liftQ a
      (LinearMap.range_le_ker_iff.mpr ha)
  have hb :
      (aQ.comp (F.subquotientEquiv S).symm.toLinearMap).comp
        (F.map (F.image S.mkQ) S.mkQ
          (fun _ => Submodule.map_le_iff_le_comap.mp le_rfl)) = a := by
    apply LinearMap.ext
    intro z
    calc
      _ = aQ ((F.subquotientEquiv S).symm
          (F.subquotientEquiv S (Submodule.Quotient.mk z))) :=
        congrArg (fun y => aQ ((F.subquotientEquiv S).symm y))
          (F.subquotientEquiv_mk S z).symm
      _ = aQ (Submodule.Quotient.mk z) :=
        congrArg aQ ((F.subquotientEquiv S).symm_apply_apply _)
      _ = a z := Submodule.liftQ_apply _ _ z
  refine ⟨aQ.comp (F.subquotientEquiv S).symm.toLinearMap, hb, ?_⟩
  intro b hb'
  apply LinearMap.ext
  intro y
  obtain ⟨z, rfl⟩ := F.map_image_surjective S.mkQ y
  exact (LinearMap.congr_fun hb' z).trans (LinearMap.congr_fun hb z).symm

end Ideal.IntFiltration
