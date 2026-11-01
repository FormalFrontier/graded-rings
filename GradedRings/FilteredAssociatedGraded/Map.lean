/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GradedRings.FilteredAssociatedGraded.ReesAction

/-!
# Maps and equivalences on integer-filtered associated graded modules

An original-`R`-linear map preserving every stage of two integer filtrations
induces a degree-preserving map on their associated graded modules. An
original-`R`-linear equivalence carrying each stage onto the corresponding stage
induces a linear equivalence with the maps of the original equivalence and its
inverse as its two directions. The scalar ring is the Rees algebra modulo the
extension of the filtration ideal, with the canonical quotient Rees actions on
both modules.

The constructions apply to all integer degrees and do not require finiteness,
exhaustivity, separatedness or a lower bound. Stage quotients and their direct
sum use Mathlib's `Submodule.mapQ` and `DirectSum.lmap`; equivalences use
`LinearEquiv.ofLinearMap`.

The induced map is injective exactly when a source-stage element mapping into the
next target stage already belongs to the next source stage. It is surjective
exactly when the source-stage image and the next target stage cover each target
stage. Stagewise pullback and image equalities give injectivity and surjectivity,
respectively, without requiring the original linear map to be injective or
surjective.

## References

* Mathlib's submodule-quotient and direct-sum universal properties.
-/

@[expose] public section

universe u v w x

namespace Ideal.IntFiltration

variable {R : Type u} [CommRing R] {I : Ideal R}
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]
variable (F : I.IntFiltration M) (H : I.IntFiltration N)
variable (f : M →ₗ[R] N) (hf : ∀ n, F.N n ≤ (H.N n).comap f)

private def stageMap (n : ℤ) : F.N n →ₗ[R] H.N n where
  toFun m := ⟨f (m : M), hf n m.property⟩
  map_add' m m' := Subtype.ext (f.map_add (m : M) (m' : M))
  map_smul' r m := Subtype.ext (f.map_smul r (m : M))

private theorem stageMap_coe (n : ℤ) (m : F.N n) :
    (stageMap F H f hf n m : N) = f (m : M) := rfl

private theorem nextStage_le_comap (n : ℤ) :
    F.nextStage n ≤ (H.nextStage n).comap (stageMap F H f hf n) := by
  intro m hm
  exact hf (n + 1) hm

private def pieceMap (n : ℤ) : F.GradedPiece n →ₗ[R] H.GradedPiece n :=
  (F.nextStage n).mapQ (H.nextStage n) (stageMap F H f hf n)
    (nextStage_le_comap F H f hf n)

private theorem pieceMap_cl (n : ℤ) (m : F.N n) :
    pieceMap F H f hf n (F.cl n m) = H.cl n (stageMap F H f hf n m) := rfl

private def mapR : F.AssociatedGraded →ₗ[R] H.AssociatedGraded :=
  DirectSum.lmap (pieceMap F H f hf)

private theorem mapR_inclusion (n : ℤ) (z : F.GradedPiece n) :
    mapR F H f hf (F.inclusion n z) = H.inclusion n (pieceMap F H f hf n z) :=
  DirectSum.lmap_lof (pieceMap F H f hf) n z

private theorem mapR_single (n : ℤ) (m : F.N n) :
    mapR F H f hf (F.single n m) = H.single n (stageMap F H f hf n m) := by
  rw [single_apply, mapR_inclusion, pieceMap_cl]
  rfl

private theorem component_mapR (n : ℤ) (z : F.AssociatedGraded) :
    H.component n (mapR F H f hf z) = pieceMap F H f hf n (F.component n z) := rfl

local notation "B" => reesAlgebra I
local notation "J" => I.map (algebraMap R B)
local notation "C" => B ⧸ J

private theorem mapR_monomial_smul (q : ℕ) (a : ↥(I ^ q))
    (z : F.AssociatedGraded) :
    mapR F H f hf ((Ideal.Quotient.mk J (reesAlgebra.monomial I q a) : C) • z) =
      (Ideal.Quotient.mk J (reesAlgebra.monomial I q a) : C) • mapR F H f hf z := by
  -- Compare original-linear maps, so stage representatives suffice even though
  -- the monomial action shifts their integer degrees.
  have h :
      (mapR F H f hf).comp
          (F.reesQuotientRepresentation (Ideal.Quotient.mk J (reesAlgebra.monomial I q a))) =
        (H.reesQuotientRepresentation
          (Ideal.Quotient.mk J (reesAlgebra.monomial I q a))).comp (mapR F H f hf) := by
    apply F.linearMap_ext
    intro n m
    simp only [LinearMap.comp_apply, reesQuotientRepresentation_apply,
      monomial_smul_single, mapR_single]
    apply congrArg (H.single (n + (q : ℤ)))
    exact Subtype.ext (f.map_smul (a : R) (m : M))
  simpa only [LinearMap.comp_apply, reesQuotientRepresentation_apply] using
    LinearMap.congr_fun h z

private theorem mapR_quotient_smul (c : C) (z : F.AssociatedGraded) :
    mapR F H f hf (c • z) = c • mapR F H f hf z := by
  -- Use the canonical image grading, without choosing a new scalar action or
  -- implementing a second decomposition of the quotient Rees algebra.
  induction c using DirectSum.Decomposition.inductionOn
      (reesAlgebra.quotientHomogeneousComponent I) with
  | zero =>
      change mapR F H f hf (F.reesQuotientRepresentation 0 z) =
        H.reesQuotientRepresentation 0 (mapR F H f hf z)
      have hF : F.reesQuotientRepresentation (0 : C) =
          (0 : Module.End R F.AssociatedGraded) :=
        _root_.map_zero F.reesQuotientRepresentation
      have hH : H.reesQuotientRepresentation (0 : C) =
          (0 : Module.End R H.AssociatedGraded) :=
        _root_.map_zero H.reesQuotientRepresentation
      calc
        mapR F H f hf (F.reesQuotientRepresentation 0 z) =
            mapR F H f hf 0 :=
          congrArg (mapR F H f hf)
            (congrArg (fun e : Module.End R F.AssociatedGraded => e z) hF)
        _ = 0 := (mapR F H f hf).map_zero
        _ = H.reesQuotientRepresentation 0 (mapR F H f hf z) :=
          (congrArg (fun e : Module.End R H.AssociatedGraded =>
            e (mapR F H f hf z)) hH).symm
  | homogeneous c =>
      obtain ⟨p, hp, hpc⟩ :=
        (reesAlgebra.mem_quotientHomogeneousComponent_iff I _ (c : C)).mp c.property
      obtain ⟨a, ha⟩ := (reesAlgebra.mem_homogeneousComponent_iff I _ p).mp hp
      simpa only [ha, hpc] using mapR_monomial_smul F H f hf _ a z
  | add c d hc hd => simp only [add_smul, map_add, hc, hd]

/-- The quotient-Rees-linear map induced by an original-linear stage-preserving map. -/
noncomputable def map : F.AssociatedGraded →ₗ[C] H.AssociatedGraded where
  toFun := private mapR F H f hf
  map_add' := by
    exact (mapR F H f hf).map_add
  map_smul' := by
    intro c z
    exact mapR_quotient_smul F H f hf c z

/-- The induced map applies the original linear map to each homogeneous representative. -/
@[simp]
theorem map_single (n : ℤ) (m : F.N n) :
    F.map H f hf (F.single n m) = H.single n ⟨f (m : M), hf n m.property⟩ := by
  exact mapR_single F H f hf n m

/-- The identity map induces the identity on the associated graded module. -/
@[simp]
theorem map_id :
    F.map F (LinearMap.id : M →ₗ[R] M) (fun _ _ hm => hm) =
      (LinearMap.id : F.AssociatedGraded →ₗ[C] F.AssociatedGraded) := by
  have h :
      mapR F F (LinearMap.id : M →ₗ[R] M) (fun _ _ hm => hm) =
        (LinearMap.id : F.AssociatedGraded →ₗ[R] F.AssociatedGraded) := by
    apply F.linearMap_ext
    intro n m
    exact mapR_single F F (LinearMap.id : M →ₗ[R] M) (fun _ _ hm => hm) n m
  apply LinearMap.ext
  intro z
  exact LinearMap.congr_fun h z

variable {P : Type x} [AddCommGroup P] [Module R P]

/-- Taking associated graded maps preserves composition of stage-preserving linear maps. -/
theorem map_comp (K : I.IntFiltration P) (g : N →ₗ[R] P)
    (hg : ∀ n, H.N n ≤ (K.N n).comap g) :
    F.map K (g.comp f) (fun n _ hm => hg n (hf n hm)) =
      (H.map K g hg).comp (F.map H f hf) := by
  have h :
      mapR F K (g.comp f) (fun n _ hm => hg n (hf n hm)) =
        (mapR H K g hg).comp (mapR F H f hf) := by
    apply F.linearMap_ext
    intro n m
    simp only [LinearMap.comp_apply, mapR_single, stageMap]
    rfl
  apply LinearMap.ext
  intro z
  exact LinearMap.congr_fun h z

section MapCriteria

/-- The induced map is injective exactly when a source-stage element mapping into the next
target stage already belongs to the next source stage. -/
theorem map_injective_iff :
    Function.Injective (F.map H f hf) ↔
      ∀ (n : ℤ) (x : M), x ∈ F.N n → f x ∈ H.N (n + 1) → x ∈ F.N (n + 1) := by
  change Function.Injective (DirectSum.lmap (pieceMap F H f hf)) ↔ _
  rw [DirectSum.lmap_injective]
  constructor
  · intro h n x hx hfx
    apply (F.cl_eq_zero_iff n ⟨x, hx⟩).mp
    apply h n
    rw [pieceMap_cl, map_zero]
    exact (H.cl_eq_zero_iff n _).mpr hfx
  · intro h n
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    obtain ⟨x, rfl⟩ := F.cl_surjective n z
    apply (F.cl_eq_zero_iff n x).mpr
    apply h n x x.property
    exact (H.cl_eq_zero_iff n _).mp ((pieceMap_cl F H f hf n x).symm.trans hz)

/-- The induced map is surjective exactly when every target stage is covered by the image
of the source stage modulo the next target stage. -/
theorem map_surjective_iff :
    Function.Surjective (F.map H f hf) ↔
      ∀ n : ℤ, H.N n ≤ (F.N n).map f ⊔ H.N (n + 1) := by
  change Function.Surjective (DirectSum.lmap (pieceMap F H f hf)) ↔ _
  rw [DirectSum.lmap_surjective]
  constructor
  · intro hs n y hy
    obtain ⟨z, hz⟩ := hs n (H.cl n ⟨y, hy⟩)
    obtain ⟨x, rfl⟩ := F.cl_surjective n z
    rw [pieceMap_cl] at hz
    have hyx : y - f (x : M) ∈ H.N (n + 1) :=
      (H.cl_eq_cl_iff n ⟨y, hy⟩ (stageMap F H f hf n x)).mp hz.symm
    exact Submodule.mem_sup.mpr
      ⟨f (x : M), Submodule.mem_map.mpr ⟨(x : M), x.property, rfl⟩,
        y - f (x : M), hyx, (add_comm _ _).trans (sub_add_cancel _ _)⟩
  · intro h n z
    obtain ⟨y, rfl⟩ := H.cl_surjective n z
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp (h n y.property)
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp ha
    refine ⟨F.cl n ⟨x, hx⟩, ?_⟩
    rw [pieceMap_cl, H.cl_eq_cl_iff, stageMap_coe, ← hab,
      sub_add_eq_sub_sub, sub_self, zero_sub]
    exact (H.N (n + 1)).neg_mem hb

/-- Stagewise pullback equality makes the induced map injective, without requiring
injectivity of the original linear map. -/
theorem map_injective_of_comap_eq (he : ∀ n : ℤ, F.N n = (H.N n).comap f) :
    Function.Injective (F.map H f (fun n => (he n).le)) := by
  apply (F.map_injective_iff H f (fun n => (he n).le)).mpr
  intro n x _ hx
  exact (he (n + 1)).ge hx

/-- Stagewise image equality makes the induced map surjective, without requiring
surjectivity of the original linear map. -/
theorem map_surjective_of_map_eq (he : ∀ n : ℤ, (F.N n).map f = H.N n) :
    Function.Surjective
      (F.map H f (fun n => Submodule.map_le_iff_le_comap.mp (he n).le)) := by
  apply (F.map_surjective_iff H f
    (fun n => Submodule.map_le_iff_le_comap.mp (he n).le)).mpr
  intro n
  rw [he n]
  exact le_sup_left

end MapCriteria

section Equivalences

variable (e : M ≃ₗ[R] N) (he : ∀ n, (F.N n).map e.toLinearMap = H.N n)

/-- An original-linear equivalence carrying every integer stage onto its counterpart
induces a quotient-Rees-linear equivalence of the whole associated graded modules. -/
noncomputable def equiv : F.AssociatedGraded ≃ₗ[C] H.AssociatedGraded :=
  LinearEquiv.ofLinearMap
    (F.map H e.toLinearMap
      (fun n => Submodule.map_le_iff_le_comap.mp (he n).le))
    (H.map F e.symm.toLinearMap
      (fun n => ((he n).symm.trans
        (Submodule.map_equiv_eq_comap_symm e (F.N n))).le))
    (by
      have h : e.toLinearMap.comp e.symm.toLinearMap =
          (LinearMap.id : N →ₗ[R] N) := by
        ext m
        exact e.apply_symm_apply m
      rw [← map_comp]
      simpa only [h] using H.map_id)
    (by
      have h : e.symm.toLinearMap.comp e.toLinearMap =
          (LinearMap.id : M →ₗ[R] M) := by
        ext m
        exact e.symm_apply_apply m
      rw [← map_comp]
      simpa only [h] using F.map_id)

/-- The forward linear map is the associated graded map of the original equivalence. -/
@[simp]
theorem equiv_toLinearMap :
    (F.equiv H e he).toLinearMap =
      F.map H e.toLinearMap
        (fun n => Submodule.map_le_iff_le_comap.mp (he n).le) := by
  rfl

/-- The induced equivalence applies the original equivalence to each representative. -/
@[simp]
theorem equiv_single (n : ℤ) (m : F.N n) :
    F.equiv H e he (F.single n m) =
      H.single n
        ⟨e (m : M), (Submodule.map_le_iff_le_comap.mp (he n).le) m.property⟩ := by
  change (F.equiv H e he).toLinearMap (F.single n m) = _
  rw [equiv_toLinearMap, map_single]
  rfl

/-- Taking the inverse commutes with the induced associated graded equivalence. -/
@[simp]
theorem equiv_symm :
    (F.equiv H e he).symm =
      H.equiv F e.symm (fun n => (Submodule.map_symm_eq_iff e).mpr (he n)) := by
  apply LinearEquiv.toLinearMap_injective
  rfl

/-- The original identity equivalence induces the identity associated graded equivalence. -/
@[simp]
theorem equiv_refl :
    F.equiv F (LinearEquiv.refl R M)
        (fun n => by
          simpa only [LinearEquiv.refl_toLinearMap] using Submodule.map_id (F.N n)) =
      LinearEquiv.refl C F.AssociatedGraded := by
  apply LinearEquiv.toLinearMap_injective
  simpa only [equiv_toLinearMap, LinearEquiv.refl_toLinearMap] using F.map_id

/-- Inducing associated graded equivalences commutes with composition. -/
theorem equiv_trans (K : I.IntFiltration P) (d : N ≃ₗ[R] P)
    (hd : ∀ n, (H.N n).map d.toLinearMap = K.N n) :
    F.equiv K (e.trans d)
        (fun n => (Submodule.map_comp e.toLinearMap d.toLinearMap (F.N n)).trans
          ((congrArg (Submodule.map d.toLinearMap) (he n)).trans (hd n))) =
      (F.equiv H e he).trans (H.equiv K d hd) := by
  apply LinearEquiv.toLinearMap_injective
  change (F.equiv K (e.trans d)
    (fun n => (Submodule.map_comp e.toLinearMap d.toLinearMap (F.N n)).trans
      ((congrArg (Submodule.map d.toLinearMap) (he n)).trans (hd n)))).toLinearMap =
        (H.equiv K d hd).toLinearMap.comp (F.equiv H e he).toLinearMap
  simp only [equiv_toLinearMap]
  exact F.map_comp H e.toLinearMap
    (fun n => Submodule.map_le_iff_le_comap.mp (he n).le)
    K d.toLinearMap
    (fun n => Submodule.map_le_iff_le_comap.mp (hd n).le)

end Equivalences

end Ideal.IntFiltration

