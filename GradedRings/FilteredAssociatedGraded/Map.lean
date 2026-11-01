/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GradedRings.FilteredAssociatedGraded.ReesAction

/-!
# Maps on integer-filtered associated graded modules

An original-`R`-linear map preserving every stage of two integer filtrations
induces a degree-preserving map on their associated graded modules. The scalar
ring is the Rees algebra modulo the extension of the filtration ideal, with the
canonical quotient Rees actions on both modules.

The construction applies to all integer degrees and does not require finiteness,
exhaustivity, separatedness or a lower bound. Stage quotients and their direct
sum use Mathlib's `Submodule.mapQ` and `DirectSum.lmap`.

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

end Ideal.IntFiltration

