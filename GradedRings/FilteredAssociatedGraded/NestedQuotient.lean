/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GradedRings.FilteredAssociatedGraded.Subquotient

/-!
# Nested induced quotients of integer-filtered modules

For submodules `S ≤ T` of an integer-filtered module `M`, put
`U = T.map S.mkQ`. The filtration induced on `U` from the image filtration on
`M ⧸ S` is the image of the filtration induced on `T`. The third isomorphism
`(M ⧸ S) ⧸ U ≃ₗ[R] M ⧸ T` carries every iterated image stage onto the direct
image stage.

On whole associated graded modules, let `A` and `B` be the ranges of the induced
`S` and `T` inclusions. The subquotient equivalence for `S` carries the image of
`B` in `gr(F) ⧸ A` onto the range of the induced `U` inclusion. Consequently,
quotient congruence followed by the subquotient equivalence for `U` and the
associated graded third isomorphism agrees with the third isomorphism over the
quotient Rees algebra followed by the subquotient equivalence for `T`.

The scalar ring of every whole associated graded and its range quotient is
`C = reesAlgebra I ⧸ I.map (algebraMap R (reesAlgebra I))`, with the canonical
actions. Individual pieces retain their original `R`-linear structures. All
stages are indexed by integers; no finiteness, normalization, exhaustivity,
separatedness, completeness or splitting is required. Submodule filtrations are
induced filtrations, not intrinsic ideal-adic filtrations.

## References

* Mathlib's `Submodule.quotientQuotientEquivQuotient` for the third isomorphism
  theorem for modules, used over both `R` and the quotient Rees algebra.
* Mathlib's `Submodule.Quotient.equiv` for quotient congruence and its submodule
  image and inverse-image API for the modular filtration identity.
-/

@[expose] public section

universe u v

namespace Ideal.IntFiltration

variable {R : Type u} [CommRing R] {I : Ideal R}
variable {M : Type v} [AddCommGroup M] [Module R M]
variable (F : I.IntFiltration M) (S T : Submodule R M)

local notation "C" =>
  reesAlgebra I ⧸ Ideal.map (algebraMap R (reesAlgebra I)) I
local notation "U" => Submodule.map (Submodule.mkQ S) T
local notation "FS" => Ideal.IntFiltration.image F (Submodule.mkQ S)
local notation "FT" => Ideal.IntFiltration.image F (Submodule.mkQ T)
local notation "FST" => Ideal.IntFiltration.image FS (Submodule.mkQ U)
local notation "k" =>
  LinearMap.restrict (Submodule.mkQ S)
    (Submodule.le_comap_map (Submodule.mkQ S) T)

/-- For `S ≤ T`, the image of the filtration induced on `T` under the restricted
quotient map is the filtration induced on `T.map S.mkQ` from the image filtration
on `M ⧸ S`. This is the modular submodule identity in every integer stage. -/
theorem image_comap_restrict_mkQ (hST : S ≤ T) :
    Ideal.IntFiltration.image
        (Ideal.IntFiltration.comap F (Submodule.subtype T)) k =
      Ideal.IntFiltration.comap FS (Submodule.subtype U) := by
  apply Ideal.IntFiltration.ext
  intro n
  apply Submodule.ext
  intro y
  constructor
  · intro hy
    obtain ⟨t, ht, hty⟩ := (mem_image (F.comap T.subtype) k n y).mp hy
    apply (mem_comap FS (Submodule.subtype U) n y).mpr
    apply (mem_image F S.mkQ n (y : M ⧸ S)).mpr
    refine ⟨(t : M), (mem_comap F T.subtype n t).mp ht, ?_⟩
    exact congrArg (fun u : U => (u : M ⧸ S)) hty
  · intro hy
    have hy' := (mem_comap FS (Submodule.subtype U) n y).mp hy
    obtain ⟨m, hm, hmy⟩ := (mem_image F S.mkQ n (y : M ⧸ S)).mp hy'
    obtain ⟨t, ht, hty⟩ := Submodule.mem_map.mp y.property
    have hmt : m - t ∈ S :=
      (Submodule.Quotient.eq S).mp (hmy.trans hty.symm)
    have hmT : m ∈ T := by
      simpa only [sub_add_cancel] using T.add_mem (hST hmt) ht
    apply (mem_image (F.comap T.subtype) k n y).mpr
    refine ⟨⟨m, hmT⟩, (mem_comap F T.subtype n _).mpr hm, ?_⟩
    exact Subtype.ext hmy

/-- The third isomorphism theorem for `S ≤ T` carries every iterated image stage
onto the corresponding direct image stage. -/
theorem image_image_quotientQuotientEquivQuotient_N (hST : S ≤ T) (n : ℤ) :
    Submodule.map
        (LinearEquiv.toLinearMap
          (Submodule.quotientQuotientEquivQuotient S T hST))
        (Ideal.IntFiltration.N FST n) =
      Ideal.IntFiltration.N FT n := by
  have hcomp :
      (Submodule.quotientQuotientEquivQuotient S T hST).toLinearMap.comp
          ((Submodule.mkQ U).comp (Submodule.mkQ S)) =
        Submodule.mkQ T := by
    ext m
    exact Submodule.quotientQuotientEquivQuotientAux_mk_mk S T hST m
  simpa only [image_N, Submodule.map_comp] using
    congrArg (fun f : M →ₗ[R] M ⧸ T => (F.N n).map f) hcomp

local notation "G" => Ideal.IntFiltration.AssociatedGraded F
local notation "A" =>
  LinearMap.range
    (Ideal.IntFiltration.map (Ideal.IntFiltration.comap F (Submodule.subtype S))
      F (Submodule.subtype S) (fun _ => le_rfl))
local notation "B" =>
  LinearMap.range
    (Ideal.IntFiltration.map (Ideal.IntFiltration.comap F (Submodule.subtype T))
      F (Submodule.subtype T) (fun _ => le_rfl))
local notation "Bbar" => Submodule.map (Submodule.mkQ A) B
local notation "D" =>
  LinearMap.range
    (Ideal.IntFiltration.map (Ideal.IntFiltration.comap FS (Submodule.subtype U))
      FS (Submodule.subtype U) (fun _ => le_rfl))
local notation "etaS" => Ideal.IntFiltration.subquotientEquiv F S
local notation "etaT" => Ideal.IntFiltration.subquotientEquiv F T
local notation "etaU" => Ideal.IntFiltration.subquotientEquiv FS U

/-- For `S ≤ T`, the range of the induced graded inclusion of `S` is contained
in the range of the induced graded inclusion of `T`. -/
theorem range_comap_subtype_le (hST : S ≤ T) : A ≤ B := by
  let f : S →ₗ[R] T := Submodule.inclusion hST
  have hf : ∀ n : ℤ, (F.comap S.subtype).N n ≤
      ((F.comap T.subtype).N n).comap f := by
    intro n x hx
    exact (mem_comap F T.subtype n (f x)).mpr
      ((mem_comap F S.subtype n x).mp hx)
  have hcomp :
      ((F.comap T.subtype).map F T.subtype (fun _ => le_rfl)).comp
          ((F.comap S.subtype).map (F.comap T.subtype) f hf) =
        (F.comap S.subtype).map F S.subtype (fun _ => le_rfl) := by
    erw [← map_comp]
    rfl
  intro z hz
  obtain ⟨x, hx⟩ := LinearMap.mem_range.mp hz
  apply LinearMap.mem_range.mpr
  refine ⟨(F.comap S.subtype).map (F.comap T.subtype) f hf x, ?_⟩
  exact (LinearMap.congr_fun hcomp x).trans hx

/-- The subquotient equivalence for `S` carries the image of the induced `T`
range in the graded quotient onto the range of the induced `T.map S.mkQ`
inclusion in the associated graded of the image filtration on `M ⧸ S`. -/
theorem map_range_subquotientEquiv (hST : S ≤ T) :
    Submodule.map (LinearEquiv.toLinearMap etaS) Bbar = D := by
  let H := F.comap T.subtype
  let L := Ideal.IntFiltration.comap FS (Submodule.subtype U)
  have himage : H.image k = L := F.image_comap_restrict_mkQ S T hST
  have hk : ∀ n, H.N n ≤ (L.N n).comap k := by
    intro n
    apply Submodule.map_le_iff_le_comap.mp
    exact (congrArg (fun K : I.IntFiltration U => K.N n) himage).le
  let j := H.map L k hk
  have hj : Function.Surjective j := by
    change Function.Surjective (H.map L k hk)
    exact H.map_surjective_of_map_eq L (k : T →ₗ[R] U)
      (fun n => congrArg (fun K : I.IntFiltration U => K.N n) himage)
  let iT := H.map F T.subtype (fun _ => le_rfl)
  let iU := L.map FS (Submodule.subtype U) (fun _ => le_rfl)
  let q := F.map FS S.mkQ
    (fun _ => Submodule.map_le_iff_le_comap.mp le_rfl)
  have hquot : (LinearEquiv.toLinearMap etaS).comp (Submodule.mkQ A) = q := by
    apply LinearMap.ext
    intro z
    exact F.subquotientEquiv_mk S z
  have hfactor : iU.comp j = q.comp iT := by
    change
      (L.map FS (Submodule.subtype U) (fun _ => le_rfl)).comp (H.map L k hk) =
        (F.map FS S.mkQ
          (fun _ => Submodule.map_le_iff_le_comap.mp le_rfl)).comp
            (H.map F T.subtype (fun _ => le_rfl))
    erw [← map_comp, ← map_comp]
    rfl
  calc
    Submodule.map (LinearEquiv.toLinearMap etaS) Bbar = Submodule.map q B := by
      rw [← Submodule.map_comp, hquot]
    _ = LinearMap.range (q.comp iT) := (LinearMap.range_comp iT q).symm
    _ = LinearMap.range (iU.comp j) := by rw [hfactor]
    _ = D := LinearMap.range_comp_of_range_eq_top iU
      (LinearMap.range_eq_top.mpr hj)

variable (hST : S ≤ T)

local notation "e0" => Submodule.quotientQuotientEquivQuotient S T hST
local notation "hstage" =>
  Ideal.IntFiltration.image_image_quotientQuotientEquivQuotient_N F S T hST
local notation "hAB" => range_comap_subtype_le F S T hST
local notation "hBD" => Ideal.IntFiltration.map_range_subquotientEquiv F S T hST
local notation "alpha" => Submodule.Quotient.equiv Bbar D etaS hBD
local notation "gamma" => Ideal.IntFiltration.equiv FST FT e0 hstage
local notation "omegaC" => Submodule.quotientQuotientEquivQuotient A B hAB
local notation "theta" => LinearEquiv.trans alpha etaU

/-- For `S ≤ T`, quotienting twice by the induced graded ranges agrees with
quotienting directly by the induced `T` range. More precisely, quotient
congruence for the subquotient equivalence of `S`, followed by the subquotient
equivalence for `T.map S.mkQ` and the graded third isomorphism over `R`, equals
the third isomorphism over `C` followed by the subquotient equivalence for `T`.
Both sides are `C`-linear equivalences from `(G ⧸ A) ⧸ B.map A.mkQ` to the
associated graded of `F.image T.mkQ`. -/
theorem subquotientEquiv_quotientQuotient_coherence :
    (LinearEquiv.trans theta gamma :
      ((G ⧸ A) ⧸ Bbar) ≃ₗ[C] Ideal.IntFiltration.AssociatedGraded FT) =
      LinearEquiv.trans omegaC etaT := by
  have hcomp :
      (LinearEquiv.toLinearMap gamma).comp
          ((Ideal.IntFiltration.map FS FST (Submodule.mkQ U)
              (fun _ => Submodule.map_le_iff_le_comap.mp le_rfl)).comp
            (F.map FS (Submodule.mkQ S)
              (fun _ => Submodule.map_le_iff_le_comap.mp le_rfl))) =
        F.map FT (Submodule.mkQ T)
          (fun _ => Submodule.map_le_iff_le_comap.mp le_rfl) := by
    erw [equiv_toLinearMap, ← map_comp, ← map_comp]
    -- The stock third isomorphism sends the double quotient of `m` to its quotient by `T`.
    rfl
  apply LinearEquiv.toLinearMap_injective
  apply Submodule.linearMap_qext Bbar
  apply Submodule.linearMap_qext A
  apply LinearMap.ext
  intro z
  change gamma
      (etaU (Submodule.Quotient.mk
        (etaS (Submodule.Quotient.mk z)))) =
    etaT (Submodule.Quotient.mk z)
  simp only [subquotientEquiv_mk]
  exact LinearMap.congr_fun hcomp z

end Ideal.IntFiltration
