/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GradedRings.FilteredAssociatedGraded.Map
public import Mathlib.LinearAlgebra.Prod

/-!
# Binary products of integer filtrations

The stages of the product filtration are products of submodules in the original
product module. The canonical maps of the two projections and the two inclusions
identify its associated graded with the product of the factor associated gradeds,
using their quotient Rees actions.

The coefficient ring and the two original modules have independent universes.
The constructions use every integer degree, without finiteness, exhaustivity,
separatedness, completeness or degree-zero normalization assumptions.

## Implementation notes

The comparison pairs the canonical associated graded projection maps, with
inverse the sum of the canonical inclusion maps. The scalar actions are the
existing quotient Rees actions on the whole associated graded modules; no action
on individual graded pieces is needed.

## References

* Mathlib's products of submodules and products and coproducts of linear maps.
* The canonical maps of integer-filtered associated graded modules.
-/

@[expose] public section

universe u v w

namespace Ideal.IntFiltration

variable {R : Type u} [CommRing R] {I : Ideal R}
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]
variable (F : I.IntFiltration M) (H : I.IntFiltration N)

local notation "B" => reesAlgebra I
local notation "J" => I.map (algebraMap R B)
local notation "C" => B ⧸ J

/-- The associated graded of a binary product filtration is the product of the
associated gradeds, with their quotient Rees module structures. -/
noncomputable def prodEquiv :
    (F.prod H).AssociatedGraded ≃ₗ[C]
      F.AssociatedGraded × H.AssociatedGraded :=
  LinearEquiv.ofLinearMap
    (((F.prod H).map F (LinearMap.fst R M N) (fun _ _ hp => hp.1)).prod
      ((F.prod H).map H (LinearMap.snd R M N) (fun _ _ hp => hp.2)))
    ((F.map (F.prod H) (LinearMap.inl R M N)
        (fun n _ hm => ⟨hm, (H.N n).zero_mem⟩)).coprod
      (H.map (F.prod H) (LinearMap.inr R M N)
        (fun n _ hn => ⟨(F.N n).zero_mem, hn⟩)))
    (by
      have hfst : ∀ n, (F.prod H).N n ≤ (F.N n).comap (LinearMap.fst R M N) :=
        fun _ _ hp => hp.1
      have hsnd : ∀ n, (F.prod H).N n ≤ (H.N n).comap (LinearMap.snd R M N) :=
        fun _ _ hp => hp.2
      have hinl : ∀ n, F.N n ≤ ((F.prod H).N n).comap (LinearMap.inl R M N) :=
        fun n _ hm => ⟨hm, (H.N n).zero_mem⟩
      have hinr : ∀ n, H.N n ≤ ((F.prod H).N n).comap (LinearMap.inr R M N) :=
        fun n _ hn => ⟨(F.N n).zero_mem, hn⟩
      let pf := (F.prod H).map F (LinearMap.fst R M N) hfst
      let ps := (F.prod H).map H (LinearMap.snd R M N) hsnd
      let il := F.map (F.prod H) (LinearMap.inl R M N) hinl
      let ir := H.map (F.prod H) (LinearMap.inr R M N) hinr
      have hfl : pf.comp il = (LinearMap.id : F.AssociatedGraded →ₗ[C]
          F.AssociatedGraded) :=
        (F.map_comp (F.prod H) (LinearMap.inl R M N) hinl F
          (LinearMap.fst R M N) hfst).symm.trans F.map_id
      have hfr : pf.comp ir = (0 : H.AssociatedGraded →ₗ[C] F.AssociatedGraded) :=
        (H.map_comp (F.prod H) (LinearMap.inr R M N) hinr F
          (LinearMap.fst R M N) hfst).symm.trans (H.map_zero F)
      have hsl : ps.comp il = (0 : F.AssociatedGraded →ₗ[C] H.AssociatedGraded) :=
        (F.map_comp (F.prod H) (LinearMap.inl R M N) hinl H
          (LinearMap.snd R M N) hsnd).symm.trans (F.map_zero H)
      have hsr : ps.comp ir = (LinearMap.id : H.AssociatedGraded →ₗ[C]
          H.AssociatedGraded) :=
        (H.map_comp (F.prod H) (LinearMap.inr R M N) hinr H
          (LinearMap.snd R M N) hsnd).symm.trans H.map_id
      change (pf.prod ps).comp (il.coprod ir) = LinearMap.id
      rw [LinearMap.prod_comp, LinearMap.comp_coprod, LinearMap.comp_coprod,
        hfl, hfr, hsl, hsr]
      simp only [LinearMap.coprod_zero_right, LinearMap.coprod_zero_left,
        LinearMap.id_comp, LinearMap.pair_fst_snd])
    (by
      have hfst : ∀ n, (F.prod H).N n ≤ (F.N n).comap (LinearMap.fst R M N) :=
        fun _ _ hp => hp.1
      have hsnd : ∀ n, (F.prod H).N n ≤ (H.N n).comap (LinearMap.snd R M N) :=
        fun _ _ hp => hp.2
      have hinl : ∀ n, F.N n ≤ ((F.prod H).N n).comap (LinearMap.inl R M N) :=
        fun n _ hm => ⟨hm, (H.N n).zero_mem⟩
      have hinr : ∀ n, H.N n ≤ ((F.prod H).N n).comap (LinearMap.inr R M N) :=
        fun n _ hn => ⟨(F.N n).zero_mem, hn⟩
      let pf := (F.prod H).map F (LinearMap.fst R M N) hfst
      let ps := (F.prod H).map H (LinearMap.snd R M N) hsnd
      let il := F.map (F.prod H) (LinearMap.inl R M N) hinl
      let ir := H.map (F.prod H) (LinearMap.inr R M N) hinr
      let a := (LinearMap.inl R M N).comp (LinearMap.fst R M N)
      let b := (LinearMap.inr R M N).comp (LinearMap.snd R M N)
      have ha : ∀ n, (F.prod H).N n ≤ ((F.prod H).N n).comap a :=
        fun n _ hp => hinl n (hfst n hp)
      have hb : ∀ n, (F.prod H).N n ≤ ((F.prod H).N n).comap b :=
        fun n _ hp => hinr n (hsnd n hp)
      have hab : ∀ n, (F.prod H).N n ≤ ((F.prod H).N n).comap (a + b) :=
        fun n _ hp => ((F.prod H).N n).add_mem (ha n hp) (hb n hp)
      have hl : il.comp pf = (F.prod H).map (F.prod H) a ha :=
        ((F.prod H).map_comp F (LinearMap.fst R M N) hfst (F.prod H)
          (LinearMap.inl R M N) hinl).symm
      have hr : ir.comp ps = (F.prod H).map (F.prod H) b hb :=
        ((F.prod H).map_comp H (LinearMap.snd R M N) hsnd (F.prod H)
          (LinearMap.inr R M N) hinr).symm
      have hid (f : M × N →ₗ[R] M × N)
          (hf : ∀ n, (F.prod H).N n ≤ ((F.prod H).N n).comap f)
          (h : f = LinearMap.id) :
          (F.prod H).map (F.prod H) f hf = LinearMap.id := by
        cases h
        exact (F.prod H).map_id
      have h : a + b = (LinearMap.id : M × N →ₗ[R] M × N) :=
        LinearMap.coprod_inl_inr
      change (il.coprod ir).comp (pf.prod ps) = LinearMap.id
      calc
        (il.coprod ir).comp (pf.prod ps) = il.comp pf + ir.comp ps :=
          LinearMap.coprod_comp_prod il ir pf ps
        _ = (F.prod H).map (F.prod H) a ha + (F.prod H).map (F.prod H) b hb :=
          congrArg₂ (fun f g => f + g) hl hr
        _ = (F.prod H).map (F.prod H) (a + b) hab :=
          ((F.prod H).map_add (F.prod H) a b ha hb).symm
        _ = LinearMap.id := hid (a + b) hab h)

/-- The first coordinate of the product comparison is the canonical projection map. -/
@[simp]
theorem prodEquiv_apply_fst (x : (F.prod H).AssociatedGraded) :
    (F.prodEquiv H x).1 =
      (F.prod H).map F (LinearMap.fst R M N) (fun _ _ hp => hp.1) x := by
  rfl

/-- The second coordinate of the product comparison is the canonical projection map. -/
@[simp]
theorem prodEquiv_apply_snd (x : (F.prod H).AssociatedGraded) :
    (F.prodEquiv H x).2 =
      (F.prod H).map H (LinearMap.snd R M N) (fun _ _ hp => hp.2) x := by
  rfl

/-- A homogeneous pair of original representatives maps to its two homogeneous classes. -/
@[simp]
theorem prodEquiv_single (n : ℤ) (m : F.N n) (p : H.N n) :
    F.prodEquiv H ((F.prod H).single n
        ⟨((m : M), (p : N)), ⟨m.property, p.property⟩⟩) =
      (F.single n m, H.single n p) := by
  let q : (F.prod H).N n :=
    ⟨((m : M), (p : N)), ⟨m.property, p.property⟩⟩
  apply Prod.ext
  · exact (F.prodEquiv_apply_fst H ((F.prod H).single n q)).trans
      ((F.prod H).map_single F (LinearMap.fst R M N) (fun _ _ hp => hp.1) n q)
  · exact (F.prodEquiv_apply_snd H ((F.prod H).single n q)).trans
      ((F.prod H).map_single H (LinearMap.snd R M N) (fun _ _ hp => hp.2) n q)

/-- The inverse adds the canonical maps of the two original inclusions. -/
theorem prodEquiv_symm_apply (y : F.AssociatedGraded) (z : H.AssociatedGraded) :
    (F.prodEquiv H).symm (y, z) =
      F.map (F.prod H) (LinearMap.inl R M N)
          (fun n _ hm => ⟨hm, (H.N n).zero_mem⟩) y +
        H.map (F.prod H) (LinearMap.inr R M N)
          (fun n _ hn => ⟨(F.N n).zero_mem, hn⟩) z := by
  rfl

/-- A homogeneous class from the left factor is included in the left original coordinate. -/
@[simp]
theorem prodEquiv_symm_single_left (n : ℤ) (m : F.N n) :
    (F.prodEquiv H).symm (F.single n m, 0) =
      (F.prod H).single n
        ⟨((m : M), (0 : N)), ⟨m.property, (H.N n).zero_mem⟩⟩ := by
  simp only [prodEquiv_symm_apply, _root_.map_zero, add_zero]
  exact F.map_single (F.prod H) (LinearMap.inl R M N)
    (fun n _ hm => ⟨hm, (H.N n).zero_mem⟩) n m

/-- A homogeneous class from the right factor is included in the right original coordinate. -/
@[simp]
theorem prodEquiv_symm_single_right (n : ℤ) (p : H.N n) :
    (F.prodEquiv H).symm (0, H.single n p) =
      (F.prod H).single n
        ⟨((0 : M), (p : N)), ⟨(F.N n).zero_mem, p.property⟩⟩ := by
  simp only [prodEquiv_symm_apply, _root_.map_zero, zero_add]
  exact H.map_single (F.prod H) (LinearMap.inr R M N)
    (fun n _ hn => ⟨(F.N n).zero_mem, hn⟩) n p

/-- Equality on both canonical projections determines a product associated graded element. -/
@[ext]
theorem prod_associatedGraded_ext {x y : (F.prod H).AssociatedGraded}
    (hfst :
      (F.prod H).map F (LinearMap.fst R M N) (fun _ _ hp => hp.1) x =
        (F.prod H).map F (LinearMap.fst R M N) (fun _ _ hp => hp.1) y)
    (hsnd :
      (F.prod H).map H (LinearMap.snd R M N) (fun _ _ hp => hp.2) x =
        (F.prod H).map H (LinearMap.snd R M N) (fun _ _ hp => hp.2) y) :
    x = y := by
  apply (F.prodEquiv H).injective
  apply Prod.ext
  · simpa only [prodEquiv_apply_fst] using hfst
  · simpa only [prodEquiv_apply_snd] using hsnd

end Ideal.IntFiltration
