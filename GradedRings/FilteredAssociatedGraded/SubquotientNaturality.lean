/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GradedRings.FilteredAssociatedGraded.Subquotient

/-!
# Naturality of associated graded subquotients

An original-linear map preserving every integer stage of two filtrations and
carrying one submodule into another induces maps on the induced submodule
filtrations and on the image filtrations of the original quotients. These maps
commute with the canonical associated graded inclusions and projections.

The subquotient equivalences intertwine the induced map on the quotients of the
whole associated graded modules by the inclusion ranges with the associated
graded map of the original quotient map. The former map is the submodule quotient
map induced by the ambient associated graded map.

All whole associated graded modules and their range quotients use the canonical
actions of the Rees algebra modulo the extension of the filtration ideal.
Individual pieces, their insertions and their projections retain their original
coefficient-linear structures. The submodule filtrations are induced, not
intrinsic ideal-adic filtrations. No strictness, ambient injectivity or
surjectivity, finiteness, normalization, exhaustivity, separatedness, completeness
or degree bound is required.

## References

* Mathlib's `LinearMap.restrict` and `Submodule.mapQ` for the maps on the
  original submodules and quotients.
* `Ideal.IntFiltration.subquotientEquiv` for the quotient-by-range equivalence.
-/

@[expose] public section

universe u v w

namespace Ideal.IntFiltration

variable {R : Type u} [CommRing R] {I : Ideal R}
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]
variable (F : I.IntFiltration M) (H : I.IntFiltration N)
variable (S : Submodule R M) (T : Submodule R N)
variable (f : M →ₗ[R] N)
variable (hf : ∀ n : ℤ, F.N n ≤ (H.N n).comap f)
variable (hST : S ≤ T.comap f)

local notation "B" => reesAlgebra I
local notation "J" => I.map (algebraMap R B)
local notation "C" => B ⧸ J

local notation "fST" =>
  f.restrict (p := S) (q := T) (fun x hx => hST hx)
local notation "fQ" => S.mapQ T f hST

local notation "a" =>
  (Ideal.IntFiltration.map (F.comap S.subtype) (H.comap T.subtype) fST
    (fun n x hx => hf n hx) :
      Ideal.IntFiltration.AssociatedGraded (F.comap S.subtype) →ₗ[C]
        Ideal.IntFiltration.AssociatedGraded (H.comap T.subtype))
local notation "b" => (F.map H f hf : F.AssociatedGraded →ₗ[C] H.AssociatedGraded)
local notation "c" =>
  (Ideal.IntFiltration.map (F.image S.mkQ) (H.image T.mkQ) fQ
    (fun n y hy =>
      Exists.elim (Submodule.mem_map.mp hy) (fun x hx =>
        And.elim (fun hxn hxy =>
          Eq.subst (motive := fun z => fQ z ∈ Submodule.map T.mkQ (H.N n)) hxy
            (Submodule.mem_map.mpr
              (Exists.intro (f x)
                (And.intro (hf n hxn) (Eq.refl (T.mkQ (f x))))))) hx)) :
      Ideal.IntFiltration.AssociatedGraded (F.image S.mkQ) →ₗ[C]
        Ideal.IntFiltration.AssociatedGraded (H.image T.mkQ))

local notation "iF" =>
  (Ideal.IntFiltration.map (F.comap S.subtype) F S.subtype (fun _ => le_rfl) :
    Ideal.IntFiltration.AssociatedGraded (F.comap S.subtype) →ₗ[C] F.AssociatedGraded)
local notation "iH" =>
  (Ideal.IntFiltration.map (H.comap T.subtype) H T.subtype (fun _ => le_rfl) :
    Ideal.IntFiltration.AssociatedGraded (H.comap T.subtype) →ₗ[C] H.AssociatedGraded)
local notation "qF" =>
  (F.map (F.image S.mkQ) S.mkQ
    (fun _ => Submodule.map_le_iff_le_comap.mp le_rfl) :
      F.AssociatedGraded →ₗ[C] Ideal.IntFiltration.AssociatedGraded (F.image S.mkQ))
local notation "qH" =>
  (H.map (H.image T.mkQ) T.mkQ
    (fun _ => Submodule.map_le_iff_le_comap.mp le_rfl) :
      H.AssociatedGraded →ₗ[C] Ideal.IntFiltration.AssociatedGraded (H.image T.mkQ))

/-- The associated graded map of a restriction commutes with the canonical maps
from the induced submodule filtrations. -/
theorem map_subtype_naturality :
    (iH).comp a = (b).comp iF := by
  erw [← map_comp, ← map_comp]
  rfl

/-- The associated graded map of the original quotient map commutes with the
canonical maps onto the image quotient filtrations. -/
theorem map_mkQ_naturality :
    (qH).comp b = (c).comp qF := by
  erw [← map_comp, ← map_comp]
  rfl

/-- The subquotient equivalences intertwine the quotient map induced by the
ambient associated graded map with the associated graded original quotient map. -/
theorem subquotientEquiv_naturality :
    (H.subquotientEquiv T).toLinearMap.comp
      ((LinearMap.range iF).mapQ (LinearMap.range iH) b
        (fun _ hz => Exists.elim hz (fun x hx =>
          ⟨a x, (LinearMap.congr_fun
            (map_subtype_naturality F H S T f hf hST) x).trans
              (congrArg b hx)⟩))) =
      (c).comp (F.subquotientEquiv S).toLinearMap := by
  apply Submodule.quot_hom_ext
  intro z
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    Submodule.mapQ_apply, subquotientEquiv_mk] using
    LinearMap.congr_fun (map_mkQ_naturality F H S T f hf hST) z

end Ideal.IntFiltration
