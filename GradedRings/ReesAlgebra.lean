/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.ReesAlgebra
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# Finite conormal modules and the Rees quotient

The quotient of the Rees algebra of an ideal `I` by the extended ideal `I` is the
canonical underlying associated-graded algebra in its Rees-quotient presentation.
A finite conormal module over `R ⧸ I` generates this algebra in degree one.
Consequently, the quotient is of finite type, and is Noetherian when `R ⧸ I` is.

The results concern the underlying algebra; no grading or direct-sum identification
is constructed here.

## References

* K. Fujiwara and F. Kato, *Foundations of Rigid Geometry I*, arXiv:1308.4734v5.
-/

@[expose] public section

universe u

namespace reesAlgebra

variable {R : Type u} [CommRing R] (I : Ideal R)

private noncomputable def degreeOne : I →ₗ[R] reesAlgebra I where
  toFun x := ⟨Polynomial.monomial 1 (x : R), monomial_mem.mpr (by simp)⟩
  map_add' x y := Subtype.ext (map_add (Polynomial.monomial 1) (x : R) (y : R))
  map_smul' r x := Subtype.ext (map_smul (Polynomial.monomial 1) r (x : R))

private theorem adjoin_degreeOne : Algebra.adjoin R (Set.range (degreeOne I)) = ⊤ := by
  apply Subalgebra.map_injective (f := (reesAlgebra I).val) Subtype.val_injective
  rw [AlgHom.map_adjoin, Algebra.map_top, Subalgebra.range_val]
  have hs : (reesAlgebra I).val '' Set.range (degreeOne I) =
      (Submodule.map (Polynomial.monomial 1 : R →ₗ[R] Polynomial R) I :
        Set (Polynomial R)) := by
    ext p
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨(x : R), x.property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨degreeOne I ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩, rfl⟩
  rw [hs, adjoin_monomial_eq_reesAlgebra]

private theorem quotient_degreeOne_mul (x y : I) :
    (Ideal.Quotient.mkₐ R (I.map (algebraMap R (reesAlgebra I))))
      (degreeOne I (x * y)) = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  have hmul : degreeOne I (x * y) =
      algebraMap R (reesAlgebra I) (x : R) * degreeOne I y := by
    ext
    simp [degreeOne, Polynomial.C_mul_monomial]
  rw [hmul]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ x.property)

/-- If the conormal module of `I` is finite over `R ⧸ I`, then the underlying
associated-graded algebra, presented as the Rees quotient, is of finite type over
`R ⧸ I`. The degree-one generators are the images of the conormal module. -/
theorem finiteType_quotient_of_finite_cotangent
    [Module.Finite (R ⧸ I) I.Cotangent] :
    Algebra.FiniteType (R ⧸ I)
      ((reesAlgebra I) ⧸ I.map (algebraMap R (reesAlgebra I))) := by
  let q := Ideal.Quotient.mkₐ R (I.map (algebraMap R (reesAlgebra I)))
  let g := q.toLinearMap.comp (degreeOne I)
  let f := Ideal.Cotangent.lift g (quotient_degreeOne_mul I)
  have hgen : Algebra.adjoin R (Set.range g) = ⊤ := by
    have h := congrArg (Subalgebra.map q) (adjoin_degreeOne I)
    rw [AlgHom.map_adjoin, Algebra.map_top,
      (AlgHom.range_eq_top q).mpr (Ideal.Quotient.mkₐ_surjective R _)] at h
    simpa only [g, LinearMap.coe_comp, AlgHom.coe_toLinearMap, Set.range_comp] using h
  have hrange : Set.range f = Set.range g := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨y, rfl⟩ := I.toCotangent_surjective x
      exact ⟨y, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨I.toCotangent x, rfl⟩
  let : Module.Finite R I.Cotangent := Module.Finite.trans (R ⧸ I) I.Cotangent
  have hfg : f.range.FG := Module.Finite.iff_fg.mp inferInstance
  obtain ⟨s, hs⟩ := hfg
  let : Algebra.FiniteType R
      ((reesAlgebra I) ⧸ I.map (algebraMap R (reesAlgebra I))) := by
    refine ⟨⟨s, ?_⟩⟩
    rw [← Algebra.adjoin_span, hs]
    change Algebra.adjoin R (Set.range f) = ⊤
    rw [hrange]
    exact hgen
  exact Algebra.FiniteType.of_restrictScalars_finiteType R (R ⧸ I)
    ((reesAlgebra I) ⧸ I.map (algebraMap R (reesAlgebra I)))

/-- The underlying associated-graded algebra in its Rees-quotient presentation is
Noetherian if its coefficient ring is Noetherian and its conormal module is finite. -/
theorem isNoetherianRing_quotient_of_finite_cotangent
    [Module.Finite (R ⧸ I) I.Cotangent] [IsNoetherianRing (R ⧸ I)] :
    IsNoetherianRing
      ((reesAlgebra I) ⧸ I.map (algebraMap R (reesAlgebra I))) := by
  let := finiteType_quotient_of_finite_cotangent I
  exact Algebra.FiniteType.isNoetherianRing (R ⧸ I)
    ((reesAlgebra I) ⧸ I.map (algebraMap R (reesAlgebra I)))

end reesAlgebra
