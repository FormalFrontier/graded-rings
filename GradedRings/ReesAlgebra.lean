/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.ReesAlgebra
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.LinearAlgebra.TensorAlgebra.Basic

/-!
# The cotangent module and the Rees quotient

The quotient of the Rees algebra of an ideal `I` by the extended ideal `I` is the
canonical underlying associated-graded algebra in its Rees-quotient presentation.
The cotangent module `I.Cotangent` maps linearly over `R ⧸ I` to this quotient by
sending the class of `x` to the class of `x X`. Its image generates the quotient
as an algebra, so the induced map from its tensor algebra is surjective.

If the cotangent module is finite over `R ⧸ I`, the quotient is of finite type,
and is Noetherian when `R ⧸ I` is.

The results concern the underlying algebra; no grading or direct-sum identification
is constructed here.

## References

* K. Fujiwara and F. Kato, *Foundations of Rigid Geometry I*, arXiv:1308.4734v5.
-/

@[expose] public section

universe u

namespace reesAlgebra

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- The degree-one map to the Rees algebra, sending `x ∈ I` to `x X`. -/
noncomputable def degreeOne : I →ₗ[R] reesAlgebra I where
  toFun x := ⟨Polynomial.monomial 1 (x : R), monomial_mem.mpr (by simp)⟩
  map_add' x y := Subtype.ext (map_add (Polynomial.monomial 1) (x : R) (y : R))
  map_smul' r x := Subtype.ext (map_smul (Polynomial.monomial 1) r (x : R))

@[simp]
theorem coe_degreeOne (x : I) :
    ((degreeOne I x : reesAlgebra I) : Polynomial R) = Polynomial.monomial 1 (x : R) :=
  rfl

/-- The Rees algebra is generated over `R` by its degree-one elements. -/
theorem adjoin_degreeOne : Algebra.adjoin R (Set.range (degreeOne I)) = ⊤ := by
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

/-- The cotangent module maps to the Rees quotient by sending the class of `x`
to the class of `x X`. The scalar action is the canonical action of `R ⧸ I`. -/
noncomputable def cotangentToQuotient :
    I.Cotangent →ₗ[R ⧸ I]
      ((reesAlgebra I) ⧸ I.map (algebraMap R (reesAlgebra I))) :=
  (Ideal.Cotangent.lift
    ((Ideal.Quotient.mkₐ R (I.map (algebraMap R (reesAlgebra I)))).toLinearMap.comp
      (degreeOne I))
    (by
      intro x y
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      have hmul : degreeOne I (x * y) =
          algebraMap R (reesAlgebra I) (x : R) * degreeOne I y := by
        ext
        simp [degreeOne, Polynomial.C_mul_monomial]
      rw [hmul]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ x.property))).extendScalarsOfSurjective
      (by
        simpa only [Ideal.Quotient.algebraMap_eq] using
          (Ideal.Quotient.mk_surjective (I := I)))

@[simp]
theorem cotangentToQuotient_toCotangent (x : I) :
    cotangentToQuotient I (I.toCotangent x) =
      Ideal.Quotient.mk (I.map (algebraMap R (reesAlgebra I))) (degreeOne I x) :=
  rfl

/-- Restricting scalars recovers the factorization of the quotient-composed
degree-one map through the cotangent quotient. -/
theorem cotangentToQuotient_comp_toCotangent :
    ((cotangentToQuotient I).restrictScalars R).comp I.toCotangent =
      (Ideal.Quotient.mkₐ R (I.map (algebraMap R (reesAlgebra I)))).toLinearMap.comp
        (degreeOne I) :=
  rfl

theorem cotangentToQuotient_mk_smul (r : R) (z : I.Cotangent) :
    cotangentToQuotient I (Ideal.Quotient.mk I r • z) =
      Ideal.Quotient.mk (I.map (algebraMap R (reesAlgebra I)))
        (algebraMap R (reesAlgebra I) r) * cotangentToQuotient I z := by
  rw [map_smul, Algebra.smul_def,
    Ideal.Quotient.algebraMap_quotient_map_quotient]

/-- The cotangent map has the same image as the quotient-composed degree-one map. -/
theorem range_cotangentToQuotient :
    Set.range (cotangentToQuotient I) =
      Set.range (fun x : I =>
        Ideal.Quotient.mk (I.map (algebraMap R (reesAlgebra I))) (degreeOne I x)) := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨y, rfl⟩ := I.toCotangent_surjective x
    exact ⟨y, (cotangentToQuotient_toCotangent I y).symm⟩
  · rintro ⟨x, rfl⟩
    exact ⟨I.toCotangent x, cotangentToQuotient_toCotangent I x⟩

/-- The image of the cotangent module generates the Rees quotient over `R ⧸ I`. -/
theorem adjoin_range_cotangentToQuotient :
    Algebra.adjoin (R ⧸ I) (Set.range (cotangentToQuotient I)) = ⊤ := by
  let q := Ideal.Quotient.mkₐ R (I.map (algebraMap R (reesAlgebra I)))
  let g := q.toLinearMap.comp (degreeOne I)
  have hgen : Algebra.adjoin R (Set.range g) = ⊤ := by
    have h := congrArg (Subalgebra.map q) (adjoin_degreeOne I)
    rw [AlgHom.map_adjoin, Algebra.map_top,
      (AlgHom.range_eq_top q).mpr (Ideal.Quotient.mkₐ_surjective R _)] at h
    simpa only [g, LinearMap.coe_comp, AlgHom.coe_toLinearMap, Set.range_comp] using h
  have hrange : Set.range (cotangentToQuotient I) = Set.range g :=
    range_cotangentToQuotient I
  rw [← hrange] at hgen
  have hle : Algebra.adjoin R (Set.range (cotangentToQuotient I)) ≤
      (Algebra.adjoin (R ⧸ I) (Set.range (cotangentToQuotient I))).restrictScalars R :=
    Algebra.adjoin_le_iff.mpr Algebra.subset_adjoin
  apply top_unique
  intro z _
  exact hle (by rw [hgen]; trivial)

/-- The algebra map from the tensor algebra of the cotangent module to the Rees
quotient, induced by its canonical degree-one map. -/
noncomputable def tensorAlgebraToQuotient :
    TensorAlgebra (R ⧸ I) I.Cotangent →ₐ[R ⧸ I]
      ((reesAlgebra I) ⧸ I.map (algebraMap R (reesAlgebra I))) :=
  TensorAlgebra.lift (R ⧸ I) (cotangentToQuotient I)

@[simp]
theorem tensorAlgebraToQuotient_ι (z : I.Cotangent) :
    tensorAlgebraToQuotient I (TensorAlgebra.ι (R ⧸ I) z) =
      cotangentToQuotient I z :=
  TensorAlgebra.lift_ι_apply _ _

theorem tensorAlgebraToQuotient_ι_toCotangent (x : I) :
    tensorAlgebraToQuotient I (TensorAlgebra.ι (R ⧸ I) (I.toCotangent x)) =
      Ideal.Quotient.mk (I.map (algebraMap R (reesAlgebra I))) (degreeOne I x) := by
  rw [tensorAlgebraToQuotient_ι, cotangentToQuotient_toCotangent]

theorem tensorAlgebraToQuotient_algebraMap_mk (r : R) :
    tensorAlgebraToQuotient I
      (algebraMap (R ⧸ I) (TensorAlgebra (R ⧸ I) I.Cotangent)
        (Ideal.Quotient.mk I r)) =
      Ideal.Quotient.mk (I.map (algebraMap R (reesAlgebra I)))
        (algebraMap R (reesAlgebra I) r) := by
  simpa only [Ideal.Quotient.algebraMap_quotient_map_quotient] using
    (tensorAlgebraToQuotient I).commutes (Ideal.Quotient.mk I r)

/-- The tensor-algebra map is uniquely determined by its values on ideal
representatives of the cotangent generators. -/
theorem tensorAlgebraToQuotient_unique
    (f : TensorAlgebra (R ⧸ I) I.Cotangent →ₐ[R ⧸ I]
      ((reesAlgebra I) ⧸ I.map (algebraMap R (reesAlgebra I))))
    (hf : ∀ x : I, f (TensorAlgebra.ι (R ⧸ I) (I.toCotangent x)) =
      Ideal.Quotient.mk (I.map (algebraMap R (reesAlgebra I))) (degreeOne I x)) :
    f = tensorAlgebraToQuotient I := by
  apply TensorAlgebra.hom_ext
  apply LinearMap.ext
  intro z
  obtain ⟨x, rfl⟩ := I.toCotangent_surjective z
  exact (hf x).trans (tensorAlgebraToQuotient_ι_toCotangent I x).symm

/-- The whole tensor-algebra map to the Rees quotient is surjective for every
ideal, without a finiteness assumption on the ideal or its cotangent module. -/
theorem tensorAlgebraToQuotient_surjective :
    Function.Surjective (tensorAlgebraToQuotient I) := by
  apply (AlgHom.range_eq_top _).mp
  exact (TensorAlgebra.range_lift (cotangentToQuotient I)).trans
    (adjoin_range_cotangentToQuotient I)

/-- If the conormal module of `I` is finite over `R ⧸ I`, then the underlying
associated-graded algebra, presented as the Rees quotient, is of finite type over
`R ⧸ I`. The degree-one generators are the images of the conormal module. -/
theorem finiteType_quotient_of_finite_cotangent
    [Module.Finite (R ⧸ I) I.Cotangent] :
    Algebra.FiniteType (R ⧸ I)
      ((reesAlgebra I) ⧸ I.map (algebraMap R (reesAlgebra I))) := by
  have hfg : (cotangentToQuotient I).range.FG := Module.Finite.iff_fg.mp inferInstance
  obtain ⟨s, hs⟩ := hfg
  refine ⟨⟨s, ?_⟩⟩
  rw [← Algebra.adjoin_span, hs]
  exact adjoin_range_cotangentToQuotient I

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
