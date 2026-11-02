/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GradedRings.ReesModule

/-!
# Maps of Rees submodules and quotient Rees modules

A linear map preserving every stage of two natural-number ideal filtrations
induces a coefficientwise map of their Rees submodules, linear over the Rees
algebra. Its polynomial, coefficient, and singleton formulas characterize it,
and it preserves identities and composition.

An original-ring linear map induces a map on the quotient of the Rees module by
the extended ideal. Its value is obtained by applying `PolynomialModule.map` to
the original polynomial-module representative and then taking the original
submodule quotient. The source and target retain their existing quotient Rees
scalar actions. The maps preserve identities and composition, and their
coefficients are computed by the ordinary original-ring quotient maps.

## References

* Mathlib's `PolynomialModule.map` supplies the coefficientwise map and its
  polynomial-scalar compatibility.
* Mathlib's `Submodule.mapQ` supplies descent through the Rees-module quotients.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v w x

namespace Ideal.Filtration

variable {R : Type u} [CommRing R] {I : Ideal R}
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]
variable (F : I.Filtration M) (H : I.Filtration N) (f : M →ₗ[R] N)

local notation "B" => reesAlgebra I

/-- A stage-preserving linear map induces a coefficientwise map of Rees
submodules, linear over the Rees algebra. -/
noncomputable def reesMap (hf : ∀ q, F.N q ≤ (H.N q).comap f) :
    F.submodule →ₗ[B] H.submodule where
  toFun := fun p =>
    ⟨PolynomialModule.map R f (p : PolynomialModule R M), by
      apply (H.mem_submodule _).2
      intro q
      exact hf q ((F.mem_submodule _).1 p.property q)⟩
  map_add' p q := Subtype.ext ((PolynomialModule.map R f).map_add _ _)
  map_smul' b p := by
    apply Subtype.ext
    change PolynomialModule.map R f ((b : Polynomial R) • (p : PolynomialModule R M)) =
      (b : Polynomial R) • PolynomialModule.map R f (p : PolynomialModule R M)
    simpa using PolynomialModule.map_smul R f (b : Polynomial R)
      (p : PolynomialModule R M)

variable (hf : ∀ q, F.N q ≤ (H.N q).comap f)

/-- The underlying polynomial map of the Rees-submodule map is
`PolynomialModule.map`. -/
theorem coe_reesMap (p : F.submodule) :
    (F.reesMap H f hf p : PolynomialModule R N) =
      PolynomialModule.map R f (p : PolynomialModule R M) := by
  rfl

/-- Every coefficient is sent through the original linear map. -/
@[simp]
theorem coeff_reesMap (q : ℕ) (p : F.submodule) :
    (F.reesMap H f hf p : PolynomialModule R N).coeff q =
      f ((p : PolynomialModule R M).coeff q) := by
  rfl

/-- An admissible polynomial single maps to the single of its image coefficient
in the same degree. -/
@[simp]
theorem reesMap_single (q : ℕ) (m : F.N q) :
    F.reesMap H f hf
        (⟨PolynomialModule.single R q (m : M), by
          apply (F.mem_submodule _).2
          intro i
          by_cases h : q = i
          · subst i
            simp
          · simp [PolynomialModule.coeff_single, h]⟩ : F.submodule) =
      (⟨PolynomialModule.single R q (f (m : M)), by
        apply (H.mem_submodule _).2
        intro i
        by_cases h : q = i
        · subst i
          simpa using hf q m.property
        · simp [PolynomialModule.coeff_single, h]⟩ : H.submodule) := by
  apply Subtype.ext
  simpa only [coe_reesMap] using PolynomialModule.map_single R f q (m : M)

/-- The identity map induces the identity on the Rees submodule. -/
@[simp]
theorem reesMap_id :
    F.reesMap F (LinearMap.id : M →ₗ[R] M) (by
      intro q m hm
      exact hm) =
      (LinearMap.id : F.submodule →ₗ[B] F.submodule) := by
  apply LinearMap.ext
  intro p
  apply Subtype.ext
  apply PolynomialModule.coeff_injective
  ext q
  simp only [coeff_reesMap, LinearMap.id_apply]

variable {P : Type x} [AddCommGroup P] [Module R P]

/-- The coefficientwise map of Rees submodules preserves composition. -/
theorem reesMap_comp (K : I.Filtration P) (g : N →ₗ[R] P)
    (hg : ∀ q, H.N q ≤ (K.N q).comap g) :
    F.reesMap K (g.comp f) (by
      intro q m hm
      exact hg q (hf q hm)) =
      (H.reesMap K g hg).comp (F.reesMap H f hf) := by
  apply LinearMap.ext
  intro p
  apply Subtype.ext
  apply PolynomialModule.coeff_injective
  ext q
  simp only [coeff_reesMap, LinearMap.comp_apply]

end Ideal.Filtration

namespace Ideal.AssociatedGradedModule

variable {R : Type u} [CommRing R] (I : Ideal R)
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

local notation "B" => reesAlgebra I
local notation "J" => I.map (algebraMap R B)
local notation "C" => B ⧸ J
local notation "Sₘ" => Ideal.Filtration.submodule (I.stableFiltration (⊤ : Submodule R M))
local notation "Sₙ" => Ideal.Filtration.submodule (I.stableFiltration (⊤ : Submodule R N))
local notation "Dₘ" => J • (⊤ : Submodule B Sₘ)
local notation "Dₙ" => J • (⊤ : Submodule B Sₙ)

private theorem map_mem_power_smul (f : M →ₗ[R] N) (q : ℕ) :
    I ^ q • (⊤ : Submodule R M) ≤
      (I ^ q • (⊤ : Submodule R N)).comap f := by
  apply Submodule.map_le_iff_le_comap.mp
  rw [Submodule.map_smul'']
  exact smul_mono_right _ le_top

/-- Coefficientwise application of an original-linear map preserves the Rees module. -/
theorem polynomialModule_map_mem (f : M →ₗ[R] N) (p : Sₘ) :
    PolynomialModule.map R f (p : PolynomialModule R M) ∈
      (I.stableFiltration (⊤ : Submodule R N)).submodule := by
  intro q
  change f ((p : PolynomialModule R M).coeff q) ∈ I ^ q • (⊤ : Submodule R N)
  exact map_mem_power_smul I f q (p.property q)

private noncomputable def reesMap (f : M →ₗ[R] N) : Sₘ →ₗ[B] Sₙ :=
  Ideal.Filtration.reesMap
    (I.stableFiltration (⊤ : Submodule R M))
    (I.stableFiltration (⊤ : Submodule R N)) f (by
      intro q
      simpa only [Ideal.stableFiltration_N] using
        (Submodule.smul_top_le_comap_smul_top (I ^ q) f))

private theorem denominator_le_comap (f : M →ₗ[R] N) :
    Dₘ ≤ (Dₙ).comap (reesMap I f) := by
  apply Submodule.map_le_iff_le_comap.mp
  rw [Submodule.map_smul'']
  exact smul_mono_right _ le_top

private noncomputable def mapB (f : M →ₗ[R] N) :
    Ideal.AssociatedGradedModule I M →ₗ[B] Ideal.AssociatedGradedModule I N := by
  exact @Submodule.mapQ B Sₘ
    (inferInstance : Ring B) (inferInstance : AddCommGroup Sₘ)
    (inferInstance : Module B Sₘ) Dₘ B Sₙ
    (inferInstance : Ring B) (inferInstance : AddCommGroup Sₙ)
    (inferInstance : Module B Sₙ) (RingHom.id B) Dₙ
    (reesMap I f) (denominator_le_comap I f)

private theorem mapB_smul (f : M →ₗ[R] N) (c : C)
    (z : Ideal.AssociatedGradedModule I M) :
    mapB I f (c • z) = c • mapB I f z := by
  refine Quotient.inductionOn' c ?_
  intro b
  change mapB I f ((algebraMap B C b) • z) = (algebraMap B C b) • mapB I f z
  simpa only [IsScalarTower.algebraMap_smul] using (mapB I f).map_smul b z

/-- The quotient Rees map induced coefficientwise by an original-ring linear map. -/
noncomputable def map (f : M →ₗ[R] N) :
    Ideal.AssociatedGradedModule I M →ₗ[C] Ideal.AssociatedGradedModule I N where
  toFun := private mapB I f
  map_add' := by exact (mapB I f).map_add
  map_smul' := by exact mapB_smul I f

/-- On an original Rees representative, the map applies the polynomial-module map
and then the original quotient constructor. -/
theorem map_mk (f : M →ₗ[R] N) (p : Sₘ) :
    map I f (mk I M p) =
      mk I N
        ⟨PolynomialModule.map R f (p : PolynomialModule R M),
          polynomialModule_map_mem I f p⟩ := by
  rfl

/-- A single class maps to the single class of the image of its coefficient. -/
theorem map_single (f : M →ₗ[R] N) (q : ℕ) (m : M)
    (hm : m ∈ I ^ q • (⊤ : Submodule R M)) :
    map I f (mk I M ⟨PolynomialModule.single R q m, single_mem I M q m hm⟩) =
      mk I N
        ⟨PolynomialModule.single R q (f m),
          single_mem I N q (f m) (by exact map_mem_power_smul I f q hm)⟩ := by
  rw [map_mk]
  exact congrArg (mk I N) (Subtype.ext (PolynomialModule.map_single R f q m))

/-- Each coefficient is carried by the ordinary original-ring quotient map.
No action on a coefficient quotient by the quotient Rees ring is used here. -/
theorem coefficient_map (f : M →ₗ[R] N) (q : ℕ)
    (z : Ideal.AssociatedGradedModule I M) :
    coefficient I N q (map I f z) =
      ((I ^ (q + 1) • (⊤ : Submodule R M)).mapQ
        (I ^ (q + 1) • (⊤ : Submodule R N)) f
        (by exact map_mem_power_smul I f (q + 1))) (coefficient I M q z) := by
  induction z using Submodule.Quotient.induction_on with
  | H p =>
      rw [show (Submodule.Quotient.mk p : Ideal.AssociatedGradedModule I M) = mk I M p
        from (mk_apply I M p).symm]
      rw [map_mk, mk_apply, coefficient_mk, mk_apply, coefficient_mk,
        Submodule.mapQ_apply]
      rfl

/-- The identity original-linear map induces the identity quotient Rees map. -/
@[simp]
theorem map_id :
    map I (LinearMap.id : M →ₗ[R] M) =
      (LinearMap.id : Ideal.AssociatedGradedModule I M →ₗ[C]
        Ideal.AssociatedGradedModule I M) := by
  apply LinearMap.ext
  intro z
  induction z using Submodule.Quotient.induction_on with
  | H p =>
      change map I (LinearMap.id : M →ₗ[R] M) (mk I M p) = mk I M p
      rw [map_mk]
      apply congrArg (mk I M)
      apply Subtype.ext
      apply PolynomialModule.ext
      apply Finsupp.ext
      intro q
      rfl

variable {P : Type x} [AddCommGroup P] [Module R P]

/-- Taking quotient Rees maps preserves composition of original-linear maps. -/
theorem map_comp (f : M →ₗ[R] N) (g : N →ₗ[R] P) :
    map I (g.comp f) = (map I g).comp (map I f) := by
  apply LinearMap.ext
  intro z
  induction z using Submodule.Quotient.induction_on with
  | H p =>
      change map I (g.comp f) (mk I M p) = map I g (map I f (mk I M p))
      rw [map_mk, map_mk, map_mk]
      apply congrArg (mk I P)
      apply Subtype.ext
      apply PolynomialModule.ext
      apply Finsupp.ext
      intro q
      rfl

end Ideal.AssociatedGradedModule
