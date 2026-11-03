/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GradedRings.Ideal.QuotientModuleMap
public import GradedRings.ReesAlgebra.Augmentation

/-!
# Constant coefficients of quotient Rees objects

For any ideal `I`, taking the constant coefficient induces a surjective ring map
from the quotient Rees ring to `R ⧸ I`. The degree-zero coefficient of the
associated graded module is semilinear over this map, with values in the original
quotient module `M ⧸ (I • ⊤)`. Both maps are characterized on the original Rees
representatives and are surjective by constant representatives.

The module map reuses `Ideal.AssociatedGradedModule.coefficient` in degree zero.
Its semilinearity concerns the existing quotient Rees action on the source and
the existing residue-ring action on the target; no quotient Rees action on the
target is introduced.

## Implementation references

* Mathlib's `Polynomial.constantCoeff` and `Ideal.Quotient.lift` give the ring map.
* The existing coefficient map and its `coefficient_mk` formula give the module
  map, while `PolynomialModule.smul_apply` proves its scalar compatibility.
-/

@[expose] public section

universe u v

namespace Ideal

variable {R : Type u} [CommRing R] (I : Ideal R)

local notation "B" => reesAlgebra I
local notation "J" => I.map (algebraMap R B)
local notation "C" => B ⧸ J
local notation "A" => R ⧸ I

/-- The ring homomorphism underlying the quotient Rees augmentation. -/
noncomputable def reesQuotientConstantCoeff : C →+* A :=
  (reesAlgebra.augmentation I).toRingHom

/-- Forgetting the algebra structure of the quotient Rees augmentation gives
its constant-coefficient ring homomorphism. -/
theorem reesQuotientConstantCoeff_eq_augmentation :
    reesQuotientConstantCoeff I = (reesAlgebra.augmentation I).toRingHom := rfl

/-- On an original Rees-algebra representative, the map takes its constant
coefficient modulo `I`. -/
@[simp]
theorem reesQuotientConstantCoeff_mk (b : B) :
    reesQuotientConstantCoeff I (Ideal.Quotient.mk J b) =
      Ideal.Quotient.mk I ((b : Polynomial R).coeff 0) := by
  rfl

/-- Constant Rees representatives map to their residue classes. -/
theorem reesQuotientConstantCoeff_mk_algebraMap (r : R) :
    reesQuotientConstantCoeff I (Ideal.Quotient.mk J (algebraMap R B r)) =
      Ideal.Quotient.mk I r := by
  rw [reesQuotientConstantCoeff_mk]
  change Ideal.Quotient.mk I ((Polynomial.C r).coeff 0) = Ideal.Quotient.mk I r
  simp

/-- Compatibility with the original-ring algebra map. -/
@[simp]
theorem reesQuotientConstantCoeff_algebraMap (r : R) :
    reesQuotientConstantCoeff I (algebraMap R C r) = Ideal.Quotient.mk I r := by
  rw [IsScalarTower.algebraMap_apply R B C]
  exact reesQuotientConstantCoeff_mk_algebraMap I r

/-- Every residue class has a constant Rees representative. -/
theorem reesQuotientConstantCoeff_surjective :
    Function.Surjective (reesQuotientConstantCoeff I) := by
  intro a
  obtain ⟨r, rfl⟩ :=
    (Ideal.Quotient.mk_surjective : Function.Surjective (Ideal.Quotient.mk I)) a
  exact ⟨Ideal.Quotient.mk J (algebraMap R B r),
    reesQuotientConstantCoeff_mk_algebraMap I r⟩

/-- The formula on original Rees representatives determines the ring map. -/
theorem reesQuotientConstantCoeff_unique (f : C →+* A)
    (hf : ∀ b : B, f (Ideal.Quotient.mk J b) =
      Ideal.Quotient.mk I ((b : Polynomial R).coeff 0)) :
    f = reesQuotientConstantCoeff I := by
  apply RingHom.ext
  intro c
  obtain ⟨b, rfl⟩ :=
    (Ideal.Quotient.mk_surjective : Function.Surjective (Ideal.Quotient.mk J)) c
  exact (hf b).trans (reesQuotientConstantCoeff_mk I b).symm

end Ideal

namespace Ideal.AssociatedGradedModule

variable {R : Type u} [CommRing R] (I : Ideal R)
variable (M : Type v) [AddCommGroup M] [Module R M]

local notation "B" => reesAlgebra I
local notation "J" => I.map (algebraMap R B)
local notation "C" => B ⧸ J
local notation "A" => R ⧸ I
local notation "S" => Ideal.Filtration.submodule (I.stableFiltration (⊤ : Submodule R M))
local notation "D" => J • (⊤ : Submodule B S)
local notation "G" => Ideal.AssociatedGradedModule I M
local notation "Q" => M ⧸ (I • (⊤ : Submodule R M))

-- Expand this expression in proof types without introducing a public helper function.
local notation "δ" =>
  (fun z : G =>
    cast (congrArg (fun N : Submodule R M => M ⧸ N)
      (congrArg (fun K : Ideal R => K • (⊤ : Submodule R M)) (pow_one I)))
      (coefficient I M 0 z))

private theorem constantCoeffFun_mk (p : S) :
    δ (Submodule.Quotient.mk p : G) =
      (Submodule.Quotient.mk ((p : PolynomialModule R M).coeff 0) : Q) := by
  have transport_mk (N P : Submodule R M) (h : N = P) (m : M) :
      cast (congrArg (fun L : Submodule R M => M ⧸ L) h)
        (Submodule.Quotient.mk m : M ⧸ N) = (Submodule.Quotient.mk m : M ⧸ P) := by
    cases h
    rfl
  dsimp only
  rw [coefficient_mk]
  exact transport_mk
    (I ^ (0 + 1) • (⊤ : Submodule R M)) (I • (⊤ : Submodule R M))
    (congrArg (fun K : Ideal R => K • (⊤ : Submodule R M)) (pow_one I))
    ((p : PolynomialModule R M).coeff 0)

private theorem constantCoeffFun_add (x y : G) :
    δ (x + y) = δ x + δ y := by
  induction x using Submodule.Quotient.induction_on with
  | H p =>
      induction y using Submodule.Quotient.induction_on with
      | H q =>
          change δ (Submodule.Quotient.mk (p + q) : G) = _
          rw [constantCoeffFun_mk, constantCoeffFun_mk, constantCoeffFun_mk]
          rfl

private theorem constantCoeffFun_smul (c : C) (z : G) :
    δ (c • z) = Ideal.reesQuotientConstantCoeff I c • δ z := by
  refine Quotient.inductionOn' c ?_
  intro b
  induction z using Submodule.Quotient.induction_on with
  | H p =>
      change δ ((algebraMap B C b) • (Submodule.Quotient.mk p : G)) =
        Ideal.reesQuotientConstantCoeff I (Ideal.Quotient.mk J b) •
          δ (Submodule.Quotient.mk p : G)
      rw [IsScalarTower.algebraMap_smul]
      rw [show b • (Submodule.Quotient.mk p : G) =
        (Submodule.Quotient.mk (b • p) : G) from
          ((@Submodule.mkQ B S
            (inferInstance : Ring B) (inferInstance : AddCommGroup S)
            (inferInstance : Module B S) D : S →ₗ[B] G).map_smul b p).symm]
      rw [constantCoeffFun_mk, Ideal.reesQuotientConstantCoeff_mk, constantCoeffFun_mk]
      change (Submodule.Quotient.mk
        (((b : Polynomial R) • (p : PolynomialModule R M)).coeff 0) : Q) = _
      rw [show (((b : Polynomial R) • (p : PolynomialModule R M)).coeff 0) =
        (b : Polynomial R).coeff 0 • (p : PolynomialModule R M).coeff 0 by
          simpa using PolynomialModule.smul_apply
            (b : Polynomial R) (p : PolynomialModule R M) 0]
      change (Submodule.Quotient.mk
        ((b : Polynomial R).coeff 0 • (p : PolynomialModule R M).coeff 0) : Q) =
          (algebraMap R A ((b : Polynomial R).coeff 0)) •
            (Submodule.Quotient.mk ((p : PolynomialModule R M).coeff 0) : Q)
      rw [IsScalarTower.algebraMap_smul]
      exact (Submodule.mkQ (I • (⊤ : Submodule R M))).map_smul _ _

/-- The degree-zero coefficient, with the original quotient Rees action on the
source and the original `R ⧸ I`-module structure on the coefficient quotient. -/
noncomputable def constantCoeff : G →ₛₗ[Ideal.reesQuotientConstantCoeff I] Q where
  toFun := δ
  map_add' := private constantCoeffFun_add I M
  map_smul' := private constantCoeffFun_smul I M

/-- Constant coefficient on an ordinary quotient representative. -/
@[simp]
theorem constantCoeff_quotient_mk (p : S) :
    constantCoeff I M (Submodule.Quotient.mk p : G) =
      (Submodule.Quotient.mk ((p : PolynomialModule R M).coeff 0) : Q) :=
  constantCoeffFun_mk I M p

/-- Constant coefficient on the original associated-graded quotient map. -/
theorem constantCoeff_mk (p : S) :
    constantCoeff I M (mk I M p) =
      (Submodule.Quotient.mk ((p : PolynomialModule R M).coeff 0) : Q) := by
  rw [mk_apply, constantCoeff_quotient_mk]

/-- A homogeneous representative contributes only in degree zero. -/
theorem constantCoeff_single (q : ℕ) (m : M)
    (hm : m ∈ I ^ q • (⊤ : Submodule R M)) :
    constantCoeff I M
      (mk I M ⟨PolynomialModule.single R q m, single_mem I M q m hm⟩) =
        if q = 0 then (Submodule.Quotient.mk m : Q) else 0 := by
  rw [constantCoeff_mk]
  by_cases h : q = 0
  · subst q
    simp [PolynomialModule.coeff_single]
  · simp [PolynomialModule.coeff_single, h]

/-- Every element of the coefficient quotient has a constant representative. -/
theorem constantCoeff_single_zero (m : M) :
    constantCoeff I M
      (mk I M ⟨PolynomialModule.single R 0 m, single_mem I M 0 m (by simp)⟩) =
        (Submodule.Quotient.mk m : Q) := by
  simp

/-- The degree-zero coefficient map is surjective, without finiteness or
regularity assumptions. -/
theorem constantCoeff_surjective : Function.Surjective (constantCoeff I M) := by
  intro x
  induction x using Submodule.Quotient.induction_on with
  | H m =>
      exact ⟨mk I M
        ⟨PolynomialModule.single R 0 m, single_mem I M 0 m (by simp)⟩,
        constantCoeff_single_zero I M m⟩

/-- Scalar compatibility for the original quotient Rees action. -/
theorem constantCoeff_smul (c : C) (z : G) :
    constantCoeff I M (c • z) =
      Ideal.reesQuotientConstantCoeff I c • constantCoeff I M z :=
  constantCoeffFun_smul I M c z

/-- Restricting to the original ring uses the existing quotient-module action. -/
theorem constantCoeff_smul_R (r : R) (z : G) :
    constantCoeff I M (r • z) = r • constantCoeff I M z := by
  calc
    constantCoeff I M (r • z) = constantCoeff I M ((algebraMap R C r) • z) := by
      rw [IsScalarTower.algebraMap_smul]
    _ = Ideal.reesQuotientConstantCoeff I (algebraMap R C r) • constantCoeff I M z :=
      constantCoeff_smul I M _ z
    _ = r • constantCoeff I M z := by
      rw [Ideal.reesQuotientConstantCoeff_algebraMap]
      change (algebraMap R A r) • constantCoeff I M z = r • constantCoeff I M z
      exact IsScalarTower.algebraMap_smul A r (constantCoeff I M z)

/-- The representative formula determines the semilinear degree-zero map. -/
theorem constantCoeff_unique (f : G →ₛₗ[Ideal.reesQuotientConstantCoeff I] Q)
    (hf : ∀ p : S, f (mk I M p) =
      (Submodule.Quotient.mk ((p : PolynomialModule R M).coeff 0) : Q)) :
    f = constantCoeff I M := by
  ext z
  induction z using Submodule.Quotient.induction_on with
  | H p =>
      rw [show (Submodule.Quotient.mk p : G) = mk I M p from (mk_apply I M p).symm]
      exact (hf p).trans (constantCoeff_mk I M p).symm

end Ideal.AssociatedGradedModule
