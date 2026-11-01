/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import GradedRings.ReesAlgebra
public import CoherentModules.LinearAlgebra.TensorProduct.Noetherian
public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Algebra.Module.RingHom
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Rees modules and associated graded modules

An ideal filtration with finitely generated Rees module is stable: multiplication
by the ideal gives the next stage in every sufficiently large degree. Neither the
ideal, the individual stages, nor the ambient module need be finitely generated.

The Rees module modulo the extended ideal carries a canonical surjection from the
scalar extension of the first quotient of the module. More generally, for a subideal
`K ≤ I` satisfying `IⁿM = KⁿM + Iⁿ⁺¹M` in every degree, scalar extension over `R` to
`reesAlgebra K` surjects onto the same associated graded module. Finiteness of the
first quotient implies finiteness over this smaller Rees algebra, without finite
generation of `K`. If the first quotient is Noetherian over `R` and `K` is finitely
generated, the associated graded module is Noetherian over the quotient Rees algebra.

## References

The finite-Rees stability argument follows Andrew Yang's
`Ideal.Filtration.submodule_fg_iff_stable` in Mathlib's
[filtration theory](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/RingTheory/Filtration.lean),
using its bounded-degree span criterion and compactness of finitely generated submodules.
Only the converse in that equivalence needs finite generation of the stages.

For background, see K. Fujiwara and F. Kato, *Foundations of Rigid Geometry I*,
[arXiv:1308.4734v5](https://arxiv.org/abs/1308.4734v5). The precise formulation
of the first-quotient finiteness criterion and its relative version in this file
is proved here. The Noetherian corollary uses essentially finite-type scalar extension
from [Coherent Modules](https://github.com/FormalFrontier/coherent-modules/blob/1dfe73a0d8d506a7871d5393e274582d36161265/CoherentModules/LinearAlgebra/TensorProduct/Noetherian.lean).
-/

@[expose] public section

open scoped TensorProduct

universe u v

namespace Ideal

variable {R : Type u} [CommRing R] (I : Ideal R)
variable (M : Type v) [AddCommGroup M] [Module R M]

namespace Filtration

variable {I M}

open PolynomialModule

-- The bounded-span order homomorphism needs semireducible type comparison.
set_option backward.isDefEq.respectTransparency.types false in
/-- A filtration with finitely generated Rees module is stable.

No finite generation of the ideal, the individual stages, or the ambient module is
required. The bounded-degree span argument is the forward implication of Andrew Yang's
`Ideal.Filtration.submodule_fg_iff_stable`, without its finite-stage hypothesis. -/
theorem stable_of_submodule_fg (F : I.Filtration M) (hF : F.submodule.FG) : F.Stable := by
  classical
  unfold Stable
  simp_rw [← F.submodule_eq_span_le_iff_stable_ge]
  refine hF.stabilizes_of_iSup_eq
    ⟨fun n₀ => Submodule.span _ (⋃ i ≤ n₀, single R i '' (F.N i : Set M)), ?_⟩ ?_
  · intro n m hnm
    rw [Submodule.span_le, Set.iUnion₂_subset_iff]
    intro i hi
    refine Set.Subset.trans ?_ Submodule.subset_span
    refine @Set.subset_iUnion₂ _ _ _ (fun j _ => single R j '' (F.N j : Set M)) i ?_
    exact hi.trans hnm
  · dsimp
    rw [← Submodule.span_iUnion, F.submodule_span_single.symm]
    simp [Set.biUnion_le_eq_iUnion]

end Filtration

private theorem Filtration.mem_smul_submodule_iff (F : I.Filtration M) (K : Ideal R)
    (p : PolynomialModule R M) :
    p ∈ K • F.submodule.restrictScalars R ↔ ∀ n, p.coeff n ∈ K • F.N n := by
  have hsingle (n : ℕ) (m : M) (hm : m ∈ F.N n) :
      PolynomialModule.single R n m ∈ F.submodule := by
    rw [← F.submodule_span_single]
    exact Submodule.subset_span
      (Set.mem_iUnion.mpr ⟨n, Set.mem_image_of_mem _ hm⟩)
  constructor
  · intro hp n
    refine Submodule.smul_induction_on hp (fun r hr q hq => ?_) (fun q q' hq hq' => ?_)
    · have he := congrArg (fun f : ℕ →₀ M => f n)
        ((PolynomialModule.coeffLinearEquiv R R).map_smul r q)
      simp only [PolynomialModule.coeffLinearEquiv_apply, Finsupp.smul_apply] at he
      rw [he]
      exact Submodule.smul_mem_smul hr (hq n)
    · have he := congrArg (fun f : ℕ →₀ M => f n)
        ((PolynomialModule.coeffLinearEquiv R R).map_add q q')
      simp only [PolynomialModule.coeffLinearEquiv_apply, Finsupp.add_apply] at he
      rw [he]
      exact Submodule.add_mem _ hq hq'
  · intro hp
    have hsingle_mul (n : ℕ) (m : M) (hm : m ∈ K • F.N n) :
        PolynomialModule.single R n m ∈ K • F.submodule.restrictScalars R := by
      refine Submodule.smul_induction_on hm (fun r hr m' hm' => ?_) (fun x y hx hy => ?_)
      · rw [PolynomialModule.single_smul]
        exact Submodule.smul_mem_smul hr (hsingle n m' hm')
      · rw [PolynomialModule.single_add]
        exact Submodule.add_mem _ hx hy
    rw [← p.ofCoeff_coeff, ← p.coeff.sum_single, PolynomialModule.ofCoeff_finsuppSum]
    apply Submodule.sum_mem _ _
    intro n _
    exact hsingle_mul n (p.coeff n) (hp n)

/-- The Rees module of the ideal-adic filtration modulo the extended ideal. -/
def AssociatedGradedModule :=
  _root_.Quotient
    (@Submodule.quotientRel (reesAlgebra I)
      (↥(Ideal.Filtration.submodule (I.stableFiltration (⊤ : Submodule R M))))
      (inferInstance : Ring (reesAlgebra I))
      (inferInstance : AddCommGroup
        (↥(Ideal.Filtration.submodule (I.stableFiltration (⊤ : Submodule R M)))))
      (inferInstance : Module (reesAlgebra I)
        (↥(Ideal.Filtration.submodule (I.stableFiltration (⊤ : Submodule R M)))))
      (I.map (algebraMap R (reesAlgebra I)) •
        (⊤ : Submodule (reesAlgebra I)
          ((I.stableFiltration (⊤ : Submodule R M)).submodule))))

namespace AssociatedGradedModule

local notation "B" => reesAlgebra I
local notation "J" => I.map (algebraMap R B)
local notation "A" => R ⧸ I
local notation "C" => B ⧸ J
local notation "N" => (Ideal.Filtration.submodule (I.stableFiltration (⊤ : Submodule R M)))
local notation "Q" => M ⧸ (I • (⊤ : Submodule R M))
local notation "G" => AssociatedGradedModule I M

private instance reesModuleScalarTower : IsScalarTower R B N where
  smul_assoc r b n := by
    apply Subtype.ext
    change ((r • b : B) : Polynomial R) • (n : PolynomialModule R M) =
      r • ((b : Polynomial R) • (n : PolynomialModule R M))
    exact smul_assoc r (b : Polynomial R) (n : PolynomialModule R M)

/-- The additive group inherited from the quotient Rees module. -/
@[reducible]
noncomputable instance instAddCommGroup : AddCommGroup G :=
  @Submodule.Quotient.addCommGroup B N
    (inferInstance : Ring B)
    (inferInstance : AddCommGroup N)
    (inferInstance : Module B N)
    (J • (⊤ : Submodule B N))

/-- The Rees action inherited from the quotient Rees module. -/
@[reducible]
noncomputable instance instModuleRees : Module B G :=
  @Submodule.Quotient.module B N
    (inferInstance : Ring B)
    (inferInstance : AddCommGroup N)
    (inferInstance : Module B N)
    (J • (⊤ : Submodule B N))

/-- The coefficient action inherited from the original Rees module. -/
@[reducible]
noncomputable instance instModuleCoefficients : Module R G :=
  @Submodule.Quotient.module' B N
    (inferInstance : Ring B)
    (inferInstance : AddCommGroup N)
    (inferInstance : Module B N)
    R
    (inferInstance : Semiring R)
    (inferInstance : SMul R B)
    (inferInstance : Module R N)
    (show IsScalarTower R B N from
      { smul_assoc := fun r b n => by
          apply Subtype.ext
          change ((r • b : B) : Polynomial R) • (n : PolynomialModule R M) =
            r • ((b : Polynomial R) • (n : PolynomialModule R M))
          exact smul_assoc r (b : Polynomial R) (n : PolynomialModule R M) })
    (J • (⊤ : Submodule B N))

/-- The canonical quotient map from the Rees module. -/
noncomputable def mk : N →ₗ[B] G :=
  let q : N → G := @Submodule.Quotient.mk B N
    (inferInstance : Ring B)
    (inferInstance : AddCommGroup N)
    (inferInstance : Module B N)
    (J • (⊤ : Submodule B N))
  { toFun := q
    map_add' := fun x y =>
      @Submodule.Quotient.mk_add B N x y
        (inferInstance : Ring B)
        (inferInstance : AddCommGroup N)
        (inferInstance : Module B N)
        (J • (⊤ : Submodule B N))
    map_smul' := fun b x =>
      @Submodule.Quotient.mk_smul B N
        (inferInstance : Ring B)
        (inferInstance : AddCommGroup N)
        (inferInstance : Module B N)
        (J • (⊤ : Submodule B N)) B
        (inferInstance : SMul B B)
        (inferInstance : SMul B N)
        (inferInstance : IsScalarTower B B N) b x }

/-- The canonical quotient map sends a representative to its class. -/
@[simp]
theorem mk_apply (n : N) :
    mk I M n =
      (@Submodule.Quotient.mk B N
        (inferInstance : Ring B)
        (inferInstance : AddCommGroup N)
        (inferInstance : Module B N)
        (J • (⊤ : Submodule B N)) n : G) := rfl

instance scalarTowerRees : IsScalarTower R B G where
  smul_assoc r b g := by
    refine @Submodule.Quotient.induction_on B N
      (inferInstance : Ring B)
      (inferInstance : AddCommGroup N)
      (inferInstance : Module B N)
      (J • (⊤ : Submodule B N))
      (fun x : G => (r • b) • x = r • (b • x)) g ?_
    intro n
    let q : N → G := @Submodule.Quotient.mk B N
      (inferInstance : Ring B)
      (inferInstance : AddCommGroup N)
      (inferInstance : Module B N)
      (J • (⊤ : Submodule B N))
    have hR (a : R) (x : N) : q (a • x) = a • q x := by
      exact @Submodule.Quotient.mk_smul B N
        (inferInstance : Ring B)
        (inferInstance : AddCommGroup N)
        (inferInstance : Module B N)
        (J • (⊤ : Submodule B N)) R
        (inferInstance : SMul R B)
        (inferInstance : SMul R N)
        (inferInstance : IsScalarTower R B N) a x
    have hB (c : B) (x : N) : q (c • x) = c • q x := by
      exact @Submodule.Quotient.mk_smul B N
        (inferInstance : Ring B)
        (inferInstance : AddCommGroup N)
        (inferInstance : Module B N)
        (J • (⊤ : Submodule B N)) B
        (inferInstance : SMul B B)
        (inferInstance : SMul B N)
        (inferInstance : IsScalarTower B B N) c x
    have hN : ((r • b) • n : N) = r • (b • n) := smul_assoc r b n
    change (r • b) • q n = r • (b • q n)
    calc
      (r • b) • q n = q ((r • b) • n) := (hB (r • b) n).symm
      _ = q (r • (b • n)) := congrArg q hN
      _ = r • q (b • n) := hR r (b • n)
      _ = r • (b • q n) := congrArg (fun x : G => r • x) (hB b n)

/-- The quotient Rees algebra acts canonically on the associated graded module. -/
@[reducible]
noncomputable instance moduleReesQuotient : Module C G :=
  (Module.isTorsionBySet_quotient_ideal_smul N J).module

/-- Quotient scalars act on classes by their Rees representatives. -/
theorem quotient_smul_mk (b : B) (n : N) :
    (Ideal.Quotient.mk J b : C) • mk I M n = mk I M (b • n) := by
  exact Module.Quotient.mk_smul_mk (R := B) (M := N) (I := J) b n

instance scalarTowerReesQuotient : IsScalarTower B C G :=
  (Module.isTorsionBySet_quotient_ideal_smul N J).isScalarTower

instance scalarTowerCoefficients : IsScalarTower R C G :=
  (Module.isTorsionBySet_quotient_ideal_smul N J).isScalarTower (S := R)

section RelativeAction

variable (K : Ideal R) (hKI : K ≤ I)

/-- The action of a subideal Rees algebra, through the quotient Rees algebra. -/
@[reducible]
noncomputable def moduleReesOfLE : Module (reesAlgebra K) G :=
  Module.compHom G (reesAlgebra.quotientMapOfLE I K hKI).toRingHom

/-- Subideal Rees scalars act through their canonical quotient images. -/
theorem moduleReesOfLE_smul (a : reesAlgebra K) (g : G) :
    @SMul.smul (reesAlgebra K) G (moduleReesOfLE I M K hKI).toSMul a g =
      reesAlgebra.quotientMapOfLE I K hKI a • g := rfl

/-- Subideal Rees scalars act on representatives by inclusion into the Rees algebra. -/
theorem moduleReesOfLE_smul_mk (a : reesAlgebra K) (p : N) :
    @SMul.smul (reesAlgebra K) G (moduleReesOfLE I M K hKI).toSMul a (mk I M p) =
      mk I M ((Subalgebra.inclusion (S := reesAlgebra K) (T := B)
        (fun _ hp n => pow_le_pow_left' hKI n (hp n)) a) • p) := by
  rw [moduleReesOfLE_smul, reesAlgebra.quotientMapOfLE_apply, quotient_smul_mk]

/-- Compatibility of the coefficient and subideal Rees actions. -/
theorem scalarTowerReesOfLE :
    @IsScalarTower R (reesAlgebra K) G _ (moduleReesOfLE I M K hKI).toSMul _ := by
  let : Module (reesAlgebra K) G := moduleReesOfLE I M K hKI
  refine ⟨fun r a g => ?_⟩
  change reesAlgebra.quotientMapOfLE I K hKI (r • a) • g =
    r • (reesAlgebra.quotientMapOfLE I K hKI a • g)
  rw [map_smul, smul_assoc]

/-- Compatibility of the subideal Rees and quotient Rees actions. -/
theorem scalarTowerReesQuotientOfLE :
    @IsScalarTower (reesAlgebra K) C G
      (reesAlgebra.quotientMapOfLE I K hKI).toRingHom.toModule.toSMul
      _ (moduleReesOfLE I M K hKI).toSMul := by
  let : Module (reesAlgebra K) C := (reesAlgebra.quotientMapOfLE I K hKI).toRingHom.toModule
  let : Module (reesAlgebra K) G := moduleReesOfLE I M K hKI
  refine ⟨fun a c g => ?_⟩
  change ((reesAlgebra.quotientMapOfLE I K hKI a) * c) • g =
    reesAlgebra.quotientMapOfLE I K hKI a • (c • g)
  exact mul_smul _ _ _

end RelativeAction

/-- Restriction through the quotient recovers the original Rees action for the same ideal. -/
theorem moduleReesOfLE_refl_smul (a : B) (g : G) :
    @SMul.smul B G (moduleReesOfLE I M I le_rfl).toSMul a g = a • g := by
  rw [moduleReesOfLE_smul, reesAlgebra.quotientMapOfLE_refl]
  exact IsScalarTower.algebraMap_smul C a g

@[reducible]
noncomputable instance moduleQuotient : Module A G :=
  Module.compHom G (algebraMap A C)

instance scalarTowerQuotient : IsScalarTower A C G where
  smul_assoc a c g := by
    change (a • c) • g = algebraMap A C a • (c • g)
    rw [Algebra.smul_def, mul_smul]

instance smulCommClassQuotient : SMulCommClass A C G :=
  IsScalarTower.to_smulCommClass (R := A) («A» := C) (M := G)

instance scalarTowerResidue : IsScalarTower R A G where
  smul_assoc r a g := by
    change algebraMap A C (r • a) • g = r • (algebraMap A C a • g)
    rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply R A C, mul_smul,
      Algebra.algebraMap_eq_smul_one, smul_assoc, one_smul]

/-- Restricting the residue action to the coefficient ring gives its coefficient action. -/
theorem residue_smul (r : R) (g : G) :
    (Ideal.Quotient.mk I r : A) • g = r • g := by
  change (algebraMap R A r) • g = r • g
  exact IsScalarTower.algebraMap_smul A r g

/-- The residue scalar action on a class is induced by coefficient multiplication. -/
theorem residue_smul_mk (r : R) (n : N) :
    (Ideal.Quotient.mk I r : A) • mk I M n =
      mk I M ((algebraMap R B r) • n) := by
  change algebraMap A C (Ideal.Quotient.mk I r) • mk I M n =
    mk I M ((algebraMap R B r) • n)
  rw [Ideal.Quotient.algebraMap_quotient_map_quotient]
  exact quotient_smul_mk I M (algebraMap R B r) n

/-- Coefficient restriction agrees with the Rees action on every quotient representative. -/
theorem coefficient_smul_mk (r : R) (n : N) :
    r • mk I M n = mk I M ((algebraMap R B r) • n) := by
  exact (residue_smul I M r (mk I M n)).symm.trans (residue_smul_mk I M r n)

private noncomputable abbrev reesModuleCoefficients : Module R N :=
  Module.compHom N (algebraMap R B)

/-- The restricted coefficient action on the Rees submodule is coefficientwise. -/
theorem coe_coefficient_smul (r : R) (n : N) :
    (((algebraMap R B r) • n : N) : PolynomialModule R M) = r • (n : PolynomialModule R M) := by
  change (algebraMap R (Polynomial R) r) • (n : PolynomialModule R M) = _
  exact IsScalarTower.algebraMap_smul (Polynomial R) r (n : PolynomialModule R M)

private theorem reesModuleCoefficients_eq :
    reesModuleCoefficients I M = Submodule.module (Submodule.restrictScalars R N) := by
  apply Module.ext'
  intro r n
  apply Subtype.ext
  exact coe_coefficient_smul I M r n

/-- A single coefficient in the corresponding ideal power lies in the Rees module. -/
theorem single_mem (n : ℕ) (m : M) (hm : m ∈ I ^ n • (⊤ : Submodule R M)) :
    PolynomialModule.single R n m ∈ N := by
  rw [Ideal.Filtration.mem_submodule]
  intro k
  by_cases h : n = k
  · subst k
    simpa using hm
  · simp [PolynomialModule.coeff_single, h]

private noncomputable def constant (m : M) : N :=
  ⟨PolynomialModule.single R 0 m, single_mem I M 0 m (by simp)⟩

private theorem constant_add (m m' : M) :
    constant I M (m + m') = constant I M m + constant I M m' := by
  apply Subtype.ext
  exact PolynomialModule.single_add _ _ _

private theorem constant_smul (r : R) (m : M) :
    constant I M (r • m) = (algebraMap R B r) • constant I M m := by
  apply Subtype.ext
  rw [coe_coefficient_smul]
  exact PolynomialModule.single_smul _ _ _

private theorem constant_mem (m : M) (hm : m ∈ I • (⊤ : Submodule R M)) :
    constant I M m ∈ J • (⊤ : Submodule B N) := by
  refine Submodule.smul_induction_on hm (fun r hr m _ => ?_) (fun m m' hm hm' => ?_)
  · rw [constant_smul]
    exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hr) (Submodule.mem_top)
  · rw [constant_add]
    exact Submodule.add_mem _ hm hm'

/-- The map from the first quotient to constant classes in the associated graded module. -/
noncomputable def degreeZero : Q →ₗ[A] G :=
  letI : IsScalarTower R B N :=
    { smul_assoc := fun r b n => by
        apply Subtype.ext
        change ((r • b : B) : Polynomial R) • (n : PolynomialModule R M) =
          r • ((b : Polynomial R) • (n : PolynomialModule R M))
        exact smul_assoc r (b : Polynomial R) (n : PolynomialModule R M) }
  let κ₀ : M →ₗ[R] N :=
    { toFun := fun m =>
        ⟨PolynomialModule.single R 0 m, single_mem I M 0 m (by simp)⟩
      map_add' := fun m m' => by
        apply Subtype.ext
        exact PolynomialModule.single_add _ _ _
      map_smul' := fun r m => by
        apply Subtype.ext
        change PolynomialModule.single R 0 (r • m) = r • PolynomialModule.single R 0 m
        exact PolynomialModule.single_smul _ _ _ }
  let f : M →ₗ[R] G := ((mk I M).restrictScalars R).comp κ₀
  let q : N → G := @Submodule.Quotient.mk B N
    (inferInstance : Ring B)
    (inferInstance : AddCommGroup N)
    (inferInstance : Module B N)
    (J • (⊤ : Submodule B N))
  have hf (m : M) (hm : m ∈ I • (⊤ : Submodule R M)) : f m = (0 : G) := by
    change q (constant I M m) = 0
    exact (@Submodule.Quotient.mk_eq_zero B N (constant I M m)
      (inferInstance : Ring B)
      (inferInstance : AddCommGroup N)
      (inferInstance : Module B N)
      (J • (⊤ : Submodule B N))).mpr (constant_mem I M m hm)
  let l : Q → G := fun x =>
    (I • (⊤ : Submodule R M)).liftQ f (fun m hm => hf m hm) x
  let g : Q →ₗ[R] G :=
    { toFun := l
      map_add' := fun x y =>
        ((I • (⊤ : Submodule R M)).liftQ f (fun m hm => hf m hm)).map_add x y
      map_smul' := fun r x =>
        ((I • (⊤ : Submodule R M)).liftQ f (fun m hm => hf m hm)).map_smul r x }
  letI : IsScalarTower R A Q :=
    (Module.isTorsionBySet_quotient_ideal_smul M I).isScalarTower (S := R)
  LinearMap.extendScalarsOfSurjective (R := R) (S := A) (M := Q) («N» := G)
    (by
      intro a
      refine Quotient.inductionOn' a ?_
      intro r
      exact ⟨r, rfl⟩)
    g

/-- The degree-zero map sends the class of an element to its constant polynomial class. -/
@[simp]
theorem degreeZero_mk (m : M) :
    degreeZero I M (Submodule.Quotient.mk m) =
      (@Submodule.Quotient.mk B N
        (inferInstance : Ring B)
        (inferInstance : AddCommGroup N)
        (inferInstance : Module B N)
        (J • (⊤ : Submodule B N))
        (⟨PolynomialModule.single R 0 m, single_mem I M 0 m (by simp)⟩ : N) : G) := rfl

/-- The characteristic map from the scalar extension of the first quotient. -/
noncomputable def characteristic : C ⊗[A] Q →ₗ[C] G :=
  TensorProduct.AlgebraTensorModule.lift
    { toFun := fun c => c • degreeZero I M
      map_add' := fun c c' => add_smul c c' _
      map_smul' := fun c c' => mul_smul c c' _ }

/-- The characteristic map on every pure tensor. -/
@[simp]
theorem characteristic_tmul (c : C) (q : Q) :
    characteristic I M (c ⊗ₜ[A] q) = c • degreeZero I M q := rfl

/-- The characteristic map on a pure tensor represented by an element of the module. -/
@[simp]
theorem characteristic_tmul_mk (c : C) (m : M) :
    characteristic I M (c ⊗ₜ[A] Submodule.Quotient.mk m) =
      c • Submodule.Quotient.mk (p := J • (⊤ : Submodule B N))
        (⟨PolynomialModule.single R 0 m, single_mem I M 0 m (by simp)⟩ : N) := rfl

/-- The characteristic map on classes represented in the Rees algebra and the module. -/
theorem characteristic_mk_tmul_mk (b : B) (m : M) :
    characteristic I M ((Ideal.Quotient.mk J b) ⊗ₜ[A] Submodule.Quotient.mk m) =
      Submodule.Quotient.mk (p := J • (⊤ : Submodule B N))
        (b • (⟨PolynomialModule.single R 0 m, single_mem I M 0 m (by simp)⟩ : N)) := by
  rw [characteristic_tmul_mk, Module.Quotient.mk_smul_mk]

/-- The characteristic map is determined by its values on tensors with first factor one. -/
theorem characteristic_unique (f : C ⊗[A] Q →ₗ[C] G)
    (h : ∀ q, f ((1 : C) ⊗ₜ[A] q) = degreeZero I M q) :
    f = characteristic I M := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro c q
  have ht : c ⊗ₜ[A] q = c • ((1 : C) ⊗ₜ[A] q) :=
    TensorProduct.tmul_eq_smul_one_tmul c q
  calc
    f (c ⊗ₜ[A] q) = c • f ((1 : C) ⊗ₜ[A] q) := by rw [ht, f.map_smul]
    _ = c • degreeZero I M q := by rw [h]
    _ = characteristic I M (c ⊗ₜ[A] q) := (characteristic_tmul I M c q).symm

/-- The extended ideal multiple consists exactly of polynomials whose coefficients lie
in the next ideal powers. -/
theorem mem_ideal_smul_iff_coeff (p : N) :
    p ∈ J • (⊤ : Submodule B N) ↔
      ∀ n, (p : PolynomialModule R M).coeff n ∈ I ^ (n + 1) • (⊤ : Submodule R M) := by
  have hrestrict :
      (J • (⊤ : Submodule B N)).restrictScalars R = I • (⊤ : Submodule R N) := by
    simpa using Submodule.restrictScalars_map_smul_eq I (⊤ : Submodule B N)
  change p ∈ (J • (⊤ : Submodule B N)).restrictScalars R ↔ _
  rw [hrestrict]
  let f : N →ₗ[R] PolynomialModule R M := (Submodule.subtype N).restrictScalars R
  have hrange : LinearMap.range f = (Submodule.restrictScalars R N) := by
    ext q
    constructor
    · rintro ⟨n, rfl⟩
      exact n.property
    · intro hq
      exact ⟨⟨q, hq⟩, rfl⟩
  have hmap : (I • (⊤ : Submodule R N)).map f = I • (Submodule.restrictScalars R N) := by
    rw [Submodule.map_smul'', Submodule.map_top, hrange]
  have hmem : p ∈ I • (⊤ : Submodule R N) ↔
      (p : PolynomialModule R M) ∈ I • (Submodule.restrictScalars R N) := by
    rw [← hmap]
    constructor
    · intro hp
      exact Submodule.mem_map.mpr ⟨p, hp, rfl⟩
    · intro hp
      rcases Submodule.mem_map.mp hp with ⟨q, hq, hqp⟩
      exact (Subtype.ext hqp : q = p) ▸ hq
  rw [hmem]
  rw [Filtration.mem_smul_submodule_iff I M]
  change (∀ n, (p : PolynomialModule R M).coeff n ∈
    I • (I ^ n • (⊤ : Submodule R M))) ↔ _
  simp_rw [← mul_smul, ← pow_succ']

/-- A class vanishes exactly when every coefficient lies in the next ideal power. -/
theorem mk_eq_zero_iff_coeff (p : N) :
    @Eq G
      (@Submodule.Quotient.mk B N
        (inferInstance : Ring B)
        (inferInstance : AddCommGroup N)
        (inferInstance : Module B N)
        (J • (⊤ : Submodule B N)) p)
      (0 : G) ↔
      ∀ n, (p : PolynomialModule R M).coeff n ∈ I ^ (n + 1) • (⊤ : Submodule R M) := by
  let K : Submodule B N := J • (⊤ : Submodule B N)
  constructor
  · intro h
    have hp : p ∈ K :=
      (@Submodule.Quotient.mk_eq_zero B N p
        (inferInstance : Ring B)
        (inferInstance : AddCommGroup N)
        (inferInstance : Module B N) K).mp h
    exact (mem_ideal_smul_iff_coeff I M p).mp hp
  · intro h
    have hp : p ∈ K := (mem_ideal_smul_iff_coeff I M p).mpr h
    exact (@Submodule.Quotient.mk_eq_zero B N p
      (inferInstance : Ring B)
      (inferInstance : AddCommGroup N)
      (inferInstance : Module B N) K).mpr hp

/-- Equality of classes is equality of all their coefficient classes. -/
theorem mk_eq_mk_iff_coeff (p q : N) :
    @Eq G
      (@Submodule.Quotient.mk B N
        (inferInstance : Ring B)
        (inferInstance : AddCommGroup N)
        (inferInstance : Module B N)
        (J • (⊤ : Submodule B N)) p)
      (@Submodule.Quotient.mk B N
        (inferInstance : Ring B)
        (inferInstance : AddCommGroup N)
        (inferInstance : Module B N)
        (J • (⊤ : Submodule B N)) q) ↔
      ∀ n, ((p - q : N) : PolynomialModule R M).coeff n ∈
        I ^ (n + 1) • (⊤ : Submodule R M) := by
  let K : Submodule B N := J • (⊤ : Submodule B N)
  constructor
  · intro h
    have hmem : p - q ∈ K :=
      (@Submodule.Quotient.eq B N
        (inferInstance : Ring B)
        (inferInstance : AddCommGroup N)
        (inferInstance : Module B N)
        K p q).mp h
    exact (mem_ideal_smul_iff_coeff I M (p - q)).mp hmem
  · intro h
    have hmem : p - q ∈ K :=
      (mem_ideal_smul_iff_coeff I M (p - q)).mpr h
    exact (@Submodule.Quotient.eq B N
      (inferInstance : Ring B)
      (inferInstance : AddCommGroup N)
      (inferInstance : Module B N)
      K p q).mpr hmem

/-- The denominator in degree `n` is precisely the next ideal power of the module. -/
theorem single_mem_ideal_smul_iff (n : ℕ) (m : M)
    (hm : m ∈ I ^ n • (⊤ : Submodule R M)) :
    (⟨PolynomialModule.single R n m, single_mem I M n m hm⟩ : N) ∈
      J • (⊤ : Submodule B N) ↔ m ∈ I ^ (n + 1) • (⊤ : Submodule R M) := by
  rw [mem_ideal_smul_iff_coeff]
  constructor
  · intro h
    simpa using h n
  · intro h k
    by_cases hnk : n = k
    · subst k
      simpa using h
    · simp [PolynomialModule.coeff_single, hnk]

private theorem coefficient_sub_apply (p q : PolynomialModule R M) (n : ℕ) :
    (p - q).coeff n = p.coeff n - q.coeff n := by
  change (PolynomialModule.coeffAddEquiv (p - q)) n =
    (PolynomialModule.coeffAddEquiv p) n - (PolynomialModule.coeffAddEquiv q) n
  rw [map_sub, Finsupp.sub_apply]

/-- The first quotient embeds as the constant classes. -/
theorem degreeZero_injective : Function.Injective (degreeZero I M) := by
  intro q q' h
  induction q using Submodule.Quotient.induction_on with
  | H m =>
    induction q' using Submodule.Quotient.induction_on with
    | H m' =>
      let p : N :=
        ⟨PolynomialModule.single R 0 m, single_mem I M 0 m (by simp)⟩
      let p' : N :=
        ⟨PolynomialModule.single R 0 m', single_mem I M 0 m' (by simp)⟩
      have hclasses : mk I M p = mk I M p' :=
        (degreeZero_mk I M m).symm.trans (h.trans (degreeZero_mk I M m'))
      have hc := (mk_eq_mk_iff_coeff I M p p').mp hclasses
      apply (Submodule.Quotient.eq _).mpr
      have hz := hc 0
      change ((p : PolynomialModule R M) - (p' : PolynomialModule R M)).coeff 0 ∈
        I ^ (0 + 1) • (⊤ : Submodule R M) at hz
      rw [coefficient_sub_apply M] at hz
      simpa [p, p'] using hz

/-- The degree-`n` coefficient class of an associated graded element. -/
noncomputable def coefficient (n : ℕ) :
    G →+ M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M)) :=
  let f : N →ₗ[R] M :=
    { toFun := fun p => (p : PolynomialModule R M).coeff n
      map_add' := fun p q => by
        simp only [Submodule.coe_add, PolynomialModule.coeff_add, Finsupp.add_apply]
      map_smul' := fun r p => by
        change (r • (p : PolynomialModule R M)).coeff n = _
        simpa only [PolynomialModule.coeffLinearEquiv_apply, Finsupp.smul_apply,
          RingHom.id_apply] using
          congrArg (fun f : ℕ →₀ M => f n)
            ((PolynomialModule.coeffLinearEquiv R R).map_smul r (p : PolynomialModule R M)) }
  let φ : N →+ M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M)) :=
    ((((I ^ (n + 1) • (⊤ : Submodule R M)).mkQ).comp f).toAddMonoidHom)
  let H : AddSubgroup N :=
    ((J • (⊤ : Submodule B N)) : Submodule B N).toAddSubgroup
  have hφ : H ≤ φ.ker := by
    intro p hp
    have hc : (p : PolynomialModule R M).coeff n ∈
        I ^ (n + 1) • (⊤ : Submodule R M) :=
      (mem_ideal_smul_iff_coeff I M p).mp hp n
    have hz :
        (Submodule.Quotient.mk ((p : PolynomialModule R M).coeff n) :
          M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M))) = 0 :=
      (@Submodule.Quotient.mk_eq_zero R M ((p : PolynomialModule R M).coeff n)
        (inferInstance : Ring R)
        (inferInstance : AddCommGroup M)
        (inferInstance : Module R M)
        (I ^ (n + 1) • (⊤ : Submodule R M))).mpr hc
    change φ p = 0
    exact hz
  let lHom : (N ⧸ H) →+ M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M)) :=
    QuotientAddGroup.lift H φ hφ
  let l : G → M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M)) := by
    change (N ⧸ H) → M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M))
    exact fun g => lHom g
  let q : N → G := @Submodule.Quotient.mk B N
    (inferInstance : Ring B)
    (inferInstance : AddCommGroup N)
    (inferInstance : Module B N)
    (J • (⊤ : Submodule B N))
  have hzero : q 0 = (0 : G) := by
    exact (QuotientAddGroup.mk' H).map_zero
  have hadd (p p' : N) : q (p + p') = q p + q p' := by
    exact (QuotientAddGroup.mk' H).map_add p p'
  have hl (p : N) : l (q p) = φ p := rfl
  { toFun := l
    map_zero' := by
      calc
        l 0 = l (q 0) := congrArg l hzero.symm
        _ = φ 0 := hl 0
        _ = 0 := φ.map_zero
    map_add' := fun g g' => by
      refine @Submodule.Quotient.induction_on B N
        (inferInstance : Ring B)
        (inferInstance : AddCommGroup N)
        (inferInstance : Module B N)
        (J • (⊤ : Submodule B N))
        (fun x : G => l (x + g') = l x + l g') g ?_
      intro p
      refine @Submodule.Quotient.induction_on B N
        (inferInstance : Ring B)
        (inferInstance : AddCommGroup N)
        (inferInstance : Module B N)
        (J • (⊤ : Submodule B N))
        (fun y : G => l (q p + y) = l (q p) + l y) g' ?_
      intro p'
      calc
        l (q p + q p') = l (q (p + p')) := congrArg l (hadd p p').symm
        _ = φ (p + p') := hl (p + p')
        _ = φ p + φ p' := φ.map_add p p'
        _ = l (q p) + l (q p') :=
          congrArg₂ (· + ·) (hl p).symm (hl p').symm }

/-- Coefficient classes are computed on any polynomial representative. -/
@[simp]
theorem coefficient_mk (n : ℕ) (p : N) :
    coefficient I M n
        (@Submodule.Quotient.mk B N
          (inferInstance : Ring B)
          (inferInstance : AddCommGroup N)
          (inferInstance : Module B N)
          (J • (⊤ : Submodule B N)) p : G) =
      Submodule.Quotient.mk ((p : PolynomialModule R M).coeff n) := rfl

/-- Inside the `n`th ideal power, the next power is its ideal multiple. -/
theorem stage_denominator_eq (n : ℕ) :
    (I ^ (n + 1) • (⊤ : Submodule R M)).comap
        (I ^ n • (⊤ : Submodule R M)).subtype =
      I • (⊤ : Submodule R ↥(I ^ n • (⊤ : Submodule R M))) := by
  ext m
  change (m : M) ∈ I ^ (n + 1) • (⊤ : Submodule R M) ↔
    m ∈ I • (⊤ : Submodule R ↥(I ^ n • (⊤ : Submodule R M)))
  rw [Submodule.mem_smul_top_iff]
  rw [← mul_smul, ← pow_succ']

/-- The kernel of the stage map is the next ideal power, viewed inside the current one. -/
theorem stage_kernel (n : ℕ) :
    LinearMap.ker (((I ^ (n + 1) • (⊤ : Submodule R M)).mkQ).comp
      (I ^ n • (⊤ : Submodule R M)).subtype) =
      I • (⊤ : Submodule R ↥(I ^ n • (⊤ : Submodule R M))) := by
  rw [LinearMap.ker_comp, Submodule.ker_mkQ, stage_denominator_eq]

/-- The range of the stage map is the image of the current ideal power in the next quotient. -/
theorem stage_range (n : ℕ) :
    LinearMap.range (((I ^ (n + 1) • (⊤ : Submodule R M)).mkQ).comp
      (I ^ n • (⊤ : Submodule R M)).subtype) =
      (I ^ n • (⊤ : Submodule R M)).map
        (I ^ (n + 1) • (⊤ : Submodule R M)).mkQ := by
  ext x
  constructor
  · rintro ⟨m, rfl⟩
    exact Submodule.mem_map.mpr ⟨m, m.property, rfl⟩
  · intro hx
    rcases Submodule.mem_map.mp hx with ⟨m, hm, rfl⟩
    exact ⟨⟨m, hm⟩, rfl⟩

/-- The quotient of the current ideal power by the next one is its image in the ambient quotient. -/
noncomputable def stageComparison (n : ℕ) :
    (↥(I ^ n • (⊤ : Submodule R M)) ⧸
      (I • (⊤ : Submodule R ↥(I ^ n • (⊤ : Submodule R M))))) ≃ₗ[R]
      ((I ^ n • (⊤ : Submodule R M)).map
        (I ^ (n + 1) • (⊤ : Submodule R M)).mkQ) :=
  (Submodule.quotEquivOfEq _ _ (stage_kernel I M n).symm).trans
    (((((I ^ (n + 1) • (⊤ : Submodule R M)).mkQ).comp
      (I ^ n • (⊤ : Submodule R M)).subtype).quotKerEquivRange).trans
        (LinearEquiv.ofEq _ _ (stage_range I M n)))

/-- The stage comparison sends each representative to its ambient quotient class. -/
@[simp]
theorem stageComparison_mk (n : ℕ) (m : ↥(I ^ n • (⊤ : Submodule R M))) :
    ((stageComparison I M n (Submodule.Quotient.mk m)) :
      M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M))) = Submodule.Quotient.mk (m : M) := rfl

/-- Residue scalars on a stage quotient agree with coefficient scalars on its image. -/
theorem stageComparison_smul_mk (n : ℕ) (r : R) (m : ↥(I ^ n • (⊤ : Submodule R M))) :
    ((stageComparison I M n ((Ideal.Quotient.mk I r : A) • Submodule.Quotient.mk m)) :
      M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M))) =
        r • ((stageComparison I M n (Submodule.Quotient.mk m)) :
          M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M))) := by
  rw [Module.Quotient.mk_smul_mk, stageComparison_mk, stageComparison_mk]
  exact ((I ^ (n + 1) • (⊤ : Submodule R M)).mkQ).map_smul r (m : M)

/-- The degree-`n` coefficient class lies in the image of the `n`th ideal power. -/
theorem coefficient_mem (n : ℕ) (g : G) :
    coefficient I M n g ∈
      (I ^ n • (⊤ : Submodule R M)).map
        (I ^ (n + 1) • (⊤ : Submodule R M)).mkQ := by
  induction g using Submodule.Quotient.induction_on with
  | H p => exact Submodule.mem_map.mpr ⟨_, p.property n, rfl⟩

/-- Residue scalars act on every coefficient through the original coefficient action. -/
theorem coefficient_residue_smul (n : ℕ) (r : R) (g : G) :
    coefficient I M n ((Ideal.Quotient.mk I r : A) • g) = r • coefficient I M n g := by
  induction g using Submodule.Quotient.induction_on with
  | H p =>
    have hc (q : N) :
        coefficient I M n (mk I M q) =
          (Submodule.Quotient.mk ((q : PolynomialModule R M).coeff n) :
            M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M))) :=
      coefficient_mk I M n q
    change coefficient I M n ((Ideal.Quotient.mk I r : A) • mk I M p) =
      r • coefficient I M n (mk I M p)
    rw [residue_smul_mk, hc, hc]
    rw [coe_coefficient_smul]
    have he := congrArg (fun f : ℕ →₀ M => f n)
      ((PolynomialModule.coeffLinearEquiv R R).map_smul r (p : PolynomialModule R M))
    simp only [PolynomialModule.coeffLinearEquiv_apply, Finsupp.smul_apply] at he
    rw [he]
    exact ((I ^ (n + 1) • (⊤ : Submodule R M)).mkQ).map_smul r _

/-- Every element has only finitely many nonzero coefficient classes. -/
theorem finite_support_coefficient (g : G) :
    Set.Finite {n | coefficient I M n g ≠ 0} := by
  induction g using Submodule.Quotient.induction_on with
  | H p =>
    apply (p : PolynomialModule R M).coeff.support.finite_toSet.subset
    intro n hn
    by_contra hnot
    have hz := Finsupp.notMem_support_iff.mp hnot
    exact hn (by simp [hz])

/-- Coefficient classes jointly distinguish associated graded elements. -/
theorem coefficient_injective :
    Function.Injective (fun g : G => fun n => coefficient I M n g) := by
  intro g h he
  induction g using Submodule.Quotient.induction_on with
  | H p =>
    induction h using Submodule.Quotient.induction_on with
    | H q =>
      apply (mk_eq_mk_iff_coeff I M p q).mpr
      intro n
      have hn :
          (Submodule.Quotient.mk ((p : PolynomialModule R M).coeff n) :
            M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M))) =
            Submodule.Quotient.mk ((q : PolynomialModule R M).coeff n) :=
        (coefficient_mk I M n p).symm.trans
          ((congrFun he n).trans (coefficient_mk I M n q))
      rw [Submodule.Quotient.eq] at hn
      rw [Submodule.coe_sub, coefficient_sub_apply M]
      exact hn

/-- Every finitely supported family of stage classes is represented by an associated
graded element. -/
theorem exists_of_finite_coefficients
    (f : ∀ n, M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M)))
    (hf : Set.Finite {n | f n ≠ 0})
    (hmem : ∀ n, f n ∈ (I ^ n • (⊤ : Submodule R M)).map
      (I ^ (n + 1) • (⊤ : Submodule R M)).mkQ) :
    ∃ g : G, ∀ n, coefficient I M n g = f n := by
  classical
  have hrep : ∀ n, ∃ m : M, m ∈ I ^ n • (⊤ : Submodule R M) ∧
      (Submodule.Quotient.mk m : M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M))) = f n :=
    fun n => Submodule.mem_map.mp (hmem n)
  choose m hm he using hrep
  let g : G := ∑ i ∈ hf.toFinset,
    Submodule.Quotient.mk
      (⟨PolynomialModule.single R i (m i), single_mem I M i (m i) (hm i)⟩ : N)
  refine ⟨g, fun n => ?_⟩
  have hc (i : ℕ) :
      coefficient I M n (mk I M
        (⟨PolynomialModule.single R i (m i), single_mem I M i (m i) (hm i)⟩ : N)) =
        if i = n then f n else 0 := by
    change coefficient I M n (Submodule.Quotient.mk
      (⟨PolynomialModule.single R i (m i), single_mem I M i (m i) (hm i)⟩ : N) : G) =
        if i = n then f n else 0
    by_cases hin : i = n
    · subst i
      simpa using he n
    · simp [coefficient_mk, PolynomialModule.coeff_single, hin]
  change coefficient I M n (∑ i ∈ hf.toFinset, mk I M
    (⟨PolynomialModule.single R i (m i), single_mem I M i (m i) (hm i)⟩ : N)) = _
  simp only [map_sum, hc]
  by_cases hn : n ∈ hf.toFinset
  · simp [hn]
  · have hfn : f n = 0 := by
      by_contra h
      exact hn (hf.mem_toFinset.mpr h)
    simp [hfn]

/-- Constant classes are exactly the elements whose positive-degree coefficients vanish. -/
theorem mem_range_degreeZero_iff (g : G) :
    g ∈ LinearMap.range (degreeZero I M) ↔ ∀ n, n ≠ 0 → coefficient I M n g = 0 := by
  constructor
  · rintro ⟨q, rfl⟩ n hn
    induction q using Submodule.Quotient.induction_on with
    | H m => simp [degreeZero_mk, coefficient_mk, PolynomialModule.coeff_single, Ne.symm hn]
  · intro h
    induction g using Submodule.Quotient.induction_on with
    | H p =>
      refine ⟨Submodule.Quotient.mk ((p : PolynomialModule R M).coeff 0), ?_⟩
      apply coefficient_injective I M
      funext n
      by_cases hn : n = 0
      · subst n
        simp
      · have hz :
            coefficient I M n
              (degreeZero I M
                (Submodule.Quotient.mk ((p : PolynomialModule R M).coeff 0))) = 0 := by
          simp [degreeZero_mk, coefficient_mk, PolynomialModule.coeff_single, Ne.symm hn]
        exact hz.trans (h n hn).symm

private theorem smul_mem_pow_smul {i j : ℕ} {a : R} {m : M}
    (ha : a ∈ I ^ i) (hm : m ∈ I ^ j • (⊤ : Submodule R M)) :
    a • m ∈ I ^ (i + j) • (⊤ : Submodule R M) := by
  rw [pow_add, mul_smul]
  exact Submodule.smul_mem_smul ha hm

/-- Multiplication of homogeneous representatives is the corresponding stage product. -/
theorem monomial_smul_single {i j : ℕ} (a : R) (m : M)
    (ha : a ∈ I ^ i) (hm : m ∈ I ^ j • (⊤ : Submodule R M)) :
    (⟨Polynomial.monomial i a, reesAlgebra.monomial_mem.mpr ha⟩ : B) •
        (⟨PolynomialModule.single R j m, single_mem I M j m hm⟩ : N) =
      (⟨PolynomialModule.single R (i + j) (a • m),
        single_mem I M (i + j) (a • m) (by
          rw [pow_add, mul_smul]
          exact Submodule.smul_mem_smul ha hm)⟩ : N) := by
  apply Subtype.ext
  exact PolynomialModule.monomial_smul_single _ _ _ _

/-- A homogeneous scalar acts on a homogeneous module representative by the stage product. -/
theorem coefficient_monomial_smul_single {i j : ℕ} (a : R) (m : M)
    (ha : a ∈ I ^ i) (hm : m ∈ I ^ j • (⊤ : Submodule R M)) :
    coefficient I M (i + j)
      ((Ideal.Quotient.mk J
        (⟨Polynomial.monomial i a, reesAlgebra.monomial_mem.mpr ha⟩ : B) : C) •
        (Submodule.Quotient.mk
          (⟨PolynomialModule.single R j m, single_mem I M j m hm⟩ : N) : G)) =
      Submodule.Quotient.mk (a • m) := by
  rw [Module.Quotient.mk_smul_mk, coefficient_mk]
  change Submodule.Quotient.mk
    ((Polynomial.monomial i a • PolynomialModule.single R j m).coeff (i + j)) = _
  simp

/-- The stage product is unchanged by changing either representative by the next power. -/
theorem stage_smul_congr {i j : ℕ} (a a' : R) (m m' : M)
    (ha' : a' ∈ I ^ i) (hm : m ∈ I ^ j • (⊤ : Submodule R M))
    (haa' : a - a' ∈ I ^ (i + 1))
    (hmm' : m - m' ∈ I ^ (j + 1) • (⊤ : Submodule R M)) :
    (Submodule.Quotient.mk (a • m) : M ⧸ (I ^ (i + j + 1) • (⊤ : Submodule R M))) =
      Submodule.Quotient.mk (a' • m') := by
  apply (Submodule.Quotient.eq _).mpr
  have hleft : (a - a') • m ∈ I ^ (i + j + 1) • (⊤ : Submodule R M) := by
    simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      (smul_mem_pow_smul I M haa' hm)
  have hright : a' • (m - m') ∈ I ^ (i + j + 1) • (⊤ : Submodule R M) := by
    simpa only [Nat.add_assoc] using (smul_mem_pow_smul I M ha' hmm')
  have he : a • m - a' • m' = (a - a') • m + a' • (m - m') := by
    simp only [sub_smul, smul_sub]
    abel
  rw [he]
  exact Submodule.add_mem _ hleft hright

/-- The characteristic map on a monomial has the expected coefficient class. -/
theorem coefficient_characteristic_monomial (n : ℕ) (a : R) (ha : a ∈ I ^ n) (m : M) :
    coefficient I M n
      (characteristic I M
        ((Ideal.Quotient.mk J
          (⟨Polynomial.monomial n a, reesAlgebra.monomial_mem.mpr ha⟩ : B)) ⊗ₜ[A]
          Submodule.Quotient.mk m)) =
      Submodule.Quotient.mk (a • m) := by
  rw [characteristic_mk_tmul_mk, coefficient_mk]
  change Submodule.Quotient.mk
    ((Polynomial.monomial n a • PolynomialModule.single R 0 m).coeff n) = _
  simp

private theorem span_degreeZero_of_pow_smul_sup (K : Ideal R) (hKI : K ≤ I)
    (hcover : ∀ n : ℕ, I ^ n • (⊤ : Submodule R M) =
      K ^ n • (⊤ : Submodule R M) ⊔ I ^ (n + 1) • (⊤ : Submodule R M)) :
    @Submodule.span (reesAlgebra K) G _ _ (moduleReesOfLE I M K hKI)
      (Set.range (degreeZero I M)) = ⊤ := by
  classical
  let : Module (reesAlgebra K) G := moduleReesOfLE I M K hKI
  let S : Submodule (reesAlgebra K) G :=
    Submodule.span (reesAlgebra K) (Set.range (degreeZero I M))
  let σ (n : ℕ) (m : M) (hm : m ∈ I ^ n • (⊤ : Submodule R M)) : N :=
    ⟨PolynomialModule.single R n m, single_mem I M n m hm⟩
  have hKI' (n : ℕ) :
      K ^ n • (⊤ : Submodule R M) ≤ I ^ n • (⊤ : Submodule R M) :=
    Submodule.smul_mono_left (pow_le_pow_left' hKI n)
  have hnext (n : ℕ) :
      I ^ (n + 1) • (⊤ : Submodule R M) ≤ I ^ n • (⊤ : Submodule R M) :=
    Submodule.smul_mono_left (Ideal.pow_le_pow_right n.le_succ)
  have hσadd (n : ℕ) (x y : M)
      (hx : x ∈ I ^ n • (⊤ : Submodule R M))
      (hy : y ∈ I ^ n • (⊤ : Submodule R M)) :
      σ n (x + y) (Submodule.add_mem _ hx hy) = σ n x hx + σ n y hy := by
    apply Subtype.ext
    exact PolynomialModule.single_add _ _ _
  -- A K^n multiple is generated by the degree-n monomials of Rees(K).
  have hKsingle (n : ℕ) (m : M) (hm : m ∈ K ^ n • (⊤ : Submodule R M)) :
      mk I M (σ n m (hKI' n hm)) ∈ S := by
    refine Submodule.smul_induction_on' hm (fun a ha m _ => ?_)
      (fun x hx y hy ihx ihy => ?_)
    · let aK : reesAlgebra K :=
        ⟨Polynomial.monomial n a, reesAlgebra.monomial_mem.mpr ha⟩
      have he : aK • degreeZero I M (Submodule.Quotient.mk m) =
          mk I M (σ n (a • m)
            (hKI' n (Submodule.smul_mem_smul ha (Submodule.mem_top)))) := by
        rw [degreeZero_mk]
        change aK • mk I M (constant I M m) = _
        refine (moduleReesOfLE_smul_mk I M K hKI aK (constant I M m)).trans ?_
        apply congrArg (mk I M)
        apply Subtype.ext
        change Polynomial.monomial n a • PolynomialModule.single R 0 m =
          PolynomialModule.single R n (a • m)
        simpa only [add_zero] using PolynomialModule.monomial_smul_single n a 0 m
      rw [← he]
      exact S.smul_mem aK (Submodule.subset_span ⟨Submodule.Quotient.mk m, rfl⟩)
    · rw [hσadd n x y (hKI' n hx) (hKI' n hy), map_add]
      exact S.add_mem ihx ihy
  -- The other summand in the cover is killed only after passing to G.
  have hsingle (n : ℕ) (m : M) (hm : m ∈ I ^ n • (⊤ : Submodule R M)) :
      mk I M (σ n m hm) ∈ S := by
    have hmem : m ∈ K ^ n • (⊤ : Submodule R M) ⊔
        I ^ (n + 1) • (⊤ : Submodule R M) := by
      rwa [← hcover n]
    rcases Submodule.mem_sup.mp hmem with ⟨x, hx, y, hy, hxy⟩
    have he : σ n m hm = σ n x (hKI' n hx) + σ n y (hnext n hy) := by
      apply Subtype.ext
      change PolynomialModule.single R n m =
        PolynomialModule.single R n x + PolynomialModule.single R n y
      rw [← PolynomialModule.single_add, hxy]
    have hz : mk I M (σ n y (hnext n hy)) = 0 := by
      change (Submodule.Quotient.mk (σ n y (hnext n hy)) : G) = 0
      exact (Submodule.Quotient.mk_eq_zero _).mpr
        ((single_mem_ideal_smul_iff I M n y (hnext n hy)).mpr hy)
    rw [he, map_add, hz, add_zero]
    exact hKsingle n x hx
  -- Decompose a polynomial representative over its finite coefficient support.
  apply top_unique
  intro g _
  induction g using Submodule.Quotient.induction_on with
  | H p =>
    change mk I M p ∈ S
    have hp : p = ∑ n ∈ (p : PolynomialModule R M).coeff.support,
        σ n ((p : PolynomialModule R M).coeff n) (p.property n) := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      change (p : PolynomialModule R M) =
        ∑ n ∈ (p : PolynomialModule R M).coeff.support,
          PolynomialModule.single R n ((p : PolynomialModule R M).coeff n)
      calc
        (p : PolynomialModule R M) = PolynomialModule.ofCoeff R
            ((p : PolynomialModule R M).coeff.sum Finsupp.single) := by
          rw [Finsupp.sum_single, PolynomialModule.ofCoeff_coeff]
        _ = _ := PolynomialModule.ofCoeff_finsuppSum _ _
    rw [hp, map_sum]
    exact S.sum_mem (fun n _ => hsingle n _ (p.property n))

/-- Under all-degree covers by a subideal, scalar extension of the first quotient
surjects onto the associated graded module. No finiteness of either ideal or quotient
is required. -/
theorem liftBaseChange_surjective_of_pow_smul_sup (K : Ideal R) (hKI : K ≤ I)
    (hcover : ∀ n : ℕ, I ^ n • (⊤ : Submodule R M) =
      K ^ n • (⊤ : Submodule R M) ⊔ I ^ (n + 1) • (⊤ : Submodule R M)) :
    Function.Surjective
      (@LinearMap.liftBaseChange R Q G (reesAlgebra K) _ _ _ _ _ _ _
        (moduleReesOfLE I M K hKI) (scalarTowerReesOfLE I M K hKI)
        ((degreeZero I M).restrictScalars R)) := by
  let : Module (reesAlgebra K) G := moduleReesOfLE I M K hKI
  let : IsScalarTower R (reesAlgebra K) G := scalarTowerReesOfLE I M K hKI
  apply LinearMap.range_eq_top.mp
  rw [LinearMap.range_liftBaseChange, LinearMap.coe_range]
  exact span_degreeZero_of_pow_smul_sup I M K hKI hcover

/-- Under all-degree covers by a subideal, finiteness of the first quotient over
`R ⧸ I` implies finiteness of the associated graded module over the subideal Rees algebra.
The subideal need not be finitely generated. -/
theorem finite_rees_of_finite_quotient (K : Ideal R) (hKI : K ≤ I)
    (hcover : ∀ n : ℕ, I ^ n • (⊤ : Submodule R M) =
      K ^ n • (⊤ : Submodule R M) ⊔ I ^ (n + 1) • (⊤ : Submodule R M))
    [Module.Finite A Q] :
    @Module.Finite (reesAlgebra K) G _ _ (moduleReesOfLE I M K hKI) := by
  let : Module (reesAlgebra K) G := moduleReesOfLE I M K hKI
  let : IsScalarTower R (reesAlgebra K) G := scalarTowerReesOfLE I M K hKI
  let : IsScalarTower R A Q :=
    (Module.isTorsionBySet_quotient_ideal_smul M I).isScalarTower (S := R)
  have : Module.Finite R Q := Module.Finite.trans A Q
  exact Module.Finite.of_surjective
    (LinearMap.liftBaseChange (reesAlgebra K) ((degreeZero I M).restrictScalars R))
    (liftBaseChange_surjective_of_pow_smul_sup I M K hKI hcover)

/-- A Noetherian first quotient and all-degree covers by a finitely generated subideal
make the associated graded module Noetherian over the quotient Rees algebra.
Neither the coefficient ring nor the original module is assumed Noetherian. -/
theorem isNoetherian_of_fg_of_pow_smul_sup (K : Ideal R) (hKI : K ≤ I) (hKfg : K.FG)
    (hcover : ∀ n : ℕ, I ^ n • (⊤ : Submodule R M) =
      K ^ n • (⊤ : Submodule R M) ⊔ I ^ (n + 1) • (⊤ : Submodule R M))
    [IsNoetherian R Q] : IsNoetherian C G := by
  let : Module (reesAlgebra K) G := moduleReesOfLE I M K hKI
  let : IsScalarTower R (reesAlgebra K) G := scalarTowerReesOfLE I M K hKI
  let : Algebra.FiniteType R (reesAlgebra K) :=
    ⟨(reesAlgebra K).fg_top.mpr (reesAlgebra.fg hKfg)⟩
  have : IsNoetherian (reesAlgebra K) ((reesAlgebra K) ⊗[R] Q) :=
    Algebra.EssFiniteType.isNoetherian_tensorProduct R (reesAlgebra K) Q
  have hG : IsNoetherian (reesAlgebra K) G :=
    isNoetherian_of_surjective
      (LinearMap.liftBaseChange (reesAlgebra K) ((degreeZero I M).restrictScalars R))
      (LinearMap.range_eq_top.mpr
        (liftBaseChange_surjective_of_pow_smul_sup I M K hKI hcover))
  let : Module (reesAlgebra K) C := (reesAlgebra.quotientMapOfLE I K hKI).toRingHom.toModule
  let : IsScalarTower (reesAlgebra K) C G := scalarTowerReesQuotientOfLE I M K hKI
  exact isNoetherian_of_tower (reesAlgebra K) hG

/-- Every associated graded class is a sum of scalar multiples of constant classes. -/
theorem characteristic_surjective : Function.Surjective (characteristic I M) := by
  let : Module B G := moduleReesOfLE I M I le_rfl
  let : Module B C := (reesAlgebra.quotientMapOfLE I I le_rfl).toRingHom.toModule
  let : IsScalarTower B C G := scalarTowerReesQuotientOfLE I M I le_rfl
  have hspan := span_degreeZero_of_pow_smul_sup I M I le_rfl (fun n =>
    (sup_of_le_left (Submodule.smul_mono_left (Ideal.pow_le_pow_right n.le_succ))).symm)
  apply LinearMap.range_eq_top.mp
  apply (Submodule.restrictScalars_eq_top_iff B C G).mp
  apply top_unique
  rw [← hspan]
  apply Submodule.span_le.mpr
  rintro _ ⟨q, rfl⟩
  refine ⟨(1 : C) ⊗ₜ[A] q, ?_⟩
  simpa only [one_smul] using characteristic_tmul I M (1 : C) q

/-- Finiteness of the first quotient implies finiteness of the associated graded module.

For background, see K. Fujiwara and F. Kato, *Foundations of Rigid Geometry I*,
[arXiv:1308.4734v5](https://arxiv.org/abs/1308.4734v5). The precise formulation
of this first-quotient criterion is proved here. -/
theorem finite_of_finite_quotient [Module.Finite A Q] : Module.Finite C G :=
  Module.Finite.of_surjective (characteristic I M) (characteristic_surjective I M)

end AssociatedGradedModule
end Ideal
