/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

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
# Associated graded modules of ideal-adic filtrations

The Rees module modulo the extended ideal carries a canonical surjection from the
scalar extension of the first quotient of the module. Consequently, finiteness of
the first quotient implies finiteness of this associated graded module.

## References

For background, see K. Fujiwara and F. Kato, *Foundations of Rigid Geometry I*,
[arXiv:1308.4734v5](https://arxiv.org/abs/1308.4734v5). The precise formulation
of the first-quotient finiteness criterion in this file is proved here.
-/

@[expose] public section

open scoped TensorProduct

universe u v

namespace Ideal

variable {R : Type u} [CommRing R] (I : Ideal R)
variable (M : Type v) [AddCommGroup M] [Module R M]

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

private theorem span_constants : Submodule.span B (Set.range (constant I M)) = ⊤ := by
  have hgen : N = Submodule.span B
      (PolynomialModule.single R 0 '' (Set.univ : Set M)) := by
    have h := ((I.stableFiltration (⊤ : Submodule R M)).submodule_eq_span_le_iff_stable_ge 0).2
      (fun n _ => by
        simp only [Ideal.stableFiltration_N]
        rw [← mul_smul, pow_succ'])
    simpa using h
  have himage : (Submodule.subtype N) '' Set.range (constant I M) =
      PolynomialModule.single R 0 '' (Set.univ : Set M) := by
    ext f
    constructor
    · rintro ⟨n, ⟨m, rfl⟩, rfl⟩
      exact ⟨m, Set.mem_univ _, rfl⟩
    · rintro ⟨m, _, rfl⟩
      exact ⟨constant I M m, ⟨m, rfl⟩, rfl⟩
  have hmap : (Submodule.span B (Set.range (constant I M))).map (Submodule.subtype N) = N := by
    rw [Submodule.map_span, himage, ← hgen]
  apply top_unique
  intro n _
  have hn : (n : PolynomialModule R M) ∈
      (Submodule.span B (Set.range (constant I M))).map (Submodule.subtype N) := by
    rw [hmap]
    exact n.property
  rcases Submodule.mem_map.mp hn with ⟨n', hn', he⟩
  have : n' = n := Subtype.ext he
  simpa only [this] using hn'

/-- Every associated graded class is a sum of scalar multiples of constant classes. -/
theorem characteristic_surjective : Function.Surjective (characteristic I M) := by
  intro g
  induction g using Submodule.Quotient.induction_on with
  | H n =>
    have hn : n ∈ Submodule.span B (Set.range (constant I M)) := by
      rw [span_constants]
      exact Submodule.mem_top
    induction hn using Submodule.span_induction with
    | mem n hn =>
      rcases hn with ⟨m, rfl⟩
      refine ⟨(1 : C) ⊗ₜ[A] Submodule.Quotient.mk m, ?_⟩
      calc
        characteristic I M ((1 : C) ⊗ₜ[A] Submodule.Quotient.mk m) =
            (1 : C) • degreeZero I M (Submodule.Quotient.mk m) :=
          characteristic_tmul I M 1 (Submodule.Quotient.mk m)
        _ = degreeZero I M (Submodule.Quotient.mk m) := _root_.one_smul C _
        _ = mk I M (constant I M m) := degreeZero_mk I M m
    | zero =>
      exact ⟨0, by
        rw [map_zero]
        exact (mk I M).map_zero.symm⟩
    | add n n' _ _ hn hn' =>
      rcases hn with ⟨t, ht⟩
      rcases hn' with ⟨t', ht'⟩
      exact ⟨t + t', by
        rw [map_add, ht, ht']
        exact ((mk I M).map_add n n').symm⟩
    | smul b n _ hn =>
      rcases hn with ⟨t, ht⟩
      exact ⟨Ideal.Quotient.mk J b • t, by
        rw [map_smul, ht]
        exact quotient_smul_mk I M b n⟩

/-- Finiteness of the first quotient implies finiteness of the associated graded module.

For background, see K. Fujiwara and F. Kato, *Foundations of Rigid Geometry I*,
[arXiv:1308.4734v5](https://arxiv.org/abs/1308.4734v5). The precise formulation
of this first-quotient criterion is proved here. -/
theorem finite_of_finite_quotient [Module.Finite A Q] : Module.Finite C G :=
  Module.Finite.of_surjective (characteristic I M) (characteristic_surjective I M)

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

end AssociatedGradedModule
end Ideal
