/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GradedRings.ReesModule.Evaluation
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.RingTheory.Ideal.Operations

/-!
# Positive augmentation of Rees modules

For an ideal filtration `H`, the constant-coefficient augmentation of `reesAlgebra I`
has a kernel consisting of positive-degree elements. This module characterizes the
product of this ideal with the Rees module coefficientwise, and characterizes when
that product equals the kernel of evaluation at zero.

## Main results

* `Ideal.Filtration.mem_augmentationIdeal_smul_top_iff` gives the coefficient
  criterion for membership in the augmentation ideal times the Rees module.
* `Ideal.Filtration.ker_evalRees_zero_eq_augmentationIdeal_smul_top_iff` identifies
  equality with the evaluation kernel with stability from degree zero.
* `Ideal.Filtration.ker_evalRees_zero_eq_augmentationIdeal_smul_top_iff_eq_pow_smul`
  expresses the same equality by powers of the ideal acting on the initial stage.

The augmentation has codomain `R`, rather than `R ⧸ I`. Evaluation retains its
codomain `H.N 0`, and the initial stage need not be all of the ambient module.
The statements use the Rees module and semilinear evaluation API of
`GradedRings.ReesModule.Evaluation` and Mathlib's polynomial-module and
ideal–submodule operations.
-/

@[expose] public section

universe u v

open scoped Pointwise

namespace Ideal.Filtration

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
variable {I : Ideal R} (H : I.Filtration M)

local notation "B" => reesAlgebra I
local notation "E" => H.submodule
local notation "K₀" =>
  RingHom.ker (RingHom.comp (Polynomial.evalRingHom (0 : R))
    (AlgHom.toRingHom (Subalgebra.val (reesAlgebra I))))

private theorem single_succ_mem_augmentationIdeal_smul (n : ℕ) (x : M)
    (hx : x ∈ I • H.N n) :
    PolynomialModule.single R (n + 1) x ∈ K₀ • H.submodule := by
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro a ha m hm
    let b : B := ⟨Polynomial.monomial 1 a,
      reesAlgebra.monomial_mem.mpr (by simpa only [pow_one] using ha)⟩
    have hb : b ∈ K₀ := by
      apply RingHom.mem_ker.mpr
      simp [b, Polynomial.coe_evalRingHom, Polynomial.eval_monomial]
    have hm' : PolynomialModule.single R n m ∈ H.submodule := by
      apply (H.mem_submodule _).mpr
      intro q
      simp only [PolynomialModule.coeff_single]
      by_cases hq : q = n
      · simpa only [hq, Finsupp.single_eq_same] using hm
      · simpa only [Finsupp.single_eq_of_ne hq] using (H.N q).zero_mem
    have hprod := Submodule.smul_mem_smul hb hm'
    simpa only [Subalgebra.smul_def, b, PolynomialModule.monomial_smul_single,
      Nat.add_comm 1 n] using hprod
  · intro x y hx hy
    simpa only [PolynomialModule.single_add] using
      (K₀ • H.submodule).add_mem hx hy

private theorem mem_augmentationIdeal_smul_top_of_coeff (f : E)
    (hzero : (f : PolynomialModule R M).coeff 0 = 0)
    (hpos : ∀ n : ℕ, (f : PolynomialModule R M).coeff (n + 1) ∈ I • H.N n) :
    f ∈ K₀ • (⊤ : Submodule B E) := by
  apply (Submodule.mem_smul_top_iff (I := K₀) H.submodule f).mpr
  have hsingle (n : ℕ) :
      PolynomialModule.single R n ((f : PolynomialModule R M).coeff n) ∈
        K₀ • H.submodule := by
    cases n with
    | zero =>
        simpa only [hzero, PolynomialModule.single_zero] using
          (K₀ • H.submodule).zero_mem
    | succ n =>
        exact H.single_succ_mem_augmentationIdeal_smul n _ (hpos n)
  have hsum :
      (f : PolynomialModule R M).coeff.sum (fun n m => PolynomialModule.single R n m) ∈
        K₀ • H.submodule := by
    exact Submodule.sum_mem _ fun n _ => hsingle n
  have hrec :
      (f : PolynomialModule R M).coeff.sum (fun n m => PolynomialModule.single R n m) =
        (f : PolynomialModule R M) := by
    apply PolynomialModule.coeff_injective
    rw [PolynomialModule.coeff_finsuppSum]
    simpa only [PolynomialModule.coeff_single] using
      (Finsupp.sum_single (f : PolynomialModule R M).coeff)
  simpa only [hrec] using hsum

private lemma augmentationIdeal_smul_top_coeff (f : E)
    (hf : f ∈ K₀ • (⊤ : Submodule B E)) :
    (f : PolynomialModule R M).coeff 0 = 0 ∧
      ∀ n : ℕ, (f : PolynomialModule R M).coeff (n + 1) ∈ I • H.N n := by
  classical
  refine Submodule.smul_induction_on hf ?_ ?_
  · intro b hb g _
    have hb0 : (b : Polynomial R).coeff 0 = 0 := by
      simpa only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
        Polynomial.coe_evalRingHom, Subalgebra.val_apply,
        Polynomial.coeff_zero_eq_eval_zero] using
        (RingHom.mem_ker.mp hb)
    have hbI : ∀ i, (b : Polynomial R).coeff i ∈ I ^ i :=
      (mem_reesAlgebra_iff I (b : Polynomial R)).mp b.property
    have hg : ∀ j, (g : PolynomialModule R M).coeff j ∈ H.N j :=
      (H.mem_submodule (g : PolynomialModule R M)).mp g.property
    constructor
    · rw [Submodule.coe_smul, Subalgebra.smul_def, PolynomialModule.smul_apply]
      simp only [Finset.Nat.antidiagonal_zero, Finset.sum_singleton, hb0, zero_smul]
    · intro n
      rw [Submodule.coe_smul, Subalgebra.smul_def, PolynomialModule.smul_apply]
      apply (I • H.N n).sum_mem
      intro p hp
      have hp' : p.1 + p.2 = n + 1 := by simpa using hp
      cases hi : p.1 with
      | zero =>
          simpa only [hi, hb0, zero_smul] using (I • H.N n).zero_mem
      | succ k =>
          have hkn : k + p.2 = n := by
            apply Nat.succ.inj
            simpa only [hi, Nat.succ_add] using hp'
          have hmem :
              (b : Polynomial R).coeff p.1 • (g : PolynomialModule R M).coeff p.2 ∈
                I ^ (k + 1) • H.N p.2 :=
            Submodule.smul_mem_smul
              (by simpa only [hi, Nat.succ_eq_add_one] using hbI p.1) (hg p.2)
          simpa only [pow_one, hkn, hi] using
            (H.pow_smul_le_pow_smul k p.2 1 hmem)
  · intro x y hx hy
    constructor
    · simp only [Submodule.coe_add, PolynomialModule.coeff_add, Finsupp.add_apply,
        hx.1, hy.1, add_zero]
    · intro n
      simpa only [Submodule.coe_add, PolynomialModule.coeff_add, Finsupp.add_apply] using
        (I • H.N n).add_mem (hx.2 n) (hy.2 n)

/-- An element of the Rees module belongs to the positive augmentation ideal times
that module exactly when its constant coefficient is zero and its coefficient of
degree `n + 1` belongs to `I • H.N n` for every `n`. -/
theorem mem_augmentationIdeal_smul_top_iff (f : E) :
    f ∈ K₀ • (⊤ : Submodule B E) ↔
      (f : PolynomialModule R M).coeff 0 = 0 ∧
        ∀ n : ℕ, (f : PolynomialModule R M).coeff (n + 1) ∈ I • H.N n := by
  constructor
  · exact H.augmentationIdeal_smul_top_coeff f
  · rintro ⟨hzero, hpos⟩
    exact H.mem_augmentationIdeal_smul_top_of_coeff f hzero hpos

private theorem mem_ker_evalRees_zero_iff (f : E) :
    f ∈ LinearMap.ker (H.evalRees (0 : R)) ↔
      (f : PolynomialModule R M).coeff 0 = 0 := by
  rw [LinearMap.mem_ker]
  constructor
  · intro hf
    simpa only [coe_evalRees, PolynomialModule.eval_zero, Submodule.coe_zero] using
      congrArg (fun x : H.N 0 => (x : M)) hf
  · intro hf
    apply Subtype.ext
    simpa only [coe_evalRees, PolynomialModule.eval_zero, Submodule.coe_zero] using hf

/-- The kernel of semilinear evaluation at zero equals the positive augmentation
ideal times the Rees module if and only if the filtration is stable from degree zero. -/
theorem ker_evalRees_zero_eq_augmentationIdeal_smul_top_iff :
    LinearMap.ker (H.evalRees (0 : R)) = K₀ • (⊤ : Submodule B E) ↔
      ∀ n : ℕ, I • H.N n = H.N (n + 1) := by
  constructor
  · intro h n
    apply le_antisymm
    · simpa only [pow_one, Nat.add_comm 1 n] using H.pow_smul_le 1 n
    · intro x hx
      have hsingle : PolynomialModule.single R (n + 1) x ∈ H.submodule := by
        apply (H.mem_submodule _).2
        intro i
        by_cases hi : i = n + 1
        · subst i
          simpa only [PolynomialModule.coeff_single, Finsupp.single_eq_same] using hx
        · simpa only [PolynomialModule.coeff_single, Finsupp.single_eq_of_ne hi] using
            (H.N i).zero_mem
      let f : E := ⟨PolynomialModule.single R (n + 1) x, hsingle⟩
      have hf : f ∈ LinearMap.ker (H.evalRees (0 : R)) := by
        apply (H.mem_ker_evalRees_zero_iff f).2
        simp [f, PolynomialModule.coeff_single]
      rw [h] at hf
      have hcoeff := ((H.mem_augmentationIdeal_smul_top_iff f).1 hf).2 n
      simpa only [f, PolynomialModule.coeff_single, Finsupp.single_eq_same] using hcoeff
  · intro h
    apply Submodule.ext
    intro f
    rw [H.mem_ker_evalRees_zero_iff, H.mem_augmentationIdeal_smul_top_iff]
    constructor
    · intro hf
      refine ⟨hf, ?_⟩
      intro n
      rw [h n]
      exact (H.mem_submodule (f : PolynomialModule R M)).1 f.property (n + 1)
    · exact fun hf => hf.1

/-- The kernel of semilinear evaluation at zero equals the positive augmentation
ideal times the Rees module if and only if every stage is the corresponding power
of the ideal acting on the initial stage. -/
theorem ker_evalRees_zero_eq_augmentationIdeal_smul_top_iff_eq_pow_smul :
    LinearMap.ker (H.evalRees (0 : R)) = K₀ • (⊤ : Submodule B E) ↔
      ∀ n : ℕ, H.N n = I ^ n • H.N 0 := by
  rw [H.ker_evalRees_zero_eq_augmentationIdeal_smul_top_iff]
  constructor
  · intro h n
    induction n with
    | zero => simp only [pow_zero, Submodule.one_smul]
    | succ n ih =>
        rw [← h n, ih, Ideal.IsTwoSided.pow_succ, Submodule.mul_smul]
  · intro h n
    rw [h n, h (n + 1), Ideal.IsTwoSided.pow_succ, Submodule.mul_smul]

end Ideal.Filtration
