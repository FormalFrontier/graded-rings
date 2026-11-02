/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GradedRings.ReesModule.Map

/-!
# Kernels and injectivity of natural Rees-module maps

The kernel of a natural Rees-module map is detected coefficientwise by the kernel
of the original linear map. Injectivity is equivalent to injectivity on the
degree-zero source stage: antitonicity places every source coefficient in that
stage, and degree-zero singletons detect its kernel. Ambient injectivity is not
required.
-/

@[expose] public section

universe u v w

namespace Ideal.Filtration

variable {R : Type u} [CommRing R] {I : Ideal R}
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]
variable (F : I.Filtration M) (H : I.Filtration N) (f : M →ₗ[R] N)
variable (hf : ∀ q : ℕ, F.N q ≤ (H.N q).comap f)

/-- Kernel membership for a natural Rees-module map is coefficientwise
membership in the kernel of the original linear map. -/
theorem mem_ker_reesMap_iff (p : F.submodule) :
    p ∈ LinearMap.ker (F.reesMap H f hf) ↔
      ∀ q : ℕ, (p : PolynomialModule R M).coeff q ∈ LinearMap.ker f := by
  constructor
  · intro hp q
    rw [LinearMap.mem_ker, ← F.coeff_reesMap H f hf q p]
    rw [LinearMap.mem_ker] at hp
    rw [hp]
    simp
  · intro hp
    apply LinearMap.mem_ker.mpr
    apply Subtype.ext
    apply PolynomialModule.coeff_injective
    apply Finsupp.ext
    intro q
    simpa only [F.coeff_reesMap H f hf, Submodule.coe_zero,
      PolynomialModule.coeff_zero, Finsupp.zero_apply] using LinearMap.mem_ker.mp (hp q)

/-- A natural Rees-module map is injective exactly when the original
linear map is injective on the degree-zero filtration stage. -/
theorem reesMap_injective_iff :
    Function.Injective (F.reesMap H f hf) ↔
      Function.Injective (f.domRestrict (F.N 0)) := by
  rw [LinearMap.injective_domRestrict_iff, LinearMap.disjoint_ker]
  constructor
  · intro hinj m hm hfm
    let p : F.submodule :=
      ⟨PolynomialModule.single R 0 m, by
        apply (F.mem_submodule _).2
        intro q
        by_cases hq : 0 = q
        · subst q
          simpa [PolynomialModule.coeff_single] using hm
        · simp [PolynomialModule.coeff_single, hq]⟩
    have hp : p ∈ LinearMap.ker (F.reesMap H f hf) := by
      apply (F.mem_ker_reesMap_iff H f hf p).2
      intro q
      apply LinearMap.mem_ker.mpr
      by_cases hq : 0 = q
      · subst q
        simpa [p, PolynomialModule.coeff_single] using hfm
      · simp [p, PolynomialModule.coeff_single, hq]
    have hp0 : p = 0 :=
      hinj (by simpa only [map_zero] using LinearMap.mem_ker.mp hp)
    have hc := congrArg
      (fun z : F.submodule => (z : PolynomialModule R M).coeff 0) hp0
    simpa [p, PolynomialModule.coeff_single] using hc
  · intro hzero p r hpr
    apply Subtype.ext
    apply PolynomialModule.coeff_injective
    apply Finsupp.ext
    intro q
    apply sub_eq_zero.mp
    apply hzero
    · exact (F.N 0).sub_mem
        (F.antitone (Nat.zero_le q) ((F.mem_submodule _).1 p.property q))
        (F.antitone (Nat.zero_le q) ((F.mem_submodule _).1 r.property q))
    · rw [map_sub, ← F.coeff_reesMap H f hf q p,
        ← F.coeff_reesMap H f hf q r, hpr, sub_self]

end Ideal.Filtration
