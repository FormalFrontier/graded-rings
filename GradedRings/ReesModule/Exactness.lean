/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GradedRings.ReesModule.Range
public import GradedRings.ReesModule.Kernel
public import Mathlib.Algebra.Exact.Basic

/-!
# Exactness of natural Rees-module maps

Natural Rees maps are exact at the middle Rees module precisely when each source-stage
image equals the intersection of the corresponding middle stage with the kernel of the
original second map. No ambient complex condition is assumed. The criterion combines the
coefficientwise range and kernel descriptions for natural Rees maps with Mathlib's
exactness API, developed by Antoine Chambert-Loir.
-/

@[expose] public section

universe u v w x

namespace Ideal.Filtration

variable {R : Type u} [CommRing R] {I : Ideal R}
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]
variable {P : Type x} [AddCommGroup P] [Module R P]
variable (F : I.Filtration M) (G : I.Filtration N) (H : I.Filtration P)
variable (f : M →ₗ[R] N) (g : N →ₗ[R] P)
variable (hf : ∀ n : ℕ, F.N n ≤ (G.N n).comap f)
variable (hg : ∀ n : ℕ, G.N n ≤ (H.N n).comap g)

/-- The two induced natural Rees-module maps are exact if and only if, in every degree,
the image of the source stage is the intersection of the middle stage with the kernel of
the second linear map. -/
theorem reesMap_exact_iff :
    Function.Exact (F.reesMap G f hf) (G.reesMap H g hg) ↔
      ∀ n : ℕ, (F.N n).map f = G.N n ⊓ LinearMap.ker g := by
  constructor
  · intro hex n
    apply le_antisymm
    · rintro y ⟨m, hm, rfl⟩
      refine ⟨hf n hm, ?_⟩
      let p : F.submodule := ⟨PolynomialModule.single R n m, by
        apply (F.mem_submodule _).mpr
        intro i
        by_cases hi : n = i
        · subst i
          simpa [PolynomialModule.coeff_single] using hm
        · simp [PolynomialModule.coeff_single, hi]⟩
      have hcomp : G.reesMap H g hg (F.reesMap G f hf p) = 0 :=
        (hex _).mpr ⟨p, rfl⟩
      have hpker : F.reesMap G f hf p ∈ LinearMap.ker (G.reesMap H g hg) :=
        LinearMap.mem_ker.mpr hcomp
      have hc :=
        (G.mem_ker_reesMap_iff H g hg (F.reesMap G f hf p)).mp hpker n
      rw [F.coeff_reesMap G f hf] at hc
      simpa [p, PolynomialModule.coeff_single] using hc
    · rintro y ⟨hyG, hyg⟩
      let p : G.submodule := ⟨PolynomialModule.single R n y, by
        apply (G.mem_submodule _).mpr
        intro i
        by_cases hi : n = i
        · subst i
          simpa [PolynomialModule.coeff_single] using hyG
        · simp [PolynomialModule.coeff_single, hi]⟩
      have hpker : p ∈ LinearMap.ker (G.reesMap H g hg) := by
        apply (G.mem_ker_reesMap_iff H g hg p).mpr
        intro i
        by_cases hi : n = i
        · subst i
          simpa [p, PolynomialModule.coeff_single] using hyg
        · simp [p, PolynomialModule.coeff_single, hi]
      have hprange : p ∈ LinearMap.range (F.reesMap G f hf) :=
        LinearMap.mem_range.mpr ((hex p).mp (LinearMap.mem_ker.mp hpker))
      simpa [p, PolynomialModule.coeff_single] using
        ((F.mem_range_reesMap_iff G f hf p).mp hprange n)
  · intro hstage
    apply LinearMap.exact_iff.mpr
    apply Submodule.ext
    intro y
    rw [G.mem_ker_reesMap_iff H g hg y,
      F.mem_range_reesMap_iff G f hf y]
    constructor
    · intro hy n
      rw [hstage n]
      exact ⟨(G.mem_submodule _).mp y.property n, hy n⟩
    · intro hy n
      have hn := hy n
      rw [hstage n] at hn
      exact hn.2

end Ideal.Filtration
