/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GradedRings.ReesModule.Map
public import Mathlib.LinearAlgebra.Finsupp.Pi

/-!
# Images of natural Rees-module maps

The range of a stage-preserving Rees-module map is described by membership of every
coefficient in the corresponding stage image. In particular, the Rees-module map is
surjective precisely when the original linear map maps each source stage onto its target
stage.

The proofs use Mathlib's coefficient equivalence for polynomial modules, its all-stage
`Finsupp.submodule_eq_iSup` description, and its submodule image calculus.
-/

@[expose] public section

universe u v w

namespace Ideal.Filtration

variable {R : Type u} [CommRing R] {I : Ideal R}
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]
variable (F : I.Filtration M) (H : I.Filtration N) (f : M →ₗ[R] N)
variable (hf : ∀ q, F.N q ≤ (H.N q).comap f)

/-- A target Rees-module element is in the range of the induced map if and only if each
coefficient belongs to the image of the corresponding source stage. -/
theorem mem_range_reesMap_iff (y : H.submodule) :
    y ∈ LinearMap.range (F.reesMap H f hf) ↔
      ∀ q : ℕ, (y : PolynomialModule R N).coeff q ∈ (F.N q).map f := by
  constructor
  · intro hy q
    obtain ⟨p, rfl⟩ := LinearMap.mem_range.mp hy
    rw [F.coeff_reesMap H f hf]
    exact Submodule.mem_map.mpr
      ⟨_, (F.mem_submodule _).mp p.property q, rfl⟩
  · intro hy
    -- Transport the stock all-stage description through the coefficient map.
    have himage : (Finsupp.submodule F.N).map (Finsupp.mapRange.linearMap f) =
        Finsupp.submodule (fun q => (F.N q).map f) := by
      rw [Finsupp.submodule_eq_iSup, Submodule.map_iSup, Finsupp.submodule_eq_iSup]
      apply iSup_congr
      intro q
      rw [← Submodule.map_comp, ← Submodule.map_comp]
      congr 1
      ext m i
      simp [Finsupp.lsingle_apply, Finsupp.mapRange_single]
    have hy' : (y : PolynomialModule R N).coeff ∈
        Finsupp.submodule (fun q => (F.N q).map f) :=
      (Finsupp.mem_submodule_iff _ _).mpr hy
    rw [← himage] at hy'
    obtain ⟨c, hc, hcy⟩ := Submodule.mem_map.mp hy'
    let p : PolynomialModule R M := (PolynomialModule.coeffLinearEquiv R R).symm c
    have hp : p.coeff = c := by simp [p]
    have hpF : p ∈ F.submodule := by
      apply (F.mem_submodule p).mpr
      simpa only [hp] using (Finsupp.mem_submodule_iff _ _).mp hc
    refine LinearMap.mem_range.mpr ⟨⟨p, hpF⟩, ?_⟩
    apply Subtype.ext
    apply PolynomialModule.coeff_injective
    ext q
    rw [F.coeff_reesMap H f hf]
    change f (p.coeff q) = (y : PolynomialModule R N).coeff q
    rw [hp]
    exact congrArg (fun z : ℕ →₀ N => z q) hcy

/-- The induced Rees-module map is surjective if and only if the original linear map
maps every source stage onto the corresponding target stage. -/
theorem reesMap_surjective_iff :
    Function.Surjective (F.reesMap H f hf) ↔
      ∀ q : ℕ, (F.N q).map f = H.N q := by
  constructor
  · intro h q
    apply le_antisymm
    · rintro n ⟨m, hm, rfl⟩
      exact hf q hm
    · intro n hn
      let y : H.submodule := ⟨PolynomialModule.single R q n, by
        apply (H.mem_submodule _).mpr
        intro i
        by_cases hi : q = i
        · subst i
          simpa using hn
        · simp [PolynomialModule.coeff_single, hi]⟩
      have hy : y ∈ LinearMap.range (F.reesMap H f hf) :=
        LinearMap.mem_range.mpr (h y)
      simpa [y] using ((F.mem_range_reesMap_iff H f hf y).mp hy q)
  · intro h y
    apply LinearMap.mem_range.mp
    apply (F.mem_range_reesMap_iff H f hf y).mpr
    intro q
    rw [h q]
    exact (H.mem_submodule _).mp y.property q

end Ideal.Filtration
