/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GradedRings.FilteredAssociatedGraded.Adic
import GradedRings.FilteredAssociatedGraded.Map
import GradedRings.FilteredAssociatedGraded.PowerQuotientAction
import Mathlib.Tactic

/-!
# Integer filtrations with nonzero graded pieces

The zero-ideal stable filtration of `2ℤ` starts at a proper submodule. Its degree-zero
piece contains the nonzero class of `2`, transported through the equivalence between
natural and integer graded pieces.

The integer filtration equal to `ℤ` through degree `-2` and zero thereafter has a
nonzero degree-`-2` piece represented by `1`. Its stages at `-2` and `-1` differ, so it
is not the extension of a natural filtration by `Ideal.Filtration.toIntFiltration`.

A stage-preserving map restricts to the ideal-power quotient scalars through
`LinearMap.restrictScalars`. The final example computes how this map intertwines
homogeneous scalar multiplication on representatives.
-/

@[expose] public section

universe u v w

namespace IntegerFiltrations

private def doubledIntegers : Submodule ℤ ℤ :=
  Submodule.span ℤ {(2 : ℤ)}

private def doubledFiltration : (0 : Ideal ℤ).Filtration ℤ :=
  (0 : Ideal ℤ).stableFiltration doubledIntegers

private theorem doubledFiltration_zero : doubledFiltration.N 0 = doubledIntegers := by
  change (0 : Ideal ℤ) ^ (0 : ℕ) • doubledIntegers = doubledIntegers
  simp

private theorem doubledFiltration_one : doubledFiltration.N 1 = ⊥ := by
  change (0 : Ideal ℤ) ^ (1 : ℕ) • doubledIntegers = ⊥
  simp

private theorem one_not_mem_doubledIntegers : (1 : ℤ) ∉ doubledIntegers := by
  intro h
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp h
  have ha' : a * (2 : ℤ) = 1 := by
    simpa only [smul_eq_mul] using ha
  omega

private def twoAtZero : doubledFiltration.N 0 :=
  ⟨2, by
    rw [doubledFiltration_zero]
    exact Submodule.subset_span (by simp)⟩

private def twoInNaturalQuotient :
    (doubledFiltration.N 0) ⧸
      (doubledFiltration.N 1).comap (doubledFiltration.N 0).subtype :=
  Submodule.Quotient.mk twoAtZero

private theorem twoInNaturalQuotient_ne_zero : twoInNaturalQuotient ≠ 0 := by
  intro h
  have hm : twoAtZero ∈
      (doubledFiltration.N 1).comap (doubledFiltration.N 0).subtype := by
    simpa [twoInNaturalQuotient] using h
  change (2 : ℤ) ∈ doubledFiltration.N 1 at hm
  rw [doubledFiltration_one] at hm
  simp at hm

private def twoInDegreeZero : (doubledFiltration.toIntFiltration).GradedPiece (0 : ℤ) :=
  (Ideal.Filtration.gradedPieceToIntEquiv doubledFiltration 0).symm twoInNaturalQuotient

private theorem twoInDegreeZero_ne_zero : twoInDegreeZero ≠ 0 := by
  intro h
  apply twoInNaturalQuotient_ne_zero
  simpa [twoInDegreeZero] using
    congrArg (Ideal.Filtration.gradedPieceToIntEquiv doubledFiltration 0) h

/-- The extension preserves the proper stage `2ℤ` at zero and its nonzero class of `2`. -/
private theorem doubledFiltration_nontrivial :
    (1 : ℤ) ∉ (doubledFiltration.toIntFiltration).N 0 ∧
      (doubledFiltration.toIntFiltration).N 0 ≠ ⊤ ∧
      twoInDegreeZero ≠ 0 ∧
      Nontrivial ((doubledFiltration.toIntFiltration).GradedPiece (0 : ℤ)) := by
  have hzero : (doubledFiltration.toIntFiltration).N 0 = doubledIntegers := by
    rw [Ideal.Filtration.toIntFiltration_N]
    exact doubledFiltration_zero
  have hone : (1 : ℤ) ∉ (doubledFiltration.toIntFiltration).N 0 := by
    rw [hzero]
    exact one_not_mem_doubledIntegers
  have hproper : (doubledFiltration.toIntFiltration).N 0 ≠ ⊤ := by
    intro htop
    apply hone
    rw [htop]
    trivial
  refine ⟨hone, hproper, twoInDegreeZero_ne_zero, ?_⟩
  exact ⟨⟨twoInDegreeZero, 0, twoInDegreeZero_ne_zero⟩⟩

/-- A natural filtration can have a proper stage at zero whose integer graded piece is
nontrivial. -/
theorem exists_proper_zero_stage_nontrivial_piece :
    ∃ F : (0 : Ideal ℤ).Filtration ℤ,
      (1 : ℤ) ∉ F.toIntFiltration.N 0 ∧
        F.toIntFiltration.N 0 ≠ ⊤ ∧
        Nontrivial (F.toIntFiltration.GradedPiece (0 : ℤ)) := by
  exact ⟨doubledFiltration, doubledFiltration_nontrivial.1,
    doubledFiltration_nontrivial.2.1, doubledFiltration_nontrivial.2.2.2⟩

private def negativeCutoffFiltration : (0 : Ideal ℤ).IntFiltration ℤ where
  N n := if n ≤ -2 then ⊤ else ⊥
  antitone := by
    intro a b hab
    by_cases hb : b ≤ -2
    · have ha : a ≤ -2 := hab.trans hb
      simp [ha, hb]
    · simp [hb]
  smul_le := by
    intro n
    simp

private def oneAtNegativeTwo : negativeCutoffFiltration.N (-2) :=
  ⟨1, by norm_num [negativeCutoffFiltration]⟩

private def oneInDegreeNegativeTwo : negativeCutoffFiltration.GradedPiece (-2) :=
  Submodule.Quotient.mk oneAtNegativeTwo

private theorem oneInDegreeNegativeTwo_ne_zero : oneInDegreeNegativeTwo ≠ 0 := by
  intro h
  have hm : oneAtNegativeTwo ∈
      (negativeCutoffFiltration.N ((-2 : ℤ) + 1)).comap
        (negativeCutoffFiltration.N (-2)).subtype := by
    change (Submodule.Quotient.mk oneAtNegativeTwo :
      (negativeCutoffFiltration.N (-2)) ⧸
        (negativeCutoffFiltration.N ((-2 : ℤ) + 1)).comap
          (negativeCutoffFiltration.N (-2)).subtype) = 0 at h
    simpa using h
  change (1 : ℤ) ∈ negativeCutoffFiltration.N ((-2 : ℤ) + 1) at hm
  norm_num [negativeCutoffFiltration] at hm

/-- A full integer filtration can have a nonzero negative piece, represented here by `1`. -/
example :
    negativeCutoffFiltration.N (-2) ≠ negativeCutoffFiltration.N (-1) ∧
      oneInDegreeNegativeTwo ≠ 0 ∧
      Nontrivial (negativeCutoffFiltration.GradedPiece (-2)) := by
  have hstages : negativeCutoffFiltration.N (-2) ≠ negativeCutoffFiltration.N (-1) := by
    intro h
    have hone : (1 : ℤ) ∈ negativeCutoffFiltration.N (-1) := by
      rw [← h]
      norm_num [negativeCutoffFiltration]
    norm_num [negativeCutoffFiltration] at hone
  refine ⟨hstages, oneInDegreeNegativeTwo_ne_zero, ?_⟩
  exact ⟨⟨oneInDegreeNegativeTwo, 0, oneInDegreeNegativeTwo_ne_zero⟩⟩

section ScalarRestriction

variable {R : Type u} [CommRing R] {I : Ideal R}
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

/-- Restricting a graded map intertwines degree-moving coefficient multiplication. -/
example (F : I.IntFiltration M) (H : I.IntFiltration N) (f : M →ₗ[R] N)
    (hf : ∀ n, F.N n ≤ (H.N n).comap f)
    (q : ℕ) (n : ℤ) (a : ↥(I ^ q)) (m : F.N n) :
    ((F.map H f hf).restrictScalars (reesAlgebra.powerQuotientSum I))
        ((DirectSum.of (reesAlgebra.powerQuotient I) q
          (Submodule.Quotient.mk a) : reesAlgebra.powerQuotientSum I) • F.single n m) =
      H.single (n + (q : ℤ))
        ⟨(a : R) • f (m : M),
          H.pow_smul_le q n
            (Submodule.smul_mem_smul a.property (hf n m.property))⟩ := by
  rw [map_smul, LinearMap.restrictScalars_apply, F.map_single,
    H.powerQuotientSum_of_mk_smul_single]

end ScalarRestriction

end IntegerFiltrations
