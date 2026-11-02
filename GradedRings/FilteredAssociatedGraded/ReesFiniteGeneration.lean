/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GradedRings.FilteredAssociatedGraded.FiniteGeneration
public import GradedRings.FilteredAssociatedGraded.ReesProjection

/-!
# Weighted cutoffs for natural tails of integer filtrations

An all-integer weighted description of the stages converts to a natural-tail
weighted description at any common lower cutoff `k` for the integer weights.
The relative weights are `(d i - k).toNat`, and subtraction in the natural-tail
ideal powers is natural subtraction. Every stage at or below `k` equals the
stage at `k`; the common stage need not be the whole module.

These algebraic conversions take the weighted description as an explicit input.
The indexing family may be infinite or empty, and its integer weights may be
negative. No finiteness, completeness, separation or exhaustivity is required.

Over precomplete coefficient rings, a separated integer filtration has finite
associated graded exactly when some finitely generated natural tail has a
surjective prescribed Rees projection. This criterion does not require
exhaustivity or finite generation of the ideal or the individual stages.

## References

* K. Fujiwara and F. Kato, *Foundations of Rigid Geometry I*,
  arXiv:1308.4734v5, for the filtered-generation setting.
* Andrew Yang's ideal filtrations in Mathlib, and Mathlib's integer truncation
  and complete-lattice API.
-/

@[expose] public section

universe u v w

namespace Ideal.IntFiltration

variable {R : Type u} [CommRing R] {I : Ideal R}
variable {M : Type v} [AddCommGroup M] [Module R M]
variable (F : I.IntFiltration M)

/-- A supplied integer weighted stage formula becomes a natural-tail formula at
any common lower cutoff, using the relative natural weights `(d i - k).toNat`.
The family need not be finite or nonempty. -/
theorem natTail_N_eq_iSup_pow_smul_span_singleton
    {ι : Type w} (d : ι → ℤ) (x : ι → M)
    (hNF : ∀ n : ℤ, F.N n =
      ⨆ i : ι, I ^ ((n - d i).toNat) •
        Submodule.span R ({x i} : Set M))
    (k : ℤ) (hk : ∀ i : ι, k ≤ d i) (q : ℕ) :
    (F.natTail k).N q =
      ⨆ i : ι, I ^ (q - (d i - k).toNat) •
        Submodule.span R ({x i} : Set M) := by
  rw [F.natTail_N, hNF]
  apply iSup_congr
  intro i
  have hki : k ≤ d i := hk i
  have hexp : (k + (q : ℤ) - d i).toNat = q - (d i - k).toNat := by
    omega
  rw [hexp]

/-- A supplied integer weighted stage formula is constant at and below any
common lower cutoff for its weights, without requiring a top stage. -/
theorem eq_at_cutoff_of_eq_iSup_pow_smul_span_singleton
    {ι : Type w} (d : ι → ℤ) (x : ι → M)
    (hNF : ∀ n : ℤ, F.N n =
      ⨆ i : ι, I ^ ((n - d i).toNat) •
        Submodule.span R ({x i} : Set M))
    (k : ℤ) (hk : ∀ i : ι, k ≤ d i)
    (n : ℤ) (hn : n ≤ k) :
    F.N n = F.N k := by
  rw [hNF n, hNF k]
  apply iSup_congr
  intro i
  have hki : k ≤ d i := hk i
  have hnexp : (n - d i).toNat = 0 := by omega
  have hkexp : (k - d i).toNat = 0 := by omega
  rw [hnexp, hkexp]

local notation "B" => reesAlgebra I
local notation "J" => I.map (algebraMap R B)
local notation "C" => B ⧸ J

/-- Over precomplete coefficients, a separated integer filtration with finite associated
graded has a finitely generated natural tail whose prescribed projection is surjective.

The proof reuses the weighted-generation argument of Fujiwara–Kato,
*Foundations of Rigid Geometry I*, Proposition 0.7.5.2. It needs neither
exhaustivity nor finite generation of the ideal or the individual stages. -/
theorem exists_fg_natTail_of_finite_associatedGraded
    [IsPrecomplete I R] [Module.Finite C F.AssociatedGraded]
    (hsep : (⨅ n : ℤ, F.N n) = ⊥) :
    ∃ k : ℤ, ((F.natTail k).submodule).FG ∧
      Function.Surjective (F.shiftedReesProjection k) := by
  classical
  obtain ⟨m, d, x, _, hNF⟩ :=
    F.exists_eq_iSup_pow_smul_span_singleton_of_finite_associatedGraded hsep
  obtain ⟨k, hk⟩ := (Set.finite_range d).bddBelow
  have hkd : ∀ i : Fin m, k ≤ d i := fun i => hk ⟨i, rfl⟩
  refine ⟨k, ?_, ?_⟩
  · exact (F.natTail k).submodule_fg_of_weighted_normal_form
      (fun i => (d i - k).toNat) x
      (fun q => F.natTail_N_eq_iSup_pow_smul_span_singleton d x hNF k hkd q)
  · apply (F.shiftedReesProjection_surjective_iff k).2
    intro n hn
    apply (F.subsingleton_gradedPiece_iff n).2
    exact (F.eq_at_cutoff_of_eq_iSup_pow_smul_span_singleton d x hNF k hkd n
      (le_of_lt hn)).trans
        (F.eq_at_cutoff_of_eq_iSup_pow_smul_span_singleton d x hNF k hkd (n + 1)
          (by omega)).symm

/-- Over precomplete coefficients, the associated graded of a separated integer filtration
is finite exactly when a finitely generated natural tail projects surjectively onto it. -/
theorem finite_associatedGraded_iff_exists_fg_natTail
    [IsPrecomplete I R] (hsep : (⨅ n : ℤ, F.N n) = ⊥) :
    Module.Finite C F.AssociatedGraded ↔
      ∃ k : ℤ, ((F.natTail k).submodule).FG ∧
        Function.Surjective (F.shiftedReesProjection k) := by
  constructor
  · intro hfinite
    let : Module.Finite C F.AssociatedGraded := hfinite
    exact F.exists_fg_natTail_of_finite_associatedGraded hsep
  · rintro ⟨k, hfg, hsurj⟩
    exact F.finite_of_fg_natTail k hfg
      ((F.shiftedReesProjection_surjective_iff k).1 hsurj)

end Ideal.IntFiltration
