/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Basic.Finite.Sigma
public import Mathlib.RingTheory.Filtration

/-!
# Generators and finite generation of Rees modules

For a filtration with a weighted normal form, its Rees module is spanned by the
polynomial singles of each lift in every degree from zero through its weight. The
index type is arbitrary. If it is finite, the Rees module is finitely generated,
without any finite-generation hypothesis on the ideal or the individual stages.

A filtration that is stable from a given degree has finitely generated Rees module
provided its stages through that degree are finitely generated over the original ring.
No finite generation of the ideal, the later stages, or the ambient module is required.

The proof uses the bounded-degree span criterion for a stable filtration. Each initial
stage is mapped to polynomial singles over the original ring; extending scalars in the
span then gives a finitely generated submodule over the Rees algebra. This uses the
constant scalar map, without requiring that map to be surjective.

## References

The bounded-initial-stage criterion generalizes the reverse implication of Andrew Yang's
`Ideal.Filtration.submodule_fg_iff_stable` in Mathlib's
[filtration theory](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/RingTheory/Filtration.lean).
The bounded-degree span criterion and the finite supremum argument are due to that
formalization. `Ideal.Filtration.submodule_fg_of_stable` recovers its reverse implication
under the original all-stage finite-generation hypothesis.
-/

@[expose] public section

universe u v uι

namespace Ideal.Filtration

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
variable {I : Ideal R}

open PolynomialModule

private theorem fg_span_single (q : ℕ) {N : Submodule R M} (hN : N.FG) :
    (Submodule.span (reesAlgebra I) (single R q '' (N : Set M))).FG := by
  -- The map here is R-linear; scalar extension is performed only by `FG.span`.
  have hmap : (N.map (lsingle R q)).FG := hN.map (lsingle R q)
  have himage : ((N.map (lsingle R q) : Submodule R (PolynomialModule R M)) :
      Set (PolynomialModule R M)) = single R q '' (N : Set M) := rfl
  simpa only [himage] using (Submodule.FG.span (A := reesAlgebra I) hmap)

/-- If a filtration is stable from degree `q0` and its stages through `q0` are
finitely generated over the original ring, its Rees module is finitely generated.

This strengthens the reverse implication of Mathlib's
`Ideal.Filtration.submodule_fg_iff_stable`: no finite generation of stages above the
chosen stability threshold is needed. -/
theorem submodule_fg_of_stable_ge (G : I.Filtration M) (q0 : ℕ)
    (hstable : ∀ q, q0 ≤ q → I • G.N q = G.N (q + 1))
    (hinit : ∀ q, q ≤ q0 → (G.N q).FG) : G.submodule.FG := by
  classical
  rw [(G.submodule_eq_span_le_iff_stable_ge q0).mpr hstable]
  simp_rw [Submodule.span_iUnion₂, ← Finset.mem_range_succ_iff, iSup_subtype']
  apply Submodule.fg_iSup
  rintro ⟨q, hq⟩
  exact fg_span_single q (hinit q (Finset.mem_range_succ_iff.mp hq))

/-- A stable filtration with finitely generated stages has finitely generated Rees module.

This recovers the reverse implication of Mathlib's
`Ideal.Filtration.submodule_fg_iff_stable` from the bounded initial-stage criterion. -/
theorem submodule_fg_of_stable (G : I.Filtration M) (hstage : ∀ q, (G.N q).FG)
    (hstable : G.Stable) : G.submodule.FG := by
  obtain ⟨q0, hq0⟩ := hstable
  exact G.submodule_fg_of_stable_ge q0 hq0 (fun q _ => hstage q)

/-- A weighted normal form for every stage expresses the Rees module as the span of
singles of each lift in all degrees from zero through its weight.

The index type is arbitrary; no finiteness of the index type or the ideal is required. -/
theorem submodule_eq_span_range_single_of_weighted_normal_form
    {ι : Type uι} (H : I.Filtration M) (w : ι → ℕ) (x : ι → M)
    (hH : ∀ n : ℕ,
      H.N n = ⨆ i : ι, I ^ (n - w i) • Submodule.span R ({x i} : Set M)) :
    H.submodule = Submodule.span (reesAlgebra I)
      (Set.range (fun p : Σ i : ι, Fin (w i + 1) =>
        PolynomialModule.single R (p.2 : ℕ) (x p.1))) := by
  classical
  let S : Submodule (reesAlgebra I) (PolynomialModule R M) :=
    Submodule.span (reesAlgebra I)
      (Set.range (fun p : Σ i : ι, Fin (w i + 1) =>
        single R (p.2 : ℕ) (x p.1)))
  change H.submodule = S
  apply le_antisymm
  · rw [← H.submodule_span_single]
    apply Submodule.span_le.mpr
    intro f hf
    rcases Set.mem_iUnion.mp hf with ⟨n, hn⟩
    rcases hn with ⟨m, hm, rfl⟩
    rw [hH n] at hm
    refine Submodule.iSup_induction
      (fun i : ι => I ^ (n - w i) • Submodule.span R ({x i} : Set M))
      (motive := fun m => single R n m ∈ S) hm ?_ ?_ ?_
    · intro i m hm
      obtain ⟨a, ha, rfl⟩ := Submodule.mem_smul_span_singleton.mp hm
      let q := min n (w i)
      have hq : q < w i + 1 := Nat.lt_succ_of_le (Nat.min_le_right _ _)
      have hdeg : n - w i + q = n := by
        dsimp [q]
        rcases le_total n (w i) with hn | hn
        · rw [min_eq_left hn, Nat.sub_eq_zero_of_le hn, zero_add]
        · rw [min_eq_right hn, Nat.sub_add_cancel hn]
      let b : reesAlgebra I :=
        ⟨Polynomial.monomial (n - w i) a, reesAlgebra.monomial_mem.mpr ha⟩
      have hg : single R q (x i) ∈ S := by
        apply Submodule.subset_span
        exact ⟨⟨i, ⟨q, hq⟩⟩, rfl⟩
      simpa only [Subalgebra.smul_def, b, monomial_smul_single, hdeg] using
        S.smul_mem b hg
    · simpa only [single_zero] using S.zero_mem
    · intro m m' hm hm'
      simpa only [single_add] using S.add_mem hm hm'
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨i, q⟩, rfl⟩
    have hq : (q : ℕ) ≤ w i := Nat.le_of_lt_succ q.isLt
    have hx : x i ∈ H.N (q : ℕ) := by
      rw [hH (q : ℕ)]
      apply (le_iSup (fun j : ι =>
        I ^ ((q : ℕ) - w j) • Submodule.span R ({x j} : Set M)) i)
      apply Submodule.mem_smul_span_singleton.mpr
      refine ⟨1, ?_, one_smul R (x i)⟩
      simp [Nat.sub_eq_zero_of_le hq]
    apply (H.mem_submodule _).mpr
    intro j
    by_cases hj : (q : ℕ) = j
    · subst j
      simpa only [coeff_single, Finsupp.single_eq_same] using hx
    · simp [coeff_single, hj]

/-- A weighted normal form indexed by a finite type gives a finitely generated Rees module.

No separate finite-generation assumption on the ideal, the stages, or the ambient module
is required. -/
theorem submodule_fg_of_weighted_normal_form
    {ι : Type uι} [Finite ι] (H : I.Filtration M) (w : ι → ℕ) (x : ι → M)
    (hH : ∀ n : ℕ,
      H.N n = ⨆ i : ι, I ^ (n - w i) • Submodule.span R ({x i} : Set M)) :
    H.submodule.FG := by
  rw [H.submodule_eq_span_range_single_of_weighted_normal_form w x hH]
  exact Submodule.fg_span (Set.finite_range _)

end Ideal.Filtration
