/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GradedRings.ReesModule
public import GradedRings.ReesModule.FiniteGeneration
import Mathlib.RingTheory.Finiteness.Ideal

/-!
# Finite homogeneous generators and stability of Rees modules

A finitely generated Rees module admits finitely many original-module elements
`x i ∈ H.N (w i)` whose polynomial singles in every degree from zero through
`w i` span the Rees module. The elements are chosen from a finite subset of the
homogeneous singles spanning the Rees module. Antitonicity then supplies all
lower-degree singles without enlarging the submodule.

The homogeneous description requires no finiteness of the ideal, the individual
stages, or the ambient module. The family may be empty, and the initial stage need
not be the whole module. Finite generation is equivalent to the existence of one
finite weighted family describing every natural stage as a sum of ideal-power
multiples of its cyclic submodules over the original ring. The bounded-degree
criterion in `GradedRings.ReesModule` gives eventual stability without any of these
finiteness hypotheses.

If the ideal is finitely generated, each stage of a finitely generated Rees module
is finitely generated over the original ring. In this case, finite generation of
the Rees module is equivalent to finite generation of every stage together with
eventual stability.

## References

This uses Andrew Yang's filtration and polynomial-module formalizations in
Mathlib, in particular `Ideal.Filtration.submodule_span_single`, together with
Johan Commelin's finite-span extraction API in `Mathlib.RingTheory.Finiteness.Defs`.
The all-lower-degree form of the generating family is the one used by the
weighted-normal-form results in `GradedRings.ReesModule.FiniteGeneration`.
-/

@[expose] public section

universe u v

namespace Ideal.Filtration

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
variable {I : Ideal R}

open PolynomialModule

/-- A finitely generated Rees module has a finite family of homogeneous lifts
whose singles in all degrees up to their weights generate the same Rees module.

The lifts lie in their indicated filtration stages. No finite generation of the
ideal, the stages, or the ambient module is required. -/
theorem exists_fin_generating_family_single_le_of_submodule_fg
    (H : I.Filtration M) (hfg : H.submodule.FG) :
    ∃ (m : ℕ) (w : Fin m → ℕ) (x : Fin m → M),
      (∀ i, x i ∈ H.N (w i)) ∧
      H.submodule = Submodule.span (reesAlgebra I)
        (Set.range (fun p : Σ i : Fin m, Fin (w i + 1) =>
          PolynomialModule.single R (p.2 : ℕ) (x p.1))) := by
  classical
  have hfg' : (Submodule.span (reesAlgebra I)
      (⋃ q, single R q '' (H.N q : Set M))).FG := by
    rw [H.submodule_span_single]
    exact hfg
  obtain ⟨s, hs, hspan⟩ :=
    (Submodule.fg_span_iff_fg_span_finset_subset _).mp hfg'
  obtain ⟨m, g, hg⟩ := s.finite_toSet.fin_embedding
  have hsingle (i : Fin m) :
      ∃ (q : ℕ) (x : M), x ∈ H.N q ∧ single R q x = g i := by
    have hi : g i ∈ (s : Set (PolynomialModule R M)) := by
      rw [← hg]
      exact Set.mem_range_self i
    obtain ⟨q, x, hx, hsingle⟩ := Set.mem_iUnion.mp (hs hi)
    exact ⟨q, x, hx, hsingle⟩
  choose w x hx hsingle using hsingle
  refine ⟨m, w, x, hx, le_antisymm ?_ ?_⟩
  · have hgen : H.submodule = Submodule.span (reesAlgebra I) (Set.range g) := by
      rw [hg, ← hspan, H.submodule_span_single]
    rw [hgen]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    rw [← hsingle i]
    apply Submodule.subset_span
    exact ⟨⟨i, ⟨w i, Nat.lt_succ_self _⟩⟩, rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨i, q⟩, rfl⟩
    apply (H.mem_submodule _).mpr
    intro j
    rw [coeff_single, Finsupp.single_apply]
    split_ifs with hq
    · subst j
      exact H.antitone (Nat.le_of_lt_succ q.isLt) (hx i)
    · exact (H.N j).zero_mem

/-- The Rees submodule is finitely generated exactly when every natural stage
has one finite weighted normal form over the original ring.

The weights and elements are shared by all stages. No finite generation of the
ideal, the individual stages, or the ambient module is assumed. -/
theorem submodule_fg_iff_exists_weighted_normal_form (H : I.Filtration M) :
    H.submodule.FG ↔
      ∃ (m : ℕ) (w : Fin m → ℕ) (x : Fin m → M),
        ∀ n : ℕ,
          H.N n = ⨆ i : Fin m,
            I ^ (n - w i) • Submodule.span R ({x i} : Set M) := by
  constructor
  · intro hfg
    obtain ⟨m, w, x, _, hspan⟩ :=
      H.exists_fin_generating_family_single_le_of_submodule_fg hfg
    exact ⟨m, w, x,
      H.weighted_normal_form_of_submodule_eq_span_range_single w x hspan⟩
  · rintro ⟨m, w, x, hnormal⟩
    exact H.submodule_fg_of_weighted_normal_form w x hnormal

/-- If the ideal and the Rees submodule are finitely generated, every filtration
stage is finitely generated over the original ring.

The finite weighted normal form expresses each stage as a finite supremum of
finitely generated ideal powers times cyclic submodules. -/
theorem fg_of_submodule_fg
    (H : I.Filtration M) (hI : I.FG) (hfg : H.submodule.FG) (n : ℕ) :
    (H.N n).FG := by
  obtain ⟨m, w, x, hnormal⟩ :=
    (H.submodule_fg_iff_exists_weighted_normal_form).mp hfg
  rw [hnormal n]
  exact Submodule.fg_iSup _ fun i =>
    Submodule.FG.smul (Ideal.FG.pow hI) (Submodule.fg_span_singleton (x i))

/-- For a finitely generated ideal, the Rees submodule is finitely generated
exactly when every original-ring stage is finitely generated and the filtration
is eventually stable.

The stability implication itself requires no finite generation of the ideal. -/
theorem submodule_fg_iff_fg_stable (H : I.Filtration M) (hI : I.FG) :
    H.submodule.FG ↔ (∀ n : ℕ, (H.N n).FG) ∧ H.Stable := by
  constructor
  · intro hfg
    exact ⟨H.fg_of_submodule_fg hI hfg, H.stable_of_submodule_fg hfg⟩
  · rintro ⟨hstage, hstable⟩
    exact H.submodule_fg_of_stable hstage hstable

end Ideal.Filtration
