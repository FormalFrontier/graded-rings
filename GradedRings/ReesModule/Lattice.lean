/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# Lattice compatibility of Rees submodules

The Rees submodule of an ideal filtration reflects inclusion of all stages and preserves
binary suprema and arbitrary indexed suprema and infima. Finite generation of the Rees
submodules in a finite family passes to the Rees submodule of their supremum.

The filtration and Rees-submodule constructions, with their stage and coefficient
characterizations, are those of `Mathlib.RingTheory.Filtration`. Binary infimum compatibility
is already given by `Ideal.Filtration.inf_submodule`. Finite-supremum finite generation is
supplied by `Submodule.fg_iSup`; the finite-generation hypotheses are over `reesAlgebra I`,
not hypotheses on the stages over the base ring.
-/

@[expose] public section

universe u v w

namespace Ideal.Filtration

variable {R : Type u} [CommRing R] {I : Ideal R}
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Inclusion of Rees submodules is equivalent to inclusion at every filtration stage. -/
theorem submodule_le_submodule_iff (H K : I.Filtration M) :
    H.submodule ≤ K.submodule ↔ ∀ n : ℕ, H.N n ≤ K.N n := by
  constructor
  · intro h n m hm
    have hs : PolynomialModule.single R n m ∈ H.submodule := by
      apply (mem_submodule H _).2
      intro i
      by_cases hi : n = i
      · subst i
        simpa only [PolynomialModule.coeff_single, Finsupp.single_eq_same] using hm
      · simpa only [PolynomialModule.coeff_single, Finsupp.single_eq_of_ne' hi] using
          (H.N i).zero_mem
    have hk := (mem_submodule K _).1 (h hs) n
    simpa only [PolynomialModule.coeff_single, Finsupp.single_eq_same] using hk
  · intro h p hp
    exact (mem_submodule K p).2 fun n => h n ((mem_submodule H p).1 hp n)

private theorem single_mem_submodule (H : I.Filtration M) {n : ℕ} {m : M}
    (hm : m ∈ H.N n) : PolynomialModule.single R n m ∈ H.submodule := by
  rw [← H.submodule_span_single]
  exact Submodule.subset_span (Set.mem_iUnion.mpr ⟨n, m, hm, rfl⟩)

/-- The Rees submodule of a binary supremum is the supremum of the Rees submodules. -/
theorem sup_submodule (H K : I.Filtration M) :
    (H ⊔ K).submodule = H.submodule ⊔ K.submodule := by
  apply le_antisymm
  · rw [← (H ⊔ K).submodule_span_single]
    refine Submodule.span_le.mpr ?_
    intro p hp
    rcases Set.mem_iUnion.mp hp with ⟨n, m, hm, rfl⟩
    rw [sup_N] at hm
    rcases Submodule.mem_sup.mp hm with ⟨a, ha, b, hb, rfl⟩
    rw [PolynomialModule.single_add]
    exact Submodule.add_mem_sup (single_mem_submodule H ha) (single_mem_submodule K hb)
  · refine sup_le ?_ ?_
    · apply (submodule_le_submodule_iff H (H ⊔ K)).2
      intro n
      rw [sup_N]
      exact le_sup_left
    · apply (submodule_le_submodule_iff K (H ⊔ K)).2
      intro n
      rw [sup_N]
      exact le_sup_right

/-- The Rees submodule of an indexed infimum is the infimum of the Rees submodules. -/
theorem iInf_submodule {ι : Sort w} (f : ι → I.Filtration M) :
    (iInf f).submodule = ⨅ i, (f i).submodule := by
  apply Submodule.ext
  intro p
  simp only [mem_submodule, iInf_N, iInf_apply, Submodule.mem_iInf]
  exact ⟨fun h i n => h n i, fun h n i => h i n⟩

/-- The Rees submodule of an indexed supremum is the supremum of the Rees submodules. -/
theorem iSup_submodule {ι : Sort w} (f : ι → I.Filtration M) :
    (iSup f).submodule = ⨆ i, (f i).submodule := by
  apply le_antisymm
  · rw [← (iSup f).submodule_span_single]
    refine Submodule.span_le.mpr ?_
    intro p hp
    rcases Set.mem_iUnion.mp hp with ⟨n, m, hm, rfl⟩
    rw [iSup_N, iSup_apply] at hm
    exact Submodule.iSup_induction (fun i => (f i).N n)
      (motive := fun m => PolynomialModule.single R n m ∈ ⨆ i, (f i).submodule) hm
      (fun i m hm => Submodule.mem_iSup_of_mem i (single_mem_submodule (f i) hm))
      (by rw [PolynomialModule.single_zero]; exact Submodule.zero_mem _)
      (fun a b ha hb => by
        rw [PolynomialModule.single_add]
        exact Submodule.add_mem _ ha hb)
  · refine iSup_le fun i => ?_
    apply (submodule_le_submodule_iff (f i) (iSup f)).2
    intro n
    rw [iSup_N, iSup_apply]
    exact le_iSup (fun i => (f i).N n) i

/-- A finite supremum of filtrations with finitely generated Rees submodules has a
finitely generated Rees submodule. -/
theorem iSup_submodule_fg {ι : Sort w} [Finite ι] (f : ι → I.Filtration M)
    (h : ∀ i, (f i).submodule.FG) : (iSup f).submodule.FG := by
  rw [iSup_submodule]
  exact Submodule.fg_iSup (fun i => (f i).submodule) h

end Ideal.Filtration
