/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GradedRings.FilteredAssociatedGraded.Adic
public import GradedRings.FilteredAssociatedGraded.FiniteGeneration
public import GradedRings.FilteredAssociatedGraded.ReesProjection
public import GradedRings.ReesModule.FiniteGeneration

/-!
# Natural Rees modules and associated-graded finite generation

For a separated natural ideal filtration over precomplete coefficients, finite generation
of its Rees submodule is equivalent to finiteness of the associated graded of its integer
extension over the quotient Rees ring. No exhaustivity or finite-generation assumption on
the ideal, stages, or ambient module is imposed.
-/

@[expose] public section

universe u v

namespace Ideal.Filtration

variable {R : Type u} [CommRing R] {I : Ideal R}
variable {M : Type v} [AddCommGroup M] [Module R M]
variable (H : I.Filtration M)

/-- The natural tail at zero of the integer extension is the original filtration. -/
@[simp] theorem toIntFiltration_natTail_zero :
    H.toIntFiltration.natTail 0 = H := by
  ext q x
  rw [Ideal.IntFiltration.natTail_N, zero_add, toIntFiltration_N_nat]

/-- The natural and integer extensions have the same intersection of stages. -/
theorem iInf_toIntFiltration_N :
    (⨅ n : ℤ, H.toIntFiltration.N n) = ⨅ n : ℕ, H.N n := by
  apply le_antisymm
  · refine le_iInf fun q => ?_
    simpa only [toIntFiltration_N_nat] using
      (iInf_le (fun n : ℤ => H.toIntFiltration.N n) (q : ℤ))
  · refine le_iInf fun n => ?_
    simpa only [toIntFiltration_N] using
      (iInf_le (fun q : ℕ => H.N q) n.toNat)

/-- The integer extension has no nonzero graded piece in a negative degree. -/
theorem subsingleton_toIntFiltration_gradedPiece_of_neg (n : ℤ) (hn : n < 0) :
    Subsingleton (H.toIntFiltration.GradedPiece n) := by
  apply (Ideal.IntFiltration.subsingleton_gradedPiece_iff H.toIntFiltration n).2
  rw [toIntFiltration_N_of_nonpos H n (le_of_lt hn),
    toIntFiltration_N_of_nonpos H (n + 1) (Int.add_one_le_iff.mpr hn)]

universe uι

private theorem nat_weighted_normal_form_of_int_weighted_normal_form
    {ι : Sort uι} (w : ι → ℤ) (x : ι → M)
    (hform : ∀ n : ℤ, H.toIntFiltration.N n =
      ⨆ i : ι, I ^ (n - w i).toNat • Submodule.span R ({x i} : Set M)) :
    ∀ n : ℕ, H.N n =
      ⨆ i : ι, I ^ (n - (w i).toNat) • Submodule.span R ({x i} : Set M) := by
  have hx (i : ι) : x i ∈ H.N (w i).toNat := by
    rw [← H.toIntFiltration_N (w i), hform (w i)]
    exact (le_iSup (fun j : ι =>
      I ^ (w i - w j).toNat • Submodule.span R ({x j} : Set M)) i)
      (by simp)
  intro n
  apply le_antisymm
  · rw [← H.toIntFiltration_N_nat n, hform (n : ℤ)]
    apply iSup_mono
    intro i
    have hexp : n - (w i).toNat ≤ ((n : ℤ) - w i).toNat := by omega
    exact Submodule.smul_mono (Ideal.pow_le_pow_right hexp) le_rfl
  · apply iSup_le
    intro i
    have hspan : Submodule.span R ({x i} : Set M) ≤ H.N (w i).toNat :=
      (Submodule.span_singleton_le_iff_mem (x i) (H.N (w i).toNat)).mpr (hx i)
    calc
      I ^ (n - (w i).toNat) • Submodule.span R ({x i} : Set M) ≤
          I ^ (n - (w i).toNat) • H.N (w i).toNat :=
        Submodule.smul_mono le_rfl hspan
      _ ≤ H.N ((n - (w i).toNat) + (w i).toNat) :=
        H.pow_smul_le (n - (w i).toNat) (w i).toNat
      _ ≤ H.N n := H.antitone (by omega)

/-- A separated natural filtration has a finitely generated Rees submodule exactly when
its integer-extension associated graded is finite over the quotient Rees ring, assuming
precompleteness of the coefficient ring. -/
theorem submodule_fg_iff_finite_associatedGraded [IsPrecomplete I R]
    (hsep : (⨅ n : ℕ, H.N n) = ⊥) :
    H.submodule.FG ↔
      Module.Finite ((reesAlgebra I) ⧸ I.map (algebraMap R (reesAlgebra I)))
        H.toIntFiltration.AssociatedGraded := by
  constructor
  · intro hfg
    apply H.toIntFiltration.finite_of_fg_natTail 0
    · simpa only [H.toIntFiltration_natTail_zero] using hfg
    · intro n hn
      exact H.subsingleton_toIntFiltration_gradedPiece_of_neg n hn
  · intro hfinite
    let := hfinite
    obtain ⟨k, w, x, _, hform⟩ :=
      H.toIntFiltration.exists_eq_iSup_pow_smul_span_singleton_of_finite_associatedGraded
        (by rw [H.iInf_toIntFiltration_N, hsep])
    exact H.submodule_fg_of_weighted_normal_form (fun i => (w i).toNat) x
      (H.nat_weighted_normal_form_of_int_weighted_normal_form w x hform)

end Ideal.Filtration
