/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import CoherentModules.RingTheory.Noetherian
import GradedRings.ReesAlgebra.Map
public import GradedRings.ReesModule.Annihilator
import GradedRings.ReesModule.FiniteGeneration
import GradedRings.ReesModule.Lattice

/-!
# Noetherianity of Rees modules

A Rees module is Noetherian over its Rees algebra exactly when its initial stage is
Noetherian over the coefficient ring and its filtration is stable. Neither finite
generation of the ideal nor Noetherianity of the original ring is required.

Evaluation at zero gives the initial-stage conclusion by surjective semilinear
descent. Finite generation over the Rees algebra gives stability through the
bounded-degree span criterion. Conversely, each stage is a submodule of the
Noetherian initial stage, so stability gives a finitely generated Rees module.

For the reverse implication, coefficient reduction identifies the Rees algebra
modulo the annihilator of the Rees module with a Rees algebra over the quotient
by the annihilator of the initial stage. This effective coefficient ring and its
Rees algebra are Noetherian. The original-action finite-module criterion then
applies without choosing a quotient-coefficient action on the Rees module.

Every stagewise subfiltration of a filtration with Noetherian Rees module is stable.
Intersecting with a constant filtration gives a uniform Artin–Rees equality for each
submodule of the original ambient module, without finite generation of that submodule.

## References

- Mathlib's filtration, polynomial-module, ideal-quotient and Noetherian-ring APIs.
- Coherent Modules' `isNoetherian_of_surjective_semilinear`,
  `isNoetherianRing_quotient_annihilator` and
  `isNoetherian_iff_finite_and_isNoetherianRing_quotient_annihilator` provide
  semilinear descent, the effective coefficient ring and the original-action
  finite-module criterion.
-/

@[expose] public section

universe u v

namespace Ideal.Filtration

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
variable {I : Ideal R}

private lemma isNoetherian_N_zero_and_stable_of_isNoetherian_submodule
    (H : I.Filtration M) (h : IsNoetherian (reesAlgebra I) H.submodule) :
    IsNoetherian R (H.N 0) ∧ H.Stable := by
  let : IsNoetherian (reesAlgebra I) H.submodule := h
  constructor
  · exact isNoetherian_of_surjective_semilinear (H.evalRees 0) (H.evalRees_surjective 0)
  · exact H.stable_of_submodule_fg (Module.Finite.iff_fg.mp inferInstance)

private lemma submodule_fg_of_isNoetherian_N_zero_and_stable
    (H : I.Filtration M) (h0 : IsNoetherian R (H.N 0)) (hstable : H.Stable) :
    H.submodule.FG := by
  let : IsNoetherian R (H.N 0) := h0
  have hstage (n : ℕ) : (H.N n).FG :=
    Submodule.FG.of_le_of_isNoetherian (H.antitone (Nat.zero_le n))
  exact H.submodule_fg_of_stable hstage hstable

/-- A Rees module is Noetherian over its original Rees algebra exactly when its
initial stage is Noetherian over the original ring and its filtration is stable. -/
theorem isNoetherian_submodule_iff (H : I.Filtration M) :
    IsNoetherian (reesAlgebra I) H.submodule ↔
      IsNoetherian R (H.N 0) ∧ H.Stable := by
  constructor
  · exact H.isNoetherian_N_zero_and_stable_of_isNoetherian_submodule
  · rintro ⟨h0, hstable⟩
    let : IsNoetherian R (H.N 0) := h0
    have hfg := H.submodule_fg_of_isNoetherian_N_zero_and_stable h0 hstable
    let J : Ideal R := Module.annihilator R (H.N 0)
    let A := R ⧸ J
    let π : R →+* A := Ideal.Quotient.mk J
    let φ : reesAlgebra I →+* reesAlgebra (I.map π) :=
      reesAlgebra.map π le_rfl
    let : IsNoetherianRing A :=
      isNoetherianRing_quotient_annihilator (A := R) (H.N 0)
    let : IsNoetherianRing (reesAlgebra (I.map π)) := inferInstance
    have hsurj : Function.Surjective φ :=
      (reesAlgebra.map_surjective_iff π le_rfl).mpr
        ⟨Ideal.Quotient.mk_surjective, rfl⟩
    have hker : RingHom.ker φ =
        Module.annihilator (reesAlgebra I) H.submodule := by
      ext b
      rw [reesAlgebra.mem_ker_map_iff, H.mem_annihilator_submodule_iff]
      simp only [RingHom.mem_ker]
      exact forall_congr' fun n =>
        Ideal.Quotient.eq_zero_iff_mem (I := J) (a := (b : Polynomial R).coeff n)
    let e := RingHom.quotientKerEquivOfSurjective (f := φ) hsurj
    have hquot : IsNoetherianRing
        ((reesAlgebra I) ⧸ Module.annihilator (reesAlgebra I) H.submodule) := by
      rw [← hker]
      exact isNoetherianRing_of_surjective (reesAlgebra (I.map π)) _
        e.symm.toRingHom e.symm.surjective
    exact (isNoetherian_iff_finite_and_isNoetherianRing_quotient_annihilator
      (R := reesAlgebra I) (M := H.submodule)).mpr
        ⟨Module.Finite.iff_fg.mpr hfg, hquot⟩

/-- Every stagewise subfiltration of a filtration with Noetherian Rees module is stable. -/
theorem stable_of_le_of_isNoetherian_submodule (H K : I.Filtration M)
    [IsNoetherian (reesAlgebra I) H.submodule]
    (hKH : ∀ n : ℕ, K.N n ≤ H.N n) : K.Stable := by
  let : IsNoetherian (reesAlgebra I) K.submodule :=
    isNoetherian_of_le ((submodule_le_submodule_iff K H).mpr hKH)
  exact (K.isNoetherian_submodule_iff.mp inferInstance).2

/-- A filtration with Noetherian Rees module satisfies a uniform Artin–Rees equality
for each submodule of its original ambient module. The bound may depend on the submodule. -/
theorem exists_inf_eq_pow_smul_of_isNoetherian_submodule (H : I.Filtration M)
    [IsNoetherian (reesAlgebra I) H.submodule] (N : Submodule R M) :
    ∃ c : ℕ, ∀ n : ℕ, H.N (n + c) ⊓ N = (I ^ n) • (H.N c ⊓ N) := by
  have hstable : (H ⊓ I.trivialFiltration N).Stable := by
    apply H.stable_of_le_of_isNoetherian_submodule
    intro n
    simpa only [inf_N, Pi.inf_apply, Ideal.trivialFiltration_N] using
      (inf_le_left : H.N n ⊓ N ≤ H.N n)
  obtain ⟨c, hc⟩ := hstable.exists_pow_smul_eq
  refine ⟨c, fun n => ?_⟩
  simpa only [inf_N, Pi.inf_apply, Ideal.trivialFiltration_N, Nat.add_comm] using hc n

end Ideal.Filtration
