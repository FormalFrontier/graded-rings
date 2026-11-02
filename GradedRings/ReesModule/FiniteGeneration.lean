/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Filtration

/-!
# Finite generation of Rees modules from bounded initial stages

A filtration that is stable from a given degree has finitely generated Rees module
provided its stages through that degree are finitely generated over the original ring.
No finite generation of the ideal, the later stages, or the ambient module is required.

The proof uses the bounded-degree span criterion for a stable filtration. Each initial
stage is mapped to polynomial singles over the original ring; extending scalars in the
span then gives a finitely generated submodule over the Rees algebra. This uses the
constant scalar map, without requiring that map to be surjective.

## References

This generalizes the reverse implication of Andrew Yang's
`Ideal.Filtration.submodule_fg_iff_stable` in Mathlib's
[filtration theory](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/RingTheory/Filtration.lean).
The bounded-degree span criterion and the finite supremum argument are due to that
formalization. `Ideal.Filtration.submodule_fg_of_stable` recovers its reverse implication
under the original all-stage finite-generation hypothesis.
-/

@[expose] public section

universe u v

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

end Ideal.Filtration
