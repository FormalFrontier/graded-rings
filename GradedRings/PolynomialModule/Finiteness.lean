/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GradedRings.PolynomialModule.Basic
public import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Algebra.Polynomial.Coeff

/-!
# Finite generation of polynomial modules

Extension to polynomial scalars preserves and reflects finite generation over a
possibly noncommutative semiring. A finite generating set for the coefficient
module gives generators in degree zero, and multiplication by monomials generates
all other degrees. Conversely, taking the constant coefficient is a surjective
semilinear map along `Polynomial.constantCoeff`.

The polynomial action is the one on `PolynomialModule.Extension`: constants act
by the given coefficient action, and the variable acts by successor shift.
-/

@[expose] public section

universe u v

open Polynomial

namespace PolynomialModule.Extension

variable {R : Type u} {M : Type v} [Semiring R] [AddCommMonoid M] [Module R M]

/-- Extension to polynomial scalars is finitely generated exactly when the original
coefficient module is finitely generated. Neither commutativity of the semiring nor
additive inverses in the module are required. -/
theorem finite_iff : Module.Finite R[X] (PolynomialModule.Extension R M) ↔
    Module.Finite R M := by
  constructor
  · intro h
    let := h
    let f : PolynomialModule.Extension R M →ₛₗ[Polynomial.constantCoeff] M :=
      { toFun := fun q => q.coeff 0
        map_add' := fun q q' => by simp
        map_smul' := fun p q => by simpa using coeff_smul p q 0 }
    apply Module.Finite.of_surjective f
    intro m
    refine ⟨single R 0 m, ?_⟩
    change (single R 0 m).coeff 0 = m
    simp
  · intro h
    classical
    obtain ⟨s, hs⟩ := h.fg_top
    let T : Finset (PolynomialModule.Extension R M) := s.image (single R 0)
    let P : Submodule R[X] (PolynomialModule.Extension R M) :=
      Submodule.span R[X] (T : Set (PolynomialModule.Extension R M))
    have hsingle0 (m : M) : single R 0 m ∈ P := by
      have hm : m ∈ Submodule.span R (s : Set M) := by
        rw [hs]
        trivial
      refine Submodule.span_induction
        (p := fun x _ => single R 0 x ∈ P) ?_ ?_ ?_ ?_ hm
      · intro x hx
        apply Submodule.subset_span
        exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
      · simpa only [single_zero] using P.zero_mem
      · intro x y _ _ hx hy
        simpa only [single_add] using P.add_mem hx hy
      · intro r x _ hx
        simpa only [single_smul, C_smul] using P.smul_mem (C r) hx
    have hP : P = ⊤ := by
      apply top_unique
      intro q _
      refine induction_linear q P.zero_mem (fun x y hx hy => P.add_mem hx hy) ?_
      intro n m
      simpa only [monomial_smul_single, add_zero, one_smul] using
        P.smul_mem (monomial n (1 : R)) (hsingle0 m)
    exact Module.Finite.of_fg_top ⟨T, hP⟩

/-- Polynomial extension preserves finite generation of the coefficient module. -/
instance [Module.Finite R M] : Module.Finite R[X] (PolynomialModule.Extension R M) :=
  finite_iff.mpr inferInstance

end PolynomialModule.Extension
