/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GradedRings.ReesModule

/-!
# The Rees module of the regular module

For any ideal `I` of a commutative ring `R`, `Ideal.Filtration.regularReesEquiv`
identifies `reesAlgebra I` with the Rees submodule of the stable filtration of
`(⊤ : Submodule R R)`. It sends a Rees polynomial to its multiple of the degree-zero
polynomial-module unit. Applying `PolynomialModule.equivPolynomialSelf` to the image
recovers the Rees polynomial; the same comparison gives the underlying polynomial of
its inverse.

The construction restricts the polynomial-module comparison to the canonical Rees
submodule. No finite-generation, Noetherian, or nontriviality assumption is needed.

## References

* Mathlib's `PolynomialModule.equivPolynomialSelf` supplies the regular polynomial-module
  comparison and its single-monomial formulas.
* `GradedRings.ReesModule` supplies the canonical Rees submodule and its single-element
  membership theorem.
-/

@[expose] public section

universe u

namespace Ideal.Filtration

open Ideal.AssociatedGradedModule

variable {R : Type u} [CommRing R] (I : Ideal R)

local notation "B" => reesAlgebra I
local notation "N" => (Ideal.Filtration.submodule (I.stableFiltration (⊤ : Submodule R R)))

private theorem coeff_equivPolynomialSelf (p : PolynomialModule R R) (n : ℕ) :
    (PolynomialModule.equivPolynomialSelf p).coeff n = p.coeff n := rfl

/-- The regular Rees equivalence sends each Rees polynomial to its multiple of the
degree-zero polynomial-module unit in the canonical Rees submodule. -/
noncomputable def regularReesEquiv : B ≃ₗ[B] N :=
  LinearEquiv.ofBijective
    (LinearMap.toSpanSingleton B N
      ⟨PolynomialModule.single R 0 (1 : R), single_mem I R 0 (1 : R) (by simp)⟩) (by
    let u₀ : N :=
      ⟨PolynomialModule.single R 0 (1 : R), single_mem I R 0 (1 : R) (by simp)⟩
    let e := PolynomialModule.equivPolynomialSelf (R := R)
    have hunit : e (PolynomialModule.single R 0 (1 : R)) = 1 := by
      simp [e]
    have he (b : B) :
        e ((b • u₀ : N) : PolynomialModule R R) = (b : Polynomial R) := by
      change e ((b : Polynomial R) • PolynomialModule.single R 0 (1 : R)) = _
      rw [e.map_smul, hunit, smul_eq_mul, mul_one]
    constructor
    · intro b b' h
      apply Subtype.ext
      exact (he b).symm.trans
        ((congrArg (fun p : N => e (p : PolynomialModule R R)) h).trans (he b'))
    · intro p
      let b : B := ⟨e (p : PolynomialModule R R), by
        intro n
        change (PolynomialModule.equivPolynomialSelf (p : PolynomialModule R R)).coeff n ∈
          I ^ n
        rw [coeff_equivPolynomialSelf]
        have hp : (p : PolynomialModule R R).coeff n ∈
            I ^ n • (⊤ : Submodule R R) := p.property n
        simpa only [Ideal.smul_eq_mul, Ideal.mul_top] using hp⟩
      refine ⟨b, ?_⟩
      apply Subtype.ext
      apply e.injective
      exact he b)

/-- The regular Rees equivalence is multiplication by the degree-zero unit. -/
theorem regularReesEquiv_apply (b : B) :
    regularReesEquiv I b =
      b • (⟨PolynomialModule.single R 0 (1 : R),
        single_mem I R 0 (1 : R) (by simp)⟩ : N) := rfl

/-- The inverse regular Rees equivalence has the polynomial of the regular
polynomial-module comparison. -/
@[simp]
theorem regularReesEquiv_symm_apply_coe (p : N) :
    (((regularReesEquiv I).symm p : B) : Polynomial R) =
      PolynomialModule.equivPolynomialSelf (p : PolynomialModule R R) := by
  let e := PolynomialModule.equivPolynomialSelf (R := R)
  have hunit : e (PolynomialModule.single R 0 (1 : R)) = 1 := by
    simp [e]
  have h := congrArg (fun q : N => e (q : PolynomialModule R R))
    ((regularReesEquiv I).apply_symm_apply p)
  rw [regularReesEquiv_apply] at h
  change e ((((regularReesEquiv I).symm p : B) : Polynomial R) •
    PolynomialModule.single R 0 (1 : R)) = e (p : PolynomialModule R R) at h
  rw [e.map_smul, hunit, smul_eq_mul, mul_one] at h
  exact h

/-- The polynomial-module comparison recovers a Rees polynomial from its regular
Rees image. -/
theorem equivPolynomialSelf_regularReesEquiv_apply (b : B) :
    PolynomialModule.equivPolynomialSelf (regularReesEquiv I b : PolynomialModule R R) =
      (b : Polynomial R) := by
  exact (regularReesEquiv_symm_apply_coe I (regularReesEquiv I b)).symm.trans
    (congrArg (fun a : B => (a : Polynomial R)) ((regularReesEquiv I).symm_apply_apply b))

end Ideal.Filtration
