/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GradedRings.PolynomialModule.UniversalProperty

/-!
# Polynomial extension of the regular module

The polynomial extension of the left regular module over a semiring is the left regular
module over its polynomial semiring. The forward map extends the inclusion of constants;
the inverse sends a polynomial to its action on the degree-zero coefficient `1`.

The coefficient, single-degree and inverse formulas describe this equivalence without
requiring commutativity or additive inverses.
-/

@[expose] public section

universe u

namespace PolynomialModule.Extension

variable (R : Type u) [Semiring R]

private noncomputable def regularTo : Extension R R →ₗ[Polynomial R] Polynomial R :=
  lift
    { toFun := Polynomial.C
      map_add' := fun a b => Polynomial.C_add (a := a) (b := b)
      map_smul' := fun r a => Polynomial.C_mul (a := r) (b := a) }

private noncomputable def regularFrom : Polynomial R →ₗ[Polynomial R] Extension R R where
  toFun p := p • single R 0 (1 : R)
  map_add' p q := add_smul p q _
  map_smul' c p := mul_smul c p _

private theorem regularTo_single (n : ℕ) (r : R) :
    regularTo R (single R n r) = Polynomial.monomial n r := by
  rw [regularTo, lift_single]
  change Polynomial.monomial n 1 * Polynomial.C r = Polynomial.monomial n r
  rw [Polynomial.monomial_mul_C, one_mul]

/-- The polynomial extension of the left regular `R`-module is the left regular
`R[X]`-module. -/
noncomputable def regularEquiv : Extension R R ≃ₗ[Polynomial R] Polynomial R :=
  LinearEquiv.ofLinearMap
    (lift
      { toFun := Polynomial.C
        map_add' := fun a b => Polynomial.C_add (a := a) (b := b)
        map_smul' := fun r a => Polynomial.C_mul (a := r) (b := a) })
    { toFun := fun p => p • single R 0 (1 : R)
      map_add' := fun p q => add_smul p q _
      map_smul' := fun c p => mul_smul c p _ }
    (by
      apply LinearMap.ext
      intro p
      change regularTo R (p • single R 0 (1 : R)) = p
      rw [(regularTo R).map_smul, regularTo_single]
      simp [smul_eq_mul])
    (by
      apply linearMap_ext
      intro r
      change regularFrom R (regularTo R (single R 0 r)) = single R 0 r
      rw [regularTo_single]
      simp [regularFrom, ← single_smul, smul_eq_mul])

@[simp]
theorem regularEquiv_apply_single (n : ℕ) (r : R) :
    regularEquiv R (single R n r) = Polynomial.monomial n r :=
  regularTo_single R n r

/-- The inverse regular comparison is polynomial scalar multiplication of `single R 0 1`. -/
theorem regularEquiv_symm_apply (p : Polynomial R) :
    (regularEquiv R).symm p = p • single R 0 (1 : R) := rfl

@[simp]
theorem regularEquiv_symm_coeff (p : Polynomial R) (n : ℕ) :
    coeff ((regularEquiv R).symm p) n = p.coeff n := by
  simp [regularEquiv_symm_apply, smul_single_apply, smul_eq_mul]

@[simp]
theorem regularEquiv_coeff (q : Extension R R) (n : ℕ) :
    (regularEquiv R q).coeff n = coeff q n := by
  simpa only [LinearEquiv.symm_apply_apply] using
    (regularEquiv_symm_coeff R (regularEquiv R q) n).symm

/-- The regular comparison sums the monomials of the coefficient sequence. -/
theorem regularEquiv_apply (q : Extension R R) :
    regularEquiv R q = (coeff q).sum fun n r => Polynomial.monomial n r := by
  change regularTo R q = _
  rw [regularTo, lift_apply]
  apply congrArg (fun f : ℕ → R → Polynomial R => (coeff q).sum f)
  funext n r
  change Polynomial.monomial n 1 * Polynomial.C r = Polynomial.monomial n r
  rw [Polynomial.monomial_mul_C, one_mul]

@[simp]
theorem regularEquiv_symm_monomial (n : ℕ) (r : R) :
    (regularEquiv R).symm (Polynomial.monomial n r) = single R n r := by
  rw [regularEquiv_symm_apply]
  simp [monomial_smul_single, smul_eq_mul]

/-- Polynomial multiples of constant coefficients correspond to right multiplication
by the associated constant polynomial. -/
theorem regularEquiv_smul_single (p : Polynomial R) (r : R) :
    regularEquiv R (p • single R 0 r) = p * Polynomial.C r := by
  rw [(regularEquiv R).map_smul, regularEquiv_apply_single]
  simp only [Polynomial.monomial_zero_left, smul_eq_mul]

end PolynomialModule.Extension
