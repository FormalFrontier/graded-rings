/-
Copyright (c) 2026 Formal Frontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rudder
-/
module

public import GradedRings.PolynomialModule.Basic
public import Mathlib.Algebra.Polynomial.Module.Basic

/-!
# Comparison of polynomial modules

At commutative-ring coefficients and additive-group module coefficients, the coefficient
constructor identifies `PolynomialModule.Extension R M` with `PolynomialModule R M`.
This identification preserves coefficientwise scalar actions and the polynomial actions.

The polynomial-action comparison follows from the antidiagonal coefficient formulas for
the two polynomial modules.

## References

Andrew Yang's polynomial-module construction in Mathlib, in particular
`PolynomialModule.smul_apply`.
-/

@[expose] public noncomputable section

universe u v w

open Polynomial

namespace PolynomialModule.Extension

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]

/-- The coefficient-preserving map to the polynomial module. -/
def toPolynomialModule (q : Extension R M) : PolynomialModule R M :=
  PolynomialModule.ofCoeff R q.coeff

/-- The coefficient-preserving map from the polynomial module. -/
def ofPolynomialModule (q : PolynomialModule R M) : Extension R M :=
  ofCoeff R q.coeff

@[simp]
theorem coeff_toPolynomialModule (q : Extension R M) :
    (toPolynomialModule q).coeff = q.coeff := rfl

@[simp]
theorem coeff_ofPolynomialModule (q : PolynomialModule R M) :
    (ofPolynomialModule q).coeff = q.coeff := rfl

@[simp]
theorem ofPolynomialModule_toPolynomialModule (q : Extension R M) :
    ofPolynomialModule (toPolynomialModule q) = q := rfl

@[simp]
theorem toPolynomialModule_ofPolynomialModule (q : PolynomialModule R M) :
    toPolynomialModule (ofPolynomialModule q) = q := rfl

@[simp]
theorem toPolynomialModule_ofCoeff (f : ℕ →₀ M) :
    toPolynomialModule (ofCoeff R f) = PolynomialModule.ofCoeff R f := rfl

@[simp]
theorem ofPolynomialModule_ofCoeff (f : ℕ →₀ M) :
    ofPolynomialModule (PolynomialModule.ofCoeff R f) = ofCoeff R f := rfl

@[simp]
theorem toPolynomialModule_zero :
    toPolynomialModule (0 : Extension R M) = 0 := rfl

@[simp]
theorem ofPolynomialModule_zero :
    ofPolynomialModule (0 : PolynomialModule R M) = 0 := rfl

@[simp]
theorem toPolynomialModule_add (q q' : Extension R M) :
    toPolynomialModule (q + q') = toPolynomialModule q + toPolynomialModule q' := rfl

@[simp]
theorem ofPolynomialModule_add (q q' : PolynomialModule R M) :
    ofPolynomialModule (q + q') = ofPolynomialModule q + ofPolynomialModule q' := rfl

@[simp]
theorem toPolynomialModule_single (n : ℕ) (m : M) :
    toPolynomialModule (single R n m) = PolynomialModule.single R n m := rfl

@[simp]
theorem ofPolynomialModule_single (n : ℕ) (m : M) :
    ofPolynomialModule (PolynomialModule.single R n m) = single R n m := rfl

/-- The additive equivalence preserving all coefficients. -/
def addEquivPolynomialModule : Extension R M ≃+ PolynomialModule R M :=
  (coeffAddEquiv R M).trans (PolynomialModule.coeffAddEquiv (R := R) (M := M)).symm

@[simp]
theorem addEquivPolynomialModule_apply (q : Extension R M) :
    addEquivPolynomialModule q = PolynomialModule.ofCoeff R q.coeff := rfl

@[simp]
theorem addEquivPolynomialModule_symm_apply (q : PolynomialModule R M) :
    addEquivPolynomialModule.symm q = ofCoeff R q.coeff := rfl

theorem coeff_addEquivPolynomialModule (q : Extension R M) :
    (addEquivPolynomialModule q).coeff = q.coeff := rfl

theorem coeff_addEquivPolynomialModule_symm (q : PolynomialModule R M) :
    (addEquivPolynomialModule.symm q).coeff = q.coeff := rfl

/-- The coefficientwise `R`-linear equivalence between the polynomial modules. -/
def linearEquivPolynomialModule :
    letI : Module R (Extension R M) := coefficientModule (R := R) (M := M);
    letI : Module R (PolynomialModule R M) :=
      (PolynomialModule.coeffAddEquiv (R := R) (M := M)).module R;
    Extension R M ≃ₗ[R] PolynomialModule R M := by
  letI : Module R (Extension R M) := coefficientModule (R := R) (M := M)
  letI : Module R (PolynomialModule R M) :=
    (PolynomialModule.coeffAddEquiv (R := R) (M := M)).module R
  exact (coeffLinearEquiv R M).trans (PolynomialModule.coeffLinearEquiv R R).symm

@[simp]
theorem linearEquivPolynomialModule_apply (q : Extension R M) :
    linearEquivPolynomialModule q = toPolynomialModule q := rfl

@[simp]
theorem linearEquivPolynomialModule_symm_apply (q : PolynomialModule R M) :
    linearEquivPolynomialModule.symm q = ofPolynomialModule q := rfl

@[simp]
theorem toPolynomialModule_smul (r : R) (q : Extension R M) :
    toPolynomialModule (r • q) = r • toPolynomialModule q :=
  linearEquivPolynomialModule.map_smul r q

@[simp]
theorem ofPolynomialModule_smul (r : R) (q : PolynomialModule R M) :
    ofPolynomialModule (r • q) = r • ofPolynomialModule q :=
  linearEquivPolynomialModule.symm.map_smul r q

section Pointwise

variable {S : Type w} [Semiring S] [Module S M]

/-- The coefficientwise `S`-linear equivalence for the specified scalar action. -/
def pointwiseLinearEquivPolynomialModule :
    letI : Module S (Extension R M) := pointwiseModule (R := R) (M := M) S;
    letI : Module S (PolynomialModule R M) :=
      (PolynomialModule.coeffAddEquiv (R := R) (M := M)).module S;
    Extension R M ≃ₗ[S] PolynomialModule R M := by
  letI : Module S (Extension R M) := pointwiseModule (R := R) (M := M) S
  letI : Module S (PolynomialModule R M) :=
    (PolynomialModule.coeffAddEquiv (R := R) (M := M)).module S
  exact (pointwiseCoeffLinearEquiv (R := R) (M := M) S).trans
    ((PolynomialModule.coeffAddEquiv (R := R) (M := M)).linearEquiv S).symm

@[simp]
theorem pointwiseLinearEquivPolynomialModule_apply (q : Extension R M) :
    pointwiseLinearEquivPolynomialModule (S := S) q = toPolynomialModule q := rfl

@[simp]
theorem pointwiseLinearEquivPolynomialModule_symm_apply (q : PolynomialModule R M) :
    (pointwiseLinearEquivPolynomialModule (S := S)).symm q = ofPolynomialModule q := rfl

/-- The coefficient map intertwines the specified pointwise scalar operations. -/
theorem toPolynomialModule_pointwise_smul (s : S) (q : Extension R M) :
    letI : Module S (Extension R M) := pointwiseModule (R := R) (M := M) S;
    letI : Module S (PolynomialModule R M) :=
      (PolynomialModule.coeffAddEquiv (R := R) (M := M)).module S;
    toPolynomialModule (s • q) = s • toPolynomialModule q :=
  (pointwiseLinearEquivPolynomialModule (S := S)).map_smul s q

/-- The inverse coefficient map intertwines the specified pointwise scalar operations. -/
theorem ofPolynomialModule_pointwise_smul (s : S) (q : PolynomialModule R M) :
    letI : Module S (Extension R M) := pointwiseModule (R := R) (M := M) S;
    letI : Module S (PolynomialModule R M) :=
      (PolynomialModule.coeffAddEquiv (R := R) (M := M)).module S;
    ofPolynomialModule (s • q) = s • ofPolynomialModule q :=
  (pointwiseLinearEquivPolynomialModule (S := S)).symm.map_smul s q

end Pointwise

/-- The inverse coefficient map preserves the polynomial scalar actions. -/
theorem ofPolynomialModule_polynomial_smul (p : R[X]) (q : PolynomialModule R M) :
    letI : Module R[X] (Extension R M) := polynomialModule (R := R) (M := M);
    letI : Module R[X] (PolynomialModule R M) :=
      PolynomialModule.polynomialModule (R := R) (M := M);
    ofPolynomialModule (p • q) = p • ofPolynomialModule q := by
  let : Module R[X] (Extension R M) := polynomialModule (R := R) (M := M)
  let : Module R[X] (PolynomialModule R M) :=
    PolynomialModule.polynomialModule (R := R) (M := M)
  apply ext
  ext n
  rw [coeff_ofPolynomialModule, PolynomialModule.Extension.coeff_smul,
    coeff_ofPolynomialModule]
  exact PolynomialModule.smul_apply p q n

/-- The coefficient-preserving equivalence for the polynomial scalar actions. -/
def polynomialLinearEquivPolynomialModule :
    letI : Module R[X] (Extension R M) := polynomialModule (R := R) (M := M);
    letI : Module R[X] (PolynomialModule R M) :=
      PolynomialModule.polynomialModule (R := R) (M := M);
    Extension R M ≃ₗ[R[X]] PolynomialModule R M := by
  letI : Module R[X] (Extension R M) := polynomialModule (R := R) (M := M)
  letI : Module R[X] (PolynomialModule R M) :=
    PolynomialModule.polynomialModule (R := R) (M := M)
  refine { toAddEquiv := addEquivPolynomialModule, map_smul' := ?_ }
  intro p q
  change toPolynomialModule (p • q) = p • toPolynomialModule q
  simpa only [ofPolynomialModule_toPolynomialModule, toPolynomialModule_ofPolynomialModule]
    using (congrArg toPolynomialModule
      (ofPolynomialModule_polynomial_smul p (toPolynomialModule q))).symm

@[simp]
theorem polynomialLinearEquivPolynomialModule_apply (q : Extension R M) :
    polynomialLinearEquivPolynomialModule q = toPolynomialModule q := rfl

@[simp]
theorem polynomialLinearEquivPolynomialModule_symm_apply (q : PolynomialModule R M) :
    polynomialLinearEquivPolynomialModule.symm q = ofPolynomialModule q := rfl

/-- The coefficient map preserves the polynomial scalar actions. -/
theorem toPolynomialModule_polynomial_smul (p : R[X]) (q : Extension R M) :
    letI : Module R[X] (Extension R M) := polynomialModule (R := R) (M := M);
    letI : Module R[X] (PolynomialModule R M) :=
      PolynomialModule.polynomialModule (R := R) (M := M);
    toPolynomialModule (p • q) = p • toPolynomialModule q :=
  polynomialLinearEquivPolynomialModule.map_smul p q

end PolynomialModule.Extension
