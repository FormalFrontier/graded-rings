/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GradedRings.ReesAlgebra.QuotientPieces
public import Mathlib.LinearAlgebra.Quotient.Bilinear

/-!
# Multiplication of ideal-power quotients

Multiplication of coefficients induces an `R ⧸ I`-bilinear map from the quotients
of `I ^ q` and `I ^ r` by their ideal multiples to the corresponding quotient of
`I ^ (q + r)`. On representatives this map sends the classes of `a` and `b` to
the class of `a * b`.

The construction uses coefficient multiplication and the two denominator checks,
independently of any comparison with quotient Rees components. The scalar actions
on the quotients are the existing quotient-module actions.

## References

* Mathlib's `LinearMap.mk₂` and `LinearMap.liftQ₂` for bilinear maps and their
  descent to quotients.
-/

@[expose] public section

universe u

namespace reesAlgebra

variable {R : Type u} [CommRing R] (I : Ideal R)

private def coefficientMul (q r : ℕ) :
    ↥(I ^ q) →ₗ[R] ↥(I ^ r) →ₗ[R] ↥(I ^ (q + r)) :=
  LinearMap.mk₂ R
    (fun a b => ⟨(a : R) * (b : R), by
      rw [pow_add]
      exact Ideal.mul_mem_mul a.property b.property⟩)
    (fun a₁ a₂ b => Subtype.ext (add_mul (a₁ : R) (a₂ : R) (b : R)))
    (fun c a b => Subtype.ext (smul_mul_assoc c (a : R) (b : R)))
    (fun a b₁ b₂ => Subtype.ext (mul_add (a : R) (b₁ : R) (b₂ : R)))
    (fun c a b => Subtype.ext (mul_smul_comm c (a : R) (b : R)))

private def coefficientMulQuotient (q r : ℕ) :
    ↥(I ^ q) →ₗ[R] ↥(I ^ r) →ₗ[R] powerQuotient I (q + r) :=
  (coefficientMul I q r).compr₂
    (I • (⊤ : Submodule R ↥(I ^ (q + r)))).mkQ

private theorem coefficientMulQuotient_left_denominator (q r : ℕ) :
    I • (⊤ : Submodule R ↥(I ^ q)) ≤ (coefficientMulQuotient I q r).ker := by
  apply Submodule.smul_le.mpr
  intro c hc a _
  rw [LinearMap.mem_ker]
  apply LinearMap.ext
  intro b
  change Submodule.Quotient.mk (coefficientMul I q r (c • a) b) = 0
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  rw [LinearMap.map_smul, LinearMap.smul_apply]
  exact Submodule.smul_mem_smul hc Submodule.mem_top

private theorem coefficientMulQuotient_right_denominator (q r : ℕ) :
    I • (⊤ : Submodule R ↥(I ^ r)) ≤ (coefficientMulQuotient I q r).flip.ker := by
  apply Submodule.smul_le.mpr
  intro c hc b _
  rw [LinearMap.mem_ker]
  apply LinearMap.ext
  intro a
  change Submodule.Quotient.mk (coefficientMul I q r a (c • b)) = 0
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  rw [LinearMap.map_smul]
  exact Submodule.smul_mem_smul hc Submodule.mem_top

private def powerQuotientMulR (q r : ℕ) :
    powerQuotient I q →ₗ[R] powerQuotient I r →ₗ[R] powerQuotient I (q + r) :=
  (coefficientMulQuotient I q r).liftQ₂
    (I • (⊤ : Submodule R ↥(I ^ q)))
    (I • (⊤ : Submodule R ↥(I ^ r)))
    (coefficientMulQuotient_left_denominator I q r)
    (coefficientMulQuotient_right_denominator I q r)

/-- Multiplication of coefficient classes in ideal-power quotients, bilinear over `R ⧸ I`. -/
@[no_expose]
noncomputable def powerQuotientMul (q r : ℕ) :
    powerQuotient I q →ₗ[R ⧸ I]
      powerQuotient I r →ₗ[R ⧸ I] powerQuotient I (q + r) :=
  LinearMap.extendScalarsOfSurjective (R := R) (S := R ⧸ I)
    Ideal.Quotient.mk_surjective
    (((LinearMap.extendScalarsOfSurjectiveEquiv (R := R) (S := R ⧸ I)
      (M := powerQuotient I r) (N := powerQuotient I (q + r))
      Ideal.Quotient.mk_surjective).toLinearMap).comp (powerQuotientMulR I q r))

-- Keep the definitional computation private so that the implementation can remain opaque.
private theorem powerQuotientMul_mk_proof (q r : ℕ) (a : ↥(I ^ q)) (b : ↥(I ^ r)) :
    powerQuotientMul I q r (Submodule.Quotient.mk a) (Submodule.Quotient.mk b) =
      Submodule.Quotient.mk
        (⟨(a : R) * (b : R), by
          rw [pow_add]
          exact Ideal.mul_mem_mul a.property b.property⟩ : ↥(I ^ (q + r))) :=
  rfl

/-- Multiplication of coefficient classes is represented by the ordinary coefficient product. -/
@[simp]
theorem powerQuotientMul_mk (q r : ℕ) (a : ↥(I ^ q)) (b : ↥(I ^ r)) :
    powerQuotientMul I q r (Submodule.Quotient.mk a) (Submodule.Quotient.mk b) =
      Submodule.Quotient.mk
        (⟨(a : R) * (b : R), by
          rw [pow_add]
          exact Ideal.mul_mem_mul a.property b.property⟩ : ↥(I ^ (q + r))) :=
  powerQuotientMul_mk_proof I q r a b

private theorem powerQuotient_cast_mk {q r : ℕ} (h : q = r) (a : ↥(I ^ q)) :
    cast (congrArg (powerQuotient I) h) (Submodule.Quotient.mk a) =
      Submodule.Quotient.mk (⟨(a : R), h ▸ a.property⟩ : ↥(I ^ r)) := by
  cases h
  rfl

/-- Coefficient multiplication is commutative after identifying the two sum degrees. -/
theorem powerQuotientMul_comm (q r : ℕ)
    (x : powerQuotient I q) (y : powerQuotient I r) :
    cast (congrArg (powerQuotient I) (Nat.add_comm q r)) (powerQuotientMul I q r x y) =
      powerQuotientMul I r q y x := by
  induction x using Submodule.Quotient.induction_on with
  | H a =>
    induction y using Submodule.Quotient.induction_on with
    | H b =>
      rw [powerQuotientMul_mk, powerQuotientMul_mk,
        powerQuotient_cast_mk I (Nat.add_comm q r)]
      apply congrArg Submodule.Quotient.mk
      exact Subtype.ext (mul_comm (a : R) (b : R))

/-- Coefficient multiplication is associative after identifying the two sum degrees. -/
theorem powerQuotientMul_assoc (q r s : ℕ)
    (x : powerQuotient I q) (y : powerQuotient I r) (z : powerQuotient I s) :
    cast (congrArg (powerQuotient I) (Nat.add_assoc q r s))
        (powerQuotientMul I (q + r) s (powerQuotientMul I q r x y) z) =
      powerQuotientMul I q (r + s) x (powerQuotientMul I r s y z) := by
  induction x using Submodule.Quotient.induction_on with
  | H a =>
    induction y using Submodule.Quotient.induction_on with
    | H b =>
      induction z using Submodule.Quotient.induction_on with
      | H c =>
        simp only [powerQuotientMul_mk]
        rw [powerQuotient_cast_mk I (Nat.add_assoc q r s)]
        apply congrArg Submodule.Quotient.mk
        exact Subtype.ext (mul_assoc (a : R) (b : R) (c : R))

/-- The class of `1` in degree zero is a left unit for coefficient multiplication. -/
theorem powerQuotientMul_one_left (q : ℕ) (x : powerQuotient I q) :
    cast (congrArg (powerQuotient I) (Nat.zero_add q))
        (powerQuotientMul I 0 q (Submodule.Quotient.mk ⟨1, by simp⟩) x) = x := by
  induction x using Submodule.Quotient.induction_on with
  | H a =>
    rw [powerQuotientMul_mk, powerQuotient_cast_mk I (Nat.zero_add q)]
    apply congrArg Submodule.Quotient.mk
    exact Subtype.ext (one_mul (a : R))

/-- The class of `1` in degree zero is a right unit for coefficient multiplication. -/
theorem powerQuotientMul_one_right (q : ℕ) (x : powerQuotient I q) :
    cast (congrArg (powerQuotient I) (Nat.add_zero q))
        (powerQuotientMul I q 0 x (Submodule.Quotient.mk ⟨1, by simp⟩)) = x := by
  induction x using Submodule.Quotient.induction_on with
  | H a =>
    rw [powerQuotientMul_mk, powerQuotient_cast_mk I (Nat.add_zero q)]
    apply congrArg Submodule.Quotient.mk
    exact Subtype.ext (mul_one (a : R))

end reesAlgebra
