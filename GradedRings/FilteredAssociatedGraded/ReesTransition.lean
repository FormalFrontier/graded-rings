/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GradedRings.FilteredAssociatedGraded.ReesProjectionNaturality
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Module.Submodule.LinearMap

/-!
# Cutoff transitions for natural Rees tails

For integer cutoffs `k ≤ l`, multiplication by the ambient polynomial
`X ^ (l - k).toNat` carries the natural Rees tail at `l` into the tail at `k`.
The coefficient in polynomial degree `q` moves to degree `(l - k).toNat + q`,
so its integer filtration degree remains `l + q`. The resulting maps are linear
over the Rees algebra, although the multiplying polynomial need not belong to
that algebra.

The transitions are injective, preserve identities and composition, commute
with shifted Rees projections along the same quotient homomorphism, and are
natural for stage-preserving linear maps.

## References

* Mathlib's polynomial-module action and its monomial coefficient and single laws.
* Mathlib's `DistribSMul.toLinearMap` and `LinearMap.restrict`.
* `GradedRings.FilteredAssociatedGraded.ReesProjectionNaturality` supplies the
  shifted projections and the natural maps of Rees tails.
-/

@[expose] public section

universe uR uM uN

namespace Ideal.IntFiltration

variable {R : Type uR} [CommRing R] {I : Ideal R}
variable {M : Type uM} [AddCommGroup M] [Module R M]
variable (F : I.IntFiltration M)

local notation "B" => reesAlgebra I
local notation "J" => I.map (algebraMap R B)

/-- The cutoff transition multiplies by an ambient power of `X` and restricts
this linear map to the natural Rees tails. -/
noncomputable def natTailTransition (k l : ℤ) (hkl : k ≤ l) :
    (F.natTail l).submodule →ₗ[B] (F.natTail k).submodule :=
  (DistribSMul.toLinearMap B (PolynomialModule R M)
      ((Polynomial.X : Polynomial R) ^ (l - k).toNat)).restrict
    (p := (F.natTail l).submodule) (q := (F.natTail k).submodule) (by
      intro p hp
      change ((Polynomial.X : Polynomial R) ^ (l - k).toNat) • p ∈
        (F.natTail k).submodule
      rw [(F.natTail k).mem_submodule]
      intro q
      rw [Polynomial.X_pow_eq_monomial, PolynomialModule.monomial_smul_apply]
      by_cases hq : (l - k).toNat ≤ q
      · rw [ite_eq_left hq, one_smul, natTail_N]
        have hpq := ((F.natTail l).mem_submodule p).mp hp (q - (l - k).toNat)
        rw [natTail_N] at hpq
        have hdegree :
            k + (q : ℤ) = l + ((q - (l - k).toNat : ℕ) : ℤ) := by
          omega
        rw [hdegree]
        exact hpq
      · rw [ite_eq_right hq]
        exact ((F.natTail k).N q).zero_mem)

/-- The underlying polynomial is obtained using the ambient polynomial action. -/
theorem coe_natTailTransition (k l : ℤ) (hkl : k ≤ l)
    (p : (F.natTail l).submodule) :
    (F.natTailTransition k l hkl p : PolynomialModule R M) =
      ((Polynomial.X : Polynomial R) ^ (l - k).toNat) •
        (p : PolynomialModule R M) := by
  rfl

/-- Coefficients are shifted by the cutoff difference and vanish below it. -/
theorem coeff_natTailTransition (k l : ℤ) (hkl : k ≤ l) (q : ℕ)
    (p : (F.natTail l).submodule) :
    (F.natTailTransition k l hkl p : PolynomialModule R M).coeff q =
      if (l - k).toNat ≤ q then
        (p : PolynomialModule R M).coeff (q - (l - k).toNat)
      else 0 := by
  rw [coe_natTailTransition, Polynomial.X_pow_eq_monomial,
    PolynomialModule.monomial_smul_apply]
  simp only [one_smul]

/-- The coefficient at the shifted degree is the unchanged source coefficient. -/
@[simp]
theorem coeff_natTailTransition_add (k l : ℤ) (hkl : k ≤ l) (q : ℕ)
    (p : (F.natTail l).submodule) :
    (F.natTailTransition k l hkl p : PolynomialModule R M).coeff
        ((l - k).toNat + q) =
      (p : PolynomialModule R M).coeff q := by
  simp [coeff_natTailTransition]

/-- An admissible single keeps its coefficient and acquires the shifted
polynomial degree. -/
@[simp]
theorem natTailTransition_single (k l : ℤ) (hkl : k ≤ l) (q : ℕ)
    (m : F.N (l + (q : ℤ))) :
    F.natTailTransition k l hkl (F.natTailSingle l q m) =
      F.natTailSingle k ((l - k).toNat + q)
        ⟨(m : M), by
          rw [Nat.cast_add, Int.toNat_of_nonneg (sub_nonneg.mpr hkl),
            ← add_assoc, add_comm k (l - k), sub_add_cancel]
          exact m.property⟩ := by
  apply Subtype.ext
  simp only [coe_natTailTransition, coe_natTailSingle, Polynomial.X_pow_eq_monomial,
    PolynomialModule.monomial_smul_single, one_smul]

/-- A cutoff transition is injective without any regularity hypothesis. -/
theorem natTailTransition_injective (k l : ℤ) (hkl : k ≤ l) :
    Function.Injective (F.natTailTransition k l hkl) := by
  intro p p' h
  apply Subtype.ext
  apply PolynomialModule.coeff_injective
  apply Finsupp.ext
  intro q
  have hcoeff := congrArg
    (fun x : (F.natTail k).submodule =>
      (x : PolynomialModule R M).coeff ((l - k).toNat + q)) h
  simpa only [coeff_natTailTransition_add] using hcoeff

/-- Equal cutoffs give the identity map on the natural Rees tail. -/
@[simp]
theorem natTailTransition_self (k : ℤ) :
    F.natTailTransition k k le_rfl =
      (LinearMap.id : (F.natTail k).submodule →ₗ[B] (F.natTail k).submodule) := by
  apply LinearMap.ext
  intro p
  apply Subtype.ext
  simp only [coe_natTailTransition, sub_self, Int.toNat_zero, pow_zero, one_smul,
    LinearMap.id_apply]

/-- Successive cutoff transitions compose to the transition between the outer
cutoffs. -/
theorem natTailTransition_comp (k l m : ℤ) (hkl : k ≤ l) (hlm : l ≤ m) :
    (F.natTailTransition k l hkl).comp (F.natTailTransition l m hlm) =
      F.natTailTransition k m (hkl.trans hlm) := by
  have hdiff : (l - k).toNat + (m - l).toNat = (m - k).toNat := by
    lia
  apply LinearMap.ext
  intro p
  apply Subtype.ext
  simp only [LinearMap.comp_apply, coe_natTailTransition]
  rw [smul_smul, ← pow_add, hdiff]

/-- Shifted Rees projections commute with cutoff transitions as semilinear maps
along the same quotient of the Rees algebra. -/
theorem shiftedReesProjection_comp_natTailTransition (k l : ℤ) (hkl : k ≤ l) :
    ((F.shiftedReesProjection k).comp (F.natTailTransition k l hkl) :
        (F.natTail l).submodule →ₛₗ[Ideal.Quotient.mk J] F.AssociatedGraded) =
      F.shiftedReesProjection l := by
  apply F.shiftedReesProjection_unique l
  intro q m
  rw [LinearMap.comp_apply, F.natTailTransition_single,
    F.shiftedReesProjection_single]
  have hdeg : k + (((l - k).toNat + q : ℕ) : ℤ) = l + (q : ℤ) := by
    lia
  have hsingle {n n' : ℤ} (hn : n = n') (a : F.N n) (a' : F.N n')
      (ha : (a : M) = (a' : M)) : F.single n a = F.single n' a' := by
    subst n'
    exact congrArg (F.single n) (Subtype.ext ha)
  exact hsingle hdeg _ _ rfl

variable {N : Type uN} [AddCommGroup N] [Module R N]
variable (H : I.IntFiltration N) (f : M →ₗ[R] N)
variable (hf : ∀ n, F.N n ≤ (H.N n).comap f)

/-- Stage-preserving linear maps commute with the cutoff transitions through
the coefficientwise maps of natural Rees tails. -/
theorem natTailTransition_naturality (k l : ℤ) (hkl : k ≤ l) :
    (H.natTailTransition k l hkl).comp
        ((F.natTail l).reesMap (H.natTail l) f (by
          intro q
          simpa only [natTail_N] using hf (l + (q : ℤ)))) =
      ((F.natTail k).reesMap (H.natTail k) f (by
          intro q
          simpa only [natTail_N] using hf (k + (q : ℤ)))).comp
        (F.natTailTransition k l hkl) := by
  apply LinearMap.ext
  intro p
  apply Subtype.ext
  simp only [LinearMap.comp_apply, coe_natTailTransition, Ideal.Filtration.coe_reesMap]
  simpa using (PolynomialModule.map_smul R f
    ((Polynomial.X : Polynomial R) ^ (l - k).toNat)
    (p : PolynomialModule R M)).symm

end Ideal.IntFiltration
