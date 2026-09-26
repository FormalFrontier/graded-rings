/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GradedRings.HomogeneousPrimeMultiplicity
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# Homogeneous localization of multivariate polynomial rings

For a nonconstant homogeneous prime polynomial, prime multiplicity of a
homogeneous numerator is bounded by the denominator exponent.  This is the
degree estimate underlying reduced denominators in the homogeneous
localization away from that polynomial.
-/

@[expose] public section

noncomputable section

open Multiplicative WithZero

namespace MvPolynomial

variable {k ι : Type*} [Field k]
variable {p x : MvPolynomial ι k} {d n : ℕ}

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A nonconstant homogeneous prime cannot occur in a homogeneous polynomial
of degree `n * d` with multiplicity greater than `n`. -/
theorem multiplicity_le_of_isHomogeneous (hp : Prime p)
    (hpHom : p.IsHomogeneous d) (hd : d ≠ 0)
    (hxHom : x.IsHomogeneous (n * d)) (hx0 : x ≠ 0) :
    multiplicity p x ≤ n := by
  have hpowHom : (p ^ multiplicity p x).IsHomogeneous
      (multiplicity p x * d) := by
    simpa [mul_comm] using hpHom.pow (multiplicity p x)
  have hle := totalDegree_le_of_dvd_of_isDomain
    (pow_multiplicity_dvd p x) hx0
  rw [hpowHom.totalDegree (pow_ne_zero _ hp.ne_zero),
    hxHom.totalDegree hx0] at hle
  exact Nat.le_of_mul_le_mul_right hle (Nat.zero_lt_of_ne_zero hd)

/-- If the multiplicity reaches the degree bound, the remaining factor is a
nonzero coefficient. -/
theorem exists_eq_pow_mul_C_of_multiplicity_eq (hp : Prime p)
    (hpHom : p.IsHomogeneous d) (hxHom : x.IsHomogeneous (n * d))
    (hx0 : x ≠ 0) (hm : multiplicity p x = n) :
    ∃ c : k, c ≠ 0 ∧ x = p ^ n * C c := by
  have hdvd : p ^ n ∣ x := by
    rw [← hm]
    exact pow_multiplicity_dvd p x
  obtain ⟨a, ha⟩ := hdvd
  have ha0 : a ≠ 0 := by
    intro ha0
    apply hx0
    simp [ha, ha0]
  have hpPow0 : p ^ n ≠ 0 := pow_ne_zero n hp.ne_zero
  have hdeg : a.totalDegree = 0 := by
    have hprod := totalDegree_mul_of_isDomain hpPow0 ha0
    rw [← ha, hxHom.totalDegree hx0,
      (hpHom.pow n).totalDegree hpPow0] at hprod
    simp only [Nat.mul_comm d n] at hprod
    omega
  refine ⟨a.coeff 0, ?_, ?_⟩
  · intro hc
    apply ha0
    rw [totalDegree_eq_zero_iff_eq_C.mp hdeg, hc, C_0]
  · exact ha.trans <| congrArg (p ^ n * ·)
      (totalDegree_eq_zero_iff_eq_C.mp hdeg)

/-- Coefficients map naturally to any degree-zero homogeneous localization of
a multivariate polynomial ring. -/
noncomputable def homogeneousAwayCoefficientHom (p : MvPolynomial ι k) :
    k →+* HomogeneousLocalization.Away (homogeneousSubmodule ι k) p :=
  (HomogeneousLocalization.fromZeroRingHom
      (homogeneousSubmodule ι k) (Submonoid.powers p)).comp
    { toFun := fun r ↦ ⟨C r,
        (mem_homogeneousSubmodule 0 _).2 (isHomogeneous_C ι r)⟩
      map_one' := by ext; simp
      map_mul' := by intro a b; ext; simp
      map_zero' := by ext; simp
      map_add' := by intro a b; ext; simp }

/-- A homogeneous fraction whose numerator contains the full possible power
of the homogeneous prime is a unit. -/
theorem isUnit_away_mk_of_multiplicity_eq (hp : Prime p)
    (hpHom : p.IsHomogeneous d) (hxHom : x.IsHomogeneous (n * d))
    (hx0 : x ≠ 0) (hm : multiplicity p x = n) :
    IsUnit (HomogeneousLocalization.Away.mk
      (homogeneousSubmodule ι k) hpHom n x hxHom) := by
  obtain ⟨c, hc, hxc⟩ :=
    exists_eq_pow_mul_C_of_multiplicity_eq hp hpHom hxHom hx0 hm
  have heq : HomogeneousLocalization.Away.mk
      (homogeneousSubmodule ι k) hpHom n x hxHom =
      homogeneousAwayCoefficientHom p c := by
    apply HomogeneousLocalization.val_injective
    let s : Submonoid.powers p :=
      ⟨p ^ n, (Submonoid.powers p).pow_mem (Submonoid.mem_powers p) n⟩
    change Localization.mk x s =
      Localization.mk (C c) 1
    rw [hxc]
    change Localization.mk ((s : MvPolynomial ι k) * C c) s =
      Localization.mk (C c) 1
    simp only [Localization.mk_eq_mk'_apply,
      IsLocalization.mk'_mul_cancel_left, IsLocalization.mk'_one]
  rw [heq]
  exact IsUnit.map (homogeneousAwayCoefficientHom p)
    (isUnit_iff_ne_zero.mpr hc)

/-- Every nonzero element of the degree-zero homogeneous localization has
prime-multiplicity valuation at least one (equivalently, nonnegative
denominator order). -/
theorem one_le_awayPrimeMultiplicityValuation (hp : Prime p)
    (hpHom : p.IsHomogeneous d) (hd : d ≠ 0)
    {z : HomogeneousLocalization.Away (homogeneousSubmodule ι k) p}
    (hz : z ≠ 0) :
    1 ≤ HomogeneousLocalization.awayPrimeMultiplicityValuation
      (homogeneousSubmodule ι k) hp z := by
  obtain ⟨m, a, ha, rfl⟩ :=
    HomogeneousLocalization.Away.mk_surjective
      (homogeneousSubmodule ι k) hpHom z
  have ha0 : a ≠ 0 := by
    intro ha0
    subst a
    apply hz
    exact HomogeneousLocalization.mk_eq_zero_of_num _ rfl
  have haHom : a.IsHomogeneous (m * d) := by
    simpa [nsmul_eq_mul] using ha
  rw [HomogeneousLocalization.awayPrimeMultiplicityValuation_mk
    (homogeneousSubmodule ι k) hp hpHom m a ha ha0, ← exp_zero,
    exp_le_exp]
  exact sub_nonneg.mpr <| by
    exact_mod_cast multiplicity_le_of_isHomogeneous hp hpHom hd haHom ha0

/-- The valuation of a nonzero homogeneous-localization element is an
exponential of a natural-number denominator order. -/
theorem exists_awayPrimeMultiplicityValuation_eq_exp_nat (hp : Prime p)
    (hpHom : p.IsHomogeneous d) (hd : d ≠ 0)
    {z : HomogeneousLocalization.Away (homogeneousSubmodule ι k) p}
    (hz : z ≠ 0) :
    ∃ q : ℕ, HomogeneousLocalization.awayPrimeMultiplicityValuation
      (homogeneousSubmodule ι k) hp z = exp (q : ℤ) := by
  obtain ⟨m, a, ha, rfl⟩ :=
    HomogeneousLocalization.Away.mk_surjective
      (homogeneousSubmodule ι k) hpHom z
  have ha0 : a ≠ 0 := by
    intro ha0
    subst a
    apply hz
    exact HomogeneousLocalization.mk_eq_zero_of_num _ rfl
  have haHom : a.IsHomogeneous (m * d) := by
    simpa [nsmul_eq_mul] using ha
  have hle := multiplicity_le_of_isHomogeneous hp hpHom hd haHom ha0
  refine ⟨m - multiplicity p a, ?_⟩
  rw [HomogeneousLocalization.awayPrimeMultiplicityValuation_mk
    (homogeneousSubmodule ι k) hp hpHom m a ha ha0]
  congr 1
  omega

/-- In the degree-zero homogeneous localization away from a nonconstant prime
polynomial, valuation one characterizes units. -/
theorem awayPrimeMultiplicityValuation_eq_one_iff_isUnit (hp : Prime p)
    (hpHom : p.IsHomogeneous d) (hd : d ≠ 0)
    {z : HomogeneousLocalization.Away (homogeneousSubmodule ι k) p} :
    HomogeneousLocalization.awayPrimeMultiplicityValuation
        (homogeneousSubmodule ι k) hp z = 1 ↔
      IsUnit z := by
  constructor
  · intro hv
    have hz : z ≠ 0 := by
      intro hz
      subst z
      exact (zero_ne_one : (0 : ℤᵐ⁰) ≠ 1) <| by
        simpa only [map_zero] using hv
    obtain ⟨m, a, ha, rfl⟩ :=
      HomogeneousLocalization.Away.mk_surjective
        (homogeneousSubmodule ι k) hpHom z
    have ha0 : a ≠ 0 := by
      intro ha0
      subst a
      apply hz
      exact HomogeneousLocalization.mk_eq_zero_of_num _ rfl
    have haHom : a.IsHomogeneous (m * d) := by
      simpa [nsmul_eq_mul] using ha
    rw [HomogeneousLocalization.awayPrimeMultiplicityValuation_mk
      (homogeneousSubmodule ι k) hp hpHom m a ha ha0,
      ← exp_zero] at hv
    have horder : (m : ℤ) - multiplicity p a = 0 := exp_inj.mp hv
    have hm : multiplicity p a = m := by omega
    exact isUnit_away_mk_of_multiplicity_eq hp hpHom haHom ha0 hm
  · rintro ⟨u, rfl⟩
    let _ : IsDomain (HomogeneousLocalization.Away
        (homogeneousSubmodule ι k) p) :=
      HomogeneousLocalization.isDomain_away (homogeneousSubmodule ι k) hp
    have hu0 : (u : HomogeneousLocalization.Away
        (homogeneousSubmodule ι k) p) ≠ 0 := Units.ne_zero u
    have huInv0 : (↑(u⁻¹) : HomogeneousLocalization.Away
        (homogeneousSubmodule ι k) p) ≠ 0 := Units.ne_zero (u⁻¹)
    have hu := one_le_awayPrimeMultiplicityValuation hp hpHom hd hu0
    have huInv := one_le_awayPrimeMultiplicityValuation hp hpHom hd huInv0
    apply le_antisymm ?_ hu
    calc
      HomogeneousLocalization.awayPrimeMultiplicityValuation
          (homogeneousSubmodule ι k) hp (u :
            HomogeneousLocalization.Away (homogeneousSubmodule ι k) p) =
          HomogeneousLocalization.awayPrimeMultiplicityValuation
            (homogeneousSubmodule ι k) hp u * 1 := by rw [mul_one]
      _ ≤ HomogeneousLocalization.awayPrimeMultiplicityValuation
            (homogeneousSubmodule ι k) hp u *
          HomogeneousLocalization.awayPrimeMultiplicityValuation
            (homogeneousSubmodule ι k) hp (↑(u⁻¹) :
              HomogeneousLocalization.Away (homogeneousSubmodule ι k) p) :=
        by gcongr
      _ = 1 := by rw [← map_mul]; simp

/-- Denominator order one implies irreducibility in the degree-zero
homogeneous localization away from a nonconstant homogeneous prime. -/
theorem irreducible_of_awayPrimeMultiplicityValuation_eq_exp_one
    (hp : Prime p) (hpHom : p.IsHomogeneous d) (hd : d ≠ 0)
    {z : HomogeneousLocalization.Away (homogeneousSubmodule ι k) p}
    (hzVal : HomogeneousLocalization.awayPrimeMultiplicityValuation
      (homogeneousSubmodule ι k) hp z = exp (1 : ℤ)) :
    Irreducible z := by
  let v := HomogeneousLocalization.awayPrimeMultiplicityValuation
    (homogeneousSubmodule ι k) hp
  have hz : z ≠ 0 := by
    intro hz
    subst z
    have hzero : (0 : ℤᵐ⁰) = exp (1 : ℤ) := by
      simpa only [v, map_zero] using hzVal
    exact WithZero.coe_ne_zero hzero.symm
  have hzNonunit : ¬IsUnit z := by
    intro hzUnit
    have hzOne : v z = 1 :=
      (awayPrimeMultiplicityValuation_eq_one_iff_isUnit hp hpHom hd).2 hzUnit
    have hexp : exp (0 : ℤ) = exp (1 : ℤ) := by
      rw [exp_zero, ← hzOne]
      exact hzVal
    exact Int.zero_ne_one (exp_inj.mp hexp)
  refine ⟨hzNonunit, ?_⟩
  intro a b hab
  have ha0 : a ≠ 0 := by
    intro ha
    apply hz
    rw [hab, ha, zero_mul]
  have hb0 : b ≠ 0 := by
    intro hb
    apply hz
    rw [hab, hb, mul_zero]
  obtain ⟨qa, hva⟩ :=
    exists_awayPrimeMultiplicityValuation_eq_exp_nat hp hpHom hd ha0
  obtain ⟨qb, hvb⟩ :=
    exists_awayPrimeMultiplicityValuation_eq_exp_nat hp hpHom hd hb0
  have hvab := congrArg v hab
  rw [hzVal, map_mul, hva, hvb, ← exp_add] at hvab
  have hsum : (qa : ℤ) + qb = 1 := exp_inj.mp hvab.symm
  have hzero : qa = 0 ∨ qb = 0 := by omega
  rcases hzero with hqa | hqb
  · left
    apply (awayPrimeMultiplicityValuation_eq_one_iff_isUnit hp hpHom hd).1
    simpa [hqa] using hva
  · right
    apply (awayPrimeMultiplicityValuation_eq_one_iff_isUnit hp hpHom hd).1
    simpa [hqb] using hvb

end MvPolynomial
