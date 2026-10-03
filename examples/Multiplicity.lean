/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GradedRings

/-! # Prime powers and denominator order

Prime multiplicity gives a multiplicative integer-valued valuation. The
polynomial application uses a nonconstant homogeneous prime over a field.
Its coordinate type need not be finite. These examples use the aggregate import.
-/

namespace GradedRingsExamples.Multiplicity

noncomputable section

open Multiplicative WithZero

section Domain

variable {R : Type*} [CommRing R] [IsDomain R] [WfDvdMonoid R]
variable {p : R}

/-- A prime valuation is multiplicative on two powers of its prime. -/
public theorem value_of_two_prime_powers (hp : Prime p) (m n : ℕ) :
    PrimeMultiplicity.valuation hp (p ^ m * p ^ n) =
      exp (-(m : ℤ)) * exp (-(n : ℤ)) := by
  rw [map_mul, PrimeMultiplicity.valuation_apply_pow,
    PrimeMultiplicity.valuation_apply_pow]

end Domain

section Polynomial

variable {k ι : Type*} [Field k]
variable {p a : MvPolynomial ι k} {d n : ℕ}

attribute [local instance] MvPolynomial.gradedAlgebra

private theorem maximal_multiplicity_gives_unit (hp : Prime p)
    (hpHom : p.IsHomogeneous d) (haHom : a.IsHomogeneous (n * d))
    (ha0 : a ≠ 0) (hm : multiplicity p a = n) :
    IsUnit (HomogeneousLocalization.Away.mk
      (MvPolynomial.homogeneousSubmodule ι k) hpHom n a haHom) :=
  MvPolynomial.isUnit_away_mk_of_multiplicity_eq hp hpHom haHom ha0 hm

private theorem order_one_has_unit_factor (hp : Prime p)
    (hpHom : p.IsHomogeneous d) (hd : d ≠ 0)
    {z x y : HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule ι k) p}
    (hz : HomogeneousLocalization.awayPrimeMultiplicityValuation
      (MvPolynomial.homogeneousSubmodule ι k) hp z = exp (1 : ℤ))
    (hxy : z = x * y) : IsUnit x ∨ IsUnit y :=
  (MvPolynomial.irreducible_of_awayPrimeMultiplicityValuation_eq_exp_one
    hp hpHom hd hz).2 hxy

end Polynomial

#print axioms value_of_two_prime_powers
#print axioms maximal_multiplicity_gives_unit
#print axioms order_one_has_unit_factor

end

end GradedRingsExamples.Multiplicity
