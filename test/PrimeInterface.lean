/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import GradedRings.MvPolynomialAway

/-! # Ordinary native direct-import prime-multiplicity construction checks -/

namespace GradedRingsTest.PrimeInterface

set_option warningAsError true

noncomputable section

open Multiplicative WithZero

universe u v w x

section Prime

variable {R : Type u} [CommRing R] [IsDomain R] [WfDvdMonoid R]
variable {p : R}

private theorem valuation_computation (hp : Prime p) (r : R) :
    PrimeMultiplicity.valuation hp r = PrimeMultiplicity.valuationDef p r := rfl

omit [WfDvdMonoid R] in
private theorem valuationDef_pow_simp (hp : Prime p) (n : ℕ) :
    PrimeMultiplicity.valuationDef p (p ^ n) = exp (-(n : ℤ)) := by simp [hp]

private theorem valuation_pow_simp (hp : Prime p) (n : ℕ) :
    PrimeMultiplicity.valuation hp (p ^ n) = exp (-(n : ℤ)) := by simp [hp]

private theorem valuation_pow_explicit (hp : Prime p) (n : ℕ) :
    PrimeMultiplicity.valuation hp (p ^ n) = exp (-(n : ℤ)) :=
  PrimeMultiplicity.valuation_apply_pow hp n

private theorem full_valuation (hp : Prime p) :
    PrimeMultiplicity.valuation hp =
      ({ toFun := PrimeMultiplicity.valuationDef p
         map_zero' := PrimeMultiplicity.valuationDef_zero p
         map_one' := PrimeMultiplicity.valuationDef_one hp
         map_mul' := PrimeMultiplicity.valuationDef_mul hp
         map_add_le_max' := PrimeMultiplicity.valuationDef_add_le_max hp } :
        Valuation R ℤᵐ⁰) := rfl

variable {S : Submonoid R} {B : Type v} [CommRing B] [Algebra R B]
  [IsLocalization S B]

private def original_localization (hp : Prime p) (hS : S ≤ nonZeroDivisors R) :
    Valuation B ℤᵐ⁰ :=
  (PrimeMultiplicity.valuation hp).extendToLocalization (B := B)
    (show S ≤ (PrimeMultiplicity.valuation hp).supp.primeCompl from by
      intro s hs
      change s ∉ (PrimeMultiplicity.valuation hp).supp
      rw [Valuation.mem_supp_iff]
      exact PrimeMultiplicity.valuation_ne_zero hp
        (nonZeroDivisors.coe_ne_zero ⟨s, hS hs⟩))

private theorem localization_complete_construction (hp : Prime p)
    (hS : S ≤ nonZeroDivisors R) :
    PrimeMultiplicity.localizationValuation (B := B) hp hS =
      original_localization (B := B) hp hS := rfl

private theorem localization_fraction (hp : Prime p) (hS : S ≤ nonZeroDivisors R)
    (a : R) (s : S) :
    PrimeMultiplicity.localizationValuation (B := B) hp hS (IsLocalization.mk' B a s) =
      PrimeMultiplicity.valuation hp a * (PrimeMultiplicity.valuation hp s)⁻¹ :=
  PrimeMultiplicity.localizationValuation_mk' hp hS a s

private theorem away_complete_construction (hp : Prime p)
    {C : Type v} [CommRing C] [Algebra R C] [IsLocalization.Away p C] :
    PrimeMultiplicity.awayValuation (B := C) hp =
      PrimeMultiplicity.localizationValuation hp
        (PrimeMultiplicity.powers_le_nonZeroDivisors hp) := rfl

end Prime

section Homogeneous

variable {A : Type u} {ι : Type v} {σ : Type w}
variable [CommRing A] [IsDomain A] [WfDvdMonoid A]
variable [SetLike σ A] [AddSubgroupClass σ A]
variable [AddCommMonoid ι] [DecidableEq ι]
variable (𝒜 : ι → σ) [GradedRing 𝒜] {p : A}

private theorem homogeneous_complete_construction (hp : Prime p) :
    HomogeneousLocalization.awayPrimeMultiplicityValuation 𝒜 hp =
      (PrimeMultiplicity.awayValuation (B := Localization.Away p) hp).comap
        (algebraMap (HomogeneousLocalization.Away 𝒜 p) (Localization.Away p)) := rfl

omit [WfDvdMonoid A] in
private theorem homogeneous_domain (hp : Prime p) :
    IsDomain (HomogeneousLocalization.Away 𝒜 p) :=
  HomogeneousLocalization.isDomain_away 𝒜 hp

end Homogeneous

section Polynomial

variable {k : Type u} {ι : Type v} [Field k]
variable {p a : MvPolynomial ι k} {d n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra

private theorem polynomial_degree (hp : Prime p) (hpHom : p.IsHomogeneous d)
    (hd : d ≠ 0) (haHom : a.IsHomogeneous (n * d)) (ha0 : a ≠ 0) :
    multiplicity p a ≤ n :=
  MvPolynomial.multiplicity_le_of_isHomogeneous hp hpHom hd haHom ha0

private theorem unit_criterion (hp : Prime p) (hpHom : p.IsHomogeneous d)
    (hd : d ≠ 0)
    {z : HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule ι k) p} :
    HomogeneousLocalization.awayPrimeMultiplicityValuation
      (MvPolynomial.homogeneousSubmodule ι k) hp z = 1 ↔ IsUnit z :=
  MvPolynomial.awayPrimeMultiplicityValuation_eq_one_iff_isUnit hp hpHom hd

private theorem order_one_irreducible (hp : Prime p) (hpHom : p.IsHomogeneous d)
    (hd : d ≠ 0)
    {z : HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule ι k) p}
    (hz : HomogeneousLocalization.awayPrimeMultiplicityValuation
      (MvPolynomial.homogeneousSubmodule ι k) hp z = exp (1 : ℤ)) :
    Irreducible z :=
  MvPolynomial.irreducible_of_awayPrimeMultiplicityValuation_eq_exp_one hp hpHom hd hz

end Polynomial

#print axioms PrimeMultiplicity.localizationValuation
#print axioms HomogeneousLocalization.isDomain_away
#print axioms MvPolynomial.awayPrimeMultiplicityValuation_eq_one_iff_isUnit
#print axioms MvPolynomial.irreducible_of_awayPrimeMultiplicityValuation_eq_exp_one

end

end GradedRingsTest.PrimeInterface
