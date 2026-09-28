/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import GradedRings

set_option warningAsError true

noncomputable section

namespace GradedRingsTest.RootClient

universe u v w x

section SymmetricAlgebra

variable {R : Type u} {M : Type v} {N : Type w}
variable [CommSemiring R] [AddCommMonoid M] [Module R M]
variable [AddCommMonoid N] [Module R N]

@[instance_reducible] private def symmetric_grading :
    GradedAlgebra (SymmetricAlgebra.homogeneousSubmodule (R := R) (M := M)) :=
  SymmetricAlgebra.gradedAlgebra

private def symmetric_graded_map (f : M →ₗ[R] N) :
    SymmetricAlgebra.homogeneousSubmodule (R := R) (M := M) →ₐᵍ[R]
      SymmetricAlgebra.homogeneousSubmodule (R := R) (M := N) :=
  SymmetricAlgebra.gradedMap f

variable {I : Type x}

attribute [local instance] MvPolynomial.gradedAlgebra

private theorem basis_coordinate_degree (b : Module.Basis I R M) {n : ℕ}
    {s : SymmetricAlgebra R M}
    (hs : s ∈ SymmetricAlgebra.homogeneousSubmodule (R := R) (M := M) n) :
    SymmetricAlgebra.equivMvPolynomial b s ∈
      MvPolynomial.homogeneousSubmodule I R n :=
  SymmetricAlgebra.equivMvPolynomial_mem_homogeneousSubmodule b hs

private def basis_coordinate_graded_map (b : Module.Basis I R M) :
    SymmetricAlgebra.homogeneousSubmodule (R := R) (M := M) →ₐᵍ[R]
      MvPolynomial.homogeneousSubmodule I R :=
  SymmetricAlgebra.equivMvPolynomialGradedHom b

end SymmetricAlgebra

section PrimeMultiplicity

open Multiplicative WithZero

variable {A : Type u} [CommRing A] [IsDomain A] [WfDvdMonoid A]
variable {p : A}

private theorem prime_power_valuation (hp : Prime p) (n : ℕ) :
    PrimeMultiplicity.valuation hp (p ^ n) = exp (-(n : ℤ)) :=
  PrimeMultiplicity.valuation_apply_pow hp n

variable {ι : Type v} {σ : Type w}
variable [SetLike σ A] [AddSubgroupClass σ A]
variable [AddCommMonoid ι] [DecidableEq ι]
variable (𝒜 : ι → σ) [GradedRing 𝒜]

private def homogeneous_away_valuation (hp : Prime p) :
    Valuation (HomogeneousLocalization.Away 𝒜 p) ℤᵐ⁰ :=
  HomogeneousLocalization.awayPrimeMultiplicityValuation 𝒜 hp

private theorem homogeneous_away_mk {d : ι} (hp : Prime p)
    (hpHom : p ∈ 𝒜 d) (n : ℕ) (a : A) (ha : a ∈ 𝒜 (n • d))
    (ha0 : a ≠ 0) :
    HomogeneousLocalization.awayPrimeMultiplicityValuation 𝒜 hp
        (HomogeneousLocalization.Away.mk 𝒜 hpHom n a ha) =
      exp ((n : ℤ) - multiplicity p a) :=
  HomogeneousLocalization.awayPrimeMultiplicityValuation_mk 𝒜 hp hpHom n a ha ha0

end PrimeMultiplicity

section MultivariatePolynomial

open Multiplicative WithZero

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type u} {ι : Type v} [Field k]
variable {p a : MvPolynomial ι k} {d n : ℕ}

private theorem homogeneous_degree_bound (hp : Prime p)
    (hpHom : p.IsHomogeneous d) (hd : d ≠ 0)
    (haHom : a.IsHomogeneous (n * d)) (ha0 : a ≠ 0) :
    multiplicity p a ≤ n :=
  MvPolynomial.multiplicity_le_of_isHomogeneous hp hpHom hd haHom ha0

private theorem homogeneous_away_unit_criterion (hp : Prime p)
    (hpHom : p.IsHomogeneous d) (hd : d ≠ 0)
    {z : HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule ι k) p} :
    HomogeneousLocalization.awayPrimeMultiplicityValuation
        (MvPolynomial.homogeneousSubmodule ι k) hp z = 1 ↔ IsUnit z :=
  MvPolynomial.awayPrimeMultiplicityValuation_eq_one_iff_isUnit hp hpHom hd

private theorem homogeneous_away_order_one_irreducible (hp : Prime p)
    (hpHom : p.IsHomogeneous d) (hd : d ≠ 0)
    {z : HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule ι k) p}
    (hz : HomogeneousLocalization.awayPrimeMultiplicityValuation
      (MvPolynomial.homogeneousSubmodule ι k) hp z = exp (1 : ℤ)) :
    Irreducible z :=
  MvPolynomial.irreducible_of_awayPrimeMultiplicityValuation_eq_exp_one hp hpHom hd hz

end MultivariatePolynomial

section DegreeMultiplyingLocalization

variable {A : Type u} {B : Type v} {σ : Type w} {τ : Type x}
variable [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  (ℬ : ℕ → τ) [GradedRing ℬ]

private def homogeneous_localization_degree_mul_map (f : A →+* B) (d : ℕ)
    (hdeg : ∀ n a, a ∈ 𝒜 n → f a ∈ ℬ (d * n))
    {P : Submonoid A} {Q : Submonoid B} (hPQ : P ≤ Q.comap f) :
    HomogeneousLocalization 𝒜 P →+* HomogeneousLocalization ℬ Q :=
  HomogeneousLocalization.mapDegreeMul 𝒜 ℬ f d hdeg hPQ

end DegreeMultiplyingLocalization

section Veronese

variable {S : Type u} [CommRing S] {σ : Type v} [SetLike σ S]
  [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮]

private def selected_veronese_inclusion (n : ℕ) :
    GradedRing.Veronese.VeroneseRing 𝒮 n →+* S :=
  GradedRing.Veronese.inclusion 𝒮 n

end Veronese

end GradedRingsTest.RootClient
