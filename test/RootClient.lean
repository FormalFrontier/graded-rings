/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GradedRings

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

/-- The valuation of a power of a prime is its negative exponent. -/
public theorem prime_power_valuation (hp : Prime p) (n : ℕ) :
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

section CoherentTailVeronese

variable {R : Type u} {S : Type v} {σ : Type w} {τ : Type x}
variable [CommRing R] [CommRing S]
  [SetLike σ R] [AddSubgroupClass σ R]
  [SetLike τ S] [AddSubgroupClass τ S]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
  {N : ℕ}

private theorem coherent_tail_selected_zero_and_inverse
    (E : GradedRing.Veronese.CoherentTail.TailEquiv 𝒜 ℬ N)
    (n : ℕ) (hNn : N ≤ n) (hn : 0 < n) :
    (GradedRing.Veronese.zeroRingEquiv ℬ n hn).toRingHom.comp
        (GradedRingHom.gradedZeroRingHom (E.selectedGradedHom n hNn)) =
      E.zero.toRingHom.comp (GradedRing.Veronese.zeroRingEquiv 𝒜 n hn).toRingHom ∧
    (E.selectedGradedHomSymm n hNn).comp (E.selectedGradedHom n hNn) =
      GradedRingHom.id (GradedRing.Veronese.component 𝒜 n) :=
  ⟨E.selected_zero n hNn hn, E.selectedGradedHomSymm_comp n hNn⟩

end CoherentTailVeronese

section VeroneseDegreeOne

variable {S : Type u} [CommRing S] {σ : Type v} [SetLike σ S]
  [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮]

private theorem veronese_degree_one_generated (n : ℕ) (hn : 0 < n)
    (hgen : Algebra.adjoin (𝒮 0) (𝒮 1 : Set S) = ⊤) :
    Algebra.adjoin (GradedRing.Veronese.component 𝒮 n 0)
      (GradedRing.Veronese.component 𝒮 n 1 :
        Set (GradedRing.Veronese.VeroneseRing 𝒮 n)) = ⊤ :=
  GradedRing.Veronese.adjoin_component_one_eq_top 𝒮 n hn hgen

end VeroneseDegreeOne

section HomogeneousLifts

variable {S : Type u} [CommRing S] {σ : Type v} [SetLike σ S]
  [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮]

private theorem homogeneous_polynomial_lift
    (hgen : Algebra.adjoin (𝒮 0) (𝒮 1 : Set S) = ⊤)
    {m : ℕ} {s : S} (hs : s ∈ 𝒮 m) :
    ∃ p : MvPolynomial (𝒮 1) (𝒮 0), p.IsHomogeneous m ∧
      MvPolynomial.aeval (fun a : 𝒮 1 => (a : S)) p = s :=
  MvPolynomial.exists_isHomogeneous_aeval 𝒮 hgen hs

end HomogeneousLifts

section WeightedBlocks

variable {ι : Type*} [Fintype ι]

private theorem weighted_blocks_root (w : ι → ℕ) (hw : ∀ i, 0 < w i)
    (k : ℕ) (f : ι →₀ ℕ)
    (hf : Finsupp.weight w f = k * Finsupp.weightedBlockSize w) :
    0 < Finsupp.weightedBlockSize w ∧
      ∃ blocks : Fin k → (ι →₀ ℕ),
        (∑ j, blocks j) = f ∧
          ∀ j, Finsupp.weight w (blocks j) = Finsupp.weightedBlockSize w :=
  ⟨Finsupp.weightedBlockSize_pos w hw,
    Finsupp.exists_weightedBlocks w hw k f hf⟩

end WeightedBlocks

section WeightedEvaluation

variable {ι S σ : Type*} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮] (w : ι → ℕ) (x : ∀ i : ι, 𝒮 (w i))

private theorem weighted_evaluation_root (n : ℕ) (p : MvPolynomial ι (𝒮 0)) :
    MvPolynomial.aeval (fun i => (x i : S))
      (MvPolynomial.weightedHomogeneousComponent w n p) =
      (DirectSum.decompose 𝒮
        (MvPolynomial.aeval (fun i => (x i : S)) p) n : S) :=
  MvPolynomial.aeval_weightedHomogeneousComponent 𝒮 w x n p

end WeightedEvaluation

section WeightedBlockAdjoin

variable {ι R : Type*} [Fintype ι] [CommSemiring R]

private theorem weightedBlockAdjoin_root (w : ι → ℕ) (hw : ∀ i, 0 < w i)
    (k : ℕ) {p : MvPolynomial ι R}
    (hp : p.IsWeightedHomogeneous w (k * Finsupp.weightedBlockSize w)) :
    p ∈ Algebra.adjoin R
      ((fun d : ι →₀ ℕ => MvPolynomial.monomial d (1 : R)) ''
        {d | Finsupp.weight w d = Finsupp.weightedBlockSize w}) :=
  MvPolynomial.IsWeightedHomogeneous.mem_adjoin_weightedBlockSize w hw k hp

end WeightedBlockAdjoin

section FiniteVeronese

variable {ι S σ : Type*} [Fintype ι] [CommRing S]
variable [SetLike σ S] [AddSubgroupClass σ S]
variable (𝒮 : ℕ → σ) [GradedRing 𝒮]

private theorem finiteVeronese_root (weights : ι → ℕ)
    (weights_pos : ∀ i, 0 < weights i) (generators : ∀ i, 𝒮 (weights i))
    (hgen : Algebra.adjoin (𝒮 0) (Set.range (fun i => (generators i : S))) = ⊤) :
    ∃ T : Set (GradedRing.Veronese.VeroneseRing 𝒮 (Finsupp.weightedBlockSize weights)),
      T.Finite ∧
      T ⊆ (GradedRing.Veronese.component 𝒮 (Finsupp.weightedBlockSize weights) 1 : Set _) ∧
      Algebra.adjoin
        (GradedRing.Veronese.component 𝒮 (Finsupp.weightedBlockSize weights) 0) T = ⊤ :=
  GradedRing.Veronese.exists_finite_degree_one_generators
    𝒮 weights weights_pos generators hgen

end FiniteVeronese

section WeightedVeroneseGenerators

variable {ι : Type u} {R : Type v} [Finite ι] [CommSemiring R]

private theorem weightedVeroneseGenerators_root (weights : ι → ℕ)
    (index : ℕ) (index_pos : 0 < index) :
    ∃ T : Finset (MvPolynomial ι R),
      (∀ p ∈ T, ∃ j : ℕ, p.IsWeightedHomogeneous weights (index * j)) ∧
      ∀ j : ℕ, ∀ p : MvPolynomial ι R,
        p.IsWeightedHomogeneous weights (index * j) →
          p ∈ Algebra.adjoin R (T : Set (MvPolynomial ι R)) :=
  MvPolynomial.exists_finset_weightedVeronese_generators weights index index_pos

end WeightedVeroneseGenerators

section VeroneseFiniteType

variable {S : Type u} {σ : Type v} {ι : Type w} [CommRing S] [Finite ι]
variable [SetLike σ S] [AddSubgroupClass σ S]
variable (𝒮 : ℕ → σ) [GradedRing 𝒮]

private theorem veroneseFiniteType_root (weights : ι → ℕ)
    (generators : ∀ i : ι, 𝒮 (weights i))
    (hgen : Algebra.adjoin (𝒮 0) (Set.range (fun i => (generators i : S))) = ⊤)
    (index : ℕ) (index_pos : 0 < index) :
    Algebra.FiniteType (GradedRing.Veronese.component 𝒮 index 0)
      (GradedRing.Veronese.VeroneseRing 𝒮 index) :=
  GradedRing.Veronese.finiteType_of_finite_homogeneous_generators
    𝒮 weights generators hgen index index_pos

end VeroneseFiniteType

section VeroneseFinite

variable {S : Type u} [CommRing S] {σ : Type v} [SetLike σ S]
  [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮]

private theorem veroneseFinite_root [Algebra.FiniteType (𝒮 0) S]
    (n : ℕ) (hn : 0 < n) :
    (GradedRing.Veronese.inclusion 𝒮 n).Finite :=
  GradedRing.Veronese.inclusion_finite 𝒮 n hn

end VeroneseFinite

section VeroneseResidue

variable {S : Type u} [CommRing S] {σ : Type v} [SetLike σ S]
  [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮]

private theorem residueProjection_range_finite_root [Algebra.FiniteType (𝒮 0) S]
    (n r : ℕ) (hn : 0 < n) (hr : r < n) :
    letI : Algebra (GradedRing.Veronese.VeroneseRing 𝒮 n) S :=
      (GradedRing.Veronese.inclusion 𝒮 n).toAlgebra
    Module.Finite (GradedRing.Veronese.VeroneseRing 𝒮 n)
      (GradedRing.Veronese.residueProjection 𝒮 n r hn hr).range :=
  GradedRing.Veronese.residueProjection_range_finite_of_finiteType 𝒮 n r hn hr

end VeroneseResidue

section VeroneseResidueModule

variable {S : Type u} [CommRing S] {σ : Type v} [SetLike σ S]
  [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮]

private theorem residueModule_finite_root [Algebra.FiniteType (𝒮 0) S]
    (n r : ℕ) (hn : 0 < n) (hr : r < n) :
    Module.Finite (GradedRing.Veronese.VeroneseRing 𝒮 n)
      (GradedRing.Veronese.ResidueModule 𝒮 n r) :=
  GradedRing.Veronese.residueModule_finite_of_finiteType 𝒮 n r hn hr

end VeroneseResidueModule

section VeroneseZero

variable {S : Type u} [CommRing S] {σ : Type v} [SetLike σ S]
  [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮]

private def zeroRingEquivAll_root (n : ℕ) :
    GradedRing.Veronese.component 𝒮 n 0 ≃+* 𝒮 0 :=
  GradedRing.Veronese.zeroRingEquivAll 𝒮 n

private theorem finiteType_zero_root :
    Algebra.FiniteType (GradedRing.Veronese.component 𝒮 0 0)
      (GradedRing.Veronese.VeroneseRing 𝒮 0) :=
  GradedRing.Veronese.finiteType_zero 𝒮

end VeroneseZero

end GradedRingsTest.RootClient
