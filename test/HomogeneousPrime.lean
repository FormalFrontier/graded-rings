/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import GradedRings.HomogeneousPrime

namespace GradedRing

universe u v

variable {A : Type u} [CommRing A]
variable {σ : Type v} [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℤ → σ) [GradedRing 𝒜]

private def degree_zero_prime_equiv {d : ℤ} (u : Aˣ) (hu : (u : A) ∈ 𝒜 d) (hd : 0 < d) :
    {P : Ideal A // P.IsPrime ∧ P.IsHomogeneous 𝒜} ≃
      {q : Ideal (𝒜 0) // q.IsPrime} :=
  homogeneousPrimeEquivDegreeZeroPrime 𝒜 u hu hd

private theorem radical_extension_prime {d : ℤ} (u : Aˣ) (hu : (u : A) ∈ 𝒜 d) (hd : 0 < d)
    (q : Ideal (𝒜 0)) (hq : q.IsPrime) :
    (q.map (algebraMap (𝒜 0) A)).radical.IsPrime :=
  radical_map_degreeZero_isPrime 𝒜 u hu hd q hq

private theorem radical_comap_map {d : ℤ} (u : Aˣ) (hu : (u : A) ∈ 𝒜 d) (hd : 0 < d)
    (P : Ideal A) (hPprime : P.IsPrime) (hPhom : P.IsHomogeneous 𝒜) :
    ((P.comap (algebraMap (𝒜 0) A)).map
      (algebraMap (𝒜 0) A)).radical = P :=
  radical_map_comap_degreeZero 𝒜 u hu hd P hPprime hPhom

end GradedRing
