/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GradedRings.VeroneseFinite

@[expose] public section

set_option warningAsError true
set_option linter.style.haveILetI false

noncomputable section

namespace VeroneseFiniteClient

universe u v

variable {S : Type u} [CommRing S] {σ : Type v} [SetLike σ S]
  [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮]

theorem generic_usage [Algebra.FiniteType (𝒮 0) S] (n : ℕ) (hn : 0 < n) :
    (GradedRing.Veronese.inclusion 𝒮 n).Finite :=
  GradedRing.Veronese.inclusion_finite 𝒮 n hn

example [Algebra.FiniteType (𝒮 0) S] (n : ℕ) (hn : 0 < n) :
    letI : Algebra (GradedRing.Veronese.VeroneseRing 𝒮 n) S :=
      (GradedRing.Veronese.inclusion 𝒮 n).toAlgebra
    Module.Finite (GradedRing.Veronese.VeroneseRing 𝒮 n) S :=
  GradedRing.Veronese.inclusion_finite 𝒮 n hn

example [Algebra.FiniteType (𝒮 0) S] :
    (GradedRing.Veronese.inclusion 𝒮 1).Finite :=
  GradedRing.Veronese.inclusion_finite 𝒮 1 (by decide)

example (hempty : Algebra.adjoin (𝒮 0) (∅ : Set S) = ⊤)
    (n : ℕ) (hn : 0 < n) : (GradedRing.Veronese.inclusion 𝒮 n).Finite := by
  letI : Algebra.FiniteType (𝒮 0) S := ⟨⟨∅, by simpa using hempty⟩⟩
  exact GradedRing.Veronese.inclusion_finite 𝒮 n hn

example (hzero : ∀ x : S, x ∈ 𝒮 0) (n : ℕ) (hn : 0 < n) :
    (GradedRing.Veronese.inclusion 𝒮 n).Finite := by
  have hsur : Function.Surjective (algebraMap (𝒮 0) S) := by
    intro x
    exact ⟨⟨x, hzero x⟩, rfl⟩
  letI : Algebra.FiniteType (𝒮 0) S :=
    RingHom.finiteType_algebraMap.mp
      (RingHom.FiniteType.of_surjective (algebraMap (𝒮 0) S) hsur)
  exact GradedRing.Veronese.inclusion_finite 𝒮 n hn

example [Subsingleton S] (n : ℕ) (hn : 0 < n) :
    (GradedRing.Veronese.inclusion 𝒮 n).Finite := by
  have hsur : Function.Surjective (algebraMap (𝒮 0) S) := by
    intro x
    have hx : x = 0 := Subsingleton.elim x 0
    exact ⟨⟨x, hx ▸ zero_mem (𝒮 0)⟩, rfl⟩
  letI : Algebra.FiniteType (𝒮 0) S :=
    RingHom.finiteType_algebraMap.mp
      (RingHom.FiniteType.of_surjective (algebraMap (𝒮 0) S) hsur)
  exact GradedRing.Veronese.inclusion_finite 𝒮 n hn

example [Algebra.FiniteType (𝒮 0) S] (x : S) (hx : x ^ 2 = 0)
    (n : ℕ) (hn : 0 < n) :
    (GradedRing.Veronese.inclusion 𝒮 n).Finite ∧ x ^ 2 = 0 :=
  ⟨GradedRing.Veronese.inclusion_finite 𝒮 n hn, hx⟩

end VeroneseFiniteClient
