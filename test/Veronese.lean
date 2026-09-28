/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GradedRings.Veronese

@[expose] public section

/-! # Ordinary-import client for selected-component Veronese rings -/

set_option warningAsError true

noncomputable section

namespace GradedRingsTest.Veronese

open GradedRing.Veronese

universe u v

variable {S : Type u} [CommRing S] {σ : Type v} [SetLike σ S]
  [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮]

example (n j : ℕ) (a : 𝒮 (n * j)) :
    ∃ x : VeroneseRing 𝒮 n, x ∈ component 𝒮 n j ∧ inclusion 𝒮 n x = a :=
  exists_component 𝒮 n j a

example (n : ℕ) (hn : 0 < n) (x y : VeroneseRing 𝒮 n)
    (h : inclusion 𝒮 n x = inclusion 𝒮 n y) : x = y :=
  inclusion_injective 𝒮 n hn h

example (a : 𝒮 6) :
    ∃ x : VeroneseRing 𝒮 2, x ∈ component 𝒮 2 3 ∧ inclusion 𝒮 2 x = a := by
  simpa using exists_component 𝒮 2 3 a

example (n : ℕ) (hn : 0 < n) : component 𝒮 n 0 ≃+* 𝒮 0 :=
  zeroRingEquiv 𝒮 n hn

example : component 𝒮 1 0 ≃+* 𝒮 0 :=
  zeroRingEquiv 𝒮 1 (by decide)

end GradedRingsTest.Veronese
