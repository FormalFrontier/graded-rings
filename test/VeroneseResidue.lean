/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GradedRings.VeroneseResidue

@[expose] public section

set_option warningAsError true
set_option linter.style.haveILetI false

noncomputable section

namespace VeroneseResidueClient

universe u v

variable {S : Type u} [CommRing S] {σ : Type v} [SetLike σ S]
  [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮]

example (n r : ℕ) (hn : 0 < n) (hr : r < n)
    (a : GradedRing.Veronese.VeroneseRing 𝒮 n) (x : S) :
    letI : Algebra (GradedRing.Veronese.VeroneseRing 𝒮 n) S :=
      (GradedRing.Veronese.inclusion 𝒮 n).toAlgebra
    GradedRing.Veronese.residueProjection 𝒮 n r hn hr (a • x) =
      a • GradedRing.Veronese.residueProjection 𝒮 n r hn hr x := by
  letI : Algebra (GradedRing.Veronese.VeroneseRing 𝒮 n) S :=
    (GradedRing.Veronese.inclusion 𝒮 n).toAlgebra
  exact map_smul (GradedRing.Veronese.residueProjection 𝒮 n r hn hr) a x

example (n r d : ℕ) (hn : 0 < n) (hr : r < n) {x : S} (hx : x ∈ 𝒮 d) :
    GradedRing.Veronese.residueProjection 𝒮 n r hn hr x =
      if d % n = r then x else 0 :=
  GradedRing.Veronese.residueProjection_of_mem 𝒮 n r d hn hr hx

example (n r : ℕ) (hn : 0 < n) (hr : r < n) (x : S) :
    letI : Algebra (GradedRing.Veronese.VeroneseRing 𝒮 n) S :=
      (GradedRing.Veronese.inclusion 𝒮 n).toAlgebra
    x ∈ (GradedRing.Veronese.residueProjection 𝒮 n r hn hr).range ↔
      ∀ d : ℕ, d % n ≠ r → DirectSum.decompose 𝒮 x d = 0 :=
  GradedRing.Veronese.mem_residueProjection_range_iff 𝒮 n r hn hr x

example (n r : ℕ) (hn : 0 < n) (hr : r < n) (x : S) :
    GradedRing.Veronese.residueProjection 𝒮 n r hn hr
      (GradedRing.Veronese.residueProjection 𝒮 n r hn hr x) =
      GradedRing.Veronese.residueProjection 𝒮 n r hn hr x :=
  GradedRing.Veronese.residueProjection_idempotent 𝒮 n r hn hr x

example [Algebra.FiniteType (𝒮 0) S] (n r : ℕ) (hn : 0 < n) (hr : r < n) :
    letI : Algebra (GradedRing.Veronese.VeroneseRing 𝒮 n) S :=
      (GradedRing.Veronese.inclusion 𝒮 n).toAlgebra
    Module.Finite (GradedRing.Veronese.VeroneseRing 𝒮 n)
      (GradedRing.Veronese.residueProjection 𝒮 n r hn hr).range :=
  GradedRing.Veronese.residueProjection_range_finite_of_finiteType 𝒮 n r hn hr

example (x : S) :
    GradedRing.Veronese.residueProjection 𝒮 1 0 (by decide) (by decide) x = x := by
  apply (GradedRing.Veronese.residueProjectionAdd_eq_iff 𝒮 1 0 x).mpr
  intro d hd
  exact (hd (Nat.mod_one d)).elim

example [Subsingleton S] (n r : ℕ) (hn : 0 < n) (hr : r < n) :
    letI : Algebra (GradedRing.Veronese.VeroneseRing 𝒮 n) S :=
      (GradedRing.Veronese.inclusion 𝒮 n).toAlgebra
    Module.Finite (GradedRing.Veronese.VeroneseRing 𝒮 n)
      (GradedRing.Veronese.residueProjection 𝒮 n r hn hr).range := by
  have hsur : Function.Surjective (algebraMap (𝒮 0) S) := by
    intro x
    have hx : x = 0 := Subsingleton.elim x 0
    exact ⟨⟨x, hx ▸ zero_mem (𝒮 0)⟩, rfl⟩
  letI : Algebra.FiniteType (𝒮 0) S :=
    RingHom.finiteType_algebraMap.mp
      (RingHom.FiniteType.of_surjective (algebraMap (𝒮 0) S) hsur)
  exact GradedRing.Veronese.residueProjection_range_finite_of_finiteType 𝒮 n r hn hr

end VeroneseResidueClient
