/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GradedRings.VeroneseResidueModule

@[expose] public section

set_option warningAsError true
set_option linter.style.haveILetI false

noncomputable section

namespace VeroneseResidueModuleClient

open DirectSum

universe u v

variable {S : Type u} [CommRing S] {σ : Type v} [SetLike σ S]
  [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮]

private theorem clientAction (n r : ℕ) :
    Nonempty (Module (GradedRing.Veronese.VeroneseRing 𝒮 n)
      (GradedRing.Veronese.ResidueModule 𝒮 n r)) := ⟨inferInstance⟩

private theorem clientConvolution (n r i k : ℕ) (a : 𝒮 (n * i)) (b : 𝒮 (n * k + r)) :
    DirectSum.of (fun j : ℕ => 𝒮 (n * j)) i a •
      DirectSum.of (fun j : ℕ => 𝒮 (n * j + r)) k b =
        DirectSum.of (fun j : ℕ => 𝒮 (n * j + r)) (i + k)
          (⟨(a : S) * b, by
            simpa only [mul_add, add_assoc] using
              (SetLike.GradedMul.mul_mem a.property b.property :
                (a : S) * b ∈ 𝒮 (n * i + (n * k + r)))⟩) :=
  GradedRing.Veronese.of_smul_of_residue 𝒮 n r i k a b

private theorem clientEvaluation (n r k : ℕ) (b : 𝒮 (n * k + r)) :
    GradedRing.Veronese.residueEvaluation 𝒮 n r
      (DirectSum.of (fun j : ℕ => 𝒮 (n * j + r)) k b) = b := by
  simp

private theorem clientInjectivity (n r : ℕ) (hn : 0 < n) :
    Function.Injective (GradedRing.Veronese.residueEvaluation 𝒮 n r) :=
  GradedRing.Veronese.residueEvaluation_injective 𝒮 n r hn

private theorem clientRange (n r : ℕ) (hn : 0 < n) (hr : r < n) :
    letI : Algebra (GradedRing.Veronese.VeroneseRing 𝒮 n) S :=
      (GradedRing.Veronese.inclusion 𝒮 n).toAlgebra
    (GradedRing.Veronese.residueEvaluation 𝒮 n r).range =
      (GradedRing.Veronese.residueProjection 𝒮 n r hn hr).range :=
  GradedRing.Veronese.residueEvaluation_range_eq 𝒮 n r hn hr

private theorem clientEquivForward (n r : ℕ) (hn : 0 < n) (hr : r < n)
    (x : GradedRing.Veronese.ResidueModule 𝒮 n r) :
    letI : Algebra (GradedRing.Veronese.VeroneseRing 𝒮 n) S :=
      (GradedRing.Veronese.inclusion 𝒮 n).toAlgebra
    ((GradedRing.Veronese.residueEvaluationEquiv 𝒮 n r hn hr x :
      (GradedRing.Veronese.residueProjection 𝒮 n r hn hr).range) : S) =
        GradedRing.Veronese.residueEvaluation 𝒮 n r x := by
  simp

private theorem clientFiniteAmbient (n r : ℕ) (hn : 0 < n) (hr : r < n) :
    letI : Algebra (GradedRing.Veronese.VeroneseRing 𝒮 n) S :=
      (GradedRing.Veronese.inclusion 𝒮 n).toAlgebra
    [Module.Finite (GradedRing.Veronese.VeroneseRing 𝒮 n) S] →
      Module.Finite (GradedRing.Veronese.VeroneseRing 𝒮 n)
        (GradedRing.Veronese.ResidueModule 𝒮 n r) :=
  GradedRing.Veronese.residueModule_finite 𝒮 n r hn hr

private theorem clientFiniteType [Algebra.FiniteType (𝒮 0) S]
    (n r : ℕ) (hn : 0 < n) (hr : r < n) :
    Module.Finite (GradedRing.Veronese.VeroneseRing 𝒮 n)
      (GradedRing.Veronese.ResidueModule 𝒮 n r) :=
  GradedRing.Veronese.residueModule_finite_of_finiteType 𝒮 n r hn hr

/-- The residue evaluation at index one is a bijection. -/
public theorem clientIndexOne :
    Function.Bijective (GradedRing.Veronese.residueEvaluation 𝒮 1 0) := by
  letI : Algebra (GradedRing.Veronese.VeroneseRing 𝒮 1) S :=
    (GradedRing.Veronese.inclusion 𝒮 1).toAlgebra
  refine ⟨GradedRing.Veronese.residueEvaluation_injective 𝒮 1 0 (by decide), ?_⟩
  intro x
  have hx : x ∈ (GradedRing.Veronese.residueProjection 𝒮 1 0
      (by decide) (by decide)).range := by
    apply (GradedRing.Veronese.mem_residueProjection_range_iff 𝒮 1 0
      (by decide) (by decide) x).mpr
    intro d hd
    exact (hd (Nat.mod_one d)).elim
  rw [← GradedRing.Veronese.residueEvaluation_range_eq 𝒮 1 0
    (by decide) (by decide)] at hx
  exact hx

private theorem clientZeroRing [Subsingleton S] (n r : ℕ) (hn : 0 < n)
    (hr : r < n) :
    Module.Finite (GradedRing.Veronese.VeroneseRing 𝒮 n)
      (GradedRing.Veronese.ResidueModule 𝒮 n r) := by
  have hsur : Function.Surjective (algebraMap (𝒮 0) S) := by
    intro x
    have hx : x = 0 := Subsingleton.elim x 0
    exact ⟨⟨x, hx ▸ zero_mem (𝒮 0)⟩, rfl⟩
  letI : Algebra.FiniteType (𝒮 0) S :=
    RingHom.finiteType_algebraMap.mp
      (RingHom.FiniteType.of_surjective (algebraMap (𝒮 0) S) hsur)
  exact GradedRing.Veronese.residueModule_finite_of_finiteType 𝒮 n r hn hr

end VeroneseResidueModuleClient
