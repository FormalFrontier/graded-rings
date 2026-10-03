/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GradedRings.Localization
public import Mathlib.Algebra.MonoidAlgebra.Grading

set_option warningAsError true

noncomputable section

namespace GradedRingsTest

open DirectSum

universe u v w

variable {A : Type u} [CommRing A]
variable {ι : Type v} [DecidableEq ι] [AddCommGroup ι]
variable {σ : Type w} [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ι → σ) [GradedRing 𝒜]
variable (M : Submonoid A)
variable (hM : M ≤ SetLike.homogeneousSubmonoid 𝒜)

private theorem component_graded_monoid :
    SetLike.GradedMonoid (GradedLocalization.component (𝒜 := 𝒜) M) :=
  inferInstance

@[instance_reducible] private def component_graded_ring :
    GradedRing (GradedLocalization.component (𝒜 := 𝒜) M) :=
  GradedLocalization.gradedRing 𝒜 M hM

private def zero_component_equiv : HomogeneousLocalization 𝒜 M ≃+*
    GradedLocalization.zeroComponent (𝒜 := 𝒜) M :=
  GradedLocalization.homogeneousLocalizationEquivZeroComponent 𝒜 M

private theorem zero_component_equiv_val (x : HomogeneousLocalization 𝒜 M) :
    (GradedLocalization.homogeneousLocalizationEquivZeroComponent 𝒜 M x).1 =
      x.val := rfl

private def localization_decomposition :
    Localization M ≃+* ⨁ i, GradedLocalization.component (𝒜 := 𝒜) M i := by
  letI := GradedLocalization.gradedRing 𝒜 M hM
  exact DirectSum.decomposeRingEquiv (GradedLocalization.component (𝒜 := 𝒜) M)

section IntegerGradingClient

variable (R : Type*) [CommRing R]

local notation "B" => AddMonoidAlgebra R ℕ
local notation "𝓑" => AddMonoidAlgebra.gradeBy R (Nat.castAddMonoidHom ℤ)
local notation "t" => AddMonoidAlgebra.single (1 : ℕ) (1 : R)
local notation "W" => Submonoid.powers (t : B)

private theorem powers_le_homogeneous :
    W ≤ SetLike.homogeneousSubmonoid (𝓑 : ℤ → Submodule R B) := by
  rintro _ ⟨n, rfl⟩
  refine ⟨(n : ℤ), ?_⟩
  simpa using SetLike.pow_mem_graded n
    (AddMonoidAlgebra.single_mem_gradeBy
      (Nat.castAddMonoidHom ℤ) (1 : ℕ) (1 : R))

@[instance_reducible] private def integer_component_graded_ring : GradedRing
    (GradedLocalization.component (𝒜 := (𝓑 : ℤ → Submodule R B)) W) :=
  GradedLocalization.gradedRing _ _ (powers_le_homogeneous R)

/-- Inverting the degree-one monomial produces a degree-negative-one
homogeneous element. -/
private theorem negative_degree_monomial : Localization.mk (1 : B) ⟨t, Submonoid.mem_powers t⟩ ∈
    GradedLocalization.component (𝒜 := (𝓑 : ℤ → Submodule R B)) W (-1) := by
  refine ⟨1, ⟨1, ?_⟩,
    ⟨t, AddMonoidAlgebra.single_mem_gradeBy
      (Nat.castAddMonoidHom ℤ) (1 : ℕ) (1 : R)⟩,
    Submonoid.mem_powers t, rfl⟩
  norm_num
  exact SetLike.one_mem_graded (𝓑 : ℤ → Submodule R B)

/-- Inverting the degree-one monomial gives a nonzero negative-degree fraction. -/
public theorem negative_degree_monomial_nonzero : Localization.mk (1 : AddMonoidAlgebra ℤ ℕ)
    ⟨AddMonoidAlgebra.single (1 : ℕ) (1 : ℤ),
      Submonoid.mem_powers _⟩ ≠ 0 := by
  intro h
  rw [Localization.mk_eq_mk'_apply] at h
  rw [IsLocalization.mk'_eq_zero_iff
    (M := Submonoid.powers (AddMonoidAlgebra.single (1 : ℕ) (1 : ℤ)))
    (S := Localization
      (Submonoid.powers (AddMonoidAlgebra.single (1 : ℕ) (1 : ℤ))))] at h
  obtain ⟨m, hm⟩ := h
  obtain ⟨n, hn⟩ := m.2
  rw [← hn] at hm
  simp at hm

end IntegerGradingClient

section TrivialLocalization

local notation "B₀" => AddMonoidAlgebra (ZMod 1) ℕ
local notation "t₀" => AddMonoidAlgebra.single (1 : ℕ) (1 : ZMod 1)
local notation "W₀" => Submonoid.powers (t₀ : B₀)

private theorem zero_in_powers : 0 ∈ W₀ := by
  convert Submonoid.mem_powers (t₀ : B₀) using 1
  exact Subsingleton.elim _ _

@[instance_reducible] private def trivial_component_graded_ring :
    GradedRing (GradedLocalization.component
      (𝒜 := (AddMonoidAlgebra.gradeBy (ZMod 1) (Nat.castAddMonoidHom ℤ) :
        ℤ → Submodule (ZMod 1) B₀)) W₀) :=
  GradedLocalization.gradedRing _ _ (powers_le_homogeneous (ZMod 1))

end TrivialLocalization

end GradedRingsTest
