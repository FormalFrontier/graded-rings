/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GradedRings.Localization

/-! # Ordinary direct-import reduction checks for graded localization -/

set_option warningAsError true

noncomputable section

namespace GradedRingsTest.LocalizationInterface

universe u v w

variable {A : Type u} [CommRing A]
variable {ι : Type v} [DecidableEq ι] [AddCommGroup ι]
variable {σ : Type w} [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ι → σ) [GradedRing 𝒜] (M : Submonoid A)

/-- Homogeneous localization components consist of fractions of matching shifted degree. -/
public theorem componentCarrier (i : ι) (z : Localization M) :
    z ∈ GradedLocalization.component (𝒜 := 𝒜) M i ↔
      ∃ (j : ι) (a : 𝒜 (i + j)) (b : 𝒜 j) (hb : (b : A) ∈ M),
        z = Localization.mk (a : A) ⟨(b : A), hb⟩ :=
  Iff.rfl

private theorem componentConstructor (i : ι) :
    GradedLocalization.component (𝒜 := 𝒜) M i =
      { carrier := {z | ∃ (j : ι) (a : 𝒜 (i + j)) (b : 𝒜 j)
          (hb : (b : A) ∈ M), z = Localization.mk (a : A) ⟨(b : A), hb⟩}
        zero_mem' := (GradedLocalization.component (𝒜 := 𝒜) M i).zero_mem
        add_mem' := (GradedLocalization.component (𝒜 := 𝒜) M i).add_mem
        neg_mem' := (GradedLocalization.component (𝒜 := 𝒜) M i).neg_mem } :=
  rfl

private theorem zeroComponentCarrier (z : Localization M) :
    z ∈ GradedLocalization.zeroComponent (𝒜 := 𝒜) M ↔
      z ∈ GradedLocalization.component (𝒜 := 𝒜) M 0 :=
  Iff.rfl

private def expectedZeroComponentMap :
    HomogeneousLocalization 𝒜 M →+* GradedLocalization.zeroComponent (𝒜 := 𝒜) M where
  toFun x := ⟨x.val, by
    obtain ⟨c, rfl⟩ := HomogeneousLocalization.mk_surjective x
    let a : 𝒜 (0 + c.deg) := ⟨c.num, by
      rw [zero_add]
      exact c.num.property⟩
    exact ⟨c.deg, a, c.den, c.den_mem, rfl⟩⟩
  map_zero' := by ext; exact HomogeneousLocalization.val_zero
  map_one' := by ext; exact HomogeneousLocalization.val_one
  map_add' x y := by ext; exact HomogeneousLocalization.val_add x y
  map_mul' x y := by ext; exact HomogeneousLocalization.val_mul x y

private theorem toZeroComponentValue (x : HomogeneousLocalization 𝒜 M) :
    ((GradedLocalization.toZeroComponent (𝒜 := 𝒜) M x :
      GradedLocalization.zeroComponent (𝒜 := 𝒜) M) : Localization M) = x.val :=
  rfl

private theorem toZeroComponentFullRingMap :
    GradedLocalization.toZeroComponent (𝒜 := 𝒜) M = expectedZeroComponentMap 𝒜 M :=
  rfl

private theorem equivalenceForward (x : HomogeneousLocalization 𝒜 M) :
    ((GradedLocalization.homogeneousLocalizationEquivZeroComponent 𝒜 M x :
      GradedLocalization.zeroComponent (𝒜 := 𝒜) M) : Localization M) = x.val :=
  rfl

variable (hM : M ≤ SetLike.homogeneousSubmonoid 𝒜)

private theorem projectionFunction (i : ι) :
    (GradedLocalization.projection 𝒜 M hM i).toFun =
      GradedLocalization.projectionFun 𝒜 M hM i :=
  rfl

private theorem decompositionConstruction :
    GradedLocalization.decomposition 𝒜 M hM =
      (GradedLocalization.isInternal 𝒜 M hM).chooseDecomposition :=
  rfl

private theorem gradedRingDecomposition :
    (GradedLocalization.gradedRing 𝒜 M hM).toDecomposition =
      GradedLocalization.decomposition 𝒜 M hM :=
  rfl

private theorem gradedRingMultiplication :
    (GradedLocalization.gradedRing 𝒜 M hM).toGradedMonoid =
      GradedLocalization.componentGradedMonoid (𝒜 := 𝒜) M :=
  rfl

end GradedRingsTest.LocalizationInterface
