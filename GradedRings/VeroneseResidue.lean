/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GradedRings.VeroneseFinite

/-!
# Residue projections for the whole Veronese ring

The projection onto one congruence class of a natural grading is linear over the
entire external Veronese ring through its canonical inclusion. Its image is
finite whenever the original ring is finite over the same Veronese ring.
-/

@[expose] public section

set_option warningAsError true
set_option linter.style.haveILetI false

noncomputable section

namespace GradedRing.Veronese

universe u v

variable {S : Type u} [CommRing S] {σ : Type v} [SetLike σ S]
  [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-- Additively retain precisely the components whose old degree has remainder `r`. -/
def residueProjectionAdd (n r : ℕ) : S →+ S :=
  (DirectSum.decomposeAddEquiv 𝒮).symm.toAddMonoidHom.comp
    ((DFinsupp.filterAddMonoidHom (fun d => 𝒮 d) (fun d => d % n = r)).comp
      (DirectSum.decomposeAddEquiv 𝒮).toAddMonoidHom)

/-- On a homogeneous element, the residue projection either retains it or kills it. -/
theorem residueProjectionAdd_of_mem (n r d : ℕ) {x : S} (hx : x ∈ 𝒮 d) :
    residueProjectionAdd 𝒮 n r x = if d % n = r then x else 0 := by
  classical
  simp only [residueProjectionAdd, AddMonoidHom.comp_apply]
  change (DirectSum.decompose 𝒮).symm
    ((DirectSum.decompose 𝒮 x).filter (fun j => j % n = r)) = _
  rw [DirectSum.decompose_of_mem 𝒮 hx]
  change (DirectSum.decompose 𝒮).symm
    ((DFinsupp.single d (⟨x, hx⟩ : 𝒮 d)).filter (fun j => j % n = r)) = _
  rw [DFinsupp.filter_single]
  by_cases hd : d % n = r
  · simp only [ite_eq_left hd]
    change (DirectSum.decompose 𝒮).symm
      (DirectSum.of (fun j => 𝒮 j) d (⟨x, hx⟩ : 𝒮 d)) = x
    exact DirectSum.decompose_symm_of 𝒮 ⟨x, hx⟩
  · simp only [ite_eq_right hd]
    exact DirectSum.decompose_symm_zero 𝒮

/-- The projection is the coordinatewise filter on the native decomposition. -/
theorem decompose_residueProjectionAdd (n r : ℕ) (x : S) (d : ℕ) :
    DirectSum.decompose 𝒮 (residueProjectionAdd 𝒮 n r x) d =
      if d % n = r then DirectSum.decompose 𝒮 x d else 0 := by
  classical
  simp [residueProjectionAdd, DFinsupp.filter_apply]

/-- The additive projection is idempotent. -/
theorem residueProjectionAdd_idempotent (n r : ℕ) (x : S) :
    residueProjectionAdd 𝒮 n r (residueProjectionAdd 𝒮 n r x) =
      residueProjectionAdd 𝒮 n r x := by
  apply (DirectSum.decomposeAddEquiv 𝒮).injective
  ext d
  by_cases hd : d % n = r <;>
    simp [decompose_residueProjectionAdd, hd]

/-- Fixed points have precisely the unwanted homogeneous components zero. -/
theorem residueProjectionAdd_eq_iff (n r : ℕ) (x : S) :
    residueProjectionAdd 𝒮 n r x = x ↔
      ∀ d : ℕ, d % n ≠ r → DirectSum.decompose 𝒮 x d = 0 := by
  constructor
  · intro h d hd
    have hcoord := congrArg (fun y : S => DirectSum.decompose 𝒮 y d) h
    simpa [decompose_residueProjectionAdd, hd] using hcoord.symm
  · intro h
    apply (DirectSum.decomposeAddEquiv 𝒮).injective
    apply DFinsupp.ext
    intro d
    by_cases hd : d % n = r
    · simp [decompose_residueProjectionAdd, hd]
    · simpa [decompose_residueProjectionAdd, hd] using (h d hd).symm

/-- Multiplication by every selected scalar preserves the residue filter. -/
theorem residueProjectionAdd_inclusion_mul (n r : ℕ)
    (a : VeroneseRing 𝒮 n) (x : S) :
    residueProjectionAdd 𝒮 n r (inclusion 𝒮 n a * x) =
      inclusion 𝒮 n a * residueProjectionAdd 𝒮 n r x := by
  classical
  induction a using DirectSum.induction_on with
  | zero => simp
  | of i a =>
    simp only [inclusion_of]
    induction x using DirectSum.Decomposition.inductionOn (ℳ := 𝒮) with
    | zero => simp
    | homogeneous b =>
      rename_i d
      have hprod : (a : S) * (b : S) ∈ 𝒮 (n * i + d) :=
        SetLike.GradedMul.mul_mem a.property b.property
      have hmod : (n * i + d) % n = d % n := by
        simp [Nat.add_mod]
      rw [residueProjectionAdd_of_mem 𝒮 n r (n * i + d) hprod,
        residueProjectionAdd_of_mem 𝒮 n r d b.property, hmod]
      split_ifs <;> simp
    | add y z hy hz =>
      simp [mul_add, map_add, hy, hz]
  | add a b ha hb =>
    simp [map_add, add_mul, ha, hb]

/-- The residue filter, linear for the canonical action of the *whole* external
Veronese ring on the original ring. Positivity and the reduced residue specify
the usual disjoint residue classes. -/
def residueProjection (n r : ℕ) (_hn : 0 < n) (_hr : r < n) :
    letI : Algebra (VeroneseRing 𝒮 n) S := (inclusion 𝒮 n).toAlgebra
    S →ₗ[VeroneseRing 𝒮 n] S := by
  letI : Algebra (VeroneseRing 𝒮 n) S := (inclusion 𝒮 n).toAlgebra
  exact {
    toFun := residueProjectionAdd 𝒮 n r
    map_add' := (residueProjectionAdd 𝒮 n r).map_add
    map_smul' := by
      intro a x
      change residueProjectionAdd 𝒮 n r (inclusion 𝒮 n a * x) =
        inclusion 𝒮 n a * residueProjectionAdd 𝒮 n r x
      exact residueProjectionAdd_inclusion_mul 𝒮 n r a x }

@[simp] theorem residueProjection_apply (n r : ℕ) (hn : 0 < n) (hr : r < n)
    (x : S) : residueProjection 𝒮 n r hn hr x = residueProjectionAdd 𝒮 n r x := rfl

/-- The whole-Veronese linear projection is idempotent. -/
theorem residueProjection_idempotent (n r : ℕ) (hn : 0 < n) (hr : r < n) (x : S) :
    residueProjection 𝒮 n r hn hr (residueProjection 𝒮 n r hn hr x) =
      residueProjection 𝒮 n r hn hr x := by
  simpa using residueProjectionAdd_idempotent 𝒮 n r x

/-- Homogeneous decision law for the linear projection. -/
theorem residueProjection_of_mem (n r d : ℕ) (hn : 0 < n) (hr : r < n)
    {x : S} (hx : x ∈ 𝒮 d) :
    residueProjection 𝒮 n r hn hr x = if d % n = r then x else 0 := by
  simpa using residueProjectionAdd_of_mem 𝒮 n r d hx

/-- Exact range: every component of the other residues vanishes. -/
theorem mem_residueProjection_range_iff (n r : ℕ) (hn : 0 < n) (hr : r < n)
    (x : S) :
    letI : Algebra (VeroneseRing 𝒮 n) S := (inclusion 𝒮 n).toAlgebra
    x ∈ (residueProjection 𝒮 n r hn hr).range ↔
      ∀ d : ℕ, d % n ≠ r → DirectSum.decompose 𝒮 x d = 0 := by
  letI : Algebra (VeroneseRing 𝒮 n) S := (inclusion 𝒮 n).toAlgebra
  constructor
  · rintro ⟨y, rfl⟩
    exact (residueProjectionAdd_eq_iff 𝒮 n r _).mp
      (by simpa using residueProjection_idempotent 𝒮 n r hn hr y)
  · intro hx
    exact ⟨x, by simpa using (residueProjectionAdd_eq_iff 𝒮 n r x).mpr hx⟩

/-- The image of the linear projection is finite when its ambient module is finite. -/
theorem residueProjection_range_finite (n r : ℕ) (hn : 0 < n) (hr : r < n) :
    letI : Algebra (VeroneseRing 𝒮 n) S := (inclusion 𝒮 n).toAlgebra
    [Module.Finite (VeroneseRing 𝒮 n) S] →
      Module.Finite (VeroneseRing 𝒮 n) (residueProjection 𝒮 n r hn hr).range := by
  letI : Algebra (VeroneseRing 𝒮 n) S := (inclusion 𝒮 n).toAlgebra
  intro _
  exact Module.Finite.range (residueProjection 𝒮 n r hn hr)

/-- Finite type over the entire old degree-zero ring makes every positive
Veronese residue range finite, through the canonical finite inclusion. -/
theorem residueProjection_range_finite_of_finiteType
    [Algebra.FiniteType (𝒮 0) S] (n r : ℕ) (hn : 0 < n) (hr : r < n) :
    letI : Algebra (VeroneseRing 𝒮 n) S := (inclusion 𝒮 n).toAlgebra
    Module.Finite (VeroneseRing 𝒮 n) (residueProjection 𝒮 n r hn hr).range := by
  letI : Algebra (VeroneseRing 𝒮 n) S := (inclusion 𝒮 n).toAlgebra
  letI : Module.Finite (VeroneseRing 𝒮 n) S := inclusion_finite 𝒮 n hn
  exact residueProjection_range_finite 𝒮 n r hn hr

end GradedRing.Veronese
