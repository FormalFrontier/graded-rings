/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.GradedAlgebra.Radical

/-!
# Homogeneous prime ideals and the degree-zero component

This file relates homogeneous prime ideals in an integer-graded commutative
ring to prime ideals of its degree-zero component when the ring contains a
positive-degree homogeneous unit. The inverse to contraction is radical
extension; the radical cannot in general be omitted.
-/

public section

open DirectSum

namespace GradedRing

universe u v

variable {A : Type u} [CommRing A]
variable {σ : Type v} [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℤ → σ) [GradedRing 𝒜]

/-- The inverse selected from a homogeneous unit of degree `d` is homogeneous
of degree `-d`. -/
theorem inv_mem_of_isUnit {d : ℤ} {u : A} (hu : u ∈ 𝒜 d) (hu' : IsUnit u) :
    (↑hu'.unit⁻¹ : A) ∈ 𝒜 (-d) := by
  let v : A := ↑hu'.unit⁻¹
  have huv : u * v = 1 := by
    dsimp [v]
    exact hu'.mul_val_inv
  have hcomponent : u * (decompose 𝒜 v (-d) : A) = 1 := by
    calc
      _ = (decompose 𝒜 (u * v) (d + -d) : A) :=
        (coe_decompose_mul_add_of_left_mem (j := -d) 𝒜 hu).symm
      _ = (decompose 𝒜 (u * v) 0 : A) := by rw [add_neg_cancel]
      _ = (decompose 𝒜 (1 : A) 0 : A) := by rw [huv]
      _ = 1 := by
        simpa using decompose_of_mem_same 𝒜 (SetLike.one_mem_graded 𝒜)
  have hv : v = (decompose 𝒜 v (-d) : A) := by
    apply hu'.mul_right_injective
    change u * v = u * (decompose 𝒜 v (-d) : A)
    rw [huv, hcomponent]
  change v ∈ 𝒜 (-d)
  rw [hv]
  exact SetLike.coe_mem _

/-- An integer power of a homogeneous unit of degree `d` is homogeneous of
degree `n * d`. -/
theorem unit_zpow_mem {d : ℤ} (u : Aˣ) (hu : (u : A) ∈ 𝒜 d) (n : ℤ) :
    (↑(u ^ n) : A) ∈ 𝒜 (n * d) := by
  cases n with
  | ofNat n =>
      simpa [nsmul_eq_mul] using SetLike.pow_mem_graded n hu
  | negSucc n =>
      have hinv : (↑u⁻¹ : A) ∈ 𝒜 (-d) := by
        simpa using inv_mem_of_isUnit 𝒜 hu u.isUnit
      have hpow := SetLike.pow_mem_graded (n + 1) hinv
      have hval : (↑(u ^ Int.negSucc n) : A) = (↑u⁻¹ : A) ^ (n + 1) := by
        have heq : u ^ Int.negSucc n = (u⁻¹) ^ (n + 1) := by
          rw [zpow_negSucc, inv_pow]
        exact congrArg (fun z : Aˣ => (z : A)) heq
      have hdeg : Int.negSucc n * d = (n + 1) • (-d) := by
        simp only [Int.negSucc_eq, nsmul_eq_mul]
        push_cast
        ring
      rw [hdeg, hval]
      exact hpow

/-- Projection onto the degree-zero component, linear over that component. -/
@[expose]
def degreeZeroProjection : A →ₗ[𝒜 0] 𝒜 0 where
  toFun a := decompose 𝒜 a 0
  map_add' a b := by
    rw [decompose_add, add_apply]
  map_smul' r a := by
    ext
    exact coe_decompose_mul_of_left_mem_zero 𝒜 r.property

/-- Projection onto degree zero is surjective. -/
theorem degreeZeroProjection_surjective : Function.Surjective (degreeZeroProjection 𝒜) := by
  intro x
  refine ⟨(x : A), ?_⟩
  exact Subtype.ext (decompose_of_mem_same 𝒜 x.property)

/-- Extending an ideal from the degree-zero component and contracting it back
recovers the original ideal. -/
theorem comap_map_degreeZero (q : Ideal (𝒜 0)) :
    (q.map (algebraMap (𝒜 0) A)).comap (algebraMap (𝒜 0) A) = q := by
  apply le_antisymm
  · intro x hx
    have hx' : (x : A) ∈ q • (⊤ : Submodule (𝒜 0) A) := by
      rw [Ideal.smul_top_eq_map]
      exact hx
    have hp : degreeZeroProjection 𝒜 (x : A) ∈
        (q • (⊤ : Submodule (𝒜 0) A)).map (degreeZeroProjection 𝒜) :=
      Submodule.mem_map_of_mem hx'
    rw [Submodule.map_smul'', Submodule.map_top,
      LinearMap.range_eq_top.mpr (degreeZeroProjection_surjective 𝒜)] at hp
    have hproj : degreeZeroProjection 𝒜 (x : A) = x :=
      Subtype.ext (decompose_of_mem_same 𝒜 x.property)
    rw [hproj] at hp
    simpa [Ideal.smul_eq_mul, Ideal.mul_top] using hp
  · exact Ideal.le_comap_map

/-- The extension of a degree-zero ideal is homogeneous. -/
theorem map_degreeZero_isHomogeneous (q : Ideal (𝒜 0)) :
    (q.map (algebraMap (𝒜 0) A)).IsHomogeneous 𝒜 := by
  rw [← q.span_eq, Ideal.map_span]
  apply Ideal.homogeneous_span
  rintro x ⟨y, hy, rfl⟩
  exact ⟨0, y.property⟩

private def normalize (u : Aˣ) (D : ℕ) (n : ℤ) (x : A) : A :=
  x ^ D * (u ^ (-n) : Aˣ)

private theorem normalize_mem_zero {d n : ℤ} {D : ℕ} (u : Aˣ)
    (hu : (u : A) ∈ 𝒜 d) (hd : (D : ℤ) = d) {x : A} (hx : x ∈ 𝒜 n) :
    normalize u D n x ∈ 𝒜 0 := by
  have hxpow := SetLike.pow_mem_graded D hx
  have hupow := unit_zpow_mem 𝒜 u hu (-n)
  have hmul := SetLike.mul_mem_graded hxpow hupow
  change x ^ D * (↑(u ^ (-n)) : A) ∈ 𝒜 0
  have hdeg : D • n + -n * d = 0 := by
    simp only [nsmul_eq_mul]
    rw [hd]
    ring
  rw [← hdeg]
  exact hmul

private theorem normalize_mul (u : Aˣ) (D : ℕ) (n m : ℤ) (x y : A) :
    normalize u D (n + m) (x * y) = normalize u D n x * normalize u D m y := by
  simp only [normalize, mul_pow]
  have huadd : u ^ (-(n + m)) = u ^ (-n) * u ^ (-m) := by
    rw [show -(n + m) = -n + -m by ring]
    exact zpow_add u (-n) (-m)
  rw [congrArg (fun z : Aˣ => (z : A)) huadd]
  simp only [Units.val_mul]
  ring

private theorem normalize_mul_zpow (u : Aˣ) (D : ℕ) (n : ℤ) (x : A) :
    normalize u D n x * (u ^ n : Aˣ) = x ^ D := by
  have huone : u ^ (-n) * u ^ n = 1 := by
    rw [← zpow_add u (-n) n]
    simp
  simp only [normalize, mul_assoc]
  rw [← Units.val_mul, huone]
  simp

private theorem mem_radical_map_of_normalize_mem (q : Ideal (𝒜 0))
    (u : Aˣ) (D : ℕ) (n : ℤ) (x : A)
    (hx : normalize u D n x ∈ 𝒜 0)
    (h : (⟨normalize u D n x, hx⟩ : 𝒜 0) ∈ q) :
    x ∈ (q.map (algebraMap (𝒜 0) A)).radical := by
  have hmap : normalize u D n x ∈ q.map (algebraMap (𝒜 0) A) :=
    Ideal.mem_map_of_mem (algebraMap (𝒜 0) A) h
  have hrad : normalize u D n x ∈ (q.map (algebraMap (𝒜 0) A)).radical :=
    Ideal.le_radical hmap
  have hpow : x ^ D ∈ (q.map (algebraMap (𝒜 0) A)).radical := by
    have hmul := Ideal.mul_mem_right (↑(u ^ n) : A)
      (q.map (algebraMap (𝒜 0) A)).radical hrad
    rw [normalize_mul_zpow] at hmul
    exact hmul
  exact Ideal.mem_radical_of_pow_mem hpow

/-- The radical extension of a prime ideal from degree zero is prime when the
graded ring contains a positive-degree homogeneous unit. -/
theorem radical_map_degreeZero_isPrime {d : ℤ} (u : Aˣ)
    (hu : (u : A) ∈ 𝒜 d) (hd : 0 < d) (q : Ideal (𝒜 0)) (hq : q.IsPrime) :
    (q.map (algebraMap (𝒜 0) A)).radical.IsPrime := by
  let J := (q.map (algebraMap (𝒜 0) A)).radical
  have hJhom : J.IsHomogeneous 𝒜 := (map_degreeZero_isHomogeneous 𝒜 q).radical
  have hcontract : J.comap (algebraMap (𝒜 0) A) = q := by
    dsimp [J]
    rw [Ideal.comap_radical, comap_map_degreeZero 𝒜, hq.radical]
  rw [hJhom.isPrime_iff]
  refine ⟨?_, ?_⟩
  · intro htop
    apply hq.ne_top
    rw [← hcontract, htop, Ideal.comap_top]
  · intro x y hxhy hyhy hxy
    obtain ⟨n, hxn⟩ := hxhy
    obtain ⟨m, hym⟩ := hyhy
    let D := d.toNat
    have hD : (D : ℤ) = d := Int.toNat_of_nonneg hd.le
    have hDpos : 0 < D := by omega
    have hnormx : normalize u D n x ∈ 𝒜 0 :=
      normalize_mem_zero 𝒜 u hu hD hxn
    have hnormy : normalize u D m y ∈ 𝒜 0 :=
      normalize_mem_zero 𝒜 u hu hD hym
    have hnormxy : normalize u D (n + m) (x * y) ∈ 𝒜 0 :=
      normalize_mem_zero 𝒜 u hu hD (SetLike.mul_mem_graded hxn hym)
    have hnormxyJ : normalize u D (n + m) (x * y) ∈ J := by
      have hpow : (x * y) ^ D ∈ J := J.pow_mem_of_mem hxy D hDpos
      exact J.mul_mem_right (↑(u ^ (-(n + m))) : A) hpow
    have hnormxyq : (⟨normalize u D (n + m) (x * y), hnormxy⟩ : 𝒜 0) ∈ q := by
      rw [← hcontract]
      exact hnormxyJ
    have hmul :
        (⟨normalize u D (n + m) (x * y), hnormxy⟩ : 𝒜 0) =
          ⟨normalize u D n x, hnormx⟩ * ⟨normalize u D m y, hnormy⟩ := by
      exact Subtype.ext (normalize_mul u D n m x y)
    rw [hmul] at hnormxyq
    rcases hq.mem_or_mem hnormxyq with hxq | hyq
    · exact Or.inl (mem_radical_map_of_normalize_mem 𝒜 q u D n x hnormx hxq)
    · exact Or.inr (mem_radical_map_of_normalize_mem 𝒜 q u D m y hnormy hyq)

/-- A homogeneous prime ideal is the radical extension of its contraction to
degree zero when the graded ring contains a positive-degree homogeneous unit. -/
theorem radical_map_comap_degreeZero {d : ℤ} (u : Aˣ)
    (hu : (u : A) ∈ 𝒜 d) (hd : 0 < d) (P : Ideal A)
    (hPprime : P.IsPrime) (hPhom : P.IsHomogeneous 𝒜) :
    ((P.comap (algebraMap (𝒜 0) A)).map
      (algebraMap (𝒜 0) A)).radical = P := by
  let q := P.comap (algebraMap (𝒜 0) A)
  let J := (q.map (algebraMap (𝒜 0) A)).radical
  have hJhom : J.IsHomogeneous 𝒜 := (map_degreeZero_isHomogeneous 𝒜 q).radical
  apply le_antisymm
  · apply (hPprime.radical_le_iff).mpr
    exact Ideal.map_le_of_le_comap le_rfl
  · intro x hx
    apply (hJhom.mem_iff 𝒜).mpr
    intro n
    have hxn : (decompose 𝒜 x n : A) ∈ P := (hPhom.mem_iff 𝒜).mp hx n
    let D := d.toNat
    have hD : (D : ℤ) = d := Int.toNat_of_nonneg hd.le
    have hDpos : 0 < D := by omega
    have hxgrade : (decompose 𝒜 x n : A) ∈ 𝒜 n := SetLike.coe_mem _
    have hnorm : normalize u D n (decompose 𝒜 x n : A) ∈ 𝒜 0 :=
      normalize_mem_zero 𝒜 u hu hD hxgrade
    have hnormP : normalize u D n (decompose 𝒜 x n : A) ∈ P := by
      have hpow : (decompose 𝒜 x n : A) ^ D ∈ P :=
        P.pow_mem_of_mem hxn D hDpos
      exact P.mul_mem_right (↑(u ^ (-n)) : A) hpow
    apply mem_radical_map_of_normalize_mem 𝒜 q u D n (decompose 𝒜 x n : A) hnorm
    exact hnormP

/-- If an integer-graded commutative ring has a positive-degree homogeneous
unit, contraction to degree zero and radical extension are inverse on prime
ideals and homogeneous prime ideals. -/
@[expose]
def homogeneousPrimeEquivDegreeZeroPrime {d : ℤ} (u : Aˣ)
    (hu : (u : A) ∈ 𝒜 d) (hd : 0 < d) :
    {P : Ideal A // P.IsPrime ∧ P.IsHomogeneous 𝒜} ≃
      {q : Ideal (𝒜 0) // q.IsPrime} where
  toFun P := ⟨P.1.comap (algebraMap (𝒜 0) A), P.2.1.comap _⟩
  invFun q := ⟨(q.1.map (algebraMap (𝒜 0) A)).radical,
    radical_map_degreeZero_isPrime 𝒜 u hu hd q.1 q.2,
    (map_degreeZero_isHomogeneous 𝒜 q.1).radical⟩
  left_inv P := by
    apply Subtype.ext
    exact radical_map_comap_degreeZero 𝒜 u hu hd P.1 P.2.1 P.2.2
  right_inv q := by
    apply Subtype.ext
    change ((q.1.map (algebraMap (𝒜 0) A)).radical).comap
      (algebraMap (𝒜 0) A) = q.1
    rw [Ideal.comap_radical, comap_map_degreeZero 𝒜, q.2.radical]

end GradedRing
