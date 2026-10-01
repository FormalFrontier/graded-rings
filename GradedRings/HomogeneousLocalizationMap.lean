/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Authors: Formal Frontier Agents
  Jujian Zhang and Eric Wieser (homogeneous-localization construction and native maps in mathlib)
Adapted material released under Apache 2.0, as in mathlib's LICENSE.
-/
module

public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization

@[expose] public section

set_option warningAsError true

/-!
# Degree-multiplying maps on homogeneous localizations

A ring homomorphism carrying degree `n` to degree `d * n` sends a fraction with
homogeneous numerator and denominator of equal degree to another such fraction.
This construction does not require `d` to be positive, nor denominators to be regular.
-/

noncomputable section

namespace HomogeneousLocalization

universe u v w x

variable {A : Type u} {B : Type v} {σ : Type w} {τ : Type x}
variable [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  (ℬ : ℕ → τ) [GradedRing ℬ]

/-- A degree-multiplying ring map sends equal-degree numerator/denominator pairs to
equal-degree pairs, with no restriction on the scaling factor. -/
def NumDenSameDeg.mapDegreeMul (f : A →+* B) (d : ℕ)
    (hdeg : ∀ n a, a ∈ 𝒜 n → f a ∈ ℬ (d * n))
    {P : Submonoid A} {Q : Submonoid B} (hPQ : P ≤ Q.comap f)
    (c : NumDenSameDeg 𝒜 P) : NumDenSameDeg ℬ Q where
  deg := d * c.deg
  num := ⟨f c.num, hdeg c.deg c.num c.num.property⟩
  den := ⟨f c.den, hdeg c.deg c.den c.den.property⟩
  den_mem := hPQ c.den_mem

/-- Underlying quotient map of `mapDegreeMul`. -/
def mapDegreeMulFun (f : A →+* B) (d : ℕ)
    (hdeg : ∀ n a, a ∈ 𝒜 n → f a ∈ ℬ (d * n))
    {P : Submonoid A} {Q : Submonoid B} (hPQ : P ≤ Q.comap f) :
    HomogeneousLocalization 𝒜 P → HomogeneousLocalization ℬ Q :=
  Quotient.map' (NumDenSameDeg.mapDegreeMul 𝒜 ℬ f d hdeg hPQ) (by
    intro c e h
    change c.embedding = e.embedding at h
    change (NumDenSameDeg.mapDegreeMul 𝒜 ℬ f d hdeg hPQ c).embedding =
      (NumDenSameDeg.mapDegreeMul 𝒜 ℬ f d hdeg hPQ e).embedding
    have hh := congrArg (IsLocalization.map (Localization Q) f hPQ) h
    simp_rw [NumDenSameDeg.embedding, Localization.mk_eq_mk',
      IsLocalization.map_mk', ← Localization.mk_eq_mk'] at hh
    simpa only [NumDenSameDeg.embedding, NumDenSameDeg.mapDegreeMul] using hh)

omit [AddSubgroupClass σ A] [GradedRing 𝒜] [AddSubgroupClass τ B] [GradedRing ℬ] in
theorem val_mapDegreeMulFun (f : A →+* B) (d : ℕ)
    (hdeg : ∀ n a, a ∈ 𝒜 n → f a ∈ ℬ (d * n))
    {P : Submonoid A} {Q : Submonoid B} (hPQ : P ≤ Q.comap f)
    (z : HomogeneousLocalization 𝒜 P) :
    (mapDegreeMulFun 𝒜 ℬ f d hdeg hPQ z).val =
      IsLocalization.map (Localization Q) f hPQ z.val := by
  obtain ⟨c, rfl⟩ := mk_surjective z
  change (mk (NumDenSameDeg.mapDegreeMul 𝒜 ℬ f d hdeg hPQ c)).val =
    IsLocalization.map (Localization Q) f hPQ (mk c).val
  simp only [val_mk, NumDenSameDeg.mapDegreeMul, Localization.mk_eq_mk',
    IsLocalization.map_mk']

/-- A ring homomorphism between homogeneous localizations induced by a ring map
which multiplies degrees by `d`. The ordinary localization map accounts for
annihilating denominators, including when the source has zero divisors. -/
def mapDegreeMul (f : A →+* B) (d : ℕ)
    (hdeg : ∀ n a, a ∈ 𝒜 n → f a ∈ ℬ (d * n))
    {P : Submonoid A} {Q : Submonoid B} (hPQ : P ≤ Q.comap f) :
    HomogeneousLocalization 𝒜 P →+* HomogeneousLocalization ℬ Q where
  toFun := mapDegreeMulFun 𝒜 ℬ f d hdeg hPQ
  map_one' := by
    apply val_injective Q
    simp only [val_mapDegreeMulFun, val_one, map_one]
  map_mul' a b := by
    apply val_injective Q
    simp only [val_mapDegreeMulFun, val_mul, map_mul]
  map_zero' := by
    apply val_injective Q
    simp only [val_mapDegreeMulFun, val_zero, map_zero]
  map_add' a b := by
    apply val_injective Q
    simp only [val_mapDegreeMulFun, val_add, map_add]

@[simp] theorem mapDegreeMul_mk (f : A →+* B) (d : ℕ)
    (hdeg : ∀ n a, a ∈ 𝒜 n → f a ∈ ℬ (d * n))
    {P : Submonoid A} {Q : Submonoid B} (hPQ : P ≤ Q.comap f)
    (c : NumDenSameDeg 𝒜 P) :
    mapDegreeMul 𝒜 ℬ f d hdeg hPQ (mk c) =
      mk (c.mapDegreeMul 𝒜 ℬ f d hdeg hPQ) := by
  rfl

/-- The degree-multiplying map is the restriction of the ordinary localization map. -/
@[simp] theorem val_mapDegreeMul (f : A →+* B) (d : ℕ)
    (hdeg : ∀ n a, a ∈ 𝒜 n → f a ∈ ℬ (d * n))
    {P : Submonoid A} {Q : Submonoid B} (hPQ : P ≤ Q.comap f)
    (z : HomogeneousLocalization 𝒜 P) :
    (mapDegreeMul 𝒜 ℬ f d hdeg hPQ z).val =
      IsLocalization.map (Localization Q) f hPQ z.val :=
  val_mapDegreeMulFun 𝒜 ℬ f d hdeg hPQ z

/-- Degree-multiplying map on homogeneous localizations away from one element. -/
def Away.mapDegreeMul (f : A →+* B) (d : ℕ)
    (hdeg : ∀ n a, a ∈ 𝒜 n → f a ∈ ℬ (d * n)) (a : A) :
    Away 𝒜 a →+* Away ℬ (f a) :=
  HomogeneousLocalization.mapDegreeMul 𝒜 ℬ f d hdeg (by
    rintro b ⟨n, rfl⟩
    exact ⟨n, by simp⟩)

@[simp] theorem Away.mapDegreeMul_mk (f : A →+* B) (d : ℕ)
    (hdeg : ∀ n a, a ∈ 𝒜 n → f a ∈ ℬ (d * n))
    {degree : ℕ} (a : A) (ha : a ∈ 𝒜 degree) (n : ℕ)
    (b : A) (hb : b ∈ 𝒜 (n • degree)) :
    Away.mapDegreeMul 𝒜 ℬ f d hdeg a (Away.mk 𝒜 ha n b hb) =
      Away.mk ℬ (hdeg degree a ha) n (f b)
        (by simpa [nsmul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
          hdeg (n • degree) b hb) := by
  apply val_injective _
  simp only [Away.mapDegreeMul, val_mapDegreeMul, Away.val_mk, IsLocalization.map_mk',
    Localization.mk_eq_mk']
  simp only [map_pow]

/-- Degree scaling commutes with restriction from the chart at `a` to the chart
at `a * b`. This equality of ring homomorphisms requires `b` homogeneous,
but not `a`; it also applies when `d = 0`. -/
theorem Away.mapDegreeMul_awayMap (f : A →+* B) (d : ℕ)
    (hdeg : ∀ n c, c ∈ 𝒜 n → f c ∈ ℬ (d * n))
    {degreeB : ℕ} (a b : A) (hb : b ∈ 𝒜 degreeB) :
    (Away.mapDegreeMul 𝒜 ℬ f d hdeg (a * b)).comp
      (awayMap 𝒜 hb (show a * b = a * b by rfl)) =
    (awayMap ℬ (hdeg degreeB b hb) (by simp)).comp
      (Away.mapDegreeMul 𝒜 ℬ f d hdeg a) := by
  let mapA : Localization.Away a →+* Localization.Away (f a) :=
    IsLocalization.map _ f (by
      show Submonoid.powers a ≤ (Submonoid.powers (f a)).comap f
      rintro c ⟨n, rfl⟩
      exact ⟨n, by simp⟩)
  let mapAB : Localization.Away (a * b) →+* Localization.Away (f (a * b)) :=
    IsLocalization.map _ f (by
      show Submonoid.powers (a * b) ≤ (Submonoid.powers (f (a * b))).comap f
      rintro c ⟨n, rfl⟩
      exact ⟨n, by simp⟩)
  have unitA : IsUnit (algebraMap A (Localization.Away (a * b)) a) :=
    isUnit_of_dvd_unit (map_dvd _ (dvd_mul_right a b))
      (IsLocalization.Away.algebraMap_isUnit (a * b))
  have unitB : IsUnit (algebraMap B (Localization.Away (f (a * b))) (f a)) :=
    isUnit_of_dvd_unit (map_dvd _ (map_dvd f (dvd_mul_right a b)))
      (IsLocalization.Away.algebraMap_isUnit (f (a * b)))
  let restrictA : Localization.Away a →+* Localization.Away (a * b) :=
    Localization.awayLift (algebraMap A _) a unitA
  let restrictB : Localization.Away (f a) →+* Localization.Away (f (a * b)) :=
    Localization.awayLift (algebraMap B _) (f a) unitB
  have hsquare : mapAB.comp restrictA = restrictB.comp mapA := by
    apply IsLocalization.ringHom_ext (Submonoid.powers a)
    apply RingHom.ext
    intro c
    change mapAB (restrictA (algebraMap A (Localization.Away a) c)) =
      restrictB (mapA (algebraMap A (Localization.Away a) c))
    simp only [restrictA, restrictB, mapA, mapAB,
      IsLocalization.Away.lift_eq, IsLocalization.map_eq]
  apply RingHom.ext
  intro z
  apply val_injective _
  simp only [RingHom.comp_apply, Away.mapDegreeMul, val_mapDegreeMul, val_awayMap]
  exact congrArg (fun k : Localization.Away a →+* Localization.Away (f (a * b)) =>
    k z.val) hsquare

/-- For scaling factor one, the construction agrees with mathlib's native graded map. -/
theorem mapDegreeMul_one (g : 𝒜 →+*ᵍ ℬ)
    {P : Submonoid A} {Q : Submonoid B} (hPQ : P ≤ Q.comap g) :
    mapDegreeMul 𝒜 ℬ g.toRingHom 1
      (fun n c hc => by simpa using Graded.map_mem g hc) hPQ = map g hPQ := by
  apply RingHom.ext
  intro z
  obtain ⟨c, rfl⟩ := mk_surjective z
  apply val_injective Q
  simp only [map_mk, val_mk]
  rfl

/-- On away charts the factor-one specialization is mathlib's native `Away.map`. -/
theorem Away.mapDegreeMul_one (g : 𝒜 →+*ᵍ ℬ) (a : A) :
    Away.mapDegreeMul 𝒜 ℬ g.toRingHom 1
      (fun n c hc => by simpa using Graded.map_mem g hc) a = Away.map g a := by
  exact HomogeneousLocalization.mapDegreeMul_one 𝒜 ℬ g _

/-- The degree-multiplying map associated with the identity ring homomorphism is the identity. -/
theorem mapDegreeMul_id (P : Submonoid A) :
    mapDegreeMul 𝒜 𝒜 (RingHom.id A) 1
      (fun n c hc => by simpa using hc) (P := P) (Q := P) le_rfl = .id _ := by
  apply RingHom.ext
  intro z
  obtain ⟨c, rfl⟩ := mk_surjective z
  apply val_injective P
  simp only [RingHom.id_apply, val_mk]
  rfl

section Composition

universe y z

variable {C : Type y} {ψ : Type z} [CommRing C] [SetLike ψ C]
  [AddSubgroupClass ψ C] (𝒞 : ℕ → ψ) [GradedRing 𝒞]

/-- Scaling factors multiply when degree-multiplying maps are composed. -/
theorem mapDegreeMul_comp (f : A →+* B) (g : B →+* C) (d e : ℕ)
    (hf : ∀ n a, a ∈ 𝒜 n → f a ∈ ℬ (d * n))
    (hg : ∀ n b, b ∈ ℬ n → g b ∈ 𝒞 (e * n))
    {P : Submonoid A} {Q : Submonoid B} {R : Submonoid C}
    (hPQ : P ≤ Q.comap f) (hQR : Q ≤ R.comap g) :
    mapDegreeMul 𝒜 𝒞 (g.comp f) (e * d)
      (by
        intro n a ha
        change g (f a) ∈ 𝒞 ((e * d) * n)
        simpa only [mul_assoc] using (hg (d * n) (f a) (hf n a ha)))
      (hPQ.trans <| Submonoid.monotone_comap hQR) =
    (mapDegreeMul ℬ 𝒞 g e hg hQR).comp (mapDegreeMul 𝒜 ℬ f d hf hPQ) := by
  apply RingHom.ext
  intro z
  obtain ⟨c, rfl⟩ := mk_surjective z
  apply val_injective R
  simp only [RingHom.comp_apply, mapDegreeMul_mk, val_mk]
  rfl

end Composition

end HomogeneousLocalization
