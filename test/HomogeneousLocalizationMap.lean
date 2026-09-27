module

public import GradedRings.HomogeneousLocalizationMap

@[expose] public section

set_option warningAsError true

namespace GradedRingsTest.HomogeneousLocalizationMap

open HomogeneousLocalization

universe u v w x

variable {A : Type u} {B : Type v} {σ : Type w} {τ : Type x}
variable [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  (ℬ : ℕ → τ) [GradedRing ℬ]
variable (f : A →+* B) (d : ℕ)
  (hdeg : ∀ n a, a ∈ 𝒜 n → f a ∈ ℬ (d * n))
  {P : Submonoid A} {Q : Submonoid B} (hPQ : P ≤ Q.comap f)

example : HomogeneousLocalization 𝒜 P →+* HomogeneousLocalization ℬ Q :=
  mapDegreeMul 𝒜 ℬ f d hdeg hPQ

private theorem client_fraction_formula (c : NumDenSameDeg 𝒜 P) :
    mapDegreeMul 𝒜 ℬ f d hdeg hPQ (mk c) =
      mk (c.mapDegreeMul 𝒜 ℬ f d hdeg hPQ) :=
  mapDegreeMul_mk 𝒜 ℬ f d hdeg hPQ c

example (c : NumDenSameDeg 𝒜 P) :
    mapDegreeMul 𝒜 ℬ f d hdeg hPQ (mk c) =
      mk (c.mapDegreeMul 𝒜 ℬ f d hdeg hPQ) :=
  client_fraction_formula 𝒜 ℬ f d hdeg hPQ c

example (z : HomogeneousLocalization 𝒜 P) :
    (mapDegreeMul 𝒜 ℬ f d hdeg hPQ z).val =
      IsLocalization.map (Localization Q) f hPQ z.val :=
  val_mapDegreeMul 𝒜 ℬ f d hdeg hPQ z

example (a : A) : Away 𝒜 a →+* Away ℬ (f a) :=
  Away.mapDegreeMul 𝒜 ℬ f d hdeg a

example {degree : ℕ} (a : A) (ha : a ∈ 𝒜 degree) (n : ℕ)
    (b : A) (hb : b ∈ 𝒜 (n • degree)) :
    Away.mapDegreeMul 𝒜 ℬ f d hdeg a (Away.mk 𝒜 ha n b hb) =
      Away.mk ℬ (hdeg degree a ha) n (f b)
        (by simpa [nsmul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
          hdeg (n • degree) b hb) :=
  Away.mapDegreeMul_mk 𝒜 ℬ f d hdeg a ha n b hb

example {degreeB : ℕ} (a b : A) (hb : b ∈ 𝒜 degreeB) :
    (Away.mapDegreeMul 𝒜 ℬ f d hdeg (a * b)).comp
      (awayMap 𝒜 hb (show a * b = a * b by rfl)) =
    (awayMap ℬ (hdeg degreeB b hb) (by simp)).comp
      (Away.mapDegreeMul 𝒜 ℬ f d hdeg a) :=
  Away.mapDegreeMul_awayMap 𝒜 ℬ f d hdeg a b hb

example (hzero : ∀ n a, a ∈ 𝒜 n → f a ∈ ℬ 0) :
    HomogeneousLocalization 𝒜 P →+* HomogeneousLocalization ℬ Q :=
  mapDegreeMul 𝒜 ℬ f 0 (by simpa using hzero) hPQ

example (g : 𝒜 →+*ᵍ ℬ) {S : Submonoid A} {T : Submonoid B}
    (hST : S ≤ T.comap g) :
    mapDegreeMul 𝒜 ℬ g.toRingHom 1
      (fun n c hc => by simpa using Graded.map_mem g hc) hST = map g hST :=
  mapDegreeMul_one 𝒜 ℬ g hST

example (g : 𝒜 →+*ᵍ ℬ) (a : A) :
    Away.mapDegreeMul 𝒜 ℬ g.toRingHom 1
      (fun n c hc => by simpa using Graded.map_mem g hc) a = Away.map g a :=
  Away.mapDegreeMul_one 𝒜 ℬ g a

example (S : Submonoid A) :
    mapDegreeMul 𝒜 𝒜 (RingHom.id A) 1
      (fun n c hc => by simpa using hc) (P := S) (Q := S) le_rfl = .id _ :=
  mapDegreeMul_id 𝒜 S

section Composition

universe y z

variable {C : Type y} {ψ : Type z} [CommRing C] [SetLike ψ C]
  [AddSubgroupClass ψ C] (𝒞 : ℕ → ψ) [GradedRing 𝒞]

example (g : B →+* C) (e : ℕ)
    (hg : ∀ n b, b ∈ ℬ n → g b ∈ 𝒞 (e * n))
    {R : Submonoid C} (hQR : Q ≤ R.comap g) :
    mapDegreeMul 𝒜 𝒞 (g.comp f) (e * d)
      (by
        intro n a ha
        change g (f a) ∈ 𝒞 ((e * d) * n)
        simpa only [mul_assoc] using (hg (d * n) (f a) (hdeg n a ha)))
      (hPQ.trans <| Submonoid.monotone_comap hQR) =
    (mapDegreeMul ℬ 𝒞 g e hg hQR).comp (mapDegreeMul 𝒜 ℬ f d hdeg hPQ) :=
  mapDegreeMul_comp 𝒜 ℬ 𝒞 f g d e hdeg hg hPQ hQR

end Composition

end GradedRingsTest.HomogeneousLocalizationMap
