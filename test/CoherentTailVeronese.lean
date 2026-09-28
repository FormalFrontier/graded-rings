/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GradedRings.CoherentTailVeronese
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Data.ZMod.Basic

@[expose] public section

/-! Concrete tests for coherent-tail selected ring equivalences. -/

noncomputable section

namespace GradedRingsTest.CoherentTailVeronese

open DirectSum GradedRing.Veronese GradedRing.Veronese.CoherentTail

universe u

variable {C : Type u} [CommRing C]

abbrev polynomialGrade (C : Type u) [CommRing C] :=
  MvPolynomial.homogeneousSubmodule Unit C

local instance : GradedRing (polynomialGrade C) := MvPolynomial.gradedAlgebra

def mapPiece (e : C ≃+* C) (d : ℕ) : polynomialGrade C d ≃+ polynomialGrade C d where
  toFun x := ⟨MvPolynomial.mapEquiv Unit e x, by
    change (MvPolynomial.mapEquiv Unit e (x : MvPolynomial Unit C)).IsHomogeneous d
    exact x.property.map (e : C →+* C)⟩
  invFun x := ⟨(MvPolynomial.mapEquiv Unit e).symm x, by
    rw [MvPolynomial.mapEquiv_symm]
    change (MvPolynomial.mapEquiv Unit e.symm (x : MvPolynomial Unit C)).IsHomogeneous d
    exact x.property.map (e.symm : C →+* C)⟩
  left_inv x := Subtype.ext ((MvPolynomial.mapEquiv Unit e).left_inv (x : MvPolynomial Unit C))
  right_inv x := Subtype.ext ((MvPolynomial.mapEquiv Unit e).right_inv (x : MvPolynomial Unit C))
  map_add' x y := Subtype.ext (map_add (MvPolynomial.mapEquiv Unit e)
    (x : MvPolynomial Unit C) (y : MvPolynomial Unit C))

def mapZero (e : C ≃+* C) : polynomialGrade C 0 ≃+* polynomialGrade C 0 where
  __ := mapPiece e 0
  map_mul' x y := Subtype.ext (map_mul (MvPolynomial.mapEquiv Unit e)
    (x : MvPolynomial Unit C) (y : MvPolynomial Unit C))

def polynomialTail (e : C ≃+* C) :
    TailEquiv (polynomialGrade C) (polynomialGrade C) 2 where
  positive := by decide
  zero := mapZero e
  high _ _ := mapPiece e _
  coeff _ _ a x := by
    change (MvPolynomial.mapEquiv Unit e) ((a : MvPolynomial Unit C) * x) =
      (MvPolynomial.mapEquiv Unit e) a * (MvPolynomial.mapEquiv Unit e) x
    exact map_mul (MvPolynomial.mapEquiv Unit e) _ _
  product _ _ _ _ x y := by
    change (MvPolynomial.mapEquiv Unit e) ((x : MvPolynomial Unit C) * y) =
      (MvPolynomial.mapEquiv Unit e) x * (MvPolynomial.mapEquiv Unit e) y
    exact map_mul (MvPolynomial.mapEquiv Unit e) _ _

def swapCoefficients : (ZMod 4 × ZMod 4) ≃+* (ZMod 4 × ZMod 4) :=
  RingEquiv.prodComm

def swapTail : TailEquiv (polynomialGrade (ZMod 4 × ZMod 4))
    (polynomialGrade (ZMod 4 × ZMod 4)) 2 :=
  polynomialTail swapCoefficients

theorem swapCoefficients_nonidentity : swapCoefficients ((1 : ZMod 4), 0) ≠
    ((1 : ZMod 4), 0) := by
  decide

theorem swap_zero_nonidentity :
    swapTail.zero
      (⟨MvPolynomial.C ((1 : ZMod 4), 0),
        MvPolynomial.isHomogeneous_C _ _⟩ : polynomialGrade (ZMod 4 × ZMod 4) 0) ≠
      (⟨MvPolynomial.C ((1 : ZMod 4), 0),
        MvPolynomial.isHomogeneous_C _ _⟩ : polynomialGrade (ZMod 4 × ZMod 4) 0) := by
  intro heq
  have hmap := congrArg Subtype.val heq
  change MvPolynomial.map (swapCoefficients :
      (ZMod 4 × ZMod 4) →+* (ZMod 4 × ZMod 4))
    (MvPolynomial.C ((1 : ZMod 4), 0) : MvPolynomial Unit _) =
    MvPolynomial.C ((1 : ZMod 4), 0) at hmap
  have hc : swapCoefficients ((1 : ZMod 4), 0) = ((1 : ZMod 4), 0) := by
    apply MvPolynomial.C_injective Unit (ZMod 4 × ZMod 4)
    simpa [MvPolynomial.map_C, swapCoefficients] using hmap
  exact swapCoefficients_nonidentity hc

theorem swap_selected_zero :
    (zeroRingEquiv (polynomialGrade (ZMod 4 × ZMod 4)) 2 (by decide)).toRingHom.comp
      (GradedRingHom.gradedZeroRingHom (swapTail.selectedGradedHom 2 (by decide))) =
      swapTail.zero.toRingHom.comp
        (zeroRingEquiv (polynomialGrade (ZMod 4 × ZMod 4)) 2 (by decide)).toRingHom :=
  swapTail.selected_zero 2 (by decide) (by decide)

theorem swap_selected_inverse :
    (swapTail.selectedGradedHomSymm 2 (by decide)).comp
      (swapTail.selectedGradedHom 2 (by decide)) =
        GradedRingHom.id (component (polynomialGrade (ZMod 4 × ZMod 4)) 2) :=
  swapTail.selectedGradedHomSymm_comp 2 (by decide)

theorem swap_selected_inverse_other :
    (swapTail.selectedGradedHom 2 (by decide)).comp
      (swapTail.selectedGradedHomSymm 2 (by decide)) =
        GradedRingHom.id (component (polynomialGrade (ZMod 4 × ZMod 4)) 2) :=
  swapTail.selectedGradedHom_comp_symm 2 (by decide)

def zeroTail : TailEquiv (polynomialGrade (ZMod 1))
    (polynomialGrade (ZMod 1)) 2 :=
  polynomialTail (RingEquiv.refl _)

theorem zero_selected_inverse :
    (zeroTail.selectedGradedHomSymm 2 (by decide)).comp
      (zeroTail.selectedGradedHom 2 (by decide)) =
        GradedRingHom.id (component (polynomialGrade (ZMod 1)) 2) :=
  zeroTail.selectedGradedHomSymm_comp 2 (by decide)

section MissingLinear

variable {T : Type*} [CommRing T] {σ : Type*} [SetLike σ T]
  [AddSubgroupClass σ T] (𝒢 : ℕ → σ) [GradedRing 𝒢]

/-- The graded subring obtained by deleting precisely the degree-one summand. -/
def noLinearSubring : Subring T where
  carrier := {t | (DirectSum.decompose 𝒢 t) 1 = 0}
  zero_mem' := by simp
  one_mem' := by
    have hunit : (1 : T) ∈ 𝒢 0 := SetLike.one_mem_graded 𝒢
    change (DirectSum.decompose 𝒢 ((⟨1, hunit⟩ : 𝒢 0) : T)) 1 = 0
    rw [DirectSum.decompose_coe]
    exact DirectSum.of_eq_of_ne 0 1 _ (by decide)
  add_mem' := by
    intro a b ha hb
    change (DirectSum.decompose 𝒢 a) 1 = 0 at ha
    change (DirectSum.decompose 𝒢 b) 1 = 0 at hb
    change (DirectSum.decompose 𝒢 (a + b)) 1 = 0
    simp [ha, hb]
  mul_mem' := by
    intro a b ha hb
    change (DirectSum.decompose 𝒢 a) 1 = 0 at ha
    change (DirectSum.decompose 𝒢 b) 1 = 0 at hb
    change (DirectSum.decompose 𝒢 (a * b)) 1 = 0
    rw [DirectSum.decompose_mul]
    apply Subtype.ext
    have hanti : Finset.antidiagonal (1 : ℕ) = {(0, 1), (1, 0)} := by decide
    rw [DirectSum.coe_mul_apply_eq_sum_antidiagonal, hanti]
    simp [ha, hb]
  neg_mem' := by
    intro a ha
    change (DirectSum.decompose 𝒢 a) 1 = 0 at ha
    change (DirectSum.decompose 𝒢 (-a)) 1 = 0
    rw [DirectSum.decompose_neg, DFinsupp.neg_apply, ha, neg_zero]

/-- The actual inherited degree-`d` part of `noLinearSubring`. -/
def noLinearGrade (d : ℕ) : AddSubgroup (noLinearSubring 𝒢) where
  carrier := {x | (x : T) ∈ 𝒢 d}
  zero_mem' := zero_mem (𝒢 d)
  add_mem' := by
    intro a b ha hb
    exact add_mem ha hb
  neg_mem' := by
    intro a ha
    exact neg_mem ha

theorem noLinearGrade_one_subsingleton (x : noLinearGrade 𝒢 1) : x = 0 := by
  apply Subtype.ext
  apply Subtype.ext
  have hx : (x : T) ∈ 𝒢 1 := x.property
  have hs := x.val.property
  change (DirectSum.decompose 𝒢 (x : T)) 1 = 0 at hs
  have hproj := DirectSum.decompose_of_mem_same 𝒢 hx
  rw [hs] at hproj
  exact hproj.symm

/-- Inclusion of each inherited component into its ambient component. -/
def noLinearIncludePiece (d : ℕ) : noLinearGrade 𝒢 d →+ 𝒢 d where
  toFun x := ⟨(x : T), x.property⟩
  map_zero' := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl

def noLinearIncludeSum : (⨁ d, noLinearGrade 𝒢 d) →+ (⨁ d, 𝒢 d) :=
  DirectSum.map (noLinearIncludePiece 𝒢)

theorem noLinearIncludeSum_coe (q : ⨁ d, noLinearGrade 𝒢 d) :
    (DirectSum.coeAddMonoidHom 𝒢) (noLinearIncludeSum 𝒢 q) =
      ((DirectSum.coeAddMonoidHom (noLinearGrade 𝒢) q : noLinearSubring 𝒢) : T) := by
  induction q using DirectSum.induction_on with
  | zero => simp
  | of d a => simp [noLinearIncludeSum, noLinearIncludePiece]
  | add a b ha hb =>
    simp only [map_add, ha, hb, Subring.coe_add]

theorem noLinearIncludeSum_injective : Function.Injective (noLinearIncludeSum 𝒢) := by
  apply (DirectSum.map_injective (noLinearIncludePiece 𝒢)).mpr
  intro d a b hab
  have h := congrArg Subtype.val hab
  change (a : T) = (b : T) at h
  apply Subtype.ext
  apply Subtype.ext
  exact h

/-- A component of any degree other than one belongs to the subring. -/
theorem noLinear_of_homogeneous {d : ℕ} (hd : d ≠ 1) (x : 𝒢 d) :
    (x : T) ∈ noLinearSubring 𝒢 := by
  change (DirectSum.decompose 𝒢 (x : T)) 1 = 0
  rw [DirectSum.decompose_coe, DirectSum.of_eq_of_ne]
  exact hd.symm

def noLinearLiftPiece (d : ℕ) : 𝒢 d →+ noLinearGrade 𝒢 d := by
  classical
  by_cases hd : d = 1
  · exact 0
  · exact {
      toFun := fun x => ⟨⟨(x : T), noLinear_of_homogeneous 𝒢 hd x⟩, x.property⟩
      map_zero' := Subtype.ext (Subtype.ext rfl)
      map_add' := fun _ _ => Subtype.ext (Subtype.ext rfl) }

theorem noLinearLiftPiece_include (d : ℕ) (hd : d ≠ 1) (x : 𝒢 d) :
    noLinearIncludePiece 𝒢 d (noLinearLiftPiece 𝒢 d x) = x := by
  apply Subtype.ext
  simp [noLinearLiftPiece, hd, noLinearIncludePiece]

theorem noLinearIncludeSum_surjective :
    Function.Surjective (DirectSum.coeAddMonoidHom (noLinearGrade 𝒢)) := by
  classical
  intro s
  let q := DirectSum.decompose 𝒢 (s : T)
  let lift : ⨁ d, noLinearGrade 𝒢 d := DirectSum.map (noLinearLiftPiece 𝒢) q
  have hq : noLinearIncludeSum 𝒢 lift = q := by
    apply DirectSum.ext
    intro d
    simp only [lift, noLinearIncludeSum, DirectSum.map_apply]
    by_cases hd : d = 1
    · subst d
      have hfirst : q 1 = 0 := s.property
      rw [hfirst]
      simp
    · exact noLinearLiftPiece_include 𝒢 d hd (q d)
  refine ⟨lift, ?_⟩
  apply Subtype.ext
  rw [← noLinearIncludeSum_coe 𝒢 lift, hq]
  exact (DirectSum.decompose 𝒢).symm_apply_apply (s : T)

theorem noLinearIncludeSum_injective_coe :
    Function.Injective (DirectSum.coeAddMonoidHom (noLinearGrade 𝒢)) := by
  intro q q' heq
  apply noLinearIncludeSum_injective 𝒢
  apply (DirectSum.decompose 𝒢).symm.injective
  change (DirectSum.coeAddMonoidHom 𝒢) (noLinearIncludeSum 𝒢 q) =
    (DirectSum.coeAddMonoidHom 𝒢) (noLinearIncludeSum 𝒢 q')
  rw [noLinearIncludeSum_coe, noLinearIncludeSum_coe, heq]

instance noLinearGradedRing : GradedRing (noLinearGrade 𝒢) := by
  let equiv : (⨁ d, noLinearGrade 𝒢 d) ≃ noLinearSubring 𝒢 :=
    Equiv.ofBijective (DirectSum.coeAddMonoidHom (noLinearGrade 𝒢))
      ⟨noLinearIncludeSum_injective_coe 𝒢, noLinearIncludeSum_surjective 𝒢⟩
  exact {
    one_mem := SetLike.one_mem_graded 𝒢
    mul_mem := by
      intro i j x y hx hy
      change (x : T) ∈ 𝒢 i at hx
      change (y : T) ∈ 𝒢 j at hy
      change ((x : T) * (y : T)) ∈ 𝒢 (i + j)
      exact SetLike.GradedMul.mul_mem hx hy
    decompose' := equiv.symm
    left_inv := equiv.apply_symm_apply
    right_inv := equiv.symm_apply_apply }

/-- Inclusion is an additive equivalence at every degree except one. -/
def noLinearPieceEquiv (d : ℕ) (hd : d ≠ 1) : 𝒢 d ≃+ noLinearGrade 𝒢 d where
  toFun := noLinearLiftPiece 𝒢 d
  invFun := noLinearIncludePiece 𝒢 d
  left_inv := noLinearLiftPiece_include 𝒢 d hd
  right_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    simp [noLinearLiftPiece, hd, noLinearIncludePiece]
  map_add' := (noLinearLiftPiece 𝒢 d).map_add

@[simp] theorem noLinearPieceEquiv_coe (d : ℕ) (hd : d ≠ 1) (x : 𝒢 d) :
    (((noLinearPieceEquiv 𝒢 d hd x : noLinearGrade 𝒢 d) : noLinearSubring 𝒢) : T) = x :=
  congrArg Subtype.val (noLinearLiftPiece_include 𝒢 d hd x)

def noLinearZeroEquiv : 𝒢 0 ≃+* noLinearGrade 𝒢 0 where
  __ := noLinearPieceEquiv 𝒢 0 (by decide)
  map_mul' a b := by
    apply Subtype.ext
    apply Subtype.ext
    change (a : T) * (b : T) = (a : T) * (b : T)
    rfl

@[simp] theorem noLinearZeroEquiv_coe (x : 𝒢 0) :
    (((noLinearZeroEquiv 𝒢 x : noLinearGrade 𝒢 0) : noLinearSubring 𝒢) : T) = x :=
  noLinearPieceEquiv_coe 𝒢 0 (by decide) x

def noLinearTail : TailEquiv 𝒢 (noLinearGrade 𝒢) 2 where
  positive := by decide
  zero := noLinearZeroEquiv 𝒢
  high d hd := noLinearPieceEquiv 𝒢 d (by omega)
  coeff d hd a x := by
    apply Subtype.ext
    simp only [noLinearPieceEquiv_coe, noLinearZeroEquiv_coe, Subring.coe_mul]
  product d k hd hk x y := by
    apply Subtype.ext
    simp only [noLinearPieceEquiv_coe, Subring.coe_mul]

end MissingLinear

abbrev integerPolynomialGrade := polynomialGrade ℤ

abbrev integerNoLinear := noLinearSubring integerPolynomialGrade

abbrev integerNoLinearGrade := noLinearGrade integerPolynomialGrade

def missingLinearTail : TailEquiv integerPolynomialGrade integerNoLinearGrade 2 :=
  noLinearTail integerPolynomialGrade

def missingLinearSelected : VeroneseRing integerPolynomialGrade 2 ≃+*
    VeroneseRing integerNoLinearGrade 2 :=
  missingLinearTail.selectedRingEquiv 2 (by decide)

/-- There is no graded extension of the selected tail identity across degree one. -/
theorem missingLinear_no_extension
    (f : integerPolynomialGrade →+*ᵍ integerNoLinearGrade)
    (hhigh : ∀ d, 2 ≤ d → ∀ x : integerPolynomialGrade d,
      ((f (x : MvPolynomial Unit ℤ) : integerNoLinear) : MvPolynomial Unit ℤ) = x) :
    False := by
  let xOne : integerPolynomialGrade 1 :=
    ⟨MvPolynomial.X (), MvPolynomial.isHomogeneous_X ℤ ()⟩
  have hx : f (MvPolynomial.X () : MvPolynomial Unit ℤ) = 0 := by
    have hzero := noLinearGrade_one_subsingleton integerPolynomialGrade
      (⟨f (MvPolynomial.X () : MvPolynomial Unit ℤ), f.map_mem xOne.property⟩ :
        integerNoLinearGrade 1)
    exact congrArg Subtype.val hzero
  let xTwo : integerPolynomialGrade 2 :=
    ⟨(MvPolynomial.X () : MvPolynomial Unit ℤ) ^ 2,
      MvPolynomial.isHomogeneous_X_pow () 2⟩
  have hzero : f ((MvPolynomial.X () : MvPolynomial Unit ℤ) ^ 2) = 0 := by
    rw [map_pow, hx, zero_pow (by decide : 2 ≠ 0)]
  have hp : (MvPolynomial.X () : MvPolynomial Unit ℤ) ^ 2 = 0 := by
    have htwo := hhigh 2 (by decide) xTwo
    simpa only [xTwo, hzero, Subring.coe_zero] using htwo.symm
  exact (pow_ne_zero 2 (MvPolynomial.X_ne_zero ())) hp

end GradedRingsTest.CoherentTailVeronese
