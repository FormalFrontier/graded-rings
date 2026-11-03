/-
Copyright (c) 2026 Formal Frontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rudder
-/
module

import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Ring.Pi
public import GradedRings.PolynomialModule.Basic

/-!
# The universal property of polynomial module extension

Polynomial module extension is extension of scalars along `Polynomial.C`: polynomial-linear
maps out of an extension are equivalent, additively, to coefficient-semilinear maps out of
the original module. The target needs only its polynomial module structure.

Coefficient-semilinear maps also extend coefficientwise along the induced polynomial hom.
Coordinate projection for dependent products is a specialization of this construction; it
requires no finiteness or nonemptiness assumption on the coordinate type.

The additive lift and coefficientwise map use Mathlib's Finsupp constructions.
-/

@[expose] public noncomputable section

open Polynomial

namespace PolynomialModule.Extension

universe uR uS uT uM uN uP uI

section Additive

variable {R : Type uR} [Semiring R]
variable {M : Type uM} [AddCommMonoid M] [Module R M]

private theorem addHom_ext {A : Type*} [AddCommMonoid A]
    {F G : Extension R M →+ A}
    (h : ∀ n m, F (single R n m) = G (single R n m)) : F = G := by
  apply AddMonoidHom.ext
  intro q
  induction q using induction_linear with
  | zero => simp
  | add q q' hq hq' => simp only [map_add, hq, hq']
  | single n m => exact h n m

end Additive

section UniversalProperty

variable {R : Type uR} [Semiring R]
variable {M : Type uM} [AddCommMonoid M] [Module R M]
variable {N : Type uN} [AddCommMonoid N] [Module R[X] N]

/-- Restriction of a polynomial-linear map to the degree-zero coefficients. -/
def restrict (L : Extension R M →ₗ[R[X]] N) :
    M →ₛₗ[(Polynomial.C : R →+* R[X])] N where
  toFun m := L (single R 0 m)
  map_add' m m' := by simp
  map_smul' r m := by
    rw [← L.map_smul]
    congr 1
    simp

@[simp]
theorem restrict_apply (L : Extension R M →ₗ[R[X]] N) (m : M) :
    restrict L m = L (single R 0 m) := rfl

private def liftAddHom (g : M →ₛₗ[(Polynomial.C : R →+* R[X])] N) :
    Extension R M →+ N :=
  (Finsupp.liftAddHom fun n : ℕ =>
    (Module.toAddMonoidEnd R[X] N (Polynomial.monomial n 1 : R[X])).comp
      g.toAddMonoidHom).comp
    (coeffAddEquiv R M).toAddMonoidHom

private theorem liftAddHom_apply (g : M →ₛₗ[(Polynomial.C : R →+* R[X])] N)
    (q : Extension R M) :
    liftAddHom g q = (coeff q).sum fun n m => (Polynomial.monomial n 1 : R[X]) • g m := rfl

private theorem liftAddHom_single (g : M →ₛₗ[(Polynomial.C : R →+* R[X])] N)
    (n : ℕ) (m : M) :
    liftAddHom g (single R n m) = (Polynomial.monomial n 1 : R[X]) • g m := by
  change Finsupp.liftAddHom
    (fun k : ℕ => (Module.toAddMonoidEnd R[X] N (Polynomial.monomial k 1 : R[X])).comp
      g.toAddMonoidHom) (Finsupp.single n m) = _
  exact Finsupp.liftAddHom_apply_single _ n m

private theorem monomial_smul_monomial_one (a b : ℕ) (r : R) (x : N) :
    (Polynomial.monomial a r) • ((Polynomial.monomial b 1 : R[X]) • x) =
      (Polynomial.monomial (a + b) 1 : R[X]) • (Polynomial.C r • x) := by
  rw [← mul_smul, ← mul_smul]
  change (Polynomial.monomial a r * (Polynomial.monomial b 1 : R[X])) • x =
    ((Polynomial.monomial (a + b) 1 : R[X]) * Polynomial.monomial 0 r) • x
  simp only [Polynomial.monomial_mul_monomial, mul_one, one_mul, Nat.add_zero]

/-- Extend a `Polynomial.C`-semilinear map by the finite sum of shifted coefficient images. -/
def lift (g : M →ₛₗ[(Polynomial.C : R →+* R[X])] N) :
    Extension R M →ₗ[R[X]] N where
  __ := (Finsupp.liftAddHom fun n : ℕ =>
    (Module.toAddMonoidEnd R[X] N (Polynomial.monomial n 1 : R[X])).comp
      g.toAddMonoidHom).comp
    (coeffAddEquiv R M).toAddMonoidHom
  map_smul' p q := by
    change liftAddHom g (p • q) = p • liftAddHom g q
    induction p using Polynomial.induction_on' with
    | add p p' hp hp' =>
        rw [add_smul, (liftAddHom g).map_add, hp, hp', add_smul]
    | monomial a r =>
        have hlin :
            (liftAddHom g).comp
                (Module.toAddMonoidEnd R[X] (Extension R M) (Polynomial.monomial a r)) =
              (Module.toAddMonoidEnd R[X] N (Polynomial.monomial a r)).comp
                (liftAddHom g) := by
          apply addHom_ext
          intro b m
          change liftAddHom g ((Polynomial.monomial a r) • single R b m) =
            (Polynomial.monomial a r) • liftAddHom g (single R b m)
          rw [monomial_smul_single, liftAddHom_single, liftAddHom_single, g.map_smulₛₗ]
          exact (monomial_smul_monomial_one a b r (g m)).symm
        exact DFunLike.congr_fun hlin q

/-- The extension is the additive finite sum of the shifted coefficient images. -/
theorem lift_apply (g : M →ₛₗ[(Polynomial.C : R →+* R[X])] N)
    (q : Extension R M) :
    lift g q = (coeff q).sum fun n m => (Polynomial.monomial n 1 : R[X]) • g m :=
  liftAddHom_apply g q

@[simp]
theorem lift_single (g : M →ₛₗ[(Polynomial.C : R →+* R[X])] N) (n : ℕ) (m : M) :
    lift g (single R n m) = (Polynomial.monomial n 1 : R[X]) • g m :=
  liftAddHom_single g n m

theorem lift_csingle (g : M →ₛₗ[(Polynomial.C : R →+* R[X])] N) (n : ℕ) (m : M) :
    lift g (csingle R n m) = (Polynomial.monomial n 1 : R[X]) • g m := by simp

/-- Polynomial-linear maps are determined by their degree-zero coefficient values. -/
@[ext]
theorem linearMap_ext {L K : Extension R M →ₗ[R[X]] N}
    (h : ∀ m, L (single R 0 m) = K (single R 0 m)) : L = K := by
  have hadd : L.toAddMonoidHom = K.toAddMonoidHom := by
    apply addHom_ext
    intro n m
    change L (single R n m) = K (single R n m)
    have hs : single R n m =
        (Polynomial.monomial n 1 : R[X]) • single R 0 m := by
      simp
    calc
      L (single R n m) =
          (Polynomial.monomial n 1 : R[X]) • L (single R 0 m) := by
        rw [hs, L.map_smul]
      _ = (Polynomial.monomial n 1 : R[X]) • K (single R 0 m) :=
        congrArg (fun x => (Polynomial.monomial n 1 : R[X]) • x) (h m)
      _ = K (single R n m) := by rw [hs, K.map_smul]
  exact LinearMap.ext fun q => DFunLike.congr_fun hadd q

/-- Restricting an extension recovers the coefficient-semilinear map. -/
@[simp]
theorem restrict_lift (g : M →ₛₗ[(Polynomial.C : R →+* R[X])] N) : restrict (lift g) = g := by
  apply LinearMap.ext
  intro m
  simp

/-- A polynomial-linear map is recovered by extending its degree-zero restriction. -/
@[simp]
theorem lift_restrict (L : Extension R M →ₗ[R[X]] N) : lift (restrict L) = L := by
  apply linearMap_ext
  intro m
  simp

/-- The polynomial-linear extension is unique with its prescribed degree-zero values. -/
theorem lift_unique (g : M →ₛₗ[(Polynomial.C : R →+* R[X])] N)
    (L : Extension R M →ₗ[R[X]] N)
    (h : ∀ m, L (single R 0 m) = g m) : L = lift g := by
  apply linearMap_ext
  intro m
  simpa using h m

/-- Extension along `Polynomial.C`, with the additive structures on both Hom spaces. -/
def universalProperty :
    (Extension R M →ₗ[R[X]] N) ≃+ (M →ₛₗ[(Polynomial.C : R →+* R[X])] N) where
  toFun := restrict
  invFun := lift
  left_inv := lift_restrict
  right_inv := restrict_lift
  map_add' L K := by
    apply LinearMap.ext
    intro m
    rfl

@[simp]
theorem universalProperty_apply (L : Extension R M →ₗ[R[X]] N) :
    universalProperty L = restrict L := rfl

@[simp]
theorem universalProperty_symm_apply (g : M →ₛₗ[(Polynomial.C : R →+* R[X])] N) :
    universalProperty.symm g = lift g := rfl

@[simp]
theorem restrict_add (L K : Extension R M →ₗ[R[X]] N) :
    restrict (L + K) = restrict L + restrict K :=
  universalProperty.map_add L K

@[simp]
theorem lift_add (g h : M →ₛₗ[(Polynomial.C : R →+* R[X])] N) :
    lift (g + h) = lift g + lift h :=
  universalProperty.symm.map_add g h

end UniversalProperty

section Map

variable {R : Type uR} {S : Type uS} {T : Type uT}
variable [Semiring R] [Semiring S] [Semiring T]
variable {M : Type uM} {N : Type uN} {P : Type uP}
variable [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]
variable [Module R M] [Module S N] [Module T P]
variable {σ : R →+* S} {τ : S →+* T}

private def mapAddHom (g : M →ₛₗ[σ] N) : Extension R M →+ Extension S N :=
  (coeffAddEquiv S N).symm.toAddMonoidHom.comp
    ((Finsupp.mapRange.linearMap g).toAddMonoidHom.comp
      (coeffAddEquiv R M).toAddMonoidHom)

private theorem mapAddHom_single (g : M →ₛₗ[σ] N) (n : ℕ) (m : M) :
    mapAddHom g (single R n m) = single S n (g m) := by
  apply (coeffAddEquiv S N).injective
  ext k
  change g (coeff (single R n m) k) = coeff (single S n (g m)) k
  by_cases h : n = k <;> simp [h]

/-- Extend a coefficient-semilinear map coefficientwise along the induced polynomial hom. -/
def map (g : M →ₛₗ[σ] N) :
    Extension R M →ₛₗ[Polynomial.mapRingHom σ] Extension S N where
  __ := (coeffAddEquiv S N).symm.toAddMonoidHom.comp
    ((Finsupp.mapRange.linearMap g).toAddMonoidHom.comp
      (coeffAddEquiv R M).toAddMonoidHom)
  map_smul' p q := by
    change mapAddHom g (p • q) = Polynomial.mapRingHom σ p • mapAddHom g q
    induction p using Polynomial.induction_on' with
    | add p p' hp hp' =>
        rw [add_smul, (mapAddHom g).map_add, hp, hp', map_add, add_smul]
    | monomial a r =>
        have hlin :
            (mapAddHom g).comp
                (Module.toAddMonoidEnd R[X] (Extension R M) (Polynomial.monomial a r)) =
              (Module.toAddMonoidEnd S[X] (Extension S N)
                (Polynomial.mapRingHom σ (Polynomial.monomial a r))).comp
                (mapAddHom g) := by
          apply addHom_ext
          intro b m
          change mapAddHom g ((Polynomial.monomial a r) • single R b m) =
            Polynomial.mapRingHom σ (Polynomial.monomial a r) •
              mapAddHom g (single R b m)
          rw [monomial_smul_single, mapAddHom_single, mapAddHom_single]
          rw [Polynomial.coe_mapRingHom, Polynomial.map_monomial,
            monomial_smul_single, g.map_smulₛₗ]
        exact DFunLike.congr_fun hlin q

@[simp]
theorem coeff_map (g : M →ₛₗ[σ] N) (q : Extension R M) (n : ℕ) :
    coeff (map g q) n = g (coeff q n) := rfl

@[simp]
theorem map_single (g : M →ₛₗ[σ] N) (n : ℕ) (m : M) :
    map g (single R n m) = single S n (g m) :=
  mapAddHom_single g n m

/-- The coefficientwise extension respects polynomial scalars through the induced hom. -/
theorem map_smul (g : M →ₛₗ[σ] N) (p : R[X]) (q : Extension R M) :
    map g (p • q) = Polynomial.mapRingHom σ p • map g q :=
  (map g).map_smulₛₗ p q

/-- Coefficientwise extension preserves the identity map. -/
@[simp]
theorem map_id (q : Extension R M) : map (LinearMap.id : M →ₗ[R] M) q = q := by
  apply (coeffAddEquiv R M).injective
  ext n
  rfl

/-- Coefficientwise extension preserves composition of semilinear maps. -/
theorem map_comp (g : N →ₛₗ[τ] P) (f : M →ₛₗ[σ] N) (q : Extension R M) :
    map (show M →ₛₗ[τ.comp σ] P from by
      letI : RingHomCompTriple σ τ (τ.comp σ) := ⟨rfl⟩
      exact g.comp f) q = map g (map f q) := by
  apply (coeffAddEquiv T P).injective
  ext n
  rfl

end Map

section Coordinate

variable {I : Type uI} (R : I → Type uR) (M : I → Type uM)
variable [∀ i, Semiring (R i)] [∀ i, AddCommMonoid (M i)] [∀ i, Module (R i) (M i)]

/-- Coordinate projection on extensions of the original dependent-product modules. -/
def coordinate (i : I) :
    Extension (∀ i, R i) (∀ i, M i) →ₛₗ[
      Polynomial.mapRingHom (Pi.evalRingHom R i)] Extension (R i) (M i) :=
  map
    ({ toFun := fun m => m i
       map_add' := fun _ _ => rfl
       map_smul' := fun _ _ => rfl } :
      (∀ j, M j) →ₛₗ[Pi.evalRingHom R i] M i)

@[simp]
theorem coeff_coordinate (i : I) (q : Extension (∀ i, R i) (∀ i, M i)) (n : ℕ) :
    coeff (coordinate R M i q) n = coeff q n i := rfl

@[simp]
theorem coordinate_single (i : I) (n : ℕ) (m : ∀ i, M i) :
    coordinate R M i (single (∀ i, R i) n m) =
      single (R i) n (m i) :=
  map_single _ n m

/-- Coordinate projection respects polynomial scalars through coordinate evaluation. -/
theorem coordinate_smul (i : I) (p : (∀ i, R i)[X])
    (q : Extension (∀ i, R i) (∀ i, M i)) :
    coordinate R M i (p • q) =
      Polynomial.mapRingHom (Pi.evalRingHom R i) p • coordinate R M i q :=
  (coordinate R M i).map_smulₛₗ p q

/-- At a coordinate, polynomial scalar multiplication is the antidiagonal sum of the
original coordinate scalar actions. -/
theorem coeff_coordinate_smul (i : I) (p : (∀ i, R i)[X])
    (q : Extension (∀ i, R i) (∀ i, M i)) (n : ℕ) :
    coeff (coordinate R M i (p • q)) n =
      ∑ ab ∈ Finset.antidiagonal n, (p.coeff ab.1) i • coeff q ab.2 i := by
  change (coeff (p • q) n) i = _
  simpa only [Finset.sum_apply, Pi.smul_apply'] using
    congrArg (fun m => m i) (coeff_smul p q n)

end Coordinate

end PolynomialModule.Extension
