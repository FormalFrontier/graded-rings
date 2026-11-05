/-
Copyright (c) 2026 Formal Frontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rudder
-/
module

public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.BigOperators.NatAntidiagonal
public import Mathlib.Algebra.Module.End
import Mathlib.Algebra.Module.Hom
import Mathlib.Algebra.Module.RingHom
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.LinearAlgebra.Finsupp.Defs

/-!
# Extension of a module to polynomial scalars

For a semiring `R` and an additive commutative monoid `M` with its given `R`-module
structure, `PolynomialModule.Extension R M` is extension of scalars along
`Polynomial.C`. Its elements are finitely supported sequences in `M`. Constants act
by the given coefficient action, and the polynomial variable acts by successor shift.

The polynomial action is evaluation in additive endomorphisms. In particular, neither
commutativity of the coefficient semiring nor an additive group structure is required.
Additional coefficientwise scalar actions are available as explicit module structures,
not as global instances.

## References

The coefficient model and successor-shift action generalize Mathlib's `PolynomialModule`
construction by Andrew Yang in `Mathlib/Algebra/Polynomial/Module/Basic.lean`.
-/

@[expose] public noncomputable section

universe u v w

open Polynomial

namespace PolynomialModule

/-- The extension of an `R`-module to polynomial scalars, represented by finitely
supported coefficients. The coefficient-semiring parameter distinguishes coefficient
scalars from polynomial-variable scalars. -/
structure Extension (R : Type u) (M : Type v) [Semiring R] [AddCommMonoid M]
    [Module R M] : Type v where
  /-- Construct an element from its finitely supported coefficients. -/
  ofCoeff (R) ::
  /-- The finitely supported sequence of coefficients. -/
  coeff : ℕ →₀ M

namespace Extension

variable {R : Type u} {M : Type v} [Semiring R] [AddCommMonoid M] [Module R M]

@[simp] theorem coeff_ofCoeff (f : ℕ →₀ M) : coeff (ofCoeff R f) = f := rfl
@[simp] theorem ofCoeff_coeff (q : Extension R M) : ofCoeff R q.coeff = q := rfl

/-- The coefficient equivalence. -/
def coeffEquiv (R : Type u) (M : Type v) [Semiring R] [AddCommMonoid M]
    [Module R M] : Extension R M ≃ (ℕ →₀ M) where
  toFun := coeff
  invFun := ofCoeff R
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem coeffEquiv_apply (q : Extension R M) : coeffEquiv R M q = q.coeff := rfl
@[simp] theorem coeffEquiv_symm_apply (f : ℕ →₀ M) :
    (coeffEquiv R M).symm f = ofCoeff R f := rfl

@[ext] theorem ext {q q' : Extension R M} (h : q.coeff = q'.coeff) : q = q' :=
  (coeffEquiv R M).injective h

instance : AddCommMonoid (Extension R M) := (coeffEquiv R M).addCommMonoid

/-- The additive coefficient equivalence. -/
def coeffAddEquiv (R : Type u) (M : Type v) [Semiring R] [AddCommMonoid M]
    [Module R M] : Extension R M ≃+ (ℕ →₀ M) := (coeffEquiv R M).addEquiv

@[simp] theorem coeffAddEquiv_apply (q : Extension R M) :
    coeffAddEquiv R M q = q.coeff := rfl
@[simp] theorem coeffAddEquiv_symm_apply (f : ℕ →₀ M) :
    (coeffAddEquiv R M).symm f = ofCoeff R f := rfl

@[simp] theorem coeff_zero : coeff (0 : Extension R M) = 0 := rfl
@[simp] theorem ofCoeff_zero : ofCoeff R (0 : ℕ →₀ M) = 0 := rfl
@[simp] theorem coeff_add (q q' : Extension R M) :
    coeff (q + q') = q.coeff + q'.coeff := rfl
@[simp] theorem ofCoeff_add (f g : ℕ →₀ M) :
    ofCoeff R (f + g) = ofCoeff R f + ofCoeff R g := rfl
@[simp] theorem coeff_eq_zero {q : Extension R M} : q.coeff = 0 ↔ q = 0 :=
  (coeffAddEquiv R M).map_eq_zero_iff

@[simp] theorem coeff_sum {ι : Type*} (s : Finset ι) (f : ι → Extension R M) :
    coeff (∑ i ∈ s, f i) = ∑ i ∈ s, coeff (f i) :=
  map_sum (coeffAddEquiv R M) ..

@[simp] theorem coeff_finsuppSum {ι N : Type*} [AddCommMonoid N]
    (f : ι →₀ N) (g : ι → N → Extension R M) :
    coeff (f.sum g) = f.sum (fun i n ↦ coeff (g i n)) :=
  map_finsuppSum (coeffAddEquiv R M) ..

@[simp] theorem ofCoeff_finsuppSum {ι N : Type*} [AddCommMonoid N]
    (f : ι →₀ N) (g : ι → N → ℕ →₀ M) :
    ofCoeff R (f.sum g) = f.sum (fun i n ↦ ofCoeff R (g i n)) :=
  map_finsuppSum (coeffAddEquiv R M).symm ..

/-- A sequence supported in one degree. -/
def single (R : Type u) {M : Type v} [Semiring R] [AddCommMonoid M] [Module R M]
    (n : ℕ) (m : M) : Extension R M := ofCoeff R (Finsupp.single n m)

@[simp] theorem coeff_single (n : ℕ) (m : M) :
    coeff (single R n m) = Finsupp.single n m := rfl
@[simp] theorem ofCoeff_single (n : ℕ) (m : M) :
    ofCoeff R (Finsupp.single n m) = single R n m := rfl

theorem coeff_single_apply (n : ℕ) (m : M) (k : ℕ) :
    coeff (single R n m) k = if n = k then m else 0 := Finsupp.single_apply

@[simp] theorem single_zero (n : ℕ) : single R n (0 : M) = 0 := by
  apply ext
  simp

@[simp] theorem single_add (n : ℕ) (m m' : M) :
    single R n (m + m') = single R n m + single R n m' := by
  apply ext
  simp

/-- The sum of the coefficients of a polynomial module element. -/
def coefficientSum : Extension R M →+ M :=
  (Finsupp.liftAddHom (fun _ : ℕ => AddMonoidHom.id M)).comp
    (coeffAddEquiv R M).toAddMonoidHom

/-- Coefficient sum is the finite sum over the coefficient support. -/
theorem coefficientSum_apply (q : Extension R M) :
    coefficientSum q = q.coeff.sum (fun _ m => m) := rfl

@[simp] theorem coefficientSum_ofCoeff (f : ℕ →₀ M) :
    coefficientSum (ofCoeff R f) = f.sum (fun _ m => m) := rfl

@[simp] theorem coefficientSum_single (n : ℕ) (m : M) :
    coefficientSum (single R n m) = m := by
  change coefficientSum (ofCoeff R (Finsupp.single n m)) = m
  rw [coefficientSum_ofCoeff]
  exact Finsupp.sum_single_index rfl

theorem coefficientSum_add (q q' : Extension R M) :
    coefficientSum (q + q') = coefficientSum q + coefficientSum q' :=
  map_add coefficientSum q q'

/-- Every element is the finite sum of its single coefficients. -/
theorem sum_single (q : Extension R M) : q.coeff.sum (single R) = q := by
  apply ext
  simpa only [coeff_finsuppSum, coeff_single] using Finsupp.sum_single q.coeff

/-- Additive induction on single coefficients. -/
@[elab_as_elim] theorem induction_linear {P : Extension R M → Prop} (q : Extension R M)
    (zero : P 0) (add : ∀ x y : Extension R M, P x → P y → P (x + y))
    (single : ∀ n m, P (Extension.single R n m)) : P q :=
  Finsupp.induction_linear (motive := (P <| ofCoeff R ·)) q.coeff zero (fun _ _ ↦ add _ _)
    (fun _ _ ↦ single _ _)

/-- The coefficientwise action of the original coefficient semiring. -/
instance coefficientModule : Module R (Extension R M) := (coeffAddEquiv R M).module R

@[simp] theorem coeff_rsmul (r : R) (q : Extension R M) :
    coeff (r • q) = r • q.coeff := rfl

@[simp] theorem coeff_rsmul_apply (r : R) (q : Extension R M) (n : ℕ) :
    coeff (r • q) n = r • q.coeff n := Finsupp.smul_apply ..

/-- The coefficient equivalence for the original coefficient action. -/
def coeffLinearEquiv (R : Type u) (M : Type v) [Semiring R] [AddCommMonoid M]
    [Module R M] : Extension R M ≃ₗ[R] (ℕ →₀ M) := (coeffAddEquiv R M).linearEquiv R

@[simp] theorem coeffLinearEquiv_apply (q : Extension R M) :
    coeffLinearEquiv R M q = q.coeff := rfl
@[simp] theorem coeffLinearEquiv_symm_apply (f : ℕ →₀ M) :
    (coeffLinearEquiv R M).symm f = ofCoeff R f := rfl

@[simp] theorem single_smul (r : R) (n : ℕ) (m : M) :
    single R n (r • m) = r • single R n m := by
  apply ext
  simp

/-- Insertion in one degree as an `R`-linear map. -/
def lsingle (R : Type u) {M : Type v} [Semiring R] [AddCommMonoid M] [Module R M]
    (n : ℕ) : M →ₗ[R] Extension R M :=
  (coeffLinearEquiv R M).symm.toLinearMap.comp (Finsupp.lsingle n)

@[simp] theorem lsingle_apply (n : ℕ) (m : M) : lsingle R n m = single R n m := rfl

/-- Explicit coefficientwise module data for an additional scalar semiring. This is
not a global instance: the dedicated polynomial action is distinct from an incidental
coefficientwise polynomial action on `M`. -/
@[instance_reducible] def pointwiseModule (S : Type w) [Semiring S] [Module S M] :
    Module S (Extension R M) := (coeffAddEquiv R M).module S

/-- The scalar operation of `pointwiseModule`. -/
def pointwiseSMul (S : Type w) [Semiring S] [Module S M] (s : S) (q : Extension R M) :
    Extension R M :=
  @SMul.smul S (Extension R M) (pointwiseModule (R := R) (M := M) S).toSMul s q

@[simp] theorem coeff_pointwiseSMul (S : Type w) [Semiring S] [Module S M]
    (s : S) (q : Extension R M) : coeff (pointwiseSMul S s q) = s • q.coeff := rfl

@[simp] theorem coeff_pointwiseSMul_apply (S : Type w) [Semiring S] [Module S M]
    (s : S) (q : Extension R M) (n : ℕ) :
    coeff (pointwiseSMul S s q) n = s • q.coeff n := Finsupp.smul_apply ..

/-- The coefficientwise linear equivalence for the explicitly specified additional
scalar action. Its source module structure is `pointwiseModule S`. -/
def pointwiseCoeffLinearEquiv (S : Type w) [Semiring S] [Module S M] :
    letI := pointwiseModule (R := R) (M := M) S
    Extension R M ≃ₗ[S] (ℕ →₀ M) := by
  letI := pointwiseModule (R := R) (M := M) S
  exact (coeffAddEquiv R M).linearEquiv S

@[simp] theorem pointwiseCoeffLinearEquiv_apply (S : Type w) [Semiring S] [Module S M]
    (q : Extension R M) : pointwiseCoeffLinearEquiv (R := R) (M := M) S q = q.coeff := rfl

@[simp] theorem pointwiseCoeffLinearEquiv_symm_apply (S : Type w) [Semiring S] [Module S M]
    (f : ℕ →₀ M) :
    (pointwiseCoeffLinearEquiv (R := R) (M := M) S).symm f = ofCoeff R f := rfl

private def shiftEnd : AddMonoid.End (ℕ →₀ M) :=
  (Finsupp.lmapDomain M R Nat.succ).toAddMonoidHom

/-- The polynomial action obtained by evaluating additive endomorphisms at successor
shift, transported through the coefficient equivalence. -/
instance polynomialModule : Module R[X] (Extension R M) := by
  let c : R →+* AddMonoid.End (ℕ →₀ M) := Module.toAddMonoidEnd R _
  let T : AddMonoid.End (ℕ →₀ M) :=
    (Finsupp.lmapDomain M R Nat.succ).toAddMonoidHom
  let e : R[X] →+* AddMonoid.End (ℕ →₀ M) :=
    Polynomial.eval₂RingHom' c T (fun r ↦ by
      change c r * T = T * c r
      apply AddMonoidHom.ext
      intro f
      exact ((Finsupp.lmapDomain M R Nat.succ).map_smul r f).symm)
  letI : Module R[X] (ℕ →₀ M) := Module.compHom (ℕ →₀ M) e
  exact (coeffAddEquiv R M).module R[X]

/-- Polynomial scalar multiplication is evaluation at successor shift. -/
theorem smul_def (p : R[X]) (q : Extension R M) :
    coeff (p • q) =
      (Polynomial.eval₂ (Module.toAddMonoidEnd R (ℕ →₀ M))
        (Finsupp.lmapDomain M R Nat.succ).toAddMonoidHom p) q.coeff := rfl

/-- Constants act by the original coefficient action. -/
@[simp] theorem C_smul (r : R) (q : Extension R M) : (C r) • q = r • q := by
  apply ext
  rw [smul_def]
  exact congrArg (fun f : AddMonoid.End (ℕ →₀ M) ↦ f q.coeff)
    (Polynomial.eval₂_C ..)

theorem coeff_C_smul (r : R) (q : Extension R M) (n : ℕ) :
    coeff ((C r) • q) n = r • q.coeff n := by
  rw [C_smul, coeff_rsmul_apply]

/-- The polynomial variable acts by successor shift. -/
theorem X_smul (q : Extension R M) :
    (X : R[X]) • q = ofCoeff R (Finsupp.mapDomain Nat.succ q.coeff) := by
  apply ext
  rw [smul_def]
  exact congrArg (fun f : AddMonoid.End (ℕ →₀ M) ↦ f q.coeff)
    (Polynomial.eval₂_X ..)

theorem coeff_X_smul (q : Extension R M) :
    coeff ((X : R[X]) • q) = Finsupp.mapDomain Nat.succ q.coeff := by
  rw [X_smul, coeff_ofCoeff]

@[simp] theorem coeff_X_smul_zero (q : Extension R M) :
    coeff ((X : R[X]) • q) 0 = 0 := by
  rw [X_smul, coeff_ofCoeff]
  exact Finsupp.mapDomain_of_notMem_range _ _ (by simp)

@[simp] theorem coeff_X_smul_succ (q : Extension R M) (n : ℕ) :
    coeff ((X : R[X]) • q) (n + 1) = q.coeff n := by
  rw [X_smul, coeff_ofCoeff]
  exact Finsupp.mapDomain_apply_of_injective Nat.succ_injective _ n

@[simp] theorem X_smul_single (n : ℕ) (m : M) :
    (X : R[X]) • single R n m = single R (n + 1) m := by
  rw [X_smul]
  simp only [coeff_single, Finsupp.mapDomain_single, ofCoeff_single]

private theorem shiftEnd_pow_single (a b : ℕ) (m : M) :
    (shiftEnd (R := R) (M := M) ^ a) (Finsupp.single b m) =
      Finsupp.single (a + b) m := by
  induction a with
  | zero =>
    change Finsupp.single b m = Finsupp.single (0 + b) m
    rw [zero_add]
  | succ a ih =>
    rw [pow_succ']
    change Finsupp.mapDomain Nat.succ
      ((shiftEnd (R := R) (M := M) ^ a) (Finsupp.single b m)) = _
    rw [ih]
    simp only [Finsupp.mapDomain_single, Nat.succ_add]

/-- A monomial shifts a single coefficient and acts on it on the left. -/
@[simp] theorem monomial_smul_single (a : ℕ) (r : R) (b : ℕ) (m : M) :
    (monomial a r) • single R b m = single R (a + b) (r • m) := by
  apply ext
  rw [smul_def]
  trans ((Module.toAddMonoidEnd R (ℕ →₀ M)) r *
    shiftEnd (R := R) (M := M) ^ a) (Finsupp.single b m)
  · exact congrArg (fun f : AddMonoid.End (ℕ →₀ M) ↦ f (Finsupp.single b m))
      (Polynomial.eval₂_monomial ..)
  · change r • ((shiftEnd (R := R) (M := M) ^ a) (Finsupp.single b m)) = _
    rw [shiftEnd_pow_single, Finsupp.smul_single]; rfl

/-- Insertion in one degree is semilinear along the coefficient inclusion. -/
def csingle (R : Type u) {M : Type v} [Semiring R] [AddCommMonoid M] [Module R M]
    (n : ℕ) : M →ₛₗ[Polynomial.C (R := R)] Extension R M where
  toFun := single R n
  map_add' := single_add n
  map_smul' r m := by rw [C_smul, single_smul]

@[simp] theorem csingle_apply (n : ℕ) (m : M) : csingle R n m = single R n m := rfl

/-- Coefficient sum respects the coefficient action. -/
@[simp] theorem coefficientSum_rsmul (r : R) (q : Extension R M) :
    coefficientSum (r • q) = r • coefficientSum q := by
  refine induction_linear q ?_ ?_ ?_
  · simp
  · intro x y hx hy
    simp only [smul_add, coefficientSum_add, hx, hy]
  · intro n m
    rw [← single_smul, coefficientSum_single, coefficientSum_single]

/-- A constant polynomial acts on coefficient sum through its coefficient. -/
theorem coefficientSum_C_smul (r : R) (q : Extension R M) :
    coefficientSum ((C r) • q) = r • coefficientSum q := by
  rw [C_smul, coefficientSum_rsmul]

/-- Successor shift preserves coefficient sum. -/
@[simp] theorem coefficientSum_X_smul (q : Extension R M) :
    coefficientSum ((X : R[X]) • q) = coefficientSum q := by
  refine induction_linear q ?_ ?_ ?_
  · simp
  · intro x y hx hy
    simp only [smul_add, coefficientSum_add, hx, hy]
  · intro n m
    simp only [X_smul_single, coefficientSum_single]

/-- Polynomial scalar multiplication evaluates the scalar at one on coefficient sum. -/
theorem coefficientSum_smul (p : R[X]) (q : Extension R M) :
    coefficientSum (p • q) =
      (Polynomial.eval₂AddMonoidHom (RingHom.id R) (1 : R)) p • coefficientSum q := by
  refine Polynomial.induction_on' p ?_ ?_
  · intro p p' hp hp'
    simp only [add_smul, hp, hp', map_add]
  · intro n r
    refine induction_linear q ?_ ?_ ?_
    · simp
    · intro x y hx hy
      simp only [smul_add, coefficientSum_add, hx, hy]
    · intro k m
      simp [Polynomial.eval₂AddMonoidHom]

/-- The coefficient of a monomial acting on an arbitrary sequence. -/
theorem monomial_smul_apply (a : ℕ) (r : R) (q : Extension R M) (n : ℕ) :
    coeff ((monomial a r) • q) n = if a ≤ n then r • q.coeff (n - a) else 0 := by
  induction q using induction_linear with
  | zero => simp
  | add q q' hq hq' => simp [smul_add, hq, hq', ite_add_ite]
  | single =>
    simp [monomial_smul_single, Finsupp.single_apply]; grind

/-- The coefficient of a polynomial acting on a single coefficient. -/
@[simp] theorem smul_single_apply (a : ℕ) (p : R[X]) (m : M) (n : ℕ) :
    coeff (p • single R a m) n = if a ≤ n then p.coeff (n - a) • m else 0 := by
  induction p using Polynomial.induction_on' with
  | add p p' hp hp' =>
    have hcoeff : (p + p').coeff = p.coeff + p'.coeff := by
      ext i
      have h := congrArg
        (fun f : AddMonoidAlgebra R ℕ =>
          (AddMonoidAlgebra.coeffLinearEquiv R f) i)
        (Polynomial.toFinsupp_add p p')
      rw [map_add] at h
      simpa only [AddMonoidAlgebra.coeffLinearEquiv_apply, Finsupp.add_apply,
        Polynomial.toFinsupp_apply] using h
    simp [add_smul, hp, hp', ite_add_ite, hcoeff]
  | monomial =>
    simp [monomial_smul_single, Polynomial.coeff_monomial, Finsupp.single_apply]; grind

/-- The coefficient of polynomial scalar multiplication is the antidiagonal sum of
left coefficient actions. -/
theorem coeff_smul (p : R[X]) (q : Extension R M) (n : ℕ) :
    coeff (p • q) n =
      ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal n, p.coeff ab.1 • q.coeff ab.2 := by
  induction p using Polynomial.induction_on' with
  | add p p' hp hp' =>
    have hcoeff : (p + p').coeff = p.coeff + p'.coeff := by
      ext i
      have h := congrArg
        (fun f : AddMonoidAlgebra R ℕ =>
          (AddMonoidAlgebra.coeffLinearEquiv R f) i)
        (Polynomial.toFinsupp_add p p')
      rw [map_add] at h
      simpa only [AddMonoidAlgebra.coeffLinearEquiv_apply, Finsupp.add_apply,
        Polynomial.toFinsupp_apply] using h
    simp only [add_smul, coeff_add, Finsupp.add_apply, hp, hp', hcoeff,
      Finset.sum_add_distrib]
  | monomial a r =>
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j =>
      (monomial a r).coeff i • q.coeff j) n, monomial_smul_apply]
    simp [Polynomial.coeff_monomial, Nat.lt_succ_iff]

/-- The antidiagonal coefficient formula for polynomial scalar multiplication. -/
theorem smul_apply (p : R[X]) (q : Extension R M) (n : ℕ) :
    coeff (p • q) n =
      ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal n, p.coeff ab.1 • q.coeff ab.2 :=
  coeff_smul p q n

/-- The degrees with nonzero coefficients. -/
def support (q : Extension R M) : Finset ℕ := q.coeff.support

@[simp] theorem mem_support (q : Extension R M) (n : ℕ) :
    n ∈ q.support ↔ q.coeff n ≠ 0 := Finsupp.mem_support_iff

@[simp] theorem support_zero : support (0 : Extension R M) = ∅ := rfl

/-- Polynomial scalar multiplication has support contained in the sum of the two
coefficient supports. -/
theorem support_smul (p : R[X]) (q : Extension R M) :
    support (p • q) ⊆ Finset.image₂ (· + ·) p.support q.support := by
  classical
  intro n hn
  by_contra h
  have hz : coeff (p • q) n = 0 := by
    rw [coeff_smul]
    apply Finset.sum_eq_zero
    intro ab hab
    by_cases hp : p.coeff ab.1 = 0
    · rw [hp, zero_smul]
    by_cases hq : q.coeff ab.2 = 0
    · rw [hq, smul_zero]
    exfalso
    apply h
    exact Finset.mem_image₂.mpr
      ⟨ab.1, by simpa using hp, ab.2, by simpa using hq, by simpa using hab⟩
  exact (mem_support _ _).mp hn hz

end Extension
end PolynomialModule
