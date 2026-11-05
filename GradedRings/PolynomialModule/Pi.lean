/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Polynomial.Module.Basic
public import Mathlib.LinearAlgebra.Pi
public import CoherentModules.LinearAlgebra.FinsuppPi
public import GradedRings.Polynomial.Pi
public import GradedRings.PolynomialModule.Regular
public import GradedRings.PolynomialModule.Comparison

/-!
# Polynomial modules over finite products

For a finite family of rings `R` and modules `M`, `PolynomialModule.piEquiv R M`
identifies the polynomial module of the product with the product of the polynomial
modules. It is semilinear along `Polynomial.piRingEquiv R`: a polynomial with product
coefficients acts in each coordinate by its corresponding polynomial.

The coefficient formulas characterize both directions. The single-coefficient formulas
and the monomial action formula let users work with supported elements directly.

`PolynomialModule.Extension.piEquiv R M` gives the corresponding equivalence for
canonical extensions of modules over semirings, with additive commutative monoid
coefficients. Its forward map is the coordinate projection, and its characteristic
lemmas describe coefficients and single-degree elements in both directions. At
commutative-ring and additive-group coefficients, the coefficient-preserving
comparison with `PolynomialModule` intertwines the two finite-product equivalences.

For a single semiring `R`, `PolynomialModule.Extension.piLinearEquiv R M ι` identifies
the extension of `ι → M` with `ι → Extension R M`, using the original `R`-module
structure on `M`. The regular specialization `PolynomialModule.Extension.piRegularEquiv R ι`
identifies the extension of a finite free module with a finite tuple of polynomials.

## Implementation notes

The additive equivalence composes Mathlib's `PolynomialModule.coeffAddEquiv` with
CoherentModules' `Finsupp.piLinearEquiv` and the coordinate coefficient equivalences.
Polynomial semilinearity follows from Mathlib's convolution formula for the polynomial
module action and the coefficient formula for `Polynomial.piRingEquiv`.
Finiteness is needed only for the coordinate index; the index, ring and module universes
are independent. No nonemptiness hypothesis is imposed.
For `Extension.piEquiv`, the additive construction uses the same finite-product
coefficient equivalence, while polynomial semilinearity follows from
`PolynomialModule.Extension.coordinate_smul`.
For homogeneous finite functions, the forward map extends each coefficient projection,
and the inverse is a finite sum of extended coordinate inclusions. The regular
specialization then applies `Extension.regularEquiv` pointwise.
-/

@[expose] public section

universe uI uR uM

namespace PolynomialModule

variable {ι : Type uI} (R : ι → Type uR) (M : ι → Type uM)
variable [Finite ι] [∀ i, CommRing (R i)]
variable [∀ i, AddCommGroup (M i)] [∀ i, Module (R i) (M i)]

private theorem coeff_piEquiv_toAddEquiv
    (f : PolynomialModule (∀ i, R i) (∀ i, M i)) (i : ι) (n : ℕ) :
    ((((coeffAddEquiv (R := ∀ i, R i) (M := ∀ i, M i)).trans
      ((Finsupp.piLinearEquiv (κ := ℕ) R M).toAddEquiv.trans
        (AddEquiv.piCongrRight fun j =>
          (coeffAddEquiv (R := R j) (M := M j)).symm))).toFun f i).coeff n) =
      (f.coeff n) i := by
  change
    ((coeffAddEquiv (R := R i) (M := M i)).symm
      (Finsupp.piLinearEquiv (κ := ℕ) R M
        (coeffAddEquiv (R := ∀ i, R i) (M := ∀ i, M i) f) i)).coeff n = _
  rw [coeffAddEquiv_apply, coeffAddEquiv_symm_apply, coeff_ofCoeff,
    Finsupp.piLinearEquiv_apply]

/-- The polynomial module over a finite product of rings is the product of the
coordinate polynomial modules, semilinearly along `Polynomial.piRingEquiv R`.
Both polynomial actions are those induced by the given coordinate modules. -/
noncomputable def piEquiv :
    @LinearEquiv
      (Polynomial (∀ i, R i))
      (∀ i, Polynomial (R i))
      Polynomial.semiring
      Pi.semiring
      ((Polynomial.piRingEquiv R) :
        Polynomial (∀ i, R i) →+* (∀ i, Polynomial (R i)))
      (((Polynomial.piRingEquiv R).symm) :
        (∀ i, Polynomial (R i)) →+* Polynomial (∀ i, R i))
      (RingHomInvPair.of_ringEquiv (Polynomial.piRingEquiv R))
      (RingHomInvPair.of_ringEquiv_symm (Polynomial.piRingEquiv R))
      (PolynomialModule (∀ i, R i) (∀ i, M i))
      (∀ i, PolynomialModule (R i) (M i))
      (PolynomialModule.instAddCommGroup
        (R := ∀ i, R i) (M := ∀ i, M i)).toAddCommMonoid
      Pi.addCommMonoid
      PolynomialModule.polynomialModule
      Pi.module' := by
  letI := RingHomInvPair.of_ringEquiv (Polynomial.piRingEquiv R)
  letI := RingHomInvPair.of_ringEquiv_symm (Polynomial.piRingEquiv R)
  exact
    { toAddEquiv :=
        (PolynomialModule.coeffAddEquiv
          (R := ∀ i, R i) (M := ∀ i, M i)).trans
          ((Finsupp.piLinearEquiv (κ := ℕ) R M).toAddEquiv.trans
            (AddEquiv.piCongrRight fun i =>
              (PolynomialModule.coeffAddEquiv
                (R := R i) (M := M i)).symm))
      map_smul' := by
        intro p f
        funext i
        change _ = (Polynomial.piRingEquiv R p i) •
          (_ : PolynomialModule (R i) (M i))
        apply PolynomialModule.ext
        apply Finsupp.ext
        intro n
        simp only [coeff_piEquiv_toAddEquiv, smul_apply, Finset.sum_apply,
          Pi.smul_apply', Polynomial.coeff_piRingEquiv] }

/-- The comparison preserves the degree and takes the corresponding coordinate of
each coefficient. -/
@[simp] theorem coeff_piEquiv
    (f : PolynomialModule (∀ i, R i) (∀ i, M i)) (i : ι) (n : ℕ) :
    (piEquiv R M f i).coeff n = (f.coeff n) i := by
  exact coeff_piEquiv_toAddEquiv R M f i n

/-- The inverse comparison assembles the coefficients of the coordinate polynomial
modules. -/
@[simp] theorem coeff_piEquiv_symm
    (g : ∀ i, PolynomialModule (R i) (M i)) (n : ℕ) (i : ι) :
    ((piEquiv R M).symm g).coeff n i = (g i).coeff n := by
  simpa only [(piEquiv R M).apply_symm_apply] using
    (coeff_piEquiv R M ((piEquiv R M).symm g) i n).symm

/-- A single product coefficient maps to the coordinate singles at the same degree. -/
@[simp] theorem piEquiv_single (n : ℕ) (m : ∀ i, M i) :
    piEquiv R M (single (∀ i, R i) n m) = (fun i => single (R i) n (m i)) := by
  funext i
  apply PolynomialModule.ext
  apply Finsupp.ext
  intro k
  simp only [coeff_piEquiv, coeff_single, Finsupp.single_apply]
  split_ifs <;> rfl

/-- Coordinate singles at a common degree assemble into one product coefficient. -/
@[simp] theorem piEquiv_symm_single (n : ℕ) (m : ∀ i, M i) :
    (piEquiv R M).symm (fun i => single (R i) n (m i)) = single (∀ i, R i) n m := by
  apply (piEquiv R M).injective
  rw [(piEquiv R M).apply_symm_apply, piEquiv_single]

/-- A monomial acting on a single adds their degrees and acts on each coefficient by
the corresponding scalar. -/
theorem piEquiv_monomial_smul_single (a : ℕ) (r : ∀ i, R i) (b : ℕ)
    (m : ∀ i, M i) (i : ι) :
    piEquiv R M (Polynomial.monomial a r • single (∀ i, R i) b m) i =
      single (R i) (a + b) (r i • m i) := by
  simp only [monomial_smul_single, piEquiv_single, Pi.smul_apply']

end PolynomialModule

universe uι

namespace PolynomialModule.Extension

/-- Canonical polynomial-module extension commutes with finite products. -/
noncomputable def piEquiv
    {ι : Type uι} (R : ι → Type uR) (M : ι → Type uM)
    [finiteι : Finite ι]
    [semiringR : ∀ i, Semiring (R i)]
    [addCommMonoidM : ∀ i, AddCommMonoid (M i)]
    [moduleRM : ∀ i, Module (R i) (M i)] :
    letI coefficientProductModule :
        Module (∀ i, R i) (∀ i, M i) := Pi.module';
    letI sourcePolynomialModule :
        Module (Polynomial (∀ i, R i))
          (Extension (∀ i, R i) (∀ i, M i)) :=
      @polynomialModule (∀ i, R i) (∀ i, M i) _ _ coefficientProductModule;
    letI fiberPolynomialModule :
        ∀ i, Module (Polynomial (R i)) (Extension (R i) (M i)) :=
      fun i => polynomialModule (R := R i) (M := M i);
    letI targetPolynomialModule :
        Module (∀ i, Polynomial (R i))
          (∀ i, Extension (R i) (M i)) :=
      @Pi.module' _ _ _ _ _ fiberPolynomialModule;
    @LinearEquiv
      (Polynomial (∀ i, R i))
      (∀ i, Polynomial (R i))
      Polynomial.semiring
      Pi.semiring
      ((Polynomial.piRingEquiv R) :
        Polynomial (∀ i, R i) →+* (∀ i, Polynomial (R i)))
      (((Polynomial.piRingEquiv R).symm) :
        (∀ i, Polynomial (R i)) →+* Polynomial (∀ i, R i))
      (RingHomInvPair.of_ringEquiv (Polynomial.piRingEquiv R))
      (RingHomInvPair.of_ringEquiv_symm (Polynomial.piRingEquiv R))
      (Extension (∀ i, R i) (∀ i, M i))
      (∀ i, Extension (R i) (M i))
      ((coeffEquiv (∀ i, R i) (∀ i, M i)).addCommMonoid)
      Pi.addCommMonoid
      sourcePolynomialModule
      targetPolynomialModule := by
  letI coefficientProductModule :
      Module (∀ i, R i) (∀ i, M i) := Pi.module'
  letI sourcePolynomialModule :
      Module (Polynomial (∀ i, R i))
        (Extension (∀ i, R i) (∀ i, M i)) :=
    @polynomialModule (∀ i, R i) (∀ i, M i) _ _ coefficientProductModule
  letI fiberPolynomialModule :
      ∀ i, Module (Polynomial (R i)) (Extension (R i) (M i)) :=
    fun i => polynomialModule (R := R i) (M := M i)
  letI targetPolynomialModule :
      Module (∀ i, Polynomial (R i))
        (∀ i, Extension (R i) (M i)) :=
    @Pi.module' _ _ _ _ _ fiberPolynomialModule
  letI := RingHomInvPair.of_ringEquiv (Polynomial.piRingEquiv R)
  letI := RingHomInvPair.of_ringEquiv_symm (Polynomial.piRingEquiv R)
  let e : Extension (∀ i, R i) (∀ i, M i) ≃+
      (∀ i, Extension (R i) (M i)) :=
    (coeffAddEquiv (∀ i, R i) (∀ i, M i)).trans
      ((Finsupp.piLinearEquiv (κ := ℕ) R M).toAddEquiv.trans
        (AddEquiv.piCongrRight fun i =>
          (coeffAddEquiv (R i) (M i)).symm))
  have hcoordinate
      (q : Extension (∀ i, R i) (∀ i, M i)) (i : ι) :
      e q i = coordinate R M i q := by
    apply PolynomialModule.Extension.ext
    apply Finsupp.ext
    intro n
    change (Finsupp.piLinearEquiv (κ := ℕ) R M q.coeff i) n =
      (coordinate R M i q).coeff n
    rw [Finsupp.piLinearEquiv_apply, coeff_coordinate]
  exact
    (show
      @LinearEquiv
        (Polynomial (∀ i, R i))
        (∀ i, Polynomial (R i))
        Polynomial.semiring
        Pi.semiring
        ((Polynomial.piRingEquiv R) :
          Polynomial (∀ i, R i) →+* (∀ i, Polynomial (R i)))
        (((Polynomial.piRingEquiv R).symm) :
          (∀ i, Polynomial (R i)) →+* Polynomial (∀ i, R i))
        (RingHomInvPair.of_ringEquiv (Polynomial.piRingEquiv R))
        (RingHomInvPair.of_ringEquiv_symm (Polynomial.piRingEquiv R))
        (Extension (∀ i, R i) (∀ i, M i))
        (∀ i, Extension (R i) (M i))
        ((coeffEquiv (∀ i, R i) (∀ i, M i)).addCommMonoid)
        Pi.addCommMonoid
        sourcePolynomialModule
        targetPolynomialModule
      from
        { toAddEquiv := e
          map_smul' := by
            intro p q
            funext i
            change e (p • q) i =
              (Polynomial.piRingEquiv R p i) • e q i
            simpa only [hcoordinate, Polynomial.piRingEquiv_apply,
              Polynomial.coe_mapRingHom] using
              (coordinate_smul R M i p q) })


section Semiring

variable {ι : Type uι} (R : ι → Type uR) (M : ι → Type uM)
variable [Finite ι] [∀ i, Semiring (R i)]
variable [∀ i, AddCommMonoid (M i)] [∀ i, Module (R i) (M i)]

/-- The finite-product equivalence takes each coefficient to its corresponding coordinate. -/
@[simp] theorem coeff_piEquiv
    (q : Extension (∀ i, R i) (∀ i, M i)) (i : ι) (n : ℕ) :
    (piEquiv R M q i).coeff n = (q.coeff n) i := by
  change (Finsupp.piLinearEquiv (κ := ℕ) R M q.coeff i) n = _
  exact Finsupp.piLinearEquiv_apply R M q.coeff i n

/-- Each component of the finite-product equivalence is the coordinate projection. -/
theorem piEquiv_apply (q : Extension (∀ i, R i) (∀ i, M i)) (i : ι) :
    piEquiv R M q i = coordinate R M i q := by
  apply PolynomialModule.Extension.ext
  apply Finsupp.ext
  intro n
  simp only [coeff_piEquiv, coeff_coordinate]

/-- The inverse equivalence assembles the coefficients of the coordinate extensions. -/
@[simp] theorem coeff_piEquiv_symm
    (q : ∀ i, Extension (R i) (M i)) (n : ℕ) (i : ι) :
    ((piEquiv R M).symm q).coeff n i = (q i).coeff n := by
  simpa only [(piEquiv R M).apply_symm_apply] using
    (coeff_piEquiv R M ((piEquiv R M).symm q) i n).symm

/-- A single product coefficient maps to the coordinate singles at the same degree. -/
@[simp] theorem piEquiv_single (n : ℕ) (m : ∀ i, M i) :
    piEquiv R M (single (∀ i, R i) n m) = (fun i => single (R i) n (m i)) := by
  funext i
  rw [piEquiv_apply, coordinate_single]

/-- Coordinate singles at a common degree assemble into a single product coefficient. -/
@[simp] theorem piEquiv_symm_single (n : ℕ) (m : ∀ i, M i) :
    (piEquiv R M).symm (fun i => single (R i) n (m i)) = single (∀ i, R i) n m := by
  apply (piEquiv R M).injective
  rw [(piEquiv R M).apply_symm_apply, piEquiv_single]

end Semiring

section Naturality

universe uS uN

variable {I : Type uI} (R : I → Type uR) (S : I → Type uS)
variable (M : I → Type uM) (N : I → Type uN)
variable [Finite I]
variable [r : ∀ i, Semiring (R i)] [s : ∀ i, Semiring (S i)]
variable [aM : ∀ i, AddCommMonoid (M i)] [aN : ∀ i, AddCommMonoid (N i)]
variable [μM : ∀ i, @Module (R i) (M i) (r i) (aM i)]
variable [μN : ∀ i, @Module (S i) (N i) (s i) (aN i)]

/-- The finite-product equivalence commutes with extension of a family of
coefficient-semilinear maps. -/
@[simp] theorem piEquiv_map
    (σ : ∀ i, @RingHom (R i) (S i)
      ((r i).toNonAssocSemiring) ((s i).toNonAssocSemiring))
    (f : ∀ i, @LinearMap (R i) (S i) (r i) (s i) (σ i)
      (M i) (N i) (aM i) (aN i) (μM i) (μN i))
    (i : I) (q : Extension (∀ i, R i) (∀ i, M i)) :
    piEquiv S N
      (map
          ({ toFun := fun m i => f i (m i)
             map_add' := fun m m' =>
               funext (fun i => (f i).map_add (m i) (m' i))
             map_smul' := fun r₀ m =>
               funext (fun i => (f i).map_smulₛₗ (r₀ i) (m i)) } :
            @LinearMap (∀ i, R i) (∀ i, S i)
              (@Pi.semiring I R r) (@Pi.semiring I S s)
              (show @RingHom (∀ i, R i) (∀ i, S i)
                  (@Pi.nonAssocSemiring I R (fun i => (r i).toNonAssocSemiring))
                  (@Pi.nonAssocSemiring I S (fun i => (s i).toNonAssocSemiring)) from
                @RingHom.pi I S (∀ i, R i)
                  (fun i => (s i).toNonAssocSemiring)
                  (@Pi.nonAssocSemiring I R (fun i => (r i).toNonAssocSemiring))
                  (fun i => (σ i).comp
                    (@Pi.evalRingHom I R (fun j => (r j).toNonAssocSemiring) i)))
              (∀ i, M i) (∀ i, N i)
              (@Pi.addCommMonoid I M aM) (@Pi.addCommMonoid I N aN)
              (@Pi.module' I R M r aM μM) (@Pi.module' I S N s aN μN)) q) i =
      map (f i) (piEquiv R M q i) := by
  simpa only [piEquiv_apply] using (coordinate_map R S M N σ f i q)

end Naturality

section CommRing

variable {ι : Type uι} (R : ι → Type uR) (M : ι → Type uM)
variable [Finite ι] [∀ i, CommRing (R i)]
variable [∀ i, AddCommGroup (M i)] [∀ i, Module (R i) (M i)]

/-- The coefficient-preserving comparison with `PolynomialModule` commutes with
finite-product equivalences at commutative-ring and additive-group coefficients. -/
theorem polynomialLinearEquivPolynomialModule_piEquiv
    (q : Extension (∀ i, R i) (∀ i, M i)) (i : ι) :
    polynomialLinearEquivPolynomialModule (R := R i) (M := M i) (piEquiv R M q i) =
      PolynomialModule.piEquiv R M
        (polynomialLinearEquivPolynomialModule (R := ∀ i, R i) (M := ∀ i, M i) q) i := by
  apply PolynomialModule.ext
  apply Finsupp.ext
  intro n
  simp only [polynomialLinearEquivPolynomialModule_apply, coeff_toPolynomialModule,
    PolynomialModule.coeff_piEquiv, coeff_piEquiv]

end CommRing

end PolynomialModule.Extension

universe u v w v'

namespace PolynomialModule.Extension

section Homogeneous

variable {R : Type u} [Semiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]

private theorem coeff_eqMp {P : Type v'} [AddCommMonoid P] [Module R P]
    {σ τ : Polynomial R →+* Polynomial R} (h : σ = τ)
    (f : Extension R P →ₛₗ[σ] Extension R M) (q : Extension R P) (n : ℕ) :
    coeff ((Eq.mp (congrArg
      (fun ρ => Extension R P →ₛₗ[ρ] Extension R M) h) f) q) n = coeff (f q) n := by
  cases h
  rfl

private theorem coeff_map_cast {P : Type v'} [AddCommMonoid P] [Module R P]
    (g : P →ₗ[R] M) (q : Extension R P) (n : ℕ) :
    coeff ((Eq.mp (congrArg
      (fun ρ => Extension R P →ₛₗ[ρ] Extension R M)
      (Polynomial.mapRingHom_id (R := R))) (map g)) q) n = g (coeff q n) := by
  rw [coeff_eqMp (Polynomial.mapRingHom_id (R := R))]
  exact coeff_map g q n

variable (R M) (ι : Type w)

private noncomputable def piLinearMap : Extension R (ι → M) →ₗ[Polynomial R] (ι → Extension R M) :=
  LinearMap.pi fun i =>
    Eq.mp (congrArg
      (fun ρ => Extension R (ι → M) →ₛₗ[ρ] Extension R M)
      (Polynomial.mapRingHom_id (R := R)))
      (map (LinearMap.proj i : (ι → M) →ₗ[R] M))

private theorem coeff_piLinearMap (q : Extension R (ι → M)) (i : ι) (n : ℕ) :
    coeff (piLinearMap R M ι q i) n = coeff q n i :=
  coeff_map_cast (LinearMap.proj i) q n

variable [Finite ι]

private noncomputable def piLinearMapInv :
    (ι → Extension R M) →ₗ[Polynomial R] Extension R (ι → M) := by
  letI : DecidableEq ι := Classical.typeDecidableEq ι
  letI : Fintype ι := Fintype.ofFinite ι
  exact ∑ i : ι,
    (Eq.mp (congrArg
      (fun ρ => Extension R M →ₛₗ[ρ] Extension R (ι → M))
      (Polynomial.mapRingHom_id (R := R)))
      (map (LinearMap.single R (fun _ => M) i))).comp (LinearMap.proj i)

private theorem coeff_piLinearMapInv (p : ι → Extension R M) (n : ℕ) (i : ι) :
    coeff (piLinearMapInv R M ι p) n i = coeff (p i) n := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let ev : ((ι → Extension R M) →ₗ[Polynomial R] Extension R (ι → M)) →+ M :=
    { toFun := fun f => coeff (f p) n i
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  change ev (piLinearMapInv R M ι) = _
  simp only [piLinearMapInv, map_sum]
  change (∑ j : ι,
    coeff ((Eq.mp (congrArg
      (fun ρ => Extension R M →ₛₗ[ρ] Extension R (ι → M))
      (Polynomial.mapRingHom_id (R := R)))
      (map (LinearMap.single R (fun _ => M) j))) (p j)) n i) = coeff (p i) n
  trans ∑ j : ι, (LinearMap.single R (fun _ => M) j (coeff (p j) n)) i
  · apply Finset.sum_congr rfl
    intro j _
    exact congrFun (coeff_map_cast (LinearMap.single R (fun _ => M) j) (p j) n) i
  · simp [LinearMap.single_apply, Pi.single_apply]

/-- Polynomial extension commutes with functions on a finite index type, over the same
coefficient semiring and with the given coefficient module. -/
noncomputable def piLinearEquiv :
    Extension R (ι → M) ≃ₗ[Polynomial R] (ι → Extension R M) :=
  LinearEquiv.ofLinearMap
    (LinearMap.pi fun i =>
      Eq.mp (congrArg
        (fun ρ => Extension R (ι → M) →ₛₗ[ρ] Extension R M)
        (Polynomial.mapRingHom_id (R := R)))
        (map (LinearMap.proj i : (ι → M) →ₗ[R] M)))
    (by
      letI : DecidableEq ι := Classical.typeDecidableEq ι
      letI : Fintype ι := Fintype.ofFinite ι
      exact ∑ i : ι,
        (Eq.mp (congrArg
          (fun ρ => Extension R M →ₛₗ[ρ] Extension R (ι → M))
          (Polynomial.mapRingHom_id (R := R)))
          (map (LinearMap.single R (fun _ => M) i))).comp (LinearMap.proj i))
    (by
      apply LinearMap.ext
      intro p
      funext i
      apply Extension.ext
      apply Finsupp.ext
      intro n
      change coeff (piLinearMap R M ι (piLinearMapInv R M ι p) i) n = coeff (p i) n
      rw [coeff_piLinearMap, coeff_piLinearMapInv])
    (by
      apply LinearMap.ext
      intro q
      apply Extension.ext
      apply Finsupp.ext
      intro n
      funext i
      change coeff (piLinearMapInv R M ι (piLinearMap R M ι q)) n i = coeff q n i
      rw [coeff_piLinearMapInv, coeff_piLinearMap])

@[simp]
theorem piLinearEquiv_coeff (q : Extension R (ι → M)) (i : ι) (n : ℕ) :
    coeff (piLinearEquiv R M ι q i) n = coeff q n i :=
  coeff_piLinearMap R M ι q i n

/-- Each coordinate of the homogeneous comparison is the extension of evaluation. -/
theorem piLinearEquiv_apply (q : Extension R (ι → M)) (i : ι) :
    piLinearEquiv R M ι q i = map (LinearMap.proj i : (ι → M) →ₗ[R] M) q := by
  apply Extension.ext
  apply Finsupp.ext
  intro n
  rw [piLinearEquiv_coeff, coeff_map]
  rfl

@[simp]
theorem piLinearEquiv_apply_single (n : ℕ) (a : ι → M) (i : ι) :
    piLinearEquiv R M ι (single R n a) i = single R n (a i) := by
  apply Extension.ext
  apply Finsupp.ext
  intro k
  rw [piLinearEquiv_coeff]
  by_cases h : n = k <;> simp [h]

@[simp]
theorem piLinearEquiv_symm_coeff (p : ι → Extension R M) (n : ℕ) (i : ι) :
    coeff ((piLinearEquiv R M ι).symm p) n i = coeff (p i) n :=
  coeff_piLinearMapInv R M ι p n i

open Classical in
/-- The inverse homogeneous comparison sums the extensions of the coordinate inclusions. -/
theorem piLinearEquiv_symm_apply (p : ι → Extension R M) :
    (piLinearEquiv R M ι).symm p =
      ∑ i ∈ (@Finset.univ ι (Fintype.ofFinite ι)),
        map (LinearMap.single R (fun _ => M) i) (p i) := by
  let : Fintype ι := Fintype.ofFinite ι
  apply Extension.ext
  apply Finsupp.ext
  intro n
  funext i
  simp [coeff_sum, Finsupp.finsetSum_apply, Finset.sum_apply, coeff_map,
    LinearMap.single_apply, Pi.single_apply]

/-- The polynomial extension of a finite free regular module is a finite tuple of
polynomials, with pointwise left polynomial scalar multiplication. -/
noncomputable def piRegularEquiv : Extension R (ι → R) ≃ₗ[Polynomial R] (ι → Polynomial R) :=
  (piLinearEquiv R R ι).trans (LinearEquiv.piCongrRight fun _ => regularEquiv R)

/-- The regular finite-function comparison applies the regular comparison coordinatewise. -/
theorem piRegularEquiv_apply (q : Extension R (ι → R)) (i : ι) :
    piRegularEquiv R ι q i =
      regularEquiv R (map (LinearMap.proj i : (ι → R) →ₗ[R] R) q) := by
  change regularEquiv R (piLinearEquiv R R ι q i) = _
  rw [piLinearEquiv_apply]

@[simp]
theorem piRegularEquiv_coeff (q : Extension R (ι → R)) (i : ι) (n : ℕ) :
    (piRegularEquiv R ι q i).coeff n = coeff q n i := by
  change (regularEquiv R (piLinearEquiv R R ι q i)).coeff n = _
  rw [regularEquiv_coeff, piLinearEquiv_coeff]

@[simp]
theorem piRegularEquiv_apply_single (n : ℕ) (a : ι → R) (i : ι) :
    piRegularEquiv R ι (single R n a) i = Polynomial.monomial n (a i) := by
  change regularEquiv R (piLinearEquiv R R ι (single R n a) i) = _
  rw [piLinearEquiv_apply_single, regularEquiv_apply_single]

@[simp]
theorem piRegularEquiv_symm_coeff (p : ι → Polynomial R) (n : ℕ) (i : ι) :
    coeff ((piRegularEquiv R ι).symm p) n i = (p i).coeff n := by
  change coeff ((piLinearEquiv R R ι).symm
    (fun j => (regularEquiv R).symm (p j))) n i = _
  rw [piLinearEquiv_symm_coeff, regularEquiv_symm_coeff]

open Classical in
/-- The inverse regular finite-function comparison expands a tuple in the standard
coordinate generators. -/
theorem piRegularEquiv_symm_apply (p : ι → Polynomial R) :
    (piRegularEquiv R ι).symm p =
      ∑ i ∈ (@Finset.univ ι (Fintype.ofFinite ι)),
        p i • single R 0 (Pi.single i (1 : R)) := by
  let : Fintype ι := Fintype.ofFinite ι
  apply Extension.ext
  apply Finsupp.ext
  intro n
  funext i
  simp [coeff_sum, Finsupp.finsetSum_apply, Finset.sum_apply, smul_single_apply,
    Pi.single_apply, smul_eq_mul]

open Classical in
/-- Every element of the extension of a finite free module is the polynomial-linear
combination of its coordinate generators given by its polynomial coordinates. -/
theorem sum_piRegularEquiv_smul_single (q : Extension R (ι → R)) :
    (∑ i ∈ (@Finset.univ ι (Fintype.ofFinite ι)),
      piRegularEquiv R ι q i • single R 0 (Pi.single i (1 : R))) = q := by
  simpa only [piRegularEquiv_symm_apply] using
    (piRegularEquiv R ι).symm_apply_apply q

end Homogeneous

section CommRingRegular

variable {R : Type u} [CommRing R]

/-- Over a commutative ring, the regular comparison agrees with the polynomial-module
comparison followed by Mathlib's regular polynomial-module equivalence. -/
theorem regularEquiv_eq_equivPolynomialSelf (q : Extension R R) :
    regularEquiv R q =
      PolynomialModule.equivPolynomialSelf (polynomialLinearEquivPolynomialModule q) := by
  apply Polynomial.ext
  intro n
  rw [regularEquiv_coeff, polynomialLinearEquivPolynomialModule_apply]
  change coeff q n = (toPolynomialModule q).coeff n
  exact (congrArg (fun f : ℕ →₀ R => f n) (coeff_toPolynomialModule q)).symm

end CommRingRegular

end PolynomialModule.Extension
