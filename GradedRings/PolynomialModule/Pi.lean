/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Polynomial.Module.Basic
public import CoherentModules.LinearAlgebra.FinsuppPi
public import GradedRings.Polynomial.Pi
public import GradedRings.PolynomialModule.UniversalProperty
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

## Implementation notes

The additive equivalence composes Mathlib's `PolynomialModule.coeffAddEquiv` with
CoherentModules' `Finsupp.piLinearEquiv` and the coordinate coefficient equivalences.
Polynomial semilinearity follows from Mathlib's convolution formula for the polynomial
module action and the coefficient formula for `Polynomial.piRingEquiv`.
Finiteness is needed only for the coordinate index; the index, ring and module universes
are independent. No nonemptiness hypothesis is imposed.
For canonical extensions, the additive construction uses the same finite-product
coefficient equivalence, while polynomial semilinearity follows from
`PolynomialModule.Extension.coordinate_smul`.
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
