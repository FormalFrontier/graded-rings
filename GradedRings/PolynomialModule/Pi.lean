/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Polynomial.Module.Basic
public import CoherentModules.LinearAlgebra.FinsuppPi
public import GradedRings.Polynomial.Pi

/-!
# Polynomial modules over finite products

For a finite family of rings `R` and modules `M`, `PolynomialModule.piEquiv R M`
identifies the polynomial module of the product with the product of the polynomial
modules. It is semilinear along `Polynomial.piRingEquiv R`: a polynomial with product
coefficients acts in each coordinate by its corresponding polynomial.

The coefficient formulas characterize both directions. The single-coefficient formulas
and the monomial action formula let users work with supported elements directly.

## Implementation notes

The additive equivalence composes Mathlib's `PolynomialModule.coeffAddEquiv` with
CoherentModules' `Finsupp.piLinearEquiv` and the coordinate coefficient equivalences.
Polynomial semilinearity follows from Mathlib's convolution formula for the polynomial
module action and the coefficient formula for `Polynomial.piRingEquiv`.
Finiteness is needed only for the coordinate index; the index, ring and module universes
are independent. No nonemptiness hypothesis is imposed.
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
