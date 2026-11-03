/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Algebra.Ring.Equiv

/-!
# Polynomials over finite products of semirings

For a finite family of semirings `R`, `Polynomial.piRingEquiv R` identifies polynomials
with coefficients in `∀ i, R i` with families of polynomials over the `R i`.
Its forward map applies the corresponding coefficient projection in each coordinate.
The coefficient formulas characterize both directions, and the constants, indeterminate,
and inverse monomial formulas give convenient ways to use the comparison.

## Implementation notes

The comparison packages the product of the polynomial maps induced by `Pi.evalRingHom`.
Its inverse is the inverse of this bijective ring homomorphism. Finiteness of the index
permits a common finite support for a family of polynomials; no nonemptiness hypothesis
is imposed. The index and coefficient universes are independent, and the coefficient
semirings need not be commutative.
-/

@[expose] public section

universe u v

namespace Polynomial

variable {ι : Type v}

/-- Polynomials over a finite product of semirings are the product of the polynomial
semirings, by mapping coefficients to each coordinate. -/
noncomputable def piRingEquiv (R : ι → Type u) [∀ i, Semiring (R i)] [Finite ι] :
    (∀ i, R i)[X] ≃+* ∀ i, (R i)[X] :=
  RingEquiv.ofBijective
    (RingHom.pi fun i => Polynomial.mapRingHom (Pi.evalRingHom R i))
    (by
      classical
      constructor
      · intro p q h
        apply Polynomial.ext
        intro n
        funext i
        have hi := congrArg (fun f : ∀ i, (R i)[X] => (f i).coeff n) h
        change (p.map (Pi.evalRingHom R i)).coeff n =
          (q.map (Pi.evalRingHom R i)).coeff n at hi
        simpa only [coeff_map, Pi.evalRingHom_apply] using hi
      · intro p
        let _ := Fintype.ofFinite ι
        -- All components have their support in this common finite set.
        let s : Finset ℕ := Finset.univ.biUnion fun i => (p i).support
        -- Compute the coefficient vector before taking any component.
        have hcoeff (n : ℕ) :
            (∑ m ∈ s, monomial m (fun j => (p j).coeff m)).coeff n =
              if n ∈ s then (fun j => (p j).coeff n) else 0 := by
          rw [Polynomial.finsetSum_coeff]
          simp [Polynomial.coeff_monomial]
        refine ⟨∑ n ∈ s, monomial n (fun i => (p i).coeff n), ?_⟩
        funext i
        apply Polynomial.ext
        intro n
        change
          ((∑ m ∈ s, monomial m (fun j => (p j).coeff m)).map
            (Pi.evalRingHom R i)).coeff n = (p i).coeff n
        rw [coeff_map]
        change
          ((∑ m ∈ s, monomial m (fun j => (p j).coeff m)).coeff n) i =
            (p i).coeff n
        rw [hcoeff]
        by_cases hn : n ∈ s
        · rw [ite_eq_left hn]
        · rw [ite_eq_right hn]
          have hni : n ∉ (p i).support := by
            intro hni
            apply hn
            exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hni⟩
          change (0 : R i) = (p i).coeff n
          exact (Polynomial.notMem_support_iff.mp hni).symm)

variable (R : ι → Type u) [∀ i, Semiring (R i)] [Finite ι]

/-- Each component of the finite-product comparison is the polynomial map induced by
coefficient evaluation at that component. -/
@[simp] theorem piRingEquiv_apply (p : (∀ i, R i)[X]) (i : ι) :
    piRingEquiv R p i = Polynomial.map (Pi.evalRingHom R i) p := by
  -- Forward polynomial map characteristic.
  unfold piRingEquiv
  rw [RingEquiv.ofBijective_apply]
  simp only [RingHom.pi_apply, Polynomial.coe_mapRingHom]

/-- The comparison sends each coefficient to its corresponding coordinate. -/
theorem coeff_piRingEquiv (p : (∀ i, R i)[X]) (i : ι) (n : ℕ) :
    (piRingEquiv R p i).coeff n = (p.coeff n) i := by
  -- Forward coefficient characteristic.
  rw [piRingEquiv_apply, Polynomial.coeff_map]
  simp only [Pi.evalRingHom_apply]

/-- The inverse comparison assembles the coefficients of a family of polynomials. -/
@[simp] theorem coeff_piRingEquiv_symm (p : ∀ i, (R i)[X]) (n : ℕ) (i : ι) :
    ((piRingEquiv R).symm p).coeff n i = (p i).coeff n := by
  -- Inverse coefficient characteristic.
  simpa only [(piRingEquiv R).apply_symm_apply] using
    (coeff_piRingEquiv R ((piRingEquiv R).symm p) i n).symm

/-- The comparison sends a constant polynomial to the corresponding family of constants. -/
@[simp] theorem piRingEquiv_C (a : ∀ i, R i) :
    piRingEquiv R (C a) = (fun i => C (a i)) := by
  -- Constant polynomial characteristic.
  funext i
  simp only [piRingEquiv_apply, Polynomial.map_C, Pi.evalRingHom_apply]

/-- The comparison sends the indeterminate to the indeterminate in every coordinate. -/
@[simp] theorem piRingEquiv_X :
    piRingEquiv R (X : (∀ i, R i)[X]) = (fun i => (X : (R i)[X])) := by
  -- Indeterminate characteristic.
  funext i
  simp only [piRingEquiv_apply, Polynomial.map_X]

/-- The inverse comparison assembles a family of monomials of the same degree. -/
@[simp] theorem piRingEquiv_symm_monomial (n : ℕ) (a : ∀ i, R i) :
    (piRingEquiv R).symm (fun i => monomial n (a i)) = monomial n a := by
  -- Inverse monomial characteristic.
  apply Polynomial.ext
  intro m
  funext i
  rw [coeff_piRingEquiv_symm]
  simp only [Polynomial.coeff_monomial]
  split_ifs <;> rfl

end Polynomial
