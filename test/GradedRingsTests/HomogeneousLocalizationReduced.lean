/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GradedRings.HomogeneousLocalizationReduced
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Reduced homogeneous polynomial charts

For the total-degree grading on a polynomial ring in two variables over a field,
a nilpotent element of the chart at the first variable is zero. Inverting zero
instead gives the zero ring.
-/

@[expose] public section

namespace GradedRingsTests.HomogeneousLocalizationReduced

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

private theorem polynomialChart_nilpotent_eq_zero (K : Type u) [Field K]
    (z : HomogeneousLocalization.Away
      (MvPolynomial.homogeneousSubmodule (Fin 2) K) (MvPolynomial.X (0 : Fin 2)))
    (hz : IsNilpotent z) : z = 0 := by
  letI : IsReduced (HomogeneousLocalization.Away
      (MvPolynomial.homogeneousSubmodule (Fin 2) K) (MvPolynomial.X (0 : Fin 2))) :=
    HomogeneousLocalization.isReduced (MvPolynomial.homogeneousSubmodule (Fin 2) K)
      (Submonoid.powers (MvPolynomial.X (0 : Fin 2)))
  exact hz.eq_zero

private theorem zeroDenominator_zero_eq_one (K : Type u) [Field K] :
    (0 : HomogeneousLocalization.Away
      (MvPolynomial.homogeneousSubmodule (Fin 2) K) 0) = 1 := by
  letI := HomogeneousLocalization.subsingleton
    (MvPolynomial.homogeneousSubmodule (Fin 2) K)
    (x := Submonoid.powers (0 : MvPolynomial (Fin 2) K)) ⟨1, by simp⟩
  exact Subsingleton.elim _ _

end GradedRingsTests.HomogeneousLocalizationReduced
