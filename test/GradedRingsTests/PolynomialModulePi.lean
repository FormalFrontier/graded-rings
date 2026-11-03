/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import GradedRings.PolynomialModule.Pi

/-!
# A coordinatewise polynomial-module action

A degree-two monomial with different scalar coefficients in the two coordinates acts
on a degree-seven single. The comparison preserves the resulting degree nine and the
two different coefficient products.
-/

example :
    PolynomialModule.piEquiv (fun _ : Bool => ℤ) (fun _ : Bool => ℤ)
      (Polynomial.monomial 2 (fun i : Bool => if i then (3 : ℤ) else 2) •
        PolynomialModule.single (Bool → ℤ) 7
          (fun i : Bool => if i then (7 : ℤ) else 5)) =
      (fun i : Bool => PolynomialModule.single ℤ 9 (if i then (21 : ℤ) else 10)) := by
  funext i
  rw [PolynomialModule.piEquiv_monomial_smul_single]
  cases i <;> rfl
