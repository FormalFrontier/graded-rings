/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.ReesAlgebra

/-!
# Finite type of quotients of Rees algebras

Every quotient of the Rees algebra of a finitely generated ideal is a finite-type
algebra over the base ring.
-/

@[expose] public section

universe u

variable {R : Type u} [CommRing R] {I : Ideal R}

namespace reesAlgebra

/-- Every quotient of the Rees algebra of a finitely generated ideal is a finite-type algebra
over the base ring. -/
theorem finiteType_quotient_of_fg (hI : I.FG) (J : Ideal (reesAlgebra I)) :
    Algebra.FiniteType R ((reesAlgebra I) ⧸ J) := by
  let : Algebra.FiniteType R (reesAlgebra I) :=
    (Subalgebra.fg_iff_finiteType (reesAlgebra I)).mp (reesAlgebra.fg hI)
  infer_instance

end reesAlgebra
