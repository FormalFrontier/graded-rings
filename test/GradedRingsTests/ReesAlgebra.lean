/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import GradedRings

/-!
# Finitely generated ideals and the Rees quotient

Finite generation of an ideal implies finite generation of its conormal module.
The finite-conormal criterion therefore applies over arbitrary commutative rings,
without a Noetherian hypothesis on the ambient ring.
-/

universe u

variable {R : Type u} [CommRing R]

example (I : Ideal R) (hI : I.FG) :
    Algebra.FiniteType (R ⧸ I)
      ((reesAlgebra I) ⧸ I.map (algebraMap R (reesAlgebra I))) := by
  let : Module.Finite R I := Module.Finite.of_fg hI
  let : Module.Finite R I.Cotangent :=
    Module.Finite.of_surjective I.toCotangent I.toCotangent_surjective
  let : Module.Finite (R ⧸ I) I.Cotangent :=
    Module.Finite.of_restrictScalars_finite R (R ⧸ I) I.Cotangent
  exact reesAlgebra.finiteType_quotient_of_finite_cotangent I
