/-
Copyright (c) 2026 Formal Frontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier
-/
module

import GradedRings.ReesModule.PrincipalPolynomialNaturality
import Mathlib.RingTheory.Noetherian.Defs

noncomputable section

universe u v

namespace Ideal.AssociatedGradedModule

example {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] :
    R → Prop :=
  fun (a : R) =>
    let I : Ideal R := Ideal.span (Singleton.singleton a : Set R)
    let C := (reesAlgebra I) ⧸ Ideal.map (algebraMap R (reesAlgebra I)) I
    let G := Ideal.AssociatedGradedModule I M
    let Q := M ⧸ (I • (⊤ : Submodule R M))
    @IsNoetherian C G
        (inferInstance : Semiring C)
        (inferInstance : AddCommMonoid G)
        (inferInstance : Module C G)
      ↔
    @IsNoetherian R Q
        (inferInstance : Semiring R)
        (inferInstance : AddCommMonoid Q)
        (inferInstance : Module R Q)

end Ideal.AssociatedGradedModule

end
