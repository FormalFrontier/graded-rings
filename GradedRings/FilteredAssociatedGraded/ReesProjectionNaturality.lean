/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GradedRings.FilteredAssociatedGraded.Map
public import GradedRings.FilteredAssociatedGraded.ReesProjection
public import GradedRings.ReesModule.Map

/-!
# Naturality of shifted Rees projections

A linear map preserving every integer filtration stage induces a coefficientwise
linear map between the polynomial Rees submodules of the natural tails at any
common integer cutoff. This is the natural-tail specialization of
`Ideal.Filtration.reesMap`. The shifted Rees projections commute with this map and
the induced map on the full integer associated graded modules, as semilinear
maps along the canonical quotient of the Rees algebra.

## References

* `GradedRings.ReesModule.Map` supplies the coefficientwise Rees-submodule map
  and its polynomial, coefficient, singleton, identity, and composition formulas.
* `GradedRings.FilteredAssociatedGraded.ReesProjection` supplies the shifted
  projections and their admissible-single formulas.
-/

@[expose] public section

universe uR uM uN

namespace Ideal.IntFiltration

variable {R : Type uR} [CommRing R] {I : Ideal R}
variable {M : Type uM} [AddCommGroup M] [Module R M]
variable {N : Type uN} [AddCommGroup N] [Module R N]
variable (F : I.IntFiltration M) (H : I.IntFiltration N)
variable (f : M →ₗ[R] N) (hf : ∀ n, F.N n ≤ (H.N n).comap f)

local notation "B" => reesAlgebra I
local notation "J" => I.map (algebraMap R B)
local notation "C" => B ⧸ J

/-- The shifted Rees projections form a natural square, semilinear along the
same canonical quotient of the Rees algebra. -/
theorem shiftedReesProjection_naturality (k : ℤ) :
    ((H.shiftedReesProjection k).comp
        ((F.natTail k).reesMap (H.natTail k) f (by
          intro q
          simpa only [natTail_N] using hf (k + (q : ℤ)))) :
        (F.natTail k).submodule →ₛₗ[Ideal.Quotient.mk J] H.AssociatedGraded) =
      (F.map H f hf : F.AssociatedGraded →ₗ[C] H.AssociatedGraded).comp
        (F.shiftedReesProjection k) := by
  have hfTail : ∀ q, (F.natTail k).N q ≤ ((H.natTail k).N q).comap f := by
    intro q
    simpa only [natTail_N] using hf (k + (q : ℤ))
  have hcomp :
      ((H.shiftedReesProjection k).comp
        ((F.natTail k).reesMap (H.natTail k) f hfTail)).toAddMonoidHom =
      ((F.map H f hf).comp (F.shiftedReesProjection k)).toAddMonoidHom := by
    apply F.natTail_addHom_ext k
    intro q m
    change H.shiftedReesProjection k
        ((F.natTail k).reesMap (H.natTail k) f hfTail (F.natTailSingle k q m)) =
      F.map H f hf (F.shiftedReesProjection k (F.natTailSingle k q m))
    have hsingle :
        (F.natTail k).reesMap (H.natTail k) f hfTail (F.natTailSingle k q m) =
          H.natTailSingle k q ⟨f (m : M), hf (k + (q : ℤ)) m.property⟩ := by
      exact (F.natTail k).reesMap_single (H.natTail k) f hfTail q
        ⟨(m : M), by simpa only [natTail_N] using m.property⟩
    rw [hsingle, H.shiftedReesProjection_single, F.shiftedReesProjection_single,
      F.map_single]
  apply LinearMap.ext
  intro p
  exact DFunLike.congr_fun hcomp p

end Ideal.IntFiltration
