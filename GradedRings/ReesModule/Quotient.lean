/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GradedRings.Filtration.Map
public import GradedRings.ReesModule.Exactness

/-!
# The Rees-module sequence of a submodule and quotient

For an ideal filtration `H` on `M` and a submodule `N`, the inverse-image filtration
along `N.subtype` is the induced filtration on `N`, while the image filtration along
`N.mkQ` is the quotient filtration on `M ⧸ N`.

The two linear maps induce Rees-module maps over `reesAlgebra I`. Their coefficient
formulas use the original `R`-linear inclusion and quotient map, and they form a short
exact sequence without any normalization of `H.N 0`.

## Implementation notes

Both maps are instances of `Ideal.Filtration.reesMap`, with the existing Rees-module
carriers and actions. The injectivity, exactness, and surjectivity statements specialize
the corresponding stagewise Rees-map criteria.
-/

@[expose] public section

universe u v

namespace Ideal.Filtration

variable {R : Type u} [CommRing R] {I : Ideal R}
variable {M : Type v} [AddCommGroup M] [Module R M]
variable (H : I.Filtration M) (N : Submodule R M)

/-- The Rees-module map induced by the inclusion of a submodule with its induced
filtration into the original filtered module. -/
noncomputable def reesSubtype :
    (H.comap N.subtype).submodule →ₗ[↥(reesAlgebra I)] H.submodule :=
  (H.comap N.subtype).reesMap H N.subtype (by
    intro n x hx
    exact (H.mem_comap_N N.subtype n x).mp hx)

/-- The Rees-module map induced by the quotient map, where the quotient carries the
image filtration. -/
noncomputable def reesMkQ :
    H.submodule →ₗ[↥(reesAlgebra I)] (H.map N.mkQ).submodule :=
  H.reesMap (H.map N.mkQ) N.mkQ (by
    intro n x hx
    exact (H.mem_map_N N.mkQ n (N.mkQ x)).mpr ⟨x, hx, rfl⟩)

/-- The underlying polynomial-module map of the induced inclusion is obtained by
applying the original `R`-linear inclusion to coefficients. -/
theorem coe_reesSubtype (p : (H.comap N.subtype).submodule) :
    (H.reesSubtype N p : PolynomialModule R M) =
      PolynomialModule.map R N.subtype (p : PolynomialModule R N) := by
  simp only [reesSubtype, coe_reesMap]

/-- Each coefficient of the induced Rees inclusion is the inclusion of the corresponding
coefficient over the original ring `R`. -/
@[simp]
theorem coeff_reesSubtype (n : ℕ) (p : (H.comap N.subtype).submodule) :
    (H.reesSubtype N p : PolynomialModule R M).coeff n =
      ((p : PolynomialModule R N).coeff n : M) := by
  simp only [reesSubtype, coeff_reesMap, Submodule.subtype_apply]

/-- The underlying polynomial-module map of the induced quotient map is obtained by
applying the original `R`-linear quotient map to coefficients. -/
theorem coe_reesMkQ (p : H.submodule) :
    (H.reesMkQ N p : PolynomialModule R (M ⧸ N)) =
      PolynomialModule.map R N.mkQ (p : PolynomialModule R M) := by
  simp only [reesMkQ, coe_reesMap]

/-- Each coefficient of the induced Rees quotient map is the quotient class of the
corresponding coefficient over the original ring `R`. -/
theorem coeff_reesMkQ (n : ℕ) (p : H.submodule) :
    (H.reesMkQ N p : PolynomialModule R (M ⧸ N)).coeff n =
      N.mkQ ((p : PolynomialModule R M).coeff n) := by
  simp only [reesMkQ, coeff_reesMap]

/-- Each coefficient of the induced Rees quotient map is the class of the source
coefficient. -/
@[simp]
theorem coeff_reesMkQ_mk (n : ℕ) (p : H.submodule) :
    (H.reesMkQ N p : PolynomialModule R (M ⧸ N)).coeff n =
      Submodule.Quotient.mk ((p : PolynomialModule R M).coeff n) := by
  simpa only [Submodule.mkQ_apply] using H.coeff_reesMkQ N n p

/-- The Rees-module map of the induced inclusion is injective. -/
theorem reesSubtype_injective : Function.Injective (H.reesSubtype N) := by
  unfold reesSubtype
  rw [reesMap_injective_iff]
  intro x y hxy
  exact Subtype.ext (Subtype.ext hxy)

/-- The induced inclusion and quotient Rees maps are exact at the original Rees module. -/
theorem reesSubtype_mkQ_exact :
    Function.Exact (H.reesSubtype N) (H.reesMkQ N) := by
  unfold reesSubtype reesMkQ
  rw [reesMap_exact_iff]
  intro n
  rw [comap_N, Submodule.map_comap_subtype, Submodule.ker_mkQ, inf_comm]

/-- The Rees-module map to the quotient with its image filtration is surjective. -/
theorem reesMkQ_surjective : Function.Surjective (H.reesMkQ N) := by
  unfold reesMkQ
  rw [reesMap_surjective_iff]
  intro n
  exact (H.map_N N.mkQ n).symm

end Ideal.Filtration
