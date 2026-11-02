/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GradedRings.FilteredAssociatedGraded.Adic
public import GradedRings.FilteredAssociatedGraded.Map

/-!
# Maps on ideal-adic integer associated graded modules

Every original-ring linear map preserves the integer ideal-adic stages
`I ^ n.toNat • ⊤`. Specializing the existing filtered associated graded map
therefore gives a canonical map, linear over the quotient Rees algebra for the
existing actions. Its value on each homogeneous representative applies the
original map without changing the degree. Components, identities and composition
are inherited from the generic map.

The original module structures and all integer degrees are retained. No
finiteness, completeness, separatedness or nontriviality assumption is needed.

## References

* Mathlib's `Submodule.smul_top_le_comap_smul_top` supplies stage preservation.
* `GradedRings.FilteredAssociatedGraded.Map` supplies the induced map and its
  representative, component and functor laws.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v w x

namespace Ideal

variable {R : Type u} [CommRing R] (I : Ideal R)
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

local notation "B" => reesAlgebra I
local notation "J" => I.map (algebraMap R B)
local notation "C" => B ⧸ J
local notation "Fₘ" => I.adicIntFiltration M
local notation "Fₙ" => I.adicIntFiltration N
local notation "Gₘ" => Ideal.IntFiltration.AssociatedGraded (I.adicIntFiltration M)
local notation "Gₙ" => Ideal.IntFiltration.AssociatedGraded (I.adicIntFiltration N)

/-- The ideal-adic associated graded map of an original-ring linear map. -/
noncomputable def adicAssociatedGradedHom (f : M →ₗ[R] N) : Gₘ →ₗ[C] Gₙ :=
  (Fₘ).map Fₙ f
    (fun n => Submodule.smul_top_le_comap_smul_top (I ^ n.toNat) f)

/-- An adic homogeneous representative is carried to its image in the same degree. -/
@[simp]
theorem adicAssociatedGradedHom_single (f : M →ₗ[R] N) (n : ℤ)
    (m : ↥(I ^ n.toNat • (⊤ : Submodule R M))) :
    adicAssociatedGradedHom I f
        (@DFunLike.coe (↥(I ^ n.toNat • (⊤ : Submodule R M)) →ₗ[R] Gₘ)
          _ _ _ ((Fₘ).single n) m) =
      (Fₙ).single n
        ⟨f (m : M),
          Submodule.smul_top_le_comap_smul_top (I ^ n.toNat) f m.property⟩ := by
  exact (Fₘ).map_single Fₙ f
    (fun k => Submodule.smul_top_le_comap_smul_top (I ^ k.toNat) f) n m

/-- Every component is the canonical quotient piece map of the corresponding component. -/
theorem component_adicAssociatedGradedHom (f : M →ₗ[R] N) (n : ℤ) (z : Gₘ) :
    (Fₙ).component n (adicAssociatedGradedHom I f z) =
      (Fₘ).pieceMap Fₙ f
        (fun k => Submodule.smul_top_le_comap_smul_top (I ^ k.toNat) f)
        n ((Fₘ).component n z) := by
  exact (Fₘ).component_map Fₙ f
    (fun k => Submodule.smul_top_le_comap_smul_top (I ^ k.toNat) f) n z

/-- The identity original map induces the identity adic associated graded map. -/
@[simp]
theorem adicAssociatedGradedHom_id :
    adicAssociatedGradedHom I (LinearMap.id : M →ₗ[R] M) =
      (LinearMap.id : Gₘ →ₗ[C] Gₘ) := by
  exact (Fₘ).map_id

variable {P : Type x} [AddCommGroup P] [Module R P]

/-- Ideal-adic associated graded maps preserve composition. -/
theorem adicAssociatedGradedHom_comp (f : M →ₗ[R] N) (g : N →ₗ[R] P) :
    adicAssociatedGradedHom I (g.comp f) =
      (adicAssociatedGradedHom I g).comp (adicAssociatedGradedHom I f) := by
  exact (Fₘ).map_comp Fₙ f
    (fun k => Submodule.smul_top_le_comap_smul_top (I ^ k.toNat) f)
    (I.adicIntFiltration P) g
    (fun k => Submodule.smul_top_le_comap_smul_top (I ^ k.toNat) g)

end Ideal
