/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Filtration

/-!
# Images and inverse images of ideal filtrations

An `I`-filtration can be transported along an `R`-linear map by taking the image or
inverse image of each stage. These constructions use the existing `Ideal.Filtration`
record and do not require its degree-zero stage to be the whole module.

The stage and membership formulas describe both constructions, and the identity and
composition formulas express their functoriality.
-/

@[expose] public section

universe u v w x

namespace Ideal.Filtration

variable {R : Type u} [CommRing R] {I : Ideal R}
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]
variable {P : Type x} [AddCommGroup P] [Module R P]

/-- The image filtration of `F` along an `R`-linear map, with each stage given by
its submodule image. -/
def map (F : I.Filtration M) (f : M →ₗ[R] N) : I.Filtration N where
  N n := (F.N n).map f
  mono := by
    intro n
    exact Submodule.map_mono (F.mono n)
  smul_le := by
    intro n
    rw [← Submodule.map_smul'']
    exact Submodule.map_mono (F.smul_le n)

/-- The inverse-image filtration of `G` along an `R`-linear map, with each stage given
by its submodule inverse image. -/
def comap (G : I.Filtration N) (f : M →ₗ[R] N) : I.Filtration M where
  N n := (G.N n).comap f
  mono := by
    intro n
    exact Submodule.comap_mono (G.mono n)
  smul_le := by
    intro n
    exact (Submodule.smul_comap_le_comap_smul f (G.N n) I).trans
      (Submodule.comap_mono (G.smul_le n))

/-- Each stage of an image filtration is the image of the corresponding stage. -/
@[simp]
theorem map_N (F : I.Filtration M) (f : M →ₗ[R] N) (n : ℕ) :
    (F.map f).N n = (F.N n).map f := by
  rfl

/-- Each stage of an inverse-image filtration is the inverse image of the corresponding
stage. -/
@[simp]
theorem comap_N (G : I.Filtration N) (f : M →ₗ[R] N) (n : ℕ) :
    (G.comap f).N n = (G.N n).comap f := by
  rfl

/-- Membership in an image stage means having a preimage in the source stage. -/
theorem mem_map_N (F : I.Filtration M) (f : M →ₗ[R] N) (n : ℕ) (y : N) :
    y ∈ (F.map f).N n ↔ ∃ x : M, x ∈ F.N n ∧ f x = y := by
  exact Submodule.mem_map

/-- Membership in an inverse-image stage is tested by applying the linear map. -/
theorem mem_comap_N (G : I.Filtration N) (f : M →ₗ[R] N) (n : ℕ) (x : M) :
    x ∈ (G.comap f).N n ↔ f x ∈ G.N n := by
  exact Submodule.mem_comap

/-- Taking the image along the identity leaves a filtration unchanged. -/
@[simp]
theorem map_id (F : I.Filtration M) :
    F.map (LinearMap.id : M →ₗ[R] M) = F := by
  apply Ideal.Filtration.ext
  funext n
  simp only [map_N, Submodule.map_id]

/-- Taking images respects composition of linear maps. -/
theorem map_comp (F : I.Filtration M) (f : M →ₗ[R] N) (g : N →ₗ[R] P) :
    (F.map f).map g = F.map (g.comp f) := by
  apply Ideal.Filtration.ext
  funext n
  simp only [map_N, Submodule.map_comp]

/-- Taking the inverse image along the identity leaves a filtration unchanged. -/
@[simp]
theorem comap_id (F : I.Filtration M) :
    F.comap (LinearMap.id : M →ₗ[R] M) = F := by
  apply Ideal.Filtration.ext
  funext n
  simp only [comap_N, Submodule.comap_id]

/-- Taking inverse images reverses the order of composition of linear maps. -/
theorem comap_comp (H : I.Filtration P) (f : M →ₗ[R] N) (g : N →ₗ[R] P) :
    (H.comap g).comap f = H.comap (g.comp f) := by
  apply Ideal.Filtration.ext
  funext n
  simp only [comap_N, Submodule.comap_comp]

end Ideal.Filtration
