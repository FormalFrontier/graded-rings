/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GradedRings.ReesModule.Regular

/-!
# The associated graded module of the regular module

For any ideal `I` of a commutative ring `R`, the existing associated graded module
`Ideal.AssociatedGradedModule I R` is free of rank one over the quotient Rees algebra
`reesAlgebra I ⧸ I.map (algebraMap R (reesAlgebra I))`. Its distinguished generator is
the class of the degree-zero polynomial-module unit.

`Ideal.AssociatedGradedModule.regularEquiv` sends a scalar to its multiple of this
generator. The representative and coefficient formulas describe this equivalence without
unfolding either the quotient or its scalar action. The generator also gives unique scalar
expressions and extensionality for linear maps out of the regular associated graded module.

The proof uses `Ideal.Filtration.regularReesEquiv` and transports the extended-ideal
multiple through that linear equivalence. No finiteness, completeness, separatedness,
or nontriviality assumption is needed.

## References

* `GradedRings.ReesModule.Regular` supplies the regular Rees equivalence.
* `GradedRings.ReesModule` supplies the Rees-module quotient, its coefficient maps, and
  the quotient-Rees scalar action used here.
-/

@[expose] public section

universe u v

namespace Ideal.AssociatedGradedModule

variable {R : Type u} [CommRing R] (I : Ideal R)

local notation "B" => reesAlgebra I
local notation "J" => I.map (algebraMap R B)
local notation "C" => B ⧸ J
local notation "N" => (Ideal.Filtration.submodule (I.stableFiltration (⊤ : Submodule R R)))
local notation "G" => Ideal.AssociatedGradedModule I R

private noncomputable def regularReesUnit : N :=
  ⟨PolynomialModule.single R 0 (1 : R),
    single_mem I R 0 (1 : R) (by simp)⟩

/-- The degree-zero unit class in the associated graded module of the regular module. -/
noncomputable def regularUnit : G :=
  mk I R
    ⟨PolynomialModule.single R 0 (1 : R),
      single_mem I R 0 (1 : R) (by simp)⟩

/-- The regular generator is the image of the unit class under the existing degree-zero map. -/
theorem regularUnit_eq_degreeZero :
    regularUnit I = degreeZero I R (Submodule.Quotient.mk (1 : R)) := by
  exact (degreeZero_mk I R (1 : R)).symm

private theorem regularUnit_bijective :
    Function.Bijective (LinearMap.toSpanSingleton C G (regularUnit I)) := by
  let e := Ideal.Filtration.regularReesEquiv I
  have hmk (b : B) :
      LinearMap.toSpanSingleton C G (regularUnit I) (Ideal.Quotient.mk J b) =
        mk I R (e b) := by
    calc
      _ = mk I R (b • regularReesUnit I) :=
        quotient_smul_mk I R b (regularReesUnit I)
      _ = mk I R (e b) :=
        congrArg (mk I R) (Ideal.Filtration.regularReesEquiv_apply I b).symm
  -- A linear equivalence carries the extended-ideal multiple onto the same multiple.
  have hmap : Submodule.map e.toLinearMap (J : Submodule B B) =
      J • (⊤ : Submodule B N) := by
    have hJ : J • (⊤ : Submodule B B) = J := by
      rw [Ideal.smul_eq_mul, Ideal.mul_top]
    have hrange : LinearMap.range e.toLinearMap = ⊤ :=
      LinearMap.range_eq_top.mpr e.surjective
    calc
      Submodule.map e.toLinearMap (J : Submodule B B) =
          Submodule.map e.toLinearMap (J • (⊤ : Submodule B B)) :=
        congrArg (fun S : Submodule B B => Submodule.map e.toLinearMap S) hJ.symm
      _ = J • (⊤ : Submodule B N) := by
        rw [Submodule.map_smul'', Submodule.map_top, hrange]
  constructor
  · intro c
    refine Quotient.inductionOn' c ?_
    intro b d
    refine Quotient.inductionOn' d ?_
    intro b' h
    apply Ideal.Quotient.eq.mpr
    have hh : mk I R (e b) = mk I R (e b') :=
      (hmk b).symm.trans (h.trans (hmk b'))
    have hmem : e b - e b' ∈ J • (⊤ : Submodule B N) :=
      (Submodule.Quotient.eq _).mp hh
    have hmem' : e (b - b') ∈ J • (⊤ : Submodule B N) := by
      simpa only [map_sub] using hmem
    rw [← hmap] at hmem'
    rcases Submodule.mem_map.mp hmem' with ⟨a, ha, hea⟩
    exact e.injective hea ▸ ha
  · intro g
    induction g using Submodule.Quotient.induction_on with
    | H p =>
      obtain ⟨b, rfl⟩ := e.surjective p
      exact ⟨Ideal.Quotient.mk J b, hmk b⟩

/-- The canonical regular associated graded equivalence, sending a scalar to its multiple
of the degree-zero unit class. -/
noncomputable def regularEquiv :
    (reesAlgebra I ⧸ I.map (algebraMap R (reesAlgebra I))) ≃ₗ[
      reesAlgebra I ⧸ I.map (algebraMap R (reesAlgebra I))]
      Ideal.AssociatedGradedModule I R :=
  LinearEquiv.ofBijective (LinearMap.toSpanSingleton C G (regularUnit I))
    (by exact regularUnit_bijective I)

/-- The regular equivalence is scalar multiplication on the distinguished generator. -/
@[simp]
theorem regularEquiv_apply (c : C) :
    regularEquiv I c = c • regularUnit I := rfl

/-- The inverse regular equivalence sends the distinguished generator to one. -/
@[simp]
theorem regularEquiv_symm_regularUnit :
    (regularEquiv I).symm (regularUnit I) = 1 := by
  apply (regularEquiv I).injective
  simp

/-- On a Rees representative, the regular equivalence acts on the degree-zero unit
representative before taking its class. -/
theorem regularEquiv_mk (b : B) :
    regularEquiv I (Ideal.Quotient.mk J b) =
      mk I R
        (b • (⟨PolynomialModule.single R 0 (1 : R),
          single_mem I R 0 (1 : R) (by simp)⟩ : N)) := by
  exact quotient_smul_mk I R b (regularReesUnit I)

/-- Every coefficient of the regular equivalence is the coefficient of the Rees
representative modulo the next ideal power. -/
@[simp↓]
theorem coefficient_regularEquiv_mk (n : ℕ) (b : B) :
    coefficient I R n (regularEquiv I (Ideal.Quotient.mk J b)) =
      (Submodule.Quotient.mk ((b : Polynomial R).coeff n) :
        R ⧸ (I ^ (n + 1) • (⊤ : Submodule R R))) := by
  rw [regularEquiv_mk]
  refine (coefficient_mk I R n (b • regularReesUnit I)).trans ?_
  change (Submodule.Quotient.mk
    (((b : Polynomial R) • PolynomialModule.single R 0 (1 : R)).coeff n) :
      R ⧸ (I ^ (n + 1) • (⊤ : Submodule R R))) = _
  simp

/-- Every regular associated graded element has a unique scalar expression in the
fixed degree-zero generator. -/
theorem existsUnique_smul_regularUnit (g : G) :
    ∃! c : C, c • regularUnit I = g := by
  obtain ⟨c, hc⟩ := (regularEquiv I).surjective g
  have hc' : c • regularUnit I = g := by
    simpa only [regularEquiv_apply] using hc
  refine ⟨c, hc', ?_⟩
  intro d hd
  apply (regularEquiv I).injective
  simpa only [regularEquiv_apply] using hd.trans hc'.symm

/-- Linear maps out of the regular associated graded module are determined by their
value at the degree-zero generator. -/
@[ext]
theorem linearMap_ext_regularUnit
    {P : Type v} [AddCommMonoid P] [Module C P]
    {f g : G →ₗ[C] P}
    (h : f (regularUnit I) = g (regularUnit I)) : f = g := by
  have heq : f.comp (regularEquiv I).toLinearMap = g.comp (regularEquiv I).toLinearMap := by
    apply LinearMap.ext_ring
    change f (regularEquiv I 1) = g (regularEquiv I 1)
    simpa only [regularEquiv_apply, one_smul] using h
  apply LinearMap.ext
  intro x
  obtain ⟨c, rfl⟩ := (regularEquiv I).surjective x
  exact DFunLike.congr_fun heq c

end Ideal.AssociatedGradedModule
