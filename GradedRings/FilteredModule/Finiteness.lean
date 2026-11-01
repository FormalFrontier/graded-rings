/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GradedRings.FilteredModule.WeightedSpan
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.RingTheory.Finiteness.Ideal

/-!
# Finiteness consequences of weighted filtered generation

For a separated, compatible integer-indexed filtration over an ideal-adically
precomplete coefficient ring, finite weighted generation of the successive
quotients gives eventual stability. Exhaustivity additionally gives finiteness
of the ambient module. Finite generation of the ideal instead gives finite
generation of every filtration stage.

These are consequences of
`Submodule.eq_iSup_pow_smul_span_singleton_of_isPrecomplete`, over the original
coefficient ring and module action. The finite family may be empty, its weights
may be negative, and the ring, module and family have independent universes.

## Implementation notes

Neither stability nor ambient finiteness requires the ideal to be finitely
generated. Stage finiteness does not require exhaustivity. No new filtration
structure or associated-graded construction is introduced here.

## References

Fujiwara--Kato, *Foundations of Rigid Geometry I*, arXiv:1308.4734v5,
Proposition 0.7.5.2, provides the context for the filtered lifting argument.
The precomplete-coefficient, all-integer weighted formulation is an independent
generalization of that ingredient, not the full proposition or its graded
formulation.
-/

@[expose] public section

universe uR uM uι

namespace Submodule

variable {R : Type uR} [CommRing R]
variable {M : Type uM} [AddCommGroup M] [Module R M]
variable {ι : Type uι} [Finite ι]

omit [Finite ι] in
private theorem iSup_pow_smul_span_singleton_add_one
    (I : Ideal R) (d : ι → ℤ) (x : ι → M) (n : ℤ)
    (hd : ∀ i : ι, d i ≤ n) :
    (⨆ i : ι, (I ^ ((n + 1 - d i).toNat)) • span R ({x i} : Set M)) =
      I • (⨆ i : ι, (I ^ ((n - d i).toNat)) • span R ({x i} : Set M)) := by
  rw [smul_iSup]
  apply iSup_congr
  intro i
  have he : (n + 1 - d i).toNat = (n - d i).toNat + 1 := by
    have hi := hd i
    omega
  rw [he, Ideal.IsTwoSided.pow_succ, Submodule.mul_smul]

/-- Finite weighted generation of successive quotients over precomplete
coefficients makes a separated compatible integer filtration eventually
`I`-stable. No additional finiteness or exhaustivity assumption is needed, and the
generator family may be empty. This is the stability consequence of the
filtered lifting argument underlying Fujiwara--Kato, *Foundations of Rigid
Geometry I*, Proposition 0.7.5.2, in the generalized precomplete setting. -/
theorem exists_eq_smul_of_weighted_generation
    (I : Ideal R) [IsPrecomplete I R] (F : ℤ → Submodule R M)
    (hanti : Antitone F) (hcompat : ∀ n : ℤ, I • F n ≤ F (n + 1))
    (hsep : (⨅ n : ℤ, F n) = ⊥) (d : ι → ℤ) (x : ι → M)
    (hx : ∀ i : ι, x i ∈ F (d i))
    (hgen : ∀ n : ℤ, F n ≤
      (⨆ i : ι, (I ^ ((n - d i).toNat)) • span R ({x i} : Set M)) ⊔ F (n + 1)) :
    ∃ c : ℤ, ∀ n : ℤ, c ≤ n → F (n + 1) = I • F n := by
  classical
  let := Fintype.ofFinite ι
  -- A natural supremum has value zero for an empty family.
  let c : ℕ := Finset.univ.sup fun i : ι => (d i).toNat
  refine ⟨(c : ℤ), ?_⟩
  intro n hn
  have hd : ∀ i : ι, d i ≤ n := by
    intro i
    have hi : (d i).toNat ≤ c :=
      Finset.le_sup (f := fun i : ι => (d i).toNat) (Finset.mem_univ i)
    omega
  rw [eq_iSup_pow_smul_span_singleton_of_isPrecomplete I F hanti hcompat hsep d x hx hgen
      (n + 1),
    eq_iSup_pow_smul_span_singleton_of_isPrecomplete I F hanti hcompat hsep d x hx hgen n]
  exact iSup_pow_smul_span_singleton_add_one I d x n hd

/-- If a separated compatible integer filtration is exhaustive, finite weighted
generation of its successive quotients over precomplete coefficients makes the
original module finite. The ideal need not be finitely generated. This is the
ambient-finiteness consequence of the filtered lifting argument underlying
Fujiwara--Kato, *Foundations of Rigid Geometry I*, Proposition 0.7.5.2, with
precompleteness in place of completeness of the coefficient ring. -/
theorem moduleFinite_of_weighted_generation
    (I : Ideal R) [IsPrecomplete I R] (F : ℤ → Submodule R M)
    (hanti : Antitone F) (hcompat : ∀ n : ℤ, I • F n ≤ F (n + 1))
    (hsep : (⨅ n : ℤ, F n) = ⊥) (d : ι → ℤ) (x : ι → M)
    (hx : ∀ i : ι, x i ∈ F (d i))
    (hgen : ∀ n : ℤ, F n ≤
      (⨆ i : ι, (I ^ ((n - d i).toNat)) • span R ({x i} : Set M)) ⊔ F (n + 1))
    (hexhaustive : (⨆ n : ℤ, F n) = ⊤) : Module.Finite R M := by
  have hspan : (⨆ i : ι, span R ({x i} : Set M)) = ⊤ := by
    apply top_unique
    rw [← hexhaustive]
    refine iSup_le fun n => ?_
    rw [eq_iSup_pow_smul_span_singleton_of_isPrecomplete I F hanti hcompat hsep d x hx hgen n]
    exact iSup_le fun i =>
      smul_le_right.trans (le_iSup (fun i : ι => span R ({x i} : Set M)) i)
  apply Module.Finite.of_fg_top
  rw [← hspan]
  exact fg_iSup _ fun i => fg_span_singleton (x i)

/-- When `I` is finitely generated, finite weighted generation of successive
quotients over precomplete coefficients makes every stage of a separated
compatible integer filtration finitely generated, without exhaustivity. This is
the stage-finiteness consequence of the filtered lifting argument underlying
Fujiwara--Kato, *Foundations of Rigid Geometry I*, Proposition 0.7.5.2; it also
includes negative stages and negative generator weights. -/
theorem fg_of_weighted_generation
    (I : Ideal R) [IsPrecomplete I R] (F : ℤ → Submodule R M)
    (hanti : Antitone F) (hcompat : ∀ n : ℤ, I • F n ≤ F (n + 1))
    (hsep : (⨅ n : ℤ, F n) = ⊥) (d : ι → ℤ) (x : ι → M)
    (hx : ∀ i : ι, x i ∈ F (d i))
    (hgen : ∀ n : ℤ, F n ≤
      (⨆ i : ι, (I ^ ((n - d i).toNat)) • span R ({x i} : Set M)) ⊔ F (n + 1))
    (hI : I.FG) (n : ℤ) : (F n).FG := by
  rw [eq_iSup_pow_smul_span_singleton_of_isPrecomplete I F hanti hcompat hsep d x hx hgen n]
  exact fg_iSup _ fun i => Submodule.FG.smul (Ideal.FG.pow hI) (fg_span_singleton (x i))

end Submodule
