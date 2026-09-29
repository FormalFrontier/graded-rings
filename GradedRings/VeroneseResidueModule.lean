/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GradedRings.VeroneseResidue
public import Mathlib.Algebra.Module.GradedModule
public import Mathlib.Algebra.Module.Submodule.Equiv

/-!
# Shifted Veronese residue modules

The external direct sum of the components in degrees `n * k + r` carries the
convolution action of the entire external Veronese ring. Coefficient evaluation
identifies it with the range of the residue projection when `0 < n` and `r < n`.
-/

@[expose] public section

set_option warningAsError true
set_option linter.style.haveILetI false

noncomputable section

namespace GradedRing.Veronese

open DirectSum

universe u v

variable {S : Type u} [CommRing S] {σ : Type v} [SetLike σ S]
  [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-- The sum of the complete old homogeneous components in degrees `n * k + r`. -/
abbrev ResidueModule (n r : ℕ) := ⨁ (k : ℕ), 𝒮 (n * k + r)

instance shiftedGradedSMul (n r : ℕ) :
    SetLike.GradedSMul (fun i : ℕ => 𝒮 (n * i)) (fun k : ℕ => 𝒮 (n * k + r)) where
  smul_mem := by
    intro i k a b ha hb
    change a * b ∈ 𝒮 (n * (i + k) + r)
    simpa only [mul_add, add_assoc] using
      (SetLike.GradedMul.mul_mem ha hb : a * b ∈ 𝒮 (n * i + (n * k + r)))

/-- Convolution by the whole external Veronese ring on the shifted sum. -/
noncomputable instance instResidueModule (n r : ℕ) :
    Module (VeroneseRing 𝒮 n) (ResidueModule 𝒮 n r) := by
  classical
  infer_instance

/-- The action of a pure Veronese summand on a pure shifted summand. -/
theorem of_smul_of_residue (n r i k : ℕ) (a : 𝒮 (n * i)) (b : 𝒮 (n * k + r)) :
    DirectSum.of (fun j : ℕ => 𝒮 (n * j)) i a •
      DirectSum.of (fun j : ℕ => 𝒮 (n * j + r)) k b =
        DirectSum.of (fun j : ℕ => 𝒮 (n * j + r)) (i + k)
          (⟨(a : S) * b, by
            simpa only [mul_add, add_assoc] using
              (SetLike.GradedMul.mul_mem a.property b.property :
                (a : S) * b ∈ 𝒮 (n * i + (n * k + r)))⟩) := by
  classical
  exact DirectSum.Gmodule.of_smul_of (fun j : ℕ => 𝒮 (n * j))
    (fun j : ℕ => 𝒮 (n * j + r)) a b

/-- Coefficient evaluation, linear for the canonical full-Veronese action on `S`. -/
def residueEvaluation (n r : ℕ) :
    letI : Algebra (VeroneseRing 𝒮 n) S := (inclusion 𝒮 n).toAlgebra
    ResidueModule 𝒮 n r →ₗ[VeroneseRing 𝒮 n] S := by
  classical
  letI : Algebra (VeroneseRing 𝒮 n) S := (inclusion 𝒮 n).toAlgebra
  let evalAdd : ResidueModule 𝒮 n r →+ S :=
    DirectSum.coeAddMonoidHom (fun k : ℕ => 𝒮 (n * k + r))
  refine { evalAdd with map_smul' := ?_ }
  intro a x
  change evalAdd (a • x) = inclusion 𝒮 n a * evalAdd x
  induction a using DirectSum.induction_on with
  | zero => simp
  | of i a =>
    induction x using DirectSum.induction_on with
    | zero => simp
    | of k b =>
      change evalAdd (DirectSum.of (fun j : ℕ => 𝒮 (n * j)) i a •
          DirectSum.of (fun j : ℕ => 𝒮 (n * j + r)) k b) =
        inclusion 𝒮 n (DirectSum.of (fun j : ℕ => 𝒮 (n * j)) i a) *
          evalAdd (DirectSum.of (fun j : ℕ => 𝒮 (n * j + r)) k b)
      rw [of_smul_of_residue, inclusion_of, DirectSum.coeAddMonoidHom_of,
        DirectSum.coeAddMonoidHom_of]
    | add x y hx hy =>
      simp only [smul_add, map_add, mul_add, hx, hy]
  | add a b ha hb =>
    simp only [add_smul, map_add, add_mul, ha, hb]

@[simp] theorem residueEvaluation_of (n r k : ℕ) (b : 𝒮 (n * k + r)) :
    residueEvaluation 𝒮 n r (DirectSum.of (fun j : ℕ => 𝒮 (n * j + r)) k b) = b := by
  exact DirectSum.coeAddMonoidHom_of (fun k : ℕ => 𝒮 (n * k + r)) k b

/-- Put the shifted summands back into the original direct-sum indexing. -/
private def residueReindex (n r : ℕ) : ResidueModule 𝒮 n r →+ ⨁ d : ℕ, 𝒮 d :=
  DirectSum.toAddMonoid fun k => DirectSum.of (fun d : ℕ => 𝒮 d) (n * k + r)

private theorem decompose_residueEvaluation (n r : ℕ) (x : ResidueModule 𝒮 n r) :
    DirectSum.decompose 𝒮 (residueEvaluation 𝒮 n r x) = residueReindex 𝒮 n r x := by
  induction x using DirectSum.induction_on with
  | zero => simp [residueReindex]
  | of k a =>
    rw [residueEvaluation_of, DirectSum.decompose_coe]
    change DirectSum.of (fun d : ℕ => 𝒮 d) (n * k + r) a =
      DirectSum.toAddMonoid (fun k => DirectSum.of (fun d : ℕ => 𝒮 d) (n * k + r))
        (DirectSum.of (fun k : ℕ => 𝒮 (n * k + r)) k a)
    rw [DirectSum.toAddMonoid_of]
  | add x y hx hy =>
    simp only [map_add, DirectSum.decompose_add, hx, hy]

/-- Distinct shifted degrees have distinct old degree, whenever `n` is positive. -/
theorem residueEvaluation_injective (n r : ℕ) (hn : 0 < n) :
    Function.Injective (residueEvaluation 𝒮 n r) := by
  classical
  have hindex : Function.Injective (fun k : ℕ => n * k + r) := by
    intro i j hij
    exact Nat.eq_of_mul_eq_mul_left hn (Nat.add_right_cancel hij)
  have hleft : ∀ x : ResidueModule 𝒮 n r,
      DFinsupp.comapDomain (fun k : ℕ => n * k + r) hindex (residueReindex 𝒮 n r x) = x := by
    intro x
    induction x using DirectSum.induction_on with
    | zero => simp [residueReindex]
    | of k a =>
      rw [residueReindex, DirectSum.toAddMonoid_of]
      change DFinsupp.comapDomain (fun k : ℕ => n * k + r) hindex
        (DFinsupp.single (n * k + r) a : ⨁ d : ℕ, 𝒮 d) =
        (DFinsupp.single k a : ResidueModule 𝒮 n r)
      exact DFinsupp.comapDomain_single (β := fun d : ℕ => 𝒮 d)
        (fun k : ℕ => n * k + r) hindex k a
    | add x y hx hy =>
      rw [map_add, DFinsupp.comapDomain_add, hx, hy]
  intro x y hxy
  calc
    x = DFinsupp.comapDomain (fun k : ℕ => n * k + r) hindex
        (residueReindex 𝒮 n r x) := (hleft x).symm
    _ = DFinsupp.comapDomain (fun k : ℕ => n * k + r) hindex
        (residueReindex 𝒮 n r y) := by
      rw [← decompose_residueEvaluation 𝒮 n r x,
        ← decompose_residueEvaluation 𝒮 n r y, hxy]
    _ = y := hleft y

/-- Reindexed shifted sums have no coordinates outside the chosen residue class. -/
private theorem residueReindex_apply_of_mod_ne (n r : ℕ) (hr : r < n)
    (x : ResidueModule 𝒮 n r) (d : ℕ) (hd : d % n ≠ r) :
    residueReindex 𝒮 n r x d = 0 := by
  classical
  induction x using DirectSum.induction_on with
  | zero => simp
  | of k a =>
    have hne : d ≠ n * k + r := by
      intro heq
      apply hd
      rw [heq]
      simp [Nat.add_mod, Nat.mod_eq_of_lt hr]
    rw [residueReindex, DirectSum.toAddMonoid_of]
    exact DFinsupp.single_eq_of_ne hne
  | add x y hx hy =>
    rw [map_add, DFinsupp.add_apply, hx, hy, add_zero]

/-- Evaluation lands in, and exhausts, the canonical residue projection range. -/
theorem residueEvaluation_range_eq (n r : ℕ) (hn : 0 < n) (hr : r < n) :
    letI : Algebra (VeroneseRing 𝒮 n) S := (inclusion 𝒮 n).toAlgebra
    (residueEvaluation 𝒮 n r).range = (residueProjection 𝒮 n r hn hr).range := by
  classical
  letI : Algebra (VeroneseRing 𝒮 n) S := (inclusion 𝒮 n).toAlgebra
  apply le_antisymm
  · intro x hx
    obtain ⟨y, rfl⟩ := hx
    apply (mem_residueProjection_range_iff 𝒮 n r hn hr _).mpr
    intro d hd
    rw [decompose_residueEvaluation]
    exact residueReindex_apply_of_mod_ne 𝒮 n r hr y d hd
  · intro x hx
    obtain ⟨y, rfl⟩ := hx
    induction y using DirectSum.Decomposition.inductionOn (ℳ := 𝒮) with
    | zero => simp
    | homogeneous a =>
      rename_i d
      rw [residueProjection_of_mem 𝒮 n r d hn hr a.property]
      by_cases hd : d % n = r
      · simp only [ite_eq_left hd]
        have hdeg : d = n * (d / n) + r := by
          calc
            d = d % n + n * (d / n) := (Nat.mod_add_div d n).symm
            _ = n * (d / n) + r := by rw [hd, add_comm]
        let b : 𝒮 (n * (d / n) + r) := ⟨a, hdeg ▸ a.property⟩
        exact ⟨DirectSum.of (fun k : ℕ => 𝒮 (n * k + r)) (d / n) b, by
          simp only [residueEvaluation_of]
          rfl⟩
      · simp only [ite_eq_right hd]
        exact Submodule.zero_mem _
    | add x y hx hy =>
      rw [map_add]
      exact Submodule.add_mem _ hx hy

/-- The explicit external shifted sum is the internal projection range. -/
noncomputable def residueEvaluationEquiv (n r : ℕ) (hn : 0 < n) (hr : r < n) :
    letI : Algebra (VeroneseRing 𝒮 n) S := (inclusion 𝒮 n).toAlgebra
    ResidueModule 𝒮 n r ≃ₗ[VeroneseRing 𝒮 n]
      (residueProjection 𝒮 n r hn hr).range := by
  letI : Algebra (VeroneseRing 𝒮 n) S := (inclusion 𝒮 n).toAlgebra
  exact (LinearEquiv.ofInjective (residueEvaluation 𝒮 n r)
    (residueEvaluation_injective 𝒮 n r hn)).trans
      (LinearEquiv.ofEq _ _ (residueEvaluation_range_eq 𝒮 n r hn hr))

@[simp] theorem residueEvaluationEquiv_apply (n r : ℕ) (hn : 0 < n) (hr : r < n)
    (x : ResidueModule 𝒮 n r) :
    letI : Algebra (VeroneseRing 𝒮 n) S := (inclusion 𝒮 n).toAlgebra
    ((residueEvaluationEquiv 𝒮 n r hn hr x :
      (residueProjection 𝒮 n r hn hr).range) : S) = residueEvaluation 𝒮 n r x := by
  letI : Algebra (VeroneseRing 𝒮 n) S := (inclusion 𝒮 n).toAlgebra
  rfl

/-- Finiteness of the shifted module, transported from the finite linear image. -/
theorem residueModule_finite (n r : ℕ) (hn : 0 < n) (hr : r < n) :
    letI : Algebra (VeroneseRing 𝒮 n) S := (inclusion 𝒮 n).toAlgebra
    [Module.Finite (VeroneseRing 𝒮 n) S] →
      Module.Finite (VeroneseRing 𝒮 n) (ResidueModule 𝒮 n r) := by
  letI : Algebra (VeroneseRing 𝒮 n) S := (inclusion 𝒮 n).toAlgebra
  intro _
  letI : Module.Finite (VeroneseRing 𝒮 n) (residueProjection 𝒮 n r hn hr).range :=
    residueProjection_range_finite 𝒮 n r hn hr
  exact Module.Finite.equiv (residueEvaluationEquiv 𝒮 n r hn hr).symm

/-- Finite type over the full original degree-zero ring suffices for finite generation. -/
theorem residueModule_finite_of_finiteType [Algebra.FiniteType (𝒮 0) S]
    (n r : ℕ) (hn : 0 < n) (hr : r < n) :
    Module.Finite (VeroneseRing 𝒮 n) (ResidueModule 𝒮 n r) := by
  letI : Algebra (VeroneseRing 𝒮 n) S := (inclusion 𝒮 n).toAlgebra
  letI : Module.Finite (VeroneseRing 𝒮 n) (residueProjection 𝒮 n r hn hr).range :=
    residueProjection_range_finite_of_finiteType 𝒮 n r hn hr
  exact Module.Finite.equiv (residueEvaluationEquiv 𝒮 n r hn hr).symm

end GradedRing.Veronese
