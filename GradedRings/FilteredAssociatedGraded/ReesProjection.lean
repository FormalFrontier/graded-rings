/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GradedRings.FilteredAssociatedGraded.ReesAction
public import GradedRings.ReesModule.FiniteGeneration
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.RingTheory.Finiteness.Basic

/-!
# Projection from a shifted Rees module to an associated graded module

The natural tail of an integer filtration defines a polynomial Rees submodule.
The coefficientwise homogeneous-class sum is semilinear along the quotient
from the Rees algebra to its coefficient-ideal quotient. Its kernel is the next
tail, and its image consists exactly of elements vanishing below the cutoff.
A finite tail therefore gives a finite associated graded when the lower pieces
vanish. Eventual ideal stability and finite generation through the stability
threshold suffice for a finite tail. For an exhaustive integer filtration on a
finite original module, stability at and above a common threshold and finite
generation of stages at and below it give this finite associated graded.

## References

* Mathlib's `Ideal.Filtration` and polynomial-module development supply the
  natural Rees submodule and its admissible-single generation.
* Mathlib's finite-support linear maps and semilinear finite-image theorem.
-/

@[expose] public section

universe u v w

namespace Ideal.IntFiltration

variable {R : Type u} [CommRing R] {I : Ideal R}
variable {M : Type v} [AddCommGroup M] [Module R M]
variable (F : I.IntFiltration M)

local notation "B" => reesAlgebra I
local notation "J" => I.map (algebraMap R B)
local notation "C" => B ⧸ J

/-- An admissible polynomial single in the natural tail. -/
noncomputable def natTailSingle (k : ℤ) (q : ℕ) (m : F.N (k + (q : ℤ))) :
    (F.natTail k).submodule :=
  ⟨PolynomialModule.single R q (m : M), by
    intro i
    change (PolynomialModule.single R q (m : M)).coeff i ∈ F.N (k + (i : ℤ))
    rw [PolynomialModule.coeff_single, Finsupp.single_apply]
    split_ifs with hqi
    · subst i
      exact m.property
    · exact (F.N (k + (i : ℤ))).zero_mem⟩

/-- The tail single has the prescribed polynomial value. -/
@[simp]
theorem coe_natTailSingle (k : ℤ) (q : ℕ) (m : F.N (k + (q : ℤ))) :
    (F.natTailSingle k q m : PolynomialModule R M) =
      PolynomialModule.single R q (m : M) := rfl

private theorem sum_natTailSingle (k : ℤ) (p : (F.natTail k).submodule) :
    (∑ q ∈ (p : PolynomialModule R M).coeff.support,
      F.natTailSingle k q ⟨(p : PolynomialModule R M).coeff q, p.property q⟩) = p := by
  classical
  apply Subtype.ext
  calc
    (↑(∑ q ∈ (p : PolynomialModule R M).coeff.support,
        F.natTailSingle k q ⟨(p : PolynomialModule R M).coeff q, p.property q⟩) :
        PolynomialModule R M) =
        ∑ q ∈ (p : PolynomialModule R M).coeff.support,
          PolynomialModule.single R q ((p : PolynomialModule R M).coeff q) :=
      map_sum ((F.natTail k).submodule.subtype) _ _
    _ = (p : PolynomialModule R M) := by
      apply PolynomialModule.coeff_injective
      simpa only [PolynomialModule.coeff_sum, PolynomialModule.coeff_single, Finsupp.sum]
        using Finsupp.sum_single (p : PolynomialModule R M).coeff

/-- Additive maps from a tail agree if they agree on all admissible polynomial singles. -/
theorem natTail_addHom_ext (k : ℤ) {A : Type w} [AddCommMonoid A]
    {f g : (F.natTail k).submodule →+ A}
    (h : ∀ (q : ℕ) (m : F.N (k + (q : ℤ))),
      f (F.natTailSingle k q m) = g (F.natTailSingle k q m)) : f = g := by
  classical
  apply AddMonoidHom.ext
  intro p
  calc
    f p = f (∑ q ∈ (p : PolynomialModule R M).coeff.support,
        F.natTailSingle k q ⟨(p : PolynomialModule R M).coeff q, p.property q⟩) :=
      congrArg f (sum_natTailSingle F k p).symm
    _ = g (∑ q ∈ (p : PolynomialModule R M).coeff.support,
        F.natTailSingle k q ⟨(p : PolynomialModule R M).coeff q, p.property q⟩) := by
      simp only [map_sum]
      exact Finset.sum_congr rfl (fun q _ => h q _)
    _ = g p := congrArg g (sum_natTailSingle F k p)

private noncomputable def reesProjectionFun (k : ℤ) (p : (F.natTail k).submodule) :
    F.AssociatedGraded := by
  classical
  exact ∑ q ∈ (p : PolynomialModule R M).coeff.support,
    F.single (k + (q : ℤ)) ⟨(p : PolynomialModule R M).coeff q, p.property q⟩

private theorem reesProjectionFun_eq_sum_of_support_subset (k : ℤ)
    (p : (F.natTail k).submodule) (s : Finset ℕ)
    (hs : (p : PolynomialModule R M).coeff.support ⊆ s) :
    reesProjectionFun F k p = ∑ q ∈ s,
      F.single (k + (q : ℤ)) ⟨(p : PolynomialModule R M).coeff q, p.property q⟩ := by
  classical
  unfold reesProjectionFun
  apply Finset.sum_subset hs
  intro q _ hq
  have hc : (p : PolynomialModule R M).coeff q = 0 := Finsupp.notMem_support_iff.mp hq
  have hz : (⟨(p : PolynomialModule R M).coeff q, p.property q⟩ :
      F.N (k + (q : ℤ))) = 0 := Subtype.ext hc
  rw [hz, map_zero]

private theorem reesProjectionFun_zero (k : ℤ) :
    reesProjectionFun F k 0 = 0 := by
  classical
  simp [reesProjectionFun]

private theorem reesProjectionFun_add (k : ℤ) (p p' : (F.natTail k).submodule) :
    reesProjectionFun F k (p + p') = reesProjectionFun F k p + reesProjectionFun F k p' := by
  classical
  let s := (p : PolynomialModule R M).coeff.support ∪
    (p' : PolynomialModule R M).coeff.support
  have hp : (p : PolynomialModule R M).coeff.support ⊆ s := Finset.subset_union_left
  have hp' : (p' : PolynomialModule R M).coeff.support ⊆ s := Finset.subset_union_right
  have hadd : (↑(p + p') : PolynomialModule R M).coeff.support ⊆ s := by
    change ((p : PolynomialModule R M).coeff + (p' : PolynomialModule R M).coeff).support ⊆ s
    exact Finsupp.support_add
  rw [reesProjectionFun_eq_sum_of_support_subset F k (p + p') s hadd,
    reesProjectionFun_eq_sum_of_support_subset F k p s hp,
    reesProjectionFun_eq_sum_of_support_subset F k p' s hp', ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q _
  have hrep : (⟨(↑(p + p') : PolynomialModule R M).coeff q, (p + p').property q⟩ :
      F.N (k + (q : ℤ))) =
      (⟨(p : PolynomialModule R M).coeff q, p.property q⟩ : F.N (k + (q : ℤ))) +
        ⟨(p' : PolynomialModule R M).coeff q, p'.property q⟩ := by
    apply Subtype.ext
    rfl
  rw [hrep, map_add]

private theorem reesProjectionFun_single (k : ℤ) (q : ℕ)
    (m : F.N (k + (q : ℤ))) :
    reesProjectionFun F k (F.natTailSingle k q m) = F.single (k + (q : ℤ)) m := by
  classical
  have hs : (F.natTailSingle k q m : PolynomialModule R M).coeff.support ⊆ {q} := by
    change (Finsupp.single q (m : M)).support ⊆ {q}
    exact Finsupp.support_single_subset
  rw [reesProjectionFun_eq_sum_of_support_subset F k (F.natTailSingle k q m) {q} hs,
    Finset.sum_singleton]
  apply congrArg (F.single (k + (q : ℤ)))
  apply Subtype.ext
  exact Finsupp.single_eq_same

private theorem reesProjectionFun_smul_R (k : ℤ) (r : R) (p : (F.natTail k).submodule) :
    reesProjectionFun F k (r • p) = r • reesProjectionFun F k p := by
  classical
  have hcoeff : (r • (p : PolynomialModule R M)).coeff =
      r • (p : PolynomialModule R M).coeff :=
    (PolynomialModule.coeffLinearEquiv R R).map_smul r (p : PolynomialModule R M)
  have hs : (↑(r • p) : PolynomialModule R M).coeff.support ⊆
      (p : PolynomialModule R M).coeff.support := by
    change (r • (p : PolynomialModule R M)).coeff.support ⊆ _
    rw [hcoeff]
    exact Finsupp.support_smul
  rw [reesProjectionFun_eq_sum_of_support_subset F k (r • p)
    (p : PolynomialModule R M).coeff.support hs, reesProjectionFun, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro q _
  have hrep : (⟨(↑(r • p) : PolynomialModule R M).coeff q, (r • p).property q⟩ :
      F.N (k + (q : ℤ))) =
      r • (⟨(p : PolynomialModule R M).coeff q, p.property q⟩ : F.N (k + (q : ℤ))) := by
    apply Subtype.ext
    exact congrArg (fun c : ℕ →₀ M => c q) hcoeff
  rw [hrep, map_smul]

private theorem reesProjectionFun_smul (k : ℤ) (b : B) (p : (F.natTail k).submodule) :
    reesProjectionFun F k (b • p) = (Ideal.Quotient.mk J b : C) • reesProjectionFun F k p := by
  classical
  let π : (F.natTail k).submodule →+ F.AssociatedGraded :=
    { toFun := reesProjectionFun F k
      map_zero' := reesProjectionFun_zero F k
      map_add' := reesProjectionFun_add F k }
  have hsingle {n n' : ℤ} (hn : n = n') (m : F.N n) (m' : F.N n')
      (hm : (m : M) = (m' : M)) : F.single n m = F.single n' m' := by
    subst n'
    exact congrArg (F.single n) (Subtype.ext hm)
  have hmonomial (d : ℕ) (a : ↥(I ^ d)) (x : (F.natTail k).submodule) :
      π (reesAlgebra.monomial I d a • x) =
        (Ideal.Quotient.mk J (reesAlgebra.monomial I d a) : C) • π x := by
    -- Both sides are additive in the tail variable. Its admissible singles
    -- retain the stage membership needed by the homogeneous target formula.
    let left : (F.natTail k).submodule →+ F.AssociatedGraded :=
      { toFun := fun y => π (reesAlgebra.monomial I d a • y)
        map_zero' := by rw [smul_zero, π.map_zero]
        map_add' := by
          intro y z
          rw [smul_add, π.map_add] }
    let right : (F.natTail k).submodule →+ F.AssociatedGraded :=
      { toFun := fun y =>
          (Ideal.Quotient.mk J (reesAlgebra.monomial I d a) : C) • π y
        map_zero' := by rw [π.map_zero, smul_zero]
        map_add' := by
          intro y z
          rw [π.map_add, smul_add] }
    have h : left = right := by
      apply F.natTail_addHom_ext k
      intro q m
      have hdeg : k + ((d + q : ℕ) : ℤ) = (k + (q : ℤ)) + (d : ℤ) := by
        rw [Nat.cast_add, add_comm (d : ℤ) (q : ℤ), add_assoc]
      have hmem : (a : R) • (m : M) ∈ F.N (k + ((d + q : ℕ) : ℤ)) := by
        rw [hdeg]
        exact F.pow_smul_le d (k + (q : ℤ))
          (Submodule.smul_mem_smul a.property m.property)
      let m' : F.N (k + ((d + q : ℕ) : ℤ)) := ⟨(a : R) • (m : M), hmem⟩
      have hsource : reesAlgebra.monomial I d a • F.natTailSingle k q m =
          F.natTailSingle k (d + q) m' := by
        apply Subtype.ext
        change (reesAlgebra.monomial I d a : B) •
            (F.natTailSingle k q m : PolynomialModule R M) =
          (F.natTailSingle k (d + q) m' : PolynomialModule R M)
        simp only [coe_natTailSingle, Subalgebra.smul_def, reesAlgebra.coe_monomial,
          PolynomialModule.monomial_smul_single, m']
      change reesProjectionFun F k
          (reesAlgebra.monomial I d a • F.natTailSingle k q m) =
        (Ideal.Quotient.mk J (reesAlgebra.monomial I d a) : C) •
          reesProjectionFun F k (F.natTailSingle k q m)
      rw [hsource, reesProjectionFun_single, reesProjectionFun_single,
        F.monomial_smul_single]
      exact hsingle hdeg _ _ rfl
    exact DFunLike.congr_fun h x
  -- Assemble scalars using the existing natural homogeneous decomposition of
  -- the stock Rees algebra, not an ambient induction with arbitrary coefficients.
  change π (b • p) = (Ideal.Quotient.mk J b : C) • π p
  induction b using DirectSum.Decomposition.inductionOn
      (reesAlgebra.homogeneousComponent I) with
  | zero =>
      calc
        π ((0 : B) • p) = 0 := by
          rw [_root_.zero_smul B p, π.map_zero]
        _ = (Ideal.Quotient.mk J (0 : B) : C) • π p := by
          rw [_root_.map_zero]
          exact (_root_.zero_smul C (π p)).symm
  | homogeneous b =>
      obtain ⟨a, ha⟩ :=
        (reesAlgebra.mem_homogeneousComponent_iff I _ (b : B)).mp b.property
      simpa only [ha] using hmonomial _ a p
  | add b b' hb hb' =>
      rw [add_smul, π.map_add, hb, hb', _root_.map_add, add_smul]

/-- The homogeneous-class sum of the coefficients of a shifted Rees polynomial,
semilinear for the quotient from the Rees algebra. -/
@[no_expose]
noncomputable def shiftedReesProjection (k : ℤ) :
    (F.natTail k).submodule →ₛₗ[Ideal.Quotient.mk J] F.AssociatedGraded where
  toFun := reesProjectionFun F k
  map_add' := reesProjectionFun_add F k
  map_smul' := reesProjectionFun_smul F k

private theorem shiftedReesProjection_apply_eq (k : ℤ) (p : (F.natTail k).submodule) :
    F.shiftedReesProjection k p =
      ∑ q ∈ (p : PolynomialModule R M).coeff.support,
        F.single (k + (q : ℤ)) ⟨(p : PolynomialModule R M).coeff q, p.property q⟩ := by
  rfl

private theorem shiftedReesProjection_single_eq (k : ℤ) (q : ℕ)
    (m : F.N (k + (q : ℤ))) :
    F.shiftedReesProjection k (F.natTailSingle k q m) = F.single (k + (q : ℤ)) m :=
  reesProjectionFun_single F k q m

private theorem shiftedReesProjection_smul_R_eq (k : ℤ) (r : R)
    (p : (F.natTail k).submodule) :
    F.shiftedReesProjection k (r • p) = r • F.shiftedReesProjection k p :=
  reesProjectionFun_smul_R F k r p

/-- The projection is the sum over the original polynomial coefficient support. -/
theorem shiftedReesProjection_apply (k : ℤ) (p : (F.natTail k).submodule) :
    F.shiftedReesProjection k p =
      ∑ q ∈ (p : PolynomialModule R M).coeff.support,
        F.single (k + (q : ℤ)) ⟨(p : PolynomialModule R M).coeff q, p.property q⟩ :=
  shiftedReesProjection_apply_eq F k p

/-- An admissible polynomial single maps to its homogeneous class. -/
@[simp]
theorem shiftedReesProjection_single (k : ℤ) (q : ℕ) (m : F.N (k + (q : ℤ))) :
    F.shiftedReesProjection k (F.natTailSingle k q m) = F.single (k + (q : ℤ)) m :=
  shiftedReesProjection_single_eq F k q m

/-- The projection preserves the original coefficient-ring scalar action. -/
theorem shiftedReesProjection_smul_R (k : ℤ) (r : R) (p : (F.natTail k).submodule) :
    F.shiftedReesProjection k (r • p) = r • F.shiftedReesProjection k p :=
  shiftedReesProjection_smul_R_eq F k r p

/-- The scalar law uses the stock source action and the quotient-Rees target action. -/
theorem shiftedReesProjection_smul (k : ℤ) (b : B) (p : (F.natTail k).submodule) :
    F.shiftedReesProjection k (b • p) = (Ideal.Quotient.mk J b : C) •
      F.shiftedReesProjection k p :=
  (F.shiftedReesProjection k).map_smul' b p

/-- Its values on admissible singles characterize the semilinear projection. -/
theorem shiftedReesProjection_unique (k : ℤ)
    (f : (F.natTail k).submodule →ₛₗ[Ideal.Quotient.mk J] F.AssociatedGraded)
    (h : ∀ (q : ℕ) (m : F.N (k + (q : ℤ))),
      f (F.natTailSingle k q m) = F.single (k + (q : ℤ)) m) :
    f = F.shiftedReesProjection k := by
  have hfg : f.toAddMonoidHom = (F.shiftedReesProjection k).toAddMonoidHom := by
    apply F.natTail_addHom_ext k
    intro q m
    exact (h q m).trans (F.shiftedReesProjection_single k q m).symm
  apply LinearMap.ext
  intro p
  exact DFunLike.congr_fun hfg p

/-- Projection to a tail degree gives the class of that polynomial coefficient. -/
@[simp]
theorem component_shiftedReesProjection (k : ℤ) (q : ℕ) (p : (F.natTail k).submodule) :
    F.component (k + (q : ℤ)) (F.shiftedReesProjection k p) =
      F.cl (k + (q : ℤ)) ⟨(p : PolynomialModule R M).coeff q, p.property q⟩ := by
  classical
  rw [shiftedReesProjection_apply, map_sum]
  trans F.component (k + (q : ℤ))
    (F.single (k + (q : ℤ)) ⟨(p : PolynomialModule R M).coeff q, p.property q⟩)
  · apply Finset.sum_eq_single q
    · intro i _ hi
      apply F.component_single_of_ne
      intro he
      apply hi
      lia
    · intro hq
      have hz : (p : PolynomialModule R M).coeff q = 0 :=
        Finsupp.notMem_support_iff.mp hq
      have hm : (⟨(p : PolynomialModule R M).coeff q, p.property q⟩ :
          F.N (k + (q : ℤ))) = 0 := Subtype.ext hz
      simp only [hm, map_zero]
  · exact F.component_single _ _

/-- All components strictly below the tail cutoff vanish. -/
theorem component_shiftedReesProjection_of_lt (k : ℤ) (n : ℤ) (hn : n < k)
    (p : (F.natTail k).submodule) :
    F.component n (F.shiftedReesProjection k p) = 0 := by
  classical
  rw [shiftedReesProjection_apply, map_sum]
  apply Finset.sum_eq_zero
  intro q _
  apply F.component_single_of_ne
  lia

private theorem component_shiftedReesProjection_at_degree (k : ℤ) (q : ℕ)
    (n : ℤ) (he : k + (q : ℤ) = n) (p : (F.natTail k).submodule) :
    F.component n (F.shiftedReesProjection k p) =
      F.cl n ⟨(p : PolynomialModule R M).coeff q, he ▸ p.property q⟩ := by
  subst n
  exact F.component_shiftedReesProjection k q p

/-- Every integer component at or above the cutoff is its transported coefficient class. -/
theorem component_shiftedReesProjection_of_le (k n : ℤ) (hn : k ≤ n)
    (p : (F.natTail k).submodule) :
    F.component n (F.shiftedReesProjection k p) =
      F.cl n ⟨(p : PolynomialModule R M).coeff (n - k).toNat, by
        have he : k + (((n - k).toNat : ℕ) : ℤ) = n := by lia
        simpa only [natTail_N, he] using p.property (n - k).toNat⟩ := by
  have he : k + (((n - k).toNat : ℕ) : ℤ) = n := by lia
  exact component_shiftedReesProjection_at_degree F k (n - k).toNat n he p

/-- A top stage makes every strictly lower graded piece subsingleton. -/
theorem subsingleton_gradedPiece_of_lt_of_top (k : ℤ) (hF : F.N k = ⊤)
    (n : ℤ) (hn : n < k) : Subsingleton (F.GradedPiece n) := by
  have hz : ∀ z : F.GradedPiece n, z = 0 := by
    intro z
    obtain ⟨m, rfl⟩ := F.cl_surjective n z
    apply (F.cl_eq_zero_iff n m).2
    apply F.antitone (show n + 1 ≤ k by lia)
    rw [hF]
    exact Submodule.mem_top
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

/-- The projection vanishes exactly when every coefficient lies in the next stage. -/
theorem shiftedReesProjection_eq_zero_iff (k : ℤ) (p : (F.natTail k).submodule) :
    F.shiftedReesProjection k p = 0 ↔
      ∀ q : ℕ, (p : PolynomialModule R M).coeff q ∈ F.N (k + (q : ℤ) + 1) := by
  constructor
  · intro hp q
    apply (F.cl_eq_zero_iff (k + (q : ℤ))
      ⟨(p : PolynomialModule R M).coeff q, p.property q⟩).1
    rw [← F.component_shiftedReesProjection k q p, hp, map_zero]
  · intro hp
    apply F.associatedGraded_ext
    intro n
    by_cases hn : n < k
    · rw [F.component_shiftedReesProjection_of_lt k n hn p, map_zero]
    · have he : k + (((n - k).toNat : ℕ) : ℤ) = n := by lia
      rw [F.component_shiftedReesProjection_of_le k n (le_of_not_gt hn) p, map_zero]
      apply (F.cl_eq_zero_iff n _).2
      simpa only [he] using hp (n - k).toNat

/-- The kernel is the next tail pulled back to the source tail. -/
theorem ker_shiftedReesProjection (k : ℤ) :
    LinearMap.ker (F.shiftedReesProjection k) =
      ((F.natTail (k + 1)).submodule).comap ((F.natTail k).submodule).subtype := by
  ext p
  rw [LinearMap.mem_ker, F.shiftedReesProjection_eq_zero_iff]
  change (∀ q : ℕ, (p : PolynomialModule R M).coeff q ∈ F.N (k + (q : ℤ) + 1)) ↔
    ∀ q : ℕ, (p : PolynomialModule R M).coeff q ∈ F.N ((k + 1) + (q : ℤ))
  constructor <;> intro hp q <;>
    simpa only [add_assoc, add_comm, add_left_comm] using hp q

private theorem single_mem_range_shiftedReesProjection (k n : ℤ) (hn : k ≤ n)
    (m : F.N n) : F.single n m ∈ LinearMap.range (F.shiftedReesProjection k) := by
  let q : ℕ := (n - k).toNat
  have he : k + (q : ℤ) = n := by dsimp [q]; lia
  have hlift : ∀ (d : ℤ) (hd : k + (q : ℤ) = d) (a : F.N d),
      F.shiftedReesProjection k
          (F.natTailSingle k q ⟨(a : M), hd.symm ▸ a.property⟩) = F.single d a := by
    intro d hd a
    subst d
    exact F.shiftedReesProjection_single k q a
  exact ⟨F.natTailSingle k q ⟨(m : M), he.symm ▸ m.property⟩, hlift n he m⟩

/-- The projection image consists exactly of elements supported at or above the cutoff. -/
theorem mem_range_shiftedReesProjection_iff (k : ℤ) (z : F.AssociatedGraded) :
    z ∈ LinearMap.range (F.shiftedReesProjection k) ↔
      ∀ n : ℤ, n < k → F.component n z = 0 := by
  classical
  constructor
  · rintro ⟨p, rfl⟩ n hn
    exact F.component_shiftedReesProjection_of_lt k n hn p
  · intro hz
    rw [← F.sum_support_inclusion z]
    apply Submodule.sum_mem
    intro n _
    by_cases hn : k ≤ n
    · obtain ⟨m, hm⟩ := F.cl_surjective n (F.component n z)
      simpa only [single_apply, hm] using
        single_mem_range_shiftedReesProjection F k n hn m
    · rw [hz n (lt_of_not_ge hn), map_zero]
      exact Submodule.zero_mem _

/-- Vanishing of lower pieces makes the shifted Rees projection surjective. -/
theorem shiftedReesProjection_surjective (k : ℤ)
    (hlower : ∀ n : ℤ, n < k → Subsingleton (F.GradedPiece n)) :
    Function.Surjective (F.shiftedReesProjection k) := by
  intro z
  apply (F.mem_range_shiftedReesProjection_iff k z).2
  intro n hn
  let : Subsingleton (F.GradedPiece n) := hlower n hn
  exact Subsingleton.elim _ _

/-- A finite shifted Rees module generates the full associated graded when lower pieces vanish. -/
theorem finite_of_finite_natTail (k : ℤ)
    [Module.Finite B (F.natTail k).submodule]
    (hlower : ∀ n : ℤ, n < k → Subsingleton (F.GradedPiece n)) :
    Module.Finite C F.AssociatedGraded := by
  exact Module.Finite.of_surjective (F.shiftedReesProjection k)
    (F.shiftedReesProjection_surjective k hlower)

/-- An FG shifted Rees submodule gives the same finite-image conclusion. -/
theorem finite_of_fg_natTail (k : ℤ) (hfg : ((F.natTail k).submodule).FG)
    (hlower : ∀ n : ℤ, n < k → Subsingleton (F.GradedPiece n)) :
    Module.Finite C F.AssociatedGraded := by
  let : Module.Finite B (F.natTail k).submodule := Module.Finite.of_fg hfg
  exact F.finite_of_finite_natTail k hlower

/-- A natural tail is finitely generated if it is stable from `q0` onward and its stages
through `q0` are finitely generated over the original coefficient ring. -/
theorem natTail_submodule_fg_of_stable_ge (k : ℤ) (q0 : ℕ)
    (hstable : ∀ q : ℕ, q0 ≤ q →
      I • F.N (k + (q : ℤ)) = F.N (k + (q : ℤ) + 1))
    (hinit : ∀ q : ℕ, q ≤ q0 → (F.N (k + (q : ℤ))).FG) :
    ((F.natTail k).submodule).FG := by
  apply Ideal.Filtration.submodule_fg_of_stable_ge (F.natTail k) q0
  · intro q hq
    simpa only [natTail_N, Nat.cast_add, Nat.cast_one, add_assoc] using hstable q hq
  · intro q hq
    simpa only [natTail_N] using hinit q hq

/-- An exhaustive integer filtration on a finite original module has finite associated graded
over the quotient Rees algebra if it is stable at and above `c` and its stages at and below
`c` are finitely generated. Finiteness of the original module supplies a top stage; no
finite-generation hypothesis is imposed on stages above `c`. -/
theorem finite_of_stable_ge_of_fg_le [Module.Finite R M]
    (hexhaustive : (⨆ n : ℤ, F.N n) = ⊤) (c : ℤ)
    (hstable : ∀ n : ℤ, c ≤ n → I • F.N n = F.N (n + 1))
    (hstage : ∀ n : ℤ, n ≤ c → (F.N n).FG) :
    Module.Finite C F.AssociatedGraded := by
  obtain ⟨k0, hk0⟩ := F.exists_eq_top_of_iSup_eq_top hexhaustive
  let k : ℤ := min k0 c
  have hkk0 : k ≤ k0 := min_le_left _ _
  have hkc : k ≤ c := min_le_right _ _
  have hk : F.N k = ⊤ := by
    apply top_unique
    rw [← hk0]
    exact F.antitone hkk0
  let q0 : ℕ := (c - k).toNat
  have hq0 : k + (q0 : ℤ) = c := by
    dsimp [q0]
    lia
  have hfg : ((F.natTail k).submodule).FG := by
    apply F.natTail_submodule_fg_of_stable_ge k q0
    · intro q hq
      apply hstable (k + (q : ℤ))
      calc
        c = k + (q0 : ℤ) := hq0.symm
        _ ≤ k + (q : ℤ) := by lia
    · intro q hq
      apply hstage (k + (q : ℤ))
      calc
        k + (q : ℤ) ≤ k + (q0 : ℤ) := by lia
        _ = c := hq0
  exact F.finite_of_fg_natTail k hfg (F.subsingleton_gradedPiece_of_lt_of_top k hk)

end Ideal.IntFiltration
