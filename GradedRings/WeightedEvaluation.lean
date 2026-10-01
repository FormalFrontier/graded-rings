/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GradedRings.HomogeneousLifts
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-!
# Weighted evaluation into a graded ring

Evaluation of a weighted multivariate polynomial at homogeneous elements of the
specified degrees preserves weighted degree. The coefficients are the *actual*
degree-zero ring of the target grading.
-/

@[expose] public section

namespace MvPolynomial

variable {ι S σ : Type*} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮] (w : ι → ℕ) (x : ∀ i : ι, 𝒮 (w i))

private theorem weightedAeval_monomial_mem (d : ι →₀ ℕ) (r : 𝒮 0) :
    aeval (fun i => (x i : S)) (monomial d r) ∈ 𝒮 (Finsupp.weight w d) := by
  classical
  have hprod : (∏ i ∈ d.support, (x i : S) ^ d i) ∈
      𝒮 (∑ i ∈ d.support, d i • w i) :=
    SetLike.prod_pow_mem_graded 𝒮 w (fun i => (x i : S)) d
      (fun i _ => (x i).property)
  rw [aeval_monomial, Finsupp.prod, Finsupp.weight_apply,
    SetLike.GradeZero.algebraMap_apply]
  simpa only [Finsupp.sum, zero_add] using
    (SetLike.GradedMul.mul_mem (show (r : S) ∈ 𝒮 0 from r.property) hprod :
      (r : S) * (∏ i ∈ d.support, (x i : S) ^ d i) ∈
        𝒮 (0 + ∑ i ∈ d.support, d i • w i))

/-- Evaluation at homogeneous elements of specified weights preserves weighted degree. -/
theorem IsWeightedHomogeneous.aeval_mem {n : ℕ} {p : MvPolynomial ι (𝒮 0)}
    (hp : p.IsWeightedHomogeneous w n) :
    aeval (fun i => (x i : S)) p ∈ 𝒮 n := by
  classical
  rw [← p.support_sum_monomial_coeff, map_sum]
  apply sum_mem
  intro d hd
  simpa only [hp (mem_support_iff.mp hd)] using
    weightedAeval_monomial_mem 𝒮 w x d (p.coeff d)

/-- Ordinary polynomial evaluation, bundled as a degree-preserving ring map. -/
noncomputable def weightedAevalGradedHom :
    (weightedHomogeneousSubmodule (𝒮 0) w) →+*ᵍ 𝒮 := by
  let _ : GradedAlgebra (weightedHomogeneousSubmodule (𝒮 0) w) :=
    weightedGradedAlgebra (𝒮 0) w
  exact { (aeval (fun i => (x i : S))).toRingHom with
    map_mem := fun hp => hp.aeval_mem 𝒮 w x }

/-- Weighted polynomial components evaluate to the corresponding target component. -/
theorem aeval_weightedHomogeneousComponent (n : ℕ) (p : MvPolynomial ι (𝒮 0)) :
    aeval (fun i => (x i : S)) (weightedHomogeneousComponent w n p) =
      (DirectSum.decompose 𝒮 (aeval (fun i => (x i : S)) p) n : S) := by
  classical
  let _ : GradedAlgebra (weightedHomogeneousSubmodule (𝒮 0) w) :=
    weightedGradedAlgebra (𝒮 0) w
  have h := (weightedAevalGradedHom 𝒮 w x).map_directSumDecompose
    (x := p) (i := n)
  have hcomponent : (DirectSum.decompose (weightedHomogeneousSubmodule (𝒮 0) w) p n :
      MvPolynomial ι (𝒮 0)) = weightedHomogeneousComponent w n p := by
    exact weightedDecomposition.decompose'_apply (𝒮 0) w p n
  rw [hcomponent] at h
  exact h

/-- A generating homogeneous family admits weighted-homogeneous lifts in every degree. -/
theorem exists_isWeightedHomogeneous_aeval
    (hgen : Algebra.adjoin (𝒮 0) (Set.range (fun i => (x i : S))) = ⊤)
    {n : ℕ} {s : S} (hs : s ∈ 𝒮 n) :
    ∃ p : MvPolynomial ι (𝒮 0), p.IsWeightedHomogeneous w n ∧
      aeval (fun i => (x i : S)) p = s := by
  let _ : GradedAlgebra (weightedHomogeneousSubmodule (𝒮 0) w) :=
    weightedGradedAlgebra (𝒮 0) w
  have hsurj : Function.Surjective (aeval (fun i => (x i : S)) :
      MvPolynomial ι (𝒮 0) →ₐ[𝒮 0] S) := by
    rw [← AlgHom.range_eq_top, aeval_range]
    exact hgen
  obtain ⟨p, hp⟩ := GradedRingHom.surjective_gradedAddHom
    (weightedHomogeneousSubmodule (𝒮 0) w) 𝒮
    (weightedAevalGradedHom 𝒮 w x) hsurj n ⟨s, hs⟩
  exact ⟨p, p.property, congrArg Subtype.val hp⟩

end MvPolynomial
