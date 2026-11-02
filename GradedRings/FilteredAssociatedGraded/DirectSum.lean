/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GradedRings.FilteredAssociatedGraded.Map
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.LinearAlgebra.Pi

/-!
# Associated graded modules of dependent direct sums

An arbitrary dependent direct sum of integer filtered modules has the componentwise
filtration on its finitely supported elements. Its associated graded module is the
direct sum of the associated graded modules, over the quotient Rees ring.

The comparison is the inverse of the linear map assembled from the filtered summand
inclusions. Thus it preserves the summand, the absolute integer degree, and the original
homogeneous representative. No common lower bound for the filtrations is needed.

The construction uses Mathlib's direct-sum universal property and the existing maps of
associated graded modules. Individual homogeneous pieces remain modules over the
original ring; only the whole associated graded modules carry the quotient Rees action.
-/

@[expose] public section

open scoped DirectSum

namespace Ideal.IntFiltration

universe uR uι uM uN

variable {R : Type uR} [CommRing R] {I : Ideal R}
  {ι : Type uι} {M : ι → Type uM}
  [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]

noncomputable section

attribute [local instance] Classical.propDecidable

local notation "C" => (reesAlgebra I) ⧸ I.map (algebraMap R (reesAlgebra I))

/-- The componentwise integer filtration on the original dependent direct sum. -/
def directSum (F : ∀ i, I.IntFiltration (M i)) :
    I.IntFiltration (⨁ i, M i) := by
  refine ⟨fun n =>
    (Submodule.pi Set.univ (fun i => (F i).N n)).comap
      (DirectSum.coeFnLinearMap R), ?_, ?_⟩
  · intro n m hnm x hx
    have hx' : ∀ i, x i ∈ (F i).N m := by
      simpa only [Submodule.mem_comap, Submodule.mem_pi,
        DirectSum.coeFnLinearMap_apply, Set.mem_univ, forall_const] using hx
    simpa only [Submodule.mem_comap, Submodule.mem_pi,
      DirectSum.coeFnLinearMap_apply, Set.mem_univ, forall_const] using
      (fun i => (F i).antitone hnm (hx' i))
  · intro n
    rw [Submodule.smul_le]
    intro a ha x hx
    have hx' : ∀ i, x i ∈ (F i).N n := by
      simpa only [Submodule.mem_comap, Submodule.mem_pi,
        DirectSum.coeFnLinearMap_apply, Set.mem_univ, forall_const] using hx
    change DirectSum.coeFnLinearMap R (a • x) ∈
      Submodule.pi Set.univ (fun i => (F i).N (n + 1))
    rw [_root_.map_smul]
    apply Submodule.mem_pi.mpr
    intro i _
    exact (F i).smul_le n (Submodule.smul_mem_smul ha (hx' i))

/-- Membership in a direct-sum filtration is membership in every component stage. -/
@[simp]
theorem mem_directSum (F : ∀ i, I.IntFiltration (M i))
    (n : ℤ) (x : ⨁ i, M i) :
    x ∈ (directSum F).N n ↔ ∀ i, x i ∈ (F i).N n := by
  simp only [directSum, Submodule.mem_comap, Submodule.mem_pi,
    DirectSum.coeFnLinearMap_apply, Set.mem_univ, forall_const]

private theorem directSum_lof_mem (F : ∀ i, I.IntFiltration (M i)) (i : ι)
    (n : ℤ) :
    (F i).N n ≤ ((directSum F).N n).comap (DirectSum.lof R ι M i) := by
  intro x hx
  apply (mem_directSum F n _).2
  intro j
  change DirectSum.component R ι M j (DirectSum.lof R ι M i x) ∈ (F j).N n
  by_cases hij : i = j
  · subst j
    simpa only [DirectSum.component.lof_self] using hx
  · rw [DirectSum.component.of, dite_eq_right hij]
    exact ((F j).N n).zero_mem

private theorem directSum_component_mem (F : ∀ i, I.IntFiltration (M i))
    (i : ι) (n : ℤ) :
    (directSum F).N n ≤ ((F i).N n).comap (DirectSum.component R ι M i) := by
  intro x hx
  change DirectSum.component R ι M i x ∈ (F i).N n
  simpa only [← DirectSum.apply_eq_component] using (mem_directSum F n x).1 hx i

private def directSumInclusion (F : ∀ i, I.IntFiltration (M i)) (i : ι) :
    (F i).AssociatedGraded →ₗ[C] (directSum F).AssociatedGraded :=
  (F i).map (directSum F) (DirectSum.lof R ι M i) (directSum_lof_mem F i)

private def directSumProjection (F : ∀ i, I.IntFiltration (M i)) (i : ι) :
    (directSum F).AssociatedGraded →ₗ[C] (F i).AssociatedGraded :=
  (directSum F).map (F i) (DirectSum.component R ι M i)
    (directSum_component_mem F i)

private def directSumAssembly (F : ∀ i, I.IntFiltration (M i)) :
    (⨁ i, (F i).AssociatedGraded) →ₗ[C] (directSum F).AssociatedGraded :=
  DirectSum.toModule C ι (directSum F).AssociatedGraded (directSumInclusion F)

private theorem directSumProjection_inclusion
    (F : ∀ i, I.IntFiltration (M i)) (i j : ι) (z : (F j).AssociatedGraded) :
    directSumProjection F i (directSumInclusion F j z) =
      DirectSum.component C ι (fun k => (F k).AssociatedGraded) i
        (DirectSum.lof C ι (fun k => (F k).AssociatedGraded) j z) := by
  induction z using DirectSum.induction_on with
  | zero =>
    change directSumProjection F i (directSumInclusion F j 0) =
      DirectSum.component C ι (fun k => (F k).AssociatedGraded) i
        (DirectSum.lof C ι (fun k => (F k).AssociatedGraded) j 0)
    simp only [_root_.map_zero]
  | add x y hx hy =>
    change (F j).AssociatedGraded at x y
    change directSumProjection F i (directSumInclusion F j (x + y)) =
      DirectSum.component C ι (fun k => (F k).AssociatedGraded) i
        (DirectSum.lof C ι (fun k => (F k).AssociatedGraded) j (x + y))
    simp only [_root_.map_add, hx, hy]
  | of n q =>
    obtain ⟨x, rfl⟩ := (F j).cl_surjective n q
    change directSumProjection F i (directSumInclusion F j ((F j).single n x)) =
      DirectSum.component C ι (fun k => (F k).AssociatedGraded) i
        (DirectSum.lof C ι (fun k => (F k).AssociatedGraded) j ((F j).single n x))
    by_cases hji : j = i
    · subst j
      simp only [directSumInclusion, directSumProjection, map_single,
        DirectSum.component.lof_self]
    · simp only [directSumInclusion, directSumProjection, map_single,
        DirectSum.component.of, dite_eq_right hji]
      change (F i).single n 0 = 0
      exact _root_.map_zero ((F i).single n)

private theorem directSumProjection_comp_assembly
    (F : ∀ i, I.IntFiltration (M i)) (i : ι) :
    (directSumProjection F i).comp (directSumAssembly F) =
      DirectSum.component C ι (fun j => (F j).AssociatedGraded) i := by
  apply DirectSum.linearMap_ext
  intro j
  apply LinearMap.ext
  intro z
  change directSumProjection F i
      (directSumAssembly F (DirectSum.lof C ι (fun k => (F k).AssociatedGraded) j z)) = _
  rw [directSumAssembly, DirectSum.toModule_lof]
  exact directSumProjection_inclusion F i j z

private theorem directSumAssembly_injective
    (F : ∀ i, I.IntFiltration (M i)) :
    Function.Injective (directSumAssembly F) := by
  intro x y hxy
  apply (DirectSum.ext_component_iff C).mpr
  intro i
  have hi := congrArg (directSumProjection F i) hxy
  change ((directSumProjection F i).comp (directSumAssembly F)) x =
    ((directSumProjection F i).comp (directSumAssembly F)) y at hi
  simpa only [directSumProjection_comp_assembly] using hi

private theorem directSumAssembly_surjective
    (F : ∀ i, I.IntFiltration (M i)) :
    Function.Surjective (directSumAssembly F) := by
  classical
  -- First lift one homogeneous original representative, using its finite support.
  have hhom (n : ℤ) (x : (directSum F).N n) :
      ∃ y : ⨁ i, (F i).AssociatedGraded,
        directSumAssembly F y = (directSum F).single n x := by
    let r : ∀ i, (F i).N n := fun i =>
      ⟨(x : ⨁ i, M i) i, (mem_directSum F n _).1 x.property i⟩
    let s : ι → (directSum F).N n := fun i =>
      ⟨DirectSum.lof R ι M i (r i : M i), directSum_lof_mem F i n (r i).property⟩
    have hsplit : (∑ i ∈ (x : ⨁ i, M i).support, s i) = x := by
      apply Subtype.ext
      change ((directSum F).N n).subtype
          (∑ i ∈ (x : ⨁ i, M i).support, s i) = (x : ⨁ i, M i)
      rw [_root_.map_sum]
      change (x : ⨁ i, M i).sum DFinsupp.single = (x : ⨁ i, M i)
      exact DFinsupp.sum_single
    refine ⟨∑ i ∈ (x : ⨁ i, M i).support,
      DirectSum.lof C ι (fun i => (F i).AssociatedGraded) i ((F i).single n (r i)), ?_⟩
    calc
      directSumAssembly F
          (∑ i ∈ (x : ⨁ i, M i).support,
            DirectSum.lof C ι (fun i => (F i).AssociatedGraded) i
              ((F i).single n (r i))) =
          ∑ i ∈ (x : ⨁ i, M i).support,
            directSumInclusion F i ((F i).single n (r i)) := by
        simp only [_root_.map_sum, directSumAssembly, DirectSum.toModule_lof]
      _ = ∑ i ∈ (x : ⨁ i, M i).support, (directSum F).single n (s i) := by
        apply Finset.sum_congr rfl
        intro i _
        simp only [directSumInclusion, map_single]
        rfl
      _ = (directSum F).single n
          (∑ i ∈ (x : ⨁ i, M i).support, s i) := by rw [_root_.map_sum]
      _ = (directSum F).single n x := congrArg ((directSum F).single n) hsplit
  intro z
  -- A graded element is represented by a finite family of original stage elements.
  obtain ⟨w, hw⟩ := (directSum F).quotientMap_surjective z
  let y (n : ℤ) : ⨁ i, (F i).AssociatedGraded := Classical.choose (hhom n (w n))
  have hy (n : ℤ) :
      directSumAssembly F (y n) = (directSum F).single n (w n) :=
    Classical.choose_spec (hhom n (w n))
  refine ⟨∑ n ∈ w.support, y n, ?_⟩
  calc
    directSumAssembly F (∑ n ∈ w.support, y n) =
        ∑ n ∈ w.support, (directSum F).single n (w n) := by
      simp only [_root_.map_sum, hy]
    _ = (directSum F).quotientMap
        (∑ n ∈ w.support,
          DirectSum.lof R ℤ (fun n => (directSum F).N n) n (w n)) := by
      simp only [_root_.map_sum, quotientMap_lof]
    _ = (directSum F).quotientMap w := by
      apply congrArg (directSum F).quotientMap
      change w.sum DFinsupp.single = w
      exact DFinsupp.sum_single
    _ = z := hw

/-- The associated graded module of a dependent direct sum is the direct sum of the
associated graded modules, over the quotient Rees ring.

Its forward function is the inverse function of the assembly map of filtered summand
inclusions; its inverse is that assembly map. -/
@[no_expose]
def directSumEquiv (F : ∀ i, I.IntFiltration (M i)) :
    (directSum F).AssociatedGraded ≃ₗ[C] (⨁ i, (F i).AssociatedGraded) where
  toFun := Function.invFun (directSumAssembly F)
  invFun := directSumAssembly F
  left_inv := Function.rightInverse_invFun (directSumAssembly_surjective F)
  right_inv := Function.leftInverse_invFun (directSumAssembly_injective F)
  map_add' := by
    intro x y
    apply directSumAssembly_injective F
    rw [_root_.map_add]
    have hL := Function.rightInverse_invFun (directSumAssembly_surjective F)
    exact (hL (x + y)).trans (congrArg₂ (· + ·) (hL x).symm (hL y).symm)
  map_smul' := by
    intro c x
    change Function.invFun (directSumAssembly F) (c • x) =
      c • Function.invFun (directSumAssembly F) x
    apply directSumAssembly_injective F
    rw [_root_.map_smul]
    have hL := Function.rightInverse_invFun (directSumAssembly_surjective F)
    exact (hL (c • x)).trans (congrArg (fun y => c • y) (hL x).symm)

/-- The inverse comparison on an arbitrary finitely supported family is the canonical
linear map assembled from the filtered summand inclusions. -/
theorem directSumEquiv_symm_apply (F : ∀ i, I.IntFiltration (M i))
    (y : ⨁ i, (F i).AssociatedGraded) :
    (directSumEquiv F).symm y =
      DirectSum.toModule C ι (directSum F).AssociatedGraded
        (fun i => (F i).map (directSum F) (DirectSum.lof R ι M i)
          (by exact directSum_lof_mem F i)) y := by
  rfl

/-- Every coordinate of the direct-sum comparison is the associated graded map of the
original component projection. -/
@[simp]
theorem directSumEquiv_apply (F : ∀ i, I.IntFiltration (M i))
    (z : (directSum F).AssociatedGraded) (i : ι) :
    (directSumEquiv F z) i =
      ((directSum F).map (F i) (DirectSum.component R ι M i)
        (by exact directSum_component_mem F i)) z := by
  have hz : directSumAssembly F (directSumEquiv F z) = z :=
    (directSumEquiv F).symm_apply_apply z
  have hi := congrArg (directSumProjection F i) hz
  change ((directSumProjection F i).comp (directSumAssembly F)) (directSumEquiv F z) =
    directSumProjection F i z at hi
  rw [directSumProjection_comp_assembly] at hi
  simpa only [← DirectSum.apply_eq_component, directSumProjection] using hi

/-- A homogeneous representative supported in one summand retains the same summand,
absolute integer degree, and original representative under the comparison. -/
@[simp]
theorem directSumEquiv_single (F : ∀ i, I.IntFiltration (M i))
    (i : ι) (n : ℤ) (x : (F i).N n) :
    directSumEquiv F
        ((directSum F).single n
          ⟨DirectSum.lof R ι M i (x : M i),
            by exact directSum_lof_mem F i n x.property⟩) =
      DirectSum.lof C ι (fun j => (F j).AssociatedGraded) i ((F i).single n x) := by
  apply (directSumEquiv F).symm.injective
  rw [LinearEquiv.symm_apply_apply, directSumEquiv_symm_apply,
    DirectSum.toModule_lof, map_single]

variable {N : ι → Type uN}
  [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]

private theorem directSum_lmap_mem
    (F : ∀ i, I.IntFiltration (M i)) (H : ∀ i, I.IntFiltration (N i))
    (f : ∀ i, M i →ₗ[R] N i)
    (hf : ∀ i n, (F i).N n ≤ ((H i).N n).comap (f i)) (n : ℤ) :
    (directSum F).N n ≤ ((directSum H).N n).comap (DirectSum.lmap f) := by
  intro x hx
  change DirectSum.lmap f x ∈ (directSum H).N n
  apply (mem_directSum H n _).2
  intro i
  have hi := hf i n ((mem_directSum F n x).1 hx i)
  change f i (x i) ∈ (H i).N n at hi
  simpa only [DirectSum.lmap_apply] using hi

/-- The comparison commutes with every family of original linear maps preserving
all integer filtration stages. Both sides are linear over the quotient Rees ring. -/
theorem directSumEquiv_naturality
    (F : ∀ i, I.IntFiltration (M i)) (H : ∀ i, I.IntFiltration (N i))
    (f : ∀ i, M i →ₗ[R] N i)
    (hf : ∀ i n, (F i).N n ≤ ((H i).N n).comap (f i)) :
    (directSumEquiv H).toLinearMap.comp
        ((directSum F).map (directSum H) (DirectSum.lmap f)
          (by exact directSum_lmap_mem F H f hf)) =
      (DirectSum.lmap (fun i => (F i).map (H i) (f i) (hf i))).comp
        (directSumEquiv F).toLinearMap := by
  have hcoord (i : ι) :
      (directSumProjection H i).comp
          ((directSum F).map (directSum H) (DirectSum.lmap f)
            (directSum_lmap_mem F H f hf)) =
        ((F i).map (H i) (f i) (hf i)).comp (directSumProjection F i) := by
    rw [directSumProjection, directSumProjection, ← map_comp, ← map_comp]
    congr 1
  apply LinearMap.ext
  intro z
  apply (DirectSum.ext_component_iff C).mpr
  intro i
  change (directSumEquiv H
      (((directSum F).map (directSum H) (DirectSum.lmap f)
        (directSum_lmap_mem F H f hf)) z)) i =
    (DirectSum.lmap (fun j => (F j).map (H j) (f j) (hf j))
      (directSumEquiv F z)) i
  rw [DirectSum.lmap_apply, directSumEquiv_apply, directSumEquiv_apply]
  simpa only [LinearMap.comp_apply, directSumProjection] using
    congrArg (fun q => q z) (hcoord i)

end

end Ideal.IntFiltration
