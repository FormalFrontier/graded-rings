/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.Ideal.Operations

/-!
# Associated graded modules of integer filtrations

An `Ideal.IntFiltration I M` is an antitone family of submodules of the original
`R`-module `M`, with `I • N n ≤ N (n + 1)` in every integer degree. Its graded
piece is the quotient of `N n` by the next stage, pulled back along the subtype
map. The associated graded module is the external direct sum of these pieces,
with its componentwise `R`-module structure.

Pullback and image along original-`R`-linear maps preserve ideal compatibility.
Their stages satisfy the usual image–preimage universal property, and the
constructed filtration data respect identities and composition.

The representative map from the direct sum of the stages is surjective. Its
kernel consists of the families whose coefficients belong to the next stages;
the first isomorphism theorem identifies its quotient with the associated graded.

## Implementation notes

This file constructs the carrier and its original-scalar representative API.
The action of the quotient Rees algebra is not constructed here. No finiteness,
exhaustivity, separatedness or boundedness assumption is used.

## References

* K. Fujiwara and F. Kato, *Foundations of Rigid Geometry I*, arXiv:1308.4734v5,
  Chapter 0, §7.5, for integer-indexed associated graded modules.
* Andrew Yang's `Ideal.Filtration` in Mathlib for compatible ideal filtrations.
* Mathlib's direct sums of modules and submodule quotient isomorphisms supply
  the finite-support and quotient constructions used here.
-/

@[expose] public section

universe u v w x

open scoped DirectSum

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- A descending integer-indexed filtration compatible with multiplication by `I`. -/
structure Ideal.IntFiltration (M : Type v) [AddCommGroup M] [Module R M] where
  /-- The submodule in each absolute integer degree. -/
  N : ℤ → Submodule R M
  /-- Higher stages are contained in lower stages. -/
  antitone : Antitone N
  /-- Multiplication by `I` raises the degree by one. -/
  smul_le : ∀ n : ℤ, I • N n ≤ N (n + 1)

namespace Ideal.IntFiltration

variable {I} {M : Type v} [AddCommGroup M] [Module R M]

/-- Filtrations are equal when all their stages agree. -/
@[ext]
theorem ext {F F' : I.IntFiltration M} (h : ∀ n, F.N n = F'.N n) : F = F' := by
  cases F
  cases F'
  congr
  exact funext h

/-- The constructor preserves the supplied stage family. -/
@[simp]
theorem mk_N (N : ℤ → Submodule R M) (hN : Antitone N)
    (hI : ∀ n : ℤ, I • N n ≤ N (n + 1)) :
    (IntFiltration.mk N hN hI).N = N := rfl

section Products

variable {N : Type w} [AddCommGroup N] [Module R N]
variable (F : I.IntFiltration M) (H : I.IntFiltration N)

/-- The product filtration on the original product module. -/
def prod : I.IntFiltration (M × N) where
  N := fun n => (F.N n).prod (H.N n)
  antitone := fun _ _ h => Submodule.prod_mono (F.antitone h) (H.antitone h)
  smul_le := fun n => Submodule.smul_le.mpr (fun _ hr _ hp =>
    ⟨F.smul_le n (Submodule.smul_mem_smul hr hp.1),
      H.smul_le n (Submodule.smul_mem_smul hr hp.2)⟩)

/-- Each stage of the product filtration is the product of the two stages. -/
@[simp]
theorem prod_N (n : ℤ) : (F.prod H).N n = (F.N n).prod (H.N n) := by
  rfl

/-- Membership in a product stage is membership of both original coordinates. -/
theorem mem_prod (n : ℤ) (p : M × N) :
    p ∈ (F.prod H).N n ↔ p.1 ∈ F.N n ∧ p.2 ∈ H.N n := by
  rfl

end Products

section Transport

variable {N : Type w} [AddCommGroup N] [Module R N]
variable {P : Type x} [AddCommGroup P] [Module R P]

/-- The pullback of an integer filtration along an original-linear map. -/
def comap (H : I.IntFiltration N) (f : M →ₗ[R] N) : I.IntFiltration M where
  N := fun n => (H.N n).comap f
  antitone := fun _ _ h => Submodule.comap_mono (H.antitone h)
  smul_le := fun n =>
    (Submodule.smul_comap_le_comap_smul f (H.N n) I).trans
      (Submodule.comap_mono (H.smul_le n))

/-- The image of an integer filtration under an original-linear map. -/
def image (F : I.IntFiltration M) (f : M →ₗ[R] N) : I.IntFiltration N where
  N := fun n => (F.N n).map f
  antitone := fun _ _ h => Submodule.map_mono (F.antitone h)
  smul_le := fun n =>
    (Submodule.map_smul'' I (F.N n) f).ge.trans
      (Submodule.map_mono (F.smul_le n))

/-- A pullback stage is the inverse image of the corresponding target stage. -/
@[simp]
theorem comap_N (H : I.IntFiltration N) (f : M →ₗ[R] N) (n : ℤ) :
    (H.comap f).N n = (H.N n).comap f := by
  rfl

/-- An image stage is the direct image of the corresponding source stage. -/
@[simp]
theorem image_N (F : I.IntFiltration M) (f : M →ₗ[R] N) (n : ℤ) :
    (F.image f).N n = (F.N n).map f := by
  rfl

/-- Pullback-stage membership is target-stage membership after applying the map. -/
theorem mem_comap (H : I.IntFiltration N) (f : M →ₗ[R] N) (n : ℤ) (m : M) :
    m ∈ (H.comap f).N n ↔ f m ∈ H.N n := by
  simp only [comap_N, Submodule.mem_comap]

/-- Image-stage membership means having a representative in the source stage. -/
theorem mem_image (F : I.IntFiltration M) (f : M →ₗ[R] N) (n : ℤ) (y : N) :
    y ∈ (F.image f).N n ↔ ∃ m : M, m ∈ F.N n ∧ f m = y := by
  simp only [image_N, Submodule.mem_map]

/-- Pullback along the identity leaves the filtration unchanged. -/
@[simp]
theorem comap_id (F : I.IntFiltration M) :
    F.comap (LinearMap.id : M →ₗ[R] M) = F := by
  apply ext
  intro n
  simpa only [comap_N] using Submodule.comap_id (F.N n)

/-- Image under the identity leaves the filtration unchanged. -/
@[simp]
theorem image_id (F : I.IntFiltration M) :
    F.image (LinearMap.id : M →ₗ[R] M) = F := by
  apply ext
  intro n
  simpa only [image_N] using Submodule.map_id (F.N n)

/-- Pullback reverses composition of original-linear maps. -/
theorem comap_comp (K : I.IntFiltration P) (f : M →ₗ[R] N) (g : N →ₗ[R] P) :
    K.comap (g.comp f) = (K.comap g).comap f := by
  apply ext
  intro n
  simpa only [comap_N] using Submodule.comap_comp f g (K.N n)

/-- Taking images preserves composition of original-linear maps. -/
theorem image_comp (F : I.IntFiltration M) (f : M →ₗ[R] N) (g : N →ₗ[R] P) :
    F.image (g.comp f) = (F.image f).image g := by
  apply ext
  intro n
  simpa only [image_N] using Submodule.map_comp f g (F.N n)

/-- Stagewise image containment is equivalent to stagewise pullback containment. -/
theorem image_le_iff_le_comap (F : I.IntFiltration M) (H : I.IntFiltration N)
    (f : M →ₗ[R] N) :
    (∀ n : ℤ, (F.image f).N n ≤ H.N n) ↔
      ∀ n : ℤ, F.N n ≤ (H.comap f).N n := by
  simp only [image_N, comap_N, Submodule.map_le_iff_le_comap]

end Transport

variable (F : I.IntFiltration M)

/-- Every natural ideal power raises the absolute integer degree by its exponent. -/
theorem pow_smul_le (q : ℕ) (n : ℤ) : I ^ q • F.N n ≤ F.N (n + (q : ℤ)) := by
  let G : I.Filtration M :=
    { N := fun t => F.N (n + (t : ℤ))
      mono := fun t => F.antitone (by lia)
      smul_le := fun t => by
        simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using
          F.smul_le (n + (t : ℤ)) }
  simpa [G] using G.pow_smul_le q 0

/-- The next stage viewed as a submodule of the current stage. -/
def nextStage (n : ℤ) : Submodule R (F.N n) :=
  (F.N (n + 1)).comap (F.N n).subtype

/-- Membership in the denominator is membership in the next original stage. -/
@[simp]
theorem mem_nextStage (n : ℤ) (m : F.N n) :
    m ∈ F.nextStage n ↔ (m : M) ∈ F.N (n + 1) := Iff.rfl

/-- The associated graded piece in absolute integer degree `n`. -/
def GradedPiece (n : ℤ) : Type v := (F.N n) ⧸ F.nextStage n

instance instAddCommGroupGradedPiece (n : ℤ) : AddCommGroup (F.GradedPiece n) :=
  inferInstanceAs (AddCommGroup ((F.N n) ⧸ F.nextStage n))

instance instModuleGradedPiece (n : ℤ) : Module R (F.GradedPiece n) :=
  inferInstanceAs (Module R ((F.N n) ⧸ F.nextStage n))

/-- The whole integer-graded module, with finite support in the absolute degrees. -/
def AssociatedGraded : Type v := ⨁ n : ℤ, F.GradedPiece n

instance instAddCommGroupAssociatedGraded : AddCommGroup F.AssociatedGraded :=
  inferInstanceAs (AddCommGroup (⨁ n : ℤ, F.GradedPiece n))

instance instModuleAssociatedGraded : Module R F.AssociatedGraded :=
  inferInstanceAs (Module R (⨁ n : ℤ, F.GradedPiece n))

/-- The quotient map from a stage to its graded piece. -/
def cl (n : ℤ) : F.N n →ₗ[R] F.GradedPiece n := (F.nextStage n).mkQ

/-- The stage quotient map sends a representative to its class. -/
theorem cl_apply (n : ℤ) (m : F.N n) : F.cl n m = Submodule.Quotient.mk m := rfl

/-- Every piece class has a representative in its original stage. -/
theorem cl_surjective (n : ℤ) : Function.Surjective (F.cl n) :=
  (F.nextStage n).mkQ_surjective

/-- The kernel of the stage quotient map is the next stage. -/
@[simp]
theorem ker_cl (n : ℤ) : LinearMap.ker (F.cl n) = F.nextStage n :=
  Submodule.ker_mkQ _

/-- A representative vanishes precisely when it lies in the next stage. -/
@[simp]
theorem cl_eq_zero_iff (n : ℤ) (m : F.N n) :
    F.cl n m = 0 ↔ (m : M) ∈ F.N (n + 1) :=
  Submodule.Quotient.mk_eq_zero _

/-- Two piece representatives agree precisely when their difference is in the next stage. -/
theorem cl_eq_cl_iff (n : ℤ) (m m' : F.N n) :
    F.cl n m = F.cl n m' ↔ (m : M) - (m' : M) ∈ F.N (n + 1) :=
  Submodule.Quotient.eq _

/-- Inclusion of a graded piece into the whole associated graded module. -/
def inclusion (n : ℤ) : F.GradedPiece n →ₗ[R] F.AssociatedGraded :=
  DirectSum.lof R ℤ F.GradedPiece n

/-- Projection to an absolute integer degree. -/
def component (n : ℤ) : F.AssociatedGraded →ₗ[R] F.GradedPiece n :=
  DirectSum.component R ℤ F.GradedPiece n

/-- Inserting and then projecting to the same degree recovers the piece. -/
@[simp]
theorem component_inclusion (n : ℤ) (z : F.GradedPiece n) :
    F.component n (F.inclusion n z) = z :=
  DirectSum.component.lof_self R n z

/-- An insertion has zero component in every other degree. -/
@[simp]
theorem component_inclusion_of_ne (n k : ℤ) (h : k ≠ n) (z : F.GradedPiece n) :
    F.component k (F.inclusion n z) = 0 :=
  DirectSum.of_eq_of_ne n k z h

/-- Each piece embeds in the direct sum. -/
theorem inclusion_injective (n : ℤ) : Function.Injective (F.inclusion n) :=
  DirectSum.of_injective (β := F.GradedPiece) n

/-- Insert a stage representative as its homogeneous class, not as an injective stage map. -/
def single (n : ℤ) : F.N n →ₗ[R] F.AssociatedGraded := (F.inclusion n).comp (F.cl n)

/-- Representative insertion factors through the corresponding piece quotient. -/
theorem single_apply (n : ℤ) (m : F.N n) :
    F.single n m = F.inclusion n (F.cl n m) := rfl

/-- The component of a representative insertion in its own degree is its quotient class. -/
@[simp]
theorem component_single (n : ℤ) (m : F.N n) :
    F.component n (F.single n m) = F.cl n m :=
  F.component_inclusion n (F.cl n m)

/-- A representative insertion has zero component in every other degree. -/
@[simp]
theorem component_single_of_ne (n k : ℤ) (h : k ≠ n) (m : F.N n) :
    F.component k (F.single n m) = 0 :=
  F.component_inclusion_of_ne n k h (F.cl n m)

/-- A homogeneous representative insertion vanishes exactly in the next stage. -/
@[simp]
theorem single_eq_zero_iff (n : ℤ) (m : F.N n) :
    F.single n m = 0 ↔ (m : M) ∈ F.N (n + 1) := by
  rw [single_apply, ← map_zero (F.inclusion n), (F.inclusion_injective n).eq_iff,
    cl_eq_zero_iff]

/-- Equality in the whole associated graded module can be checked componentwise. -/
@[ext]
theorem associatedGraded_ext {x y : F.AssociatedGraded}
    (h : ∀ n, F.component n x = F.component n y) : x = y :=
  DirectSum.ext_component R h

/-- Every coefficient in `I` annihilates the associated graded module. -/
theorem smul_eq_zero_of_mem {r : R} (hr : r ∈ I) (x : F.AssociatedGraded) :
    r • x = 0 := by
  apply F.associatedGraded_ext
  intro n
  rw [map_smul, map_zero]
  obtain ⟨m, hm⟩ := F.cl_surjective n (F.component n x)
  rw [← hm, ← map_smul]
  exact (F.cl_eq_zero_iff n (r • m)).2
    (F.smul_le n (Submodule.smul_mem_smul hr m.property))

variable {T : Type w} [AddCommMonoid T] [Module R T]

/-- The linear map from the associated graded specified on each graded piece. -/
def lift (f : ∀ n, F.GradedPiece n →ₗ[R] T) : F.AssociatedGraded →ₗ[R] T :=
  DirectSum.toModule R ℤ T f

/-- The map specified on pieces has the specified value on each inclusion. -/
@[simp]
theorem lift_inclusion (f : ∀ n, F.GradedPiece n →ₗ[R] T) (n : ℤ) (z : F.GradedPiece n) :
    F.lift f (F.inclusion n z) = f n z := DirectSum.toModule_lof R n z

/-- Agreement on every homogeneous stage representative determines a linear map. -/
theorem linearMap_ext {f g : F.AssociatedGraded →ₗ[R] T}
    (h : ∀ n m, f (F.single n m) = g (F.single n m)) : f = g := by
  apply DirectSum.linearMap_ext
  intro n
  apply LinearMap.ext
  intro z
  obtain ⟨m, rfl⟩ := F.cl_surjective n z
  exact h n m

/-- The nonzero components of an element form a finite set. -/
theorem finite_support (x : F.AssociatedGraded) :
    Set.Finite {n | F.component n x ≠ 0} := DFinsupp.finite_support x

/-- The finite set of nonzero absolute-degree components. -/
noncomputable def support (x : F.AssociatedGraded) : Finset ℤ := by
  classical
  exact x.support

/-- A degree belongs to the support precisely when its component is nonzero. -/
@[simp]
theorem mem_support_iff (x : F.AssociatedGraded) (n : ℤ) :
    n ∈ F.support x ↔ F.component n x ≠ 0 := by
  classical
  exact DFinsupp.mem_support_iff

/-- Reconstruction from the finitely many nonzero components. -/
theorem sum_support_inclusion (x : F.AssociatedGraded) :
    ∑ n ∈ F.support x, F.inclusion n (F.component n x) = x := by
  classical
  exact DirectSum.sum_support_of x

/-- The coefficientwise map from stage representatives to the associated graded. -/
def quotientMap : (⨁ n : ℤ, F.N n) →ₗ[R] F.AssociatedGraded :=
  DirectSum.lmap (fun n => F.cl n)

/-- Each component of the representative map is the corresponding piece quotient. -/
@[simp]
theorem component_quotientMap (x : ⨁ n : ℤ, F.N n) (n : ℤ) :
    F.component n (F.quotientMap x) = F.cl n (x n) := rfl

/-- A single stage coefficient maps to its homogeneous class. -/
@[simp]
theorem quotientMap_lof (n : ℤ) (m : F.N n) :
    F.quotientMap (DirectSum.lof R ℤ (fun n => F.N n) n m) = F.single n m :=
  DirectSum.lmap_lof (fun n => F.cl n) n m

/-- Every element has a finitely supported family of stage representatives. -/
theorem quotientMap_surjective : Function.Surjective F.quotientMap :=
  (DirectSum.lmap_surjective (fun n => F.cl n)).mpr F.cl_surjective

/-- Families of stage representatives lying coefficientwise in the next stages. -/
def representativeKernel : Submodule R (⨁ n : ℤ, F.N n) :=
  (Submodule.pi Set.univ (fun n => F.nextStage n)).comap (DirectSum.coeFnLinearMap R)

/-- Kernel membership is the next-stage condition in every absolute degree. -/
@[simp]
theorem mem_representativeKernel (x : ⨁ n : ℤ, F.N n) :
    x ∈ F.representativeKernel ↔ ∀ n, (x n : M) ∈ F.N (n + 1) := by
  simp [representativeKernel]

/-- A family of representatives maps to zero exactly when every coefficient is in the next stage. -/
@[simp]
theorem quotientMap_eq_zero_iff (x : ⨁ n : ℤ, F.N n) :
    F.quotientMap x = 0 ↔ ∀ n, (x n : M) ∈ F.N (n + 1) := by
  rw [F.associatedGraded_ext_iff]
  simp only [component_quotientMap, map_zero, cl_eq_zero_iff]

/-- The kernel of the representative map is the coefficientwise next-stage submodule. -/
theorem ker_quotientMap : LinearMap.ker F.quotientMap = F.representativeKernel := by
  ext x
  rw [LinearMap.mem_ker, quotientMap_eq_zero_iff, mem_representativeKernel]

/-- The first-isomorphism comparison from the quotient of all stage representatives. -/
noncomputable def quotientEquiv :
    ((⨁ n : ℤ, F.N n) ⧸ F.representativeKernel) ≃ₗ[R] F.AssociatedGraded :=
  (Submodule.quotEquivOfEq _ _ F.ker_quotientMap.symm).trans
    (F.quotientMap.quotKerEquivOfSurjective F.quotientMap_surjective)

/-- The first-isomorphism comparison computes by taking every coefficient class. -/
@[simp]
theorem quotientEquiv_mk (x : ⨁ n : ℤ, F.N n) :
    F.quotientEquiv (Submodule.Quotient.mk x) = F.quotientMap x := rfl

end Ideal.IntFiltration
