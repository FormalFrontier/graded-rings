/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GradedRings.FilteredAssociatedGraded
public import GradedRings.ReesAlgebra.Grading
public import Mathlib.Algebra.Module.RingHom

/-!
# The quotient Rees action on an integer-filtered associated graded module

Multiplication by an element of `I ^ q` carries a filtration stage in degree `n`
to degree `n + q`. It carries the next stage into the next stage there, so it
induces an original-`R`-linear endomorphism of the whole associated graded module.
These operators are linear in the coefficient, compose by multiplication, and
vanish when the coefficient belongs to the next ideal power.

The quotient Rees representation has source exactly the canonical Rees algebra
modulo the extension of `I`. Its evaluation action retains the original
componentwise `R`-module and sends homogeneous representatives to their products
in degree `n + q`. No finiteness, exhaustivity, separatedness or lower bound is
required, and the coefficient ring and module have independent universes.

## Implementation notes

The private maps implement the homogeneous ideal-power operators. Their
extension uses `DirectSum.toSemiring` and the coefficient decomposition of the
Rees algebra. Degree-zero scalar agreement and annihilation by `I` kill the
extended ideal, so the quotient universal property gives the representation.
This construction does not require identifying the quotient components with
quotients of consecutive ideal powers.

## References

* K. Fujiwara and F. Kato, *Foundations of Rigid Geometry I*, arXiv:1308.4734v5,
  Chapter 0, §7.5, for associated graded modules of integer filtrations.
* Mathlib's direct-sum, submodule-quotient and scalar-restriction universal
  properties, and its tautological evaluation action of linear endomorphisms.
-/

@[expose] public section

universe u v

namespace Ideal.IntFiltration

variable {R : Type u} [CommRing R] {I : Ideal R}
variable {M : Type v} [AddCommGroup M] [Module R M] (F : I.IntFiltration M)

private def powerStageMap (q : ℕ) (a : ↥(I ^ q)) (n : ℤ) :
    F.N n →ₗ[R] F.N (n + (q : ℤ)) where
  toFun m := ⟨(a : R) • (m : M),
    F.pow_smul_le q n (Submodule.smul_mem_smul a.property m.property)⟩
  map_add' m m' := Subtype.ext (smul_add (a : R) (m : M) (m' : M))
  map_smul' r m := Subtype.ext (smul_comm (a : R) r (m : M))

private theorem powerStageMap_coe (q : ℕ) (a : ↥(I ^ q)) (n : ℤ) (m : F.N n) :
    (powerStageMap F q a n m : M) = (a : R) • (m : M) := rfl

-- The second argument descends because its denominator is shifted into the
-- denominator in the target degree, not merely into the target stage.
private theorem powerStageMap_nextStage (q : ℕ) (a : ↥(I ^ q)) (n : ℤ) :
    F.nextStage n ≤ LinearMap.ker ((F.single (n + (q : ℤ))).comp
      (powerStageMap F q a n)) := by
  intro m hm
  rw [LinearMap.mem_ker, LinearMap.comp_apply, F.single_eq_zero_iff, powerStageMap_coe]
  have h := F.pow_smul_le q (n + 1) (Submodule.smul_mem_smul a.property hm)
  simpa only [Submodule.subtype_apply, add_right_comm] using h

private def powerPieceMap (q : ℕ) (a : ↥(I ^ q)) (n : ℤ) :
    F.GradedPiece n →ₗ[R] F.AssociatedGraded :=
  (F.nextStage n).liftQ ((F.single (n + (q : ℤ))).comp (powerStageMap F q a n))
    (powerStageMap_nextStage F q a n)

private def powerEnd (q : ℕ) (a : ↥(I ^ q)) : Module.End R F.AssociatedGraded :=
  F.lift (powerPieceMap F q a)

private theorem powerEnd_single (q : ℕ) (a : ↥(I ^ q)) (n : ℤ) (m : F.N n) :
    powerEnd F q a (F.single n m) =
      F.single (n + (q : ℤ)) (powerStageMap F q a n m) := by
  rw [single_apply, powerEnd, F.lift_inclusion]
  rfl

private def powerAction (q : ℕ) : ↥(I ^ q) →ₗ[R] Module.End R F.AssociatedGraded where
  toFun := powerEnd F q
  map_add' a b := by
    apply F.linearMap_ext
    intro n m
    simp only [LinearMap.add_apply, powerEnd_single]
    rw [← map_add]
    congr 1
    exact Subtype.ext (add_smul (a : R) (b : R) (m : M))
  map_smul' r a := by
    apply F.linearMap_ext
    intro n m
    simp only [LinearMap.smul_apply, powerEnd_single, RingHom.id_apply]
    rw [← map_smul]
    congr 1
    exact Subtype.ext (smul_smul r (a : R) (m : M)).symm

private theorem powerAction_single (q : ℕ) (a : ↥(I ^ q)) (n : ℤ) (m : F.N n) :
    powerAction F q a (F.single n m) =
      F.single (n + (q : ℤ))
        ⟨(a : R) • (m : M),
          F.pow_smul_le q n (Submodule.smul_mem_smul a.property m.property)⟩ :=
  powerEnd_single F q a n m

-- Comparing in the whole direct sum avoids casts between varying graded pieces.
private theorem single_congr {n k : ℤ} (h : n = k) (m : F.N n) (m' : F.N k)
    (hm : (m : M) = (m' : M)) : F.single n m = F.single k m' := by
  subst k
  exact congrArg (F.single n) (Subtype.ext hm)

private theorem powerAction_zero (r : ↥(I ^ 0)) :
    powerAction F 0 r = (r : R) • (LinearMap.id : Module.End R F.AssociatedGraded) := by
  apply F.linearMap_ext
  intro n m
  simp only [powerAction_single, LinearMap.smul_apply, LinearMap.id_apply]
  rw [← map_smul]
  exact single_congr F (by simp) _ _ rfl

private theorem powerAction_zero_apply (r : ↥(I ^ 0)) (x : F.AssociatedGraded) :
    powerAction F 0 r x = (r : R) • x := by
  rw [powerAction_zero]
  rfl

private theorem powerAction_one :
    powerAction F 0 ⟨1, by simp⟩ = (LinearMap.id : Module.End R F.AssociatedGraded) := by
  rw [powerAction_zero, one_smul]

private theorem powerAction_comp (q p : ℕ) (a : ↥(I ^ q)) (b : ↥(I ^ p)) :
    (powerAction F q a).comp (powerAction F p b) =
      powerAction F (q + p)
        ⟨(a : R) * (b : R), by
          rw [pow_add]
          exact Ideal.mul_mem_mul a.property b.property⟩ := by
  apply F.linearMap_ext
  intro n m
  simp only [LinearMap.comp_apply, powerAction_single]
  apply single_congr F (by push_cast; lia)
  exact (mul_smul (a : R) (b : R) (m : M)).symm

private theorem powerAction_eq_zero (q : ℕ) (a : ↥(I ^ q))
    (ha : (a : R) ∈ I ^ (q + 1)) : powerAction F q a = 0 := by
  apply F.linearMap_ext
  intro n m
  rw [powerAction_single, LinearMap.zero_apply, F.single_eq_zero_iff]
  simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using
    F.pow_smul_le (q + 1) n (Submodule.smul_mem_smul ha m.property)

local notation "B" => reesAlgebra I
local notation "J" => I.map (algebraMap R B)
local notation "C" => B ⧸ J
local notation "G" => F.AssociatedGraded
local notation "ℬ" => fun q : ℕ =>
  Subtype (fun p : reesAlgebra I => p ∈ reesAlgebra.homogeneousComponent I q)

private noncomputable def homogeneousAction (q : ℕ) :
    reesAlgebra.homogeneousComponent I q →ₗ[R] Module.End R G :=
  (powerAction F q).comp (reesAlgebra.monomialEquiv I q).symm.toLinearMap

private theorem homogeneousAction_monomialEquiv (q : ℕ) (a : ↥(I ^ q)) :
    homogeneousAction F q (reesAlgebra.monomialEquiv I q a) = powerAction F q a := by
  simp [homogeneousAction]

private theorem homogeneousAction_one :
    homogeneousAction F 0
      (GradedMonoid.GOne.one (A := ℬ) : reesAlgebra.homogeneousComponent I 0) =
        (1 : Module.End R G) := by
  have h : (GradedMonoid.GOne.one (A := ℬ) : reesAlgebra.homogeneousComponent I 0) =
      reesAlgebra.monomialEquiv I 0 (⟨1, by simp⟩ : ↥(I ^ 0)) := by
    apply Subtype.ext
    change (1 : B) = (reesAlgebra.monomialEquiv I 0 (⟨1, by simp⟩ : ↥(I ^ 0)) : B)
    rw [reesAlgebra.coe_monomialEquiv]
    apply Subtype.ext
    simp
  rw [h, homogeneousAction_monomialEquiv]
  exact powerAction_one F

private theorem homogeneousAction_mul {q p : ℕ}
    (x : reesAlgebra.homogeneousComponent I q)
    (y : reesAlgebra.homogeneousComponent I p) :
    homogeneousAction F (q + p) (GradedMonoid.GMul.mul (A := ℬ) x y) =
      homogeneousAction F q x * homogeneousAction F p y := by
  obtain ⟨a, rfl⟩ := (reesAlgebra.monomialEquiv I q).surjective x
  obtain ⟨b, rfl⟩ := (reesAlgebra.monomialEquiv I p).surjective y
  have h : GradedMonoid.GMul.mul (A := ℬ) (reesAlgebra.monomialEquiv I q a)
      (reesAlgebra.monomialEquiv I p b) =
        reesAlgebra.monomialEquiv I (q + p)
          ⟨(a : R) * (b : R), by
            rw [pow_add]
            exact Ideal.mul_mem_mul a.property b.property⟩ := by
    apply Subtype.ext
    change (reesAlgebra.monomialEquiv I q a : B) *
      (reesAlgebra.monomialEquiv I p b : B) = _
    simpa only [reesAlgebra.coe_monomialEquiv] using
      reesAlgebra.monomial_mul_monomial I q p a b
  rw [h, homogeneousAction_monomialEquiv, homogeneousAction_monomialEquiv,
    homogeneousAction_monomialEquiv]
  exact (powerAction_comp F q p a b).symm

private noncomputable def reesRepresentationRingHom : B →+* Module.End R G :=
  (DirectSum.toSemiring (A := ℬ)
    (fun q => (homogeneousAction F q).toAddMonoidHom)
    (homogeneousAction_one F) (homogeneousAction_mul F)).comp
      (DirectSum.decomposeRingEquiv (reesAlgebra.homogeneousComponent I)).toRingHom

private theorem reesRepresentationRingHom_homogeneous (q : ℕ)
    (x : reesAlgebra.homogeneousComponent I q) :
    reesRepresentationRingHom F (x : B) = homogeneousAction F q x := by
  change DirectSum.toSemiring (A := ℬ)
    (fun q => (homogeneousAction F q).toAddMonoidHom)
    (homogeneousAction_one F) (homogeneousAction_mul F)
      (DirectSum.decompose (reesAlgebra.homogeneousComponent I) (x : B)) = _
  rw [DirectSum.decompose_coe]
  exact DirectSum.toSemiring_of
    (fun q => (homogeneousAction F q).toAddMonoidHom)
    (homogeneousAction_one F) (homogeneousAction_mul F) q x

private theorem reesRepresentationRingHom_monomial (q : ℕ) (a : ↥(I ^ q)) :
    reesRepresentationRingHom F (reesAlgebra.monomial I q a) = powerAction F q a := by
  rw [← reesAlgebra.coe_monomialEquiv I q a, reesRepresentationRingHom_homogeneous,
    homogeneousAction_monomialEquiv]

private noncomputable def reesRepresentation : B →ₐ[R] Module.End R G where
  toRingHom := reesRepresentationRingHom F
  commutes' r := by
    change reesRepresentationRingHom F (algebraMap R B r) = algebraMap R (Module.End R G) r
    rw [← reesAlgebra.monomial_zero I (⟨r, by simp⟩ : ↥(I ^ 0)),
      reesRepresentationRingHom_monomial]
    apply LinearMap.ext
    intro x
    exact powerAction_zero_apply F ⟨r, by simp⟩ x

private theorem reesRepresentation_monomial (q : ℕ) (a : ↥(I ^ q)) :
    reesRepresentation F (reesAlgebra.monomial I q a) = powerAction F q a :=
  reesRepresentationRingHom_monomial F q a

private theorem extendedIdeal_le_ker_reesRepresentation :
    J ≤ RingHom.ker (reesRepresentation F).toRingHom := by
  apply Ideal.map_le_iff_le_comap.mpr
  intro r hr
  change reesRepresentation F (algebraMap R B r) = 0
  rw [(reesRepresentation F).commutes]
  apply LinearMap.ext
  intro x
  change r • x = 0
  exact F.smul_eq_zero_of_mem hr x

/-- The canonical quotient Rees representation by original-`R`-linear endomorphisms. -/
@[no_expose]
noncomputable def reesQuotientRepresentation : C →ₐ[R] Module.End R G := by
  exact Ideal.Quotient.liftₐ J (reesRepresentation F)
    (fun x hx => extendedIdeal_le_ker_reesRepresentation F hx)

private theorem reesQuotientRepresentation_mk (x : B) :
    F.reesQuotientRepresentation (Ideal.Quotient.mk J x) = reesRepresentation F x := rfl

/-- The quotient Rees action obtained by evaluating the canonical representation. -/
@[reducible]
noncomputable instance moduleReesQuotient : Module C G :=
  Module.compHom G F.reesQuotientRepresentation.toRingHom

/-- The quotient Rees action evaluates its original-linear endomorphism. -/
theorem reesQuotientRepresentation_apply (c : C) (x : G) :
    F.reesQuotientRepresentation c x = c • x := rfl

/-- Coefficient constants act by the fixed original coefficient action. -/
theorem quotient_algebraMap_smul (r : R) (x : G) :
    (Ideal.Quotient.mk J (algebraMap R B r) : C) • x = r • x := by
  change F.reesQuotientRepresentation (algebraMap R C r) x = r • x
  rw [AlgHom.commutes]
  rfl

/-- The quotient Rees action extends the fixed original coefficient action. -/
instance scalarTowerCoefficients : IsScalarTower R C G where
  smul_assoc r c x := by
    change F.reesQuotientRepresentation (r • c) x =
      r • F.reesQuotientRepresentation c x
    rw [map_smul, LinearMap.smul_apply]

/-- A degree-`q` quotient Rees monomial acts on a degree-`n` representative by multiplication. -/
theorem monomial_smul_single (q : ℕ) (n : ℤ) (a : ↥(I ^ q)) (m : F.N n) :
    (Ideal.Quotient.mk J (reesAlgebra.monomial I q a) : C) • F.single n m =
      F.single (n + (q : ℤ))
        ⟨(a : R) • (m : M),
          F.pow_smul_le q n (Submodule.smul_mem_smul a.property m.property)⟩ := by
  change F.reesQuotientRepresentation
    (Ideal.Quotient.mk J (reesAlgebra.monomial I q a)) (F.single n m) = _
  rw [reesQuotientRepresentation_mk, reesRepresentation_monomial, powerAction_single]

/-- A next-power coefficient acts as zero in the corresponding quotient Rees degree. -/
theorem monomial_smul_eq_zero (q : ℕ) (a : ↥(I ^ q))
    (ha : (a : R) ∈ I ^ (q + 1)) (x : G) :
    (Ideal.Quotient.mk J (reesAlgebra.monomial I q a) : C) • x = 0 := by
  change F.reesQuotientRepresentation
    (Ideal.Quotient.mk J (reesAlgebra.monomial I q a)) x = 0
  rw [reesQuotientRepresentation_mk, reesRepresentation_monomial,
    powerAction_eq_zero F q a ha, LinearMap.zero_apply]

end Ideal.IntFiltration
