/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GradedRings.ReesModule.Quotient
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Rees modules of quotient filtrations

The quotient by the image of the induced Rees module identifies with the Rees
module of the image filtration. The forward map sends each coefficient to its
class in the original module quotient.

## Implementation notes

The range, kernel and quotient operations are formed in a common generic
ring-and-additive-group context. The linear-map records use the original Rees
maps as functions and their stored additivity and scalar-linearity proofs;
the Rees-module carriers, addition and scalar actions are unchanged. The named
quotient and its projection use the stock quotient in this same context.

## References

* Mathlib's quotient-module and first-isomorphism constructions in
  `Mathlib.LinearAlgebra.Isomorphisms`.
-/

universe u v w

namespace Ideal.Filtration

section

variable {S : Type u} [Ring S]
variable {X : Type v} [AddCommGroup X] [Module S X]
variable {Y : Type w} [AddCommGroup Y] [Module S Y]

private def rangeOfFunction
    (f : X → Y) (ha : ∀ (x y : X), f (x + y) = f x + f y)
    (hs : ∀ (s : S) (x : X), f (s • x) = s • f x) : Submodule S Y :=
  ({ toFun := f, map_add' := ha, map_smul' := hs } : X →ₗ[S] Y).range

private def quotientMkOfSubmodule (P : Submodule S X) : X →ₗ[S] (X ⧸ P) :=
  P.mkQ

private noncomputable def quotientEquivOfFunction
    (P : Submodule S X)
    (q : X → Y) (ha : ∀ (x y : X), q (x + y) = q x + q y)
    (hs : ∀ (s : S) (x : X), q (s • x) = s • q x)
    (hP : P = ({ toFun := q, map_add' := ha, map_smul' := hs } : X →ₗ[S] Y).ker)
    (hq : Function.Surjective q) : (X ⧸ P) ≃ₗ[S] Y :=
  let f : X →ₗ[S] Y := { toFun := q, map_add' := ha, map_smul' := hs }
  (Submodule.quotEquivOfEq P f.ker hP).trans (f.quotKerEquivOfSurjective hq)

private theorem quotientMkOfSubmodule_apply (P : Submodule S X) (x : X) :
    quotientMkOfSubmodule P x = (Submodule.Quotient.mk x : X ⧸ P) := by
  simp only [quotientMkOfSubmodule, Submodule.mkQ_apply]

private theorem quotientEquivOfFunction_mk
    (P : Submodule S X)
    (q : X → Y) (ha : ∀ (x y : X), q (x + y) = q x + q y)
    (hs : ∀ (s : S) (x : X), q (s • x) = s • q x)
    (hP : P = ({ toFun := q, map_add' := ha, map_smul' := hs } : X →ₗ[S] Y).ker)
    (hq : Function.Surjective q) (x : X) :
    quotientEquivOfFunction P q ha hs hP hq (Submodule.Quotient.mk x) = q x := by
  simp only [quotientEquivOfFunction, LinearEquiv.trans_apply,
    Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk]
  rfl

end

@[expose] public section

variable {R : Type u} [CommRing R] {I : Ideal R}
variable {M : Type v} [AddCommGroup M] [Module R M]
variable (H : I.Filtration M) (N : Submodule R M)

/-- The image of the Rees module of the induced filtration inside the original
Rees module. -/
@[no_expose]
noncomputable def reesSubtypeRange :=
  (fun (i : (H.comap N.subtype).submodule →ₗ[↥(reesAlgebra I)] H.submodule) =>
    rangeOfFunction (S := ↥(reesAlgebra I))
      (fun p : (H.comap N.subtype).submodule => i p)
      (fun p q => i.map_add' p q) (fun b p => i.map_smul' b p))
    (H.reesSubtype N)

/-- The quotient of a Rees module by the image of its induced filtration. -/
noncomputable abbrev reesSubtypeQuotient :=
  (fun {S : Type u} [Ring S] {X : Type v} [AddCommGroup X] [Module S X]
      (P : Submodule S X) => X ⧸ P)
    (S := ↥(reesAlgebra I)) (X := H.submodule) (H.reesSubtypeRange N)

/-- The quotient projection modulo the image of the induced Rees module. -/
@[no_expose]
noncomputable def reesSubtypeQuotientMkQ :=
  quotientMkOfSubmodule (S := ↥(reesAlgebra I)) (X := H.submodule)
    (H.reesSubtypeRange N)

/-- Every element maps to its class in the quotient by the induced Rees image. -/
@[simp]
theorem reesSubtypeQuotientMkQ_apply (p : H.submodule) :
    H.reesSubtypeQuotientMkQ N p =
      (Submodule.Quotient.mk (R := ↥(reesAlgebra I)) (M := H.submodule) p :
        H.reesSubtypeQuotient N) := by
  simp only [reesSubtypeQuotientMkQ, quotientMkOfSubmodule_apply]

/-- The image of the induced Rees module consists of elements whose coefficients
belong to the given submodule. -/
@[simp]
theorem mem_reesSubtypeRange_iff (p : H.submodule) :
    p ∈ H.reesSubtypeRange N ↔
      ∀ n, (p : PolynomialModule R M).coeff n ∈ N := by
  change (∃ x, H.reesSubtype N x = p) ↔ _
  constructor
  · rintro ⟨x, rfl⟩ n
    rw [H.coeff_reesSubtype N]
    exact ((x : PolynomialModule R N).coeff n).property
  · intro hp
    apply (H.reesSubtype_mkQ_exact N p).mp
    apply Subtype.ext
    apply PolynomialModule.coeff_injective
    apply Finsupp.ext
    intro n
    have hn : (p : PolynomialModule R M).coeff n ∈ LinearMap.ker N.mkQ := by
      rw [Submodule.ker_mkQ]
      exact hp n
    simpa only [H.coeff_reesMkQ N, Submodule.coe_zero,
      PolynomialModule.coeff_zero, Finsupp.zero_apply] using LinearMap.mem_ker.mp hn

/-- The quotient by the induced Rees image is canonically equivalent to the Rees
module of the image filtration. -/
@[no_expose]
noncomputable def reesQuotientEquiv :=
  (fun (q : H.submodule →ₗ[↥(reesAlgebra I)] (H.map N.mkQ).submodule)
      (hexact : Function.Exact (H.reesSubtype N) q) (hq : Function.Surjective q) =>
    quotientEquivOfFunction (S := ↥(reesAlgebra I)) (H.reesSubtypeRange N)
      (fun p : H.submodule => q p)
      (fun p r => q.map_add' p r) (fun b p => q.map_smul' b p)
      (by
        apply Submodule.ext
        intro p
        change (∃ x, H.reesSubtype N x = p) ↔ q p = 0
        exact (hexact p).symm) hq)
    (H.reesMkQ N) (H.reesSubtype_mkQ_exact N) (H.reesMkQ_surjective N)

/-- On quotient classes the canonical equivalence is the original Rees quotient
map. -/
@[simp]
theorem reesQuotientEquiv_mkQ (p : H.submodule) :
    H.reesQuotientEquiv N
      (Submodule.Quotient.mk (R := ↥(reesAlgebra I)) (M := H.submodule) p :
        H.reesSubtypeQuotient N) = H.reesMkQ N p := by
  simp only [reesQuotientEquiv, quotientEquivOfFunction_mk]

/-- Applying the inverse equivalence to a Rees quotient image recovers its class
modulo the induced Rees image. -/
@[simp]
theorem reesQuotientEquiv_symm_reesMkQ (p : H.submodule) :
    (H.reesQuotientEquiv N).symm (H.reesMkQ N p) =
      (Submodule.Quotient.mk (R := ↥(reesAlgebra I)) (M := H.submodule) p :
        H.reesSubtypeQuotient N) := by
  rw [← H.reesQuotientEquiv_mkQ N p]
  exact (H.reesQuotientEquiv N).symm_apply_apply _

/-- The Rees quotient is trivial exactly when the initial filtration stage is
contained in the submodule, even if the ambient module quotient is nonzero. -/
theorem subsingleton_reesSubtypeQuotient_iff :
    Subsingleton (H.reesSubtypeQuotient N) ↔ H.N 0 ≤ N := by
  constructor
  · intro h m hm
    let : Subsingleton (H.reesSubtypeQuotient N) := h
    let p : H.submodule := ⟨PolynomialModule.single R 0 m, by
      apply (H.mem_submodule _).mpr
      intro n
      by_cases hn : 0 = n
      · subst n
        simpa [PolynomialModule.coeff_single] using hm
      · simp [PolynomialModule.coeff_single, hn]⟩
    have hp : H.reesMkQ N p = 0 := by
      rw [← H.reesQuotientEquiv_mkQ N p]
      have hpclass :
          (Submodule.Quotient.mk p : H.reesSubtypeQuotient N) = 0 :=
        Subsingleton.elim _ _
      rw [hpclass, map_zero]
    have hc : N.mkQ m = 0 := by
      simpa [p, H.coeff_reesMkQ, PolynomialModule.coeff_single] using
        congrArg (fun z : (H.map N.mkQ).submodule =>
          (z : PolynomialModule R (M ⧸ N)).coeff 0) hp
    have hmker : m ∈ LinearMap.ker N.mkQ := LinearMap.mem_ker.mpr hc
    simpa only [Submodule.ker_mkQ] using hmker
  · intro h
    -- Only the image filtration must vanish, not the ambient module quotient.
    have hz (p : (H.map N.mkQ).submodule) : p = 0 := by
      apply Subtype.ext
      apply PolynomialModule.coeff_injective
      apply Finsupp.ext
      intro n
      obtain ⟨m, hm, hmq⟩ :=
        (H.mem_map_N N.mkQ n _).mp
          (((H.map N.mkQ).mem_submodule _).mp p.property n)
      have hmN : m ∈ N := h (H.antitone (Nat.zero_le n) hm)
      have hmker : m ∈ LinearMap.ker N.mkQ := by
        simpa only [Submodule.ker_mkQ] using hmN
      simpa only [Submodule.coe_zero, PolynomialModule.coeff_zero,
        Finsupp.zero_apply] using hmq.symm.trans (LinearMap.mem_ker.mp hmker)
    refine ⟨fun x y => (H.reesQuotientEquiv N).injective ?_⟩
    exact (hz (H.reesQuotientEquiv N x)).trans
      (hz (H.reesQuotientEquiv N y)).symm

end

end Ideal.Filtration
