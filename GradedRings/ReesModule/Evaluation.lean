/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GradedRings.ReesModule.Map
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.RingTheory.Finiteness.Basic

/-!
# Evaluation of Rees modules

For any natural ideal filtration `H` and any scalar `r`, polynomial evaluation
restricts to a semilinear map from the Rees module to the original submodule
`H.N 0`. Its scalar hom is polynomial evaluation composed with the Rees-algebra
inclusion. The original-ring linear constant-single map is a section at every
`r`, so evaluation is surjective. In particular, finite generation of the Rees
module implies finite generation of its initial stage over the original ring.

Evaluation at zero is the constant-coefficient augmentation; its scalar hom can
be rewritten with `Polynomial.evalRingHom_zero`. No new action on the initial
stage is used. The constant section is only original-ring linear, and no
identification of the augmentation kernel with an ideal multiple is asserted.

## References

The construction uses Andrew Yang's filtration and polynomial-module
formalizations in Mathlib, especially `PolynomialModule.eval`, `eval_smul`,
`eval_single`, and `eval_map`. Naturality uses the coefficientwise Rees maps in
`GradedRings.ReesModule.Map`. The finiteness consequence uses Johan Commelin's
semilinear finite-image API `Module.Finite.of_surjective`.
-/

@[expose] public section

universe u v w

namespace PolynomialModule

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

/-- Evaluation at zero returns the constant coefficient. -/
@[simp]
theorem eval_zero (p : PolynomialModule R M) : eval (0 : R) p = p.coeff 0 := by
  induction p using induction_linear with
  | zero => simp
  | add p q hp hq => simp [hp, hq]
  | single q m => cases q <;> simp

end PolynomialModule

namespace Ideal.Filtration

variable {R : Type u} [CommRing R] {I : Ideal R}
variable {M : Type v} [AddCommGroup M] [Module R M]
variable (H : I.Filtration M)

/-- Evaluate a Rees-module element in its original zero-stage submodule. -/
noncomputable def evalRees (r : R) :
    H.submodule →ₛₗ[(Polynomial.evalRingHom r).comp
      (reesAlgebra I).val.toRingHom] H.N 0 :=
  LinearMap.codRestrict (H.N 0)
    ({ toFun := fun p => PolynomialModule.eval r (p : PolynomialModule R M)
       map_add' p q := (PolynomialModule.eval r).map_add _ _
       map_smul' b p := by
         change PolynomialModule.eval r
             ((b : Polynomial R) • (p : PolynomialModule R M)) =
           Polynomial.eval r (b : Polynomial R) •
             PolynomialModule.eval r (p : PolynomialModule R M)
         exact PolynomialModule.eval_smul _ _ _ } :
      H.submodule →ₛₗ[(Polynomial.evalRingHom r).comp
        (reesAlgebra I).val.toRingHom] M)
    (by
      intro p
      change (p : PolynomialModule R M).coeff.sum (fun q m => r ^ q • m) ∈ H.N 0
      apply Submodule.sum_mem
      intro q _
      exact (H.N 0).smul_mem _
        (H.antitone (Nat.zero_le q) ((H.mem_submodule _).mp p.property q)))

/-- The original-ring linear constant-single section of Rees evaluation. -/
noncomputable def single0 : H.N 0 →ₗ[R] H.submodule where
  toFun := fun m =>
    ⟨PolynomialModule.lsingle R 0 (m : M), by
      apply (H.mem_submodule _).mpr
      intro q
      by_cases hq : 0 = q
      · subst q
        simpa only [PolynomialModule.lsingle_apply, ite_true] using m.property
      · simp [PolynomialModule.lsingle_apply, hq]⟩
  map_add' m n := Subtype.ext ((PolynomialModule.lsingle R 0).map_add _ _)
  map_smul' a m := Subtype.ext ((PolynomialModule.lsingle R 0).map_smul a _)

/-- The underlying value of Rees evaluation is polynomial-module evaluation. -/
@[simp]
theorem coe_evalRees (r : R) (p : H.submodule) :
    (H.evalRees r p : M) = PolynomialModule.eval r (p : PolynomialModule R M) := rfl

/-- The constant section has the original polynomial single as its value. -/
@[simp]
theorem coe_single0 (m : H.N 0) :
    (H.single0 m : PolynomialModule R M) = PolynomialModule.single R 0 (m : M) := rfl

/-- The constant section has only its prescribed degree-zero coefficient. -/
theorem coeff_single0 (m : H.N 0) (q : ℕ) :
    (H.single0 m : PolynomialModule R M).coeff q = if q = 0 then (m : M) else 0 := by
  simp [Finsupp.single_apply, eq_comm]

/-- Evaluation of an admissible single is the corresponding scalar power multiple. -/
theorem coe_evalRees_single (r : R) (q : ℕ) (m : H.N q) :
    (H.evalRees r
      (⟨PolynomialModule.single R q (m : M), by
        apply (H.mem_submodule _).mpr
        intro i
        by_cases hi : q = i
        · subst i
          simp
        · simp [PolynomialModule.coeff_single, hi]⟩ : H.submodule) : M) =
      r ^ q • (m : M) := by
  rw [coe_evalRees]
  exact PolynomialModule.eval_single r q (m : M)

/-- The constant-single map is a section at every evaluation point. -/
@[simp]
theorem evalRees_single0 (r : R) (m : H.N 0) : H.evalRees r (H.single0 m) = m := by
  apply Subtype.ext
  rw [coe_evalRees, coe_single0]
  simpa only [pow_zero, one_smul] using PolynomialModule.eval_single r 0 (m : M)

/-- Rees evaluation is surjective onto the original initial stage. -/
theorem evalRees_surjective (r : R) : Function.Surjective (H.evalRees r) :=
  fun m => ⟨H.single0 m, H.evalRees_single0 r m⟩

/-- Finite generation of the Rees module implies finite generation of its initial stage.

No finite generation of the ideal, other stages, or ambient module is required. -/
theorem fg_N_zero_of_submodule_fg (hE : H.submodule.FG) : (H.N 0).FG := by
  let : Module.Finite (reesAlgebra I) H.submodule := Module.Finite.of_fg hE
  let : Module.Finite R (H.N 0) :=
    Module.Finite.of_surjective (H.evalRees 0) (H.evalRees_surjective 0)
  exact Module.Finite.iff_fg.mp inferInstance

variable {N : Type w} [AddCommGroup N] [Module R N]
variable (K : I.Filtration N) (f : M →ₗ[R] N)
variable (hf : ∀ q, H.N q ≤ (K.N q).comap f)

/-- Evaluation commutes with a stage-preserving map on underlying module elements. -/
theorem coe_evalRees_reesMap (r : R) (p : H.submodule) :
    (K.evalRees r (H.reesMap K f hf p) : N) = f (H.evalRees r p : M) := by
  simpa only [coe_evalRees, coe_reesMap, Algebra.algebraMap_self, RingHom.id_apply] using
    PolynomialModule.eval_map R f (p : PolynomialModule R M) r

/-- The evaluation square commutes as semilinear maps into the original initial stage. -/
theorem evalRees_reesMap (r : R) :
    (K.evalRees r).comp (H.reesMap K f hf) =
      ((f.domRestrict (H.N 0)).codRestrict (K.N 0)
        (fun m => hf 0 m.property)).comp (H.evalRees r) := by
  apply LinearMap.ext
  intro p
  apply Subtype.ext
  exact H.coe_evalRees_reesMap K f hf r p

/-- Stage-preserving maps carry constant sections to constant sections. -/
theorem reesMap_single0 (m : H.N 0) :
    H.reesMap K f hf (H.single0 m) = K.single0 ⟨f (m : M), hf 0 m.property⟩ := by
  apply Subtype.ext
  simp only [coe_reesMap, coe_single0, PolynomialModule.map_single]

end Ideal.Filtration
