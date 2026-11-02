/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GradedRings.ReesModule.Evaluation
public import GradedRings.FilteredAssociatedGraded.Adic
public import GradedRings.FilteredAssociatedGraded.ReesTransition
import GradedRings.PolynomialModule.EvaluationKernel
import GradedRings.PolynomialModule.Monic

/-!
# Linear-factor presentations of Rees evaluation kernels

For a natural ideal filtration `H` and any scalar `r`, multiplication by the
ambient polynomial `X - C r` defines a Rees-algebra-linear map from
`(H.toIntFiltration.natTail 1).submodule` to `H.submodule`. Its value uses the
cutoff transition from tail one to tail zero and the coefficientwise identity
maps into the original Rees module.

The map is injective, its range is the kernel of `H.evalRees r`, and every
element of that kernel has a unique successor-stage factor. These statements
require neither regularity of `r` nor finiteness of the ideal or module. The
evaluator retains its semilinear codomain in the original stage `H.N 0`; no
Rees-algebra action on that stage is used.

## References

The construction uses Andrew Yang's filtration and polynomial-module
formalizations in Mathlib, together with `PolynomialModule.monic_smul_coeff_mem_iff`,
`monic_smul_injective`, and `eval_eq_zero_iff_exists_smul_X_sub_C`. It follows the
coefficientwise Rees maps in `GradedRings.ReesModule.Map`, the natural-to-integer
extension in `GradedRings.FilteredAssociatedGraded.Adic`, and the cutoff
transitions in `GradedRings.FilteredAssociatedGraded.ReesTransition`.
-/

@[expose] public section

universe u v w

namespace Ideal.Filtration

variable {R : Type u} [CommRing R] {I : Ideal R}
variable {M : Type v} [AddCommGroup M] [Module R M]
variable (H : I.Filtration M)

private theorem natTail_one_N (n : ℕ) :
    (H.toIntFiltration.natTail (1 : ℤ)).N n = H.N (n + 1) := by
  rw [Ideal.IntFiltration.natTail_N, toIntFiltration_N]
  congr 1
  omega

/-- Multiplication by the ambient polynomial `X - C r` from the successor-stage
Rees module to the original Rees module. -/
noncomputable def mulXSubC (r : R) :
    (H.toIntFiltration.natTail (1 : ℤ)).submodule →ₗ[reesAlgebra I] H.submodule :=
  let F := H.toIntFiltration
  let i0 : (F.natTail (0 : ℤ)).submodule →ₗ[reesAlgebra I] H.submodule :=
    (F.natTail (0 : ℤ)).reesMap H (LinearMap.id : M →ₗ[R] M) (by
      intro n m hm
      change m ∈ H.N n
      change m ∈ (H.toIntFiltration.natTail (0 : ℤ)).N n at hm
      simpa only [Ideal.IntFiltration.natTail_N, zero_add, toIntFiltration_N_nat]
        using hm)
  let i1 : (F.natTail (1 : ℤ)).submodule →ₗ[reesAlgebra I] H.submodule :=
    (F.natTail (1 : ℤ)).reesMap H (LinearMap.id : M →ₗ[R] M) (by
      intro n m hm
      change m ∈ H.N n
      change m ∈ (H.toIntFiltration.natTail (1 : ℤ)).N n at hm
      exact H.mono n (by simpa only [natTail_one_N] using hm))
  show (F.natTail (1 : ℤ)).submodule →ₗ[reesAlgebra I] H.submodule from
    @Sub.sub _ (LinearMap.instSub
      (R₁ := reesAlgebra I) (R₂ := reesAlgebra I)
      (M := (F.natTail (1 : ℤ)).submodule) (N₂ := H.submodule)
      (σ₁₂ := RingHom.id (reesAlgebra I)))
      (i0.comp (F.natTailTransition (0 : ℤ) (1 : ℤ) (by omega)))
      ((algebraMap R (reesAlgebra I) r) • i1)

/-- The underlying polynomial is multiplied by `X - C r`. -/
@[simp]
theorem coe_mulXSubC (r : R)
    (p : (H.toIntFiltration.natTail (1 : ℤ)).submodule) :
    (H.mulXSubC r p : PolynomialModule R M) =
      (Polynomial.X - Polynomial.C r) • (p : PolynomialModule R M) := by
  have hid (q : PolynomialModule R M) :
      PolynomialModule.map R (LinearMap.id : M →ₗ[R] M) q = q := by
    apply PolynomialModule.coeff_injective
    ext n
    rfl
  have hsub
      (f g : (H.toIntFiltration.natTail (1 : ℤ)).submodule →ₗ[reesAlgebra I] H.submodule)
      (q : (H.toIntFiltration.natTail (1 : ℤ)).submodule) :
      (@Sub.sub _ (LinearMap.instSub
        (R₁ := reesAlgebra I) (R₂ := reesAlgebra I)
        (M := (H.toIntFiltration.natTail (1 : ℤ)).submodule) (N₂ := H.submodule)
        (σ₁₂ := RingHom.id (reesAlgebra I))) f g) q = f q - g q := rfl
  simp only [mulXSubC, hsub, LinearMap.comp_apply, LinearMap.smul_apply,
    Submodule.coe_sub, Submodule.coe_smul, coe_reesMap,
    Ideal.IntFiltration.coe_natTailTransition, hid, sub_zero, Int.toNat_one,
    pow_one, Subalgebra.smul_def, Subalgebra.coe_algebraMap,
    Polynomial.algebraMap_eq, sub_smul]

/-- The constant coefficient of a linear-factor image is the negative scalar
multiple of the source's constant coefficient. -/
theorem coeff_mulXSubC_zero (r : R)
    (p : (H.toIntFiltration.natTail (1 : ℤ)).submodule) :
    (H.mulXSubC r p : PolynomialModule R M).coeff 0 =
      -(r • (p : PolynomialModule R M).coeff 0) := by
  rw [coe_mulXSubC, sub_smul]
  change ((Polynomial.X : Polynomial R) • (p : PolynomialModule R M)).coeff 0 -
      (Polynomial.C r • (p : PolynomialModule R M)).coeff 0 = _
  rw [← Polynomial.monomial_one_one_eq_X, ← Polynomial.monomial_zero_left,
    PolynomialModule.monomial_smul_apply, PolynomialModule.monomial_smul_apply]
  simp

/-- A positive-degree coefficient is the preceding source coefficient minus
`r` times the source coefficient in the same degree. -/
theorem coeff_mulXSubC_succ (r : R)
    (p : (H.toIntFiltration.natTail (1 : ℤ)).submodule) (n : ℕ) :
    (H.mulXSubC r p : PolynomialModule R M).coeff (n + 1) =
      (p : PolynomialModule R M).coeff n -
        r • (p : PolynomialModule R M).coeff (n + 1) := by
  rw [coe_mulXSubC, sub_smul]
  change ((Polynomial.X : Polynomial R) • (p : PolynomialModule R M)).coeff (n + 1) -
      (Polynomial.C r • (p : PolynomialModule R M)).coeff (n + 1) = _
  rw [← Polynomial.monomial_one_one_eq_X, ← Polynomial.monomial_zero_left,
    PolynomialModule.monomial_smul_apply, PolynomialModule.monomial_smul_apply]
  simp

/-- An admissible single acquires one degree in the `X` term, while its scalar
term remains in the original degree. -/
theorem coe_mulXSubC_single (r : R) (n : ℕ) (m : H.N (n + 1)) :
    (H.mulXSubC r
      (H.toIntFiltration.natTailSingle (1 : ℤ) n ⟨(m : M), by
        change (m : M) ∈ (H.toIntFiltration.natTail (1 : ℤ)).N n
        simpa only [natTail_one_N] using m.property⟩) : PolynomialModule R M) =
      PolynomialModule.single R (n + 1) (m : M) -
        PolynomialModule.single R n (r • (m : M)) := by
  rw [coe_mulXSubC, Ideal.IntFiltration.coe_natTailSingle, sub_smul,
    ← Polynomial.monomial_one_one_eq_X, ← Polynomial.monomial_zero_left,
    PolynomialModule.monomial_smul_single, PolynomialModule.monomial_smul_single]
  simp only [one_smul, Nat.one_add, Nat.zero_add]

/-- At zero the underlying polynomial map is the cutoff transition from tail
one to tail zero. -/
theorem coe_mulXSubC_zero_transition
    (p : (H.toIntFiltration.natTail (1 : ℤ)).submodule) :
    (H.mulXSubC (0 : R) p : PolynomialModule R M) =
      (H.toIntFiltration.natTailTransition (0 : ℤ) (1 : ℤ) (by omega) p :
        PolynomialModule R M) := by
  rw [coe_mulXSubC, Ideal.IntFiltration.coe_natTailTransition]
  simp

/-- Multiplication by `X - C r` on the successor-stage Rees module is injective
at every scalar, without a regularity assumption. -/
theorem mulXSubC_injective (r : R) : Function.Injective (H.mulXSubC r) := by
  intro p q hpq
  apply Subtype.ext
  apply PolynomialModule.monic_smul_injective (Polynomial.X - Polynomial.C r)
    (Polynomial.monic_X_sub_C r)
  simpa only [coe_mulXSubC] using
    congrArg (fun x : H.submodule => (x : PolynomialModule R M)) hpq

/-- The range of linear-factor multiplication is the semilinear evaluation
kernel, as submodules over the Rees algebra. -/
theorem range_mulXSubC (r : R) :
    LinearMap.range (H.mulXSubC r) = LinearMap.ker (H.evalRees r) := by
  ext p
  rw [LinearMap.mem_range, LinearMap.mem_ker]
  constructor
  · rintro ⟨q, rfl⟩
    apply Subtype.ext
    change PolynomialModule.eval r (H.mulXSubC r q : PolynomialModule R M) = 0
    rw [coe_mulXSubC]
    exact (PolynomialModule.eval_eq_zero_iff_exists_smul_X_sub_C r _).mpr
      ⟨(q : PolynomialModule R M), rfl⟩
  · intro hp
    have hp' := congrArg (fun x : H.N 0 => (x : M)) hp
    change PolynomialModule.eval r (p : PolynomialModule R M) = 0 at hp'
    obtain ⟨q, hq⟩ :=
      (PolynomialModule.eval_eq_zero_iff_exists_smul_X_sub_C r _).mp hp'
    have hqmem : q ∈ (H.toIntFiltration.natTail (1 : ℤ)).submodule := by
      rcases subsingleton_or_nontrivial R with hR | hR
      · let := hR
        let : Subsingleton M := Module.subsingleton R M
        apply ((H.toIntFiltration.natTail (1 : ℤ)).mem_submodule q).mpr
        intro n
        rw [Subsingleton.elim (q.coeff n) 0]
        exact ((H.toIntFiltration.natTail (1 : ℤ)).N n).zero_mem
      · let := hR
        have hcoeff := (PolynomialModule.monic_smul_coeff_mem_iff H.N H.antitone
          (Polynomial.X - Polynomial.C r) (Polynomial.monic_X_sub_C r) q).mp
          (by rw [hq]; exact (H.mem_submodule _).mp p.property)
        apply ((H.toIntFiltration.natTail (1 : ℤ)).mem_submodule q).mpr
        intro n
        simpa only [natTail_one_N, Polynomial.natDegree_X_sub_C] using hcoeff n
    refine ⟨⟨q, hqmem⟩, ?_⟩
    apply Subtype.ext
    rw [coe_mulXSubC]
    exact hq

/-- An evaluation-zero Rees element has a unique factor in the successor-stage
Rees module. -/
theorem evalRees_eq_zero_iff_existsUnique_mulXSubC (r : R) (p : H.submodule) :
    H.evalRees r p = 0 ↔
      ∃! q : (H.toIntFiltration.natTail (1 : ℤ)).submodule, H.mulXSubC r q = p := by
  rw [← LinearMap.mem_ker, ← H.range_mulXSubC r, LinearMap.mem_range]
  constructor
  · rintro ⟨q, hq⟩
    exact ⟨q, hq, fun q' hq' => H.mulXSubC_injective r (hq'.trans hq.symm)⟩
  · rintro ⟨q, hq, _⟩
    exact ⟨q, hq⟩

variable {N : Type w} [AddCommGroup N] [Module R N]
variable (K : I.Filtration N) (f : M →ₗ[R] N)
variable (hf : ∀ n, H.N n ≤ (K.N n).comap f)

/-- Stage-preserving coefficient maps commute with linear-factor multiplication. -/
theorem mulXSubC_naturality (r : R) :
    (K.mulXSubC r).comp
      ((H.toIntFiltration.natTail (1 : ℤ)).reesMap
        (K.toIntFiltration.natTail (1 : ℤ)) f (by
          intro n
          simpa only [natTail_one_N] using hf (n + 1))) =
      (H.reesMap K f hf).comp (H.mulXSubC r) := by
  apply LinearMap.ext
  intro p
  apply Subtype.ext
  simp only [LinearMap.comp_apply, coe_mulXSubC, coe_reesMap]
  simpa using (PolynomialModule.map_smul R f (Polynomial.X - Polynomial.C r)
    (p : PolynomialModule R M)).symm

end Ideal.Filtration
