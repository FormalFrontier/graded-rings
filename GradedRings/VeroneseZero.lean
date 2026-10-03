/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
Design: Atlas (zero-index API assessment; no Lean proof authorship).
-/
module

public import GradedRings.Veronese
public import Mathlib.RingTheory.FiniteType

/-!
# Degree zero and the zero-index Veronese ring

The new degree-zero component is the entire old degree-zero ring at every index,
including zero. At index zero, the external direct sum still retains one summand
in each new degree. Its new degree-one copy of `1` generates the direct sum as an
algebra over its actual new degree-zero component, without any finiteness or
nontriviality assumption on the original graded ring.
-/

set_option warningAsError true

@[expose] public section

noncomputable section

namespace GradedRing.Veronese

open scoped DirectSum

universe u v

variable {S : Type u} [CommRing S] {σ : Type v} [SetLike σ S]
  [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-- The complete new degree-zero component agrees with the old degree-zero ring,
also for the zero-index external direct sum. -/
def zeroRingEquivAll (n : ℕ) : component 𝒮 n 0 ≃+* 𝒮 0 :=
  RingEquiv.ofBijective (zeroRingHom 𝒮 n) ⟨by
    intro x y hxy
    obtain ⟨a, ha⟩ := (mem_component_iff 𝒮 n 0 x.1).mp x.2
    obtain ⟨b, hb⟩ := (mem_component_iff 𝒮 n 0 y.1).mp y.2
    have hval : inclusion 𝒮 n x.1 = inclusion 𝒮 n y.1 := congrArg Subtype.val hxy
    rw [← ha, ← hb, inclusion_of, inclusion_of] at hval
    have hab : a = b := Subtype.ext hval
    apply Subtype.ext
    exact ha.symm.trans ((congrArg (DirectSum.of (fun k : ℕ => 𝒮 (n * k)) 0) hab).trans hb),
    by
      intro a
      obtain ⟨x, hx, heq⟩ := exists_component 𝒮 n 0 a
      exact ⟨⟨x, hx⟩, Subtype.ext heq⟩⟩

@[simp] theorem zeroRingEquivAll_apply (n : ℕ) (a : component 𝒮 n 0) :
    ((zeroRingEquivAll 𝒮 n a : 𝒮 0) : S) = inclusion 𝒮 n a := rfl

/-- At positive indices, the all-index equivalence is the released equivalence. -/
theorem zeroRingEquivAll_eq_zeroRingEquiv (n : ℕ) (hn : 0 < n) :
    zeroRingEquivAll 𝒮 n = zeroRingEquiv 𝒮 n hn := by
  ext a
  rfl

/-- The old unit, placed in any new summand at index zero. -/
def zeroUnit (j : ℕ) : 𝒮 (0 * j) :=
  ⟨1, by simpa only [zero_mul] using SetLike.one_mem_graded 𝒮⟩

/-- The degree-one element in the external zero-index Veronese direct sum. -/
def zeroVariable : VeroneseRing 𝒮 0 :=
  DirectSum.of (fun j : ℕ => 𝒮 (0 * j)) 1 (zeroUnit 𝒮 1)

@[simp] theorem inclusion_zeroVariable : inclusion 𝒮 0 (zeroVariable 𝒮) = 1 := by
  simpa only [zeroVariable, inclusion_of] using
    (show ((zeroUnit 𝒮 1 : 𝒮 (0 * 1)) : S) = 1 from rfl)

/-- Distinct new summands remain distinct when the old ring is nontrivial,
although the zero-index inclusion identifies their copies of `1`. -/
theorem zeroVariable_ne_zeroCopy [Nontrivial S] :
    zeroVariable 𝒮 ≠ DirectSum.of (fun k : ℕ => 𝒮 (0 * k)) 0 (zeroUnit 𝒮 0) := by
  intro h
  have hzero := congrArg (fun x : VeroneseRing 𝒮 0 => x 0) h
  rw [zeroVariable,
    DirectSum.of_eq_of_ne (β := fun k : ℕ => 𝒮 (0 * k)) 1 0 (zeroUnit 𝒮 1) (by decide),
    DirectSum.of_eq_same] at hzero
  have hcontr : (0 : S) = 1 := by
    simpa only [ZeroMemClass.coe_zero, zeroUnit] using
      congrArg (fun x : 𝒮 (0 * 0) => (x : S)) hzero
  exact zero_ne_one hcontr

/-- The same old coefficient placed in the *actual* new degree-zero component. -/
def zeroCoefficient (j : ℕ) (a : 𝒮 (0 * j)) : component 𝒮 0 0 :=
  ⟨DirectSum.of (fun k : ℕ => 𝒮 (0 * k)) 0
      (⟨(a : S), by simpa only [zero_mul] using a.property⟩ : 𝒮 (0 * 0)),
    (mem_component_iff 𝒮 0 0 _).mpr
      ⟨⟨(a : S), by simpa only [zero_mul] using a.property⟩, rfl⟩⟩

@[simp] theorem zeroRingEquivAll_zeroCoefficient (j : ℕ) (a : 𝒮 (0 * j)) :
    zeroRingEquivAll 𝒮 0 (zeroCoefficient 𝒮 j a) =
      (⟨(a : S), by simpa only [zero_mul] using a.property⟩ : 𝒮 0) := by
  apply Subtype.ext
  simp only [zeroRingEquivAll_apply, zeroCoefficient, inclusion_of]

theorem zeroVariable_pow (j : ℕ) :
    zeroVariable 𝒮 ^ j = DirectSum.of (fun k : ℕ => 𝒮 (0 * k)) j (zeroUnit 𝒮 j) := by
  induction j with
  | zero =>
      rw [pow_zero]
      have hunit : zeroUnit 𝒮 0 = (1 : 𝒮 0) := Subtype.ext rfl
      rw [hunit]
      rfl
  | succ j ih =>
      rw [pow_succ, ih, zeroVariable, DirectSum.of_mul_of]
      congr 1
      apply Subtype.ext
      change (1 : S) * 1 = 1
      simp

/-- Every selected zero-index summand is a monomial in the new degree-one element,
  whose coefficient is the *same* old-zero element in the whole actual new zero ring. -/
theorem of_zero_eq_algebraMap_mul_pow (j : ℕ) (a : 𝒮 (0 * j)) :
    DirectSum.of (fun k : ℕ => 𝒮 (0 * k)) j a =
      algebraMap (component 𝒮 0 0) (VeroneseRing 𝒮 0) (zeroCoefficient 𝒮 j a) *
        zeroVariable 𝒮 ^ j := by
  change DirectSum.of (fun k : ℕ => 𝒮 (0 * k)) j a =
    (zeroCoefficient 𝒮 j a : VeroneseRing 𝒮 0) * zeroVariable 𝒮 ^ j
  rw [zeroVariable_pow]
  change DirectSum.of (fun k : ℕ => 𝒮 (0 * k)) j a =
    DirectSum.of (fun k : ℕ => 𝒮 (0 * k)) 0
      (⟨(a : S), by simpa only [zero_mul] using a.property⟩ : 𝒮 (0 * 0)) *
      DirectSum.of (fun k : ℕ => 𝒮 (0 * k)) j (zeroUnit 𝒮 j)
  let b : 𝒮 (0 * 0) := ⟨(a : S), by simpa only [zero_mul] using a.property⟩
  exact
    letI selectedSmul : SMul (𝒮 (0 * 0)) (𝒮 (0 * j)) :=
      GradedMonoid.GradeZero.smul (A := fun k : ℕ => 𝒮 (0 * k)) j
    show _ from by
      have hsmul : (b • zeroUnit 𝒮 j : 𝒮 (0 * j)) = a := by
        apply Subtype.ext
        dsimp only [HSMul.hSMul, instHSMul, SMul.smul, selectedSmul,
          GradedMonoid.GradeZero.smul]
        have hcast {i k : ℕ} (hik : i = k) (c : 𝒮 (0 * i)) :
            ((hik ▸ c : 𝒮 (0 * k)) : S) = c := by
          cases hik
          rfl
        rw [hcast]
        change (a : S) * 1 = (a : S)
        simp
      calc
        DirectSum.of (fun k : ℕ => 𝒮 (0 * k)) j a =
            DirectSum.of (fun k : ℕ => 𝒮 (0 * k)) j
              (b • zeroUnit 𝒮 j : 𝒮 (0 * j)) := by rw [hsmul]
        _ = DirectSum.of (fun k : ℕ => 𝒮 (0 * k)) 0 b *
              DirectSum.of (fun k : ℕ => 𝒮 (0 * k)) j (zeroUnit 𝒮 j) :=
          DirectSum.of_zero_smul (fun k : ℕ => 𝒮 (0 * k)) b (zeroUnit 𝒮 j)

/-- Evaluating a polynomial at the degree-one element reaches every summand of
the external zero-index Veronese ring. -/
theorem aeval_zeroVariable_surjective :
    Function.Surjective
      (Polynomial.aeval (R := component 𝒮 0 0) (zeroVariable 𝒮) :
        Polynomial (component 𝒮 0 0) →ₐ[component 𝒮 0 0] VeroneseRing 𝒮 0) := by
  intro x
  induction x using DirectSum.induction_on with
  | zero => exact ⟨0, by simp⟩
  | of j a =>
      refine ⟨Polynomial.monomial j (zeroCoefficient 𝒮 j a), ?_⟩
      simpa only [Polynomial.aeval_monomial] using
        (of_zero_eq_algebraMap_mul_pow 𝒮 j a).symm
  | add x y hx hy =>
      obtain ⟨p, hp⟩ := hx
      obtain ⟨q, hq⟩ := hy
      exact ⟨p + q, by simp only [map_add, hp, hq]⟩

/-- The zero-index external Veronese ring is of finite type over its full new
degree-zero component, without a finiteness assumption on the original ring. -/
theorem finiteType_zero : Algebra.FiniteType (component 𝒮 0 0) (VeroneseRing 𝒮 0) :=
  Algebra.FiniteType.of_surjective
    (Polynomial.aeval (R := component 𝒮 0 0) (zeroVariable 𝒮))
    (aeval_zeroVariable_surjective 𝒮)

end GradedRing.Veronese
