/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents (Hive Task hive-request-a4527f02af952e11c47d91c4884c7d869bc58acc,
  UID 9b1f25a8-52cd-4da9-86eb-6f477a7e85b0)
Mixed-weight fixture adapted from GradedRings/test/FiniteVeronese.lean and
IncubatorTest/Algebra/GradedRing/VeroneseFiniteType.lean (Formal Frontier contributors).
-/
module

import GradedRings.VeroneseZero
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.Data.ZMod.Basic

set_option warningAsError true

noncomputable section

namespace VeroneseZeroClient

universe u v

variable {S : Type u} [CommRing S] {σ : Type v} [SetLike σ S]
  [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮]

example (n : ℕ) (a : GradedRing.Veronese.component 𝒮 n 0) :
    ((GradedRing.Veronese.zeroRingEquivAll 𝒮 n a : 𝒮 0) : S) =
      GradedRing.Veronese.inclusion 𝒮 n a :=
  GradedRing.Veronese.zeroRingEquivAll_apply 𝒮 n a

example (n : ℕ) (hn : 0 < n) :
    GradedRing.Veronese.zeroRingEquivAll 𝒮 n =
      GradedRing.Veronese.zeroRingEquiv 𝒮 n hn :=
  GradedRing.Veronese.zeroRingEquivAll_eq_zeroRingEquiv 𝒮 n hn

example (j : ℕ) (a : 𝒮 (0 * j)) :
    GradedRing.Veronese.zeroRingEquivAll 𝒮 0
      (GradedRing.Veronese.zeroCoefficient 𝒮 j a) =
      (⟨(a : S), by simpa only [zero_mul] using a.property⟩ : 𝒮 0) :=
  GradedRing.Veronese.zeroRingEquivAll_zeroCoefficient 𝒮 j a

example (j : ℕ) (a : 𝒮 (0 * j)) :
    DirectSum.of (fun k : ℕ => 𝒮 (0 * k)) j a =
      algebraMap (GradedRing.Veronese.component 𝒮 0 0)
        (GradedRing.Veronese.VeroneseRing 𝒮 0)
        (GradedRing.Veronese.zeroCoefficient 𝒮 j a) *
          GradedRing.Veronese.zeroVariable 𝒮 ^ j :=
  GradedRing.Veronese.of_zero_eq_algebraMap_mul_pow 𝒮 j a

example : Algebra.FiniteType (GradedRing.Veronese.component 𝒮 0 0)
    (GradedRing.Veronese.VeroneseRing 𝒮 0) :=
  GradedRing.Veronese.finiteType_zero 𝒮

example : GradedRing.Veronese.inclusion 𝒮 0
    (GradedRing.Veronese.zeroVariable 𝒮) = 1 := by
  simp

private def mixedWeights : Fin 3 → ℕ := ![0, 2, 3]
private abbrev MixedRing (R : Type*) [CommRing R] := MvPolynomial (Fin 3) R
private abbrev MixedGrading (R : Type*) [CommRing R] :=
  MvPolynomial.weightedHomogeneousSubmodule R mixedWeights

private noncomputable instance (R : Type*) [CommRing R] : GradedAlgebra (MixedGrading R) :=
  MvPolynomial.weightedGradedAlgebra R mixedWeights

private def degreeZeroVariable (R : Type*) [CommRing R] : MixedGrading R 0 :=
  ⟨MvPolynomial.X 0, by
    simpa [mixedWeights] using
      (MvPolynomial.isWeightedHomogeneous_X R mixedWeights (0 : Fin 3))⟩

example (j : ℕ) :
    GradedRing.Veronese.zeroRingEquivAll (MixedGrading ℤ) 0
      (GradedRing.Veronese.zeroCoefficient (MixedGrading ℤ) j
        (⟨(degreeZeroVariable ℤ : MixedRing ℤ), by
          simpa only [zero_mul] using (degreeZeroVariable ℤ).property⟩ :
          MixedGrading ℤ (0 * j))) = degreeZeroVariable ℤ := by
  apply Subtype.ext
  simp only [GradedRing.Veronese.zeroRingEquivAll_zeroCoefficient]

example (r : ℤ) : (degreeZeroVariable ℤ : MixedRing ℤ) ≠ MvPolynomial.C r := by
  intro h
  have hcoeff := congrArg (fun p : MixedRing ℤ =>
    p.coeff (Finsupp.single (0 : Fin 3) 1)) h
  have hsingle : (Finsupp.single (0 : Fin 3) 1 : Fin 3 →₀ ℕ) ≠ 0 := by simp
  rw [MvPolynomial.coeff_C_of_ne_zero hsingle] at hcoeff
  norm_num [degreeZeroVariable] at hcoeff

example : Algebra.FiniteType
    (GradedRing.Veronese.component (MixedGrading ℤ) 0 0)
    (GradedRing.Veronese.VeroneseRing (MixedGrading ℤ) 0) :=
  GradedRing.Veronese.finiteType_zero (MixedGrading ℤ)

example : (2 : ZMod 4) * 2 = 0 ∧
    Algebra.FiniteType (GradedRing.Veronese.component (MixedGrading (ZMod 4)) 0 0)
      (GradedRing.Veronese.VeroneseRing (MixedGrading (ZMod 4)) 0) := by
  exact ⟨by decide, GradedRing.Veronese.finiteType_zero (MixedGrading (ZMod 4))⟩

example : Subsingleton (MixedRing (ZMod 1)) := inferInstance

example : Algebra.FiniteType
    (GradedRing.Veronese.component (MixedGrading (ZMod 1)) 0 0)
    (GradedRing.Veronese.VeroneseRing (MixedGrading (ZMod 1)) 0) :=
  GradedRing.Veronese.finiteType_zero (MixedGrading (ZMod 1))

example : GradedRing.Veronese.zeroVariable (MixedGrading ℤ) ≠
    DirectSum.of (fun k : ℕ => MixedGrading ℤ (0 * k)) 0
      (GradedRing.Veronese.zeroUnit (MixedGrading ℤ) 0) :=
  GradedRing.Veronese.zeroVariable_ne_zeroCopy (MixedGrading ℤ)

end VeroneseZeroClient
