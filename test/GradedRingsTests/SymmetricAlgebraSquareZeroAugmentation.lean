/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import GradedRings.SymmetricAlgebraSquareZero
import Mathlib.Algebra.Module.PUnit
import Mathlib.Algebra.Module.ULift
import Mathlib.Algebra.Ring.PUnit
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Finsupp.Defs

/-!
# Augmentation of the square-zero symmetric-algebra quotient

Evaluation at zero descends through the square of the augmentation ideal, independently
of the equivalence with a trivial square-zero extension. The expressions below record
this map, the equivalence, their characteristic equations, and quotient-map extensionality.

The coefficient ring and module have independent universes. The specializations include
zero modules, torsion, an infinitely generated module, both asymmetric universe lifts,
and the regular module over a ring with zero divisors. The independently descended
augmentation satisfies its characteristic equations, and the augmentation contracts
are proved in the generic setting and in every specialization.
-/

open scoped TrivSqZeroExt

noncomputable section

-- These local notations include explicit universe parameters.
set_option quotPrecheck false

universe uR uM

/- Arbitrary coefficient ring and module. -/
section

variable (R : Type uR) (M : Type uM)
variable [CommRing R] [AddCommGroup M] [Module R M]
local notation "I" => SymmetricAlgebra.augmentationIdeal (R := R) (M := M)
local notation "Q" => SymmetricAlgebra R M ⧸ I ^ 2
local notation "ε" => SymmetricAlgebra.algebraMapInv (R := R) (M := M)
local notation "e" => SymmetricAlgebra.squareZeroQuotientEquiv (R := R) (M := M)
local notation "εbar" =>
  SymmetricAlgebra.squareZeroQuotientAugmentation (R := R) (M := M)

example : (SymmetricAlgebra R M ⧸ I ^ 2) ≃ₐ[R] TrivSqZeroExt R M := e

example : (SymmetricAlgebra R M ⧸ I ^ 2) →ₐ[R] R := εbar

example : (εbar).comp (Ideal.Quotient.mkₐ R (I ^ 2)) = ε :=
  SymmetricAlgebra.squareZeroQuotientAugmentation_comp_mkₐ (R := R) (M := M)

example : ∀ x : SymmetricAlgebra R M, εbar (Ideal.Quotient.mk _ x) = ε x :=
  SymmetricAlgebra.squareZeroQuotientAugmentation_mk (R := R) (M := M)

example : (TrivSqZeroExt.fstHom R R M).comp (e).toAlgHom = εbar :=
  SymmetricAlgebra.fstHom_comp_squareZeroQuotientEquiv (R := R) (M := M)

example : ∀ m : M,
  e (Ideal.Quotient.mk _ (SymmetricAlgebra.ι R M m)) = TrivSqZeroExt.inr m :=
  SymmetricAlgebra.squareZeroQuotientEquiv_mk_ι (R := R) (M := M)

example : ∀ r : R,
  e (Ideal.Quotient.mk _ (algebraMap R (SymmetricAlgebra R M) r)) = TrivSqZeroExt.inl r :=
  SymmetricAlgebra.squareZeroQuotientEquiv_mk_algebraMap (R := R) (M := M)

example : ∀ m : M,
  εbar (Ideal.Quotient.mk _ (SymmetricAlgebra.ι R M m)) = 0 :=
  SymmetricAlgebra.squareZeroQuotientAugmentation_mk_ι (R := R) (M := M)

example : ∀ r : R,
  εbar (Ideal.Quotient.mk _ (algebraMap R (SymmetricAlgebra R M) r)) = r :=
  SymmetricAlgebra.squareZeroQuotientAugmentation_mk_algebraMap (R := R) (M := M)

example : ∀ f g : Q →ₐ[R] R,
  (∀ x : SymmetricAlgebra R M,
    f (Ideal.Quotient.mk _ x) = g (Ideal.Quotient.mk _ x)) → f = g := by
  intro f g h
  apply Ideal.Quotient.algHom_ext
  exact AlgHom.ext h

end

/- Zero coefficient ring and zero module. -/
section

local notation "I" => SymmetricAlgebra.augmentationIdeal (R := PUnit.{1}) (M := PUnit.{1})
local notation "Q" => SymmetricAlgebra PUnit.{1} PUnit.{1} ⧸ I ^ 2
local notation "ε" => SymmetricAlgebra.algebraMapInv (R := PUnit.{1}) (M := PUnit.{1})
local notation "e" => SymmetricAlgebra.squareZeroQuotientEquiv (R := PUnit.{1}) (M := PUnit.{1})
local notation "εbar" =>
  SymmetricAlgebra.squareZeroQuotientAugmentation (R := PUnit.{1}) (M := PUnit.{1})

example : (SymmetricAlgebra PUnit.{1} PUnit.{1} ⧸ I ^ 2) ≃ₐ[PUnit.{1}] TrivSqZeroExt PUnit.{1}
  PUnit.{1} := e

example : (SymmetricAlgebra PUnit.{1} PUnit.{1} ⧸ I ^ 2) →ₐ[PUnit.{1}] PUnit.{1} := εbar

example : (εbar).comp (Ideal.Quotient.mkₐ PUnit.{1} (I ^ 2)) = ε :=
  SymmetricAlgebra.squareZeroQuotientAugmentation_comp_mkₐ (R := PUnit.{1}) (M := PUnit.{1})

example : ∀ x : SymmetricAlgebra PUnit.{1} PUnit.{1}, εbar (Ideal.Quotient.mk _ x) = ε x :=
  SymmetricAlgebra.squareZeroQuotientAugmentation_mk (R := PUnit.{1}) (M := PUnit.{1})

example : (TrivSqZeroExt.fstHom PUnit.{1} PUnit.{1} PUnit.{1}).comp (e).toAlgHom = εbar :=
  SymmetricAlgebra.fstHom_comp_squareZeroQuotientEquiv (R := PUnit.{1}) (M := PUnit.{1})

example : ∀ m : PUnit.{1},
  e (Ideal.Quotient.mk _ (SymmetricAlgebra.ι PUnit.{1} PUnit.{1} m)) = TrivSqZeroExt.inr m :=
  SymmetricAlgebra.squareZeroQuotientEquiv_mk_ι (R := PUnit.{1}) (M := PUnit.{1})

example : ∀ r : PUnit.{1},
  e (Ideal.Quotient.mk _ (algebraMap PUnit.{1} (SymmetricAlgebra PUnit.{1} PUnit.{1}) r)) =
    TrivSqZeroExt.inl r :=
  SymmetricAlgebra.squareZeroQuotientEquiv_mk_algebraMap (R := PUnit.{1}) (M := PUnit.{1})

example : ∀ m : PUnit.{1},
  εbar (Ideal.Quotient.mk _ (SymmetricAlgebra.ι PUnit.{1} PUnit.{1} m)) = 0 :=
  SymmetricAlgebra.squareZeroQuotientAugmentation_mk_ι (R := PUnit.{1}) (M := PUnit.{1})

example : ∀ r : PUnit.{1},
  εbar (Ideal.Quotient.mk _
    (algebraMap PUnit.{1} (SymmetricAlgebra PUnit.{1} PUnit.{1}) r)) = r :=
  SymmetricAlgebra.squareZeroQuotientAugmentation_mk_algebraMap (R := PUnit.{1}) (M := PUnit.{1})

example : ∀ f g : Q →ₐ[PUnit.{1}] PUnit.{1},
  (∀ x : SymmetricAlgebra PUnit.{1} PUnit.{1},
    f (Ideal.Quotient.mk _ x) = g (Ideal.Quotient.mk _ x)) → f = g := by
  intro f g h
  apply Ideal.Quotient.algHom_ext
  exact AlgHom.ext h

example : ∀ (r : PUnit.{1}) (m : PUnit.{1}), r • m = m := by
  intro r m
  exact PUnit.smul_eq' r m

end

/- The zero module over the integers. -/
section

local notation "I" => SymmetricAlgebra.augmentationIdeal (R := ℤ) (M := PUnit.{1})
local notation "Q" => SymmetricAlgebra ℤ PUnit.{1} ⧸ I ^ 2
local notation "ε" => SymmetricAlgebra.algebraMapInv (R := ℤ) (M := PUnit.{1})
local notation "e" => SymmetricAlgebra.squareZeroQuotientEquiv (R := ℤ) (M := PUnit.{1})
local notation "εbar" =>
  SymmetricAlgebra.squareZeroQuotientAugmentation (R := ℤ) (M := PUnit.{1})

example : (SymmetricAlgebra ℤ PUnit.{1} ⧸ I ^ 2) ≃ₐ[ℤ] TrivSqZeroExt ℤ PUnit.{1} := e

example : (SymmetricAlgebra ℤ PUnit.{1} ⧸ I ^ 2) →ₐ[ℤ] ℤ := εbar

example : (εbar).comp (Ideal.Quotient.mkₐ ℤ (I ^ 2)) = ε :=
  SymmetricAlgebra.squareZeroQuotientAugmentation_comp_mkₐ (R := ℤ) (M := PUnit.{1})

example : ∀ x : SymmetricAlgebra ℤ PUnit.{1}, εbar (Ideal.Quotient.mk _ x) = ε x :=
  SymmetricAlgebra.squareZeroQuotientAugmentation_mk (R := ℤ) (M := PUnit.{1})

example : (TrivSqZeroExt.fstHom ℤ ℤ PUnit.{1}).comp (e).toAlgHom = εbar :=
  SymmetricAlgebra.fstHom_comp_squareZeroQuotientEquiv (R := ℤ) (M := PUnit.{1})

example : ∀ m : PUnit.{1},
  e (Ideal.Quotient.mk _ (SymmetricAlgebra.ι ℤ PUnit.{1} m)) = TrivSqZeroExt.inr m :=
  SymmetricAlgebra.squareZeroQuotientEquiv_mk_ι (R := ℤ) (M := PUnit.{1})

example : ∀ r : ℤ,
  e (Ideal.Quotient.mk _ (algebraMap ℤ (SymmetricAlgebra ℤ PUnit.{1}) r)) = TrivSqZeroExt.inl r :=
  SymmetricAlgebra.squareZeroQuotientEquiv_mk_algebraMap (R := ℤ) (M := PUnit.{1})

example : ∀ m : PUnit.{1},
  εbar (Ideal.Quotient.mk _ (SymmetricAlgebra.ι ℤ PUnit.{1} m)) = 0 :=
  SymmetricAlgebra.squareZeroQuotientAugmentation_mk_ι (R := ℤ) (M := PUnit.{1})

example : ∀ r : ℤ,
  εbar (Ideal.Quotient.mk _ (algebraMap ℤ (SymmetricAlgebra ℤ PUnit.{1}) r)) = r :=
  SymmetricAlgebra.squareZeroQuotientAugmentation_mk_algebraMap (R := ℤ) (M := PUnit.{1})

example : ∀ f g : Q →ₐ[ℤ] ℤ,
  (∀ x : SymmetricAlgebra ℤ PUnit.{1},
    f (Ideal.Quotient.mk _ x) = g (Ideal.Quotient.mk _ x)) → f = g := by
  intro f g h
  apply Ideal.Quotient.algHom_ext
  exact AlgHom.ext h

example : ∀ (r : ℤ) (m : PUnit.{1}), r • m = m := by
  intro r m
  cases m
  exact PUnit.smul_eq PUnit.unit r

end

/- Two-torsion over the integers. -/
section

local notation "I" => SymmetricAlgebra.augmentationIdeal (R := ℤ) (M := ZMod 2)
local notation "Q" => SymmetricAlgebra ℤ (ZMod 2) ⧸ I ^ 2
local notation "ε" => SymmetricAlgebra.algebraMapInv (R := ℤ) (M := ZMod 2)
local notation "e" => SymmetricAlgebra.squareZeroQuotientEquiv (R := ℤ) (M := ZMod 2)
local notation "εbar" =>
  SymmetricAlgebra.squareZeroQuotientAugmentation (R := ℤ) (M := ZMod 2)

example : (SymmetricAlgebra ℤ (ZMod 2) ⧸ I ^ 2) ≃ₐ[ℤ] TrivSqZeroExt ℤ (ZMod 2) := e

example : (SymmetricAlgebra ℤ (ZMod 2) ⧸ I ^ 2) →ₐ[ℤ] ℤ := εbar

example : (εbar).comp (Ideal.Quotient.mkₐ ℤ (I ^ 2)) = ε :=
  SymmetricAlgebra.squareZeroQuotientAugmentation_comp_mkₐ (R := ℤ) (M := ZMod 2)

example : ∀ x : SymmetricAlgebra ℤ (ZMod 2), εbar (Ideal.Quotient.mk _ x) = ε x :=
  SymmetricAlgebra.squareZeroQuotientAugmentation_mk (R := ℤ) (M := ZMod 2)

example : (TrivSqZeroExt.fstHom ℤ ℤ (ZMod 2)).comp (e).toAlgHom = εbar :=
  SymmetricAlgebra.fstHom_comp_squareZeroQuotientEquiv (R := ℤ) (M := ZMod 2)

example : ∀ m : ZMod 2,
  e (Ideal.Quotient.mk _ (SymmetricAlgebra.ι ℤ (ZMod 2) m)) = TrivSqZeroExt.inr m :=
  SymmetricAlgebra.squareZeroQuotientEquiv_mk_ι (R := ℤ) (M := ZMod 2)

example : ∀ r : ℤ,
  e (Ideal.Quotient.mk _ (algebraMap ℤ (SymmetricAlgebra ℤ (ZMod 2)) r)) = TrivSqZeroExt.inl r :=
  SymmetricAlgebra.squareZeroQuotientEquiv_mk_algebraMap (R := ℤ) (M := ZMod 2)

example : ∀ m : ZMod 2,
  εbar (Ideal.Quotient.mk _ (SymmetricAlgebra.ι ℤ (ZMod 2) m)) = 0 :=
  SymmetricAlgebra.squareZeroQuotientAugmentation_mk_ι (R := ℤ) (M := ZMod 2)

example : ∀ r : ℤ,
  εbar (Ideal.Quotient.mk _ (algebraMap ℤ (SymmetricAlgebra ℤ (ZMod 2)) r)) = r :=
  SymmetricAlgebra.squareZeroQuotientAugmentation_mk_algebraMap (R := ℤ) (M := ZMod 2)

example : ∀ f g : Q →ₐ[ℤ] ℤ,
  (∀ x : SymmetricAlgebra ℤ (ZMod 2),
    f (Ideal.Quotient.mk _ x) = g (Ideal.Quotient.mk _ x)) → f = g := by
  intro f g h
  apply Ideal.Quotient.algHom_ext
  exact AlgHom.ext h

example : ∀ (r : ℤ) (m : ZMod 2), r • m = (r : ZMod 2) * m := by
  intro r m
  exact zsmul_eq_mul m r

end

/- Finitely supported integer-valued functions on the natural numbers. -/
section

local notation "I" => SymmetricAlgebra.augmentationIdeal (R := ℤ) (M := ℕ →₀ ℤ)
local notation "Q" => SymmetricAlgebra ℤ (ℕ →₀ ℤ) ⧸ I ^ 2
local notation "ε" => SymmetricAlgebra.algebraMapInv (R := ℤ) (M := ℕ →₀ ℤ)
local notation "e" => SymmetricAlgebra.squareZeroQuotientEquiv (R := ℤ) (M := ℕ →₀ ℤ)
local notation "εbar" =>
  SymmetricAlgebra.squareZeroQuotientAugmentation (R := ℤ) (M := ℕ →₀ ℤ)

example : (SymmetricAlgebra ℤ (ℕ →₀ ℤ) ⧸ I ^ 2) ≃ₐ[ℤ] TrivSqZeroExt ℤ (ℕ →₀ ℤ) := e

example : (SymmetricAlgebra ℤ (ℕ →₀ ℤ) ⧸ I ^ 2) →ₐ[ℤ] ℤ := εbar

example : (εbar).comp (Ideal.Quotient.mkₐ ℤ (I ^ 2)) = ε :=
  SymmetricAlgebra.squareZeroQuotientAugmentation_comp_mkₐ (R := ℤ) (M := ℕ →₀ ℤ)

example : ∀ x : SymmetricAlgebra ℤ (ℕ →₀ ℤ), εbar (Ideal.Quotient.mk _ x) = ε x :=
  SymmetricAlgebra.squareZeroQuotientAugmentation_mk (R := ℤ) (M := ℕ →₀ ℤ)

example : (TrivSqZeroExt.fstHom ℤ ℤ (ℕ →₀ ℤ)).comp (e).toAlgHom = εbar :=
  SymmetricAlgebra.fstHom_comp_squareZeroQuotientEquiv (R := ℤ) (M := ℕ →₀ ℤ)

example : ∀ m : ℕ →₀ ℤ,
  e (Ideal.Quotient.mk _ (SymmetricAlgebra.ι ℤ (ℕ →₀ ℤ) m)) = TrivSqZeroExt.inr m :=
  SymmetricAlgebra.squareZeroQuotientEquiv_mk_ι (R := ℤ) (M := ℕ →₀ ℤ)

example : ∀ r : ℤ,
  e (Ideal.Quotient.mk _ (algebraMap ℤ (SymmetricAlgebra ℤ (ℕ →₀ ℤ)) r)) = TrivSqZeroExt.inl r :=
  SymmetricAlgebra.squareZeroQuotientEquiv_mk_algebraMap (R := ℤ) (M := ℕ →₀ ℤ)

example : ∀ m : ℕ →₀ ℤ,
  εbar (Ideal.Quotient.mk _ (SymmetricAlgebra.ι ℤ (ℕ →₀ ℤ) m)) = 0 :=
  SymmetricAlgebra.squareZeroQuotientAugmentation_mk_ι (R := ℤ) (M := ℕ →₀ ℤ)

example : ∀ r : ℤ,
  εbar (Ideal.Quotient.mk _ (algebraMap ℤ (SymmetricAlgebra ℤ (ℕ →₀ ℤ)) r)) = r :=
  SymmetricAlgebra.squareZeroQuotientAugmentation_mk_algebraMap (R := ℤ) (M := ℕ →₀ ℤ)

example : ∀ f g : Q →ₐ[ℤ] ℤ,
  (∀ x : SymmetricAlgebra ℤ (ℕ →₀ ℤ),
    f (Ideal.Quotient.mk _ x) = g (Ideal.Quotient.mk _ x)) → f = g := by
  intro f g h
  apply Ideal.Quotient.algHom_ext
  exact AlgHom.ext h

example : ∀ (r : ℤ) (f : ℕ →₀ ℤ) (n : ℕ), (r • f) n = r * f n := by
  intro r f n
  exact (Finsupp.smul_apply r f n).trans (zsmul_eq_mul (f n) r)

end

/- A lifted two-torsion module over the integers. -/
section

local notation "I" => SymmetricAlgebra.augmentationIdeal (R := ℤ) (M := ULift.{1, 0} (ZMod 2))
local notation "Q" => SymmetricAlgebra ℤ (ULift.{1, 0} (ZMod 2)) ⧸ I ^ 2
local notation "ε" => SymmetricAlgebra.algebraMapInv (R := ℤ) (M := ULift.{1, 0} (ZMod 2))
local notation "e" => SymmetricAlgebra.squareZeroQuotientEquiv (R := ℤ) (M := ULift.{1, 0} (ZMod 2))
local notation "εbar" =>
  SymmetricAlgebra.squareZeroQuotientAugmentation (R := ℤ) (M := ULift.{1, 0} (ZMod 2))

example : (SymmetricAlgebra ℤ (ULift.{1, 0} (ZMod 2)) ⧸ I ^ 2) ≃ₐ[ℤ] TrivSqZeroExt ℤ (ULift.{1, 0}
  (ZMod 2)) := e

example : (SymmetricAlgebra ℤ (ULift.{1, 0} (ZMod 2)) ⧸ I ^ 2) →ₐ[ℤ] ℤ := εbar

example : (εbar).comp (Ideal.Quotient.mkₐ ℤ (I ^ 2)) = ε :=
  SymmetricAlgebra.squareZeroQuotientAugmentation_comp_mkₐ (R := ℤ) (M := ULift.{1, 0} (ZMod 2))

example : ∀ x : SymmetricAlgebra ℤ (ULift.{1, 0} (ZMod 2)), εbar (Ideal.Quotient.mk _ x) = ε x :=
  SymmetricAlgebra.squareZeroQuotientAugmentation_mk (R := ℤ) (M := ULift.{1, 0} (ZMod 2))

example : (TrivSqZeroExt.fstHom ℤ ℤ (ULift.{1, 0} (ZMod 2))).comp (e).toAlgHom = εbar :=
  SymmetricAlgebra.fstHom_comp_squareZeroQuotientEquiv (R := ℤ) (M := ULift.{1, 0} (ZMod 2))

example : ∀ m : ULift.{1, 0} (ZMod 2),
  e (Ideal.Quotient.mk _ (SymmetricAlgebra.ι ℤ (ULift.{1, 0} (ZMod 2)) m)) = TrivSqZeroExt.inr m :=
  SymmetricAlgebra.squareZeroQuotientEquiv_mk_ι (R := ℤ) (M := ULift.{1, 0} (ZMod 2))

example : ∀ r : ℤ,
  e (Ideal.Quotient.mk _ (algebraMap ℤ (SymmetricAlgebra ℤ (ULift.{1, 0} (ZMod 2))) r)) =
    TrivSqZeroExt.inl r :=
  SymmetricAlgebra.squareZeroQuotientEquiv_mk_algebraMap (R := ℤ) (M := ULift.{1, 0} (ZMod 2))

example : ∀ m : ULift.{1, 0} (ZMod 2),
  εbar (Ideal.Quotient.mk _ (SymmetricAlgebra.ι ℤ (ULift.{1, 0} (ZMod 2)) m)) = 0 :=
  SymmetricAlgebra.squareZeroQuotientAugmentation_mk_ι (R := ℤ) (M := ULift.{1, 0} (ZMod 2))

example : ∀ r : ℤ,
  εbar (Ideal.Quotient.mk _ (algebraMap ℤ (SymmetricAlgebra ℤ (ULift.{1, 0} (ZMod 2))) r)) = r :=
  SymmetricAlgebra.squareZeroQuotientAugmentation_mk_algebraMap
    (R := ℤ) (M := ULift.{1, 0} (ZMod 2))

example : ∀ f g : Q →ₐ[ℤ] ℤ,
  (∀ x : SymmetricAlgebra ℤ (ULift.{1, 0} (ZMod 2)),
    f (Ideal.Quotient.mk _ x) = g (Ideal.Quotient.mk _ x)) → f = g := by
  intro f g h
  apply Ideal.Quotient.algHom_ext
  exact AlgHom.ext h

example : ∀ (r : ℤ) (m : ULift.{1, 0} (ZMod 2)), (r • m).down = r • m.down := by
  intro r m
  exact (ULift.moduleEquiv : ULift.{1, 0} (ZMod 2) ≃ₗ[ℤ] ZMod 2).map_smul r m

end

/- Two-torsion over a lifted integer coefficient ring. -/
section

local notation "I" => SymmetricAlgebra.augmentationIdeal (R := ULift.{1, 0} ℤ) (M := ZMod 2)
local notation "Q" => SymmetricAlgebra (ULift.{1, 0} ℤ) (ZMod 2) ⧸ I ^ 2
local notation "ε" => SymmetricAlgebra.algebraMapInv (R := ULift.{1, 0} ℤ) (M := ZMod 2)
local notation "e" => SymmetricAlgebra.squareZeroQuotientEquiv (R := ULift.{1, 0} ℤ) (M := ZMod 2)
local notation "εbar" =>
  SymmetricAlgebra.squareZeroQuotientAugmentation (R := ULift.{1, 0} ℤ) (M := ZMod 2)

example : (SymmetricAlgebra (ULift.{1, 0} ℤ) (ZMod 2) ⧸ I ^ 2) ≃ₐ[ULift.{1, 0} ℤ] TrivSqZeroExt
  (ULift.{1, 0} ℤ) (ZMod 2) := e

example : (SymmetricAlgebra (ULift.{1, 0} ℤ) (ZMod 2) ⧸ I ^ 2) →ₐ[ULift.{1, 0} ℤ] ULift.{1, 0} ℤ :=
  εbar

example : (εbar).comp (Ideal.Quotient.mkₐ (ULift.{1, 0} ℤ) (I ^ 2)) = ε :=
  SymmetricAlgebra.squareZeroQuotientAugmentation_comp_mkₐ (R := ULift.{1, 0} ℤ) (M := ZMod 2)

example : ∀ x : SymmetricAlgebra (ULift.{1, 0} ℤ) (ZMod 2), εbar (Ideal.Quotient.mk _ x) = ε x :=
  SymmetricAlgebra.squareZeroQuotientAugmentation_mk (R := ULift.{1, 0} ℤ) (M := ZMod 2)

example : (TrivSqZeroExt.fstHom (ULift.{1, 0} ℤ) (ULift.{1, 0} ℤ) (ZMod 2)).comp (e).toAlgHom = εbar
  :=
  SymmetricAlgebra.fstHom_comp_squareZeroQuotientEquiv (R := ULift.{1, 0} ℤ) (M := ZMod 2)

example : ∀ m : ZMod 2,
  e (Ideal.Quotient.mk _ (SymmetricAlgebra.ι (ULift.{1, 0} ℤ) (ZMod 2) m)) = TrivSqZeroExt.inr m :=
  SymmetricAlgebra.squareZeroQuotientEquiv_mk_ι (R := ULift.{1, 0} ℤ) (M := ZMod 2)

example : ∀ r : ULift.{1, 0} ℤ,
  e (Ideal.Quotient.mk _ (algebraMap (ULift.{1, 0} ℤ) (SymmetricAlgebra (ULift.{1, 0} ℤ) (ZMod 2))
    r)) = TrivSqZeroExt.inl r :=
  SymmetricAlgebra.squareZeroQuotientEquiv_mk_algebraMap (R := ULift.{1, 0} ℤ) (M := ZMod 2)

example : ∀ m : ZMod 2,
  εbar (Ideal.Quotient.mk _ (SymmetricAlgebra.ι (ULift.{1, 0} ℤ) (ZMod 2) m)) = 0 :=
  SymmetricAlgebra.squareZeroQuotientAugmentation_mk_ι (R := ULift.{1, 0} ℤ) (M := ZMod 2)

example : ∀ r : ULift.{1, 0} ℤ,
  εbar (Ideal.Quotient.mk _ (algebraMap (ULift.{1, 0} ℤ) (SymmetricAlgebra (ULift.{1, 0} ℤ) (ZMod
    2)) r)) = r :=
  SymmetricAlgebra.squareZeroQuotientAugmentation_mk_algebraMap (R := ULift.{1, 0} ℤ) (M := ZMod 2)

example : ∀ f g : Q →ₐ[ULift.{1, 0} ℤ] ULift.{1, 0} ℤ,
  (∀ x : SymmetricAlgebra (ULift.{1, 0} ℤ) (ZMod 2),
    f (Ideal.Quotient.mk _ x) = g (Ideal.Quotient.mk _ x)) → f = g := by
  intro f g h
  apply Ideal.Quotient.algHom_ext
  exact AlgHom.ext h

example : ∀ (r : ULift.{1, 0} ℤ) (m : ZMod 2), r • m = r.down • m := by
  intro r m
  exact ULift.smul_def r m

end

/- The regular module over the integers modulo four. -/
section

local notation "I" => SymmetricAlgebra.augmentationIdeal (R := ZMod 4) (M := ZMod 4)
local notation "Q" => SymmetricAlgebra (ZMod 4) (ZMod 4) ⧸ I ^ 2
local notation "ε" => SymmetricAlgebra.algebraMapInv (R := ZMod 4) (M := ZMod 4)
local notation "e" => SymmetricAlgebra.squareZeroQuotientEquiv (R := ZMod 4) (M := ZMod 4)
local notation "εbar" =>
  SymmetricAlgebra.squareZeroQuotientAugmentation (R := ZMod 4) (M := ZMod 4)

example : (SymmetricAlgebra (ZMod 4) (ZMod 4) ⧸ I ^ 2) ≃ₐ[ZMod 4] TrivSqZeroExt (ZMod 4) (ZMod 4) :=
  e

example : (SymmetricAlgebra (ZMod 4) (ZMod 4) ⧸ I ^ 2) →ₐ[ZMod 4] ZMod 4 := εbar

example : (εbar).comp (Ideal.Quotient.mkₐ (ZMod 4) (I ^ 2)) = ε :=
  SymmetricAlgebra.squareZeroQuotientAugmentation_comp_mkₐ (R := ZMod 4) (M := ZMod 4)

example : ∀ x : SymmetricAlgebra (ZMod 4) (ZMod 4), εbar (Ideal.Quotient.mk _ x) = ε x :=
  SymmetricAlgebra.squareZeroQuotientAugmentation_mk (R := ZMod 4) (M := ZMod 4)

example : (TrivSqZeroExt.fstHom (ZMod 4) (ZMod 4) (ZMod 4)).comp (e).toAlgHom = εbar :=
  SymmetricAlgebra.fstHom_comp_squareZeroQuotientEquiv (R := ZMod 4) (M := ZMod 4)

example : ∀ m : ZMod 4,
  e (Ideal.Quotient.mk _ (SymmetricAlgebra.ι (ZMod 4) (ZMod 4) m)) = TrivSqZeroExt.inr m :=
  SymmetricAlgebra.squareZeroQuotientEquiv_mk_ι (R := ZMod 4) (M := ZMod 4)

example : ∀ r : ZMod 4,
  e (Ideal.Quotient.mk _ (algebraMap (ZMod 4) (SymmetricAlgebra (ZMod 4) (ZMod 4)) r)) =
    TrivSqZeroExt.inl r :=
  SymmetricAlgebra.squareZeroQuotientEquiv_mk_algebraMap (R := ZMod 4) (M := ZMod 4)

example : ∀ m : ZMod 4,
  εbar (Ideal.Quotient.mk _ (SymmetricAlgebra.ι (ZMod 4) (ZMod 4) m)) = 0 :=
  SymmetricAlgebra.squareZeroQuotientAugmentation_mk_ι (R := ZMod 4) (M := ZMod 4)

example : ∀ r : ZMod 4,
  εbar (Ideal.Quotient.mk _ (algebraMap (ZMod 4) (SymmetricAlgebra (ZMod 4) (ZMod 4)) r)) = r :=
  SymmetricAlgebra.squareZeroQuotientAugmentation_mk_algebraMap (R := ZMod 4) (M := ZMod 4)

example : ∀ f g : Q →ₐ[ZMod 4] ZMod 4,
  (∀ x : SymmetricAlgebra (ZMod 4) (ZMod 4),
    f (Ideal.Quotient.mk _ x) = g (Ideal.Quotient.mk _ x)) → f = g := by
  intro f g h
  apply Ideal.Quotient.algHom_ext
  exact AlgHom.ext h

example : ∀ (r m : ZMod 4), r • m = r * m := by
  intro r m
  exact smul_eq_mul r m

end

end
