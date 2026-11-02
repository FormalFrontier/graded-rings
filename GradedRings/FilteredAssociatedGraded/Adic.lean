/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GradedRings.FilteredAssociatedGraded
public import Mathlib.RingTheory.Filtration
import Lean.Elab.Tactic.Omega

/-!
# Natural and ideal-adic integer filtrations

A natural-number filtration extends to the integers by taking its zeroth stage in every
nonpositive degree. This extension is the least integer filtration bounded below by its
natural stages. Its nonnegative graded pieces retain the same quotient representatives,
and its negative graded pieces are subsingletons.

The ideal-adic integer filtration is obtained from the natural filtration with stages
`I ^ q • ⊤`. All modules and linear equivalences use the original coefficient ring.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe uR uM

namespace Ideal

variable {R : Type uR} [CommRing R]

namespace Filtration

variable {M : Type uM} [AddCommGroup M] [Module R M] {I : Ideal R}

/-- Extend a natural filtration to the integers, keeping its zeroth stage in every
nonpositive degree. -/
def toIntFiltration (F : I.Filtration M) : I.IntFiltration M where
  N n := F.N n.toNat
  antitone := by
    intro i j hij
    exact F.antitone (by omega)
  smul_le n :=
    (F.smul_le n.toNat).trans (F.antitone (by omega))

/-- The integer extension is given by the natural stage indexed by `Int.toNat`. -/
@[simp]
theorem toIntFiltration_N (F : I.Filtration M) (n : ℤ) :
    F.toIntFiltration.N n = F.N n.toNat :=
  rfl

/-- Natural degrees of the integer extension are the original stages. -/
theorem toIntFiltration_N_nat (F : I.Filtration M) (q : ℕ) :
    F.toIntFiltration.N (q : ℤ) = F.N q :=
  rfl

/-- The integer extension preserves the zeroth stage, even when it is proper. -/
theorem toIntFiltration_N_zero (F : I.Filtration M) :
    F.toIntFiltration.N 0 = F.N 0 :=
  rfl

/-- All nonpositive stages of the integer extension equal the original zeroth stage. -/
theorem toIntFiltration_N_of_nonpos (F : I.Filtration M) (n : ℤ) (hn : n ≤ 0) :
    F.toIntFiltration.N n = F.N 0 := by
  rw [toIntFiltration_N, show n.toNat = 0 by omega]

/-- Membership in an integer stage is membership in the corresponding natural stage. -/
theorem mem_toIntFiltration_N (F : I.Filtration M) (n : ℤ) (x : M) :
    x ∈ F.toIntFiltration.N n ↔ x ∈ F.N n.toNat :=
  Iff.rfl

/-- Membership in a natural degree of the integer extension is unchanged. -/
theorem mem_toIntFiltration_N_nat (F : I.Filtration M) (q : ℕ) (x : M) :
    x ∈ F.toIntFiltration.N (q : ℤ) ↔ x ∈ F.N q :=
  Iff.rfl

/-- Membership in a nonpositive stage is membership in the original zeroth stage. -/
theorem mem_toIntFiltration_N_of_nonpos (F : I.Filtration M) (n : ℤ)
    (hn : n ≤ 0) (x : M) :
    x ∈ F.toIntFiltration.N n ↔ x ∈ F.N 0 := by
  rw [toIntFiltration_N_of_nonpos F n hn]

/-- The integer extension is the least integer filtration containing the natural stages. -/
theorem toIntFiltration_N_le_iff (F : I.Filtration M) (G : I.IntFiltration M) :
    (∀ n : ℤ, F.toIntFiltration.N n ≤ G.N n) ↔
      ∀ q : ℕ, F.N q ≤ G.N (q : ℤ) := by
  constructor
  · intro h q
    simpa only [toIntFiltration_N_nat] using h (q : ℤ)
  · intro h n
    rw [toIntFiltration_N]
    exact (h n.toNat).trans (G.antitone (by omega))

/-- In every natural degree, the integer extension has the original quotient as its
original-ring linear graded piece, with the same representatives in both directions. -/
def gradedPieceToIntEquiv (F : I.Filtration M) (q : ℕ) :
    F.toIntFiltration.GradedPiece (q : ℤ) ≃ₗ[R]
      (F.N q) ⧸ (F.N (q + 1)).comap (F.N q).subtype :=
  LinearEquiv.refl R _

/-- The natural-degree equivalence sends a quotient class to the class of the same element. -/
@[simp]
theorem gradedPieceToIntEquiv_apply_mk (F : I.Filtration M) (q : ℕ) (x : F.N q) :
    F.gradedPieceToIntEquiv q (Submodule.Quotient.mk x) =
      (Submodule.Quotient.mk x : (F.N q) ⧸ (F.N (q + 1)).comap (F.N q).subtype) :=
  rfl

/-- The inverse natural-degree equivalence also preserves quotient representatives. -/
@[simp]
theorem gradedPieceToIntEquiv_symm_apply_mk (F : I.Filtration M) (q : ℕ)
    (x : F.N q) :
    (F.gradedPieceToIntEquiv q).symm (Submodule.Quotient.mk x) =
      (Submodule.Quotient.mk x : F.toIntFiltration.GradedPiece (q : ℤ)) :=
  rfl

/-- In negative degree the submodule defining the quotient is the whole stage. -/
theorem toIntFiltration_comap_eq_top_of_neg (F : I.Filtration M) (n : ℤ)
    (hn : n < 0) :
    (F.toIntFiltration.N (n + 1)).comap (F.toIntFiltration.N n).subtype = ⊤ := by
  have hstage : F.toIntFiltration.N n = F.toIntFiltration.N (n + 1) := by
    rw [toIntFiltration_N_of_nonpos F n (le_of_lt hn),
      toIntFiltration_N_of_nonpos F (n + 1) (by omega)]
  rw [← hstage]
  apply top_unique
  intro x _
  exact x.property

/-- Negative graded pieces of the integer extension of a natural filtration are
subsingletons. -/
theorem toIntFiltration_gradedPiece_subsingleton (F : I.Filtration M) (n : ℤ)
    (hn : n < 0) : Subsingleton (F.toIntFiltration.GradedPiece n) := by
  change Subsingleton ((F.toIntFiltration.N n) ⧸
    (F.toIntFiltration.N (n + 1)).comap (F.toIntFiltration.N n).subtype)
  rw [toIntFiltration_comap_eq_top_of_neg F n hn]
  infer_instance

end Filtration

variable (I : Ideal R) (M : Type uM) [AddCommGroup M] [Module R M]

/-- The integer ideal-adic filtration, with stage `I ^ n.toNat • ⊤`. -/
def adicIntFiltration : I.IntFiltration M :=
  (I.stableFiltration (⊤ : Submodule R M)).toIntFiltration

/-- The stages of the integer ideal-adic filtration are powers of the ideal acting on `⊤`. -/
@[simp]
theorem adicIntFiltration_N (n : ℤ) :
    (I.adicIntFiltration M).N n = I ^ n.toNat • (⊤ : Submodule R M) :=
  rfl

/-- Natural degrees of the integer ideal-adic filtration have the usual adic stages. -/
theorem adicIntFiltration_N_nat (q : ℕ) :
    (I.adicIntFiltration M).N (q : ℤ) = I ^ q • (⊤ : Submodule R M) :=
  rfl

/-- Nonpositive stages of the integer ideal-adic filtration are the whole module. -/
theorem adicIntFiltration_N_of_nonpos (n : ℤ) (hn : n ≤ 0) :
    (I.adicIntFiltration M).N n = ⊤ := by
  rw [adicIntFiltration_N, show n.toNat = 0 by omega, pow_zero, one_smul]

/-- The zeroth stage of the integer ideal-adic filtration is the whole module. -/
theorem adicIntFiltration_N_zero : (I.adicIntFiltration M).N 0 = ⊤ :=
  adicIntFiltration_N_of_nonpos I M 0 le_rfl

/-- Membership in an integer adic stage is membership in the corresponding ideal power. -/
theorem mem_adicIntFiltration_N (n : ℤ) (x : M) :
    x ∈ (I.adicIntFiltration M).N n ↔ x ∈ I ^ n.toNat • (⊤ : Submodule R M) :=
  Iff.rfl

/-- Membership in a natural degree of the integer adic filtration has the usual formula. -/
theorem mem_adicIntFiltration_N_nat (q : ℕ) (x : M) :
    x ∈ (I.adicIntFiltration M).N (q : ℤ) ↔ x ∈ I ^ q • (⊤ : Submodule R M) :=
  Iff.rfl

/-- Every element lies in each nonpositive stage of the integer ideal-adic filtration. -/
theorem mem_adicIntFiltration_N_of_nonpos (n : ℤ) (hn : n ≤ 0) (x : M) :
    x ∈ (I.adicIntFiltration M).N n := by
  rw [adicIntFiltration_N_of_nonpos I M n hn]
  trivial

/-- In every natural degree, the integer ideal-adic graded piece is the quotient of two
successive ideal-power stages, with the same representatives and the original ring action. -/
def adicGradedPieceEquiv (q : ℕ) :
    (I.adicIntFiltration M).GradedPiece (q : ℤ) ≃ₗ[R]
      ↥(I ^ q • (⊤ : Submodule R M)) ⧸
        (I ^ (q + 1) • (⊤ : Submodule R M)).comap
          (I ^ q • (⊤ : Submodule R M)).subtype :=
  (I.stableFiltration (⊤ : Submodule R M)).gradedPieceToIntEquiv q

/-- The ideal-adic equivalence sends each quotient class to the class of the same element. -/
@[simp]
theorem adicGradedPieceEquiv_apply_mk (q : ℕ) (x : ↥(I ^ q • (⊤ : Submodule R M))) :
    I.adicGradedPieceEquiv M q (Submodule.Quotient.mk x) =
      (Submodule.Quotient.mk x :
        ↥(I ^ q • (⊤ : Submodule R M)) ⧸
          (I ^ (q + 1) • (⊤ : Submodule R M)).comap
            (I ^ q • (⊤ : Submodule R M)).subtype) :=
  rfl

/-- The inverse ideal-adic equivalence also preserves quotient representatives. -/
@[simp]
theorem adicGradedPieceEquiv_symm_apply_mk (q : ℕ) (x : ↥(I ^ q • (⊤ : Submodule R M))) :
    (I.adicGradedPieceEquiv M q).symm (Submodule.Quotient.mk x) =
      (Submodule.Quotient.mk x : (I.adicIntFiltration M).GradedPiece (q : ℤ)) :=
  rfl

/-- Negative graded pieces of the integer ideal-adic filtration are subsingletons. -/
theorem adicIntFiltration_gradedPiece_subsingleton (n : ℤ) (hn : n < 0) :
    Subsingleton ((I.adicIntFiltration M).GradedPiece n) :=
  (I.stableFiltration (⊤ : Submodule R M)).toIntFiltration_gradedPiece_subsingleton n hn

end Ideal
