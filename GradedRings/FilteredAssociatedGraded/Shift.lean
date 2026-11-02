/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GradedRings.FilteredAssociatedGraded.Map
public import GradedRings.FilteredAssociatedGraded.Coefficients

/-!
# Integer translations of filtered associated graded modules

Translating an integer filtration by `d` replaces its stage `n` by its stage
`n + d`. The corresponding piece equivalence preserves representatives. On the
whole associated graded, the direct sum of these quotient equivalences followed
by reindexing is linear for the canonical quotient Rees actions. It sends shifted
degree `n` to original degree `n + d`.

The zero, composition and inverse identities use `LinearEquiv.cast` on the
family of associated graded modules. No normalization, boundedness, finiteness,
exhaustivity or separatedness assumption is needed.

## References

* Mathlib's `Submodule.quotEquivOfEq`, `DirectSum.congrLinearEquiv`,
  `DirectSum.lequivCongrLeft` and indexed `LinearEquiv.cast`.
* The public monomial action and homogeneous decomposition of the quotient
  Rees algebra, as used for maps of integer-filtered associated gradeds.
-/

@[expose] public section

universe u v

open scoped DirectSum

namespace Ideal.IntFiltration

variable {R : Type u} [CommRing R] {I : Ideal R}
variable {M : Type v} [AddCommGroup M] [Module R M]
variable (F : I.IntFiltration M)

/-- Translate an integer filtration, with shifted stage `n` equal to stage `n + d`. -/
def shift (d : ℤ) : I.IntFiltration M where
  N n := F.N (n + d)
  antitone := by
    intro a b h
    apply F.antitone
    omega
  smul_le n := by
    simpa only [add_assoc, add_comm d 1] using F.smul_le (n + d)

/-- The stages of a translated filtration. -/
@[simp]
theorem shift_N (d n : ℤ) : (F.shift d).N n = F.N (n + d) := rfl

/-- Membership in a translated stage is membership in the original shifted degree. -/
theorem mem_shift (d n : ℤ) (m : M) :
    m ∈ (F.shift d).N n ↔ m ∈ F.N (n + d) := Iff.rfl

/-- The next-stage denominator of a translated piece, in the same ambient stage. -/
theorem shift_nextStage (d n : ℤ) :
    (F.shift d).nextStage n = F.nextStage (n + d) := by
  change (F.N ((n + 1) + d)).comap (F.N (n + d)).subtype =
    (F.N ((n + d) + 1)).comap (F.N (n + d)).subtype
  congr 2
  omega

/-- Translation by zero leaves the filtration unchanged. -/
@[simp]
theorem shift_zero : F.shift 0 = F := by
  apply Ideal.IntFiltration.ext
  intro n
  exact congrArg F.N (add_zero n)

/-- Successive translations add their parameters. -/
@[simp]
theorem shift_shift (d e : ℤ) : (F.shift d).shift e = F.shift (d + e) := by
  apply Ideal.IntFiltration.ext
  intro n
  change F.N ((n + e) + d) = F.N (n + (d + e))
  congr 1
  omega

/-- Opposite translations cancel. -/
theorem shift_shift_neg (d : ℤ) : (F.shift d).shift (-d) = F := by
  rw [shift_shift, add_neg_cancel, shift_zero]

/-- Translation identifies graded pieces by retaining their stage representatives. -/
def shiftGradedPieceEquiv (d n : ℤ) :
    (F.shift d).GradedPiece n ≃ₗ[R] F.GradedPiece (n + d) :=
  Submodule.quotEquivOfEq _ _ (F.shift_nextStage d n)

/-- The piece equivalence preserves quotient representatives. -/
@[simp]
theorem shiftGradedPieceEquiv_cl (d n : ℤ) (m : F.N (n + d)) :
    F.shiftGradedPieceEquiv d n
      (@DFunLike.coe (F.N (n + d) →ₗ[R] (F.shift d).GradedPiece n)
        (F.N (n + d)) (fun _ => (F.shift d).GradedPiece n) LinearMap.instFunLike
        ((F.shift d).cl n) m) = F.cl (n + d) m := rfl

/-- The inverse piece equivalence preserves quotient representatives. -/
@[simp]
theorem shiftGradedPieceEquiv_symm_cl (d n : ℤ) (m : F.N (n + d)) :
    (F.shiftGradedPieceEquiv d n).symm (F.cl (n + d) m) = (F.shift d).cl n m := rfl

private def shiftR (d : ℤ) : (F.shift d).AssociatedGraded ≃ₗ[R] F.AssociatedGraded :=
  (DirectSum.congrLinearEquiv (fun n => F.shiftGradedPieceEquiv d n)).trans
    (DirectSum.lequivCongrLeft R (M := F.GradedPiece) (Equiv.addRight d).symm).symm

private theorem shiftR_inclusion (d n : ℤ) (a : (F.shift d).GradedPiece n) :
    shiftR F d ((F.shift d).inclusion n a) =
      F.inclusion (n + d) (F.shiftGradedPieceEquiv d n a) := by
  change (DirectSum.lequivCongrLeft R (M := F.GradedPiece) (Equiv.addRight d).symm).symm
    (DirectSum.lmap (fun n => (F.shiftGradedPieceEquiv d n).toLinearMap)
      (DirectSum.lof R ℤ (F.shift d).GradedPiece n a)) = _
  rw [DirectSum.lmap_lof]
  exact DirectSum.lequivCongrLeft_symm_lof R

private theorem shiftR_single (d n : ℤ) (m : (F.shift d).N n) :
    shiftR F d ((F.shift d).single n m) = F.single (n + d) ⟨(m : M), m.property⟩ := by
  rw [(F.shift d).single_apply, shiftR_inclusion]
  rfl

private theorem component_shiftR (d n : ℤ) (z : (F.shift d).AssociatedGraded) :
    F.component (n + d) (shiftR F d z) =
      F.shiftGradedPieceEquiv d n ((F.shift d).component n z) := by
  exact congrArg (fun x : ⨁ k : ℤ, F.GradedPiece (k + d) => x n)
    ((DirectSum.lequivCongrLeft R (M := F.GradedPiece)
      (Equiv.addRight d).symm).apply_symm_apply
        (DirectSum.congrLinearEquiv (fun k => F.shiftGradedPieceEquiv d k) z))

private theorem single_congr {n k : ℤ} (h : n = k)
    (x : F.N n) (y : F.N k) (hxy : (x : M) = (y : M)) :
    F.single n x = F.single k y := by
  subst k
  congr 1
  exact Subtype.ext hxy

local notation "Q" => R ⧸ I
local notation "B" => reesAlgebra I
local notation "J" => I.map (algebraMap R B)
local notation "C" => B ⧸ J

private theorem shiftR_monomial_smul (d : ℤ) (p : ℕ) (a : ↥(I ^ p))
    (z : (F.shift d).AssociatedGraded) :
    shiftR F d ((Ideal.Quotient.mk J (reesAlgebra.monomial I p a) : C) • z) =
      (Ideal.Quotient.mk J (reesAlgebra.monomial I p a) : C) • shiftR F d z := by
  have h :
      (shiftR F d).toLinearMap.comp
          ((F.shift d).reesQuotientRepresentation
            (Ideal.Quotient.mk J (reesAlgebra.monomial I p a))) =
        (F.reesQuotientRepresentation
          (Ideal.Quotient.mk J (reesAlgebra.monomial I p a))).comp
            (shiftR F d).toLinearMap := by
    apply (F.shift d).linearMap_ext
    intro n m
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      reesQuotientRepresentation_apply, monomial_smul_single, shiftR_single]
    exact single_congr F (by omega) _ _ rfl
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe,
    reesQuotientRepresentation_apply] using LinearMap.congr_fun h z

private theorem shiftR_smul (d : ℤ) (c : C) (z : (F.shift d).AssociatedGraded) :
    shiftR F d (c • z) = c • shiftR F d z := by
  induction c using DirectSum.Decomposition.inductionOn
      (reesAlgebra.quotientHomogeneousComponent I) with
  | zero =>
      change shiftR F d ((F.shift d).reesQuotientRepresentation 0 z) =
        F.reesQuotientRepresentation 0 (shiftR F d z)
      have hS : (F.shift d).reesQuotientRepresentation (0 : C) =
          (0 : Module.End R (F.shift d).AssociatedGraded) :=
        _root_.map_zero (F.shift d).reesQuotientRepresentation
      have hF : F.reesQuotientRepresentation (0 : C) =
          (0 : Module.End R F.AssociatedGraded) :=
        _root_.map_zero F.reesQuotientRepresentation
      rw [hS, hF]
      exact (shiftR F d).map_zero
  | homogeneous c =>
      obtain ⟨p, hp, hpc⟩ :=
        (reesAlgebra.mem_quotientHomogeneousComponent_iff I _ (c : C)).mp c.property
      obtain ⟨a, ha⟩ := (reesAlgebra.mem_homogeneousComponent_iff I _ p).mp hp
      simpa only [ha, hpc] using shiftR_monomial_smul F d _ a z
  | add c c' hc hc' => simp only [add_smul, _root_.map_add, hc, hc']

/-- Reindex a translated associated graded, linearly for its quotient Rees action. -/
noncomputable def shiftEquiv (d : ℤ) :
    (F.shift d).AssociatedGraded ≃ₗ[C] F.AssociatedGraded :=
  let L := DirectSum.lequivCongrLeft R (M := F.GradedPiece) (Equiv.addRight d).symm
  let U := (DirectSum.congrLinearEquiv (fun n => F.shiftGradedPieceEquiv d n)).trans L.symm
  { toAddEquiv := U.toAddEquiv
    map_smul' := by
      intro c z
      exact shiftR_smul F d c z }

/-- The additive equivalence is the direct sum of the piece equivalences followed by reindexing. -/
theorem shiftEquiv_toAddEquiv (d : ℤ) :
    (F.shiftEquiv d).toAddEquiv =
      ((DirectSum.congrLinearEquiv (fun n => F.shiftGradedPieceEquiv d n)).trans
        (DirectSum.lequivCongrLeft R (M := F.GradedPiece)
          (Equiv.addRight d).symm).symm).toAddEquiv := rfl

/-- The inverse function is the inverse of the same original-scalar direct-sum equivalence. -/
theorem shiftEquiv_invFun (d : ℤ) :
    (F.shiftEquiv d).invFun =
      ((DirectSum.congrLinearEquiv (fun n => F.shiftGradedPieceEquiv d n)).trans
        (DirectSum.lequivCongrLeft R (M := F.GradedPiece)
          (Equiv.addRight d).symm).symm).invFun := rfl

/-- Restricting the translation equivalence to the original scalars preserves its construction. -/
theorem shiftEquiv_restrictScalars (d : ℤ) :
    (F.shiftEquiv d).restrictScalars R =
      (DirectSum.congrLinearEquiv (fun n => F.shiftGradedPieceEquiv d n)).trans
        (DirectSum.lequivCongrLeft R (M := F.GradedPiece)
          (Equiv.addRight d).symm).symm := by
  ext z
  rfl

/-- Restriction to residue coefficients preserves the forward function. -/
theorem shiftEquiv_restrictScalars_quotient_apply (d : ℤ)
    (z : (F.shift d).AssociatedGraded) :
    (F.shiftEquiv d).restrictScalars Q z =
      ((DirectSum.congrLinearEquiv (fun n => F.shiftGradedPieceEquiv d n)).trans
        (DirectSum.lequivCongrLeft R (M := F.GradedPiece)
          (Equiv.addRight d).symm).symm) z := rfl

/-- Restriction to residue coefficients preserves the inverse function. -/
theorem shiftEquiv_restrictScalars_quotient_symm_apply (d : ℤ)
    (y : F.AssociatedGraded) :
    ((F.shiftEquiv d).restrictScalars Q).symm y =
      ((DirectSum.congrLinearEquiv (fun n => F.shiftGradedPieceEquiv d n)).trans
        (DirectSum.lequivCongrLeft R (M := F.GradedPiece)
          (Equiv.addRight d).symm).symm).symm y := rfl

/-- Further restriction of the residue-linear equivalence agrees with original-scalar reindexing. -/
theorem shiftEquiv_restrictScalars_quotient_restrictScalars (d : ℤ) :
    ((F.shiftEquiv d).restrictScalars Q).restrictScalars R =
      (DirectSum.congrLinearEquiv (fun n => F.shiftGradedPieceEquiv d n)).trans
        (DirectSum.lequivCongrLeft R (M := F.GradedPiece)
          (Equiv.addRight d).symm).symm := by
  ext z
  rfl

/-- A homogeneous piece moves from shifted degree `n` to degree `n + d`. -/
@[simp]
theorem shiftEquiv_inclusion (d n : ℤ) (a : (F.shift d).GradedPiece n) :
    F.shiftEquiv d ((F.shift d).inclusion n a) =
      F.inclusion (n + d) (F.shiftGradedPieceEquiv d n a) := by
  exact shiftR_inclusion F d n a

/-- The inverse reindexing returns a piece to its shifted degree. -/
@[simp]
theorem shiftEquiv_symm_inclusion (d n : ℤ) (b : F.GradedPiece (n + d)) :
    (F.shiftEquiv d).symm (F.inclusion (n + d) b) =
      (F.shift d).inclusion n ((F.shiftGradedPieceEquiv d n).symm b) := by
  apply (F.shiftEquiv d).injective
  rw [LinearEquiv.apply_symm_apply, shiftEquiv_inclusion, LinearEquiv.apply_symm_apply]

/-- Translation preserves the ambient representative of each homogeneous class. -/
@[simp]
theorem shiftEquiv_single (d n : ℤ) (m : F.N (n + d)) :
    F.shiftEquiv d
      (@DFunLike.coe (F.N (n + d) →ₗ[R] (F.shift d).AssociatedGraded)
        (F.N (n + d)) (fun _ => (F.shift d).AssociatedGraded) LinearMap.instFunLike
        ((F.shift d).single n) m) = F.single (n + d) m := by
  exact shiftR_single F d n m

/-- Inverse translation preserves the ambient representative of each homogeneous class. -/
@[simp]
theorem shiftEquiv_symm_single (d n : ℤ) (m : F.N (n + d)) :
    (F.shiftEquiv d).symm (F.single (n + d) m) = (F.shift d).single n m := by
  apply (F.shiftEquiv d).injective
  erw [LinearEquiv.apply_symm_apply, shiftEquiv_single]

/-- Components of the translated sum are compared by the piece equivalence. -/
@[simp]
theorem component_shiftEquiv (d n : ℤ) (z : (F.shift d).AssociatedGraded) :
    F.component (n + d) (F.shiftEquiv d z) =
      F.shiftGradedPieceEquiv d n ((F.shift d).component n z) := by
  exact component_shiftR F d n z

/-- Components of the inverse reindexing are compared by the inverse piece equivalence. -/
@[simp]
theorem component_shiftEquiv_symm (d n : ℤ) (y : F.AssociatedGraded) :
    (F.shift d).component n ((F.shiftEquiv d).symm y) =
      (F.shiftGradedPieceEquiv d n).symm (F.component (n + d) y) := by
  apply (F.shiftGradedPieceEquiv d n).injective
  rw [← component_shiftEquiv, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

/-- A residue-class scalar is carried to the original scalar action on the target. -/
theorem shiftEquiv_quotient_mk_smul (d : ℤ) (r : R) (z : (F.shift d).AssociatedGraded) :
    F.shiftEquiv d ((Ideal.Quotient.mk I r : Q) • z) = r • F.shiftEquiv d z := by
  rw [quotient_mk_smul]
  exact ((F.shiftEquiv d).restrictScalars R).map_smul r z

/-- The original scalar action agrees with the residue-class scalar after translation. -/
theorem shiftEquiv_smul_eq_quotient_mk_smul (d : ℤ) (r : R)
    (z : (F.shift d).AssociatedGraded) :
    r • F.shiftEquiv d z = (Ideal.Quotient.mk I r : Q) • F.shiftEquiv d z :=
  (F.quotient_mk_smul r (F.shiftEquiv d z)).symm

private theorem cast_single {H K : I.IntFiltration M} (h : H = K)
    (n : ℤ) (m : H.N n) :
    LinearEquiv.cast (R := C) (M := fun L : I.IntFiltration M => L.AssociatedGraded) h
        (H.single n m) =
      K.single n ⟨(m : M), by cases h; exact m.property⟩ := by
  cases h
  rfl

/-- Translation by zero is the canonical comparison along `shift_zero`. -/
theorem shiftEquiv_zero :
    F.shiftEquiv 0 =
      LinearEquiv.cast (R := C) (M := fun K : I.IntFiltration M => K.AssociatedGraded)
        F.shift_zero := by
  apply LinearEquiv.restrictScalars_injective R
  apply LinearEquiv.toLinearMap_injective
  apply (F.shift 0).linearMap_ext
  intro n m
  change F.shiftEquiv 0 ((F.shift 0).single n m) =
    LinearEquiv.cast (R := C) (M := fun K : I.IntFiltration M => K.AssociatedGraded)
      F.shift_zero ((F.shift 0).single n m)
  erw [F.shiftEquiv_single 0 n m, cast_single]
  exact single_congr F (add_zero n) _ _ rfl

/-- Successive translation equivalences compose according to addition of shifts. -/
theorem shiftEquiv_trans (d e : ℤ) :
    ((F.shift d).shiftEquiv e).trans (F.shiftEquiv d) =
      (LinearEquiv.cast (R := C) (M := fun K : I.IntFiltration M => K.AssociatedGraded)
        (F.shift_shift d e)).trans (F.shiftEquiv (d + e)) := by
  apply LinearEquiv.restrictScalars_injective R
  apply LinearEquiv.toLinearMap_injective
  apply ((F.shift d).shift e).linearMap_ext
  intro n m
  change F.shiftEquiv d ((F.shift d).shiftEquiv e (((F.shift d).shift e).single n m)) =
    F.shiftEquiv (d + e)
      (LinearEquiv.cast (R := C) (M := fun K : I.IntFiltration M => K.AssociatedGraded)
        (F.shift_shift d e) (((F.shift d).shift e).single n m))
  erw [(F.shift d).shiftEquiv_single e n m, F.shiftEquiv_single d (n + e) m]
  rw [cast_single]
  erw [shiftEquiv_single]
  exact single_congr F (by omega) _ _ rfl

/-- Inverse translation is translation by the opposite shift after the canonical comparison. -/
theorem shiftEquiv_symm (d : ℤ) :
    (F.shiftEquiv d).symm =
      (LinearEquiv.cast (R := C) (M := fun K : I.IntFiltration M => K.AssociatedGraded)
        (F.shift_shift_neg d)).symm.trans ((F.shift d).shiftEquiv (-d)) := by
  let E := LinearEquiv.cast (R := C)
    (M := fun K : I.IntFiltration M => K.AssociatedGraded) (F.shift_shift_neg d)
  have h :
      ((F.shiftEquiv d).symm.restrictScalars R).toLinearMap.comp
          (E.restrictScalars R).toLinearMap =
        ((E.symm.trans ((F.shift d).shiftEquiv (-d))).restrictScalars R).toLinearMap.comp
          (E.restrictScalars R).toLinearMap := by
    apply ((F.shift d).shift (-d)).linearMap_ext
    intro n m
    change (F.shiftEquiv d).symm (E (((F.shift d).shift (-d)).single n m)) =
      (F.shift d).shiftEquiv (-d) (E.symm (E (((F.shift d).shift (-d)).single n m)))
    rw [LinearEquiv.symm_apply_apply]
    apply (F.shiftEquiv d).injective
    erw [LinearEquiv.apply_symm_apply, (F.shift d).shiftEquiv_single (-d) n m,
      F.shiftEquiv_single d (n + -d) m]
    dsimp only [E]
    rw [cast_single]
    exact single_congr F (by omega) _ _ rfl
  apply LinearEquiv.ext
  intro y
  obtain ⟨x, rfl⟩ := E.surjective y
  exact LinearMap.congr_fun h x

end Ideal.IntFiltration
