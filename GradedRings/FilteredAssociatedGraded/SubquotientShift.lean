/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GradedRings.FilteredAssociatedGraded.Shift
public import GradedRings.FilteredAssociatedGraded.Subquotient

/-!
# Translation and subquotients of filtered associated graded modules

For a fixed submodule of an integer-filtered module, translation commutes with
the equivalence from the quotient of the associated graded by the induced
submodule's image to the associated graded of the filtered quotient. The
comparison between the two source quotients is induced independently by the
translation equivalence using `Submodule.Quotient.equiv`.

All maps are linear over the same quotient Rees algebra. Translation retains
the original representatives and sends shifted degree `n` to degree `n + d`;
no normalization or boundedness assumption is imposed.

## References

* Mathlib's `Submodule.Quotient.equiv`, with its public quotient-representative
  formula, supplies the equivalence between the source quotients.
-/

@[expose] public section

universe u v

namespace Ideal.IntFiltration

/-- Translation commutes with the subquotient equivalence, using the quotient
comparison induced by the translation equivalence of the middle associated
graded modules. The submodule is unchanged, and shifted degree `n` corresponds
to original degree `n + d`. -/
theorem shiftEquiv_subquotientEquiv
    {R : Type u} [CommRing R] {I : Ideal R}
    {M : Type v} [AddCommGroup M] [Module R M]
    (F : I.IntFiltration M) (S : Submodule R M) (d : ℤ) :
    let C : Type u :=
      (reesAlgebra I) ⧸ I.map (algebraMap R (reesAlgebra I))
    let Fd : I.IntFiltration M := F.shift d
    let FS : I.IntFiltration S := F.comap S.subtype
    let FQ : I.IntFiltration (M ⧸ S) := F.image S.mkQ
    let FSd : I.IntFiltration S := Fd.comap S.subtype
    let FQd : I.IntFiltration (M ⧸ S) := Fd.image S.mkQ
    let uF : FS.AssociatedGraded →ₗ[C] F.AssociatedGraded :=
      FS.map F S.subtype (fun (_ : ℤ) => le_rfl)
    let ud : FSd.AssociatedGraded →ₗ[C] Fd.AssociatedGraded :=
      FSd.map Fd S.subtype (fun (_ : ℤ) => le_rfl)
    let EM : Fd.AssociatedGraded ≃ₗ[C] F.AssociatedGraded :=
      F.shiftEquiv d
    let EQ : FQd.AssociatedGraded ≃ₗ[C] FQ.AssociatedGraded :=
      FQ.shiftEquiv d
    let Pd : Submodule C Fd.AssociatedGraded := LinearMap.range ud
    let P0 : Submodule C F.AssociatedGraded := LinearMap.range uF
    let hP : Pd.map EM.toLinearMap = P0 :=
      FS.shiftEquiv_range_map F S.subtype (fun (_ : ℤ) => le_rfl) d
    let Ebar : (Fd.AssociatedGraded ⧸ Pd) ≃ₗ[C]
        (F.AssociatedGraded ⧸ P0) :=
      Submodule.Quotient.equiv Pd P0 EM hP
    let κd : (Fd.AssociatedGraded ⧸ Pd) ≃ₗ[C] FQd.AssociatedGraded :=
      Fd.subquotientEquiv S
    let κ0 : (F.AssociatedGraded ⧸ P0) ≃ₗ[C] FQ.AssociatedGraded :=
      F.subquotientEquiv S
    EQ.toLinearMap.comp κd.toLinearMap =
      κ0.toLinearMap.comp Ebar.toLinearMap := by
  intro C Fd FS FQ FSd FQd uF ud EM EQ Pd P0 hP Ebar κd κ0
  have hprojection :
      EQ.toLinearMap.comp
          (Fd.map FQd S.mkQ
            (fun (_ : ℤ) => Submodule.map_le_iff_le_comap.mp le_rfl)) =
        (F.map FQ S.mkQ
          (fun (_ : ℤ) => Submodule.map_le_iff_le_comap.mp le_rfl)).comp
            EM.toLinearMap :=
    F.shiftEquiv_map (F.image S.mkQ) S.mkQ
      (fun (_ : ℤ) => Submodule.map_le_iff_le_comap.mp le_rfl) d
  have hEbar (z : Fd.AssociatedGraded) :
      Ebar (Submodule.Quotient.mk z) = Submodule.Quotient.mk (EM z) := by
    calc
      Ebar (Submodule.Quotient.mk z) =
          Pd.mapQ P0 EM.toLinearMap (Submodule.map_le_iff_le_comap.mp hP.le)
            (Submodule.Quotient.mk z) :=
        Submodule.Quotient.equiv_apply Pd P0 EM hP (Submodule.Quotient.mk z)
      _ = Submodule.Quotient.mk (EM z) :=
        Submodule.mapQ_apply Pd P0 EM.toLinearMap z
  apply LinearMap.ext
  intro q
  obtain ⟨z, rfl⟩ := Pd.mkQ_surjective q
  change EQ (κd (Submodule.Quotient.mk z)) =
    κ0 (Ebar (Submodule.Quotient.mk z))
  calc
    EQ (κd (Submodule.Quotient.mk z)) =
        EQ (Fd.map FQd S.mkQ
          (fun (_ : ℤ) => Submodule.map_le_iff_le_comap.mp le_rfl) z) :=
      congrArg (EQ : FQd.AssociatedGraded → FQ.AssociatedGraded)
        (Fd.subquotientEquiv_mk S z)
    _ = F.map FQ S.mkQ
        (fun (_ : ℤ) => Submodule.map_le_iff_le_comap.mp le_rfl) (EM z) :=
      LinearMap.congr_fun hprojection z
    _ = κ0 (Submodule.Quotient.mk (EM z)) :=
      (F.subquotientEquiv_mk S (EM z)).symm
    _ = κ0 (Ebar (Submodule.Quotient.mk z)) :=
      congrArg (κ0 : (F.AssociatedGraded ⧸ P0) → FQ.AssociatedGraded)
        (hEbar z).symm

end Ideal.IntFiltration
