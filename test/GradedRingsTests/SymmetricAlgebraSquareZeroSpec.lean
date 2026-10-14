/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import GradedRings.SymmetricAlgebraSquareZero
import Mathlib.Algebra.Module.PUnit
import Mathlib.Algebra.Module.ULift
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.CategoryTheory.CommSq
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.ZMod.Basic

/-!
# Spectra of first-order symmetric algebras

The symmetric algebra modulo the square of its augmentation ideal and the trivial
square-zero extension have isomorphic spectra. Their structure and augmentation
maps give two commutative-square statements over the spectrum of a common-universe
lift of the base ring.

The quotient augmentation is constructed independently by the quotient universal
property. Compatibility with the structure maps follows from the algebra equivalence's
`commutes` identity; compatibility with augmentation instead uses its first-coordinate
characterization.

## Limitations

The generic square, section, and closed-immersion contracts below have private proofs.
The unlifted base spectrum is a separate object in the base ring's universe; no
change-of-universe comparison is constructed here.

## References

The algebra equivalence and its first-coordinate characterization are supplied by
`GradedRings.SymmetricAlgebraSquareZero`. Spectrum, quotient, and lift constructions
are those of Mathlib.
-/

open CategoryTheory AlgebraicGeometry
open scoped TrivSqZeroExt

noncomputable section

namespace SymmetricAlgebra

universe uR uM

variable {R : Type uR} {M : Type uM}
variable [CommRing R] [AddCommGroup M] [Module R M]

local notation "Q" =>
  SymmetricAlgebra R M ⧸ (SymmetricAlgebra.augmentationIdeal (R := R) (M := M)) ^ 2
local notation "T" => TrivSqZeroExt R M

/-- Evaluation at zero descended through the square of the augmentation ideal. -/
private noncomputable def quotientAugmentation : Q →ₐ[R] R :=
  Ideal.Quotient.liftₐ
    ((SymmetricAlgebra.augmentationIdeal (R := R) (M := M)) ^ 2)
    (SymmetricAlgebra.algebraMapInv (R := R) (M := M)) fun x hx =>
      (SymmetricAlgebra.mem_augmentationIdeal_iff (R := R) (M := M) x).mp
        ((Ideal.pow_le_self
          (I := SymmetricAlgebra.augmentationIdeal (R := R) (M := M))
          (by decide : (2 : ℕ) ≠ 0)) hx)

/-- The quotient's structure map from the lifted base ring. -/
private def quotientStructure : (ULift.{uM, uR} R) →+* Q :=
  (algebraMap R Q).comp (ULift.ringEquiv : (ULift.{uM, uR} R) ≃+* R).toRingHom

/-- The extension's structure map from the lifted base ring. -/
private def extensionStructure : (ULift.{uM, uR} R) →+* T :=
  (algebraMap R T).comp (ULift.ringEquiv : (ULift.{uM, uR} R) ≃+* R).toRingHom

/-- The quotient augmentation with values in the lifted base ring. -/
private noncomputable def quotientAugmentationLift : Q →+* (ULift.{uM, uR} R) :=
  (ULift.ringEquiv : (ULift.{uM, uR} R) ≃+* R).symm.toRingHom.comp
    (quotientAugmentation (R := R) (M := M)).toRingHom

/-- The first-coordinate augmentation with values in the lifted base ring. -/
private def extensionAugmentationLift : T →+* (ULift.{uM, uR} R) :=
  (ULift.ringEquiv : (ULift.{uM, uR} R) ≃+* R).symm.toRingHom.comp
    (TrivSqZeroExt.fstHom R R M).toRingHom

/-- The spectrum isomorphism induced contravariantly by the algebra equivalence. -/
private noncomputable def quotientSpectrumIso :
    AlgebraicGeometry.Spec (CommRingCat.of T) ≅
      AlgebraicGeometry.Spec (CommRingCat.of Q) :=
  CategoryTheory.Functor.mapIso AlgebraicGeometry.Scheme.Spec
    (RingEquiv.toCommRingCatIso
      (SymmetricAlgebra.squareZeroQuotientEquiv (R := R) (M := M)).toRingEquiv).op

/-- Projection from the quotient spectrum to the lifted base spectrum. -/
private noncomputable def quotientProjection :
    AlgebraicGeometry.Spec (CommRingCat.of Q) ⟶
      AlgebraicGeometry.Spec (CommRingCat.of (ULift.{uM, uR} R)) :=
  AlgebraicGeometry.Spec.map
    (CommRingCat.ofHom (quotientStructure (R := R) (M := M)))

/-- Projection from the extension spectrum to the lifted base spectrum. -/
private noncomputable def extensionProjection :
    AlgebraicGeometry.Spec (CommRingCat.of T) ⟶
      AlgebraicGeometry.Spec (CommRingCat.of (ULift.{uM, uR} R)) :=
  AlgebraicGeometry.Spec.map
    (CommRingCat.ofHom (extensionStructure (R := R) (M := M)))

/-- The section induced by the independently descended quotient augmentation. -/
private noncomputable def quotientSection :
    AlgebraicGeometry.Spec (CommRingCat.of (ULift.{uM, uR} R)) ⟶
      AlgebraicGeometry.Spec (CommRingCat.of Q) :=
  AlgebraicGeometry.Spec.map
    (CommRingCat.ofHom (quotientAugmentationLift (R := R) (M := M)))

/-- The section induced by first-coordinate augmentation. -/
private noncomputable def extensionSection :
    AlgebraicGeometry.Spec (CommRingCat.of (ULift.{uM, uR} R)) ⟶
      AlgebraicGeometry.Spec (CommRingCat.of T) :=
  AlgebraicGeometry.Spec.map
    (CommRingCat.ofHom (extensionAugmentationLift (R := R) (M := M)))

/-- The section identities for the two algebraic augmentations. -/
private def augmentationSectionIdentities : Prop :=
  (quotientAugmentationLift (R := R) (M := M)).comp
      (quotientStructure (R := R) (M := M)) = RingHom.id (ULift.{uM, uR} R) ∧
    (extensionAugmentationLift (R := R) (M := M)).comp
      (extensionStructure (R := R) (M := M)) = RingHom.id (ULift.{uM, uR} R)

/-- Compatibility with structure maps, governed by `AlgEquiv.commutes`. -/
private noncomputable def structureCompatibility : Prop :=
  (SymmetricAlgebra.squareZeroQuotientEquiv (R := R) (M := M)).toRingEquiv.toRingHom.comp
      (quotientStructure (R := R) (M := M)) =
    extensionStructure (R := R) (M := M)

/-- Compatibility with augmentation, governed by `squareZeroQuotientEquiv_fst`. -/
private noncomputable def augmentationCompatibility : Prop :=
  (extensionAugmentationLift (R := R) (M := M)).comp
      (SymmetricAlgebra.squareZeroQuotientEquiv (R := R) (M := M)).toRingEquiv.toRingHom =
    quotientAugmentationLift (R := R) (M := M)

/-- The spectrum morphism induced by the quotient ring homomorphism. -/
private noncomputable def quotientEmbedding :
    AlgebraicGeometry.Spec (CommRingCat.of Q) ⟶
      AlgebraicGeometry.Spec (CommRingCat.of (SymmetricAlgebra R M)) :=
  AlgebraicGeometry.Spec.map (CommRingCat.ofHom
    (Ideal.Quotient.mk ((SymmetricAlgebra.augmentationIdeal (R := R) (M := M)) ^ 2)))

/-- The closed-immersion assertion for the quotient spectrum morphism. -/
private noncomputable def quotientEmbeddingClosed : Prop :=
  AlgebraicGeometry.IsClosedImmersion (quotientEmbedding (R := R) (M := M))

/-- The extension spectrum mapped into the symmetric-algebra spectrum. -/
private noncomputable def extensionEmbedding :
    AlgebraicGeometry.Spec (CommRingCat.of T) ⟶
      AlgebraicGeometry.Spec (CommRingCat.of (SymmetricAlgebra R M)) :=
  (quotientSpectrumIso (R := R) (M := M)).hom ≫
    quotientEmbedding (R := R) (M := M)

/-- The base spectrum without a universe lift. -/
private def unliftedBaseSpectrum : AlgebraicGeometry.Scheme.{uR} :=
  AlgebraicGeometry.Spec (CommRingCat.of R)

/-- The independent quotient augmentation agrees with the first coordinate of the equivalence. -/
private theorem quotientAugmentation_eq_fst :
    quotientAugmentation (R := R) (M := M) =
      (TrivSqZeroExt.fstHom R R M).comp
        (squareZeroQuotientEquiv (R := R) (M := M)).toAlgHom := by
  apply AlgHom.ext
  intro q
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
  exact (squareZeroQuotientEquiv_fst (R := R) (M := M) x).symm

/-- Structure compatibility is the scalar identity for the algebra equivalence. -/
private theorem structureCompatibility_proof :
    structureCompatibility (R := R) (M := M) := by
  apply RingHom.ext
  intro r
  change squareZeroQuotientEquiv (R := R) (M := M)
    (algebraMap R Q r.down) = algebraMap R T r.down
  exact (squareZeroQuotientEquiv (R := R) (M := M)).commutes r.down

/-- Augmentation compatibility uses the full quotient algebra-homomorphism identity. -/
private theorem augmentationCompatibility_proof :
    augmentationCompatibility (R := R) (M := M) := by
  apply RingHom.ext
  intro q
  change ULift.up ((TrivSqZeroExt.fstHom R R M)
    (squareZeroQuotientEquiv (R := R) (M := M) q)) =
      ULift.up (quotientAugmentation (R := R) (M := M) q)
  exact congrArg ULift.up
    (congrArg (fun f : Q →ₐ[R] R => f q)
      (quotientAugmentation_eq_fst (R := R) (M := M))).symm

/-- Both augmentations retract their respective structure maps over the lifted base. -/
private theorem augmentationSectionIdentities_proof :
    augmentationSectionIdentities (R := R) (M := M) := by
  constructor
  · apply RingHom.ext
    intro r
    change ULift.up (quotientAugmentation (R := R) (M := M)
      (algebraMap R Q r.down)) = r
    exact congrArg ULift.up
      ((quotientAugmentation (R := R) (M := M)).commutes r.down)
  · apply RingHom.ext
    intro r
    change ULift.up ((TrivSqZeroExt.fstHom R R M)
      (algebraMap R T r.down)) = r
    exact congrArg ULift.up ((TrivSqZeroExt.fstHom R R M).commutes r.down)

/-- The spectrum isomorphism uses the forward ring equivalence, not its inverse. -/
private theorem quotientSpectrumIso_hom :
    (quotientSpectrumIso (R := R) (M := M)).hom =
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom
        (squareZeroQuotientEquiv (R := R) (M := M)).toRingEquiv.toRingHom) := rfl

/-- The projections commute with the spectrum isomorphism. -/
private theorem projectionCommSq :
    CommSq (quotientSpectrumIso (R := R) (M := M)).hom
      (extensionProjection (R := R) (M := M))
      (quotientProjection (R := R) (M := M))
      (𝟙 (AlgebraicGeometry.Spec (CommRingCat.of (ULift.{uM, uR} R)))) := by
  constructor
  rw [Category.comp_id]
  change AlgebraicGeometry.Spec.map (CommRingCat.ofHom
    (squareZeroQuotientEquiv (R := R) (M := M)).toRingEquiv.toRingHom) ≫
    AlgebraicGeometry.Spec.map (CommRingCat.ofHom
      (quotientStructure (R := R) (M := M))) =
    AlgebraicGeometry.Spec.map (CommRingCat.ofHom
      (extensionStructure (R := R) (M := M)))
  simpa only [← AlgebraicGeometry.Spec.map_comp, ← CommRingCat.ofHom_comp] using
    congrArg
      (fun f : (ULift.{uM, uR} R) →+* T =>
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom f))
      (structureCompatibility_proof (R := R) (M := M))

/-- The independently descended zero section commutes with the spectrum isomorphism. -/
private theorem zeroSectionCommSq :
    CommSq (extensionSection (R := R) (M := M))
      (𝟙 (AlgebraicGeometry.Spec (CommRingCat.of (ULift.{uM, uR} R))))
      (quotientSpectrumIso (R := R) (M := M)).hom
      (quotientSection (R := R) (M := M)) := by
  constructor
  rw [Category.id_comp]
  change AlgebraicGeometry.Spec.map (CommRingCat.ofHom
    (extensionAugmentationLift (R := R) (M := M))) ≫
    AlgebraicGeometry.Spec.map (CommRingCat.ofHom
      (squareZeroQuotientEquiv (R := R) (M := M)).toRingEquiv.toRingHom) =
    AlgebraicGeometry.Spec.map (CommRingCat.ofHom
      (quotientAugmentationLift (R := R) (M := M)))
  simpa only [← AlgebraicGeometry.Spec.map_comp, ← CommRingCat.ofHom_comp] using
    congrArg
      (fun f : Q →+* (ULift.{uM, uR} R) =>
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom f))
      (augmentationCompatibility_proof (R := R) (M := M))

/-- The quotient zero section is a section of its projection. -/
private theorem quotientSection_projection :
    quotientSection (R := R) (M := M) ≫ quotientProjection (R := R) (M := M) =
      𝟙 (AlgebraicGeometry.Spec (CommRingCat.of (ULift.{uM, uR} R))) := by
  change AlgebraicGeometry.Spec.map (CommRingCat.ofHom
    (quotientAugmentationLift (R := R) (M := M))) ≫
    AlgebraicGeometry.Spec.map (CommRingCat.ofHom
      (quotientStructure (R := R) (M := M))) = _
  rw [← AlgebraicGeometry.Spec.map_comp, ← CommRingCat.ofHom_comp,
    (augmentationSectionIdentities_proof (R := R) (M := M)).1,
    CommRingCat.ofHom_id, AlgebraicGeometry.Spec.map_id]

/-- The extension zero section is a section of its projection. -/
private theorem extensionSection_projection :
    extensionSection (R := R) (M := M) ≫ extensionProjection (R := R) (M := M) =
      𝟙 (AlgebraicGeometry.Spec (CommRingCat.of (ULift.{uM, uR} R))) := by
  change AlgebraicGeometry.Spec.map (CommRingCat.ofHom
    (extensionAugmentationLift (R := R) (M := M))) ≫
    AlgebraicGeometry.Spec.map (CommRingCat.ofHom
      (extensionStructure (R := R) (M := M))) = _
  rw [← AlgebraicGeometry.Spec.map_comp, ← CommRingCat.ofHom_comp,
    (augmentationSectionIdentities_proof (R := R) (M := M)).2,
    CommRingCat.ofHom_id, AlgebraicGeometry.Spec.map_id]

/-- The extension embedding is the spectrum map of the quotient composite. -/
private theorem quotientComposite :
    extensionEmbedding (R := R) (M := M) =
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom
        ((squareZeroQuotientEquiv (R := R) (M := M)).toRingEquiv.toRingHom.comp
            (Ideal.Quotient.mk
              ((SymmetricAlgebra.augmentationIdeal (R := R) (M := M)) ^ 2)))) := by
  change AlgebraicGeometry.Spec.map (CommRingCat.ofHom
    (squareZeroQuotientEquiv (R := R) (M := M)).toRingEquiv.toRingHom) ≫
    AlgebraicGeometry.Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk
        ((SymmetricAlgebra.augmentationIdeal (R := R) (M := M)) ^ 2))) = _
  rw [← AlgebraicGeometry.Spec.map_comp, ← CommRingCat.ofHom_comp]

-- The spectrum map of the quotient homomorphism is a closed immersion.
example :
    quotientEmbeddingClosed (R := R) (M := M) := by
  exact AlgebraicGeometry.IsClosedImmersion.spec_of_quotient_mk
    (R := CommRingCat.of (SymmetricAlgebra R M))
    ((SymmetricAlgebra.augmentationIdeal (R := R) (M := M)) ^ 2)

-- Arbitrary commutative rings and modules in independent universes.
example : AlgebraicGeometry.Spec (CommRingCat.of T) ≅
    AlgebraicGeometry.Spec (CommRingCat.of Q) :=
  CategoryTheory.Functor.mapIso AlgebraicGeometry.Scheme.Spec
    (RingEquiv.toCommRingCatIso
      (SymmetricAlgebra.squareZeroQuotientEquiv (R := R) (M := M)).toRingEquiv).op

-- The zero ring and its zero module.
example :
    AlgebraicGeometry.Spec (CommRingCat.of (TrivSqZeroExt ((PUnit : Type)) ((PUnit : Type)))) ≅
      AlgebraicGeometry.Spec (CommRingCat.of (SymmetricAlgebra ((PUnit : Type)) ((PUnit : Type)) ⧸
      (SymmetricAlgebra.augmentationIdeal (R := (PUnit : Type)) (M := (PUnit : Type))) ^ 2)) :=
  CategoryTheory.Functor.mapIso AlgebraicGeometry.Scheme.Spec
    (RingEquiv.toCommRingCatIso
      (SymmetricAlgebra.squareZeroQuotientEquiv
        (R := (PUnit : Type)) (M := (PUnit : Type))).toRingEquiv).op

-- Proofs of the same generic contracts for this ring and module.
example :
  CommSq (quotientSpectrumIso (R := (PUnit : Type)) (M := (PUnit : Type))).hom
    (extensionProjection (R := (PUnit : Type)) (M := (PUnit : Type)))
    (quotientProjection (R := (PUnit : Type)) (M := (PUnit : Type)))
    (𝟙 (AlgebraicGeometry.Spec (CommRingCat.of (ULift.{0, 0} ((PUnit : Type)))))) :=
  projectionCommSq
    (R := (PUnit : Type)) (M := (PUnit : Type))

example :
  CommSq (extensionSection (R := (PUnit : Type)) (M := (PUnit : Type)))
    (𝟙 (AlgebraicGeometry.Spec (CommRingCat.of (ULift.{0, 0} ((PUnit : Type))))))
    (quotientSpectrumIso (R := (PUnit : Type)) (M := (PUnit : Type))).hom
    (quotientSection (R := (PUnit : Type)) (M := (PUnit : Type))) :=
  zeroSectionCommSq
    (R := (PUnit : Type)) (M := (PUnit : Type))

example : structureCompatibility
    (R := (PUnit : Type)) (M := (PUnit : Type)) :=
  structureCompatibility_proof
    (R := (PUnit : Type)) (M := (PUnit : Type))

example : augmentationCompatibility
    (R := (PUnit : Type)) (M := (PUnit : Type)) :=
  augmentationCompatibility_proof
    (R := (PUnit : Type)) (M := (PUnit : Type))

example : augmentationSectionIdentities
    (R := (PUnit : Type)) (M := (PUnit : Type)) :=
  augmentationSectionIdentities_proof
    (R := (PUnit : Type)) (M := (PUnit : Type))

example : extensionEmbedding (R := (PUnit : Type)) (M := (PUnit : Type)) =
    AlgebraicGeometry.Spec.map (CommRingCat.ofHom
      ((squareZeroQuotientEquiv
        (R := (PUnit : Type)) (M := (PUnit : Type))).toRingEquiv.toRingHom.comp
          (Ideal.Quotient.mk
            ((augmentationIdeal
              (R := (PUnit : Type)) (M := (PUnit : Type))) ^ 2)))) :=
  quotientComposite
    (R := (PUnit : Type)) (M := (PUnit : Type))

example : quotientEmbeddingClosed
    (R := (PUnit : Type)) (M := (PUnit : Type)) := by
  exact AlgebraicGeometry.IsClosedImmersion.spec_of_quotient_mk
    (R := CommRingCat.of (SymmetricAlgebra ((PUnit : Type)) ((PUnit : Type))))
    ((augmentationIdeal (R := (PUnit : Type)) (M := (PUnit : Type))) ^ 2)

-- The integers with the zero module.
example :
    AlgebraicGeometry.Spec (CommRingCat.of (TrivSqZeroExt (ℤ) ((PUnit : Type)))) ≅
      AlgebraicGeometry.Spec (CommRingCat.of (SymmetricAlgebra (ℤ) ((PUnit : Type)) ⧸
      (SymmetricAlgebra.augmentationIdeal (R := ℤ) (M := (PUnit : Type))) ^ 2)) :=
  CategoryTheory.Functor.mapIso AlgebraicGeometry.Scheme.Spec
    (RingEquiv.toCommRingCatIso
      (SymmetricAlgebra.squareZeroQuotientEquiv (R := ℤ) (M := (PUnit : Type))).toRingEquiv).op

-- Proofs of the same generic contracts for this ring and module.
example :
  CommSq (quotientSpectrumIso (R := ℤ) (M := (PUnit : Type))).hom
    (extensionProjection (R := ℤ) (M := (PUnit : Type)))
    (quotientProjection (R := ℤ) (M := (PUnit : Type)))
    (𝟙 (AlgebraicGeometry.Spec (CommRingCat.of (ULift.{0, 0} (ℤ))))) :=
  projectionCommSq
    (R := ℤ) (M := (PUnit : Type))

example :
  CommSq (extensionSection (R := ℤ) (M := (PUnit : Type)))
    (𝟙 (AlgebraicGeometry.Spec (CommRingCat.of (ULift.{0, 0} (ℤ)))))
    (quotientSpectrumIso (R := ℤ) (M := (PUnit : Type))).hom
    (quotientSection (R := ℤ) (M := (PUnit : Type))) :=
  zeroSectionCommSq
    (R := ℤ) (M := (PUnit : Type))

example : structureCompatibility
    (R := ℤ) (M := (PUnit : Type)) :=
  structureCompatibility_proof
    (R := ℤ) (M := (PUnit : Type))

example : augmentationCompatibility
    (R := ℤ) (M := (PUnit : Type)) :=
  augmentationCompatibility_proof
    (R := ℤ) (M := (PUnit : Type))

example : augmentationSectionIdentities
    (R := ℤ) (M := (PUnit : Type)) :=
  augmentationSectionIdentities_proof
    (R := ℤ) (M := (PUnit : Type))

example : extensionEmbedding (R := ℤ) (M := (PUnit : Type)) =
    AlgebraicGeometry.Spec.map (CommRingCat.ofHom
      ((squareZeroQuotientEquiv
        (R := ℤ) (M := (PUnit : Type))).toRingEquiv.toRingHom.comp
          (Ideal.Quotient.mk
            ((augmentationIdeal
              (R := ℤ) (M := (PUnit : Type))) ^ 2)))) :=
  quotientComposite
    (R := ℤ) (M := (PUnit : Type))

example : quotientEmbeddingClosed
    (R := ℤ) (M := (PUnit : Type)) := by
  exact AlgebraicGeometry.IsClosedImmersion.spec_of_quotient_mk
    (R := CommRingCat.of (SymmetricAlgebra (ℤ) ((PUnit : Type))))
    ((augmentationIdeal (R := ℤ) (M := (PUnit : Type))) ^ 2)

-- The integers acting on a torsion module.
example :
    AlgebraicGeometry.Spec (CommRingCat.of (TrivSqZeroExt (ℤ) (ZMod 2))) ≅
      AlgebraicGeometry.Spec (CommRingCat.of (SymmetricAlgebra (ℤ) (ZMod 2) ⧸
      (SymmetricAlgebra.augmentationIdeal (R := ℤ) (M := ZMod 2)) ^ 2)) :=
  CategoryTheory.Functor.mapIso AlgebraicGeometry.Scheme.Spec
    (RingEquiv.toCommRingCatIso
      (SymmetricAlgebra.squareZeroQuotientEquiv (R := ℤ) (M := ZMod 2)).toRingEquiv).op

-- Proofs of the same generic contracts for this ring and module.
example :
  CommSq (quotientSpectrumIso (R := ℤ) (M := ZMod 2)).hom
    (extensionProjection (R := ℤ) (M := ZMod 2))
    (quotientProjection (R := ℤ) (M := ZMod 2))
    (𝟙 (AlgebraicGeometry.Spec (CommRingCat.of (ULift.{0, 0} (ℤ))))) :=
  projectionCommSq
    (R := ℤ) (M := ZMod 2)

example :
  CommSq (extensionSection (R := ℤ) (M := ZMod 2))
    (𝟙 (AlgebraicGeometry.Spec (CommRingCat.of (ULift.{0, 0} (ℤ)))))
    (quotientSpectrumIso (R := ℤ) (M := ZMod 2)).hom
    (quotientSection (R := ℤ) (M := ZMod 2)) :=
  zeroSectionCommSq
    (R := ℤ) (M := ZMod 2)

example : structureCompatibility
    (R := ℤ) (M := ZMod 2) :=
  structureCompatibility_proof
    (R := ℤ) (M := ZMod 2)

example : augmentationCompatibility
    (R := ℤ) (M := ZMod 2) :=
  augmentationCompatibility_proof
    (R := ℤ) (M := ZMod 2)

example : augmentationSectionIdentities
    (R := ℤ) (M := ZMod 2) :=
  augmentationSectionIdentities_proof
    (R := ℤ) (M := ZMod 2)

example : extensionEmbedding (R := ℤ) (M := ZMod 2) =
    AlgebraicGeometry.Spec.map (CommRingCat.ofHom
      ((squareZeroQuotientEquiv
        (R := ℤ) (M := ZMod 2)).toRingEquiv.toRingHom.comp
          (Ideal.Quotient.mk
            ((augmentationIdeal
              (R := ℤ) (M := ZMod 2)) ^ 2)))) :=
  quotientComposite
    (R := ℤ) (M := ZMod 2)

example : quotientEmbeddingClosed
    (R := ℤ) (M := ZMod 2) := by
  exact AlgebraicGeometry.IsClosedImmersion.spec_of_quotient_mk
    (R := CommRingCat.of (SymmetricAlgebra (ℤ) (ZMod 2)))
    ((augmentationIdeal (R := ℤ) (M := ZMod 2)) ^ 2)

-- The countably generated free module over the integers.
example :
    AlgebraicGeometry.Spec (CommRingCat.of (TrivSqZeroExt (ℤ) (ℕ →₀ ℤ))) ≅
      AlgebraicGeometry.Spec (CommRingCat.of (SymmetricAlgebra (ℤ) (ℕ →₀ ℤ) ⧸
      (SymmetricAlgebra.augmentationIdeal (R := ℤ) (M := ℕ →₀ ℤ)) ^ 2)) :=
  CategoryTheory.Functor.mapIso AlgebraicGeometry.Scheme.Spec
    (RingEquiv.toCommRingCatIso
      (SymmetricAlgebra.squareZeroQuotientEquiv (R := ℤ) (M := ℕ →₀ ℤ)).toRingEquiv).op

-- Proofs of the same generic contracts for this ring and module.
example :
  CommSq (quotientSpectrumIso (R := ℤ) (M := ℕ →₀ ℤ)).hom
    (extensionProjection (R := ℤ) (M := ℕ →₀ ℤ))
    (quotientProjection (R := ℤ) (M := ℕ →₀ ℤ))
    (𝟙 (AlgebraicGeometry.Spec (CommRingCat.of (ULift.{0, 0} (ℤ))))) :=
  projectionCommSq
    (R := ℤ) (M := ℕ →₀ ℤ)

example :
  CommSq (extensionSection (R := ℤ) (M := ℕ →₀ ℤ))
    (𝟙 (AlgebraicGeometry.Spec (CommRingCat.of (ULift.{0, 0} (ℤ)))))
    (quotientSpectrumIso (R := ℤ) (M := ℕ →₀ ℤ)).hom
    (quotientSection (R := ℤ) (M := ℕ →₀ ℤ)) :=
  zeroSectionCommSq
    (R := ℤ) (M := ℕ →₀ ℤ)

example : structureCompatibility
    (R := ℤ) (M := ℕ →₀ ℤ) :=
  structureCompatibility_proof
    (R := ℤ) (M := ℕ →₀ ℤ)

example : augmentationCompatibility
    (R := ℤ) (M := ℕ →₀ ℤ) :=
  augmentationCompatibility_proof
    (R := ℤ) (M := ℕ →₀ ℤ)

example : augmentationSectionIdentities
    (R := ℤ) (M := ℕ →₀ ℤ) :=
  augmentationSectionIdentities_proof
    (R := ℤ) (M := ℕ →₀ ℤ)

example : extensionEmbedding (R := ℤ) (M := ℕ →₀ ℤ) =
    AlgebraicGeometry.Spec.map (CommRingCat.ofHom
      ((squareZeroQuotientEquiv
        (R := ℤ) (M := ℕ →₀ ℤ)).toRingEquiv.toRingHom.comp
          (Ideal.Quotient.mk
            ((augmentationIdeal
              (R := ℤ) (M := ℕ →₀ ℤ)) ^ 2)))) :=
  quotientComposite
    (R := ℤ) (M := ℕ →₀ ℤ)

example : quotientEmbeddingClosed
    (R := ℤ) (M := ℕ →₀ ℤ) := by
  exact AlgebraicGeometry.IsClosedImmersion.spec_of_quotient_mk
    (R := CommRingCat.of (SymmetricAlgebra (ℤ) (ℕ →₀ ℤ)))
    ((augmentationIdeal (R := ℤ) (M := ℕ →₀ ℤ)) ^ 2)

-- A torsion module in a higher universe than its base ring.
example :
    AlgebraicGeometry.Spec (CommRingCat.of (TrivSqZeroExt (ℤ) (ULift.{1, 0} (ZMod 2)))) ≅
      AlgebraicGeometry.Spec (CommRingCat.of (SymmetricAlgebra (ℤ) (ULift.{1, 0} (ZMod 2)) ⧸
      (SymmetricAlgebra.augmentationIdeal (R := ℤ) (M := ULift.{1, 0} (ZMod 2))) ^ 2)) :=
  CategoryTheory.Functor.mapIso AlgebraicGeometry.Scheme.Spec
    (RingEquiv.toCommRingCatIso
      (SymmetricAlgebra.squareZeroQuotientEquiv
        (R := ℤ) (M := ULift.{1, 0} (ZMod 2))).toRingEquiv).op

-- Proofs of the same generic contracts for this ring and module.
example :
  CommSq (quotientSpectrumIso (R := ℤ) (M := ULift.{1, 0} (ZMod 2))).hom
    (extensionProjection (R := ℤ) (M := ULift.{1, 0} (ZMod 2)))
    (quotientProjection (R := ℤ) (M := ULift.{1, 0} (ZMod 2)))
    (𝟙 (AlgebraicGeometry.Spec (CommRingCat.of (ULift.{1, 0} (ℤ))))) :=
  projectionCommSq
    (R := ℤ) (M := ULift.{1, 0} (ZMod 2))

example :
  CommSq (extensionSection (R := ℤ) (M := ULift.{1, 0} (ZMod 2)))
    (𝟙 (AlgebraicGeometry.Spec (CommRingCat.of (ULift.{1, 0} (ℤ)))))
    (quotientSpectrumIso (R := ℤ) (M := ULift.{1, 0} (ZMod 2))).hom
    (quotientSection (R := ℤ) (M := ULift.{1, 0} (ZMod 2))) :=
  zeroSectionCommSq
    (R := ℤ) (M := ULift.{1, 0} (ZMod 2))

example : structureCompatibility
    (R := ℤ) (M := ULift.{1, 0} (ZMod 2)) :=
  structureCompatibility_proof
    (R := ℤ) (M := ULift.{1, 0} (ZMod 2))

example : augmentationCompatibility
    (R := ℤ) (M := ULift.{1, 0} (ZMod 2)) :=
  augmentationCompatibility_proof
    (R := ℤ) (M := ULift.{1, 0} (ZMod 2))

example : augmentationSectionIdentities
    (R := ℤ) (M := ULift.{1, 0} (ZMod 2)) :=
  augmentationSectionIdentities_proof
    (R := ℤ) (M := ULift.{1, 0} (ZMod 2))

example : extensionEmbedding (R := ℤ) (M := ULift.{1, 0} (ZMod 2)) =
    AlgebraicGeometry.Spec.map (CommRingCat.ofHom
      ((squareZeroQuotientEquiv
        (R := ℤ) (M := ULift.{1, 0} (ZMod 2))).toRingEquiv.toRingHom.comp
          (Ideal.Quotient.mk
            ((augmentationIdeal
              (R := ℤ) (M := ULift.{1, 0} (ZMod 2))) ^ 2)))) :=
  quotientComposite
    (R := ℤ) (M := ULift.{1, 0} (ZMod 2))

example : quotientEmbeddingClosed
    (R := ℤ) (M := ULift.{1, 0} (ZMod 2)) := by
  exact AlgebraicGeometry.IsClosedImmersion.spec_of_quotient_mk
    (R := CommRingCat.of (SymmetricAlgebra (ℤ) (ULift.{1, 0} (ZMod 2))))
    ((augmentationIdeal (R := ℤ) (M := ULift.{1, 0} (ZMod 2))) ^ 2)

-- A base ring in a higher universe than its torsion module.
example :
    AlgebraicGeometry.Spec (CommRingCat.of (TrivSqZeroExt (ULift.{1, 0} ℤ) (ZMod 2))) ≅
      AlgebraicGeometry.Spec (CommRingCat.of (SymmetricAlgebra (ULift.{1, 0} ℤ) (ZMod 2) ⧸
      (SymmetricAlgebra.augmentationIdeal (R := ULift.{1, 0} ℤ) (M := ZMod 2)) ^ 2)) :=
  CategoryTheory.Functor.mapIso AlgebraicGeometry.Scheme.Spec
    (RingEquiv.toCommRingCatIso
      (SymmetricAlgebra.squareZeroQuotientEquiv (R := ULift.{1, 0} ℤ) (M := ZMod 2)).toRingEquiv).op

-- Proofs of the same generic contracts for this ring and module.
example :
  CommSq (quotientSpectrumIso (R := ULift.{1, 0} ℤ) (M := ZMod 2)).hom
    (extensionProjection (R := ULift.{1, 0} ℤ) (M := ZMod 2))
    (quotientProjection (R := ULift.{1, 0} ℤ) (M := ZMod 2))
    (𝟙 (AlgebraicGeometry.Spec (CommRingCat.of (ULift.{0, 1} (ULift.{1, 0} ℤ))))) :=
  projectionCommSq
    (R := ULift.{1, 0} ℤ) (M := ZMod 2)

example :
  CommSq (extensionSection (R := ULift.{1, 0} ℤ) (M := ZMod 2))
    (𝟙 (AlgebraicGeometry.Spec (CommRingCat.of (ULift.{0, 1} (ULift.{1, 0} ℤ)))))
    (quotientSpectrumIso (R := ULift.{1, 0} ℤ) (M := ZMod 2)).hom
    (quotientSection (R := ULift.{1, 0} ℤ) (M := ZMod 2)) :=
  zeroSectionCommSq
    (R := ULift.{1, 0} ℤ) (M := ZMod 2)

example : structureCompatibility
    (R := ULift.{1, 0} ℤ) (M := ZMod 2) :=
  structureCompatibility_proof
    (R := ULift.{1, 0} ℤ) (M := ZMod 2)

example : augmentationCompatibility
    (R := ULift.{1, 0} ℤ) (M := ZMod 2) :=
  augmentationCompatibility_proof
    (R := ULift.{1, 0} ℤ) (M := ZMod 2)

example : augmentationSectionIdentities
    (R := ULift.{1, 0} ℤ) (M := ZMod 2) :=
  augmentationSectionIdentities_proof
    (R := ULift.{1, 0} ℤ) (M := ZMod 2)

example : extensionEmbedding (R := ULift.{1, 0} ℤ) (M := ZMod 2) =
    AlgebraicGeometry.Spec.map (CommRingCat.ofHom
      ((squareZeroQuotientEquiv
        (R := ULift.{1, 0} ℤ) (M := ZMod 2)).toRingEquiv.toRingHom.comp
          (Ideal.Quotient.mk
            ((augmentationIdeal
              (R := ULift.{1, 0} ℤ) (M := ZMod 2)) ^ 2)))) :=
  quotientComposite
    (R := ULift.{1, 0} ℤ) (M := ZMod 2)

example : quotientEmbeddingClosed
    (R := ULift.{1, 0} ℤ) (M := ZMod 2) := by
  exact AlgebraicGeometry.IsClosedImmersion.spec_of_quotient_mk
    (R := CommRingCat.of (SymmetricAlgebra (ULift.{1, 0} ℤ) (ZMod 2)))
    ((augmentationIdeal (R := ULift.{1, 0} ℤ) (M := ZMod 2)) ^ 2)

-- A nonreduced base ring with its regular module.
example :
    AlgebraicGeometry.Spec (CommRingCat.of (TrivSqZeroExt (ZMod 4) (ZMod 4))) ≅
      AlgebraicGeometry.Spec (CommRingCat.of (SymmetricAlgebra (ZMod 4) (ZMod 4) ⧸
      (SymmetricAlgebra.augmentationIdeal (R := ZMod 4) (M := ZMod 4)) ^ 2)) :=
  CategoryTheory.Functor.mapIso AlgebraicGeometry.Scheme.Spec
    (RingEquiv.toCommRingCatIso
      (SymmetricAlgebra.squareZeroQuotientEquiv (R := ZMod 4) (M := ZMod 4)).toRingEquiv).op

-- Proofs of the same generic contracts for this ring and module.
example :
  CommSq (quotientSpectrumIso (R := ZMod 4) (M := ZMod 4)).hom
    (extensionProjection (R := ZMod 4) (M := ZMod 4))
    (quotientProjection (R := ZMod 4) (M := ZMod 4))
    (𝟙 (AlgebraicGeometry.Spec (CommRingCat.of (ULift.{0, 0} (ZMod 4))))) :=
  projectionCommSq
    (R := ZMod 4) (M := ZMod 4)

example :
  CommSq (extensionSection (R := ZMod 4) (M := ZMod 4))
    (𝟙 (AlgebraicGeometry.Spec (CommRingCat.of (ULift.{0, 0} (ZMod 4)))))
    (quotientSpectrumIso (R := ZMod 4) (M := ZMod 4)).hom
    (quotientSection (R := ZMod 4) (M := ZMod 4)) :=
  zeroSectionCommSq
    (R := ZMod 4) (M := ZMod 4)

example : structureCompatibility
    (R := ZMod 4) (M := ZMod 4) :=
  structureCompatibility_proof
    (R := ZMod 4) (M := ZMod 4)

example : augmentationCompatibility
    (R := ZMod 4) (M := ZMod 4) :=
  augmentationCompatibility_proof
    (R := ZMod 4) (M := ZMod 4)

example : augmentationSectionIdentities
    (R := ZMod 4) (M := ZMod 4) :=
  augmentationSectionIdentities_proof
    (R := ZMod 4) (M := ZMod 4)

example : extensionEmbedding (R := ZMod 4) (M := ZMod 4) =
    AlgebraicGeometry.Spec.map (CommRingCat.ofHom
      ((squareZeroQuotientEquiv
        (R := ZMod 4) (M := ZMod 4)).toRingEquiv.toRingHom.comp
          (Ideal.Quotient.mk
            ((augmentationIdeal
              (R := ZMod 4) (M := ZMod 4)) ^ 2)))) :=
  quotientComposite
    (R := ZMod 4) (M := ZMod 4)

example : quotientEmbeddingClosed
    (R := ZMod 4) (M := ZMod 4) := by
  exact AlgebraicGeometry.IsClosedImmersion.spec_of_quotient_mk
    (R := CommRingCat.of (SymmetricAlgebra (ZMod 4) (ZMod 4)))
    ((augmentationIdeal (R := ZMod 4) (M := ZMod 4)) ^ 2)

end SymmetricAlgebra
