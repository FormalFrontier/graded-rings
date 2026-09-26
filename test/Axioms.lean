/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import GradedRings.FiniteType
import GradedRings.HomogeneousPrime
import GradedRings.Localization
import GradedRings.Noetherian
import GradedRings.Quotient

#print axioms HomogeneousIdeal.exists_finset_span_eq_of_fg
#print axioms GradedAlgebra.irrelevant_exists_finset_span_eq_of_fg
#print axioms GradedAlgebra.finiteType_of_irrelevant_fg
#print axioms GradedAlgebra.irrelevant_le_span_of_adjoin_eq_top
#print axioms GradedAlgebra.irrelevant_fg_of_finiteType
#print axioms GradedAlgebra.irrelevant_fg_iff_finiteType
#print axioms GradedAlgebra.irrelevant_fg_of_isNoetherianRing
#print axioms GradedAlgebra.isNoetherianRing_of_gradeZero_of_irrelevant_fg
#print axioms GradedAlgebra.isNoetherianRing_iff_gradeZero_and_irrelevant_fg

#print axioms GradedRing.inv_mem_of_isUnit
#print axioms GradedRing.unit_zpow_mem
#print axioms GradedRing.degreeZeroProjection
#print axioms GradedRing.degreeZeroProjection_surjective
#print axioms GradedRing.comap_map_degreeZero
#print axioms GradedRing.map_degreeZero_isHomogeneous
#print axioms GradedRing.radical_map_degreeZero_isPrime
#print axioms GradedRing.radical_map_comap_degreeZero
#print axioms GradedRing.homogeneousPrimeEquivDegreeZeroPrime

#print axioms GradedLocalization.component
#print axioms GradedLocalization.mk_mem_component
#print axioms GradedLocalization.algebraMap_mem_component
#print axioms GradedLocalization.componentGradedMonoid
#print axioms GradedLocalization.zeroComponent
#print axioms GradedLocalization.toZeroComponent
#print axioms GradedLocalization.toZeroComponent_injective
#print axioms GradedLocalization.toZeroComponent_surjective
#print axioms GradedLocalization.homogeneousLocalizationEquivZeroComponent
#print axioms GradedLocalization.projectionFun
#print axioms GradedLocalization.projectionFun_mk
#print axioms GradedLocalization.projection
#print axioms GradedLocalization.projection_mem_component
#print axioms GradedLocalization.projection_eq_self_of_mem
#print axioms GradedLocalization.projection_eq_zero_of_mem
#print axioms GradedLocalization.projection_coe
#print axioms GradedLocalization.coe_injective
#print axioms GradedLocalization.coe_surjective
#print axioms GradedLocalization.isInternal
#print axioms GradedLocalization.decomposition
#print axioms GradedLocalization.gradedRing

#print axioms Ideal.Quotient.gradedComponent
#print axioms Ideal.Quotient.gradedRingHom
#print axioms Ideal.Quotient.gradedRingHom_apply
#print axioms Ideal.Quotient.gradedRingHom_toRingHom
#print axioms Ideal.Quotient.gradedRingHom_surjective
#print axioms Ideal.Quotient.gradedComponentGradedMonoid
#print axioms Ideal.Quotient.gradedComponentMap
#print axioms Ideal.Quotient.gradedDecomposePre
#print axioms Ideal.Quotient.gradedDecompose
#print axioms Ideal.Quotient.gradedDecompose_mk
#print axioms Ideal.Quotient.coe_gradedDecomposePre
#print axioms Ideal.Quotient.gradedDecompose_leftInverse
#print axioms Ideal.Quotient.gradedDecompose_rightInverse
#print axioms Ideal.Quotient.gradedDecomposition
#print axioms Ideal.Quotient.gradedRing
