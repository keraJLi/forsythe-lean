import Forsythe

/-!
# Blueprint declaration regression

Every declaration named in column two of the complete equation/lemma map in
`Blueprint.md` is checked here under its fully qualified Lean name.  The
same-line annotations are consumed by `scripts/check_coverage.sh`, which keeps
this module and the map in exact agreement.
-/

#check Forsythe.rawArnoldiStep2 -- blueprint-declaration: rawArnoldiStep2
#check Forsythe.arnoldiStep2 -- blueprint-declaration: arnoldiStep2

#check Forsythe.arnoldiPoly2_orthogonal_one -- blueprint-declaration: arnoldiPoly2_orthogonal_one
#check Forsythe.arnoldiPoly2_orthogonal_X -- blueprint-declaration: arnoldiPoly2_orthogonal_X
#check Forsythe.arnoldiPoly2_minimizes -- blueprint-declaration: arnoldiPoly2_minimizes
#check Forsythe.FourNode.P_orthogonal_one -- blueprint-declaration: FourNode.P_orthogonal_one
#check Forsythe.FourNode.P_orthogonal_X -- blueprint-declaration: P_orthogonal_X

#check Forsythe.quadraticStep_transport -- blueprint-declaration: quadraticStep_transport
#check Forsythe.quadraticStep_transport_two -- blueprint-declaration: quadraticStep_transport_two
#check Forsythe.quadraticStep_energy -- blueprint-declaration: quadraticStep_energy
#check Forsythe.IsQuadraticStepSequence.energy_identity -- blueprint-declaration: IsQuadraticStepSequence.energy_identity
#check Forsythe.quadraticStep_correlation -- blueprint-declaration: quadraticStep_correlation
#check Forsythe.IsQuadraticStepSequence.two_step_correlation -- blueprint-declaration: IsQuadraticStepSequence.two_step_correlation
#check Forsythe.Arnoldi.factor_variation_of_coercive -- blueprint-declaration: factor_variation_of_coercive
#check Forsythe.Arnoldi.exists_arnoldiOrbit2_factor_variation -- blueprint-declaration: exists_arnoldiOrbit2_factor_variation
#check Forsythe.quadraticStep_cancellation -- blueprint-declaration: quadraticStep_cancellation
#check Forsythe.quadraticStep_three_step -- blueprint-declaration: quadraticStep_three_step
#check Forsythe.Arnoldi.quadraticStep_three_step_upper -- blueprint-declaration: quadraticStep_three_step_upper

#check Forsythe.Arnoldi.exists_paritywise_factor_limits -- blueprint-declaration: exists_paritywise_factor_limits
#check Forsythe.Arnoldi.arnoldiOrbit2_polynomial_limits -- blueprint-declaration: arnoldiOrbit2_polynomial_limits
#check Forsythe.Arnoldi.coeffDist_parity_limit_le_height_tail -- blueprint-declaration: coeffDist_parity_limit_le_height_tail
#check Forsythe.Arnoldi.arnoldiOrbit2_polynomial_limits_global -- blueprint-declaration: arnoldiOrbit2_polynomial_limits_global

#check Forsythe.Spectral.even_limit_equation_of_mem_arnoldiClusterSet -- blueprint-declaration: even_limit_equation_of_mem_arnoldiClusterSet
#check Forsythe.Spectral.odd_limit_equation_of_mem_arnoldiClusterSet -- blueprint-declaration: odd_limit_equation_of_mem_arnoldiClusterSet
#check Forsythe.Spectral.orderedFourNode_factorization_of_mem_evenClusterSet -- blueprint-declaration: orderedFourNode_factorization_of_mem_evenClusterSet
#check Forsythe.Spectral.orderedExteriorMass_global_geometric_of_fourNode_even_cluster -- blueprint-declaration: orderedExteriorMass_global_geometric_of_fourNode_even_cluster

#check Forsythe.Spectral.component_arnoldiOrbit2_add_two -- blueprint-declaration: component_arnoldiOrbit2_add_two
#check Forsythe.Spectral.component_arnoldiOrbit2_add_two_eq_multiplier -- blueprint-declaration: component_arnoldiOrbit2_add_two_eq_multiplier
#check Forsythe.Spectral.weight_arnoldiOrbit2_add_two -- blueprint-declaration: weight_arnoldiOrbit2_add_two

#check Forsythe.Spectral.normalizedPrincipalWeight -- blueprint-declaration: normalizedPrincipalWeight
#check Forsythe.Spectral.principalWeights -- blueprint-declaration: principalWeights
#check Forsythe.Spectral.principalWeights_apply -- blueprint-declaration: principalWeights_apply

#check Forsythe.FourNode.weight_mul_P_eval_eq_height_mul_sub_rho_div_E -- blueprint-declaration: weight_mul_P_eval_eq_height_mul_sub_rho_div_E
#check Forsythe.FourNode.rho_eq_node_formula -- blueprint-declaration: rho_eq_node_formula

#check Forsythe.FourNode.fiberWeight -- blueprint-declaration: fiberWeight
#check Forsythe.FourNode.fiberPoint -- blueprint-declaration: fiberPoint
#check Forsythe.FourNode.AdmissibleFiberFactors.pPoint -- blueprint-declaration: AdmissibleFiberFactors.pPoint
#check Forsythe.FourNode.AdmissibleFiberFactors.qPoint -- blueprint-declaration: AdmissibleFiberFactors.qPoint
#check Forsythe.FourNode.AdmissibleFiberFactors.isCompact_pCurve -- blueprint-declaration: AdmissibleFiberFactors.isCompact_pCurve
#check Forsythe.FourNode.AdmissibleFiberFactors.isClosed_pCurve -- blueprint-declaration: AdmissibleFiberFactors.isClosed_pCurve

#check Forsythe.FourNode.AdmissibleFiberFactors.pRootPlacement -- blueprint-declaration: AdmissibleFiberFactors.pRootPlacement
#check Forsythe.FourNode.AdmissibleFiberFactors.qRootPlacement -- blueprint-declaration: AdmissibleFiberFactors.qRootPlacement
#check Forsythe.FourNode.exists_uniform_factor_product_gap_on_compact -- blueprint-declaration: exists_uniform_factor_product_gap_on_compact
#check Forsythe.FourNode.exists_uniform_factor_gap_on_middleGap -- blueprint-declaration: exists_uniform_factor_gap_on_middleGap

#check Forsythe.FourNode.P_eq_of_memFiber -- blueprint-declaration: P_eq_of_memFiber
#check Forsythe.FourNode.P_T_eq_companion_of_memFiber -- blueprint-declaration: P_T_eq_companion_of_memFiber
#check Forsythe.FourNode.memFiber_T -- blueprint-declaration: memFiber_T

#check Forsythe.Spectral.principalWeights_succ_sub_T_norm_le -- blueprint-declaration: principalWeights_succ_sub_T_norm_le
#check Forsythe.Spectral.exists_eventually_principalWeights_updateDefect_geometric -- blueprint-declaration: exists_eventually_principalWeights_updateDefect_geometric

#check Forsythe.FourNode.interpolation_identity -- blueprint-declaration: interpolation_identity
#check Forsythe.FourNode.rho_T_sub_rho -- blueprint-declaration: rho_T_sub_rho
#check Forsythe.FourNode.consecutive_sharedFactor_recurrence -- blueprint-declaration: consecutive_sharedFactor_recurrence
#check Forsythe.FourNode.alphaSeq_succ_recurrence -- blueprint-declaration: alphaSeq_succ_recurrence

#check Forsythe.FourNode.remainderLinearCoeff_dividedDifference_right -- blueprint-declaration: remainderLinearCoeff_dividedDifference_right
#check Forsythe.FourNode.remainderLinearCoeff_dividedDifference_left -- blueprint-declaration: remainderLinearCoeff_dividedDifference_left
#check Forsythe.FourNode.remainderLinearCoeff_dividedDifference_eq -- blueprint-declaration: remainderLinearCoeff_dividedDifference_eq

#check Forsythe.FourNode.perturbed_recurrences_with_geometric_errors -- blueprint-declaration: perturbed_recurrences_with_geometric_errors
#check Forsythe.ScalarDynamics.exists_tendsto_of_geometric_perturbed_normalizedRecurrence -- blueprint-declaration: exists_tendsto_of_geometric_perturbed_normalizedRecurrence
#check Forsythe.FourNode.exists_tendsto_rhoSeq_of_asymptotically_exact_fourNode -- blueprint-declaration: exists_tendsto_rhoSeq_of_asymptotically_exact_fourNode
