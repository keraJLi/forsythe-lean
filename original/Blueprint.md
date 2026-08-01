# Lean blueprint for the manuscript-aligned `s = 2` proof

This standalone companion is aligned with the source manuscript through the
checked-in equation/lemma label snapshot.
All declarations listed below are in the production library, are imported by
`Forsythe.lean`, and are kernel checked without project-defined axioms or proof
placeholders.  Spectral coordinates use ordered distinct eigenvalues and grouped
orthogonal projections; the theorem-facing API remains in the manuscript's polynomial
orthogonality notation.

## Public API and representation

| Manuscript object | Lean declaration | Module |
|---|---|---|
| Polynomial action and orthogonality form | `polyApply`, `polyInner` | `Forsythe.Arnoldi.Defs` |
| Cyclic subspace and grade | `cyclicSubspace`, `grade` | `Forsythe.Arnoldi.Defs` |
| Monic quadratic and product coefficient norm | `MonicQuadratic`, `coeffPair`, `coeffDist` | `Forsythe.Polynomial.Quadratic` |
| Moment-system factor | `arnoldiPoly2` | `Forsythe.Arnoldi.Defs` |
| Normalized step and orbit | `arnoldiStep2`, `arnoldiOrbit2` | `Forsythe.Arnoldi.Defs` |
| Final operator theorem | `Forsythe.forsythe_s2` | `Forsythe.Main` |
| Final matrix theorem via `Matrix.toLpLin 2 2` | `Matrix.forsythe_s2` | `Forsythe.Matrix.Main` |

## Complete equation map

Every labeled display used in the manuscript proof has the following checked
counterpart.  A row may name several declarations when the Lean proof separates
an exact identity from its orbit-level specialization.  The first two columns
are machine-readable: every manuscript `eq:`/`lem:` label must occur exactly
once as a first-column row, and every backticked identifier in the counterpart
column has a fully qualified compile-time check in
`ForsytheTest.BlueprintDeclarations`.  The standalone project's authoritative
label snapshot is `scripts/manuscript_labels.txt`.

| TeX label | Lean counterpart | Module | Status |
|---|---|---|---|
| `eq:iteration` | `rawArnoldiStep2` (defined as the polynomial action) | `Arnoldi.Defs` | checked |
| `eq:normalization` | `arnoldiStep2` (defined by inverse-norm scaling) | `Arnoldi.Defs` | checked |
| `eq:arnoldi` | `arnoldiPoly2_orthogonal_one`, `arnoldiPoly2_orthogonal_X`, `arnoldiPoly2_minimizes` | `Arnoldi.MomentGram` | checked |
| `eq:orthogonality` | `arnoldiPoly2_orthogonal_one`, `arnoldiPoly2_orthogonal_X`; finite-node versions `FourNode.P_orthogonal_one`, `P_orthogonal_X` | `Arnoldi.MomentGram`, `FourNode.Weights` | checked |
| `eq:transport` | `quadraticStep_transport`, `quadraticStep_transport_two` | `Arnoldi.Algebra` | checked |
| `eq:energy` | `quadraticStep_energy`, orbit specialization `IsQuadraticStepSequence.energy_identity` | `Arnoldi.Algebra`, `Arnoldi.Energy` | checked |
| `eq:correlation` | `quadraticStep_correlation`, `IsQuadraticStepSequence.two_step_correlation` | `Arnoldi.Algebra`, `Arnoldi.Energy` | checked |
| `eq:variation` | `factor_variation_of_coercive`, `exists_arnoldiOrbit2_factor_variation` | `Arnoldi.Variation`, `Arnoldi.OrbitVariation` | checked for every index |
| `eq:cancellation` | `quadraticStep_cancellation` | `Arnoldi.Algebra` | checked |
| `eq:three-step` | `quadraticStep_three_step`, quantitative `quadraticStep_three_step_upper` | `Arnoldi.Algebra`, `Arnoldi.OrbitVariation` | checked |
| `eq:polynomial-limits` | `exists_paritywise_factor_limits`, `arnoldiOrbit2_polynomial_limits` | `Arnoldi.FactorConvergence`, `Arnoldi.PolynomialLimits` | checked |
| `eq:tail` | `coeffDist_parity_limit_le_height_tail`, `arnoldiOrbit2_polynomial_limits_global` | `Arnoldi.FactorConvergence`, `Arnoldi.PolynomialLimits` | checked for every index |
| `eq:limit-equation` | `even_limit_equation_of_mem_arnoldiClusterSet`, `odd_limit_equation_of_mem_arnoldiClusterSet` | `Spectral.Reduction` | checked |
| `eq:four-factor` | `orderedFourNode_factorization_of_mem_evenClusterSet` | `Spectral.OrderedFourNode` | checked |
| `eq:exterior-decay` | `orderedExteriorMass_global_geometric_of_fourNode_even_cluster` | `Spectral.OrderedExteriorDecay` | checked globally for every orbit index |
| `eq:component` | `component_arnoldiOrbit2_add_two`, `component_arnoldiOrbit2_add_two_eq_multiplier`, `weight_arnoldiOrbit2_add_two` | `Spectral.ComponentRecurrence` | checked |
| `eq:principal-weights` | `normalizedPrincipalWeight`, `principalWeights`, `principalWeights_apply` | `Spectral.PrincipalWeights` | checked |
| `eq:rho` | `weight_mul_P_eval_eq_height_mul_sub_rho_div_E`, `rho_eq_node_formula` | `FourNode.Rho` | checked |
| `eq:fiber` | `fiberWeight`, `fiberPoint`, `AdmissibleFiberFactors.pPoint`, `AdmissibleFiberFactors.qPoint`, `AdmissibleFiberFactors.isCompact_pCurve`, `AdmissibleFiberFactors.isClosed_pCurve` | `FourNode.Fiber`, `FourNode.FiberCurve` | checked in the simplex, including the three-positive boundary |
| `eq:gap` | `AdmissibleFiberFactors.pRootPlacement`, `AdmissibleFiberFactors.qRootPlacement`, `exists_uniform_factor_product_gap_on_compact`, `exists_uniform_factor_gap_on_middleGap` | `FourNode.FiberCurve`, `FourNode.Fiber`, `FourNode.MultiplierAsymptotics` | checked with roots in the two outer node gaps |
| `eq:fiber-factor` | `P_eq_of_memFiber`, `P_T_eq_companion_of_memFiber`, `memFiber_T` | `FourNode.Fiber` | checked |
| `eq:perturbed-map` | `principalWeights_succ_sub_T_norm_le`, `exists_eventually_principalWeights_updateDefect_geometric` | `Spectral.PrincipalUpdatePerturbation`, `Spectral.PrincipalAsymptotics` | checked with explicit constants |
| `eq:interpolation` | `interpolation_identity`, `rho_T_sub_rho` | `FourNode.Interpolation` | checked |
| `eq:shared-factor` | `consecutive_sharedFactor_recurrence`, `alphaSeq_succ_recurrence` | `FourNode.Interpolation`, `FourNode.Perturbation` | checked |
| `eq:remainders` | `remainderLinearCoeff_dividedDifference_right`, `remainderLinearCoeff_dividedDifference_left`; explicit formula `remainderLinearCoeff_dividedDifference_eq` | `Polynomial.FourNode`, `FourNode.RemainderContinuity` | checked |
| `eq:scalar` | `perturbed_recurrences_with_geometric_errors`, `exists_tendsto_of_geometric_perturbed_normalizedRecurrence`, `exists_tendsto_rhoSeq_of_asymptotically_exact_fourNode` | `FourNode.Perturbation`, `Dynamics.ScalarClosure`, `FourNode.AsymptoticClosure` | checked |

The two labeled manuscript lemmas are checked as complete packages:

| TeX label | Lean counterpart | Module | Status |
|---|---|---|---|
| `lem:exterior-decay` | `orderedExteriorMass_global_geometric_of_fourNode_even_cluster` | `Spectral.OrderedExteriorDecay` | checked with one global constant and rate |
| `lem:four-node-identity` | `interpolation_identity`, `rho_T_sub_rho`, `consecutive_sharedFactor_recurrence`, `remainderLinearCoeff_dividedDifference_right`, `remainderLinearCoeff_dividedDifference_left` | `FourNode.Interpolation`, `Polynomial.FourNode` | checked algebraically, including boundary states |

## Lemma and proof-stage map

### Arnoldi foundation

- Positivity of the moment Gram determinant: `momentGramDet_pos_of_grade_three`.
- Existence, uniqueness, minimizing property, and orthogonality of the explicit
  moment-system factor: `arnoldiPoly2_orthogonal_one`,
  `arnoldiPoly2_orthogonal_X`, `monicQuadratic_eq_arnoldiPoly2`, and
  `arnoldiPoly2_minimizes`.
- Nonzero step, unit norm, and grade preservation:
  `rawArnoldiStep2_ne_zero_of_grade_ge_three`, `norm_arnoldiStep2`, and
  `grade_arnoldiStep2_of_grade_three`.
- Continuity on the valid domain: `continuousAt_arnoldiPoly2_coeffPair`,
  `continuousAt_arnoldiStep2` in `Arnoldi.Continuity`.
- Height monotonicity, summability, finite exact two-periodicity, and compact
  connected parity cluster sets: `arnoldiOrbit2_height_monotone`,
  `summable_arnoldiOrbit2_height_increment_of_initial_grade_three`,
  `arnoldiOrbit2_eventually_two_periodic_of_energy_eq_zero`, and
  `compact_connected_even_arnoldiClusterSet` / `compact_connected_odd_arnoldiClusterSet`.
- The manuscript's unshifted all-index factor variation and consecutive-product
  tail bound are `exists_arnoldiOrbit2_factor_variation` and
  `arnoldiOrbit2_polynomial_limits_global`; their proofs absorb the finite
  pre-coercivity prefix into one explicit finite-sum constant.
- Generic compact-connected cluster-set theorem:
  `compact_connected_clusterSet` in `Dynamics.ClusterSet`.

### Spectral reduction

- Self-adjoint grouped eigenspace coordinates and polynomial preservation:
  `component`, `weight`, `component_polyApply` in `Spectral.Coordinates`.
- Grade equals active distinct eigenvalue count: `grade_eq_card_active` in
  `Spectral.Grade`.
- Component deletion and eventual stabilization:
  `active_arnoldiOrbit2_mono`, `exists_stable_active_spectrum`.
- Limit equation, support cardinality three or four, and three-node convergence:
  `arnoldiOrbit2_spectral_reduction`,
  `active_card_eq_three_or_four_of_quadraticProduct_sub_C_annihilator`, and
  `exists_tendsto_even_arnoldiOrbit2_of_all_cluster_active_card_three`.
- Ordered four-node enumeration and factorization:
  `orderedNodesOfFourClusterPoint`,
  `orderedFourNode_factorization_of_mem_evenClusterSet`.

### Exterior decay

- The manuscript's real-power cocycle is represented by
  `logarithmicWeightCocycle`; this is the logarithm of the positive product
  quantity denoted by `Z` in the text.
- The explicit logarithm remainder is
  `abs_log_one_add_sub_le_two_mul_sq` in `Exterior.LogEstimate`.
- Cubic Lagrange cancellation is `cubic_firstVariation_cancel`; the full
  first-variation error estimate is `abs_lagrange_log_firstVariation_le`.
- Strict drift, the grade-four subsequence contradiction, strict contraction,
  and the uniform geometric sum estimate are assembled in
  `stableExterior_geometric_of_fourNode_even_cluster`.
- Every manuscript `O(·)` in this layer is represented by an explicit constant,
  rate, and eventual inequality in `Exterior.*` or
  `Spectral.ExteriorDecayBranch`.

### Four-node closure

- The simplex, factor, height, and map are `FourNode.Weights`, `P`, `H`, and
  `T` in `FourNode.Weights`.
- `rho` is defined by one fixed node formula; node independence is
  `rho_eq_node_formula`.
- The boundary interpolation proof is algebraic (`interpolation_identity`),
  with no density argument.
- Ordered admissible fibers lie in the central gap:
  `rho_mem_middleGap_of_memFiber` and
  `rho_mem_open_middleGap_of_memFiber`.
- The full closed middle-gap parameterization is simplex-valued:
  `fiberWeight_nonneg_on_middleGap` and
  `three_le_card_positive_fiberWeight_on_middleGap` prove the simplex
  inequalities, while `AdmissibleFiberFactors.pPoint` and `qPoint` package
  them together with exact normalization.  Its two images are
  compact and closed by `isCompact_pCurve`, `isClosed_pCurve`,
  `isCompact_qCurve`, and `isClosed_qCurve` in `FourNode.FiberCurve`.
- The endpoint sign pattern is obtained from an interior limiting fiber by
  `admissibleFiberFactors_of_memFiber`.  Exact outer-gap root placement and
  linear-factor decompositions are `pRootPlacement` and `qRootPlacement`.
- Rational denominator floors and Lipschitz estimates are in
  `FourNode.Continuity`, `RemainderContinuity`, and `TailFloors`.
- Exact-update parity transfer, height transfer, and `alpha → 0` are in
  `FourNode.ParityAsymptotics`.
- Positivity and convergence of the remainder multiplier are in
  `remainderMultiplier_eventually_pos_tendsto_one`.
- The normalized-product dichotomy and one-way-crossing convergence are
  `normalizedRecurrence_geometric_dichotomy` and
  `tendsto_of_eventuallyLocallyDirectedSteps` in `Dynamics.Scalar`.
- Their final application is
  `exists_tendsto_rhoSeq_of_asymptotically_exact_fourNode`.

## Final assembly

`Spectral.exists_tendsto_parities_of_fourNode_even_cluster` combines ordered
exterior decay with the four-node closure and grouped sign recovery.  At every
principal node, `arnoldiTwoStepMultiplier_even_tendsto_one` and
`eventually_pos_arnoldiTwoStepMultiplier_even` make the exact two-step
multiplier eventually positive.  The final even-vector convergence is then
obtained by the positive-ray theorem
`exists_tendsto_arnoldiParity_of_weight_limits_of_positive_multipliers`, which
is used in `Spectral.OrderedFourNodeClosure`; zero limiting components converge
directly by their norms.  Odd convergence is recovered from the continuous
one-step Arnoldi map.
`Forsythe.forsythe_s2` applies the spectral reduction, closes the all-three-node
case directly, and otherwise uses a four-node even cluster point.  The matrix
corollary `Matrix.forsythe_s2` transports the result through
`Matrix.toLpLin 2 2` and `Matrix.isSymmetric_operator`.

## Regression and verification policy

`Forsythe.lean` and `ForsytheTest.lean` are import-only aggregators.  Regression
modules cover rational remainder identities, a three-positive boundary state,
an exactly two-periodic grade-three diagonal example, component deletion, both
scalar-recurrence dichotomy branches, and the public operator/matrix theorem
signatures.

The required gates are:

```text
lake exe cache get
./scripts/no_placeholders.sh
lake build --wfail
lake test
lake lint
```

The placeholder audit scans every production Lean source and rejects
`sorry`, `admit`, or a project-defined `axiom`.
