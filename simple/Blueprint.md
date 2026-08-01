# Blueprint for the simplified `s = 2` formalization

This project proves the same operator and matrix theorems as `original/`, but
keeps only the machinery needed by the shortest checked argument.  It uses
grouped self-adjoint eigenspace coordinates internally and retains the
orthogonality-based public API.

The main simplifications are deliberate:

- analytic estimates are stated on a tail, which is sufficient at `atTop`;
- four-node fibers are used through their rational coordinate identity rather
  than a separate topology of closed curves and explicit root objects;
- once all squared spectral components converge, vector convergence follows
  because the parity cluster set is both connected and finite.

All production modules are imported by `Forsythe.lean`.  The label snapshot in
`scripts/manuscript_labels.txt`, this map, and the fully qualified checks in
`ForsytheTest.BlueprintDeclarations` are kept in exact agreement by
`scripts/check_coverage.sh`.

## Public API

| Object | Lean declaration | Module |
|---|---|---|
| Polynomial action and orthogonality form | `polyApply`, `polyInner` | `Forsythe.Arnoldi.Defs` |
| Cyclic subspace and grade | `cyclicSubspace`, `grade` | `Forsythe.Arnoldi.Defs` |
| Explicit moment-system factor | `arnoldiPoly2` | `Forsythe.Arnoldi.Defs` |
| Normalized step and orbit | `arnoldiStep2`, `arnoldiOrbit2` | `Forsythe.Arnoldi.Defs` |
| Operator theorem | `Forsythe.forsythe_s2` | `Forsythe.Main` |
| Matrix theorem | `Matrix.forsythe_s2` | `Forsythe.Matrix.Main` |

## Complete equation map

| TeX label | Lean counterpart | Module | Simplified status |
|---|---|---|---|
| `eq:iteration` | `rawArnoldiStep2` | `Arnoldi.Defs` | definition |
| `eq:normalization` | `arnoldiStep2` | `Arnoldi.Defs` | definition |
| `eq:arnoldi` | `arnoldiPoly2_orthogonal_one`, `arnoldiPoly2_orthogonal_X`, `arnoldiPoly2_minimizes` | `Arnoldi.MomentGram` | checked |
| `eq:orthogonality` | `arnoldiPoly2_orthogonal_one`, `arnoldiPoly2_orthogonal_X`, `FourNode.P_orthogonal_one`, `P_orthogonal_X` | `Arnoldi.MomentGram`, `FourNode.Weights` | checked |
| `eq:transport` | `quadraticStep_transport`, `quadraticStep_transport_two` | `Arnoldi.Algebra` | checked |
| `eq:energy` | `quadraticStep_energy`, `IsQuadraticStepSequence.energy_identity` | `Arnoldi.Algebra`, `Arnoldi.Energy` | checked |
| `eq:correlation` | `quadraticStep_correlation`, `IsQuadraticStepSequence.two_step_correlation` | `Arnoldi.Algebra`, `Arnoldi.Energy` | checked |
| `eq:variation` | `factor_variation_of_coercive`, `exists_arnoldiOrbit2_factor_variation_tail` | `Arnoldi.Variation`, `Arnoldi.OrbitVariation` | checked on a tail |
| `eq:cancellation` | `quadraticStep_cancellation` | `Arnoldi.Algebra` | checked |
| `eq:three-step` | `quadraticStep_three_step`, `quadraticStep_three_step_upper` | `Arnoldi.Algebra`, `Arnoldi.OrbitVariation` | checked |
| `eq:polynomial-limits` | `exists_paritywise_factor_limits`, `arnoldiOrbit2_polynomial_limits` | `Arnoldi.FactorConvergence`, `Arnoldi.PolynomialLimits` | checked |
| `eq:tail` | `coeffDist_parity_limit_le_height_tail`, `arnoldiOrbit2_polynomial_limits` | `Arnoldi.FactorConvergence`, `Arnoldi.PolynomialLimits` | checked after one finite shift |
| `eq:limit-equation` | `even_limit_equation_of_mem_arnoldiClusterSet`, `odd_limit_equation_of_mem_arnoldiClusterSet` | `Spectral.Reduction` | checked |
| `eq:four-factor` | `orderedFourNode_factorization_of_mem_evenClusterSet` | `Spectral.OrderedFourNode` | checked |
| `eq:exterior-decay` | `orderedExteriorMass_geometric_of_fourNode_even_cluster` | `Spectral.OrderedExteriorDecay` | checked eventually |
| `eq:component` | `component_arnoldiOrbit2_add_two`, `weight_arnoldiOrbit2_add_two` | `Spectral.ComponentRecurrence` | checked |
| `eq:principal-weights` | `normalizedPrincipalWeight`, `principalWeights`, `principalWeights_apply` | `Spectral.PrincipalWeights` | checked |
| `eq:rho` | `weight_mul_P_eval_eq_height_mul_sub_rho_div_E`, `rho_eq_node_formula` | `FourNode.Rho` | checked |
| `eq:fiber` | `fiberWeight`, `MemFiber`, `clusterPrincipalWeights_memFiber` | `FourNode.Fiber`, `Spectral.FourNodeBranch` | checked directly in coordinates |
| `eq:gap` | `factor_eval_ne_zero_on_middleGap`, `factor_eval_middle_nodes_neg_of_memFiber`, `exists_uniform_factor_gap_on_middleGap` | `FourNode.Gap`, `FourNode.MultiplierAsymptotics` | checked without root objects |
| `eq:fiber-factor` | `sub_rho_mul_consecutive_P_eval`, `interpolation_identity` | `FourNode.Interpolation` | checked algebraically |
| `eq:perturbed-map` | `principalWeights_succ_sub_T_norm_le`, `exists_eventually_principalWeights_updateDefect_geometric` | `Spectral.PrincipalUpdatePerturbation`, `Spectral.PrincipalAsymptotics` | explicit constants |
| `eq:interpolation` | `interpolation_identity`, `rho_T_sub_rho` | `FourNode.Interpolation` | checked |
| `eq:shared-factor` | `consecutive_sharedFactor_recurrence`, `alphaSeq_succ_recurrence` | `FourNode.Interpolation`, `FourNode.Perturbation` | checked |
| `eq:remainders` | `remainderLinearCoeff_dividedDifference_right`, `remainderLinearCoeff_dividedDifference_left`, `remainderLinearCoeff_dividedDifference_eq` | `Polynomial.FourNode`, `FourNode.RemainderContinuity` | checked |
| `eq:scalar` | `perturbed_recurrences_with_geometric_errors`, `exists_tendsto_of_geometric_perturbed_normalizedRecurrence`, `exists_tendsto_rhoSeq_of_asymptotically_exact_fourNode` | `FourNode.Perturbation`, `Dynamics.ScalarClosure`, `FourNode.AsymptoticClosure` | checked |

| TeX label | Lean counterpart | Module | Simplified status |
|---|---|---|---|
| `lem:exterior-decay` | `orderedExteriorMass_geometric_of_fourNode_even_cluster` | `Spectral.OrderedExteriorDecay` | one eventual geometric estimate |
| `lem:four-node-identity` | `interpolation_identity`, `rho_T_sub_rho`, `consecutive_sharedFactor_recurrence`, `remainderLinearCoeff_dividedDifference_right`, `remainderLinearCoeff_dividedDifference_left` | `FourNode.Interpolation`, `Polynomial.FourNode` | checked algebraically |

## Proof route

The intrinsic Arnoldi layer proves positivity of the moment Gram determinant,
existence and uniqueness of the minimizing monic quadratic, unit-norm and grade
preservation, monotonicity of the height, paritywise polynomial convergence,
and compact connected parity cluster sets.

Self-adjoint diagonalization then groups repeated eigenvalues.  Polynomial
iteration preserves each initial eigenspace direction, grade equals the number
of active distinct eigenvalues, and the limit equation restricts cluster
supports to three or four nodes.  The three-node case has unique limiting
weights.  In the four-node case, logarithmic exterior decay and the scalar
four-node recurrence give convergence of every squared component.

The last step is the simplified one.  `exists_tendsto_of_grouped_weight_limits`
shows that fixed component lines and convergent squared norms make the cluster
set finite; asymptotic two-step regularity makes it connected.  Therefore
`exists_tendsto_arnoldiParity_of_weight_limits` gives even-vector convergence
without tracking multiplier signs.  Odd convergence follows continuously from
one exact Arnoldi step.

## Verification

`Forsythe.lean` and `ForsytheTest.lean` are import-only aggregators.  Tests
cover the algebraic identities, a three-positive boundary state, an exact
grade-three two-cycle, component deletion, both scalar-dichotomy branches,
the declaration map, public signatures, and the public axiom footprint.

Required gates:

```text
lake exe cache get
./scripts/no_placeholders.sh
./scripts/check_coverage.sh
lake build --wfail
lake test
lake lint
```
