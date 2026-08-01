import Forsythe.Arnoldi.OddLimit
import Forsythe.FourNode.AsymptoticClosure
import Forsythe.Spectral.OrderedFourNode
import Forsythe.Spectral.PrincipalAsymptotics
import Forsythe.Spectral.WeightConvergence

/-!
# Closing the ordered four-node spectral branch

Geometric exterior decay turns the normalized weights at the four ordered
active eigenvalues into an asymptotically exact four-node orbit.  The generic
scalar closure theorem gives convergence of its barycentric parameter, hence
of every selected squared component.  Exterior weights vanish, so grouped
sign recovery yields vector convergence.
-/

set_option autoImplicit false

namespace Forsythe
namespace Spectral

open Filter Module.End Polynomial Set Topology

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

private theorem evenIndex_tendsto_atTop :
    Tendsto (fun k : ℕ ↦ 2 * k) atTop atTop := by
  apply tendsto_atTop.2
  intro N
  exact eventually_atTop.2 ⟨N, fun k hk ↦ by omega⟩

private theorem oddIndex_tendsto_atTop :
    Tendsto (fun k : ℕ ↦ 2 * k + 1) atTop atTop := by
  apply tendsto_atTop.2
  intro N
  exact eventually_atTop.2 ⟨N, fun k hk ↦ by omega⟩

/-- The complete four-node branch, assuming the geometric exterior estimate
already obtained from the logarithmic cocycle. -/
theorem exists_tendsto_parities_of_orderedFourNode_geometricExterior
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v₀ : E)
    (hv₀ : ‖v₀‖ = 1) (hgrade₀ : 3 ≤ grade A v₀)
    (tau : ℝ) (htau : 0 < tau) (p q : MonicQuadratic)
    (hp : Tendsto
      (fun n ↦ (arnoldiFactorOrbit2 A v₀ (2 * n)).coeffPair)
      atTop (nhds p.coeffPair))
    (hq : Tendsto
      (fun n ↦ (arnoldiFactorOrbit2 A v₀ (2 * n + 1)).coeffPair)
      atTop (nhds q.coeffPair))
    (hnormalizer : Tendsto (arnoldiNormalizerOrbit2 A v₀)
      atTop (nhds tau))
    (vStar : E)
    (hvStar : vStar ∈ clusterSet
      (fun k ↦ arnoldiOrbit2 A v₀ (2 * k)))
    (hcard : (active A hA vStar).card = 4)
    {Cext theta : ℝ} (hCext : 0 ≤ Cext)
    (hthetaPos : 0 < theta) (hthetaLt : theta < 1)
    (hextGeometric : ∀ᶠ k in atTop,
      exteriorMass A hA
        (orderedNodesOfFourClusterPoint A hA vStar hcard)
        (arnoldiOrbit2 A v₀ k) ≤ Cext * theta ^ k) :
    ∃ vEven vOdd,
      Tendsto (fun k ↦ arnoldiOrbit2 A v₀ (2 * k))
        atTop (nhds vEven) ∧
      Tendsto (fun k ↦ arnoldiOrbit2 A v₀ (2 * k + 1))
        atTop (nhds vOdd) := by
  let nodes := orderedNodesOfFourClusterPoint A hA vStar hcard
  let lambda : Fin 4 → ℝ := fun i ↦ ((nodes i : A.Eigenvalues) : ℝ)
  have hnodes := orderedNodesOfFourClusterPoint_injective
    A hA vStar hcard
  have hlambda : StrictMono lambda := by
    simpa only [lambda, nodes] using
      orderedNodesOfFourClusterPoint_strictMono A hA vStar hcard
  have hlambdaInjective : Function.Injective lambda := hlambda.injective
  have hcomponent : ∀ k i,
      component A hA (arnoldiOrbit2 A v₀ k) (nodes i) ≠ 0 := by
    simpa only [nodes] using
      orderedFourNode_components_ne_zero_all A hA v₀ hvStar hcard
  let x : ℕ → FourNode.Weights := fun k ↦
    principalWeights A hA nodes (arnoldiOrbit2 A v₀ k) (hcomponent k)
  have hfactor : p.toPolynomial * q.toPolynomial =
      FourNode.nodalQuartic lambda + C (tau ^ 2) := by
    simpa only [nodes, lambda] using
      orderedFourNode_factorization_of_mem_evenClusterSet
        A hA v₀ hv₀ hgrade₀ tau p q hp hq hnormalizer hvStar hcard
  have hthetaNonneg : 0 ≤ theta := hthetaPos.le
  have hextUpper : Tendsto (fun k : ℕ ↦ Cext * theta ^ k)
      atTop (nhds 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one hthetaNonneg hthetaLt)
  have hext : Tendsto (fun k ↦
      exteriorMass A hA nodes (arnoldiOrbit2 A v₀ k))
      atTop (nhds 0) := by
    exact squeeze_zero'
      (Eventually.of_forall fun _ ↦ exteriorMass_nonneg A hA nodes _)
      (by simpa only [nodes] using hextGeometric)
      hextUpper
  have hfactorDist := tendsto_arnoldiFactor_coeffDist_principalWeights
    A hA v₀ hv₀ hgrade₀ nodes hnodes hcomponent hext
  have hpairDiff : Tendsto (fun k ↦
      (arnoldiFactorOrbit2 A v₀ k).coeffPair -
        (FourNode.P lambda (x k)).coeffPair)
      atTop (nhds 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simpa only [MonicQuadratic.coeffDist, lambda, x] using hfactorDist
  have hpairDiffEven := hpairDiff.comp evenIndex_tendsto_atTop
  have hpairDiffOdd := hpairDiff.comp oddIndex_tendsto_atTop
  have hPxEven : Tendsto
      (fun k ↦ (FourNode.P lambda (x (2 * k))).coeffPair)
      atTop (nhds p.coeffPair) := by
    have ht := hp.sub hpairDiffEven
    simpa only [Function.comp_apply, sub_zero, sub_sub_cancel] using ht
  have hPxOdd : Tendsto
      (fun k ↦ (FourNode.P lambda (x (2 * k + 1))).coeffPair)
      atTop (nhds q.coeffPair) := by
    have ht := hq.sub hpairDiffOdd
    simpa only [Function.comp_apply, sub_zero, sub_sub_cancel] using ht
  obtain ⟨kappa, hkappa, hgramBoth⟩ :=
    exists_eventually_common_momentGramDet_lower_bound
      A hA v₀ hv₀ hgrade₀ nodes hnodes hcomponent hext
  have hgram : ∀ᶠ k in atTop,
      kappa ≤ FourNode.weightedMomentGramDet lambda (x k) := by
    simpa only [lambda, x] using hgramBoth.mono fun _ hk ↦ hk.2
  have hHx : Tendsto (fun k ↦ FourNode.H lambda (x k))
      atTop (nhds (tau ^ 2)) := by
    simpa only [lambda, x] using
      tendsto_principalWeights_H_arnoldiOrbit2
        A hA v₀ hv₀ hgrade₀ nodes hnodes hcomponent hext hnormalizer
  obtain ⟨Cupdate, hCupdate, hupdate⟩ :=
    exists_eventually_principalWeights_updateDefect_geometric
      A hA v₀ hv₀ hgrade₀ nodes hnodes hcomponent htau hCext
        hthetaNonneg hthetaLt
        (by simpa only [nodes] using hextGeometric) hnormalizer
  have hupdate' : ∀ᶠ k in atTop,
      ‖FourNode.weightVector (x (k + 1)) -
        FourNode.weightVector
          (FourNode.exactUpdateSeq lambda hlambdaInjective x k)‖ ≤
        Cupdate * theta ^ k := by
    simpa only [x, lambda, FourNode.exactUpdateSeq] using hupdate
  have hpositive : ∀ᶠ k in atTop, ∀ i, 0 < x k i := by
    exact Eventually.of_forall fun k i ↦ by
      change 0 < principalWeights A hA nodes
        (arnoldiOrbit2 A v₀ k) (hcomponent k) i
      rw [principalWeights_apply]
      exact normalizedPrincipalWeight_pos A hA nodes
        (arnoldiOrbit2 A v₀ k)
        (principalMass_pos_of_components_ne_zero A hA nodes
          (arnoldiOrbit2 A v₀ k) (hcomponent k)) i (hcomponent k i)
  obtain ⟨xStar, hxStarCoord, _hxStarP, _hxStarH, hxStarFiber⟩ :=
    exists_evenClusterWeight_mem_positiveFiber
      A hA v₀ hv₀ hgrade₀ tau htau p q hp hq hnormalizer
        nodes hnodes hfactor hvStar
  have hcomponentStar : ∀ i, component A hA vStar (nodes i) ≠ 0 := by
    intro i
    exact (mem_active_iff A hA vStar (nodes i)).1 (by
      simpa only [nodes] using
        orderedNodesOfFourClusterPoint_mem_active A hA vStar hcard i)
  have hmassStar : 0 < principalMass A hA nodes vStar :=
    principalMass_pos_of_components_ne_zero
      A hA nodes vStar hcomponentStar
  have hxStarPositive : ∀ i, 0 < xStar i := by
    intro i
    rw [hxStarCoord i]
    exact normalizedPrincipalWeight_pos A hA nodes vStar
      hmassStar i (hcomponentStar i)
  have hmiddle := FourNode.factor_eval_middle_nodes_neg_of_memFiber
    hlambda htau hfactor hxStarFiber hxStarPositive
  obtain ⟨rhoLim, hrhoLim, hRho⟩ :=
    FourNode.exists_tendsto_rhoSeq_of_asymptotically_exact_fourNode
      hlambda x htau hfactor hPxEven hPxOdd hHx hpositive
        hmiddle.1 hmiddle.2.1 hmiddle.2.2.1 hmiddle.2.2.2
        hkappa hCupdate hthetaPos hthetaLt hgram hupdate'
  let selectedLimit : Fin 4 → ℝ := fun i ↦
    tau ^ 2 * (lambda i - rhoLim) /
      (FourNode.E lambda i * p.toPolynomial.eval (lambda i))
  have hnormalizedSelected : ∀ i, Tendsto
      (fun k ↦ x (2 * k) i) atTop (nhds (selectedLimit i)) := by
    intro i
    have hRhoEven := hRho.comp evenIndex_tendsto_atTop
    have hRhoEven' : Tendsto
        (fun k ↦ FourNode.rho lambda (x (2 * k)))
        atTop (nhds rhoLim) := by
      change Tendsto (fun k ↦ FourNode.rho lambda (x (2 * k)))
        atTop (nhds rhoLim) at hRhoEven
      exact hRhoEven
    have hHEven := hHx.comp evenIndex_tendsto_atTop
    have hnode : p.toPolynomial.eval (lambda i) ≠ 0 :=
      (FourNode.factor_eval_ne_zero htau hfactor i).1
    simpa only [selectedLimit, Nat.add_zero] using
      FourNode.tendsto_weight_parity_of_tendsto_rho_P_H
        hlambdaInjective x 0 p (tau ^ 2) rhoLim hPxEven hHEven
          (by simpa only [Nat.add_zero] using hRhoEven') (fun j ↦
            (FourNode.factor_eval_ne_zero htau hfactor j).1) i
  have hmass : Tendsto (fun k ↦
      principalMass A hA nodes (arnoldiOrbit2 A v₀ k))
      atTop (nhds 1) := by
    have ht : Tendsto (fun k ↦ (1 : ℝ) -
        exteriorMass A hA nodes (arnoldiOrbit2 A v₀ k))
        atTop (nhds 1) := by
      simpa only [sub_zero] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ))
          atTop (nhds 1)).sub hext
    apply ht.congr'
    exact Eventually.of_forall fun k ↦
      (principalMass_eq_one_sub_exteriorMass A hA nodes hnodes
        (arnoldiOrbit2 A v₀ k)
        (norm_arnoldiOrbit2_of_initial_grade_three
          A hA v₀ hv₀ hgrade₀ k)).symm
  have hmassEven := hmass.comp evenIndex_tendsto_atTop
  have hrawSelected : ∀ i, Tendsto (fun k ↦
      weight A hA (arnoldiOrbit2 A v₀ (2 * k)) (nodes i))
      atTop (nhds (selectedLimit i)) := by
    intro i
    have ht := hmassEven.mul (hnormalizedSelected i)
    have heq : ∀ k,
        principalMass A hA nodes (arnoldiOrbit2 A v₀ (2 * k)) *
            x (2 * k) i =
          weight A hA (arnoldiOrbit2 A v₀ (2 * k)) (nodes i) := by
      intro k
      change principalMass A hA nodes (arnoldiOrbit2 A v₀ (2 * k)) *
          principalWeights A hA nodes (arnoldiOrbit2 A v₀ (2 * k))
            (hcomponent (2 * k)) i = _
      rw [principalWeights_apply, normalizedPrincipalWeight]
      field_simp [ne_of_gt (principalMass_pos_of_components_ne_zero
        A hA nodes (arnoldiOrbit2 A v₀ (2 * k)) (hcomponent (2 * k)))]
    have ht' := ht.congr' (Eventually.of_forall heq)
    simpa only [one_mul, Function.comp_apply] using ht'
  let rhoWeight : A.Eigenvalues → ℝ := fun mu ↦
    if hmu : mu ∈ Set.range nodes then
      selectedLimit (Classical.choose hmu) else 0
  have hweight : ∀ mu, Tendsto (fun k ↦
      weight A hA (arnoldiOrbit2 A v₀ (2 * k)) mu)
      atTop (nhds (rhoWeight mu)) := by
    intro mu
    by_cases hmu : mu ∈ Set.range nodes
    · let i : Fin 4 := Classical.choose hmu
      have hi : nodes i = mu := Classical.choose_spec hmu
      have ht := hrawSelected i
      rw [hi] at ht
      simpa only [rhoWeight, hmu, ↓reduceDIte, i] using ht
    · have ht := even_exterior_weight_tendsto_zero
        A hA v₀ hv₀ hgrade₀ tau p q hp hq hnormalizer
          nodes hfactor mu hmu
      simpa only [rhoWeight, hmu, ↓reduceDIte] using ht
  obtain ⟨vEven, hvEven⟩ :=
    exists_tendsto_arnoldiParity_of_weight_limits
      A hA v₀ hv₀ hgrade₀ 0 rhoWeight
        (by simpa only [Nat.add_zero] using hweight)
  have hOdd := arnoldiOrbit2_odd_tendsto_of_even_tendsto
    A hA v₀ hv₀ hgrade₀ p tau htau vEven hvEven hp
      (hnormalizer.comp evenIndex_tendsto_atTop)
  exact ⟨vEven, tau⁻¹ • polyApply A p.toPolynomial vEven,
    hvEven, hOdd⟩

end

end Spectral
end Forsythe
