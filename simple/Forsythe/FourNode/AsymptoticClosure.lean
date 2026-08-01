import Forsythe.FourNode.CoefficientAsymptotics
import Forsythe.FourNode.EventualClosure
import Forsythe.FourNode.MiddleGapAsymptotics
import Forsythe.FourNode.MultiplierAsymptotics
import Forsythe.FourNode.ParityAsymptotics
import Forsythe.FourNode.TailFloors

/-!
# Closure of an asymptotically exact four-node orbit

This module assembles the generic four-node estimates.  It is independent of
the spectral theorem: an operator application only has to supply paritywise
factor limits, a positive limiting height, a Gram floor, and a geometric
coordinate defect.
-/

set_option autoImplicit false

namespace Forsythe
namespace FourNode

open Filter Polynomial Set Topology

noncomputable section

/-- A positive four-node sequence with a geometrically small exact-update
defect has a convergent barycentric parameter once its two factor limits form
the ordered nodal quartic and have the interior-fiber sign pattern. -/
theorem exists_tendsto_rhoSeq_of_asymptotically_exact_fourNode
    {lambda : Fin 4 → ℝ} (hlambda : StrictMono lambda)
    (x : ℕ → Weights)
    {tau : ℝ} (htau : 0 < tau) {p q : MonicQuadratic}
    (hfactor : p.toPolynomial * q.toPolynomial =
      nodalQuartic lambda + C (tau ^ 2))
    (hp : Tendsto (fun k ↦ (P lambda (x (2 * k))).coeffPair)
      atTop (nhds p.coeffPair))
    (hq : Tendsto (fun k ↦ (P lambda (x (2 * k + 1))).coeffPair)
      atTop (nhds q.coeffPair))
    (hH : Tendsto (fun k ↦ H lambda (x k))
      atTop (nhds (tau ^ 2)))
    (hpositive : ∀ᶠ k in atTop, ∀ i, 0 < x k i)
    (hp1 : p.toPolynomial.eval (lambda 1) < 0)
    (hp2 : p.toPolynomial.eval (lambda 2) < 0)
    (hq1 : q.toPolynomial.eval (lambda 1) < 0)
    (hq2 : q.toPolynomial.eval (lambda 2) < 0)
    {delta₀ B theta : ℝ}
    (hdelta₀ : 0 < delta₀) (hB : 0 ≤ B)
    (hthetaPos : 0 < theta) (hthetaLt : theta < 1)
    (hgram : ∀ᶠ k in atTop,
      delta₀ ≤ weightedMomentGramDet lambda (x k))
    (hdefect : ∀ᶠ k in atTop,
      ‖weightVector (x (k + 1)) -
          weightVector (exactUpdateSeq lambda hlambda.injective x k)‖ ≤
        B * theta ^ k) :
    ∃ rhoLim ∈ Icc (lambda 1) (lambda 2),
      Tendsto (rhoSeq lambda x) atTop (nhds rhoLim) := by
  have hthetaNonneg : 0 ≤ theta := hthetaPos.le
  have hdefectUpper : Tendsto (fun k : ℕ ↦ B * theta ^ k)
      atTop (nhds 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one hthetaNonneg hthetaLt)
  have hdefectZero : Tendsto (fun k ↦
      ‖weightVector (x (k + 1)) -
        weightVector (exactUpdateSeq lambda hlambda.injective x k)‖)
      atTop (nhds 0) := by
    exact squeeze_zero'
      (Eventually.of_forall fun _ ↦ norm_nonneg _)
      hdefect hdefectUpper
  let eta₀ : ℝ := tau ^ 2 / 2
  have heta₀ : 0 < eta₀ := by
    dsimp only [eta₀]
    positivity
  have hheightFloor : ∀ᶠ k in atTop, eta₀ ≤ H lambda (x k) :=
    ((tendsto_order.1 hH).1 eta₀ (by
      dsimp only [eta₀]
      nlinarith [sq_pos_of_pos htau])).mono fun _ hk ↦ hk.le
  obtain ⟨delta, eta, hdelta, heta, hfloors⟩ :=
    exists_eventually_perturbationFloors_of_updateDefect_tendsto_zero
      hlambda.injective x hdelta₀ heta₀ hgram hheightFloor hdefectZero
  have hgramX : ∀ᶠ k in atTop,
      delta ≤ weightedMomentGramDet lambda (x k) :=
    hfloors.mono fun _ hk ↦ hk.1
  have hgramY : ∀ᶠ k in atTop,
      delta ≤ weightedMomentGramDet lambda
        (exactUpdateSeq lambda hlambda.injective x k) :=
    hfloors.mono fun _ hk ↦ hk.2.1
  have hPy := tendsto_P_exactUpdateSeq_parity hlambda.injective x p q
    hdelta hgramX hgramY hdefectZero hp hq
  have hAlpha := tendsto_alphaSeq_zero_of_parity_factorization
    hlambda.injective x p q (tau ^ 2) hdelta hgramX hgramY
      hdefectZero hp hq hfactor
  have hHy := tendsto_H_exactUpdateSeq_of_tendsto_H
    hlambda.injective x (tau ^ 2) hdelta hgramX hgramY
      hdefectZero hH
  have hRhoOpen :=
    eventually_rho_mem_open_middleGap_of_parity_factor_signs
      hlambda x hpositive hp hq hp1 hp2 hq1 hq2
  have hRho : ∀ᶠ k in atTop,
      rhoSeq lambda x k ∈ Icc (lambda 1) (lambda 2) :=
    hRhoOpen.mono fun _ hk ↦ ⟨hk.1.le, hk.2.le⟩
  have hYpositive :=
    eventually_exactUpdateSeq_all_positive_of_parity_factors
      hlambda.injective x htau hfactor hpositive hp hq
  let y : ℕ → Weights := fun k ↦
    exactUpdateSeq lambda hlambda.injective x k
  have hRhoYOpen : ∀ᶠ k in atTop,
      rhoSeq lambda y k ∈ Ioo (lambda 1) (lambda 2) := by
    apply eventually_rho_mem_open_middleGap_of_parity_factor_signs
      hlambda y hYpositive hPy.1 hPy.2 hq1 hq2 hp1 hp2
  have hRhoY : ∀ᶠ k in atTop,
      rho lambda (exactUpdateSeq lambda hlambda.injective x k) ∈
        Icc (lambda 1) (lambda 2) := by
    simpa only [y, rhoSeq] using
      hRhoYOpen.mono fun _ hk ↦ ⟨hk.1.le, hk.2.le⟩
  obtain ⟨Cc, hCc, hcBound, hlocal⟩ :=
    exists_rhoIncrementCoeff_bound_and_local_separation
      hlambda x htau hRho hHy
  have hRhoDiff := tendsto_rhoSeq_sub_rho_exactUpdate_of_alpha_zero
    hlambda x hCc hcBound hAlpha
  obtain ⟨hden, hmpos, hm⟩ :=
    remainderMultiplier_eventually_pos_tendsto_one
      hlambda x htau hfactor hPy.1 hPy.2 hRho hRhoY hRhoDiff
  exact exists_tendsto_rhoSeq_of_eventually_geometric_weightDefect
    hlambda.injective x hdelta heta hB hthetaPos hthetaLt
      hfloors hdefect hden hmpos hm hAlpha 1 2
      (hlambda (by decide)) hCc hcBound hRho hlocal

end

end FourNode
end Forsythe
