import Forsythe.Dynamics.Parity
import Forsythe.FourNode.Perturbation

/-!
# Parity asymptotics for perturbed four-node updates

Let `y k = T (x k)` be the exact four-node update associated with a
perturbed weight sequence.  If `x (k + 1)` and `y k` become close and the
two moment Gram determinants stay uniformly coercive on a tail, then their
monic orthogonal quadratics and residual heights become close.  Consequently,
paritywise limits of `P (x k)` transfer to the opposite parity of `P (y k)`.

The final theorem records the corresponding decay of the interpolation
coefficient `alpha`: the coefficient of `z^3` in the limiting factorization
`p q = Pi + H` is exactly the sum of the two limiting linear coefficients.
All convergence of monic quadratics is expressed in the fixed product norm
on their two free coefficients.
-/

set_option autoImplicit false

namespace Forsythe
namespace FourNode

open Filter Polynomial Topology

noncomputable section

/-- The coefficient of `z^3` in a product of two monic quadratics is the
sum of their linear coefficients. -/
private theorem coeff_three_mul_monicQuadratic
    (p q : MonicQuadratic) :
    (p.toPolynomial * q.toPolynomial).coeff 3 =
      p.linearCoeff + q.linearCoeff := by
  rw [MonicQuadratic.toPolynomial, MonicQuadratic.toPolynomial]
  ring_nf
  have hmiddle :
      (C p.linearCoeff * C q.linearCoeff * X ^ 2 : Polynomial ℝ).coeff 3 = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    compute_degree
    norm_num
  simp [coeff_add, coeff_mul_C, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C]
  exact hmiddle

/-- A limiting factorization determines the sum of the two free linear
coefficients from the cubic coefficient of the nodal quartic. -/
theorem linearCoeff_add_eq_nodalQuartic_coeff_three_of_factorization
    (lambda : Fin 4 → ℝ) (p q : MonicQuadratic) (K : ℝ)
    (hfactor : p.toPolynomial * q.toPolynomial =
      nodalQuartic lambda + C K) :
    p.linearCoeff + q.linearCoeff = (nodalQuartic lambda).coeff 3 := by
  have hcoeff := congrArg (fun f : Polynomial ℝ ↦ f.coeff 3) hfactor
  simpa only [coeff_three_mul_monicQuadratic, coeff_add,
    coeff_C_of_ne_zero (by norm_num : (3 : ℕ) ≠ 0), add_zero] using hcoeff

/-- If the perturbed next state approaches the exact update and both states
have a common eventual Gram floor, then their monic quadratic coefficient
pairs approach one another. -/
theorem tendsto_P_exactUpdateSeq_coeffPair_sub_succ
    {lambda : Fin 4 → ℝ} (hlambda : Function.Injective lambda)
    (x : ℕ → Weights) {delta : ℝ}
    (hdelta : 0 < delta)
    (hgramX : ∀ᶠ k in atTop,
      delta ≤ weightedMomentGramDet lambda (x k))
    (hgramY : ∀ᶠ k in atTop,
      delta ≤ weightedMomentGramDet lambda
        (exactUpdateSeq lambda hlambda x k))
    (hdefect : Tendsto (fun k ↦
      ‖weightVector (x (k + 1)) -
        weightVector (exactUpdateSeq lambda hlambda x k)‖)
      atTop (nhds 0)) :
    Tendsto (fun k ↦
      (P lambda (exactUpdateSeq lambda hlambda x k)).coeffPair -
        (P lambda (x (k + 1))).coeffPair)
      atTop (nhds 0) := by
  let Cpair := coefficientPairLipschitzConstant lambda delta
  have hgramXSucc : ∀ᶠ k in atTop,
      delta ≤ weightedMomentGramDet lambda (x (k + 1)) :=
    (tendsto_add_atTop_nat 1).eventually hgramX
  have hbound : ∀ᶠ k in atTop,
      ‖(P lambda (exactUpdateSeq lambda hlambda x k)).coeffPair -
          (P lambda (x (k + 1))).coeffPair‖ ≤
        Cpair *
          ‖weightVector (x (k + 1)) -
            weightVector (exactUpdateSeq lambda hlambda x k)‖ := by
    filter_upwards [hgramY, hgramXSucc] with k hy hx
    have h := P_coeffPair_sub_norm_le_of_gram_floor lambda
      (exactUpdateSeq lambda hlambda x k) (x (k + 1)) hdelta hy hx
    simpa only [Cpair, norm_sub_rev (weightVector
      (exactUpdateSeq lambda hlambda x k)) (weightVector (x (k + 1)))] using h
  have hupper : Tendsto (fun k ↦
      Cpair *
        ‖weightVector (x (k + 1)) -
          weightVector (exactUpdateSeq lambda hlambda x k)‖)
      atTop (nhds 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hdefect
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero'
    (Eventually.of_forall fun k ↦ norm_nonneg _)
    hbound hupper

private theorem tendsto_even_index :
    Tendsto (fun k : ℕ ↦ 2 * k) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  exact eventually_atTop.2 ⟨b, fun k hk ↦ by omega⟩

private theorem tendsto_odd_index :
    Tendsto (fun k : ℕ ↦ 2 * k + 1) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  exact eventually_atTop.2 ⟨b, fun k hk ↦ by omega⟩

/-- The exact updates of the even states inherit the odd polynomial limit
of the perturbed sequence. -/
theorem tendsto_P_exactUpdateSeq_even
    {lambda : Fin 4 → ℝ} (hlambda : Function.Injective lambda)
    (x : ℕ → Weights) (q : MonicQuadratic) {delta : ℝ}
    (hdelta : 0 < delta)
    (hgramX : ∀ᶠ k in atTop,
      delta ≤ weightedMomentGramDet lambda (x k))
    (hgramY : ∀ᶠ k in atTop,
      delta ≤ weightedMomentGramDet lambda
        (exactUpdateSeq lambda hlambda x k))
    (hdefect : Tendsto (fun k ↦
      ‖weightVector (x (k + 1)) -
        weightVector (exactUpdateSeq lambda hlambda x k)‖)
      atTop (nhds 0))
    (hPodd : Tendsto (fun k ↦ (P lambda (x (2 * k + 1))).coeffPair)
      atTop (nhds q.coeffPair)) :
    Tendsto (fun k ↦
      (P lambda (exactUpdateSeq lambda hlambda x (2 * k))).coeffPair)
      atTop (nhds q.coeffPair) := by
  have hdiff := (tendsto_P_exactUpdateSeq_coeffPair_sub_succ hlambda x
    hdelta hgramX hgramY hdefect).comp tendsto_even_index
  have hsum := hdiff.add hPodd
  simpa only [Function.comp_apply, zero_add, sub_add_cancel] using hsum

/-- The exact updates of the odd states inherit the even polynomial limit
of the perturbed sequence. -/
theorem tendsto_P_exactUpdateSeq_odd
    {lambda : Fin 4 → ℝ} (hlambda : Function.Injective lambda)
    (x : ℕ → Weights) (p : MonicQuadratic) {delta : ℝ}
    (hdelta : 0 < delta)
    (hgramX : ∀ᶠ k in atTop,
      delta ≤ weightedMomentGramDet lambda (x k))
    (hgramY : ∀ᶠ k in atTop,
      delta ≤ weightedMomentGramDet lambda
        (exactUpdateSeq lambda hlambda x k))
    (hdefect : Tendsto (fun k ↦
      ‖weightVector (x (k + 1)) -
        weightVector (exactUpdateSeq lambda hlambda x k)‖)
      atTop (nhds 0))
    (hPeven : Tendsto (fun k ↦ (P lambda (x (2 * k))).coeffPair)
      atTop (nhds p.coeffPair)) :
    Tendsto (fun k ↦
      (P lambda (exactUpdateSeq lambda hlambda x (2 * k + 1))).coeffPair)
      atTop (nhds p.coeffPair) := by
  have hdiff := (tendsto_P_exactUpdateSeq_coeffPair_sub_succ hlambda x
    hdelta hgramX hgramY hdefect).comp tendsto_odd_index
  have hPevenShift := hPeven.comp (tendsto_add_atTop_nat 1)
  have hsum := hdiff.add hPevenShift
  have hsum' : Tendsto (fun k ↦
      (P lambda (exactUpdateSeq lambda hlambda x (2 * k + 1))).coeffPair)
      atTop (nhds (0 + p.coeffPair)) := by
    apply hsum.congr'
    exact Eventually.of_forall fun k ↦ by
      dsimp only [Function.comp_apply]
      have hindex : 2 * (k + 1) = (2 * k + 1) + 1 := by omega
      rw [hindex, sub_add_cancel]
  simpa only [zero_add] using hsum'

/-- Both opposite-parity polynomial limits for the exact updates. -/
theorem tendsto_P_exactUpdateSeq_parity
    {lambda : Fin 4 → ℝ} (hlambda : Function.Injective lambda)
    (x : ℕ → Weights) (p q : MonicQuadratic) {delta : ℝ}
    (hdelta : 0 < delta)
    (hgramX : ∀ᶠ k in atTop,
      delta ≤ weightedMomentGramDet lambda (x k))
    (hgramY : ∀ᶠ k in atTop,
      delta ≤ weightedMomentGramDet lambda
        (exactUpdateSeq lambda hlambda x k))
    (hdefect : Tendsto (fun k ↦
      ‖weightVector (x (k + 1)) -
        weightVector (exactUpdateSeq lambda hlambda x k)‖)
      atTop (nhds 0))
    (hPeven : Tendsto (fun k ↦ (P lambda (x (2 * k))).coeffPair)
      atTop (nhds p.coeffPair))
    (hPodd : Tendsto (fun k ↦ (P lambda (x (2 * k + 1))).coeffPair)
      atTop (nhds q.coeffPair)) :
    Tendsto (fun k ↦
      (P lambda (exactUpdateSeq lambda hlambda x (2 * k))).coeffPair)
        atTop (nhds q.coeffPair) ∧
    Tendsto (fun k ↦
      (P lambda (exactUpdateSeq lambda hlambda x (2 * k + 1))).coeffPair)
        atTop (nhds p.coeffPair) :=
  ⟨tendsto_P_exactUpdateSeq_even hlambda x q hdelta hgramX hgramY
      hdefect hPodd,
    tendsto_P_exactUpdateSeq_odd hlambda x p hdelta hgramX hgramY
      hdefect hPeven⟩

/-- Under a limiting factorization, the interpolation coefficient of a
perturbed four-node sequence tends to zero. -/
theorem tendsto_alphaSeq_zero_of_parity_factorization
    {lambda : Fin 4 → ℝ} (hlambda : Function.Injective lambda)
    (x : ℕ → Weights) (p q : MonicQuadratic) (K : ℝ) {delta : ℝ}
    (hdelta : 0 < delta)
    (hgramX : ∀ᶠ k in atTop,
      delta ≤ weightedMomentGramDet lambda (x k))
    (hgramY : ∀ᶠ k in atTop,
      delta ≤ weightedMomentGramDet lambda
        (exactUpdateSeq lambda hlambda x k))
    (hdefect : Tendsto (fun k ↦
      ‖weightVector (x (k + 1)) -
        weightVector (exactUpdateSeq lambda hlambda x k)‖)
      atTop (nhds 0))
    (hPeven : Tendsto (fun k ↦ (P lambda (x (2 * k))).coeffPair)
      atTop (nhds p.coeffPair))
    (hPodd : Tendsto (fun k ↦ (P lambda (x (2 * k + 1))).coeffPair)
      atTop (nhds q.coeffPair))
    (hfactor : p.toPolynomial * q.toPolynomial =
      nodalQuartic lambda + C K) :
    Tendsto (alphaSeq lambda hlambda x) atTop (nhds 0) := by
  have hlimits := tendsto_P_exactUpdateSeq_parity hlambda x p q hdelta
    hgramX hgramY hdefect hPeven hPodd
  have hcubic :=
    linearCoeff_add_eq_nodalQuartic_coeff_three_of_factorization
      lambda p q K hfactor
  have hPevenLinear : Tendsto
      (fun k ↦ (P lambda (x (2 * k))).linearCoeff)
      atTop (nhds p.linearCoeff) := by
    simpa only [MonicQuadratic.coeffPair] using hPeven.fst_nhds
  have hPoddLinear : Tendsto
      (fun k ↦ (P lambda (x (2 * k + 1))).linearCoeff)
      atTop (nhds q.linearCoeff) := by
    simpa only [MonicQuadratic.coeffPair] using hPodd.fst_nhds
  have hYEvenLinear : Tendsto (fun k ↦
      (P lambda (exactUpdateSeq lambda hlambda x (2 * k))).linearCoeff)
      atTop (nhds q.linearCoeff) := by
    simpa only [MonicQuadratic.coeffPair] using hlimits.1.fst_nhds
  have hYOddLinear : Tendsto (fun k ↦
      (P lambda (exactUpdateSeq lambda hlambda x (2 * k + 1))).linearCoeff)
      atTop (nhds p.linearCoeff) := by
    simpa only [MonicQuadratic.coeffPair] using hlimits.2.fst_nhds
  have hconst : Tendsto
      (fun _ : ℕ ↦ (nodalQuartic lambda).coeff 3)
      atTop (nhds ((nodalQuartic lambda).coeff 3)) := tendsto_const_nhds
  have hevenRaw : Tendsto (fun k ↦
      (P lambda (x (2 * k))).linearCoeff +
        (P lambda (exactUpdateSeq lambda hlambda x (2 * k))).linearCoeff -
          (nodalQuartic lambda).coeff 3)
      atTop (nhds
        (p.linearCoeff + q.linearCoeff - (nodalQuartic lambda).coeff 3)) :=
    (hPevenLinear.add hYEvenLinear).sub hconst
  have hoddRaw : Tendsto (fun k ↦
      (P lambda (x (2 * k + 1))).linearCoeff +
        (P lambda (exactUpdateSeq lambda hlambda x (2 * k + 1))).linearCoeff -
          (nodalQuartic lambda).coeff 3)
      atTop (nhds
        (q.linearCoeff + p.linearCoeff - (nodalQuartic lambda).coeff 3)) :=
    (hPoddLinear.add hYOddLinear).sub hconst
  have heven : Tendsto (fun k ↦ alphaSeq lambda hlambda x (2 * k))
      atTop (nhds 0) := by
    simpa only [alphaSeq, alpha_eq_linearCoeff_add, exactUpdateSeq_apply,
      hcubic, sub_self] using hevenRaw
  have hodd : Tendsto (fun k ↦ alphaSeq lambda hlambda x (2 * k + 1))
      atTop (nhds 0) := by
    rw [add_comm p.linearCoeff q.linearCoeff] at hcubic
    simpa only [alphaSeq, alpha_eq_linearCoeff_add, exactUpdateSeq_apply,
      hcubic, sub_self] using hoddRaw
  exact tendsto_of_even_odd heven hodd

/-- The exact update height differs asymptotically from the height of the
next perturbed state. -/
theorem tendsto_H_exactUpdateSeq_sub_succ
    {lambda : Fin 4 → ℝ} (hlambda : Function.Injective lambda)
    (x : ℕ → Weights) {delta : ℝ}
    (hdelta : 0 < delta)
    (hgramX : ∀ᶠ k in atTop,
      delta ≤ weightedMomentGramDet lambda (x k))
    (hgramY : ∀ᶠ k in atTop,
      delta ≤ weightedMomentGramDet lambda
        (exactUpdateSeq lambda hlambda x k))
    (hdefect : Tendsto (fun k ↦
      ‖weightVector (x (k + 1)) -
        weightVector (exactUpdateSeq lambda hlambda x k)‖)
      atTop (nhds 0)) :
    Tendsto (fun k ↦
      H lambda (exactUpdateSeq lambda hlambda x k) - H lambda (x (k + 1)))
      atTop (nhds 0) := by
  let CH := heightLipschitzConstant lambda delta
  have hgramXSucc : ∀ᶠ k in atTop,
      delta ≤ weightedMomentGramDet lambda (x (k + 1)) :=
    (tendsto_add_atTop_nat 1).eventually hgramX
  have hbound : ∀ᶠ k in atTop,
      |H lambda (exactUpdateSeq lambda hlambda x k) - H lambda (x (k + 1))| ≤
        CH * ‖weightVector (x (k + 1)) -
          weightVector (exactUpdateSeq lambda hlambda x k)‖ := by
    filter_upwards [hgramY, hgramXSucc] with k hy hx
    have h := abs_height_sub_le_of_gram_floor lambda
      (exactUpdateSeq lambda hlambda x k) (x (k + 1)) hdelta hy hx
    simpa only [CH, norm_sub_rev (weightVector
      (exactUpdateSeq lambda hlambda x k)) (weightVector (x (k + 1)))] using h
  have hupper : Tendsto (fun k ↦
      CH * ‖weightVector (x (k + 1)) -
        weightVector (exactUpdateSeq lambda hlambda x k)‖)
      atTop (nhds 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hdefect
  apply (tendsto_zero_iff_abs_tendsto_zero _).2
  exact squeeze_zero'
    (Eventually.of_forall fun k ↦ abs_nonneg _)
    hbound hupper

/-- Convergence of the perturbed heights transfers to the associated exact
update heights. -/
theorem tendsto_H_exactUpdateSeq_of_tendsto_H
    {lambda : Fin 4 → ℝ} (hlambda : Function.Injective lambda)
    (x : ℕ → Weights) (HLim : ℝ) {delta : ℝ}
    (hdelta : 0 < delta)
    (hgramX : ∀ᶠ k in atTop,
      delta ≤ weightedMomentGramDet lambda (x k))
    (hgramY : ∀ᶠ k in atTop,
      delta ≤ weightedMomentGramDet lambda
        (exactUpdateSeq lambda hlambda x k))
    (hdefect : Tendsto (fun k ↦
      ‖weightVector (x (k + 1)) -
        weightVector (exactUpdateSeq lambda hlambda x k)‖)
      atTop (nhds 0))
    (hH : Tendsto (fun k ↦ H lambda (x k)) atTop (nhds HLim)) :
    Tendsto (fun k ↦ H lambda (exactUpdateSeq lambda hlambda x k))
      atTop (nhds HLim) := by
  have hdiff := tendsto_H_exactUpdateSeq_sub_succ hlambda x hdelta
    hgramX hgramY hdefect
  have hshift := hH.comp (tendsto_add_atTop_nat 1)
  have hsum := hdiff.add hshift
  simpa only [Function.comp_apply, zero_add, sub_add_cancel] using hsum

end

end FourNode
end Forsythe
