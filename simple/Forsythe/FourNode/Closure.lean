import Forsythe.Dynamics.ScalarClosure
import Forsythe.FourNode.Perturbation

/-!
# Scalar closure of a perturbed four-node orbit

This module is the interface between the rational four-node perturbation
estimates and the generic scalar closure lemma.  Its hypotheses expose the
precise quantities which the spectral/exterior analysis must eventually
supply: common denominator floors, geometric coordinate defects, a positive
near-identity remainder multiplier, decay of the interpolation coefficient,
and signed control of the coefficient in the `rho` increment.
-/

set_option autoImplicit false

namespace Forsythe
namespace FourNode

open Filter Polynomial Set Topology

noncomputable section

/-- The generic scalar closure lemma applied to the exact four-node
perturbation package.  The interval endpoints are selected nodes, so the
conclusion keeps the limiting barycentric parameter in one fixed compact
node gap.

No asymptotic hypothesis is hidden in this wrapper: positivity and
near-identity convergence of the quotient multiplier, decay of `alpha`,
boundedness and local signed separation of the `rho` coefficient, and all
denominator assumptions are explicit arguments. -/
theorem exists_tendsto_rhoSeq_of_geometric_weightDefect
    {lambda : Fin 4 → ℝ} (hlambda : Function.Injective lambda)
    (x : ℕ → Weights)
    {delta eta B theta Cc : ℝ}
    (hdelta : 0 < delta) (heta : 0 < eta) (hB : 0 ≤ B)
    (hthetaPos : 0 < theta) (hthetaLt : theta < 1)
    (hfloors : PerturbationFloors lambda hlambda x delta eta)
    (hdefect : HasGeometricWeightDefect lambda hlambda x B theta)
    (hden : ∀ k, newRemainderCoeff lambda hlambda x k ≠ 0)
    (hmpos : ∀ k, 0 < remainderMultiplier lambda hlambda x k)
    (hm : Tendsto (remainderMultiplier lambda hlambda x)
      atTop (nhds 1))
    (hAlphaZero : Tendsto (alphaSeq lambda hlambda x)
      atTop (nhds 0))
    (left right : Fin 4) (_hgap : lambda left < lambda right)
    (hCc : 0 ≤ Cc)
    (hcBound : ∀ k, |rhoIncrementCoeff lambda hlambda x k| ≤ Cc)
    (hRho : ∀ k,
      rhoSeq lambda x k ∈ Set.Icc (lambda left) (lambda right))
    (hlocal : ScalarDynamics.EventuallyLocallySeparatedCoefficient
      (rhoSeq lambda x) (rhoIncrementCoeff lambda hlambda x)
      (lambda left) (lambda right)) :
    ∃ rhoLim ∈ Set.Icc (lambda left) (lambda right),
      Tendsto (rhoSeq lambda x) atTop (nhds rhoLim) := by
  have hrec := perturbed_recurrences_with_geometric_errors
    hlambda x hdelta heta hfloors hdefect hden
  apply ScalarDynamics.exists_tendsto_of_geometric_perturbed_normalizedRecurrence
    (alphaSeq lambda hlambda x)
    (remainderMultiplier lambda hlambda x)
    (bAlpha lambda hlambda x)
    (rhoSeq lambda x)
    (rhoIncrementCoeff lambda hlambda x)
    (bRho lambda hlambda x)
    (CAlpha := alphaLipschitzConstant lambda delta eta delta * B)
    (CRho := rhoLipschitzConstant lambda delta eta * B)
    (Cc := Cc) (theta := theta)
  · exact hmpos
  · exact hm
  · exact fun k ↦ (hrec k).1
  · exact mul_nonneg
      (alphaLipschitzConstant_nonneg lambda hdelta heta hdelta) hB
  · exact mul_nonneg
      (rhoLipschitzConstant_nonneg lambda hdelta heta) hB
  · exact hCc
  · exact hthetaPos
  · exact hthetaLt
  · exact fun k ↦ (hrec k).2.2.1
  · exact fun k ↦ (hrec k).2.1
  · exact fun k ↦ (hrec k).2.2.2
  · exact hcBound
  · exact hAlphaZero
  · exact hRho
  · exact hlocal

/-- The node formula for `rho` recovers every weight coordinate once
`rho`, the orthogonal quadratic, and the height converge and the limiting
quadratic is nonzero at the selected nodes. -/
theorem tendsto_weight_apply_of_tendsto_rho_P_H
    {lambda : Fin 4 → ℝ} (hlambda : Function.Injective lambda)
    (u : ℕ → Weights) (p : MonicQuadratic) (HLim rhoLim : ℝ)
    (hP : Tendsto (fun k ↦ (P lambda (u k)).coeffPair)
      atTop (nhds p.coeffPair))
    (hH : Tendsto (fun k ↦ H lambda (u k)) atTop (nhds HLim))
    (hRho : Tendsto (fun k ↦ rho lambda (u k))
      atTop (nhds rhoLim))
    (hpNode : ∀ i, p.toPolynomial.eval (lambda i) ≠ 0) :
    ∀ i, Tendsto (fun k ↦ u k i) atTop
      (nhds (HLim * (lambda i - rhoLim) /
        (E lambda i * p.toPolynomial.eval (lambda i)))) := by
  intro i
  have hLinear : Tendsto (fun k ↦ (P lambda (u k)).linearCoeff)
      atTop (nhds p.linearCoeff) := by
    simpa only [MonicQuadratic.coeffPair] using hP.fst_nhds
  have hConstant : Tendsto (fun k ↦ (P lambda (u k)).constantCoeff)
      atTop (nhds p.constantCoeff) := by
    simpa only [MonicQuadratic.coeffPair] using hP.snd_nhds
  have hEval : Tendsto
      (fun k ↦ (P lambda (u k)).toPolynomial.eval (lambda i))
      atTop (nhds (p.toPolynomial.eval (lambda i))) := by
    simpa only [MonicQuadratic.eval] using
      ((tendsto_const_nhds.pow 2).add
        (hLinear.mul tendsto_const_nhds)).add hConstant
  have hNumerator : Tendsto
      (fun k ↦ H lambda (u k) * (lambda i - rho lambda (u k)))
      atTop (nhds (HLim * (lambda i - rhoLim))) :=
    hH.mul (tendsto_const_nhds.sub hRho)
  have hDenominator : Tendsto
      (fun k ↦ E lambda i *
        (P lambda (u k)).toPolynomial.eval (lambda i))
      atTop (nhds (E lambda i * p.toPolynomial.eval (lambda i))) :=
    tendsto_const_nhds.mul hEval
  have hE : E lambda i ≠ 0 := E_ne_zero hlambda i
  have hQuotient : Tendsto
      (fun k ↦ H lambda (u k) * (lambda i - rho lambda (u k)) /
        (E lambda i * (P lambda (u k)).toPolynomial.eval (lambda i)))
      atTop (nhds (HLim * (lambda i - rhoLim) /
        (E lambda i * p.toPolynomial.eval (lambda i)))) :=
    hNumerator.div hDenominator (mul_ne_zero hE (hpNode i))
  apply hQuotient.congr'
  filter_upwards [hEval.eventually_ne (hpNode i)] with k hk
  have hid := weight_mul_P_eval_eq_height_mul_sub_rho_div_E
    hlambda (u k) i
  have hcleared := (eq_div_iff hE).1 hid
  symm
  apply (eq_div_iff (mul_ne_zero hE hk)).2
  calc
    u k i * (E lambda i *
        (P lambda (u k)).toPolynomial.eval (lambda i)) =
        (u k i * (P lambda (u k)).toPolynomial.eval (lambda i)) *
          E lambda i := by ring
    _ = H lambda (u k) * (lambda i - rho lambda (u k)) := hcleared

/-- Parity-specialized form of
`tendsto_weight_apply_of_tendsto_rho_P_H`. -/
theorem tendsto_weight_parity_of_tendsto_rho_P_H
    {lambda : Fin 4 → ℝ} (hlambda : Function.Injective lambda)
    (x : ℕ → Weights) (r : ℕ)
    (p : MonicQuadratic) (HLim rhoLim : ℝ)
    (hP : Tendsto
      (fun k ↦ (P lambda (x (2 * k + r))).coeffPair)
      atTop (nhds p.coeffPair))
    (hH : Tendsto (fun k ↦ H lambda (x (2 * k + r)))
      atTop (nhds HLim))
    (hRho : Tendsto (fun k ↦ rho lambda (x (2 * k + r)))
      atTop (nhds rhoLim))
    (hpNode : ∀ i, p.toPolynomial.eval (lambda i) ≠ 0) :
    ∀ i, Tendsto (fun k ↦ x (2 * k + r) i) atTop
      (nhds (HLim * (lambda i - rhoLim) /
        (E lambda i * p.toPolynomial.eval (lambda i)))) :=
  tendsto_weight_apply_of_tendsto_rho_P_H hlambda
    (fun k ↦ x (2 * k + r)) p HLim rhoLim hP hH hRho hpNode

end

end FourNode
end Forsythe
