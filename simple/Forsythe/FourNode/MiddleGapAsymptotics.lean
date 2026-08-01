import Forsythe.Dynamics.Parity
import Forsythe.FourNode.Gap
import Forsythe.FourNode.Perturbation

/-!
# Eventual confinement to the ordered middle gap

The limiting quadratic factors are negative at both middle nodes.  Paritywise
coefficient convergence transfers those two strict inequalities to the
finite iterates, and the node formula then confines `rho` to the middle
gap.  The same argument applies to the exact four-node update.
-/

set_option autoImplicit false

namespace Forsythe
namespace FourNode

open Filter Polynomial Set Topology

noncomputable section

/-- Coefficient-pair convergence implies convergence of evaluation at any
fixed real point. -/
theorem tendsto_monicQuadratic_eval_of_coeffPair
    (f : ℕ → MonicQuadratic) (p : MonicQuadratic)
    (h : Tendsto (fun k ↦ (f k).coeffPair) atTop (nhds p.coeffPair))
    (t : ℝ) :
    Tendsto (fun k ↦ (f k).toPolynomial.eval t)
      atTop (nhds (p.toPolynomial.eval t)) := by
  have hlinear : Tendsto (fun k ↦ (f k).linearCoeff)
      atTop (nhds p.linearCoeff) := by
    simpa only [MonicQuadratic.coeffPair] using h.fst_nhds
  have hconstant : Tendsto (fun k ↦ (f k).constantCoeff)
      atTop (nhds p.constantCoeff) := by
    simpa only [MonicQuadratic.coeffPair] using h.snd_nhds
  simpa only [MonicQuadratic.eval] using
    ((tendsto_const_nhds.pow 2).add
      (hlinear.mul tendsto_const_nhds)).add hconstant

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

/-- Paritywise convergence to factors which are negative at both middle
nodes eventually confines every barycentric parameter to the open middle
gap. -/
theorem eventually_rho_mem_open_middleGap_of_parity_factor_signs
    {lambda : Fin 4 → ℝ} (hlambda : StrictMono lambda)
    (x : ℕ → Weights) {p q : MonicQuadratic}
    (hpositive : ∀ᶠ k in atTop, ∀ i, 0 < x k i)
    (hp : Tendsto (fun k ↦ (P lambda (x (2 * k))).coeffPair)
      atTop (nhds p.coeffPair))
    (hq : Tendsto (fun k ↦ (P lambda (x (2 * k + 1))).coeffPair)
      atTop (nhds q.coeffPair))
    (hp1 : p.toPolynomial.eval (lambda 1) < 0)
    (hp2 : p.toPolynomial.eval (lambda 2) < 0)
    (hq1 : q.toPolynomial.eval (lambda 1) < 0)
    (hq2 : q.toPolynomial.eval (lambda 2) < 0) :
    ∀ᶠ k in atTop,
      rhoSeq lambda x k ∈ Ioo (lambda 1) (lambda 2) := by
  have hpositiveEven : ∀ᶠ k in atTop, ∀ i, 0 < x (2 * k) i :=
    evenIndex_tendsto_atTop.eventually hpositive
  have hpositiveOdd : ∀ᶠ k in atTop, ∀ i, 0 < x (2 * k + 1) i :=
    oddIndex_tendsto_atTop.eventually hpositive
  have hpEval1 := tendsto_monicQuadratic_eval_of_coeffPair
    (fun k ↦ P lambda (x (2 * k))) p hp (lambda 1)
  have hpEval2 := tendsto_monicQuadratic_eval_of_coeffPair
    (fun k ↦ P lambda (x (2 * k))) p hp (lambda 2)
  have hqEval1 := tendsto_monicQuadratic_eval_of_coeffPair
    (fun k ↦ P lambda (x (2 * k + 1))) q hq (lambda 1)
  have hqEval2 := tendsto_monicQuadratic_eval_of_coeffPair
    (fun k ↦ P lambda (x (2 * k + 1))) q hq (lambda 2)
  have heven : ∀ᶠ k in atTop,
      rhoSeq lambda x (2 * k) ∈ Ioo (lambda 1) (lambda 2) := by
    filter_upwards [hpositiveEven,
      (tendsto_order.1 hpEval1).2 0 hp1,
      (tendsto_order.1 hpEval2).2 0 hp2] with k hpos hP1 hP2
    exact rho_mem_open_middleGap_of_P_eval_neg hlambda (x (2 * k))
      hpos hP1 hP2
  have hodd : ∀ᶠ k in atTop,
      rhoSeq lambda x (2 * k + 1) ∈ Ioo (lambda 1) (lambda 2) := by
    filter_upwards [hpositiveOdd,
      (tendsto_order.1 hqEval1).2 0 hq1,
      (tendsto_order.1 hqEval2).2 0 hq2] with k hpos hP1 hP2
    exact rho_mem_open_middleGap_of_P_eval_neg hlambda (x (2 * k + 1))
      hpos hP1 hP2
  exact eventually_of_even_odd heven hodd

/-- If all old weights are positive and the old factors converge paritywise
to nonvanishing factors, then every exact-update weight is eventually
positive. -/
theorem eventually_exactUpdateSeq_all_positive_of_parity_factors
    {lambda : Fin 4 → ℝ} (hlambda : Function.Injective lambda)
    (x : ℕ → Weights) {tau : ℝ} (htau : 0 < tau)
    {p q : MonicQuadratic}
    (hfactor : p.toPolynomial * q.toPolynomial =
      nodalQuartic lambda + C (tau ^ 2))
    (hpositive : ∀ᶠ k in atTop, ∀ i, 0 < x k i)
    (hp : Tendsto (fun k ↦ (P lambda (x (2 * k))).coeffPair)
      atTop (nhds p.coeffPair))
    (hq : Tendsto (fun k ↦ (P lambda (x (2 * k + 1))).coeffPair)
      atTop (nhds q.coeffPair)) :
    ∀ᶠ k in atTop, ∀ i,
      0 < exactUpdateSeq lambda hlambda x k i := by
  have hpositiveEven : ∀ᶠ k in atTop, ∀ i, 0 < x (2 * k) i :=
    evenIndex_tendsto_atTop.eventually hpositive
  have hpositiveOdd : ∀ᶠ k in atTop, ∀ i, 0 < x (2 * k + 1) i :=
    oddIndex_tendsto_atTop.eventually hpositive
  have heven : ∀ᶠ k in atTop, ∀ i,
      0 < exactUpdateSeq lambda hlambda x (2 * k) i := by
    have hne : ∀ i, ∀ᶠ k in atTop,
        (P lambda (x (2 * k))).toPolynomial.eval (lambda i) ≠ 0 := by
      intro i
      exact (tendsto_monicQuadratic_eval_of_coeffPair
        (fun k ↦ P lambda (x (2 * k))) p hp (lambda i)).eventually_ne
          (factor_eval_ne_zero htau hfactor i).1
    filter_upwards [hpositiveEven, hne 0, hne 1, hne 2, hne 3]
      with k hpos h0 h1 h2 h3
    intro i
    rw [exactUpdateSeq, T_weight_pos_iff lambda hlambda]
    apply mul_ne_zero (ne_of_gt (hpos i))
    fin_cases i <;> assumption
  have hodd : ∀ᶠ k in atTop, ∀ i,
      0 < exactUpdateSeq lambda hlambda x (2 * k + 1) i := by
    have hne : ∀ i, ∀ᶠ k in atTop,
        (P lambda (x (2 * k + 1))).toPolynomial.eval (lambda i) ≠ 0 := by
      intro i
      exact (tendsto_monicQuadratic_eval_of_coeffPair
        (fun k ↦ P lambda (x (2 * k + 1))) q hq (lambda i)).eventually_ne
          (factor_eval_ne_zero htau hfactor i).2
    filter_upwards [hpositiveOdd, hne 0, hne 1, hne 2, hne 3]
      with k hpos h0 h1 h2 h3
    intro i
    rw [exactUpdateSeq, T_weight_pos_iff lambda hlambda]
    apply mul_ne_zero (ne_of_gt (hpos i))
    fin_cases i <;> assumption
  exact eventually_of_even_odd heven hodd

end

end FourNode
end Forsythe
