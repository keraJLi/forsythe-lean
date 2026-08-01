import Forsythe.Dynamics.Parity
import Forsythe.FourNode.Gap
import Forsythe.FourNode.RemainderContinuity
import Forsythe.FourNode.Perturbation

/-!
# Asymptotics of the four-node remainder multiplier

On the ordered middle node gap the two limiting quadratic factors never
vanish.  Compactness therefore gives a common quantitative lower bound.  If
the exact-update factors converge paritywise to the two limiting factors and
the old and new barycentric parameters coalesce, the two remainder
coefficients have the same eventual sign and their quotient tends to one.
-/

set_option autoImplicit false

namespace Forsythe
namespace FourNode

open Filter Polynomial Set Topology

noncomputable section

/-- Both limiting factors are uniformly separated from zero on the closed
middle node gap. -/
theorem exists_uniform_factor_gap_on_middleGap
    {lambda : Fin 4 → ℝ} (hlambda : StrictMono lambda)
    {tau : ℝ} (htau : 0 < tau) {p q : MonicQuadratic}
    (hfactor : p.toPolynomial * q.toPolynomial =
      nodalQuartic lambda + C (tau ^ 2)) :
    ∃ delta : ℝ, 0 < delta ∧
      (∀ t ∈ Icc (lambda 1) (lambda 2),
        delta ≤ |p.toPolynomial.eval t|) ∧
      (∀ t ∈ Icc (lambda 1) (lambda 2),
        delta ≤ |q.toPolynomial.eval t|) := by
  let J : Set ℝ := Icc (lambda 1) (lambda 2)
  have hJ : IsCompact J := isCompact_Icc
  obtain ⟨dp, hdp, hp⟩ := hJ.exists_forall_le'
    p.toPolynomial.continuous.abs.continuousOn (by
      intro t ht
      exact abs_pos.mpr
        (factor_eval_ne_zero_on_middleGap hlambda htau hfactor ht).1)
  obtain ⟨dq, hdq, hq⟩ := hJ.exists_forall_le'
    q.toPolynomial.continuous.abs.continuousOn (by
      intro t ht
      exact abs_pos.mpr
        (factor_eval_ne_zero_on_middleGap hlambda htau hfactor ht).2)
  refine ⟨min dp dq, lt_min hdp hdq, ?_, ?_⟩
  · intro t ht
    exact (min_le_left _ _).trans (hp t ht)
  · intro t ht
    exact (min_le_right _ _).trans (hq t ht)

private theorem abs_mem_middleGap_le_nodeRadius
    {lambda : Fin 4 → ℝ} {t : ℝ}
    (ht : t ∈ Icc (lambda 1) (lambda 2)) :
    |t| ≤ nodeRadius lambda := by
  rw [abs_le]
  constructor
  · exact (neg_le_of_abs_le (abs_node_le_nodeRadius lambda 1)).trans ht.1
  · exact ht.2.trans (le_abs_self (lambda 2) |>.trans
      (abs_node_le_nodeRadius lambda 2))

private theorem tendsto_coeffDist_of_tendsto_coeffPair
    (f : ℕ → MonicQuadratic) (g : MonicQuadratic)
    (h : Tendsto (fun k ↦ (f k).coeffPair) atTop (nhds g.coeffPair)) :
    Tendsto (fun k ↦ (f k).coeffDist g) atTop (nhds 0) := by
  rw [show (fun k ↦ (f k).coeffDist g) =
      (fun k ↦ ‖(f k).coeffPair - g.coeffPair‖) by
        funext k
        rfl]
  simpa using (h.sub_const g.coeffPair).norm

private theorem eventually_linearCoeff_bound_of_tendsto_coeffPair
    (f : ℕ → MonicQuadratic) (g : MonicQuadratic)
    (h : Tendsto (fun k ↦ (f k).coeffPair) atTop (nhds g.coeffPair)) :
    ∀ᶠ k in atTop, |(f k).linearCoeff| ≤ |g.linearCoeff| + 1 := by
  have hlinear : Tendsto (fun k ↦ (f k).linearCoeff)
      atTop (nhds g.linearCoeff) := by
    simpa only [MonicQuadratic.coeffPair] using h.fst_nhds
  have hdist : Tendsto (fun k ↦ |(f k).linearCoeff - g.linearCoeff|)
      atTop (nhds 0) := by
    simpa only [sub_self, abs_zero] using
      (hlinear.sub_const g.linearCoeff).abs
  filter_upwards [(tendsto_order.1 hdist).2 1 (by norm_num)] with k hk
  calc
    |(f k).linearCoeff| ≤
        |(f k).linearCoeff - g.linearCoeff| + |g.linearCoeff| := by
      simpa only [sub_add_cancel] using
        abs_add_le ((f k).linearCoeff - g.linearCoeff) g.linearCoeff
    _ ≤ |g.linearCoeff| + 1 := by linarith

private theorem parity_new_remainder_uniformly_nonzero
    {lambda : Fin 4 → ℝ} {delta : ℝ} (hdelta : 0 < delta)
    {limitFactor companion : MonicQuadratic}
    (hcompanion : ∀ t,
      remainderLinearCoeff companion (dividedDifference lambda t) =
        limitFactor.toPolynomial.eval t)
    (flower : ∀ t ∈ Icc (lambda 1) (lambda 2),
      delta ≤ |limitFactor.toPolynomial.eval t|)
    (f : ℕ → MonicQuadratic) (t : ℕ → ℝ)
    (hf : Tendsto (fun k ↦ (f k).coeffPair)
      atTop (nhds companion.coeffPair))
    (ht : ∀ᶠ k in atTop, t k ∈ Icc (lambda 1) (lambda 2)) :
    ∀ᶠ k in atTop,
      delta / 2 ≤
        |remainderLinearCoeff (f k) (dividedDifference lambda (t k))| := by
  let M : ℝ := max (|companion.linearCoeff| + 1) |companion.linearCoeff|
  have hMcomp : |companion.linearCoeff| ≤ M := le_max_right _ _
  have hfBound : ∀ᶠ k in atTop, |(f k).linearCoeff| ≤ M :=
    (eventually_linearCoeff_bound_of_tendsto_coeffPair f companion hf).mono
      fun k hk ↦ hk.trans (le_max_left _ _)
  have hdist := tendsto_coeffDist_of_tendsto_coeffPair f companion hf
  let L := remainderCoefficientLipschitzConstant lambda (nodeRadius lambda) M
  have herror : Tendsto (fun k ↦ L * (f k).coeffDist companion)
      atTop (nhds 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hdist
  have hsmall : ∀ᶠ k in atTop,
      L * (f k).coeffDist companion < delta / 2 :=
    (tendsto_order.1 herror).2 _ (half_pos hdelta)
  filter_upwards [ht, hfBound, hsmall] with k htk hfk hk
  have hR : |t k| ≤ nodeRadius lambda :=
    abs_mem_middleGap_le_nodeRadius htk
  have happrox :
      |remainderLinearCoeff (f k) (dividedDifference lambda (t k)) -
          limitFactor.toPolynomial.eval (t k)| ≤
        L * (f k).coeffDist companion := by
    rw [← hcompanion (t k)]
    exact abs_remainderLinearCoeff_dividedDifference_sub_sameParameter_le_of_bounds
      lambda (f k) companion (t k) hR hfk hMcomp
  have hlimit := flower (t k) htk
  have hreverse :
      |limitFactor.toPolynomial.eval (t k)| -
          |remainderLinearCoeff (f k) (dividedDifference lambda (t k))| ≤
        |remainderLinearCoeff (f k) (dividedDifference lambda (t k)) -
          limitFactor.toPolynomial.eval (t k)| := by
    simpa only [abs_sub_comm] using abs_sub_abs_le_abs_sub
      (limitFactor.toPolynomial.eval (t k))
      (remainderLinearCoeff (f k) (dividedDifference lambda (t k)))
  linarith

private theorem eventually_old_new_remainder_close
    {lambda : Fin 4 → ℝ} (hlambda : Function.Injective lambda)
    (x : ℕ → Weights)
    (M : ℝ)
    (hRhoX : ∀ᶠ k in atTop,
      rhoSeq lambda x k ∈ Icc (lambda 1) (lambda 2))
    (hRhoY : ∀ᶠ k in atTop,
      rho lambda (exactUpdateSeq lambda hlambda x k) ∈
        Icc (lambda 1) (lambda 2))
    (hfactorBound : ∀ᶠ k in atTop,
      |(P lambda (exactUpdateSeq lambda hlambda x k)).linearCoeff| ≤ M)
    (hRhoDiff : Tendsto (fun k ↦
      rhoSeq lambda x k -
        rho lambda (exactUpdateSeq lambda hlambda x k))
      atTop (nhds 0)) :
    Tendsto (fun k ↦
      |oldRemainderCoeff lambda hlambda x k -
        newRemainderCoeff lambda hlambda x k|) atTop (nhds 0) := by
  let R := nodeRadius lambda
  let B : ℝ := 2 * R + |nodeElementaryOne lambda| + M
  have hdiffAbs : Tendsto (fun k ↦
      |rhoSeq lambda x k -
        rho lambda (exactUpdateSeq lambda hlambda x k)|)
      atTop (nhds 0) := by
    simpa only [abs_zero] using hRhoDiff.abs
  have hupper : Tendsto (fun k ↦ B *
      |rhoSeq lambda x k -
        rho lambda (exactUpdateSeq lambda hlambda x k)|)
      atTop (nhds 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hdiffAbs
  apply squeeze_zero'
  · exact Eventually.of_forall fun k ↦ abs_nonneg _
  · filter_upwards [hRhoX, hRhoY, hfactorBound] with k hx hy hf
    have hxR : |rhoSeq lambda x k| ≤ R :=
      abs_mem_middleGap_le_nodeRadius hx
    have hyR : |rho lambda (exactUpdateSeq lambda hlambda x k)| ≤ R :=
      abs_mem_middleGap_le_nodeRadius hy
    have hfactor :
      |rhoSeq lambda x k +
          rho lambda (exactUpdateSeq lambda hlambda x k) -
          nodeElementaryOne lambda -
          (P lambda (exactUpdateSeq lambda hlambda x k)).linearCoeff| ≤
          |rhoSeq lambda x k| +
            |rho lambda (exactUpdateSeq lambda hlambda x k)| +
            |nodeElementaryOne lambda| +
          |(P lambda (exactUpdateSeq lambda hlambda x k)).linearCoeff| := by
        calc
          _ ≤ |rhoSeq lambda x k +
                rho lambda (exactUpdateSeq lambda hlambda x k) -
                nodeElementaryOne lambda| +
              |(P lambda (exactUpdateSeq lambda hlambda x k)).linearCoeff| :=
            abs_sub _ _
          _ ≤ (|rhoSeq lambda x k +
                rho lambda (exactUpdateSeq lambda hlambda x k)| +
              |nodeElementaryOne lambda|) +
              |(P lambda (exactUpdateSeq lambda hlambda x k)).linearCoeff| := by
            gcongr
            exact abs_sub _ _
          _ ≤ ((|rhoSeq lambda x k| +
                |rho lambda (exactUpdateSeq lambda hlambda x k)|) +
              |nodeElementaryOne lambda|) +
              |(P lambda (exactUpdateSeq lambda hlambda x k)).linearCoeff| := by
            gcongr
            exact abs_add_le _ _
          _ = _ := by ring
    have hfactorB :
        |rhoSeq lambda x k +
            rho lambda (exactUpdateSeq lambda hlambda x k) -
            nodeElementaryOne lambda -
            (P lambda (exactUpdateSeq lambda hlambda x k)).linearCoeff| ≤ B :=
      hfactor.trans (by dsimp only [B, R]; linarith)
    calc
      |oldRemainderCoeff lambda hlambda x k -
          newRemainderCoeff lambda hlambda x k| =
          |rhoSeq lambda x k -
            rho lambda (exactUpdateSeq lambda hlambda x k)| *
          |rhoSeq lambda x k +
            rho lambda (exactUpdateSeq lambda hlambda x k) -
            nodeElementaryOne lambda -
            (P lambda (exactUpdateSeq lambda hlambda x k)).linearCoeff| := by
        rw [oldRemainderCoeff, newRemainderCoeff,
          remainderLinearCoeff_dividedDifference_sub_sameQuadratic, abs_mul]
      _ ≤
          |rhoSeq lambda x k -
            rho lambda (exactUpdateSeq lambda hlambda x k)| * B :=
        mul_le_mul_of_nonneg_left hfactorB (abs_nonneg _)
      _ = B * |rhoSeq lambda x k -
          rho lambda (exactUpdateSeq lambda hlambda x k)| := by ring
  · exact hupper

/-- Paritywise convergence to the two factors, confinement to the ordered
middle gap, and coalescence of the old and exact-update parameters imply all
three multiplier conditions needed by scalar closure. -/
theorem remainderMultiplier_eventually_pos_tendsto_one
    {lambda : Fin 4 → ℝ} (hlambda : StrictMono lambda)
    (x : ℕ → Weights)
    {tau : ℝ} (htau : 0 < tau) {p q : MonicQuadratic}
    (hfactor : p.toPolynomial * q.toPolynomial =
      nodalQuartic lambda + C (tau ^ 2))
    (hPyEven : Tendsto (fun k ↦
      (P lambda (exactUpdateSeq lambda hlambda.injective x (2 * k))).coeffPair)
      atTop (nhds q.coeffPair))
    (hPyOdd : Tendsto (fun k ↦
      (P lambda
        (exactUpdateSeq lambda hlambda.injective x (2 * k + 1))).coeffPair)
      atTop (nhds p.coeffPair))
    (hRhoX : ∀ᶠ k in atTop,
      rhoSeq lambda x k ∈ Icc (lambda 1) (lambda 2))
    (hRhoY : ∀ᶠ k in atTop,
      rho lambda (exactUpdateSeq lambda hlambda.injective x k) ∈
        Icc (lambda 1) (lambda 2))
    (hRhoDiff : Tendsto (fun k ↦
      rhoSeq lambda x k -
        rho lambda (exactUpdateSeq lambda hlambda.injective x k))
      atTop (nhds 0)) :
    (∀ᶠ k in atTop,
      newRemainderCoeff lambda hlambda.injective x k ≠ 0) ∧
    (∀ᶠ k in atTop,
      0 < remainderMultiplier lambda hlambda.injective x k) ∧
    Tendsto (remainderMultiplier lambda hlambda.injective x)
      atTop (nhds 1) := by
  obtain ⟨delta, hdelta, hpGap, hqGap⟩ :=
    exists_uniform_factor_gap_on_middleGap hlambda htau hfactor
  have hevenIndex : Tendsto (fun k : ℕ ↦ 2 * k) atTop atTop := by
    apply tendsto_atTop.2
    intro N
    exact eventually_atTop.2 ⟨N, fun k hk ↦ by omega⟩
  have hoddIndex : Tendsto (fun k : ℕ ↦ 2 * k + 1) atTop atTop := by
    apply tendsto_atTop.2
    intro N
    exact eventually_atTop.2 ⟨N, fun k hk ↦ by omega⟩
  have hRhoYEven : ∀ᶠ k in atTop,
      rho lambda
        (exactUpdateSeq lambda hlambda.injective x (2 * k)) ∈
          Icc (lambda 1) (lambda 2) := hevenIndex.eventually hRhoY
  have hRhoYOdd : ∀ᶠ k in atTop,
      rho lambda
        (exactUpdateSeq lambda hlambda.injective x (2 * k + 1)) ∈
          Icc (lambda 1) (lambda 2) := hoddIndex.eventually hRhoY
  have hnewEven := parity_new_remainder_uniformly_nonzero hdelta
    (limitFactor := p) (companion := q)
    (fun t ↦ remainderLinearCoeff_dividedDifference_right
      lambda p q (tau ^ 2) t hfactor)
    hpGap
    (fun k ↦ P lambda
      (exactUpdateSeq lambda hlambda.injective x (2 * k)))
    (fun k ↦ rho lambda
      (exactUpdateSeq lambda hlambda.injective x (2 * k)))
    hPyEven hRhoYEven
  have hnewOdd := parity_new_remainder_uniformly_nonzero hdelta
    (limitFactor := q) (companion := p)
    (fun t ↦ remainderLinearCoeff_dividedDifference_left
      lambda p q (tau ^ 2) t hfactor)
    hqGap
    (fun k ↦ P lambda
      (exactUpdateSeq lambda hlambda.injective x (2 * k + 1)))
    (fun k ↦ rho lambda
      (exactUpdateSeq lambda hlambda.injective x (2 * k + 1)))
    hPyOdd hRhoYOdd
  have hnewLower : ∀ᶠ k in atTop,
      delta / 2 ≤
        |newRemainderCoeff lambda hlambda.injective x k| := by
    apply eventually_of_even_odd
    · simpa only [newRemainderCoeff] using hnewEven
    · simpa only [newRemainderCoeff] using hnewOdd
  let M : ℝ := max (|q.linearCoeff| + 1) (|p.linearCoeff| + 1)
  have hfactorEven : ∀ᶠ k in atTop,
      |(P lambda
        (exactUpdateSeq lambda hlambda.injective x (2 * k))).linearCoeff| ≤ M :=
    (eventually_linearCoeff_bound_of_tendsto_coeffPair _ q hPyEven).mono
      fun _ hk ↦ hk.trans (le_max_left _ _)
  have hfactorOdd : ∀ᶠ k in atTop,
      |(P lambda
        (exactUpdateSeq lambda hlambda.injective x (2 * k + 1))).linearCoeff| ≤ M :=
    (eventually_linearCoeff_bound_of_tendsto_coeffPair _ p hPyOdd).mono
      fun _ hk ↦ hk.trans (le_max_right _ _)
  have hfactorBound : ∀ᶠ k in atTop,
      |(P lambda
        (exactUpdateSeq lambda hlambda.injective x k)).linearCoeff| ≤ M :=
    eventually_of_even_odd hfactorEven hfactorOdd
  have hdiff := eventually_old_new_remainder_close hlambda.injective x M
    hRhoX hRhoY hfactorBound hRhoDiff
  have hdiffSmall : ∀ᶠ k in atTop,
      |oldRemainderCoeff lambda hlambda.injective x k -
        newRemainderCoeff lambda hlambda.injective x k| < delta / 2 :=
    (tendsto_order.1 hdiff).2 _ (half_pos hdelta)
  have hden : ∀ᶠ k in atTop,
      newRemainderCoeff lambda hlambda.injective x k ≠ 0 :=
    hnewLower.mono fun k hk ↦ by
      exact abs_pos.mp (lt_of_lt_of_le (half_pos hdelta) hk)
  have hmpos : ∀ᶠ k in atTop,
      0 < remainderMultiplier lambda hlambda.injective x k := by
    filter_upwards [hnewLower, hdiffSmall] with k hnew hsmall
    let old := oldRemainderCoeff lambda hlambda.injective x k
    let new := newRemainderCoeff lambda hlambda.injective x k
    have hnewNe : new ≠ 0 :=
      abs_pos.mp (lt_of_lt_of_le (half_pos hdelta) hnew)
    have hsmall' : |old - new| < |new| := hsmall.trans_le hnew
    rw [remainderMultiplier]
    rcases lt_or_gt_of_ne hnewNe with hnewNeg | hnewPos
    · apply (div_pos_iff.mpr (Or.inr ⟨?_, hnewNeg⟩))
      have hu := le_abs_self (old - new)
      rw [abs_of_neg hnewNeg] at hsmall'
      dsimp only [old, new] at hu hsmall' ⊢
      linarith
    · apply (div_pos_iff.mpr (Or.inl ⟨?_, hnewPos⟩))
      have hl := neg_le_of_abs_le (le_refl |old - new|)
      rw [abs_of_pos hnewPos] at hsmall'
      dsimp only [old, new] at hl hsmall' ⊢
      linarith
  let Cinv : ℝ := 1 / (delta / 2)
  have hCinv : 0 ≤ Cinv := by
    dsimp only [Cinv]
    positivity
  have hquotAbs : Tendsto (fun k ↦
      |(oldRemainderCoeff lambda hlambda.injective x k -
        newRemainderCoeff lambda hlambda.injective x k) /
          newRemainderCoeff lambda hlambda.injective x k|)
      atTop (nhds 0) := by
    have hupper : Tendsto (fun k ↦ Cinv *
        |oldRemainderCoeff lambda hlambda.injective x k -
          newRemainderCoeff lambda hlambda.injective x k|)
        atTop (nhds 0) := by
      simpa only [mul_zero] using tendsto_const_nhds.mul hdiff
    apply squeeze_zero'
    · exact Eventually.of_forall fun k ↦ abs_nonneg _
    · filter_upwards [hnewLower] with k hk
      have hinv :
          |newRemainderCoeff lambda hlambda.injective x k|⁻¹ ≤ Cinv := by
        simpa only [one_div, Cinv] using
          one_div_le_one_div_of_le (half_pos hdelta) hk
      calc
        |(oldRemainderCoeff lambda hlambda.injective x k -
            newRemainderCoeff lambda hlambda.injective x k) /
            newRemainderCoeff lambda hlambda.injective x k| =
          |oldRemainderCoeff lambda hlambda.injective x k -
            newRemainderCoeff lambda hlambda.injective x k| *
            |newRemainderCoeff lambda hlambda.injective x k|⁻¹ := by
          rw [abs_div, div_eq_mul_inv]
        _ ≤
          |oldRemainderCoeff lambda hlambda.injective x k -
            newRemainderCoeff lambda hlambda.injective x k| * Cinv :=
          mul_le_mul_of_nonneg_left hinv (abs_nonneg _)
        _ = Cinv *
            |oldRemainderCoeff lambda hlambda.injective x k -
              newRemainderCoeff lambda hlambda.injective x k| := by ring
    · exact hupper
  have hquot : Tendsto (fun k ↦
      (oldRemainderCoeff lambda hlambda.injective x k -
        newRemainderCoeff lambda hlambda.injective x k) /
          newRemainderCoeff lambda hlambda.injective x k)
      atTop (nhds 0) := by
    exact (tendsto_zero_iff_abs_tendsto_zero _).2 hquotAbs
  have hm : Tendsto (remainderMultiplier lambda hlambda.injective x)
      atTop (nhds 1) := by
    have hone : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    have hadd : Tendsto (fun k ↦ (1 : ℝ) +
        (oldRemainderCoeff lambda hlambda.injective x k -
          newRemainderCoeff lambda hlambda.injective x k) /
            newRemainderCoeff lambda hlambda.injective x k)
        atTop (nhds 1) := by
      simpa only [add_zero] using hone.add hquot
    apply hadd.congr'
    filter_upwards [hden] with k hk
    rw [remainderMultiplier]
    field_simp
    ring
  exact ⟨hden, hmpos, hm⟩

end

end FourNode
end Forsythe
