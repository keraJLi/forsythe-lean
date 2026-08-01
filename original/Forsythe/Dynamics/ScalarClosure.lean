import Forsythe.Dynamics.Scalar

/-!
# Closing a geometrically perturbed scalar recurrence

This module packages the last scalar argument in the four-node branch.  The
normalised-product dichotomy controls the defect variable.  In its zero
branch the parameter increments are summable; in its nonzero branch the
main increment has a locally fixed direction and dominates the geometric
error, so the one-way-crossing lemma applies.
-/

set_option autoImplicit false

namespace Forsythe
namespace ScalarDynamics

open Filter Set Topology

noncomputable section

/-- On each compact interior interval, a scalar coefficient is eventually
uniformly separated from zero with one fixed sign. -/
def EventuallyLocallySeparatedCoefficient
    (rho c : ℕ → ℝ) (a b : ℝ) : Prop :=
  ∀ lo hi, a < lo → lo < hi → hi < b →
    ∃ eta : ℝ, 0 < eta ∧
      ((∀ᶠ k in atTop, rho k ∈ Icc lo hi → eta ≤ c k) ∨
        (∀ᶠ k in atTop, rho k ∈ Icc lo hi → c k ≤ -eta))

/-- A real sequence with an eventual geometric bound on its successive
distances converges. -/
theorem exists_tendsto_of_eventually_geometric_step_bound
    (rho : ℕ → ℝ) {C theta : ℝ}
    (_hC : 0 ≤ C) (hthetaNonneg : 0 ≤ theta) (hthetaLt : theta < 1)
    (hstep : ∀ᶠ k in atTop,
      |rho (k + 1) - rho k| ≤ C * theta ^ k) :
    ∃ l : ℝ, Tendsto rho atTop (𝓝 l) := by
  obtain ⟨K, hK⟩ := eventually_atTop.1 hstep
  have hgeom : Summable (fun k : ℕ ↦ theta ^ k) :=
    summable_geometric_of_lt_one hthetaNonneg hthetaLt
  have hbound : Summable (fun k : ℕ ↦ C * theta ^ k) :=
    hgeom.mul_left C
  have hsum : Summable (fun k ↦ dist (rho k) (rho (k + 1))) := by
    apply hbound.of_norm_bounded_eventually_nat
    filter_upwards [hstep] with k hk
    simpa only [Real.norm_eq_abs, abs_of_nonneg dist_nonneg,
      Real.dist_eq, abs_sub_comm, abs_abs] using hk
  exact cauchySeq_tendsto_of_complete (cauchySeq_of_summable_dist hsum)

/-- The manuscript's final scalar closure lemma.  `alpha` obeys a positive
near-identity multiplicative recurrence with geometric forcing.  The
parameter `rho` has main increment `c * alpha` and geometric error.  A
uniform bound on `c`, confinement of `rho` to a compact interval, and local
signed separation of `c` imply convergence of `rho` in both branches of the
normalised-product dichotomy. -/
theorem exists_tendsto_of_geometric_perturbed_normalizedRecurrence
    (alpha m bAlpha rho c bRho : ℕ → ℝ)
    {a b CAlpha CRho Cc theta : ℝ}
    (hmpos : ∀ k, 0 < m k)
    (hm : Tendsto m atTop (𝓝 1))
    (hAlphaRec : ∀ k,
      alpha (k + 1) = m k * alpha k + bAlpha k)
    (hCAlpha : 0 ≤ CAlpha)
    (hCRho : 0 ≤ CRho)
    (hCc : 0 ≤ Cc)
    (hthetaPos : 0 < theta)
    (hthetaLt : theta < 1)
    (hbAlpha : ∀ k, |bAlpha k| ≤ CAlpha * theta ^ k)
    (hRhoRec : ∀ k,
      rho (k + 1) - rho k = c k * alpha k + bRho k)
    (hbRho : ∀ k, |bRho k| ≤ CRho * theta ^ k)
    (hcBound : ∀ k, |c k| ≤ Cc)
    (hAlphaZero : Tendsto alpha atTop (𝓝 0))
    (hRho : ∀ k, rho k ∈ Icc a b)
    (hlocal : EventuallyLocallySeparatedCoefficient rho c a b) :
    ∃ l ∈ Icc a b, Tendsto rho atTop (𝓝 l) := by
  obtain ⟨L, _hL, hbranch⟩ :=
    normalizedRecurrence_geometric_dichotomy hmpos hm hAlphaRec
      hCAlpha hthetaPos hthetaLt hbAlpha
  rcases hbranch with hzero | hnonzero
  · obtain ⟨C', hC', hAlphaGeom⟩ := hzero.2.2
    have hstepGeom : ∀ᶠ k in atTop,
        |rho (k + 1) - rho k| ≤ (Cc * C' + CRho) * theta ^ k := by
      filter_upwards [hAlphaGeom] with k hk
      rw [hRhoRec k]
      calc
        |c k * alpha k + bRho k| ≤
            |c k| * |alpha k| + |bRho k| := by
          simpa only [abs_mul] using abs_add_le (c k * alpha k) (bRho k)
        _ ≤ Cc * (C' * theta ^ k) + CRho * theta ^ k := by
          exact add_le_add
            (mul_le_mul (hcBound k) hk (abs_nonneg _) hCc)
            (hbRho k)
        _ = (Cc * C' + CRho) * theta ^ k := by ring
    obtain ⟨l, hl⟩ := exists_tendsto_of_eventually_geometric_step_bound
      rho (add_nonneg (mul_nonneg hCc hC') hCRho) hthetaPos.le hthetaLt
      hstepGeom
    exact ⟨l, isClosed_Icc.mem_of_tendsto hl (Eventually.of_forall hRho), hl⟩
  · have hLne : L ≠ 0 := hnonzero.1
    have hAlphaSign : ∀ᶠ k in atTop, 0 < L * alpha k := hnonzero.2.1
    have hratio : Tendsto (fun k ↦ theta ^ k / |alpha k|)
        atTop (𝓝 0) := hnonzero.2.2
    have hstepZero : Tendsto (fun k ↦ rho (k + 1) - rho k)
        atTop (𝓝 0) := by
      have hcAlpha : Tendsto (fun k ↦ c k * alpha k) atTop (𝓝 0) := by
        apply tendsto_zero_iff_norm_tendsto_zero.mpr
        have hAlphaAbs : Tendsto (fun k ↦ |alpha k|) atTop (𝓝 0) := by
          simpa only [Function.comp_def, abs_zero] using
            (continuous_abs.tendsto 0).comp hAlphaZero
        have hboundZero : Tendsto (fun k ↦ Cc * |alpha k|)
            atTop (𝓝 0) := by
          simpa only [mul_zero] using tendsto_const_nhds.mul hAlphaAbs
        simpa only [Real.norm_eq_abs] using squeeze_zero'
          (Eventually.of_forall fun k ↦ abs_nonneg (c k * alpha k))
          (Eventually.of_forall fun k ↦ by
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_right (hcBound k) (abs_nonneg _))
          hboundZero
      have hbZero : Tendsto bRho atTop (𝓝 0) := by
        apply tendsto_zero_iff_norm_tendsto_zero.mpr
        simpa only [Real.norm_eq_abs] using squeeze_zero'
          (Eventually.of_forall fun k ↦ abs_nonneg (bRho k))
          (Eventually.of_forall hbRho)
          (by
            simpa only [mul_zero] using
              tendsto_const_nhds.mul
                (tendsto_pow_atTop_nhds_zero_of_lt_one hthetaPos.le hthetaLt))
      have ht := hcAlpha.add hbZero
      simpa only [zero_add] using ht.congr'
        (Eventually.of_forall fun k ↦ (hRhoRec k).symm)
    have hdir : EventuallyLocallyDirectedSteps rho a b := by
      intro lo hi halo hlohi hhib
      obtain ⟨eta, heta, hcPos | hcNeg⟩ :=
        hlocal lo hi halo hlohi hhib
      · have hsmallRatio : ∀ᶠ k in atTop,
            CRho * (theta ^ k / |alpha k|) < eta := by
          have ht : Tendsto (fun k ↦ CRho * (theta ^ k / |alpha k|))
              atTop (𝓝 0) := by
            simpa only [mul_zero] using tendsto_const_nhds.mul hratio
          exact (tendsto_order.1 ht).2 eta heta
        by_cases hLpos : 0 < L
        · left
          filter_upwards [hAlphaSign, hsmallRatio, hcPos] with k hkSign hkSmall hkC
          intro hkRho
          have hAlphaPos : 0 < alpha k := by nlinarith
          have hAlphaAbs : |alpha k| = alpha k := abs_of_pos hAlphaPos
          have hkSmall' : CRho * theta ^ k < eta * |alpha k| := by
            have hdiv : CRho * theta ^ k / |alpha k| < eta := by
              simpa only [mul_div_assoc] using hkSmall
            exact (div_lt_iff₀ (abs_pos.mpr (ne_of_gt hAlphaPos))).1 hdiv
          have hb := hbRho k
          have hc := hkC hkRho
          apply sub_nonneg.mp
          rw [hRhoRec k]
          rw [hAlphaAbs] at hkSmall'
          nlinarith [neg_le_of_abs_le hb]
        · right
          have hLneg : L < 0 := lt_of_le_of_ne (le_of_not_gt hLpos) hLne
          filter_upwards [hAlphaSign, hsmallRatio, hcPos] with k hkSign hkSmall hkC
          intro hkRho
          have hAlphaNeg : alpha k < 0 := by nlinarith
          have hAlphaAbs : |alpha k| = -alpha k := abs_of_neg hAlphaNeg
          have hkSmall' : CRho * theta ^ k < eta * |alpha k| := by
            have hdiv : CRho * theta ^ k / |alpha k| < eta := by
              simpa only [mul_div_assoc] using hkSmall
            exact (div_lt_iff₀ (abs_pos.mpr (ne_of_lt hAlphaNeg))).1 hdiv
          have hb := hbRho k
          have hc := hkC hkRho
          apply sub_nonpos.mp
          rw [hRhoRec k]
          rw [hAlphaAbs] at hkSmall'
          nlinarith [le_abs_self (bRho k)]
      · have hsmallRatio : ∀ᶠ k in atTop,
            CRho * (theta ^ k / |alpha k|) < eta := by
          have ht : Tendsto (fun k ↦ CRho * (theta ^ k / |alpha k|))
              atTop (𝓝 0) := by
            simpa only [mul_zero] using tendsto_const_nhds.mul hratio
          exact (tendsto_order.1 ht).2 eta heta
        by_cases hLpos : 0 < L
        · right
          filter_upwards [hAlphaSign, hsmallRatio, hcNeg] with k hkSign hkSmall hkC
          intro hkRho
          have hAlphaPos : 0 < alpha k := by nlinarith
          have hAlphaAbs : |alpha k| = alpha k := abs_of_pos hAlphaPos
          have hkSmall' : CRho * theta ^ k < eta * |alpha k| := by
            have hdiv : CRho * theta ^ k / |alpha k| < eta := by
              simpa only [mul_div_assoc] using hkSmall
            exact (div_lt_iff₀ (abs_pos.mpr (ne_of_gt hAlphaPos))).1 hdiv
          have hb := hbRho k
          have hc := hkC hkRho
          apply sub_nonpos.mp
          rw [hRhoRec k]
          rw [hAlphaAbs] at hkSmall'
          nlinarith [le_abs_self (bRho k)]
        · left
          have hLneg : L < 0 := lt_of_le_of_ne (le_of_not_gt hLpos) hLne
          filter_upwards [hAlphaSign, hsmallRatio, hcNeg] with k hkSign hkSmall hkC
          intro hkRho
          have hAlphaNeg : alpha k < 0 := by nlinarith
          have hAlphaAbs : |alpha k| = -alpha k := abs_of_neg hAlphaNeg
          have hkSmall' : CRho * theta ^ k < eta * |alpha k| := by
            have hdiv : CRho * theta ^ k / |alpha k| < eta := by
              simpa only [mul_div_assoc] using hkSmall
            exact (div_lt_iff₀ (abs_pos.mpr (ne_of_lt hAlphaNeg))).1 hdiv
          have hb := hbRho k
          have hc := hkC hkRho
          apply sub_nonneg.mp
          rw [hRhoRec k]
          rw [hAlphaAbs] at hkSmall'
          nlinarith [neg_le_of_abs_le hb]
    exact tendsto_of_eventuallyLocallyDirectedSteps hRho hstepZero hdir

end

end ScalarDynamics
end Forsythe
