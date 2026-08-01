import Forsythe.Arnoldi.PolynomialLimits
import Forsythe.Exterior.Cocycle
import Forsythe.Exterior.CubicCancellation
import Forsythe.Exterior.StrictContraction
import Forsythe.Spectral.ComponentRecurrence
import Mathlib.Analysis.Real.Sqrt

/-!
# Exterior-mode decay

This module assembles the scalar ingredients of the manuscript's exterior
decay argument.  It isolates three reusable layers: cubic cancellation of the
first logarithmic variation, exclusion of a negative-neutral multiplier by a
grade-four parity cluster point, and one uniform geometric estimate for a
finite family of strictly contracting exterior weights.
-/

set_option autoImplicit false

namespace Forsythe
namespace Exterior

open Filter Finset Polynomial Set Topology
open scoped BigOperators

noncomputable section

/-- Plus-sign version of the weighted logarithmic cancellation estimate.
This is the form obtained from a negative-neutral exterior value: its signed
perturbation has linear term opposite to the four principal perturbations. -/
theorem abs_signed_weighted_log_cancellation_le
    {I : Type*} [Fintype I]
    (beta x : I → ℝ) (xExterior : ℝ)
    (hxExterior : |xExterior| ≤ (1 : ℝ) / 2)
    (hx : ∀ i, |x i| ≤ (1 : ℝ) / 2)
    (hcancel : xExterior + ∑ i, beta i * x i = 0) :
    |Real.log (1 + xExterior) +
        ∑ i, beta i * Real.log (1 + x i)| ≤
      2 * xExterior ^ 2 + ∑ i, |beta i| * (2 * (x i) ^ 2) := by
  let err : ℝ → ℝ := fun y ↦ Real.log (1 + y) - y
  have herrExterior : |err xExterior| ≤ 2 * xExterior ^ 2 := by
    simpa only [err] using abs_log_one_add_sub_le_two_mul_sq hxExterior
  have herr (i : I) : |err (x i)| ≤ 2 * (x i) ^ 2 := by
    simpa only [err] using abs_log_one_add_sub_le_two_mul_sq (hx i)
  have hrearrange :
      Real.log (1 + xExterior) +
          ∑ i, beta i * Real.log (1 + x i) =
        err xExterior + ∑ i, beta i * err (x i) := by
    dsimp only [err]
    have hsum :
        ∑ i, beta i * (Real.log (1 + x i) - x i) =
          (∑ i, beta i * Real.log (1 + x i)) -
            ∑ i, beta i * x i := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [hsum]
    linarith
  rw [hrearrange]
  calc
    |err xExterior + ∑ i, beta i * err (x i)| ≤
        |err xExterior| + |∑ i, beta i * err (x i)| := abs_add_le _ _
    _ ≤ |err xExterior| + ∑ i, |beta i * err (x i)| := by
      gcongr
      exact Finset.abs_sum_le_sum_abs _ _
    _ = |err xExterior| + ∑ i, |beta i| * |err (x i)| := by
      simp only [abs_mul]
    _ ≤ 2 * xExterior ^ 2 +
        ∑ i, |beta i| * (2 * (x i) ^ 2) := by
      apply add_le_add herrExterior
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (herr i) (abs_nonneg (beta i))

/-- Cubic Lagrange specialization matching a negative-neutral exterior node.
For `f = Q_k-Q`, the exterior factor is `1-f(t)/H`, whereas the four
principal factors are `1+f(lambda i)/H`. -/
theorem abs_signed_lagrange_log_firstVariation_le
    {lambda : Fin 4 → ℝ} (hlambda : Function.Injective lambda)
    (f : Polynomial ℝ) (hf : f.natDegree ≤ 3) (t scale : ℝ)
    (ht : |f.eval t / scale| ≤ (1 : ℝ) / 2)
    (hnodes : ∀ i, |f.eval (lambda i) / scale| ≤ (1 : ℝ) / 2) :
    |Real.log (1 - f.eval t / scale) +
        ∑ i : Fin 4, lagrangeWeight lambda t i *
          Real.log (1 + f.eval (lambda i) / scale)| ≤
      2 * (f.eval t / scale) ^ 2 +
        ∑ i : Fin 4, |lagrangeWeight lambda t i| *
          (2 * (f.eval (lambda i) / scale) ^ 2) := by
  have hcancel := cubic_firstVariation_cancel hlambda f hf t
  have hlinear :
      -(f.eval t / scale) +
          ∑ i : Fin 4, lagrangeWeight lambda t i *
            (f.eval (lambda i) / scale) = 0 := by
    have hsum :
        ∑ i : Fin 4, lagrangeWeight lambda t i *
            (f.eval (lambda i) / scale) =
          (∑ i : Fin 4, lagrangeWeight lambda t i *
            f.eval (lambda i)) / scale := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [hsum]
    calc
      -(f.eval t / scale) +
          (∑ i : Fin 4, lagrangeWeight lambda t i *
            f.eval (lambda i)) / scale =
        (-f.eval t + ∑ i : Fin 4,
          lagrangeWeight lambda t i * f.eval (lambda i)) / scale := by ring
      _ = 0 := by rw [hcancel, zero_div]
  simpa only [sub_eq_add_neg, neg_sq, abs_neg] using
    abs_signed_weighted_log_cancellation_le
      (lagrangeWeight lambda t)
      (fun i ↦ f.eval (lambda i) / scale)
      (-(f.eval t / scale)) (by simpa only [abs_neg] using ht)
      hnodes hlinear

/-- Coefficientwise/evaluation control by `D * delta` turns cubic
cancellation into one explicit `B * delta²` estimate. -/
theorem abs_signed_lagrange_log_firstVariation_le_mul_sq
    {lambda : Fin 4 → ℝ} (hlambda : Function.Injective lambda)
    (f : Polynomial ℝ) (hf : f.natDegree ≤ 3) (t scale D delta : ℝ)
    (hD : 0 ≤ D) (hdelta : 0 ≤ delta)
    (ht : |f.eval t / scale| ≤ D * delta)
    (hnodes : ∀ i, |f.eval (lambda i) / scale| ≤ D * delta)
    (hsmall : D * delta ≤ (1 : ℝ) / 2) :
    |Real.log (1 - f.eval t / scale) +
        ∑ i : Fin 4, lagrangeWeight lambda t i *
          Real.log (1 + f.eval (lambda i) / scale)| ≤
      (2 * D ^ 2 *
        (1 + ∑ i : Fin 4, |lagrangeWeight lambda t i|)) * delta ^ 2 := by
  have hraw := abs_signed_lagrange_log_firstVariation_le
    hlambda f hf t scale (ht.trans hsmall) (fun i ↦ (hnodes i).trans hsmall)
  have hDdelta : 0 ≤ D * delta := mul_nonneg hD hdelta
  have htSq : (f.eval t / scale) ^ 2 ≤ (D * delta) ^ 2 := by
    rw [← sq_abs]
    exact (sq_le_sq₀ (abs_nonneg _) hDdelta).2 ht
  have hnodeSq (i : Fin 4) :
      (f.eval (lambda i) / scale) ^ 2 ≤ (D * delta) ^ 2 := by
    rw [← sq_abs]
    exact (sq_le_sq₀ (abs_nonneg _) hDdelta).2 (hnodes i)
  calc
    |Real.log (1 - f.eval t / scale) +
        ∑ i : Fin 4, lagrangeWeight lambda t i *
          Real.log (1 + f.eval (lambda i) / scale)| ≤
      2 * (f.eval t / scale) ^ 2 +
        ∑ i : Fin 4, |lagrangeWeight lambda t i| *
          (2 * (f.eval (lambda i) / scale) ^ 2) := hraw
    _ ≤ 2 * (D * delta) ^ 2 +
        ∑ i : Fin 4, |lagrangeWeight lambda t i| *
          (2 * (D * delta) ^ 2) := by
      apply add_le_add (mul_le_mul_of_nonneg_left htSq (by norm_num))
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hnodeSq i) (by norm_num))
        (abs_nonneg _)
    _ = (2 * D ^ 2 *
        (1 + ∑ i : Fin 4, |lagrangeWeight lambda t i|)) * delta ^ 2 := by
      rw [← Finset.sum_mul]
      ring

/-- A quadratic logarithmic error cannot cancel the positive normalization
defect.  This is the explicit replacement for the manuscript expression
`(h_k+h_{k+1})/H + O(h_k²) > 0`. -/
theorem eventually_pos_of_quadratic_logError
    (h err : ℕ → ℝ) (H B : ℝ)
    (hH : 0 < H) (_hB : 0 ≤ B)
    (hhpos : ∀ k, 0 < h k)
    (hhzero : Tendsto h atTop (𝓝 0))
    (herr : ∀ᶠ k in atTop, |err k| ≤ B * (h k) ^ 2) :
    ∀ᶠ k in atTop,
      0 < err k - Real.log (1 - h k / H) -
        Real.log (1 - h (k + 1) / H) := by
  have hhshift : Tendsto (fun k ↦ h (k + 1)) atTop (𝓝 0) :=
    hhzero.comp (tendsto_add_atTop_nat 1)
  have hsmall : ∀ᶠ k in atTop, B * h k < 1 / H := by
    have ht : Tendsto (fun k ↦ B * h k) atTop (𝓝 0) := by
      simpa only [mul_zero] using tendsto_const_nhds.mul hhzero
    exact (tendsto_order.1 ht).2 (1 / H) (one_div_pos.mpr hH)
  have hratio : ∀ᶠ k in atTop, h k / H < 1 := by
    have ht : Tendsto (fun k ↦ h k / H) atTop (𝓝 0) := by
      simpa only [zero_div] using hhzero.div_const H
    exact (tendsto_order.1 ht).2 1 zero_lt_one
  have hratioShift : ∀ᶠ k in atTop, h (k + 1) / H < 1 := by
    have ht : Tendsto (fun k ↦ h (k + 1) / H) atTop (𝓝 0) := by
      simpa only [zero_div] using hhshift.div_const H
    exact (tendsto_order.1 ht).2 1 zero_lt_one
  filter_upwards [herr, hsmall, hratio, hratioShift] with k hkerr hksmall hkratio hkratio'
  have hlog : Real.log (1 - h k / H) ≤ -(h k / H) := by
    have := Real.log_le_sub_one_of_pos (sub_pos.mpr hkratio)
    linarith
  have hlog' : Real.log (1 - h (k + 1) / H) ≤ -(h (k + 1) / H) := by
    have := Real.log_le_sub_one_of_pos (sub_pos.mpr hkratio')
    linarith
  have hquad : B * (h k) ^ 2 < h k / H := by
    calc
      B * (h k) ^ 2 = (B * h k) * h k := by ring
      _ < (1 / H) * h k := mul_lt_mul_of_pos_right hksmall (hhpos k)
      _ = h k / H := by ring
  have herrLower : -(B * (h k) ^ 2) ≤ err k :=
    (neg_le_of_abs_le hkerr)
  have hbase : 0 < err k - Real.log (1 - h k / H) := by linarith
  have hlogNeg : Real.log (1 - h (k + 1) / H) < 0 := by
    have hratioPos : 0 < h (k + 1) / H := div_pos (hhpos (k + 1)) hH
    linarith
  linarith

/-- A grade-four parity cluster point drives the logarithmic cocycle to
minus infinity whenever the exterior weight tends to zero. -/
theorem tendsto_logarithmicWeightCocycle_subsequence_atBot
    {I : Type*} [Fintype I]
    (exteriorWeight : ℕ → ℝ) (principalWeight : I → ℕ → ℝ)
    (beta : I → ℝ) (r : ℕ) (phi : ℕ → ℕ)
    (hexteriorPos : ∀ k, 0 < exteriorWeight k)
    (_hprincipalPos : ∀ i k, 0 < principalWeight i k)
    (hexterior : Tendsto (fun j ↦ exteriorWeight (2 * phi j + r))
      atTop (𝓝 0))
    (principalLimit : I → ℝ)
    (hprincipalLimitPos : ∀ i, 0 < principalLimit i)
    (hprincipal : ∀ i, Tendsto
      (fun j ↦ principalWeight i (2 * phi j + r))
      atTop (𝓝 (principalLimit i))) :
    Tendsto (fun j ↦ logarithmicWeightCocycle
      exteriorWeight principalWeight beta (2 * phi j + r)) atTop atBot := by
  have hextWithin : Tendsto (fun j ↦ exteriorWeight (2 * phi j + r))
      atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hexterior,
      Eventually.of_forall fun j ↦ hexteriorPos (2 * phi j + r)⟩
  have hlogExterior : Tendsto
      (fun j ↦ Real.log (exteriorWeight (2 * phi j + r))) atTop atBot :=
    Real.tendsto_log_nhdsGT_zero.comp hextWithin
  have hsum : Tendsto
      (fun j ↦ ∑ i, beta i *
        Real.log (principalWeight i (2 * phi j + r))) atTop
      (𝓝 (∑ i, beta i * Real.log (principalLimit i))) := by
    simpa only [Function.comp_def] using tendsto_finsetSum Finset.univ fun i hi ↦
      tendsto_const_nhds.mul
        ((Real.continuousAt_log (ne_of_gt (hprincipalLimitPos i))).tendsto.comp
          (hprincipal i))
  simpa only [logarithmicWeightCocycle] using hlogExterior.atBot_add hsum

/-- Abstract negative-neutral exclusion.  Cubic cancellation supplies
`hpositiveOfNegative`; the exact component recurrence supplies `hupdate`;
and a grade-four parity cluster point supplies the positive principal limits.
-/
theorem negativeNeutral_limit_ne_of_cocycle
    {I : Type*} [Fintype I]
    (exteriorWeight : ℕ → ℝ) (principalWeight : I → ℕ → ℝ)
    (exteriorMultiplier : ℕ → ℝ) (principalMultiplier : I → ℕ → ℝ)
    (beta : I → ℝ)
    (hupdate : IsTwoStepSquaredWeightUpdate exteriorWeight principalWeight
      exteriorMultiplier principalMultiplier)
    (limitValue H : ℝ) (r : ℕ)
    (hpositiveOfNegative : limitValue = -H → ∀ᶠ k in atTop,
      0 < 2 * Real.log (exteriorMultiplier (2 * k + r)) +
        ∑ i, beta i *
          (2 * Real.log (principalMultiplier i (2 * k + r))))
    (phi : ℕ → ℕ) (hphi : Tendsto phi atTop atTop)
    (hexterior : Tendsto (fun j ↦ exteriorWeight (2 * phi j + r))
      atTop (𝓝 0))
    (principalLimit : I → ℝ)
    (hprincipalLimitPos : ∀ i, 0 < principalLimit i)
    (hprincipal : ∀ i, Tendsto
      (fun j ↦ principalWeight i (2 * phi j + r))
      atTop (𝓝 (principalLimit i))) :
    limitValue ≠ -H := by
  intro hnegative
  have hpositive := hpositiveOfNegative hnegative
  let Y := logarithmicWeightCocycle exteriorWeight principalWeight beta
  have hinc : ∀ᶠ k in atTop,
      Y (2 * k + r) < Y (2 * (k + 1) + r) := by
    filter_upwards [hpositive] with k hk
    have hdiff := logarithmicWeightCocycle_add_two_sub_eq_two_mul_log
      exteriorWeight principalWeight exteriorMultiplier principalMultiplier
      beta hupdate (2 * k + r)
    have hindex : 2 * (k + 1) + r = 2 * k + r + 2 := by omega
    rw [hindex]
    apply sub_pos.mp
    change 0 < logarithmicWeightCocycle exteriorWeight principalWeight beta
        (2 * k + r + 2) -
      logarithmicWeightCocycle exteriorWeight principalWeight beta (2 * k + r)
    rw [hdiff]
    exact hk
  have hbot : Tendsto (fun j ↦ Y (2 * phi j + r)) atTop atBot :=
    tendsto_logarithmicWeightCocycle_subsequence_atBot
      exteriorWeight principalWeight beta r phi
      hupdate.exteriorWeight_pos hupdate.principalWeight_pos hexterior
      principalLimit hprincipalLimitPos hprincipal
  exact (not_tendsto_parityCocycle_subsequence_atBot_of_eventually_strictIncrease
    Y r hinc hphi) hbot

/-- Fully quantitative cocycle exclusion from a quadratic logarithmic-error
bound.  The equality `hlogIdentity` is the exact logarithm of the two-step
component recurrences after factoring out the limiting height `H`.
`abs_signed_lagrange_log_firstVariation_le` is designed to prove `herr` with
an explicit `B`. -/
theorem negativeNeutral_limit_ne_of_quadratic_log_bound
    {I : Type*} [Fintype I]
    (exteriorWeight : ℕ → ℝ) (principalWeight : I → ℕ → ℝ)
    (exteriorMultiplier : ℕ → ℝ) (principalMultiplier : I → ℕ → ℝ)
    (beta : I → ℝ)
    (hupdate : IsTwoStepSquaredWeightUpdate exteriorWeight principalWeight
      exteriorMultiplier principalMultiplier)
    (limitValue H B : ℝ) (r : ℕ) (heightDefect logError : ℕ → ℝ)
    (hH : 0 < H) (hB : 0 ≤ B)
    (hheightPos : ∀ k, 0 < heightDefect k)
    (hheightZero : Tendsto heightDefect atTop (𝓝 0))
    (herror : ∀ᶠ k in atTop,
      |logError k| ≤ B * (heightDefect k) ^ 2)
    (hlogIdentity : limitValue = -H → ∀ k,
      2 * Real.log (exteriorMultiplier k) +
          ∑ i, beta i * (2 * Real.log (principalMultiplier i k)) =
        2 * (logError k - Real.log (1 - heightDefect k / H) -
          Real.log (1 - heightDefect (k + 1) / H)))
    (phi : ℕ → ℕ) (hphi : Tendsto phi atTop atTop)
    (hexterior : Tendsto (fun j ↦ exteriorWeight (2 * phi j + r))
      atTop (𝓝 0))
    (principalLimit : I → ℝ)
    (hprincipalLimitPos : ∀ i, 0 < principalLimit i)
    (hprincipal : ∀ i, Tendsto
      (fun j ↦ principalWeight i (2 * phi j + r))
      atTop (𝓝 (principalLimit i))) :
    limitValue ≠ -H := by
  refine negativeNeutral_limit_ne_of_cocycle
    exteriorWeight principalWeight exteriorMultiplier principalMultiplier
    beta hupdate limitValue H r ?_ phi hphi hexterior principalLimit
      hprincipalLimitPos hprincipal
  intro hnegative
  have hpositive := eventually_pos_of_quadratic_logError
    heightDefect logError H B hH hB hheightPos hheightZero herror
  have hparity : Tendsto (fun k : ℕ ↦ 2 * k + r) atTop atTop := by
    apply tendsto_atTop.2
    intro N
    exact eventually_atTop.2 ⟨N, fun k hk ↦ by omega⟩
  filter_upwards [hparity.eventually hpositive] with k hk
  rw [hlogIdentity hnegative (2 * k + r)]
  linarith

/-- Finitely many strict limiting multipliers have one common two-step
contraction factor and one common tail index. -/
theorem exists_uniform_twoStep_contraction_of_finite_limits
    {J : Type*} [Fintype J] [Nonempty J]
    (weight : J → ℕ → ℝ) (numerator : J → ℕ → ℝ)
    (denominator : ℕ → ℝ) (limitNumerator : J → ℝ) (H : ℝ)
    (hweight : ∀ j k, 0 ≤ weight j k)
    (hrec : ∀ j k, weight j (k + 2) =
      (numerator j k / denominator k) ^ 2 * weight j k)
    (hnumerator : ∀ j, Tendsto (numerator j) atTop (𝓝 (limitNumerator j)))
    (hdenominator : Tendsto denominator atTop (𝓝 H))
    (hH : H ≠ 0) (hstrict : ∀ j, |limitNumerator j / H| < 1) :
    ∃ r : ℝ, ∃ K : ℕ, 0 ≤ r ∧ r < 1 ∧
      ∀ j k, K ≤ k → weight j (k + 2) ≤ r * weight j k := by
  classical
  have hexists (j : J) : ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧
      ∀ᶠ k in atTop, (numerator j k / denominator k) ^ 2 ≤ r :=
    exists_eventually_sq_div_le_of_abs_lt
      (numerator j) denominator (limitNumerator j) H
      (hnumerator j) hdenominator hH (hstrict j)
  choose r hrNonneg hrLt hrEventually using hexists
  let R : ℝ := Finset.univ.sup' Finset.univ_nonempty r
  have hRNonneg : 0 ≤ R := by
    let j₀ : J := Classical.choice inferInstance
    exact (hrNonneg j₀).trans (Finset.le_sup' r (Finset.mem_univ j₀))
  have hRLt : R < 1 := by
    exact (Finset.sup'_lt_iff Finset.univ_nonempty).2
      (fun j hj ↦ hrLt j)
  have hmult : ∀ᶠ k in atTop, ∀ j,
      (numerator j k / denominator k) ^ 2 ≤ R := by
    rw [Filter.eventually_all]
    intro j
    exact (hrEventually j).mono fun k hk ↦
      hk.trans (Finset.le_sup' r (Finset.mem_univ j))
  obtain ⟨K, hK⟩ := eventually_atTop.1 hmult
  refine ⟨R, K, hRNonneg, hRLt, ?_⟩
  intro j k hk
  rw [hrec j k]
  exact mul_le_mul_of_nonneg_right (hK k hk j) (hweight j k)

/-- The common contraction factor gives explicit geometric estimates for the
total exterior squared mass on both parities. -/
theorem finite_exterior_mass_parity_geometric_of_multiplier_limits
    {J : Type*} [Fintype J] [Nonempty J]
    (weight : J → ℕ → ℝ) (numerator : J → ℕ → ℝ)
    (denominator : ℕ → ℝ) (limitNumerator : J → ℝ) (H : ℝ)
    (hweight : ∀ j k, 0 ≤ weight j k)
    (hrec : ∀ j k, weight j (k + 2) =
      (numerator j k / denominator k) ^ 2 * weight j k)
    (hnumerator : ∀ j, Tendsto (numerator j) atTop (𝓝 (limitNumerator j)))
    (hdenominator : Tendsto denominator atTop (𝓝 H))
    (hH : H ≠ 0) (hstrict : ∀ j, |limitNumerator j / H| < 1) :
    ∃ r : ℝ, ∃ K : ℕ, 0 ≤ r ∧ r < 1 ∧
      (∀ n, ∑ j, weight j (K + 2 * n) ≤
        r ^ n * ∑ j, weight j K) ∧
      (∀ n, ∑ j, weight j (K + 2 * n + 1) ≤
        r ^ n * ∑ j, weight j (K + 1)) := by
  obtain ⟨r, K, hr, hrOne, hstep⟩ :=
    exists_uniform_twoStep_contraction_of_finite_limits
      weight numerator denominator limitNumerator H hweight hrec
      hnumerator hdenominator hH hstrict
  exact ⟨r, K, hr, hrOne,
    sum_twoStep_parity_geometric weight K r hr hstep⟩

/-- Manuscript form of exterior decay: the total mass of a finite exterior
spectrum is eventually bounded by one geometric sequence `C * theta^k`.
The constant absorbs the two parity-dependent starting masses. -/
theorem finite_exterior_mass_geometric_of_multiplier_limits
    {J : Type*} [Fintype J] [Nonempty J]
    (weight : J → ℕ → ℝ) (numerator : J → ℕ → ℝ)
    (denominator : ℕ → ℝ) (limitNumerator : J → ℝ) (H : ℝ)
    (hweight : ∀ j k, 0 ≤ weight j k)
    (hrec : ∀ j k, weight j (k + 2) =
      (numerator j k / denominator k) ^ 2 * weight j k)
    (hnumerator : ∀ j, Tendsto (numerator j) atTop (𝓝 (limitNumerator j)))
    (hdenominator : Tendsto denominator atTop (𝓝 H))
    (hH : H ≠ 0) (hstrict : ∀ j, |limitNumerator j / H| < 1) :
    ∃ C theta : ℝ, 0 < C ∧ 0 < theta ∧ theta < 1 ∧
      ∀ᶠ k in atTop, ∑ j, weight j k ≤ C * theta ^ k := by
  obtain ⟨r, K, hr, hrOne, heven, hodd⟩ :=
    finite_exterior_mass_parity_geometric_of_multiplier_limits
      weight numerator denominator limitNumerator H hweight hrec
      hnumerator hdenominator hH hstrict
  let q : ℝ := (r + 1) / 2
  let theta : ℝ := Real.sqrt q
  let mass : ℕ → ℝ := fun k ↦ ∑ j, weight j k
  have hmass (k : ℕ) : 0 ≤ mass k := by
    dsimp only [mass]
    exact Finset.sum_nonneg fun j hj ↦ hweight j k
  have hqPos : 0 < q := by dsimp only [q]; linarith
  have hqLt : q < 1 := by dsimp only [q]; linarith
  have hthetaPos : 0 < theta := by
    exact Real.sqrt_pos.2 hqPos
  have hthetaNonneg : 0 ≤ theta := hthetaPos.le
  have hthetaLt : theta < 1 := by
    calc
      theta = Real.sqrt q := rfl
      _ < Real.sqrt 1 := Real.sqrt_lt_sqrt hqPos.le hqLt
      _ = 1 := Real.sqrt_one
  have hthetaSq : theta ^ 2 = q := by
    exact Real.sq_sqrt hqPos.le
  have hrThetaSq : r ≤ theta ^ 2 := by
    rw [hthetaSq]
    dsimp only [q]
    linarith
  let C : ℝ :=
    max (mass K / theta ^ K) (mass (K + 1) / theta ^ (K + 1)) + 1
  have hthetaPowPos (k : ℕ) : 0 < theta ^ k := pow_pos hthetaPos k
  have hCPos : 0 < C := by
    have hleft : 0 ≤ mass K / theta ^ K :=
      div_nonneg (hmass K) (hthetaPowPos K).le
    have hmax : 0 ≤ max (mass K / theta ^ K)
        (mass (K + 1) / theta ^ (K + 1)) := hleft.trans (le_max_left _ _)
    dsimp only [C]
    linarith
  have hbaseEven : mass K ≤ C * theta ^ K := by
    have hle : mass K / theta ^ K ≤ C := by
      dsimp only [C]
      linarith [le_max_left (mass K / theta ^ K)
        (mass (K + 1) / theta ^ (K + 1))]
    calc
      mass K = (mass K / theta ^ K) * theta ^ K := by
        field_simp [ne_of_gt (hthetaPowPos K)]
      _ ≤ C * theta ^ K :=
        mul_le_mul_of_nonneg_right hle (hthetaPowPos K).le
  have hbaseOdd : mass (K + 1) ≤ C * theta ^ (K + 1) := by
    have hle : mass (K + 1) / theta ^ (K + 1) ≤ C := by
      dsimp only [C]
      linarith [le_max_right (mass K / theta ^ K)
        (mass (K + 1) / theta ^ (K + 1))]
    calc
      mass (K + 1) =
          (mass (K + 1) / theta ^ (K + 1)) * theta ^ (K + 1) := by
        field_simp [ne_of_gt (hthetaPowPos (K + 1))]
      _ ≤ C * theta ^ (K + 1) :=
        mul_le_mul_of_nonneg_right hle (hthetaPowPos (K + 1)).le
  have hEvenAll (n : ℕ) :
      mass (K + 2 * n) ≤ C * theta ^ (K + 2 * n) := by
    calc
      mass (K + 2 * n) ≤ r ^ n * mass K := by
        simpa only [mass] using heven n
      _ ≤ (theta ^ 2) ^ n * mass K := by
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ hr hrThetaSq n) (hmass K)
      _ ≤ (theta ^ 2) ^ n * (C * theta ^ K) :=
        mul_le_mul_of_nonneg_left hbaseEven
          (pow_nonneg (sq_nonneg theta) n)
      _ = C * theta ^ (K + 2 * n) := by
        rw [← pow_mul, pow_add]
        ring
  have hOddAll (n : ℕ) :
      mass (K + 2 * n + 1) ≤ C * theta ^ (K + 2 * n + 1) := by
    calc
      mass (K + 2 * n + 1) ≤ r ^ n * mass (K + 1) := by
        simpa only [mass] using hodd n
      _ ≤ (theta ^ 2) ^ n * mass (K + 1) := by
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ hr hrThetaSq n) (hmass (K + 1))
      _ ≤ (theta ^ 2) ^ n * (C * theta ^ (K + 1)) :=
        mul_le_mul_of_nonneg_left hbaseOdd
          (pow_nonneg (sq_nonneg theta) n)
      _ = C * theta ^ (K + 2 * n + 1) := by
        rw [← pow_mul, show K + 2 * n + 1 = K + 1 + 2 * n by omega,
          pow_add]
        ring
  refine ⟨C, theta, hCPos, hthetaPos, hthetaLt,
    eventually_atTop.2 ⟨K, ?_⟩⟩
  intro k hk
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  rcases Nat.even_or_odd' d with ⟨n, hn | hn⟩
  · subst d
    exact hEvenAll n
  · subst d
    exact hOddAll n

/-- A value lying in `[-H,H]` is strictly interior once both neutral boundary
values have been excluded. -/
theorem abs_lt_of_abs_le_of_ne_ne {a H : ℝ} (hH : 0 < H)
    (hle : |a| ≤ H) (hnePositive : a ≠ H) (hneNegative : a ≠ -H) :
    |a| < H := by
  exact lt_of_le_of_ne hle fun heq ↦ by
    rcases (abs_eq hH.le).mp heq with ha | ha
    · exact hnePositive ha
    · exact hneNegative ha

/-- Evaluation of a product of monic quadratics is continuous in the four
free product coefficients used by `Arnoldi.quadraticProductCoeff`. -/
theorem tendsto_quadraticProduct_eval_of_tendsto_coeff
    {P Q : ℕ → MonicQuadratic} {p q : MonicQuadratic} (t : ℝ)
    (hcoeff : Tendsto (fun k ↦ Arnoldi.quadraticProductCoeff (P k) (Q k))
      atTop (𝓝 (Arnoldi.quadraticProductCoeff p q))) :
    Tendsto (fun k ↦ (P k).toPolynomial.eval t * (Q k).toPolynomial.eval t)
      atTop (𝓝 (p.toPolynomial.eval t * q.toPolynomial.eval t)) := by
  let evalCoeff : ((ℝ × ℝ) × (ℝ × ℝ)) → ℝ := fun c ↦
    t ^ 4 + c.1.1 * t ^ 3 + c.1.2 * t ^ 2 + c.2.1 * t + c.2.2
  have heval : Tendsto
      (fun k ↦ evalCoeff (Arnoldi.quadraticProductCoeff (P k) (Q k)))
      atTop
      (𝓝 (evalCoeff (Arnoldi.quadraticProductCoeff p q))) := by
    have hcontinuous : Continuous evalCoeff := by
      dsimp only [evalCoeff]
      fun_prop
    exact hcontinuous.continuousAt.tendsto.comp hcoeff
  convert heval using 1
  · funext k
    simp only [evalCoeff, Arnoldi.quadraticProductCoeff, MonicQuadratic.eval]
    ring_nf
  · simp only [evalCoeff, Arnoldi.quadraticProductCoeff, MonicQuadratic.eval]
    ring_nf

/-- Operator-specialized exterior decay.  Once the limiting two-step
polynomial is strictly smaller than `tau²` at every exterior eigenvalue, the
exact grouped-component recurrence and polynomial limits give the manuscript
geometric bound for the total exterior squared mass. -/
theorem arnoldiOrbit2_finite_exterior_mass_geometric_of_strict_limit
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v₀ : E)
    {J : Type*} [Fintype J] [Nonempty J]
    (mu : J → A.Eigenvalues) (tau : ℝ) (p q : MonicQuadratic)
    (htau : 0 < tau)
    (hnormalizer : Tendsto (arnoldiNormalizerOrbit2 A v₀) atTop (𝓝 tau))
    (hproduct : Tendsto (fun k ↦ Arnoldi.quadraticProductCoeff
      (arnoldiFactorOrbit2 A v₀ k)
      (arnoldiFactorOrbit2 A v₀ (k + 1))) atTop
      (𝓝 (Arnoldi.quadraticProductCoeff p q)))
    (hstrict : ∀ j,
      |(p.toPolynomial * q.toPolynomial).eval (mu j : ℝ)| < tau ^ 2) :
    ∃ C theta : ℝ, 0 < C ∧ 0 < theta ∧ theta < 1 ∧
      ∀ᶠ k in atTop,
        ∑ j, Spectral.weight A hA (arnoldiOrbit2 A v₀ k) (mu j) ≤
          C * theta ^ k := by
  let weight : J → ℕ → ℝ := fun j k ↦
    Spectral.weight A hA (arnoldiOrbit2 A v₀ k) (mu j)
  let numerator : J → ℕ → ℝ := fun j k ↦
    ((arnoldiFactorOrbit2 A v₀ k).toPolynomial *
      (arnoldiFactorOrbit2 A v₀ (k + 1)).toPolynomial).eval (mu j : ℝ)
  let denominator : ℕ → ℝ := fun k ↦
    arnoldiNormalizerOrbit2 A v₀ k *
      arnoldiNormalizerOrbit2 A v₀ (k + 1)
  let limitNumerator : J → ℝ := fun j ↦
    (p.toPolynomial * q.toPolynomial).eval (mu j : ℝ)
  have hweightNonneg : ∀ j k, 0 ≤ weight j k := by
    intro j k
    exact sq_nonneg _
  have hweightRec : ∀ j k, weight j (k + 2) =
      (numerator j k / denominator k) ^ 2 * weight j k := by
    intro j k
    exact Spectral.weight_arnoldiOrbit2_add_two A hA v₀ (mu j) k
  have hnumerator : ∀ j,
      Tendsto (numerator j) atTop (𝓝 (limitNumerator j)) := by
    intro j
    have ht := tendsto_quadraticProduct_eval_of_tendsto_coeff
      (P := arnoldiFactorOrbit2 A v₀)
      (Q := fun k ↦ arnoldiFactorOrbit2 A v₀ (k + 1))
      (p := p) (q := q) (mu j : ℝ) hproduct
    simpa only [numerator, limitNumerator, Polynomial.eval_mul] using ht
  have hnormalizerShift : Tendsto
      (fun k ↦ arnoldiNormalizerOrbit2 A v₀ (k + 1)) atTop (𝓝 tau) :=
    hnormalizer.comp (tendsto_add_atTop_nat 1)
  have hdenominator : Tendsto denominator atTop (𝓝 (tau ^ 2)) := by
    have ht := hnormalizer.mul hnormalizerShift
    simpa only [denominator, pow_two] using ht
  have hstrictQuotient : ∀ j, |limitNumerator j / tau ^ 2| < 1 := by
    intro j
    rw [abs_div, abs_of_pos (sq_pos_of_pos htau)]
    exact (div_lt_one (sq_pos_of_pos htau)).2 (hstrict j)
  simpa only [weight] using
    finite_exterior_mass_geometric_of_multiplier_limits
      weight numerator denominator limitNumerator (tau ^ 2)
      hweightNonneg hweightRec hnumerator hdenominator
      (pow_ne_zero 2 (ne_of_gt htau)) hstrictQuotient

/-- Boundary-value form used immediately after the cocycle argument.  The
limit equation gives `|Q(mu)| ≤ tau²`; membership outside the four principal
nodes excludes `+tau²`; and `negativeNeutral_limit_ne_of_cocycle` excludes
`-tau²`. -/
theorem arnoldiOrbit2_finite_exterior_mass_geometric_of_neutral_excluded
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v₀ : E)
    {J : Type*} [Fintype J] [Nonempty J]
    (mu : J → A.Eigenvalues) (tau : ℝ) (p q : MonicQuadratic)
    (htau : 0 < tau)
    (hnormalizer : Tendsto (arnoldiNormalizerOrbit2 A v₀) atTop (𝓝 tau))
    (hproduct : Tendsto (fun k ↦ Arnoldi.quadraticProductCoeff
      (arnoldiFactorOrbit2 A v₀ k)
      (arnoldiFactorOrbit2 A v₀ (k + 1))) atTop
      (𝓝 (Arnoldi.quadraticProductCoeff p q)))
    (hbound : ∀ j,
      |(p.toPolynomial * q.toPolynomial).eval (mu j : ℝ)| ≤ tau ^ 2)
    (hnePositive : ∀ j,
      (p.toPolynomial * q.toPolynomial).eval (mu j : ℝ) ≠ tau ^ 2)
    (hneNegative : ∀ j,
      (p.toPolynomial * q.toPolynomial).eval (mu j : ℝ) ≠ -(tau ^ 2)) :
    ∃ C theta : ℝ, 0 < C ∧ 0 < theta ∧ theta < 1 ∧
      ∀ᶠ k in atTop,
        ∑ j, Spectral.weight A hA (arnoldiOrbit2 A v₀ k) (mu j) ≤
          C * theta ^ k := by
  apply arnoldiOrbit2_finite_exterior_mass_geometric_of_strict_limit
    A hA v₀ mu tau p q htau hnormalizer hproduct
  intro j
  exact abs_lt_of_abs_le_of_ne_ne (sq_pos_of_pos htau)
    (hbound j) (hnePositive j) (hneNegative j)

end

end Exterior
end Forsythe
