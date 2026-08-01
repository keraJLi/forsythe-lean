import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

/-!
# A quadratic estimate for `log (1 + x)`

This file isolates the elementary logarithmic estimate used for exterior
coordinates.  Its sequence-level consequences are phrased as summability
statements, so they can be applied directly to geometrically decaying error
terms.
-/

set_option autoImplicit false

namespace Forsythe

open Filter
open scoped Topology

namespace Exterior

/-- On the half-unit interval, the error in the linear approximation to
`log (1 + x)` is bounded by twice the square of `x`. -/
theorem abs_log_one_add_sub_le_two_mul_sq {x : ℝ} (hx : |x| ≤ 1 / 2) :
    |Real.log (1 + x) - x| ≤ 2 * x ^ 2 := by
  have hxlt : |-x| < 1 := by
    rw [abs_neg]
    linarith [abs_nonneg x]
  have hTaylor := Real.abs_log_sub_add_sum_range_le (x := -x) hxlt 1
  have hraw : |Real.log (1 + x) - x| ≤ |x| ^ 2 / (1 - |x|) := by
    simpa [Finset.sum_range_succ, abs_neg, sub_eq_add_neg, add_comm, add_left_comm]
      using hTaylor
  calc
    |Real.log (1 + x) - x| ≤ |x| ^ 2 / (1 - |x|) := hraw
    _ ≤ 2 * |x| ^ 2 := by
      have hden : 1 / 2 ≤ 1 - |x| := by linarith
      have hdenpos : 0 < 1 - |x| := lt_of_lt_of_le (by norm_num) hden
      rw [div_le_iff₀ hdenpos]
      nlinarith [sq_nonneg |x|]
    _ = 2 * x ^ 2 := by rw [sq_abs]

/-- The pointwise logarithmic estimate applies eventually to any sequence
which eventually lies in the half-unit interval. -/
theorem eventually_abs_log_one_add_sub_le_two_mul_sq
    {u : ℕ → ℝ} (hu : ∀ᶠ n in atTop, |u n| ≤ 1 / 2) :
    ∀ᶠ n in atTop, |Real.log (1 + u n) - u n| ≤ 2 * (u n) ^ 2 :=
  hu.mono fun _ hn ↦ abs_log_one_add_sub_le_two_mul_sq hn

/-- If the squares of a perturbation are summable and the perturbation is
eventually at most one half, then the errors in linearizing `log (1 + u n)`
are summable. -/
theorem summable_log_one_add_sub_of_summable_sq
    {u : ℕ → ℝ} (hu : ∀ᶠ n in atTop, |u n| ≤ 1 / 2)
    (hsq : Summable fun n ↦ (u n) ^ 2) :
    Summable fun n ↦ Real.log (1 + u n) - u n := by
  refine (hsq.mul_left 2).of_norm_bounded_eventually_nat ?_
  filter_upwards [eventually_abs_log_one_add_sub_le_two_mul_sq hu] with n hn
  simpa only [Real.norm_eq_abs] using hn

/-- In particular, the logarithmic linearization errors are summable for a
geometrically decaying perturbation. -/
theorem summable_log_one_add_sub_of_geometric
    {u : ℕ → ℝ} {C q : ℝ} (hC : 0 ≤ C) (hq_nonneg : 0 ≤ q) (hq_lt_one : q < 1)
    (hu : ∀ n, |u n| ≤ C * q ^ n) :
    Summable fun n ↦ Real.log (1 + u n) - u n := by
  have hgeom : Summable fun n : ℕ ↦ q ^ n :=
    summable_geometric_of_lt_one hq_nonneg hq_lt_one
  have husum : Summable u := by
    refine (hgeom.mul_left C).of_norm_bounded ?_
    intro n
    simpa only [Real.norm_eq_abs] using hu n
  have hhalf : ∀ᶠ n in atTop, |u n| ≤ 1 / 2 := by
    have hzero : Tendsto (fun n ↦ |u n|) atTop (𝓝 0) :=
      by simpa only [Real.norm_eq_abs, abs_zero] using husum.tendsto_atTop_zero.norm
    exact hzero.eventually_le_const (by norm_num)
  have hq_sq_lt_one : q ^ 2 < 1 :=
    pow_lt_one₀ hq_nonneg hq_lt_one (by norm_num)
  have hgeomSq : Summable fun n : ℕ ↦ C ^ 2 * (q ^ 2) ^ n :=
    (summable_geometric_of_lt_one (sq_nonneg q) hq_sq_lt_one).mul_left (C ^ 2)
  have hsq : Summable fun n ↦ (u n) ^ 2 := by
    refine hgeomSq.of_norm_bounded ?_
    intro n
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (u n))]
    calc
      (u n) ^ 2 = |u n| ^ 2 := (sq_abs (u n)).symm
      _ ≤ (C * q ^ n) ^ 2 :=
        (sq_le_sq₀ (abs_nonneg (u n)) (mul_nonneg hC (pow_nonneg hq_nonneg n))).2 (hu n)
      _ = C ^ 2 * (q ^ 2) ^ n := by
        rw [mul_pow, ← pow_mul, Nat.mul_comm n 2, pow_mul]
  exact summable_log_one_add_sub_of_summable_sq hhalf hsq

end Exterior

end Forsythe
