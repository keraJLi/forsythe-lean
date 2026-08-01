import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-!
# A quadratic estimate for `log (1 + x)`

This file isolates the elementary logarithmic estimate used for exterior
coordinates.
-/

set_option autoImplicit false

namespace Forsythe

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

end Exterior

end Forsythe
