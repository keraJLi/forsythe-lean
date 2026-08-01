import Forsythe.Exterior.Geometric
import Mathlib.Topology.Algebra.Order.Field

/-!
# Strict contraction from a limiting multiplier

If a two-step scalar multiplier converges to a number of modulus strictly
less than one, its square is uniformly bounded by a fixed contraction factor
on a tail.  This is the easy exterior-mode branch; only the negative-neutral
case requires the logarithmic cocycle.
-/

set_option autoImplicit false

namespace Forsythe
namespace Exterior

open Filter Topology

/-- A convergent quotient whose limiting modulus is below one has a uniform
squared contraction factor. -/
theorem exists_eventually_sq_div_le_of_abs_lt
    (numerator denominator : ℕ → ℝ) (a b : ℝ)
    (hnumerator : Tendsto numerator atTop (𝓝 a))
    (hdenominator : Tendsto denominator atTop (𝓝 b))
    (hb : b ≠ 0) (hab : |a / b| < 1) :
    ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧
      ∀ᶠ n in atTop, (numerator n / denominator n) ^ 2 ≤ r := by
  let limitSq := (a / b) ^ 2
  let r := (limitSq + 1) / 2
  have hlimitNonneg : 0 ≤ limitSq := sq_nonneg _
  have hlimitLt : limitSq < 1 := by
    dsimp only [limitSq]
    rw [← sq_abs]
    nlinarith [abs_nonneg (a / b)]
  have hrNonneg : 0 ≤ r := by
    dsimp only [r]
    linarith
  have hrLt : r < 1 := by
    dsimp only [r]
    linarith
  have hquotient : Tendsto (fun n => numerator n / denominator n)
      atTop (𝓝 (a / b)) :=
    hnumerator.div hdenominator hb
  have hsquare : Tendsto (fun n => (numerator n / denominator n) ^ 2)
      atTop (𝓝 limitSq) := by
    simpa only [limitSq] using hquotient.pow 2
  have hlimitR : limitSq < r := by
    dsimp only [r]
    linarith
  exact ⟨r, hrNonneg, hrLt,
    (hsquare.eventually_lt_const hlimitR).mono fun _ hn => hn.le⟩

/-- Version with the manuscript normalization `b = tau²`. -/
theorem exists_eventually_sq_div_le_of_abs_lt_sq
    (numerator denominator : ℕ → ℝ) (a tau : ℝ)
    (hnumerator : Tendsto numerator atTop (𝓝 a))
    (hdenominator : Tendsto denominator atTop (𝓝 (tau ^ 2)))
    (htau : 0 < tau) (ha : |a| < tau ^ 2) :
    ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧
      ∀ᶠ n in atTop, (numerator n / denominator n) ^ 2 ≤ r := by
  apply exists_eventually_sq_div_le_of_abs_lt numerator denominator a (tau ^ 2)
    hnumerator hdenominator (pow_ne_zero 2 (ne_of_gt htau))
  rw [abs_div, abs_of_nonneg (sq_nonneg tau)]
  exact (div_lt_one (sq_pos_of_pos htau)).mpr ha

/-- Turn the eventual multiplier bound into an eventual two-step contraction
of a nonnegative weight sequence. -/
theorem eventually_twoStep_weight_le
    (w multiplier : ℕ → ℝ) (r : ℝ)
    (hrec : ∀ n, w (n + 2) = (multiplier n) ^ 2 * w n)
    (hw : ∀ n, 0 ≤ w n)
    (hmult : ∀ᶠ n in atTop, (multiplier n) ^ 2 ≤ r) :
    ∀ᶠ n in atTop, w (n + 2) ≤ r * w n := by
  filter_upwards [hmult] with n hn
  rw [hrec n]
  exact mul_le_mul_of_nonneg_right hn (hw n)

end Exterior
end Forsythe
