import Forsythe.Polynomial.Lagrange
import Forsythe.Exterior.LogEstimate

/-!
# Cubic first-variation cancellation

At an exterior node, the four cubic Lagrange coefficients reproduce every
degree-at-most-three perturbation.  Combining this exact cancellation with a
quadratic logarithm remainder gives the explicit estimate used in the
negative-neutral exterior-mode argument.
-/

set_option autoImplicit false

namespace Forsythe
namespace Exterior

open scoped BigOperators
open Polynomial

noncomputable section

/-- The exterior coefficient attached to principal node `i`. -/
def lagrangeWeight (lambda : Fin 4 → ℝ) (t : ℝ) (i : Fin 4) : ℝ :=
  FourNode.cubicLagrangeCoeff lambda t i

/-- Cubic interpolation cancels the complete first variation at the exterior
node. -/
theorem cubic_firstVariation_cancel
    {lambda : Fin 4 → ℝ} (hlambda : Function.Injective lambda)
    (f : Polynomial ℝ) (hf : f.natDegree ≤ 3) (t : ℝ) :
    -f.eval t + ∑ i : Fin 4, lagrangeWeight lambda t i * f.eval (lambda i) = 0 := by
  simp only [lagrangeWeight]
  have h := FourNode.eval_eq_sum_cubicLagrangeCoeff_mul_eval
    hlambda f hf t
  linarith

/-- The exterior Lagrange weights sum to one. -/
theorem sum_lagrangeWeight
    {lambda : Fin 4 → ℝ} (hlambda : Function.Injective lambda) (t : ℝ) :
    ∑ i : Fin 4, lagrangeWeight lambda t i = 1 := by
  simpa only [lagrangeWeight] using FourNode.sum_cubicLagrangeCoeff hlambda t

private def logError (x : ℝ) : ℝ := Real.log (1 + x) - x

private theorem abs_logError_le (x : ℝ) (hx : |x| ≤ (1 : ℝ) / 2) :
    |logError x| ≤ 2 * x ^ 2 := by
  simpa only [logError] using abs_log_one_add_sub_le_two_mul_sq hx

/-- Explicit quadratic control after an arbitrary finite weighted linear
cancellation. -/
theorem abs_weighted_log_cancellation_le
    {I : Type*} [Fintype I]
    (beta x : I → ℝ) (xExterior : ℝ)
    (hxExterior : |xExterior| ≤ (1 : ℝ) / 2)
    (hx : ∀ i, |x i| ≤ (1 : ℝ) / 2)
    (hcancel : -xExterior + ∑ i, beta i * x i = 0) :
    |-Real.log (1 + xExterior) +
        ∑ i, beta i * Real.log (1 + x i)| ≤
      2 * xExterior ^ 2 + ∑ i, |beta i| * (2 * (x i) ^ 2) := by
  have hrearrange :
      -Real.log (1 + xExterior) +
          ∑ i, beta i * Real.log (1 + x i) =
        -logError xExterior + ∑ i, beta i * logError (x i) := by
    dsimp only [logError]
    have hlinear : ∑ i, beta i * x i = xExterior := by linarith
    have hsum :
        ∑ i, beta i * (Real.log (1 + x i) - x i) =
          (∑ i, beta i * Real.log (1 + x i)) -
            ∑ i, beta i * x i := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [hsum, hlinear]
    ring
  rw [hrearrange]
  calc
    |-logError xExterior + ∑ i, beta i * logError (x i)| ≤
        |logError xExterior| + |∑ i, beta i * logError (x i)| := by
          simpa only [abs_neg] using
            (abs_add_le (-logError xExterior) (∑ i, beta i * logError (x i)))
    _ ≤ |logError xExterior| +
        ∑ i, |beta i * logError (x i)| := by
          gcongr
          exact Finset.abs_sum_le_sum_abs _ _
    _ = |logError xExterior| +
        ∑ i, |beta i| * |logError (x i)| := by
          simp only [abs_mul]
    _ ≤ 2 * xExterior ^ 2 +
        ∑ i, |beta i| * (2 * (x i) ^ 2) := by
          apply add_le_add (abs_logError_le xExterior hxExterior)
          apply Finset.sum_le_sum
          intro i hi
          exact mul_le_mul_of_nonneg_left
            (abs_logError_le (x i) (hx i)) (abs_nonneg (beta i))

/-- Four-node specialization: a cubic perturbation has only quadratic
logarithmic error after Lagrange aggregation. -/
theorem abs_lagrange_log_firstVariation_le
    {lambda : Fin 4 → ℝ} (hlambda : Function.Injective lambda)
    (f : Polynomial ℝ) (hf : f.natDegree ≤ 3) (t scale : ℝ)
    (ht : |f.eval t / scale| ≤ (1 : ℝ) / 2)
    (hnodes : ∀ i, |f.eval (lambda i) / scale| ≤ (1 : ℝ) / 2) :
    |-Real.log (1 + f.eval t / scale) +
        ∑ i : Fin 4, lagrangeWeight lambda t i *
          Real.log (1 + f.eval (lambda i) / scale)| ≤
      2 * (f.eval t / scale) ^ 2 +
        ∑ i : Fin 4, |lagrangeWeight lambda t i| *
          (2 * (f.eval (lambda i) / scale) ^ 2) := by
  apply abs_weighted_log_cancellation_le
  · exact ht
  · exact hnodes
  · have hcancel := cubic_firstVariation_cancel hlambda f hf t
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

end

end Exterior
end Forsythe
