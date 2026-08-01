import Forsythe.FourNode.Weights
import Forsythe.Polynomial.FourNode

/-!
# The four-node barycentric parameter

The residual values `x_i P_x(lambda_i)` satisfy three exact moment equations.
Solving this four-variable system in barycentric coordinates shows that
`E_i x_i P_x(lambda_i)` is affine in `lambda_i`.  Its slope is `H(x)`;
the negative intercept divided by this slope is the manuscript parameter
`rho(x)`.
-/

set_option autoImplicit false

namespace Forsythe
namespace FourNode

open Polynomial
open scoped BigOperators

noncomputable section

/-- The barycentric denominator
`E_i = ∏_{j ≠ i} (lambda_i - lambda_j)`. -/
def E (lambda : Fin 4 → ℝ) (i : Fin 4) : ℝ :=
  cubicLagrangeDenominator lambda i

theorem E_eq_prod (lambda : Fin 4 → ℝ) (i : Fin 4) :
    E lambda i = ∏ j ∈ Finset.univ.erase i, (lambda i - lambda j) :=
  rfl

theorem E_ne_zero {lambda : Fin 4 → ℝ}
    (hlambda : Function.Injective lambda) (i : Fin 4) :
    E lambda i ≠ 0 :=
  cubicLagrangeDenominator_ne_zero hlambda i

theorem E_ne_zero_of_strictMono {lambda : Fin 4 → ℝ}
    (hlambda : StrictMono lambda) (i : Fin 4) :
    E lambda i ≠ 0 :=
  E_ne_zero hlambda.injective i

private theorem erase_zero_fin_four :
    (Finset.univ.erase (0 : Fin 4)) = {1, 2, 3} := by decide

private theorem erase_one_fin_four :
    (Finset.univ.erase (1 : Fin 4)) = {0, 2, 3} := by decide

private theorem erase_two_fin_four :
    (Finset.univ.erase (2 : Fin 4)) = {0, 1, 3} := by decide

private theorem erase_three_fin_four :
    (Finset.univ.erase (3 : Fin 4)) = {0, 1, 2} := by decide

private theorem E_zero (lambda : Fin 4 → ℝ) :
    E lambda 0 =
      (lambda 0 - lambda 1) * (lambda 0 - lambda 2) *
        (lambda 0 - lambda 3) := by
  rw [E, cubicLagrangeDenominator, erase_zero_fin_four]
  simp
  ring

private theorem E_one (lambda : Fin 4 → ℝ) :
    E lambda 1 =
      (lambda 1 - lambda 0) * (lambda 1 - lambda 2) *
        (lambda 1 - lambda 3) := by
  rw [E, cubicLagrangeDenominator, erase_one_fin_four]
  simp
  ring

private theorem E_two (lambda : Fin 4 → ℝ) :
    E lambda 2 =
      (lambda 2 - lambda 0) * (lambda 2 - lambda 1) *
        (lambda 2 - lambda 3) := by
  rw [E, cubicLagrangeDenominator, erase_two_fin_four]
  simp
  ring

private theorem E_three (lambda : Fin 4 → ℝ) :
    E lambda 3 =
      (lambda 3 - lambda 0) * (lambda 3 - lambda 1) *
        (lambda 3 - lambda 2) := by
  rw [E, cubicLagrangeDenominator, erase_three_fin_four]
  simp
  ring

/-- The residual's quadratic moment is exactly its squared height. -/
theorem sum_weight_mul_P_eval_mul_sq_eq_height
    {lambda : Fin 4 → ℝ} (hlambda : Function.Injective lambda)
    (x : Weights) :
    ∑ i, x i * (P lambda x).toPolynomial.eval (lambda i) * lambda i ^ 2 =
      H lambda x := by
  let p := P lambda x
  have hzero := P_orthogonal_one hlambda x
  have hone := P_orthogonal_X hlambda x
  simp only [weightedPolyInner, eval_one, mul_one] at hzero
  simp only [weightedPolyInner, eval_X] at hone
  change (∑ i, x i * p.toPolynomial.eval (lambda i)) = 0 at hzero
  change (∑ i, x i * p.toPolynomial.eval (lambda i) * lambda i) = 0 at hone
  change ∑ i, x i * p.toPolynomial.eval (lambda i) * lambda i ^ 2 =
    weightedPolyInner lambda x p.toPolynomial p.toPolynomial
  rw [weightedPolyInner]
  calc
    ∑ i, x i * p.toPolynomial.eval (lambda i) * lambda i ^ 2 =
        ∑ i, (x i * p.toPolynomial.eval (lambda i) *
          p.toPolynomial.eval (lambda i) -
            p.linearCoeff *
              (x i * p.toPolynomial.eval (lambda i) * lambda i) -
            p.constantCoeff * (x i * p.toPolynomial.eval (lambda i))) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [MonicQuadratic.eval]
      ring
    _ = (∑ i, x i * p.toPolynomial.eval (lambda i) *
          p.toPolynomial.eval (lambda i)) -
        p.linearCoeff *
          (∑ i, x i * p.toPolynomial.eval (lambda i) * lambda i) -
        p.constantCoeff *
          (∑ i, x i * p.toPolynomial.eval (lambda i)) := by
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
      simp only [Finset.mul_sum]
    _ = ∑ i, x i * p.toPolynomial.eval (lambda i) *
          p.toPolynomial.eval (lambda i) := by
      rw [hone, hzero, mul_zero, sub_zero, mul_zero, sub_zero]

private theorem barycentric_affine_identity
    {lambda : Fin 4 → ℝ} (y : Fin 4 → ℝ) (K : ℝ)
    (hzero : ∑ i, y i = 0)
    (hone : ∑ i, lambda i * y i = 0)
    (htwo : ∑ i, lambda i ^ 2 * y i = K) (i : Fin 4) :
    E lambda i * y i =
      K * (lambda i - lambda 0) + E lambda 0 * y 0 := by
  simp only [Fin.sum_univ_four] at hzero hone htwo
  fin_cases i
  · change E lambda 0 * y 0 =
      K * (lambda 0 - lambda 0) + E lambda 0 * y 0
    rw [E_zero]
    ring
  · change E lambda 1 * y 1 =
      K * (lambda 1 - lambda 0) + E lambda 0 * y 0
    rw [E_one, E_zero]
    linear_combination
      (lambda 1 - lambda 0) * htwo -
      (lambda 1 - lambda 0) * (lambda 2 + lambda 3) * hone +
      (lambda 1 - lambda 0) * (lambda 2 * lambda 3) * hzero
  · change E lambda 2 * y 2 =
      K * (lambda 2 - lambda 0) + E lambda 0 * y 0
    rw [E_two, E_zero]
    linear_combination
      (lambda 2 - lambda 0) * htwo -
      (lambda 2 - lambda 0) * (lambda 1 + lambda 3) * hone +
      (lambda 2 - lambda 0) * (lambda 1 * lambda 3) * hzero
  · change E lambda 3 * y 3 =
      K * (lambda 3 - lambda 0) + E lambda 0 * y 0
    rw [E_three, E_zero]
    linear_combination
      (lambda 3 - lambda 0) * htwo -
      (lambda 3 - lambda 0) * (lambda 1 + lambda 2) * hone +
      (lambda 3 - lambda 0) * (lambda 1 * lambda 2) * hzero

/-- Denominator-cleared affine identity for the weighted Arnoldi residual. -/
theorem E_mul_weight_mul_P_eval
    {lambda : Fin 4 → ℝ} (hlambda : Function.Injective lambda)
    (x : Weights) (i : Fin 4) :
    E lambda i * (x i * (P lambda x).toPolynomial.eval (lambda i)) =
      H lambda x * (lambda i - lambda 0) +
        E lambda 0 * (x 0 * (P lambda x).toPolynomial.eval (lambda 0)) := by
  let y : Fin 4 → ℝ := fun j ↦
    x j * (P lambda x).toPolynomial.eval (lambda j)
  apply barycentric_affine_identity y (H lambda x)
  · simpa [y, weightedPolyInner] using P_orthogonal_one hlambda x
  · have h := P_orthogonal_X hlambda x
    simp only [weightedPolyInner, eval_X] at h
    simpa [y, mul_assoc, mul_left_comm, mul_comm] using h
  · have h := sum_weight_mul_P_eval_mul_sq_eq_height hlambda x
    simpa [y, mul_assoc, mul_left_comm, mul_comm] using h

/-- `rho` is defined through the fixed node `0`.  The formula is total;
distinctness later supplies the nonzero denominators and `H > 0`. -/
def rho (lambda : Fin 4 → ℝ) (x : Weights) : ℝ :=
  lambda 0 -
    E lambda 0 * (x 0 * (P lambda x).toPolynomial.eval (lambda 0)) /
      H lambda x

/-- The fixed-node definition is independent of the chosen node. -/
theorem rho_eq_node_formula
    {lambda : Fin 4 → ℝ} (hlambda : Function.Injective lambda)
    (x : Weights) (i : Fin 4) :
    rho lambda x = lambda i -
      E lambda i * (x i * (P lambda x).toPolynomial.eval (lambda i)) /
        H lambda x := by
  have hH : H lambda x ≠ 0 := ne_of_gt (height_pos hlambda x)
  have haffine := E_mul_weight_mul_P_eval hlambda x i
  rw [rho]
  field_simp [hH]
  linear_combination haffine

/-- Manuscript four-node identity
`x_i P_x(lambda_i) = H(x) (lambda_i-rho(x)) / E_i`. -/
theorem weight_mul_P_eval_eq_height_mul_sub_rho_div_E
    {lambda : Fin 4 → ℝ} (hlambda : Function.Injective lambda)
    (x : Weights) (i : Fin 4) :
    x i * (P lambda x).toPolynomial.eval (lambda i) =
      H lambda x * (lambda i - rho lambda x) / E lambda i := by
  have hE : E lambda i ≠ 0 := E_ne_zero hlambda i
  have hnode := rho_eq_node_formula hlambda x i
  have hH : H lambda x ≠ 0 := ne_of_gt (height_pos hlambda x)
  field_simp [hH] at hnode
  apply (eq_div_iff hE).2
  calc
    x i * (P lambda x).toPolynomial.eval (lambda i) * E lambda i =
        E lambda i *
          (x i * (P lambda x).toPolynomial.eval (lambda i)) := by ring
    _ = lambda i * H lambda x - rho lambda x * H lambda x := by
      linarith [hnode]
    _ = H lambda x * (lambda i - rho lambda x) := by ring

/-- Equivalent node-independent definition of `rho`. -/
theorem rho_eq_lambda_sub_E_mul_weight_mul_P_eval_div_height
    {lambda : Fin 4 → ℝ} (hlambda : Function.Injective lambda)
    (x : Weights) (i : Fin 4) :
    rho lambda x = lambda i -
      E lambda i * (x i * (P lambda x).toPolynomial.eval (lambda i)) /
        H lambda x :=
  rho_eq_node_formula hlambda x i

/-- Ordered-node form of the manuscript identity. -/
theorem weight_mul_P_eval_eq_height_mul_sub_rho_div_E_of_strictMono
    {lambda : Fin 4 → ℝ} (hlambda : StrictMono lambda)
    (x : Weights) (i : Fin 4) :
    x i * (P lambda x).toPolynomial.eval (lambda i) =
      H lambda x * (lambda i - rho lambda x) / E lambda i :=
  weight_mul_P_eval_eq_height_mul_sub_rho_div_E hlambda.injective x i

end

end FourNode
end Forsythe
