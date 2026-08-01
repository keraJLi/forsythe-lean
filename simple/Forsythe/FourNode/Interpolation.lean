import Forsythe.FourNode.Rho

/-!
# The exact four-node interpolation identity

This module proves the boundary-safe interpolation identity for one exact
four-node update.  The proof first clears the factor `z - rho(x)` and uses
uniqueness at the four distinct nodes; in particular it never divides by a
weight or by `nodalQuartic lambda` evaluated at `rho(x)`.
-/

set_option autoImplicit false

namespace Forsythe
namespace FourNode

open Polynomial

noncomputable section

/-- The cubic part left after subtracting the nodal quartic and the new
height from two consecutive monic quadratic factors. -/
def interpolationDifference (lambda : Fin 4 → ℝ)
    (hlambda : Function.Injective lambda) (x : Weights) : ℝ[X] :=
  (P lambda x).toPolynomial *
      (P lambda (T lambda hlambda x)).toPolynomial -
    nodalQuartic lambda - C (H lambda (T lambda hlambda x))

/-- The concrete cubic coefficient in the four-node interpolation identity. -/
def alpha (lambda : Fin 4 → ℝ) (hlambda : Function.Injective lambda)
    (x : Weights) : ℝ :=
  (interpolationDifference lambda hlambda x).coeff 3

/-- The factor-cleared interpolation difference.  Its quartic coefficient
cancels by the definition of `alpha`, so it is again a cubic. -/
private def clearedDifference (lambda : Fin 4 → ℝ)
    (hlambda : Function.Injective lambda) (x : Weights) : ℝ[X] :=
  (X - C (rho lambda x)) * interpolationDifference lambda hlambda x -
    alpha lambda hlambda x • nodalQuartic lambda -
      C (H lambda (T lambda hlambda x) *
        (rho lambda x - rho lambda (T lambda hlambda x)))

private theorem natDegree_monicQuadratic (p : MonicQuadratic) :
    p.toPolynomial.natDegree = 2 := by
  rw [MonicQuadratic.toPolynomial]
  compute_degree <;> norm_num

private theorem natDegree_nodalQuartic (lambda : Fin 4 → ℝ) :
    (nodalQuartic lambda).natDegree = 4 := by
  rw [nodalQuartic, natDegree_prod_of_monic]
  · simp
  · intro i hi
    exact monic_X_sub_C _

private theorem nodalQuartic_eval_node (lambda : Fin 4 → ℝ) (i : Fin 4) :
    (nodalQuartic lambda).eval (lambda i) = 0 := by
  rw [nodalQuartic, eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp

private theorem interpolationDifference_natDegree_le
    (lambda : Fin 4 → ℝ) (hlambda : Function.Injective lambda)
    (x : Weights) :
    (interpolationDifference lambda hlambda x).natDegree ≤ 3 := by
  let p := P lambda x
  let q := P lambda (T lambda hlambda x)
  have hpMonic : p.toPolynomial.Monic := MonicQuadratic.monic p
  have hqMonic : q.toPolynomial.Monic := MonicQuadratic.monic q
  have hprodMonic : (p.toPolynomial * q.toPolynomial).Monic :=
    hpMonic.mul hqMonic
  have hprodNat : (p.toPolynomial * q.toPolynomial).natDegree = 4 := by
    rw [hpMonic.natDegree_mul hqMonic]
    simp [natDegree_monicQuadratic]
  have hPiMonic : (nodalQuartic lambda).Monic := nodalQuartic_monic lambda
  have hPiNat : (nodalQuartic lambda).natDegree = 4 :=
    natDegree_nodalQuartic lambda
  rw [natDegree_le_iff_coeff_eq_zero]
  intro n hn
  by_cases hn4 : n = 4
  · subst n
    have hprodCoeff :
        (p.toPolynomial * q.toPolynomial).coeff 4 = 1 := by
      simpa [hprodNat] using hprodMonic.coeff_natDegree
    have hPiCoeff : (nodalQuartic lambda).coeff 4 = 1 := by
      simpa [hPiNat] using hPiMonic.coeff_natDegree
    simp [interpolationDifference, p, q, hprodCoeff, hPiCoeff]
  · have h4n : 4 < n := by omega
    have hprodCoeff :
        (p.toPolynomial * q.toPolynomial).coeff n = 0 :=
      coeff_eq_zero_of_natDegree_lt (hprodNat.trans_lt h4n)
    have hPiCoeff : (nodalQuartic lambda).coeff n = 0 :=
      coeff_eq_zero_of_natDegree_lt (hPiNat.trans_lt h4n)
    have hn0 : n ≠ 0 := by omega
    rw [interpolationDifference, coeff_sub, coeff_sub, hprodCoeff, hPiCoeff,
      coeff_C_of_ne_zero hn0]
    ring

private theorem clearedDifference_natDegree_le
    (lambda : Fin 4 → ℝ) (hlambda : Function.Injective lambda)
    (x : Weights) :
    (clearedDifference lambda hlambda x).natDegree ≤ 3 := by
  let g := interpolationDifference lambda hlambda x
  have hg : g.natDegree ≤ 3 := interpolationDifference_natDegree_le lambda hlambda x
  have hgRaw :
      (interpolationDifference lambda hlambda x).natDegree ≤ 3 := by
    simpa [g] using hg
  have hg4 : g.coeff 4 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hg.trans_lt (by norm_num))
  have hPiMonic : (nodalQuartic lambda).Monic := nodalQuartic_monic lambda
  have hPiNat : (nodalQuartic lambda).natDegree = 4 :=
    natDegree_nodalQuartic lambda
  have hPiCoeff : (nodalQuartic lambda).coeff 4 = 1 := by
    simpa [hPiNat] using hPiMonic.coeff_natDegree
  have hleFour : (clearedDifference lambda hlambda x).natDegree ≤ 4 := by
    rw [clearedDifference]
    compute_degree
    rw [hPiNat]
    omega
  rw [natDegree_le_iff_coeff_eq_zero]
  intro n hn
  by_cases hn4 : n = 4
  · subst n
    simp only [clearedDifference, coeff_sub, coeff_smul, coeff_C,
      if_neg (by norm_num : (4 : ℕ) ≠ 0)]
    rw [coeff_X_sub_C_mul]
    simp [g, alpha, hg4, hPiCoeff]
  · exact coeff_eq_zero_of_natDegree_lt
      (hleFour.trans_lt (by omega))

/-- The update identity at a principal node with every potentially vanishing
factor left uncancelled.  This is the algebraic input for the four-root
argument. -/
theorem sub_rho_mul_consecutive_P_eval
    {lambda : Fin 4 → ℝ} (hlambda : Function.Injective lambda)
    (x : Weights) (i : Fin 4) :
    (lambda i - rho lambda x) *
        (P lambda x).toPolynomial.eval (lambda i) *
        (P lambda (T lambda hlambda x)).toPolynomial.eval (lambda i) =
      H lambda (T lambda hlambda x) *
        (lambda i - rho lambda (T lambda hlambda x)) := by
  let y := T lambda hlambda x
  let p := (P lambda x).toPolynomial.eval (lambda i)
  let q := (P lambda y).toPolynomial.eval (lambda i)
  have hE : E lambda i ≠ 0 := E_ne_zero hlambda i
  have hHx : H lambda x ≠ 0 := ne_of_gt (height_pos hlambda x)
  have hx := weight_mul_P_eval_eq_height_mul_sub_rho_div_E hlambda x i
  have hy := weight_mul_P_eval_eq_height_mul_sub_rho_div_E hlambda y i
  have hxClear : x i * p * E lambda i =
      H lambda x * (lambda i - rho lambda x) := by
    simpa [p] using (eq_div_iff hE).mp hx
  have hyClear : y i * q * E lambda i =
      H lambda y * (lambda i - rho lambda y) := by
    simpa [q] using (eq_div_iff hE).mp hy
  have hupdate : H lambda x * y i = x i * p ^ 2 := by
    simpa [y, p] using height_mul_T_weight lambda hlambda x i
  have hmul :
      H lambda x *
        ((lambda i - rho lambda x) * p * q -
          H lambda y * (lambda i - rho lambda y)) = 0 := by
    calc
      H lambda x *
          ((lambda i - rho lambda x) * p * q -
            H lambda y * (lambda i - rho lambda y)) =
          (x i * p * E lambda i) * p * q -
            H lambda x * (y i * q * E lambda i) := by
              rw [hxClear, hyClear]
              ring
      _ = E lambda i * q * (x i * p ^ 2 - H lambda x * y i) := by
            ring
      _ = 0 := by rw [hupdate]; ring
  have hzero := (mul_eq_zero.mp hmul).resolve_left hHx
  simpa [y, p, q] using sub_eq_zero.mp hzero

private theorem eval_clearedDifference_at_node
    {lambda : Fin 4 → ℝ} (hlambda : Function.Injective lambda)
    (x : Weights) (i : Fin 4) :
    (clearedDifference lambda hlambda x).eval (lambda i) = 0 := by
  have hnode := sub_rho_mul_consecutive_P_eval hlambda x i
  simp only [clearedDifference, interpolationDifference, eval_sub, eval_mul,
    eval_X, eval_C, eval_smul, nodalQuartic_eval_node, smul_zero,
    sub_zero] at ⊢
  nlinarith

private theorem clearedDifference_eq_zero
    {lambda : Fin 4 → ℝ} (hlambda : Function.Injective lambda)
    (x : Weights) :
    clearedDifference lambda hlambda x = 0 := by
  apply cubic_eq_of_eval_eq hlambda
    (clearedDifference_natDegree_le lambda hlambda x) (by simp)
  intro i
  simpa using eval_clearedDifference_at_node hlambda x i

/-- Evaluation of the cleared four-root identity at `rho(x)`.  This form is
valid even when `rho(x)` is itself a node, since no value of the nodal
quartic is cancelled. -/
theorem height_mul_rho_T_sub_rho
    {lambda : Fin 4 → ℝ} (hlambda : Function.Injective lambda)
    (x : Weights) :
    H lambda (T lambda hlambda x) *
        (rho lambda (T lambda hlambda x) - rho lambda x) =
      alpha lambda hlambda x *
        (nodalQuartic lambda).eval (rho lambda x) := by
  have hpoly := clearedDifference_eq_zero hlambda x
  have heval := congrArg
    (Polynomial.eval (rho lambda x)) hpoly
  simp only [clearedDifference, eval_sub, eval_mul, eval_X, eval_C,
    eval_smul, sub_self, zero_mul, eval_zero] at heval
  simp only [smul_eq_mul] at heval
  nlinarith

/-- Exact scalar recurrence for the barycentric parameter. -/
theorem rho_T_sub_rho
    {lambda : Fin 4 → ℝ} (hlambda : Function.Injective lambda)
    (x : Weights) :
    rho lambda (T lambda hlambda x) - rho lambda x =
      alpha lambda hlambda x *
          (nodalQuartic lambda).eval (rho lambda x) /
        H lambda (T lambda hlambda x) := by
  apply (eq_div_iff (ne_of_gt (height_pos hlambda (T lambda hlambda x)))).2
  simpa [mul_comm] using height_mul_rho_T_sub_rho hlambda x

/-- Boundary-safe four-node interpolation identity for one exact update.
The scalar `alpha` is the actual cubic coefficient of the left-hand
difference, rather than a quotient involving `nodalQuartic(rho(x))`. -/
theorem interpolation_identity
    {lambda : Fin 4 → ℝ} (hlambda : Function.Injective lambda)
    (x : Weights) :
    (P lambda x).toPolynomial *
        (P lambda (T lambda hlambda x)).toPolynomial =
      nodalQuartic lambda + C (H lambda (T lambda hlambda x)) +
        alpha lambda hlambda x •
          dividedDifference lambda (rho lambda x) := by
  let y := T lambda hlambda x
  let r := rho lambda x
  let a := alpha lambda hlambda x
  let g := interpolationDifference lambda hlambda x
  have hzero := clearedDifference_eq_zero hlambda x
  simp only [clearedDifference, smul_eq_C_mul] at hzero
  have hbalance := height_mul_rho_T_sub_rho hlambda x
  have hconstant :
      H lambda y * (rho lambda x - rho lambda y) =
        -(a * (nodalQuartic lambda).eval r) := by
    dsimp only [y, r, a]
    nlinarith
  have hmul :
      (X - C r) * g =
        (X - C r) * (a • dividedDifference lambda r) := by
    calc
      (X - C r) * g =
          C a * nodalQuartic lambda +
            C (H lambda y * (rho lambda x - rho lambda y)) := by
        dsimp only [r, a, g, y]
        linear_combination hzero
      _ = C a *
          (nodalQuartic lambda -
            C ((nodalQuartic lambda).eval r)) := by
        rw [hconstant, C_neg, C_mul]
        ring
      _ = C a *
          ((X - C r) * dividedDifference lambda r) := by
        rw [X_sub_C_mul_dividedDifference]
      _ = (X - C r) * (a • dividedDifference lambda r) := by
        rw [smul_eq_C_mul]
        ring
  have hg : g = a • dividedDifference lambda r :=
    mul_left_cancel₀ (X_sub_C_ne_zero r) hmul
  dsimp only [g, a, r, interpolationDifference] at hg
  linear_combination hg

/-- Ordered-node form of the exact interpolation identity. -/
theorem interpolation_identity_of_strictMono
    {lambda : Fin 4 → ℝ} (hlambda : StrictMono lambda)
    (x : Weights) :
    (P lambda x).toPolynomial *
        (P lambda (T lambda hlambda.injective x)).toPolynomial =
      nodalQuartic lambda +
        C (H lambda (T lambda hlambda.injective x)) +
        alpha lambda hlambda.injective x •
          dividedDifference lambda (rho lambda x) :=
  interpolation_identity hlambda.injective x

/-- Two successive exact four-node interpolation identities give the
manuscript's shared-middle-factor recurrence. -/
theorem consecutive_sharedFactor_recurrence
    {lambda : Fin 4 → ℝ} (hlambda : Function.Injective lambda)
    (x : Weights) :
    alpha lambda hlambda (T lambda hlambda x) *
        remainderLinearCoeff (P lambda (T lambda hlambda x))
          (dividedDifference lambda
            (rho lambda (T lambda hlambda x))) =
      alpha lambda hlambda x *
        remainderLinearCoeff (P lambda (T lambda hlambda x))
          (dividedDifference lambda (rho lambda x)) := by
  exact sharedFactor_recurrence lambda
    (P lambda x)
    (P lambda (T lambda hlambda x))
    (P lambda (T lambda hlambda (T lambda hlambda x)))
    (H lambda (T lambda hlambda x))
    (H lambda (T lambda hlambda (T lambda hlambda x)))
    (alpha lambda hlambda x)
    (alpha lambda hlambda (T lambda hlambda x))
    (rho lambda x)
    (rho lambda (T lambda hlambda x))
    (interpolation_identity hlambda x)
    (interpolation_identity hlambda (T lambda hlambda x))

end

end FourNode
end Forsythe
