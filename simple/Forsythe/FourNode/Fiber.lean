import Forsythe.FourNode.Rho

/-!
# Minimal limiting four-node fibers

Only the coordinate formula and the consequences used by the convergence
proof are retained here.  A limiting fiber is represented directly by its
rational weights, without packaging a separate curve topology or root data.
-/

set_option autoImplicit false

namespace Forsythe
namespace FourNode

open Polynomial Set
open scoped BigOperators

noncomputable section

private theorem nodalQuartic_eval_node (lambda : Fin 4 → ℝ) (i : Fin 4) :
    (nodalQuartic lambda).eval (lambda i) = 0 := by
  rw [nodalQuartic, eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)

/-- At every node, the limiting factors have product `tau²`. -/
theorem factor_eval_mul_eq_tau_sq
    {lambda : Fin 4 → ℝ} {tau : ℝ} {p q : MonicQuadratic}
    (hfactor : p.toPolynomial * q.toPolynomial =
      nodalQuartic lambda + C (tau ^ 2)) (i : Fin 4) :
    p.toPolynomial.eval (lambda i) * q.toPolynomial.eval (lambda i) = tau ^ 2 := by
  have h := congrArg (Polynomial.eval (lambda i)) hfactor
  simpa [eval_mul, eval_add, nodalQuartic_eval_node] using h

theorem factor_eval_ne_zero
    {lambda : Fin 4 → ℝ} {tau : ℝ} (htau : 0 < tau)
    {p q : MonicQuadratic}
    (hfactor : p.toPolynomial * q.toPolynomial =
      nodalQuartic lambda + C (tau ^ 2)) (i : Fin 4) :
    p.toPolynomial.eval (lambda i) ≠ 0 ∧
      q.toPolynomial.eval (lambda i) ≠ 0 := by
  have hprod := factor_eval_mul_eq_tau_sq hfactor i
  have hsq : tau ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt htau)
  exact mul_ne_zero_iff.mp (hprod.symm ▸ hsq)

/-- At every active node the two limiting factors have the same strict sign. -/
theorem factor_eval_same_sign
    {lambda : Fin 4 → ℝ} {tau : ℝ} (htau : 0 < tau)
    {p q : MonicQuadratic}
    (hfactor : p.toPolynomial * q.toPolynomial =
      nodalQuartic lambda + C (tau ^ 2)) (i : Fin 4) :
    (0 < p.toPolynomial.eval (lambda i) ∧
        0 < q.toPolynomial.eval (lambda i)) ∨
      (p.toPolynomial.eval (lambda i) < 0 ∧
        q.toPolynomial.eval (lambda i) < 0) := by
  rw [← mul_pos_iff]
  rw [factor_eval_mul_eq_tau_sq hfactor i]
  positivity

/-- Candidate weights for the fiber whose Arnoldi polynomial is `p`. -/
def fiberWeight (lambda : Fin 4 → ℝ) (tau rho : ℝ)
    (p : MonicQuadratic) (i : Fin 4) : ℝ :=
  tau ^ 2 * (lambda i - rho) /
    (E lambda i * p.toPolynomial.eval (lambda i))

theorem fiberWeight_eq_zero_iff
    {lambda : Fin 4 → ℝ} (hlambda : Function.Injective lambda)
    {tau : ℝ} (htau : 0 < tau) {rho : ℝ} {p q : MonicQuadratic}
    (hfactor : p.toPolynomial * q.toPolynomial =
      nodalQuartic lambda + C (tau ^ 2)) (i : Fin 4) :
    fiberWeight lambda tau rho p i = 0 ↔ lambda i = rho := by
  have hE := E_ne_zero hlambda i
  have hp := (factor_eval_ne_zero htau hfactor i).1
  have htauSq : tau ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt htau)
  rw [fiberWeight]
  simp only [div_eq_zero_iff, mul_eq_zero, htauSq, hE, hp, or_false, false_or,
    sub_eq_zero]

/-- Membership in a fixed positive fiber, independent of proof packaging. -/
def MemFiber (lambda : Fin 4 → ℝ) (tau rho : ℝ)
    (p : MonicQuadratic) (x : Weights) : Prop :=
  ∀ i, x i = fiberWeight lambda tau rho p i

/-- The positive `p`-fiber, already intersected with the four-node simplex. -/
def positiveFiber (lambda : Fin 4 → ℝ) (tau rho : ℝ)
    (p : MonicQuadratic) : Set Weights :=
  {x | MemFiber lambda tau rho p x}

theorem memFiber_weight_mul_eval
    {lambda : Fin 4 → ℝ} (hlambda : Function.Injective lambda)
    {tau : ℝ} (htau : 0 < tau) {rho : ℝ} {p q : MonicQuadratic}
    (hfactor : p.toPolynomial * q.toPolynomial =
      nodalQuartic lambda + C (tau ^ 2))
    {x : Weights} (hx : MemFiber lambda tau rho p x) (i : Fin 4) :
    x i * p.toPolynomial.eval (lambda i) =
      tau ^ 2 * (lambda i - rho) / E lambda i := by
  have hE := E_ne_zero hlambda i
  have hp := (factor_eval_ne_zero htau hfactor i).1
  rw [hx i, fiberWeight]
  field_simp [hE, hp]

private theorem weightedPolyInner_monic_one_fiber
    (lambda : Fin 4 → ℝ) (x : Weights) (p : MonicQuadratic) :
    weightedPolyInner lambda x p.toPolynomial 1 =
      weightedMoment lambda x 2 +
        p.linearCoeff * weightedMoment lambda x 1 +
          p.constantCoeff * weightedMoment lambda x 0 := by
  simp only [weightedPolyInner, MonicQuadratic.eval, eval_one, mul_one,
    weightedMoment, pow_zero, pow_one]
  calc
    ∑ i, x i * (lambda i ^ 2 + p.linearCoeff * lambda i + p.constantCoeff) =
        ∑ i, (x i * lambda i ^ 2 +
          p.linearCoeff * (x i * lambda i) + p.constantCoeff * x i) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = (∑ i, x i * lambda i ^ 2) +
        p.linearCoeff * (∑ i, x i * lambda i) +
          p.constantCoeff * (∑ i, x i) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      simp only [Finset.mul_sum]

private theorem weightedPolyInner_monic_X_fiber
    (lambda : Fin 4 → ℝ) (x : Weights) (p : MonicQuadratic) :
    weightedPolyInner lambda x p.toPolynomial X =
      weightedMoment lambda x 3 +
        p.linearCoeff * weightedMoment lambda x 2 +
          p.constantCoeff * weightedMoment lambda x 1 := by
  simp only [weightedPolyInner, MonicQuadratic.eval, eval_X, weightedMoment,
    pow_one]
  calc
    ∑ i, x i * (lambda i ^ 2 + p.linearCoeff * lambda i + p.constantCoeff) *
        lambda i =
      ∑ i, (x i * lambda i ^ 3 +
        p.linearCoeff * (x i * lambda i ^ 2) +
          p.constantCoeff * (x i * lambda i)) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = (∑ i, x i * lambda i ^ 3) +
        p.linearCoeff * (∑ i, x i * lambda i ^ 2) +
          p.constantCoeff * (∑ i, x i * lambda i) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      simp only [Finset.mul_sum]

/-- A monic quadratic satisfying the two weighted orthogonality equations is
the explicit Cramer-system polynomial `P_x`. -/
theorem eq_P_of_orthogonal
    {lambda : Fin 4 → ℝ} (hlambda : Function.Injective lambda)
    (x : Weights) (p : MonicQuadratic)
    (hone : weightedPolyInner lambda x p.toPolynomial 1 = 0)
    (hX : weightedPolyInner lambda x p.toPolynomial X = 0) :
    p = P lambda x := by
  rw [weightedPolyInner_monic_one_fiber] at hone
  rw [weightedPolyInner_monic_X_fiber] at hX
  have hdet := weightedMomentGramDet_ne_zero hlambda x
  apply MonicQuadratic.ext
  · change p.linearCoeff =
      (weightedMoment lambda x 1 * weightedMoment lambda x 2 -
        weightedMoment lambda x 0 * weightedMoment lambda x 3) /
          weightedMomentGramDet lambda x
    field_simp [hdet]
    rw [weightedMomentGramDet]
    linear_combination
      weightedMoment lambda x 0 * hX - weightedMoment lambda x 1 * hone
  · change p.constantCoeff =
      (weightedMoment lambda x 1 * weightedMoment lambda x 3 -
        weightedMoment lambda x 2 ^ 2) /
          weightedMomentGramDet lambda x
    field_simp [hdet]
    rw [weightedMomentGramDet]
    linear_combination
      weightedMoment lambda x 2 * hone - weightedMoment lambda x 1 * hX

end

end FourNode
end Forsythe
