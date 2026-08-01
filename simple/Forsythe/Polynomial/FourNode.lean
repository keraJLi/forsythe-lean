import Forsythe.Polynomial.Quadratic
import Mathlib.Algebra.Polynomial.RingDivision

/-!
# Four-node polynomial identities

This file contains the polynomial algebra behind the four-node part of the
proof.  In particular, it records the nodal quartic, its divided difference,
the limiting remainder identities, and the shared-factor recurrence.
-/

set_option autoImplicit false

namespace Forsythe

open scoped BigOperators

noncomputable section

namespace FourNode

open Polynomial

/-- The monic quartic with the four prescribed nodes as roots. -/
def nodalQuartic (lambda : Fin 4 → ℝ) : ℝ[X] :=
  ∏ i : Fin 4, (X - C (lambda i))

/-- The polynomial divided difference `(Pi(z) - Pi(t)) / (z - t)`. -/
def dividedDifference (lambda : Fin 4 → ℝ) (t : ℝ) : ℝ[X] :=
  (nodalQuartic lambda - C ((nodalQuartic lambda).eval t)) /ₘ (X - C t)

/-- The coefficient of `z` in the remainder of `r` modulo the monic quadratic `f`. -/
def remainderLinearCoeff (f : MonicQuadratic) (r : ℝ[X]) : ℝ :=
  (r %ₘ f.toPolynomial).coeff 1

theorem nodalQuartic_monic (lambda : Fin 4 → ℝ) :
    (nodalQuartic lambda).Monic := by
  apply monic_prod_of_monic
  intro i hi
  exact monic_X_sub_C _

/-- Synthetic division reconstructs the numerator of the divided difference. -/
theorem X_sub_C_mul_dividedDifference (lambda : Fin 4 → ℝ) (t : ℝ) :
    (X - C t) * dividedDifference lambda t =
      nodalQuartic lambda - C ((nodalQuartic lambda).eval t) := by
  rw [dividedDifference, mul_divByMonic_eq_iff_isRoot]
  simp [IsRoot]

private theorem quadratic_sub_eval_factor (f : MonicQuadratic) (t : ℝ) :
    (X - C t) * (X + C (t + f.linearCoeff)) =
      f.toPolynomial - C (f.toPolynomial.eval t) := by
  rw [MonicQuadratic.eval]
  simp only [MonicQuadratic.toPolynomial]
  simp only [C_add, C_mul, C_pow]
  ring

private theorem dividedDifference_decomposition
    (lambda : Fin 4 → ℝ) (p q : MonicQuadratic) (H t : ℝ)
    (hfactor : p.toPolynomial * q.toPolynomial = nodalQuartic lambda + C H) :
    dividedDifference lambda t =
      q.toPolynomial * (X + C (t + p.linearCoeff)) +
        C (p.toPolynomial.eval t) * (X + C (t + q.linearCoeff)) := by
  apply mul_left_cancel₀ (X_sub_C_ne_zero t)
  rw [X_sub_C_mul_dividedDifference]
  have hfactorEval := congrArg (Polynomial.eval t) hfactor
  simp only [eval_mul, eval_add, eval_C] at hfactorEval
  calc
    nodalQuartic lambda - C ((nodalQuartic lambda).eval t) =
        p.toPolynomial * q.toPolynomial -
          C (p.toPolynomial.eval t * q.toPolynomial.eval t) := by
            rw [hfactor, hfactorEval]
            rw [C_add]
            ring
    _ = q.toPolynomial *
          (p.toPolynomial - C (p.toPolynomial.eval t)) +
        C (p.toPolynomial.eval t) *
          (q.toPolynomial - C (q.toPolynomial.eval t)) := by
            rw [C_mul]
            ring
    _ = (X - C t) *
        (q.toPolynomial * (X + C (t + p.linearCoeff)) +
          C (p.toPolynomial.eval t) * (X + C (t + q.linearCoeff))) := by
            rw [← quadratic_sub_eval_factor p t,
              ← quadratic_sub_eval_factor q t]
            ring

private theorem degree_quadratic (f : MonicQuadratic) :
    f.toPolynomial.degree = 2 := by
  have hle : f.toPolynomial.natDegree ≤ 2 := by
    rw [MonicQuadratic.toPolynomial]
    apply natDegree_add_le_of_degree_le
    · apply natDegree_add_le_of_degree_le
      · simp
      · simpa only [pow_one] using
          (natDegree_C_mul_X_pow_le f.linearCoeff 1).trans (by norm_num : 1 ≤ 2)
    · simp
  have hge : 2 ≤ f.toPolynomial.natDegree :=
    le_natDegree_of_ne_zero (by simp)
  have hdegree : f.toPolynomial.natDegree = 2 := le_antisymm hle hge
  rw [degree_eq_natDegree (MonicQuadratic.monic f).ne_zero, hdegree]
  norm_num

private theorem degree_scaled_linear_lt_quadratic
    (f : MonicQuadratic) (a b : ℝ) :
    degree (C a * (X + C b)) < degree f.toPolynomial := by
  rw [degree_quadratic]
  calc
    degree (C a * (X + C b)) ≤ 1 := by compute_degree
    _ < (2 : WithBot ℕ) := by norm_num

private theorem scaled_linear_mod_quadratic
    (f : MonicQuadratic) (a b : ℝ) :
    (C a * (X + C b)) %ₘ f.toPolynomial = C a * (X + C b) := by
  exact (modByMonic_eq_self_iff (MonicQuadratic.monic f)).2
    (degree_scaled_linear_lt_quadratic f a b)

private theorem constant_mod_quadratic (f : MonicQuadratic) (a : ℝ) :
    C a %ₘ f.toPolynomial = C a := by
  apply (modByMonic_eq_self_iff (MonicQuadratic.monic f)).2
  rw [degree_quadratic]
  exact lt_of_le_of_lt (degree_C_le : degree (C a : ℝ[X]) ≤ 0) (by norm_num)

private theorem product_mod_right_quadratic
    (p q : MonicQuadratic) :
    (p.toPolynomial * q.toPolynomial) %ₘ q.toPolynomial = 0 := by
  apply (modByMonic_eq_zero_iff_dvd (MonicQuadratic.monic q)).2
  exact dvd_mul_left _ _

private theorem product_mod_left_quadratic
    (p q : MonicQuadratic) :
    (p.toPolynomial * q.toPolynomial) %ₘ p.toPolynomial = 0 := by
  simpa [mul_comm] using product_mod_right_quadratic q p

private theorem coeff_one_scaled_linear (a b : ℝ) :
    (C a * (X + C b)).coeff 1 = a := by
  simp

private theorem coeff_one_interpolation_mod
    (lambda : Fin 4 → ℝ) (f : MonicQuadratic) (K alpha rho : ℝ) :
    ((nodalQuartic lambda + C K + alpha • dividedDifference lambda rho) %ₘ
        f.toPolynomial).coeff 1 =
      (nodalQuartic lambda %ₘ f.toPolynomial).coeff 1 +
        alpha * remainderLinearCoeff f (dividedDifference lambda rho) := by
  rw [add_modByMonic, add_modByMonic, constant_mod_quadratic,
    smul_modByMonic]
  simp [remainderLinearCoeff]

/-- On a limiting factorization `p*q = Pi + H`, reduction of `D_t` modulo `q`
has linear coefficient `p(t)`. -/
theorem remainderLinearCoeff_dividedDifference_right
    (lambda : Fin 4 → ℝ) (p q : MonicQuadratic) (H t : ℝ)
    (hfactor : p.toPolynomial * q.toPolynomial = nodalQuartic lambda + C H) :
    remainderLinearCoeff q (dividedDifference lambda t) = p.toPolynomial.eval t := by
  have hdecomp := dividedDifference_decomposition lambda p q H t hfactor
  have hmod :
      dividedDifference lambda t %ₘ q.toPolynomial =
        (C (p.toPolynomial.eval t) * (X + C (t + q.linearCoeff))) %ₘ
          q.toPolynomial := by
    apply modByMonic_eq_of_dvd_sub (MonicQuadratic.monic q)
    rw [hdecomp]
    refine ⟨X + C (t + p.linearCoeff), ?_⟩
    ring
  rw [remainderLinearCoeff, hmod,
    scaled_linear_mod_quadratic q (p.toPolynomial.eval t) (t + q.linearCoeff)]
  exact coeff_one_scaled_linear (p.toPolynomial.eval t) (t + q.linearCoeff)

/-- The symmetric limiting remainder identity. -/
theorem remainderLinearCoeff_dividedDifference_left
    (lambda : Fin 4 → ℝ) (p q : MonicQuadratic) (H t : ℝ)
    (hfactor : p.toPolynomial * q.toPolynomial = nodalQuartic lambda + C H) :
    remainderLinearCoeff p (dividedDifference lambda t) = q.toPolynomial.eval t := by
  apply remainderLinearCoeff_dividedDifference_right lambda q p H t
  simpa [mul_comm] using hfactor

/-- Two consecutive interpolation identities sharing their middle monic
quadratic imply the scalar shared-factor recurrence. -/
theorem sharedFactor_recurrence
    (lambda : Fin 4 → ℝ) (p₀ p₁ p₂ : MonicQuadratic)
    (K₁ K₂ alpha₀ alpha₁ rho₀ rho₁ : ℝ)
    (h₀ : p₀.toPolynomial * p₁.toPolynomial =
      nodalQuartic lambda + C K₁ + alpha₀ • dividedDifference lambda rho₀)
    (h₁ : p₁.toPolynomial * p₂.toPolynomial =
      nodalQuartic lambda + C K₂ + alpha₁ • dividedDifference lambda rho₁) :
    alpha₁ * remainderLinearCoeff p₁ (dividedDifference lambda rho₁) =
      alpha₀ * remainderLinearCoeff p₁ (dividedDifference lambda rho₀) := by
  have hm₀ := congrArg (fun r : ℝ[X] => r %ₘ p₁.toPolynomial) h₀
  have hm₁ := congrArg (fun r : ℝ[X] => r %ₘ p₁.toPolynomial) h₁
  rw [product_mod_right_quadratic] at hm₀
  rw [product_mod_left_quadratic] at hm₁
  have hc₀ := congrArg (fun r : ℝ[X] => r.coeff 1) hm₀
  have hc₁ := congrArg (fun r : ℝ[X] => r.coeff 1) hm₁
  rw [coeff_one_interpolation_mod] at hc₀ hc₁
  simp only [coeff_zero] at hc₀ hc₁
  linarith

end FourNode
end
end Forsythe
