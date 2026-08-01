import Forsythe.Polynomial.FourNode

/-!
# Explicit continuity of the four-node remainder coefficient

The shared-factor recurrence uses the coefficient of `z` in the remainder of
the synthetic quotient `D_t` modulo a monic quadratic.  Here that coefficient
is written as an explicit quadratic polynomial in `t`.  The resulting exact
difference identities give concrete Lipschitz estimates without appealing to
an abstract finite-dimensional continuity argument.
-/

set_option autoImplicit false

namespace Forsythe
namespace FourNode

open Filter Polynomial Topology

noncomputable section

/-- The first elementary symmetric coefficient of four nodes. -/
def nodeElementaryOne (lambda : Fin 4 → ℝ) : ℝ :=
  lambda 0 + lambda 1 + lambda 2 + lambda 3

/-- The second elementary symmetric coefficient of four nodes. -/
def nodeElementaryTwo (lambda : Fin 4 → ℝ) : ℝ :=
  lambda 0 * lambda 1 + lambda 0 * lambda 2 + lambda 0 * lambda 3 +
    lambda 1 * lambda 2 + lambda 1 * lambda 3 + lambda 2 * lambda 3

/-- The third elementary symmetric coefficient of four nodes. -/
def nodeElementaryThree (lambda : Fin 4 → ℝ) : ℝ :=
  lambda 0 * lambda 1 * lambda 2 + lambda 0 * lambda 1 * lambda 3 +
    lambda 0 * lambda 2 * lambda 3 + lambda 1 * lambda 2 * lambda 3

/-- The fourth elementary symmetric coefficient of four nodes. -/
def nodeElementaryFour (lambda : Fin 4 → ℝ) : ℝ :=
  lambda 0 * lambda 1 * lambda 2 * lambda 3

/-- Expansion of the nodal quartic in elementary symmetric coefficients. -/
theorem nodalQuartic_eq_elementary (lambda : Fin 4 → ℝ) :
    nodalQuartic lambda =
      X ^ 4 - C (nodeElementaryOne lambda) * X ^ 3 +
        C (nodeElementaryTwo lambda) * X ^ 2 -
          C (nodeElementaryThree lambda) * X + C (nodeElementaryFour lambda) := by
  simp [nodalQuartic, nodeElementaryOne, nodeElementaryTwo,
    nodeElementaryThree, nodeElementaryFour, Fin.prod_univ_succ]
  ring

/-- Synthetic division of the nodal quartic, with all coefficients exposed. -/
theorem dividedDifference_eq_elementary (lambda : Fin 4 → ℝ) (t : ℝ) :
    dividedDifference lambda t =
      X ^ 3 + C (t - nodeElementaryOne lambda) * X ^ 2 +
        C (t ^ 2 - nodeElementaryOne lambda * t + nodeElementaryTwo lambda) * X +
          C (t ^ 3 - nodeElementaryOne lambda * t ^ 2 +
            nodeElementaryTwo lambda * t - nodeElementaryThree lambda) := by
  apply mul_left_cancel₀ (X_sub_C_ne_zero t)
  rw [X_sub_C_mul_dividedDifference, nodalQuartic_eq_elementary]
  simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C, C_add, C_sub,
    C_mul, C_pow]
  ring

private theorem linearPolynomial_mod_monicQuadratic
    (f : MonicQuadratic) (a b : ℝ) :
    (C a * X + C b) %ₘ f.toPolynomial = C a * X + C b := by
  apply (modByMonic_eq_self_iff (MonicQuadratic.monic f)).2
  have hdegree : degree (C a * X + C b) ≤ 1 := by
    compute_degree
  have hfdegree : degree f.toPolynomial = 2 := by
    rw [MonicQuadratic.toPolynomial]
    compute_degree <;> norm_num
  rw [hfdegree]
  exact hdegree.trans_lt (by norm_num)

/-- Explicit formula for the linear remainder coefficient.  Only the first
two elementary node coefficients occur:
`ell_f(t) = t² - (e₁+u)t + e₂+u²-v+e₁u`, where
`f(z)=z²+uz+v`. -/
theorem remainderLinearCoeff_dividedDifference_eq
    (lambda : Fin 4 → ℝ) (f : MonicQuadratic) (t : ℝ) :
    remainderLinearCoeff f (dividedDifference lambda t) =
      t ^ 2 - (nodeElementaryOne lambda + f.linearCoeff) * t +
        nodeElementaryTwo lambda + f.linearCoeff ^ 2 - f.constantCoeff +
          nodeElementaryOne lambda * f.linearCoeff := by
  let ell : ℝ :=
    t ^ 2 - (nodeElementaryOne lambda + f.linearCoeff) * t +
      nodeElementaryTwo lambda + f.linearCoeff ^ 2 - f.constantCoeff +
        nodeElementaryOne lambda * f.linearCoeff
  let c : ℝ :=
    t ^ 3 - nodeElementaryOne lambda * t ^ 2 +
      nodeElementaryTwo lambda * t - nodeElementaryThree lambda -
        f.constantCoeff * (t - nodeElementaryOne lambda - f.linearCoeff)
  have hmod :
      dividedDifference lambda t %ₘ f.toPolynomial =
        (C ell * X + C c) %ₘ f.toPolynomial := by
    apply modByMonic_eq_of_dvd_sub (MonicQuadratic.monic f)
    refine ⟨X + C (t - nodeElementaryOne lambda - f.linearCoeff), ?_⟩
    rw [dividedDifference_eq_elementary, MonicQuadratic.toPolynomial]
    dsimp only [ell, c]
    simp only [C_add, C_sub, C_mul, C_pow]
    ring
  rw [remainderLinearCoeff, hmod, linearPolynomial_mod_monicQuadratic]
  change (C ell * X + C c).coeff 1 = _
  have hcoeff : (C ell * X + C c).coeff 1 = ell := by simp
  rw [hcoeff]

/-- Exact variation in the synthetic-division parameter with the quadratic
factor fixed. -/
theorem remainderLinearCoeff_dividedDifference_sub_sameQuadratic
    (lambda : Fin 4 → ℝ) (f : MonicQuadratic) (t s : ℝ) :
    remainderLinearCoeff f (dividedDifference lambda t) -
        remainderLinearCoeff f (dividedDifference lambda s) =
      (t - s) * (t + s - nodeElementaryOne lambda - f.linearCoeff) := by
  rw [remainderLinearCoeff_dividedDifference_eq,
    remainderLinearCoeff_dividedDifference_eq]
  ring

/-- Exact variation in the two free coefficients with the parameter fixed. -/
theorem remainderLinearCoeff_dividedDifference_sub_sameParameter
    (lambda : Fin 4 → ℝ) (f g : MonicQuadratic) (t : ℝ) :
    remainderLinearCoeff f (dividedDifference lambda t) -
        remainderLinearCoeff g (dividedDifference lambda t) =
      (f.linearCoeff - g.linearCoeff) *
          (f.linearCoeff + g.linearCoeff + nodeElementaryOne lambda - t) -
        (f.constantCoeff - g.constantCoeff) := by
  rw [remainderLinearCoeff_dividedDifference_eq,
    remainderLinearCoeff_dividedDifference_eq]
  ring

/-- Joint exact variation formula, split into parameter and coefficient
increments. -/
theorem remainderLinearCoeff_dividedDifference_sub
    (lambda : Fin 4 → ℝ) (f g : MonicQuadratic) (t s : ℝ) :
    remainderLinearCoeff f (dividedDifference lambda t) -
        remainderLinearCoeff g (dividedDifference lambda s) =
      (t - s) * (t + s - nodeElementaryOne lambda - f.linearCoeff) +
        (f.linearCoeff - g.linearCoeff) *
          (f.linearCoeff + g.linearCoeff + nodeElementaryOne lambda - s) -
            (f.constantCoeff - g.constantCoeff) := by
  rw [remainderLinearCoeff_dividedDifference_eq,
    remainderLinearCoeff_dividedDifference_eq]
  ring

/-- A free linear-coefficient difference is bounded by the fixed product
norm on coefficient pairs. -/
theorem abs_linearCoeff_sub_le_coeffDist
    (f g : MonicQuadratic) :
    |f.linearCoeff - g.linearCoeff| ≤ f.coeffDist g := by
  rw [MonicQuadratic.coeffDist, MonicQuadratic.coeffPair, Prod.norm_def,
    Real.norm_eq_abs, Real.norm_eq_abs]
  exact le_max_left _ _

/-- A free constant-coefficient difference is bounded by the fixed product
norm on coefficient pairs. -/
theorem abs_constantCoeff_sub_le_coeffDist
    (f g : MonicQuadratic) :
    |f.constantCoeff - g.constantCoeff| ≤ f.coeffDist g := by
  rw [MonicQuadratic.coeffDist, MonicQuadratic.coeffPair, Prod.norm_def,
    Real.norm_eq_abs, Real.norm_eq_abs]
  exact le_max_right _ _

/-- Global joint estimate before imposing compact parameter and coefficient
bounds. -/
theorem abs_remainderLinearCoeff_dividedDifference_sub_le
    (lambda : Fin 4 → ℝ) (f g : MonicQuadratic) (t s : ℝ) :
    |remainderLinearCoeff f (dividedDifference lambda t) -
        remainderLinearCoeff g (dividedDifference lambda s)| ≤
      |t - s| *
          (|t| + |s| + |nodeElementaryOne lambda| + |f.linearCoeff|) +
        |f.linearCoeff - g.linearCoeff| *
          (|f.linearCoeff| + |g.linearCoeff| +
            |nodeElementaryOne lambda| + |s|) +
          |f.constantCoeff - g.constantCoeff| := by
  have hfirst :
      |t + s - nodeElementaryOne lambda - f.linearCoeff| ≤
        |t| + |s| + |nodeElementaryOne lambda| + |f.linearCoeff| := by
    calc
      |t + s - nodeElementaryOne lambda - f.linearCoeff| ≤
          |t + s - nodeElementaryOne lambda| + |f.linearCoeff| := abs_sub _ _
      _ ≤ (|t + s| + |nodeElementaryOne lambda|) + |f.linearCoeff| := by
        gcongr
        exact abs_sub _ _
      _ ≤ ((|t| + |s|) + |nodeElementaryOne lambda|) + |f.linearCoeff| := by
        gcongr
        exact abs_add_le _ _
      _ = |t| + |s| + |nodeElementaryOne lambda| + |f.linearCoeff| := by ring
  have hsecond :
      |f.linearCoeff + g.linearCoeff + nodeElementaryOne lambda - s| ≤
        |f.linearCoeff| + |g.linearCoeff| +
          |nodeElementaryOne lambda| + |s| := by
    calc
      |f.linearCoeff + g.linearCoeff + nodeElementaryOne lambda - s| ≤
          |f.linearCoeff + g.linearCoeff + nodeElementaryOne lambda| + |s| :=
        abs_sub _ _
      _ ≤ (|f.linearCoeff + g.linearCoeff| +
          |nodeElementaryOne lambda|) + |s| := by
        gcongr
        exact abs_add_le _ _
      _ ≤ ((|f.linearCoeff| + |g.linearCoeff|) +
          |nodeElementaryOne lambda|) + |s| := by
        gcongr
        exact abs_add_le _ _
      _ = |f.linearCoeff| + |g.linearCoeff| +
          |nodeElementaryOne lambda| + |s| := by ring
  rw [remainderLinearCoeff_dividedDifference_sub]
  calc
    |(t - s) * (t + s - nodeElementaryOne lambda - f.linearCoeff) +
          (f.linearCoeff - g.linearCoeff) *
            (f.linearCoeff + g.linearCoeff + nodeElementaryOne lambda - s) -
        (f.constantCoeff - g.constantCoeff)| ≤
      |(t - s) * (t + s - nodeElementaryOne lambda - f.linearCoeff) +
          (f.linearCoeff - g.linearCoeff) *
            (f.linearCoeff + g.linearCoeff + nodeElementaryOne lambda - s)| +
        |f.constantCoeff - g.constantCoeff| := abs_sub _ _
    _ ≤
      (|(t - s) * (t + s - nodeElementaryOne lambda - f.linearCoeff)| +
        |(f.linearCoeff - g.linearCoeff) *
          (f.linearCoeff + g.linearCoeff + nodeElementaryOne lambda - s)|) +
        |f.constantCoeff - g.constantCoeff| := by
      gcongr
      exact abs_add_le _ _
    _ = |t - s| * |t + s - nodeElementaryOne lambda - f.linearCoeff| +
        |f.linearCoeff - g.linearCoeff| *
          |f.linearCoeff + g.linearCoeff + nodeElementaryOne lambda - s| +
        |f.constantCoeff - g.constantCoeff| := by rw [abs_mul, abs_mul]
    _ ≤
      |t - s| *
          (|t| + |s| + |nodeElementaryOne lambda| + |f.linearCoeff|) +
        |f.linearCoeff - g.linearCoeff| *
          (|f.linearCoeff| + |g.linearCoeff| +
            |nodeElementaryOne lambda| + |s|) +
          |f.constantCoeff - g.constantCoeff| := by
      gcongr

/-- Lipschitz constant for varying the synthetic-division parameter on
`[-R,R]`, when the relevant linear coefficient has absolute value at most
`M`. -/
def remainderParameterLipschitzConstant
    (lambda : Fin 4 → ℝ) (R M : ℝ) : ℝ :=
  2 * R + |nodeElementaryOne lambda| + M

/-- Lipschitz constant for varying the free coefficient pair on `[-R,R]`,
when both linear coefficients have absolute value at most `M`. -/
def remainderCoefficientLipschitzConstant
    (lambda : Fin 4 → ℝ) (R M : ℝ) : ℝ :=
  2 * M + |nodeElementaryOne lambda| + R + 1

theorem remainderParameterLipschitzConstant_nonneg
    (lambda : Fin 4 → ℝ) {R M : ℝ} (hR : 0 ≤ R) (hM : 0 ≤ M) :
    0 ≤ remainderParameterLipschitzConstant lambda R M := by
  dsimp only [remainderParameterLipschitzConstant]
  positivity

theorem remainderCoefficientLipschitzConstant_nonneg
    (lambda : Fin 4 → ℝ) {R M : ℝ} (hR : 0 ≤ R) (hM : 0 ≤ M) :
    0 ≤ remainderCoefficientLipschitzConstant lambda R M := by
  dsimp only [remainderCoefficientLipschitzConstant]
  positivity

/-- Joint Lipschitz estimate on a compact parameter interval and a bounded
set of free quadratic coefficients. -/
theorem abs_remainderLinearCoeff_dividedDifference_sub_le_of_bounds
    (lambda : Fin 4 → ℝ) (f g : MonicQuadratic) (t s : ℝ) {R M : ℝ}
    (ht : |t| ≤ R) (hs : |s| ≤ R)
    (hf : |f.linearCoeff| ≤ M) (hg : |g.linearCoeff| ≤ M) :
    |remainderLinearCoeff f (dividedDifference lambda t) -
        remainderLinearCoeff g (dividedDifference lambda s)| ≤
      remainderParameterLipschitzConstant lambda R M * |t - s| +
        remainderCoefficientLipschitzConstant lambda R M * f.coeffDist g := by
  have hparameter :
      |t| + |s| + |nodeElementaryOne lambda| + |f.linearCoeff| ≤
        remainderParameterLipschitzConstant lambda R M := by
    dsimp only [remainderParameterLipschitzConstant]
    linarith
  have hcoefficient :
      |f.linearCoeff| + |g.linearCoeff| +
          |nodeElementaryOne lambda| + |s| ≤
        2 * M + |nodeElementaryOne lambda| + R := by
    linarith
  calc
    |remainderLinearCoeff f (dividedDifference lambda t) -
        remainderLinearCoeff g (dividedDifference lambda s)| ≤
      |t - s| *
          (|t| + |s| + |nodeElementaryOne lambda| + |f.linearCoeff|) +
        |f.linearCoeff - g.linearCoeff| *
          (|f.linearCoeff| + |g.linearCoeff| +
            |nodeElementaryOne lambda| + |s|) +
          |f.constantCoeff - g.constantCoeff| :=
      abs_remainderLinearCoeff_dividedDifference_sub_le lambda f g t s
    _ ≤ |t - s| * remainderParameterLipschitzConstant lambda R M +
        f.coeffDist g *
          (2 * M + |nodeElementaryOne lambda| + R) + f.coeffDist g := by
      gcongr
      · exact MonicQuadratic.coeffDist_nonneg f g
      · exact abs_linearCoeff_sub_le_coeffDist f g
      · exact abs_constantCoeff_sub_le_coeffDist f g
    _ = remainderParameterLipschitzConstant lambda R M * |t - s| +
        remainderCoefficientLipschitzConstant lambda R M * f.coeffDist g := by
      dsimp only [remainderCoefficientLipschitzConstant]
      ring

/-- Uniform coefficient-pair Lipschitz estimate on the compact interval
`[-R,R]`. -/
theorem abs_remainderLinearCoeff_dividedDifference_sub_sameParameter_le_of_bounds
    (lambda : Fin 4 → ℝ) (f g : MonicQuadratic) (t : ℝ) {R M : ℝ}
    (ht : |t| ≤ R)
    (hf : |f.linearCoeff| ≤ M) (hg : |g.linearCoeff| ≤ M) :
    |remainderLinearCoeff f (dividedDifference lambda t) -
        remainderLinearCoeff g (dividedDifference lambda t)| ≤
      remainderCoefficientLipschitzConstant lambda R M * f.coeffDist g := by
  have h := abs_remainderLinearCoeff_dividedDifference_sub_le_of_bounds
    lambda f g t t ht ht hf hg
  simpa using h

/-- The preceding estimate yields uniform convergence on `[-R,R]`, written
in an explicit epsilon/eventually form that is convenient for later tail
arguments. -/
theorem eventually_uniform_remainderLinearCoeff_dividedDifference_of_coeffDist_tendsto_zero
    (lambda : Fin 4 → ℝ) (f : ℕ → MonicQuadratic) (g : MonicQuadratic)
    {R M : ℝ}
    (hf : ∀ k, |(f k).linearCoeff| ≤ M) (hg : |g.linearCoeff| ≤ M)
    (hfg : Tendsto (fun k ↦ (f k).coeffDist g) atTop (nhds 0)) :
    ∀ ε, 0 < ε → ∀ᶠ k in atTop, ∀ t, |t| ≤ R →
      |remainderLinearCoeff (f k) (dividedDifference lambda t) -
        remainderLinearCoeff g (dividedDifference lambda t)| < ε := by
  intro ε hε
  let Cₗ := remainderCoefficientLipschitzConstant lambda R M
  have hscaled :
      Tendsto (fun k ↦ Cₗ * (f k).coeffDist g) atTop (nhds 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hfg
  filter_upwards [(tendsto_order.1 hscaled).2 ε hε] with k hk
  intro t ht
  exact (abs_remainderLinearCoeff_dividedDifference_sub_sameParameter_le_of_bounds
    lambda (f k) g t ht (hf k) hg).trans_lt hk

/-- Uniform comparison with the limiting identity `ell_q(t)=p(t)` on a
factorization of the nodal quartic. -/
theorem abs_remainderLinearCoeff_dividedDifference_sub_eval_le_of_factorization
    (lambda : Fin 4 → ℝ) (p q f : MonicQuadratic) (H t : ℝ) {R M : ℝ}
    (hfactor : p.toPolynomial * q.toPolynomial = nodalQuartic lambda + C H)
    (ht : |t| ≤ R) (hf : |f.linearCoeff| ≤ M)
    (hq : |q.linearCoeff| ≤ M) :
    |remainderLinearCoeff f (dividedDifference lambda t) -
        p.toPolynomial.eval t| ≤
      remainderCoefficientLipschitzConstant lambda R M * f.coeffDist q := by
  rw [← remainderLinearCoeff_dividedDifference_right lambda p q H t hfactor]
  exact abs_remainderLinearCoeff_dividedDifference_sub_sameParameter_le_of_bounds
    lambda f q t ht hf hq

/-- Symmetric uniform comparison with `ell_p(t)=q(t)`. -/
theorem abs_remainderLinearCoeff_dividedDifference_sub_eval_le_of_factorization_left
    (lambda : Fin 4 → ℝ) (p q f : MonicQuadratic) (H t : ℝ) {R M : ℝ}
    (hfactor : p.toPolynomial * q.toPolynomial = nodalQuartic lambda + C H)
    (ht : |t| ≤ R) (hf : |f.linearCoeff| ≤ M)
    (hp : |p.linearCoeff| ≤ M) :
    |remainderLinearCoeff f (dividedDifference lambda t) -
        q.toPolynomial.eval t| ≤
      remainderCoefficientLipschitzConstant lambda R M * f.coeffDist p := by
  rw [← remainderLinearCoeff_dividedDifference_left lambda p q H t hfactor]
  exact abs_remainderLinearCoeff_dividedDifference_sub_sameParameter_le_of_bounds
    lambda f p t ht hf hp

end

end FourNode
end Forsythe
