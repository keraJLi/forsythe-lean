import Forsythe.Polynomial.Quadratic

/-!
# Regression tests for monic quadratics

These compile-time examples pin the coefficient convention
`z² + linearCoeff * z + constantCoeff` using exact rational data.
-/

set_option autoImplicit false

namespace ForsytheTest

open Forsythe

/-- The exact test polynomial `(z - 1) (z - 1/2)`. -/
private noncomputable def rationalQuadratic : MonicQuadratic where
  linearCoeff := -(3 / 2 : ℝ)
  constantCoeff := 1 / 2

example : rationalQuadratic.linearCoeff = -(3 / 2 : ℝ) := by
  rfl

example : rationalQuadratic.constantCoeff = (1 / 2 : ℝ) := by
  rfl

example : rationalQuadratic.coeffPair = (-(3 / 2 : ℝ), (1 / 2 : ℝ)) := by
  rfl

example : rationalQuadratic.toPolynomial.coeff 0 = (1 / 2 : ℝ) := by
  simp [rationalQuadratic]

example : rationalQuadratic.toPolynomial.coeff 1 = -(3 / 2 : ℝ) := by
  simp [rationalQuadratic]

example : rationalQuadratic.toPolynomial.coeff 2 = 1 := by
  simp

example : rationalQuadratic.toPolynomial.eval (1 : ℝ) = 0 := by
  norm_num [MonicQuadratic.eval, rationalQuadratic]

example : rationalQuadratic.toPolynomial.eval (1 / 2 : ℝ) = 0 := by
  norm_num [MonicQuadratic.eval, rationalQuadratic]

example : rationalQuadratic.toPolynomial.eval (2 : ℝ) = 3 / 2 := by
  norm_num [MonicQuadratic.eval, rationalQuadratic]

example : rationalQuadratic.toPolynomial.Monic := by
  exact rationalQuadratic.monic

example (p q : MonicQuadratic) (h : p.toPolynomial = q.toPolynomial) : p = q := by
  exact MonicQuadratic.toPolynomial_injective h

end ForsytheTest
