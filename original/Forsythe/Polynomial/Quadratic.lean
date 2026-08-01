import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic

/-!
# Monic quadratic polynomials

The Arnoldi factors in the paper are monic quadratics.  We store only their
two free coefficients; this gives a concrete coefficient norm and avoids
quotienting a fixed-degree polynomial subspace.
-/

set_option autoImplicit false

namespace Forsythe

/-- A monic quadratic `z² + linearCoeff * z + constantCoeff`. -/
@[ext]
structure MonicQuadratic where
  /-- Coefficient of `z`. -/
  linearCoeff : ℝ
  /-- Constant coefficient. -/
  constantCoeff : ℝ

namespace MonicQuadratic

/-- The polynomial represented by a `MonicQuadratic`. -/
noncomputable def toPolynomial (p : MonicQuadratic) : Polynomial ℝ :=
  Polynomial.X ^ 2 + Polynomial.C p.linearCoeff * Polynomial.X +
    Polynomial.C p.constantCoeff

noncomputable instance : Coe MonicQuadratic (Polynomial ℝ) := ⟨toPolynomial⟩

@[simp]
theorem coeff_zero (p : MonicQuadratic) : p.toPolynomial.coeff 0 = p.constantCoeff := by
  simp [toPolynomial]

@[simp]
theorem coeff_one (p : MonicQuadratic) : p.toPolynomial.coeff 1 = p.linearCoeff := by
  simp [toPolynomial]

@[simp]
theorem coeff_two (p : MonicQuadratic) : p.toPolynomial.coeff 2 = 1 := by
  simp [toPolynomial]

@[simp]
theorem eval (p : MonicQuadratic) (x : ℝ) :
    p.toPolynomial.eval x = x ^ 2 + p.linearCoeff * x + p.constantCoeff := by
  simp [toPolynomial]

theorem monic (p : MonicQuadratic) : p.toPolynomial.Monic := by
  exact (Polynomial.isMonicOfDegree_add_add_two
    p.linearCoeff p.constantCoeff).monic

theorem toPolynomial_injective : Function.Injective toPolynomial := by
  intro p q hpq
  apply MonicQuadratic.ext
  · have h := congrArg (fun f : Polynomial ℝ => f.coeff 1) hpq
    simpa using h
  · have h := congrArg (fun f : Polynomial ℝ => f.coeff 0) hpq
    simpa using h

@[simp]
theorem toPolynomial_inj {p q : MonicQuadratic} :
    p.toPolynomial = q.toPolynomial ↔ p = q :=
  toPolynomial_injective.eq_iff

/-- The two free coefficients, ordered as `(linear, constant)`. -/
def coeffPair (p : MonicQuadratic) : ℝ × ℝ :=
  (p.linearCoeff, p.constantCoeff)

/-- The fixed coefficient distance used in the factor-variation estimate. -/
def coeffDist (p q : MonicQuadratic) : ℝ :=
  ‖p.coeffPair - q.coeffPair‖

@[simp]
theorem coeffDist_self (p : MonicQuadratic) : p.coeffDist p = 0 := by
  simp [coeffDist]

theorem coeffDist_nonneg (p q : MonicQuadratic) : 0 ≤ p.coeffDist q :=
  norm_nonneg _

end MonicQuadratic
end Forsythe
