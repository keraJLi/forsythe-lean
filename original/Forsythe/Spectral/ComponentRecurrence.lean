import Forsythe.Spectral.Stabilization
import Forsythe.Arnoldi.Orbit
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Scalar recurrences in grouped spectral coordinates

Each grouped eigenspace component is multiplied by the scalar value of the
current Arnoldi polynomial.  Squared component norms therefore satisfy the
weight recurrences used later in the finite-node and exterior arguments.
-/

set_option autoImplicit false

namespace Forsythe
namespace Spectral

open scoped BigOperators

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Squared norm of a grouped eigenspace component. -/
def weight (A : Module.End ℝ E) (hA : A.IsSymmetric) (v : E)
    (mu : A.Eigenvalues) : ℝ :=
  ‖component A hA v mu‖ ^ 2

/-- The exact scalar multiplying a grouped eigenspace component over two
Arnoldi steps. -/
noncomputable def arnoldiTwoStepMultiplier
    (A : Module.End ℝ E) (v₀ : E) (mu : A.Eigenvalues) (k : ℕ) : ℝ :=
  ((arnoldiFactorOrbit2 A v₀ k).toPolynomial *
      (arnoldiFactorOrbit2 A v₀ (k + 1)).toPolynomial).eval (mu : ℝ) /
    (arnoldiNormalizerOrbit2 A v₀ k *
      arnoldiNormalizerOrbit2 A v₀ (k + 1))

/-- Parseval's identity for the grouped eigenspace components. -/
theorem sum_weight_eq_norm_sq
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v : E) :
    ∑ mu : A.Eigenvalues, weight A hA v mu = ‖v‖ ^ 2 := by
  rw [← hA.diagonalization.norm_map v]
  simpa only [weight, component] using
    (PiLp.norm_sq_eq_of_L2 _ (hA.diagonalization v)).symm

/-- Exact one-step component multiplier along the Arnoldi orbit. -/
theorem component_arnoldiOrbit2_succ
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v₀ : E)
    (mu : A.Eigenvalues) (k : ℕ) :
    component A hA (arnoldiOrbit2 A v₀ (k + 1)) mu =
      ((arnoldiNormalizerOrbit2 A v₀ k)⁻¹ *
        (arnoldiFactorOrbit2 A v₀ k).toPolynomial.eval (mu : ℝ)) •
          component A hA (arnoldiOrbit2 A v₀ k) mu := by
  simpa only [arnoldiOrbit2_succ, arnoldiNormalizerOrbit2,
    arnoldiFactorOrbit2] using
      component_arnoldiStep2 A hA (arnoldiOrbit2 A v₀ k) mu

/-- Exact two-step component recurrence (manuscript equation `component`). -/
theorem component_arnoldiOrbit2_add_two
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v₀ : E)
    (mu : A.Eigenvalues) (k : ℕ) :
    component A hA (arnoldiOrbit2 A v₀ (k + 2)) mu =
      (((arnoldiFactorOrbit2 A v₀ k).toPolynomial *
          (arnoldiFactorOrbit2 A v₀ (k + 1)).toPolynomial).eval (mu : ℝ) /
        (arnoldiNormalizerOrbit2 A v₀ k *
          arnoldiNormalizerOrbit2 A v₀ (k + 1))) •
            component A hA (arnoldiOrbit2 A v₀ k) mu := by
  rw [component_arnoldiOrbit2_succ A hA v₀ mu (k + 1)]
  rw [component_arnoldiOrbit2_succ A hA v₀ mu k]
  rw [smul_smul]
  simp only [Polynomial.eval_mul]
  congr 1
  field_simp

/-- The two-step component recurrence in terms of its named scalar
multiplier. -/
theorem component_arnoldiOrbit2_add_two_eq_multiplier
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v₀ : E)
    (mu : A.Eigenvalues) (k : ℕ) :
    component A hA (arnoldiOrbit2 A v₀ (k + 2)) mu =
      arnoldiTwoStepMultiplier A v₀ mu k •
        component A hA (arnoldiOrbit2 A v₀ k) mu := by
  simpa only [arnoldiTwoStepMultiplier] using
    component_arnoldiOrbit2_add_two A hA v₀ mu k

/-- Exact one-step recurrence for squared component norms. -/
theorem weight_arnoldiOrbit2_succ
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v₀ : E)
    (mu : A.Eigenvalues) (k : ℕ) :
    weight A hA (arnoldiOrbit2 A v₀ (k + 1)) mu =
      (((arnoldiNormalizerOrbit2 A v₀ k)⁻¹ *
        (arnoldiFactorOrbit2 A v₀ k).toPolynomial.eval (mu : ℝ)) ^ 2) *
          weight A hA (arnoldiOrbit2 A v₀ k) mu := by
  rw [weight, component_arnoldiOrbit2_succ]
  rw [norm_smul, mul_pow]
  simp only [Real.norm_eq_abs, sq_abs, weight]

/-- Exact two-step recurrence for squared component norms. -/
theorem weight_arnoldiOrbit2_add_two
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v₀ : E)
    (mu : A.Eigenvalues) (k : ℕ) :
    weight A hA (arnoldiOrbit2 A v₀ (k + 2)) mu =
      ((((arnoldiFactorOrbit2 A v₀ k).toPolynomial *
          (arnoldiFactorOrbit2 A v₀ (k + 1)).toPolynomial).eval (mu : ℝ) /
        (arnoldiNormalizerOrbit2 A v₀ k *
          arnoldiNormalizerOrbit2 A v₀ (k + 1))) ^ 2) *
            weight A hA (arnoldiOrbit2 A v₀ k) mu := by
  rw [weight, component_arnoldiOrbit2_add_two]
  rw [norm_smul, mul_pow]
  simp only [Real.norm_eq_abs, sq_abs, weight]

end

end Spectral
end Forsythe
