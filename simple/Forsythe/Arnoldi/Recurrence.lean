import Forsythe.Arnoldi.Orbit

/-!
# Denormalized Arnoldi recurrences

The normalized step relation is often more useful after denominators are
cleared.  This module records the exact one- and two-step vector recurrences
used when passing to cluster-point limits.
-/

set_option autoImplicit false

namespace Forsythe

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace IsQuadraticStep

/-- Clear the positive normalizer in one quadratic step. -/
theorem denormalized {A : Module.End ℝ E} {v w : E}
    {p : MonicQuadratic} {sigma : ℝ}
    (h : IsQuadraticStep A v w p sigma) :
    polyApply A p.toPolynomial v = sigma • w := by
  rw [h.update]
  rw [smul_smul]
  field_simp [h.sigma_ne]
  simp

end IsQuadraticStep

namespace IsQuadraticStepSequence

variable {A : Module.End ℝ E} {v : ℕ → E}
  {p : ℕ → MonicQuadratic} {sigma : ℕ → ℝ}

/-- Exact two-step recurrence with both normalizers cleared. -/
theorem two_step_recurrence
    (h : IsQuadraticStepSequence A v p sigma) (k : ℕ) :
    polyApply A ((p k).toPolynomial * (p (k + 1)).toPolynomial) (v k) =
      (sigma k * sigma (k + 1)) • v (k + 2) := by
  calc
    polyApply A ((p k).toPolynomial * (p (k + 1)).toPolynomial) (v k) =
        polyApply A (p (k + 1)).toPolynomial
          (polyApply A (p k).toPolynomial (v k)) := by
            rw [mul_comm, polyApply_mul]
    _ = polyApply A (p (k + 1)).toPolynomial
          (sigma k • v (k + 1)) := by rw [(h.step k).denormalized]
    _ = sigma k •
          polyApply A (p (k + 1)).toPolynomial (v (k + 1)) := by
            rw [polyApply_smul]
    _ = sigma k • (sigma (k + 1) • v (k + 2)) := by
            rw [(h.step (k + 1)).denormalized]
    _ = (sigma k * sigma (k + 1)) • v (k + 2) := by
            rw [smul_smul]

/-- The manuscript remainder `Q_k - sigma_k²` applied to the current
vector, written without polynomial notation on the right. -/
theorem two_step_remainder_recurrence
    (h : IsQuadraticStepSequence A v p sigma) (k : ℕ) :
    polyApply A
        ((p k).toPolynomial * (p (k + 1)).toPolynomial -
          Polynomial.C (sigma k ^ 2)) (v k) =
      (sigma k * sigma (k + 1)) • v (k + 2) -
        sigma k ^ 2 • v k := by
  rw [polyApply_sub, h.two_step_recurrence, polyApply_C]

end IsQuadraticStepSequence

/-- Orbit-specialized exact two-step recurrence. -/
theorem arnoldiOrbit2_two_step_recurrence
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v₀ : E)
    (hv₀ : ‖v₀‖ = 1) (hgrade₀ : 3 ≤ grade A v₀) (k : ℕ) :
    polyApply A
        ((arnoldiFactorOrbit2 A v₀ k).toPolynomial *
          (arnoldiFactorOrbit2 A v₀ (k + 1)).toPolynomial)
        (arnoldiOrbit2 A v₀ k) =
      (arnoldiNormalizerOrbit2 A v₀ k *
        arnoldiNormalizerOrbit2 A v₀ (k + 1)) •
          arnoldiOrbit2 A v₀ (k + 2) :=
  (arnoldiOrbit2_isQuadraticStepSequence_of_grade_three
    A hA v₀ hv₀ hgrade₀).two_step_recurrence k

end

end Forsythe
