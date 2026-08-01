import Forsythe.Arnoldi.Foundation
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Uniform height bounds

The monic competitor `X²` bounds every restart-two residual by `A²v`.
Finite dimensionality then turns this into the fixed operator-norm bound used
in the monotone-energy argument.
-/

set_option autoImplicit false

namespace Forsythe

open Polynomial

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The monic quadratic competitor `X²`. -/
def monicXSquared : MonicQuadratic := ⟨0, 0⟩

@[simp]
theorem monicXSquared_toPolynomial : monicXSquared.toPolynomial = X ^ 2 := by
  simp [monicXSquared, MonicQuadratic.toPolynomial]

omit [FiniteDimensional ℝ E] in
/-- Least-squares optimality bounds the raw residual by the `X²`
competitor. -/
theorem rawArnoldiStep2_norm_sq_le_apply_sq
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v : E)
    (hgrade : 3 ≤ grade A v) :
    ‖rawArnoldiStep2 A v‖ ^ 2 ≤ ‖(A ^ 2) v‖ ^ 2 := by
  rw [← rawArnoldiStep2_norm_sq]
  have hmin := arnoldiPoly2_minimizes A hA v hgrade monicXSquared
  have hx : polyApply A monicXSquared.toPolynomial v = (A ^ 2) v := by
    rw [polyApply_monicQuadratic A v monicXSquared]
    simp [monicXSquared]
  have hxX : polyApply A (X ^ 2) v = (A ^ 2) v := by
    rw [← monicXSquared_toPolynomial]
    exact hx
  simpa [polyInner, hxX] using hmin

omit [FiniteDimensional ℝ E] in
theorem rawArnoldiStep2_norm_le_apply_sq
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v : E)
    (hgrade : 3 ≤ grade A v) :
    ‖rawArnoldiStep2 A v‖ ≤ ‖(A ^ 2) v‖ := by
  have hsquare := rawArnoldiStep2_norm_sq_le_apply_sq A hA v hgrade
  nlinarith [norm_nonneg (rawArnoldiStep2 A v), norm_nonneg ((A ^ 2) v)]

/-- The fixed squared operator-norm bound for all unit states. -/
def arnoldiHeightBound (A : Module.End ℝ E) : ℝ :=
  ‖(Module.End.toContinuousLinearMap E) (A ^ 2)‖ ^ 2

theorem arnoldiHeightBound_nonneg (A : Module.End ℝ E) :
    0 ≤ arnoldiHeightBound A := by
  exact sq_nonneg _

/-- Operator-norm form of the uniform raw-residual bound. -/
theorem rawArnoldiStep2_norm_le_operatorNormSq
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v : E)
    (hv : ‖v‖ = 1) (hgrade : 3 ≤ grade A v) :
    ‖rawArnoldiStep2 A v‖ ≤
      ‖(Module.End.toContinuousLinearMap E) (A ^ 2)‖ := by
  have hraw := rawArnoldiStep2_norm_le_apply_sq A hA v hgrade
  let A2 : E →L[ℝ] E := (Module.End.toContinuousLinearMap E) (A ^ 2)
  calc
    ‖rawArnoldiStep2 A v‖ ≤ ‖(A ^ 2) v‖ := hraw
    _ = ‖A2 v‖ := rfl
    _ ≤ ‖A2‖ * ‖v‖ := A2.le_opNorm v
    _ = ‖A2‖ := by rw [hv, mul_one]

/-- Every unit grade-three state has height bounded by the fixed squared
operator norm of `A²`. -/
theorem rawArnoldiStep2_norm_sq_le_heightBound
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v : E)
    (hv : ‖v‖ = 1) (hgrade : 3 ≤ grade A v) :
    ‖rawArnoldiStep2 A v‖ ^ 2 ≤ arnoldiHeightBound A := by
  have hraw := rawArnoldiStep2_norm_le_operatorNormSq A hA v hv hgrade
  dsimp only [arnoldiHeightBound]
  nlinarith [norm_nonneg (rawArnoldiStep2 A v),
    norm_nonneg ((Module.End.toContinuousLinearMap E) (A ^ 2))]

/-- Orbit-level height bound, assuming the grade invariant. -/
theorem arnoldiOrbit2_height_le_bound
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v₀ : E)
    (hv₀ : ‖v₀‖ = 1)
    (hgrade : ∀ k : ℕ, 3 ≤ grade A (arnoldiOrbit2 A v₀ k))
    (k : ℕ) :
    quadraticStepHeight (arnoldiNormalizerOrbit2 A v₀) k ≤
      arnoldiHeightBound A := by
  rw [quadraticStepHeight, arnoldiNormalizerOrbit2]
  exact rawArnoldiStep2_norm_sq_le_heightBound A hA _
    (norm_arnoldiOrbit2_of_grade_three A v₀ hv₀ hgrade k) (hgrade k)

/-- The height increments of every valid grade-three orbit are summable. -/
theorem summable_arnoldiOrbit2_height_increment
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v₀ : E)
    (hv₀ : ‖v₀‖ = 1)
    (hgrade : ∀ k : ℕ, 3 ≤ grade A (arnoldiOrbit2 A v₀ k)) :
    Summable (fun k =>
      quadraticStepHeight (arnoldiNormalizerOrbit2 A v₀) (k + 1) -
        quadraticStepHeight (arnoldiNormalizerOrbit2 A v₀) k) := by
  have hsteps := arnoldiOrbit2_isQuadraticStepSequence A hA v₀ hv₀ hgrade
  exact hsteps.summable_height_increment hA
    (arnoldiOrbit2_height_le_bound A hA v₀ hv₀ hgrade)

end
end Forsythe
