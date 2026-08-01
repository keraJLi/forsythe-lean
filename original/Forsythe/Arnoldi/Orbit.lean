import Forsythe.Arnoldi.Bounds
import Forsythe.Arnoldi.Grade

/-!
# Unconditional valid-orbit energy API

The initial unit-norm and grade-three assumptions now suffice: grade
preservation discharges every per-index validity hypothesis used in the
conditional energy layer.
-/

set_option autoImplicit false

namespace Forsythe

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem arnoldiOrbit2_isQuadraticStepSequence_of_grade_three
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v₀ : E)
    (hv₀ : ‖v₀‖ = 1) (hgrade₀ : 3 ≤ grade A v₀) :
    IsQuadraticStepSequence A (arnoldiOrbit2 A v₀)
      (arnoldiFactorOrbit2 A v₀) (arnoldiNormalizerOrbit2 A v₀) :=
  arnoldiOrbit2_isQuadraticStepSequence A hA v₀ hv₀
    (grade_arnoldiOrbit2_of_grade_three A hA v₀ hgrade₀)

theorem norm_arnoldiOrbit2_of_initial_grade_three
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v₀ : E)
    (hv₀ : ‖v₀‖ = 1) (hgrade₀ : 3 ≤ grade A v₀) :
    ∀ k : ℕ, ‖arnoldiOrbit2 A v₀ k‖ = 1 :=
  norm_arnoldiOrbit2_of_grade_three A v₀ hv₀
    (grade_arnoldiOrbit2_of_grade_three A hA v₀ hgrade₀)

theorem arnoldiOrbit2_height_monotone
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v₀ : E)
    (hv₀ : ‖v₀‖ = 1) (hgrade₀ : 3 ≤ grade A v₀) :
    Monotone (quadraticStepHeight (arnoldiNormalizerOrbit2 A v₀)) :=
  (arnoldiOrbit2_isQuadraticStepSequence_of_grade_three
    A hA v₀ hv₀ hgrade₀).height_monotone hA

theorem arnoldiOrbit2_normalizer_monotone
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v₀ : E)
    (hv₀ : ‖v₀‖ = 1) (hgrade₀ : 3 ≤ grade A v₀) :
    Monotone (arnoldiNormalizerOrbit2 A v₀) :=
  (arnoldiOrbit2_isQuadraticStepSequence_of_grade_three
    A hA v₀ hv₀ hgrade₀).sigma_monotone hA

theorem arnoldiOrbit2_height_le_bound_of_initial_grade_three
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v₀ : E)
    (hv₀ : ‖v₀‖ = 1) (hgrade₀ : 3 ≤ grade A v₀)
    (k : ℕ) :
    quadraticStepHeight (arnoldiNormalizerOrbit2 A v₀) k ≤
      arnoldiHeightBound A :=
  arnoldiOrbit2_height_le_bound A hA v₀ hv₀
    (grade_arnoldiOrbit2_of_grade_three A hA v₀ hgrade₀) k

theorem summable_arnoldiOrbit2_height_increment_of_initial_grade_three
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v₀ : E)
    (hv₀ : ‖v₀‖ = 1) (hgrade₀ : 3 ≤ grade A v₀) :
    Summable (fun k =>
      quadraticStepHeight (arnoldiNormalizerOrbit2 A v₀) (k + 1) -
        quadraticStepHeight (arnoldiNormalizerOrbit2 A v₀) k) :=
  summable_arnoldiOrbit2_height_increment A hA v₀ hv₀
    (grade_arnoldiOrbit2_of_grade_three A hA v₀ hgrade₀)

/-- Once the exact two-step energy vanishes, the deterministic Arnoldi orbit
is two-periodic from that index onward. -/
theorem arnoldiOrbit2_eventually_two_periodic_of_energy_eq_zero
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v₀ : E)
    (hv₀ : ‖v₀‖ = 1) (hgrade₀ : 3 ≤ grade A v₀)
    {k : ℕ}
    (henergy : quadraticStepEnergy A (arnoldiOrbit2 A v₀)
      (arnoldiFactorOrbit2 A v₀) (arnoldiNormalizerOrbit2 A v₀) k = 0) :
    ∀ n, k ≤ n → arnoldiOrbit2 A v₀ (n + 2) = arnoldiOrbit2 A v₀ n := by
  have hsteps := arnoldiOrbit2_isQuadraticStepSequence_of_grade_three
    A hA v₀ hv₀ hgrade₀
  apply hsteps.eventually_two_periodic_of_energy_eq_zero hA
    (T := arnoldiStep2 A) (k := k)
  · intro n
    exact arnoldiOrbit2_succ A v₀ n
  · exact henergy

end
end Forsythe
