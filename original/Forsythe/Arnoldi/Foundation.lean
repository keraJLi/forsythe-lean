import Forsythe.Arnoldi.Continuity
import Forsythe.Arnoldi.Energy

/-!
# Valid grade-three Arnoldi states and orbits

This module discharges the conditional step interface from the manuscript's
unit-norm, symmetry, and grade hypotheses.  Grade preservation itself is kept
separate, so the orbit-level result accepts the exact invariant it needs.
-/

set_option autoImplicit false

namespace Forsythe

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A unit grade-three state realizes the exact conditional quadratic-step
interface with its raw-update norm as normalizer. -/
theorem arnoldiStep2_isQuadraticStep_of_grade_three
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v : E)
    (hv : ‖v‖ = 1) (hgrade : 3 ≤ grade A v) :
    IsQuadraticStep A v (arnoldiStep2 A v) (arnoldiPoly2 A v)
      ‖rawArnoldiStep2 A v‖ := by
  apply arnoldiStep2_isQuadraticStep A v hv
  · exact rawArnoldiStep2_ne_zero_of_grade_ge_three A v hgrade
  · exact arnoldiPoly2_orthogonal_linear A hA v hgrade

theorem norm_arnoldiStep2_of_grade_three
    (A : Module.End ℝ E) (v : E) (hgrade : 3 ≤ grade A v) :
    ‖arnoldiStep2 A v‖ = 1 :=
  norm_arnoldiStep2 A v
    (rawArnoldiStep2_ne_zero_of_grade_ge_three A v hgrade)

theorem arnoldiStep2_ne_zero_of_grade_three
    (A : Module.End ℝ E) (v : E) (hgrade : 3 ≤ grade A v) :
    arnoldiStep2 A v ≠ 0 :=
  arnoldiStep2_ne_zero A v
    (rawArnoldiStep2_ne_zero_of_grade_ge_three A v hgrade)

/-- On the grade-three domain, both rational denominators in the normalized
Arnoldi map are automatically nonzero. -/
theorem continuousAt_arnoldiStep2_of_grade_three
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v : E)
    (hgrade : 3 ≤ grade A v) :
    ContinuousAt (arnoldiStep2 A) v :=
  continuousAt_arnoldiStep2 A v
    (momentGramDet_ne_zero_of_grade_three A hA v hgrade)
    (rawArnoldiStep2_ne_zero_of_grade_ge_three A v hgrade)

/-- The monic factor selected at orbit index `k`. -/
def arnoldiFactorOrbit2 (A : Module.End ℝ E) (v₀ : E) (k : ℕ) :
    MonicQuadratic :=
  arnoldiPoly2 A (arnoldiOrbit2 A v₀ k)

/-- The positive normalization factor selected at orbit index `k`. -/
def arnoldiNormalizerOrbit2 (A : Module.End ℝ E) (v₀ : E) (k : ℕ) : ℝ :=
  ‖rawArnoldiStep2 A (arnoldiOrbit2 A v₀ k)‖

/-- Unit norm propagates along an orbit whose grade-three invariant is
available at every index. -/
theorem norm_arnoldiOrbit2_of_grade_three
    (A : Module.End ℝ E) (v₀ : E) (hv₀ : ‖v₀‖ = 1)
    (hgrade : ∀ k : ℕ, 3 ≤ grade A (arnoldiOrbit2 A v₀ k)) :
    ∀ k : ℕ, ‖arnoldiOrbit2 A v₀ k‖ = 1 := by
  apply norm_arnoldiOrbit2_of_raw_ne A v₀ hv₀
  intro k
  exact rawArnoldiStep2_ne_zero_of_grade_ge_three A _ (hgrade k)

/-- A valid grade-three Arnoldi orbit is a sequence of the conditional steps
used by the energy module. -/
theorem arnoldiOrbit2_isQuadraticStepSequence
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v₀ : E)
    (hv₀ : ‖v₀‖ = 1)
    (hgrade : ∀ k : ℕ, 3 ≤ grade A (arnoldiOrbit2 A v₀ k)) :
    IsQuadraticStepSequence A (arnoldiOrbit2 A v₀)
      (arnoldiFactorOrbit2 A v₀) (arnoldiNormalizerOrbit2 A v₀) := by
  have hnorm := norm_arnoldiOrbit2_of_grade_three A v₀ hv₀ hgrade
  constructor
  intro k
  simpa only [arnoldiFactorOrbit2, arnoldiNormalizerOrbit2,
    arnoldiOrbit2_succ] using
      arnoldiStep2_isQuadraticStep_of_grade_three A hA
        (arnoldiOrbit2 A v₀ k) (hnorm k) (hgrade k)

end
end Forsythe
