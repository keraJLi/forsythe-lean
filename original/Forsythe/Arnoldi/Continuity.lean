import Forsythe.Arnoldi.Cyclic
import Forsythe.Arnoldi.Step
import Mathlib.Analysis.InnerProductSpace.Continuous

/-!
# Continuity of the explicit restart-two step

The moment-system formula makes continuity a direct calculation away from the
Gram determinant and normalization zero sets.
-/

set_option autoImplicit false

namespace Forsythe

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem continuous_moment (A : Module.End ℝ E) (j : ℕ) :
    Continuous (fun v : E => moment A v j) := by
  exact (A ^ j).continuous_of_finiteDimensional.inner continuous_id

theorem continuous_momentGramDet (A : Module.End ℝ E) :
    Continuous (momentGramDet A) := by
  exact ((continuous_moment A 0).mul (continuous_moment A 2)).sub
    ((continuous_moment A 1).pow 2)

theorem continuousAt_arnoldiPoly2_linearCoeff
    (A : Module.End ℝ E) (v : E) (hdet : momentGramDet A v ≠ 0) :
    ContinuousAt (fun w : E => (arnoldiPoly2 A w).linearCoeff) v := by
  apply ContinuousAt.div
  · exact ((continuous_moment A 1).continuousAt.mul
      (continuous_moment A 2).continuousAt).sub
        ((continuous_moment A 0).continuousAt.mul
          (continuous_moment A 3).continuousAt)
  · exact (continuous_momentGramDet A).continuousAt
  · exact hdet

theorem continuousAt_arnoldiPoly2_constantCoeff
    (A : Module.End ℝ E) (v : E) (hdet : momentGramDet A v ≠ 0) :
    ContinuousAt (fun w : E => (arnoldiPoly2 A w).constantCoeff) v := by
  apply ContinuousAt.div
  · exact ((continuous_moment A 1).continuousAt.mul
      (continuous_moment A 3).continuousAt).sub
        ((continuous_moment A 2).continuousAt.pow 2)
  · exact (continuous_momentGramDet A).continuousAt
  · exact hdet

theorem continuousAt_arnoldiPoly2_coeffPair
    (A : Module.End ℝ E) (v : E) (hdet : momentGramDet A v ≠ 0) :
    ContinuousAt (fun w : E => (arnoldiPoly2 A w).coeffPair) v := by
  exact (continuousAt_arnoldiPoly2_linearCoeff A v hdet).prodMk
    (continuousAt_arnoldiPoly2_constantCoeff A v hdet)

/-- The unnormalized update is continuous wherever the moment Gram system is
nonsingular. -/
theorem continuousAt_rawArnoldiStep2
    (A : Module.End ℝ E) (v : E) (hdet : momentGramDet A v ≠ 0) :
    ContinuousAt (rawArnoldiStep2 A) v := by
  have hA : Continuous (A : E → E) := A.continuous_of_finiteDimensional
  have hA2 : Continuous (fun w : E => (A ^ 2) w) :=
    (A ^ 2).continuous_of_finiteDimensional
  have hlinear := continuousAt_arnoldiPoly2_linearCoeff A v hdet
  have hconstant := continuousAt_arnoldiPoly2_constantCoeff A v hdet
  have hformula : rawArnoldiStep2 A = fun w : E =>
      (A ^ 2) w + (arnoldiPoly2 A w).linearCoeff • A w +
        (arnoldiPoly2 A w).constantCoeff • w := by
    funext w
    rw [rawArnoldiStep2, polyApply_monicQuadratic A w (arnoldiPoly2 A w)]
  rw [hformula]
  exact (hA2.continuousAt.add (hlinear.smul hA.continuousAt)).add
    (hconstant.smul continuousAt_id)

/-- The normalized restart-two map is continuous at every valid state. -/
theorem continuousAt_arnoldiStep2
    (A : Module.End ℝ E) (v : E)
    (hdet : momentGramDet A v ≠ 0)
    (hraw : rawArnoldiStep2 A v ≠ 0) :
    ContinuousAt (arnoldiStep2 A) v := by
  have hrawContinuous := continuousAt_rawArnoldiStep2 A v hdet
  have hinv : ContinuousAt (fun w : E => ‖rawArnoldiStep2 A w‖⁻¹) v :=
    hrawContinuous.norm.inv₀ (norm_ne_zero_iff.mpr hraw)
  change ContinuousAt
    (fun w : E => ‖rawArnoldiStep2 A w‖⁻¹ • rawArnoldiStep2 A w) v
  exact hinv.smul hrawContinuous

end
end Forsythe
