import Forsythe.Spectral.LimitEquation

/-!
# Recovering the opposite-parity limit

Once one parity of vectors, its selected monic factors, and its positive
normalizers converge, the exact one-step Arnoldi update gives convergence of
the opposite parity.  The limit is written explicitly in polynomial
action notation.
-/

set_option autoImplicit false

namespace Forsythe

open Filter Topology

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Even-vector convergence determines the odd-vector limit through one
Arnoldi step. -/
theorem arnoldiOrbit2_odd_tendsto_of_even_tendsto
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v₀ : E)
    (hv₀ : ‖v₀‖ = 1) (hgrade₀ : 3 ≤ grade A v₀)
    (p : MonicQuadratic) (tau : ℝ) (htauPos : 0 < tau) (vEven : E)
    (hvEven : Tendsto (fun k => arnoldiOrbit2 A v₀ (2 * k))
      atTop (𝓝 vEven))
    (hpEven : Tendsto
      (fun k => (arnoldiFactorOrbit2 A v₀ (2 * k)).coeffPair)
      atTop (𝓝 p.coeffPair))
    (hsigmaEven : Tendsto
      (fun k => arnoldiNormalizerOrbit2 A v₀ (2 * k))
      atTop (𝓝 tau)) :
    Tendsto (fun k => arnoldiOrbit2 A v₀ (2 * k + 1)) atTop
      (𝓝 (tau⁻¹ • polyApply A p.toPolynomial vEven)) := by
  have haction := Spectral.tendsto_polyApply_monicQuadratic
    A hpEven hvEven
  have hupdateLimit := (hsigmaEven.inv₀ (ne_of_gt htauPos)).smul haction
  have hsteps := arnoldiOrbit2_isQuadraticStepSequence_of_grade_three
    A hA v₀ hv₀ hgrade₀
  apply hupdateLimit.congr'
  exact Eventually.of_forall fun k => (hsteps.step (2 * k)).update.symm

/-- Odd-vector convergence similarly determines the shifted even limit; a
finite initial term does not affect convergence, so the full even subsequence
has that limit. -/
theorem arnoldiOrbit2_even_tendsto_of_odd_tendsto
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v₀ : E)
    (hv₀ : ‖v₀‖ = 1) (hgrade₀ : 3 ≤ grade A v₀)
    (q : MonicQuadratic) (tau : ℝ) (htauPos : 0 < tau) (vOdd : E)
    (hvOdd : Tendsto (fun k => arnoldiOrbit2 A v₀ (2 * k + 1))
      atTop (𝓝 vOdd))
    (hqOdd : Tendsto
      (fun k => (arnoldiFactorOrbit2 A v₀ (2 * k + 1)).coeffPair)
      atTop (𝓝 q.coeffPair))
    (hsigmaOdd : Tendsto
      (fun k => arnoldiNormalizerOrbit2 A v₀ (2 * k + 1))
      atTop (𝓝 tau)) :
    Tendsto (fun k => arnoldiOrbit2 A v₀ (2 * k)) atTop
      (𝓝 (tau⁻¹ • polyApply A q.toPolynomial vOdd)) := by
  have haction := Spectral.tendsto_polyApply_monicQuadratic
    A hqOdd hvOdd
  have hupdateLimit := (hsigmaOdd.inv₀ (ne_of_gt htauPos)).smul haction
  have hsteps := arnoldiOrbit2_isQuadraticStepSequence_of_grade_three
    A hA v₀ hv₀ hgrade₀
  have hshifted :
      Tendsto (fun k => arnoldiOrbit2 A v₀ (2 * k + 2)) atTop
        (𝓝 (tau⁻¹ • polyApply A q.toPolynomial vOdd)) := by
    apply hupdateLimit.congr'
    exact Eventually.of_forall fun k => (hsteps.step (2 * k + 1)).update.symm
  apply (tendsto_add_atTop_iff_nat 1).mp
  simpa [Nat.mul_add] using hshifted

end

end Forsythe
