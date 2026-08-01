import Forsythe.Arnoldi.Orbit
import Forsythe.Dynamics.ClusterSet

/-!
# Grade of Arnoldi cluster points

This file gives the direct, spectral-free argument that the grade-three
condition cannot be lost at a limit point.  If a limit point had grade at
most two, it would have a monic quadratic annihilator `q`.  Least-squares
minimality of every Arnoldi factor would then put the whole orbit in the
closed set where `‖q(A)v‖` is bounded below by the first positive
normalizer.  The annihilated limit point cannot belong to that set.
-/

set_option autoImplicit false

namespace Forsythe

open Filter Set Topology

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Every monic quadratic competitor has action norm at least the initial
Arnoldi normalizer at every point of a valid orbit. -/
theorem arnoldiNormalizerOrbit2_zero_le_competitor_norm
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v₀ : E)
    (hv₀ : ‖v₀‖ = 1) (hgrade₀ : 3 ≤ grade A v₀)
    (q : MonicQuadratic) (k : ℕ) :
    arnoldiNormalizerOrbit2 A v₀ 0 ≤
      ‖polyApply A q.toPolynomial (arnoldiOrbit2 A v₀ k)‖ := by
  let v := arnoldiOrbit2 A v₀ k
  have hgrade : 3 ≤ grade A v :=
    grade_arnoldiOrbit2_of_grade_three A hA v₀ hgrade₀ k
  have hmin := arnoldiPoly2_minimizes A hA v hgrade q
  have hsquare :
      ‖rawArnoldiStep2 A v‖ ^ 2 ≤ ‖polyApply A q.toPolynomial v‖ ^ 2 := by
    rw [← rawArnoldiStep2_norm_sq]
    simpa only [polyInner, real_inner_self_eq_norm_sq] using hmin
  have hraw :
      ‖rawArnoldiStep2 A v‖ ≤ ‖polyApply A q.toPolynomial v‖ :=
    le_of_sq_le_sq hsquare (norm_nonneg _)
  exact (arnoldiOrbit2_normalizer_monotone A hA v₀ hv₀ hgrade₀
    (Nat.zero_le k)).trans hraw

/-- A map-cluster point of any index-selected Arnoldi orbit retains grade at
least three.  No cofinality assumption on the index selection is needed. -/
theorem grade_arnoldiOrbit2_mapClusterPt_of_grade_three
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v₀ : E)
    (hv₀ : ‖v₀‖ = 1) (hgrade₀ : 3 ≤ grade A v₀)
    (φ : ℕ → ℕ) {v : E}
    (hv : MapClusterPt v atTop
      (fun k => arnoldiOrbit2 A v₀ (φ k))) :
    3 ≤ grade A v := by
  by_contra hnot
  have hgrade : grade A v ≤ 2 := by omega
  obtain ⟨q, hq⟩ :=
    exists_monicQuadratic_apply_eq_zero_of_grade_le_two A v hgrade
  let sigma₀ := arnoldiNormalizerOrbit2 A v₀ 0
  let s : Set E := {w | sigma₀ ≤ ‖polyApply A q.toPolynomial w‖}
  have hcontinuous : Continuous (fun w : E => polyApply A q.toPolynomial w) := by
    change Continuous (Polynomial.aeval A q.toPolynomial : E → E)
    exact (Polynomial.aeval A q.toPolynomial).continuous_of_finiteDimensional
  have hsclosed : IsClosed s :=
    isClosed_le continuous_const hcontinuous.norm
  have hsorbit : ∀ᶠ k in atTop,
      arnoldiOrbit2 A v₀ (φ k) ∈ s :=
    Eventually.of_forall fun k =>
      arnoldiNormalizerOrbit2_zero_le_competitor_norm
        A hA v₀ hv₀ hgrade₀ q (φ k)
  have hvs : v ∈ s := hsclosed.mem_of_mapClusterPt hv hsorbit
  have hsigma₀ : 0 < sigma₀ := by
    exact (arnoldiOrbit2_isQuadraticStepSequence_of_grade_three
      A hA v₀ hv₀ hgrade₀).sigma_pos 0
  change sigma₀ ≤ ‖polyApply A q.toPolynomial v‖ at hvs
  rw [hq, norm_zero] at hvs
  exact (not_le_of_gt hsigma₀) hvs

/-- Sequential norm limits of index-selected orbit points retain grade at
least three. -/
theorem grade_arnoldiOrbit2_tendsto_of_grade_three
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v₀ : E)
    (hv₀ : ‖v₀‖ = 1) (hgrade₀ : 3 ≤ grade A v₀)
    (φ : ℕ → ℕ) {v : E}
    (hv : Tendsto (fun k => arnoldiOrbit2 A v₀ (φ k)) atTop (𝓝 v)) :
    3 ≤ grade A v :=
  grade_arnoldiOrbit2_mapClusterPt_of_grade_three
    A hA v₀ hv₀ hgrade₀ φ hv.mapClusterPt

/-- Every cluster point of the full Arnoldi orbit retains grade at least
three. -/
theorem grade_mem_arnoldiOrbit2_clusterSet
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v₀ : E)
    (hv₀ : ‖v₀‖ = 1) (hgrade₀ : 3 ≤ grade A v₀)
    {v : E} (hv : v ∈ clusterSet (arnoldiOrbit2 A v₀)) :
    3 ≤ grade A v := by
  exact grade_arnoldiOrbit2_mapClusterPt_of_grade_three
    A hA v₀ hv₀ hgrade₀ id (by simpa using hv)

/-- Every cluster point of the even orbit retains grade at least three. -/
theorem grade_mem_even_arnoldiClusterSet
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v₀ : E)
    (hv₀ : ‖v₀‖ = 1) (hgrade₀ : 3 ≤ grade A v₀)
    {v : E}
    (hv : v ∈ clusterSet (fun k => arnoldiOrbit2 A v₀ (2 * k))) :
    3 ≤ grade A v :=
  grade_arnoldiOrbit2_mapClusterPt_of_grade_three
    A hA v₀ hv₀ hgrade₀ (fun k => 2 * k) hv

/-- Every cluster point of the odd orbit retains grade at least three. -/
theorem grade_mem_odd_arnoldiClusterSet
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v₀ : E)
    (hv₀ : ‖v₀‖ = 1) (hgrade₀ : 3 ≤ grade A v₀)
    {v : E}
    (hv : v ∈ clusterSet (fun k => arnoldiOrbit2 A v₀ (2 * k + 1))) :
    3 ≤ grade A v :=
  grade_arnoldiOrbit2_mapClusterPt_of_grade_three
    A hA v₀ hv₀ hgrade₀ (fun k => 2 * k + 1) hv

end

end Forsythe
