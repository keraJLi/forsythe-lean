import Forsythe.Arnoldi.Orbit
import Forsythe.Dynamics.ClusterSet
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# First asymptotic consequences of the energy law

The normalizers form a positive bounded monotone sequence.  Their ratio tends
to one, so the two-step vector displacement tends to zero.  Applied to each
parity, the generic cluster-set theorem yields nonempty compact connected
even and odd cluster sets.
-/

set_option autoImplicit false

namespace Forsythe

open Filter Metric Set Topology
open scoped Topology

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The positive Arnoldi normalizers converge. -/
theorem arnoldiNormalizerOrbit2_tendsto
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v₀ : E)
    (hv₀ : ‖v₀‖ = 1) (hgrade₀ : 3 ≤ grade A v₀) :
    ∃ tau : ℝ, 0 < tau ∧
      Tendsto (arnoldiNormalizerOrbit2 A v₀) atTop (𝓝 tau) := by
  let sigma := arnoldiNormalizerOrbit2 A v₀
  let B := ‖(Module.End.toContinuousLinearMap E) (A ^ 2)‖
  have hgrade := grade_arnoldiOrbit2_of_grade_three A hA v₀ hgrade₀
  have hnorm := norm_arnoldiOrbit2_of_initial_grade_three
    A hA v₀ hv₀ hgrade₀
  have hsigmaBound : ∀ k : ℕ, sigma k ≤ B := by
    intro k
    exact rawArnoldiStep2_norm_le_operatorNormSq A hA
      (arnoldiOrbit2 A v₀ k) (hnorm k) (hgrade k)
  have hbdd : BddAbove (Set.range sigma) := by
    refine ⟨B, ?_⟩
    rintro _ ⟨k, rfl⟩
    exact hsigmaBound k
  have hmono : Monotone sigma :=
    arnoldiOrbit2_normalizer_monotone A hA v₀ hv₀ hgrade₀
  refine ⟨⨆ k, sigma k, ?_, tendsto_atTop_ciSup hmono hbdd⟩
  exact lt_of_lt_of_le
    ((arnoldiOrbit2_isQuadraticStepSequence_of_grade_three
      A hA v₀ hv₀ hgrade₀).sigma_pos 0)
    (le_ciSup hbdd 0)

/-- Consecutive normalizers have asymptotic ratio one. -/
theorem arnoldiNormalizerOrbit2_ratio_tendsto_one
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v₀ : E)
    (hv₀ : ‖v₀‖ = 1) (hgrade₀ : 3 ≤ grade A v₀) :
    Tendsto (fun k =>
      arnoldiNormalizerOrbit2 A v₀ k /
      arnoldiNormalizerOrbit2 A v₀ (k + 1)) atTop (𝓝 1) := by
  obtain ⟨tau, htauPos, htau⟩ :=
    arnoldiNormalizerOrbit2_tendsto A hA v₀ hv₀ hgrade₀
  have hshift : Tendsto (fun k => arnoldiNormalizerOrbit2 A v₀ (k + 1))
      atTop (𝓝 tau) :=
    htau.comp (tendsto_add_atTop_nat 1)
  have hdiv := htau.div hshift (ne_of_gt htauPos)
  change Tendsto
    (arnoldiNormalizerOrbit2 A v₀ /
      fun k => arnoldiNormalizerOrbit2 A v₀ (k + 1)) atTop (𝓝 1)
  simpa [div_self (ne_of_gt htauPos)] using hdiv

/-- The exact two-step displacement tends to zero. -/
theorem arnoldiOrbit2_twoStep_dist_tendsto_zero
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v₀ : E)
    (hv₀ : ‖v₀‖ = 1) (hgrade₀ : 3 ≤ grade A v₀) :
    Tendsto (fun k =>
      dist (arnoldiOrbit2 A v₀ (k + 2)) (arnoldiOrbit2 A v₀ k))
      atTop (𝓝 0) := by
  let v := arnoldiOrbit2 A v₀
  let sigma := arnoldiNormalizerOrbit2 A v₀
  have hsteps := arnoldiOrbit2_isQuadraticStepSequence_of_grade_three
    A hA v₀ hv₀ hgrade₀
  have hratio := arnoldiNormalizerOrbit2_ratio_tendsto_one
    A hA v₀ hv₀ hgrade₀
  change Tendsto (fun k => sigma k / sigma (k + 1)) atTop (𝓝 1) at hratio
  have hdistSq : ∀ k : ℕ,
      dist (v (k + 2)) (v k) ^ 2 = 2 - 2 * (sigma k / sigma (k + 1)) := by
    intro k
    rw [dist_eq_norm, norm_sub_sq_real, hsteps.norm_eq_one,
      hsteps.norm_eq_one, real_inner_comm, hsteps.two_step_correlation hA]
    ring
  have hsquare : Tendsto (fun k => dist (v (k + 2)) (v k) ^ 2)
      atTop (𝓝 0) := by
    rw [show (fun k => dist (v (k + 2)) (v k) ^ 2) =
        fun k => 2 - 2 * (sigma k / sigma (k + 1)) by
      funext k
      exact hdistSq k]
    have hlimit : Tendsto (fun k => (2 : ℝ) - 2 * (sigma k / sigma (k + 1)))
        atTop (𝓝 ((2 : ℝ) - 2 * 1)) :=
      tendsto_const_nhds.sub (tendsto_const_nhds.mul hratio)
    norm_num at hlimit
    exact hlimit
  have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hsquare
  change Tendsto (fun k => dist (v (k + 2)) (v k)) atTop (𝓝 0)
  have hsqrt' : Tendsto (fun k => Real.sqrt (dist (v (k + 2)) (v k) ^ 2))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using hsqrt
  have heq : (fun k => Real.sqrt (dist (v (k + 2)) (v k) ^ 2)) =
      fun k => dist (v (k + 2)) (v k) := by
    funext k
    exact Real.sqrt_sq dist_nonneg
  rw [← heq]
  exact hsqrt'

private theorem isCompact_closure_range_of_norm_eq_one
    (u : ℕ → E) (hu : ∀ k, ‖u k‖ = 1) :
    IsCompact (closure (Set.range u)) := by
  have hrange : Set.range u ⊆ sphere (0 : E) 1 := by
    rintro _ ⟨k, rfl⟩
    simp [hu k]
  exact (isCompact_sphere (0 : E) 1).of_isClosed_subset isClosed_closure
    (closure_minimal hrange isClosed_sphere)

private theorem tendsto_even_indices :
    Tendsto (fun k : ℕ => 2 * k) atTop atTop := by
  apply Filter.tendsto_atTop.2
  intro n
  exact eventually_atTop.2 ⟨n, fun b hb => by omega⟩

private theorem tendsto_odd_indices :
    Tendsto (fun k : ℕ => 2 * k + 1) atTop atTop := by
  apply Filter.tendsto_atTop.2
  intro n
  exact eventually_atTop.2 ⟨n, fun b hb => by omega⟩

/-- The even orbit has a nonempty compact connected cluster set. -/
theorem compact_connected_even_arnoldiClusterSet
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v₀ : E)
    (hv₀ : ‖v₀‖ = 1) (hgrade₀ : 3 ≤ grade A v₀) :
    let u := fun k => arnoldiOrbit2 A v₀ (2 * k)
    (clusterSet u).Nonempty ∧ IsCompact (clusterSet u) ∧
      IsConnected (clusterSet u) := by
  dsimp only
  have hnorm := norm_arnoldiOrbit2_of_initial_grade_three
    A hA v₀ hv₀ hgrade₀
  apply compact_connected_clusterSet
  · exact isCompact_closure_range_of_norm_eq_one _ (fun k => hnorm (2 * k))
  · have htwo := (arnoldiOrbit2_twoStep_dist_tendsto_zero
      A hA v₀ hv₀ hgrade₀).comp tendsto_even_indices
    convert htwo using 1
    funext k
    congr 2

/-- The odd orbit has a nonempty compact connected cluster set. -/
theorem compact_connected_odd_arnoldiClusterSet
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v₀ : E)
    (hv₀ : ‖v₀‖ = 1) (hgrade₀ : 3 ≤ grade A v₀) :
    let u := fun k => arnoldiOrbit2 A v₀ (2 * k + 1)
    (clusterSet u).Nonempty ∧ IsCompact (clusterSet u) ∧
      IsConnected (clusterSet u) := by
  dsimp only
  have hnorm := norm_arnoldiOrbit2_of_initial_grade_three
    A hA v₀ hv₀ hgrade₀
  apply compact_connected_clusterSet
  · exact isCompact_closure_range_of_norm_eq_one _ (fun k => hnorm (2 * k + 1))
  · have htwo := (arnoldiOrbit2_twoStep_dist_tendsto_zero
      A hA v₀ hv₀ hgrade₀).comp tendsto_odd_indices
    convert htwo using 1
    funext k
    congr 2

end
end Forsythe
