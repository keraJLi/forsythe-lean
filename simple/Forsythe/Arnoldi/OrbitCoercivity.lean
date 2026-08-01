import Forsythe.Arnoldi.Coercivity
import Forsythe.Arnoldi.LimitGrade

/-!
# Uniform coercivity along a restart-two Arnoldi orbit

The unit sphere is compact in finite dimension.  Every cluster point of a
valid Arnoldi orbit retains grade at least three, so the generic compactness
result for the moment Gram determinant supplies a positive lower bound on an
orbit tail.  Cramer's formulas then give an explicit tail bound for the two
free coefficients of the Arnoldi factors in the fixed product norm.
-/

set_option autoImplicit false

namespace Forsythe

open Filter Metric Set Topology
open scoped Topology

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The closure of a valid Arnoldi orbit is compact because the whole orbit
lies on the finite-dimensional unit sphere. -/
theorem isCompact_closure_range_arnoldiOrbit2
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v₀ : E)
    (hv₀ : ‖v₀‖ = 1) (hgrade₀ : 3 ≤ grade A v₀) :
    IsCompact (closure (range (arnoldiOrbit2 A v₀))) := by
  have hnorm := norm_arnoldiOrbit2_of_initial_grade_three
    A hA v₀ hv₀ hgrade₀
  have hrange : range (arnoldiOrbit2 A v₀) ⊆ sphere (0 : E) 1 := by
    rintro _ ⟨k, rfl⟩
    simp [hnorm k]
  exact (isCompact_sphere (0 : E) 1).of_isClosed_subset isClosed_closure
    (closure_minimal hrange isClosed_sphere)

/-- The moment Gram determinant has a common positive lower bound on some
tail of every unit grade-three Arnoldi orbit. -/
theorem exists_eventually_arnoldiOrbit2_momentGramDet_lower_bound
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v₀ : E)
    (hv₀ : ‖v₀‖ = 1) (hgrade₀ : 3 ≤ grade A v₀) :
    ∃ kappa : ℝ, 0 < kappa ∧
      ∀ᶠ k in atTop,
        kappa ≤ momentGramDet A (arnoldiOrbit2 A v₀ k) := by
  apply eventually_uniform_momentGramDet_of_cluster_grade_three
    A hA (arnoldiOrbit2 A v₀)
  · exact isCompact_closure_range_arnoldiOrbit2 A hA v₀ hv₀ hgrade₀
  · intro v hv
    exact grade_mem_arnoldiOrbit2_clusterSet A hA v₀ hv₀ hgrade₀ hv

/-- Bundled orbit-tail estimate.  The coefficient bound is the explicit
Cramer bound associated with the determinant floor `kappa`. -/
theorem exists_eventually_arnoldiOrbit2_momentGramDet_and_coeffPair_bound
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v₀ : E)
    (hv₀ : ‖v₀‖ = 1) (hgrade₀ : 3 ≤ grade A v₀) :
    ∃ kappa M : ℝ, 0 < kappa ∧ 0 ≤ M ∧
      ∀ᶠ k in atTop,
        kappa ≤ momentGramDet A (arnoldiOrbit2 A v₀ k) ∧
          ‖(arnoldiFactorOrbit2 A v₀ k).coeffPair‖ ≤ M := by
  obtain ⟨kappa, M, hkappa, hM, heventually⟩ :=
    eventually_uniform_momentGramDet_and_coeffPair_bound
      A hA (arnoldiOrbit2 A v₀)
        (isCompact_closure_range_arnoldiOrbit2 A hA v₀ hv₀ hgrade₀)
        (norm_arnoldiOrbit2_of_initial_grade_three A hA v₀ hv₀ hgrade₀)
        (fun v hv =>
          grade_mem_arnoldiOrbit2_clusterSet A hA v₀ hv₀ hgrade₀ hv)
  refine ⟨kappa, M, hkappa, hM, ?_⟩
  simpa only [arnoldiFactorOrbit2] using heventually

/-- In particular, the Arnoldi coefficient pairs are uniformly bounded on
an orbit tail. -/
theorem exists_eventually_arnoldiFactorOrbit2_coeffPair_bound
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v₀ : E)
    (hv₀ : ‖v₀‖ = 1) (hgrade₀ : 3 ≤ grade A v₀) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ᶠ k in atTop, ‖(arnoldiFactorOrbit2 A v₀ k).coeffPair‖ ≤ M := by
  obtain ⟨_, M, _, hM, heventually⟩ :=
    exists_eventually_arnoldiOrbit2_momentGramDet_and_coeffPair_bound
      A hA v₀ hv₀ hgrade₀
  exact ⟨M, hM, heventually.mono fun _ hk => hk.2⟩

end

end Forsythe
