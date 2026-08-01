import Forsythe.Dynamics.ClusterConvergence
import Forsythe.Spectral.Coordinates
import Forsythe.Spectral.ThreeNode

/-!
# Convergence in the three-node branch

Fixed squared component norms and fixed real component lines leave only a
finite set of sign choices.  A connected cluster set contained in those
choices is therefore a singleton.  This file first proves that finite-sign
principle abstractly, then packages it for the three grouped eigenspaces of a
self-adjoint operator.
-/

set_option autoImplicit false

namespace Forsythe
namespace Spectral

open Filter Metric Module.End Set Topology
open scoped BigOperators

noncomputable section

/-- Two vectors on one real line with equal norms differ by at most a sign. -/
theorem eq_or_eq_neg_of_mem_real_span_singleton_of_norm_eq
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {direction x y : F}
    (hx : x ∈ ℝ ∙ direction) (hy : y ∈ ℝ ∙ direction)
    (hnorm : ‖x‖ = ‖y‖) :
    x = y ∨ x = -y := by
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hx
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp hy
  rw [← ha, ← hb] at hnorm ⊢
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs] at hnorm
  by_cases hdirection : direction = 0
  · subst direction
    simp
  have hdirectionNorm : ‖direction‖ ≠ 0 :=
    norm_ne_zero_iff.mpr hdirection
  have habs : |a| = |b| :=
    mul_right_cancel₀ hdirectionNorm hnorm
  rcases abs_eq_abs.mp habs with hab | hab
  · left
    rw [hab]
  · right
    rw [hab]
    simp

/-- Abstract finite-sign principle.  An injective finite coordinate family,
fixed coordinate lines, and fixed squared coordinate norms make a nonempty
set finite. -/
theorem finite_of_fixed_component_lines_and_squared_norms
    {X F ι : Type*} [Finite ι]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (S : Set X) (hS : S.Nonempty)
    (coord : X → ι → F) (hcoord : Set.InjOn coord S)
    (direction : ι → F) (rho : ι → ℝ)
    (hline : ∀ x ∈ S, ∀ i, coord x i ∈ ℝ ∙ direction i)
    (hsq : ∀ x ∈ S, ∀ i, ‖coord x i‖ ^ 2 = rho i) :
    S.Finite := by
  classical
  obtain ⟨x₀, hx₀⟩ := hS
  let choices : ι → Set F := fun i => {coord x₀ i, -coord x₀ i}
  let possible : Set (ι → F) := {f | ∀ i, f i ∈ choices i}
  have hpossible : possible.Finite := by
    exact Set.Finite.pi' fun i => Set.toFinite (choices i)
  have himage : coord '' S ⊆ possible := by
    rintro _ ⟨x, hx, rfl⟩
    intro i
    have hnorm : ‖coord x i‖ = ‖coord x₀ i‖ := by
      have hxSq := hsq x hx i
      have hx₀Sq := hsq x₀ hx₀ i
      nlinarith [norm_nonneg (coord x i), norm_nonneg (coord x₀ i)]
    rcases eq_or_eq_neg_of_mem_real_span_singleton_of_norm_eq
        (hline x hx i) (hline x₀ hx₀ i) hnorm with heq | heq
    · exact Set.mem_insert_iff.mpr (Or.inl heq)
    · exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr heq))
  exact (hpossible.subset himage).of_finite_image hcoord

/-- Three-node constraints determine the fixed squared coordinate norms, so
the finite-sign principle makes the set finite. -/
theorem finite_of_threeNode_component_constraints
    {X F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (S : Set X) (hS : S.Nonempty)
    (coord : X → Fin 3 → F) (hcoord : Set.InjOn coord S)
    (direction : Fin 3 → F)
    (lambda : Fin 3 → ℝ) (hlambda : Function.Injective lambda)
    (p q : MonicQuadratic) {H : ℝ} (hH : H ≠ 0)
    (hpq : ∀ i, p.toPolynomial.eval (lambda i) *
      q.toPolynomial.eval (lambda i) = H)
    (hline : ∀ x ∈ S, ∀ i, coord x i ∈ ℝ ∙ direction i)
    (hconstraints : ∀ x ∈ S,
      threeNodeWeightConstraints lambda p (fun i => ‖coord x i‖ ^ 2) =
        (1, (0, 0))) :
    S.Finite := by
  obtain ⟨x₀, hx₀⟩ := hS
  let rho : Fin 3 → ℝ := fun i => ‖coord x₀ i‖ ^ 2
  apply finite_of_fixed_component_lines_and_squared_norms
    S ⟨x₀, hx₀⟩ coord hcoord direction rho hline
  intro x hx
  have hweights : (fun i => ‖coord x i‖ ^ 2) = rho := by
    apply threeNodeWeightConstraints_injective lambda hlambda p q hH hpq
    rw [hconstraints x hx, hconstraints x₀ hx₀]
  exact congrFun hweights

/-- A precompact asymptotically regular sequence satisfying the abstract
three-node component conditions converges. -/
theorem exists_tendsto_of_threeNode_component_constraints
    {X F : Type*} [MetricSpace X]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (u : ℕ → X) (hu : IsCompact (closure (range u)))
    (hstep : Tendsto (fun n => dist (u (n + 1)) (u n)) atTop (𝓝 0))
    (coord : X → Fin 3 → F)
    (hcoord : Set.InjOn coord (clusterSet u))
    (direction : Fin 3 → F)
    (lambda : Fin 3 → ℝ) (hlambda : Function.Injective lambda)
    (p q : MonicQuadratic) {H : ℝ} (hH : H ≠ 0)
    (hpq : ∀ i, p.toPolynomial.eval (lambda i) *
      q.toPolynomial.eval (lambda i) = H)
    (hline : ∀ x ∈ clusterSet u, ∀ i,
      coord x i ∈ ℝ ∙ direction i)
    (hconstraints : ∀ x ∈ clusterSet u,
      threeNodeWeightConstraints lambda p (fun i => ‖coord x i‖ ^ 2) =
        (1, (0, 0))) :
    ∃ x : X, Tendsto u atTop (𝓝 x) := by
  apply exists_tendsto_of_finite_clusterSet_of_dist_tendsto_zero u hu hstep
  exact finite_of_threeNode_component_constraints
    (clusterSet u) (clusterSet_nonempty hu) coord hcoord direction
      lambda hlambda p q hH hpq hline hconstraints

section GroupedComponents

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The three selected grouped eigenspace components, coerced back to the
ambient space. -/
def threeNodeComponents (A : Module.End ℝ E) (hA : A.IsSymmetric)
    (nodes : Fin 3 → A.Eigenvalues) (v : E) : Fin 3 → E :=
  fun i => component A hA v (nodes i)

/-- On vectors supported on the selected three grouped eigenspaces, the
three component map is injective. -/
theorem threeNodeComponents_injOn_of_supported
    (A : Module.End ℝ E) (hA : A.IsSymmetric)
    (nodes : Fin 3 → A.Eigenvalues) (S : Set E)
    (hsupport : ∀ v ∈ S, ∀ mu,
      mu ∉ Set.range nodes → component A hA v mu = 0) :
    Set.InjOn (threeNodeComponents A hA nodes) S := by
  intro x hx y hy hxy
  apply hA.diagonalization.injective
  ext mu
  have hcomponent : component A hA x mu = component A hA y mu := by
    by_cases hmu : mu ∈ Set.range nodes
    · obtain ⟨i, rfl⟩ := hmu
      apply Subtype.ext
      exact congrFun hxy i
    · rw [hsupport x hx mu hmu, hsupport y hy mu hmu]
  simpa only [component] using congrArg Subtype.val hcomponent

/-- Grouped-eigenspace wrapper for the three-node convergence branch.  The
support and fixed-line hypotheses are exactly what polynomial Arnoldi
iteration supplies once the active spectrum has stabilized. -/
theorem exists_tendsto_of_threeNode_grouped_components
    (A : Module.End ℝ E) (hA : A.IsSymmetric)
    (u : ℕ → E) (hu : IsCompact (closure (range u)))
    (hstep : Tendsto (fun n => dist (u (n + 1)) (u n)) atTop (𝓝 0))
    (nodes : Fin 3 → A.Eigenvalues)
    (hnodes : Function.Injective nodes)
    (direction : Fin 3 → E)
    (p q : MonicQuadratic) {H : ℝ} (hH : H ≠ 0)
    (hpq : ∀ i, p.toPolynomial.eval ((nodes i : A.Eigenvalues) : ℝ) *
      q.toPolynomial.eval ((nodes i : A.Eigenvalues) : ℝ) = H)
    (hsupport : ∀ v ∈ clusterSet u, ∀ mu,
      mu ∉ Set.range nodes → component A hA v mu = 0)
    (hline : ∀ v ∈ clusterSet u, ∀ i,
      threeNodeComponents A hA nodes v i ∈ ℝ ∙ direction i)
    (hconstraints : ∀ v ∈ clusterSet u,
      threeNodeWeightConstraints
          (fun i => ((nodes i : A.Eigenvalues) : ℝ)) p
          (fun i => ‖threeNodeComponents A hA nodes v i‖ ^ 2) =
        (1, (0, 0))) :
    ∃ v : E, Tendsto u atTop (𝓝 v) := by
  have hlambda : Function.Injective
      (fun i => ((nodes i : A.Eigenvalues) : ℝ)) := by
    intro i j hij
    apply hnodes
    exact Subtype.ext hij
  exact exists_tendsto_of_threeNode_component_constraints
    u hu hstep (threeNodeComponents A hA nodes)
      (threeNodeComponents_injOn_of_supported A hA nodes (clusterSet u) hsupport)
      direction (fun i => ((nodes i : A.Eigenvalues) : ℝ)) hlambda
      p q hH hpq hline hconstraints

end GroupedComponents

end

end Spectral
end Forsythe
