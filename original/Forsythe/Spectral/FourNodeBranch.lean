import Forsythe.FourNode.Fiber
import Forsythe.Spectral.ExteriorMass
import Forsythe.Spectral.PrincipalWeights
import Forsythe.Spectral.ThreeNodeBranch
import Forsythe.Spectral.WeightConvergence

/-!
# Spectral setup for the four-node branch

A grade-four parity cluster point canonically labels the four roots of the
common limiting annihilator by its active distinct eigenvalues.  This module
identifies the annihilator with the corresponding nodal quartic, proves that
all other parity cluster points are supported on those four nodes, and
packages their normalized principal weights as points of the exact limiting
four-node fibers.

No rate of exterior decay is asserted here.  That belongs to the logarithmic
cocycle argument in the exterior-decay stage.
-/

set_option autoImplicit false

namespace Forsythe
namespace Spectral

open Filter Module.End Polynomial Set Topology
open scoped BigOperators

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Canonical enumeration of the active distinct eigenvalues of a
grade-four cluster point. -/
def nodesOfFourClusterPoint
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v : E)
    (hcard : (active A hA v).card = 4) : Fin 4 → A.Eigenvalues :=
  fun i ↦ (((active A hA v).equivFinOfCardEq hcard).symm i :
    active A hA v)

theorem nodesOfFourClusterPoint_injective
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v : E)
    (hcard : (active A hA v).card = 4) :
    Function.Injective (nodesOfFourClusterPoint A hA v hcard) := by
  intro i j hij
  apply ((active A hA v).equivFinOfCardEq hcard).symm.injective
  exact Subtype.ext hij

theorem nodesOfFourClusterPoint_mem_active
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v : E)
    (hcard : (active A hA v).card = 4) (i : Fin 4) :
    nodesOfFourClusterPoint A hA v hcard i ∈ active A hA v :=
  (((active A hA v).equivFinOfCardEq hcard).symm i).property

/-- The canonical four nodes exhaust the active support used to define
them. -/
theorem mem_range_nodesOfFourClusterPoint_iff
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v : E)
    (hcard : (active A hA v).card = 4) (mu : A.Eigenvalues) :
    mu ∈ Set.range (nodesOfFourClusterPoint A hA v hcard) ↔
      mu ∈ active A hA v := by
  constructor
  · rintro ⟨i, rfl⟩
    exact nodesOfFourClusterPoint_mem_active A hA v hcard i
  · intro hmu
    let a : active A hA v := ⟨mu, hmu⟩
    let i : Fin 4 := (active A hA v).equivFinOfCardEq hcard a
    refine ⟨i, ?_⟩
    exact congrArg Subtype.val
      (((active A hA v).equivFinOfCardEq hcard).symm_apply_apply a)

private theorem nodalQuartic_isMonicOfDegree_four
    (lambda : Fin 4 → ℝ) :
    (FourNode.nodalQuartic lambda).IsMonicOfDegree 4 := by
  have h0 := isMonicOfDegree_X_sub_one (lambda 0)
  have h1 := isMonicOfDegree_X_sub_one (lambda 1)
  have h2 := isMonicOfDegree_X_sub_one (lambda 2)
  have h3 := isMonicOfDegree_X_sub_one (lambda 3)
  simpa only [FourNode.nodalQuartic, Fin.prod_univ_four, Nat.reduceAdd] using
    ((h0.mul h1).mul h2).mul h3

private theorem nodalQuartic_eval_node
    (lambda : Fin 4 → ℝ) (i : Fin 4) :
    (FourNode.nodalQuartic lambda).eval (lambda i) = 0 := by
  rw [FourNode.nodalQuartic, eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)

/-- Four active roots determine the common monic quartic annihilator. -/
theorem quadraticProduct_eq_nodalQuartic_add_C_of_active_card_four
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v : E)
    (p q : MonicQuadratic) (H : ℝ)
    (hcard : (active A hA v).card = 4)
    (hann : polyApply A
      (p.toPolynomial * q.toPolynomial - C H) v = 0) :
    p.toPolynomial * q.toPolynomial =
      FourNode.nodalQuartic
          (fun i ↦ ((nodesOfFourClusterPoint A hA v hcard i :
            A.Eigenvalues) : ℝ)) + C H := by
  let nodes := nodesOfFourClusterPoint A hA v hcard
  let lambda : Fin 4 → ℝ := fun i ↦ ((nodes i : A.Eigenvalues) : ℝ)
  let r := p.toPolynomial * q.toPolynomial - C H
  have hr : r.IsMonicOfDegree 4 :=
    ⟨natDegree_quadraticProduct_sub_C p q H,
      monic_quadraticProduct_sub_C p q H⟩
  have hPi : (FourNode.nodalQuartic lambda).IsMonicOfDegree 4 :=
    nodalQuartic_isMonicOfDegree_four lambda
  have hdegree :
      (r - FourNode.nodalQuartic lambda).natDegree < 4 :=
    hr.natDegree_sub_lt (by norm_num) hPi
  have heval : ∀ i : Fin 4,
      (r - FourNode.nodalQuartic lambda).eval (lambda i) = 0 := by
    intro i
    have hroot := factor_eval_eq_of_mem_active_of_limitEquation
      A hA v p q H hann (nodes i)
      (nodesOfFourClusterPoint_mem_active A hA v hcard i)
    rw [eval_sub, nodalQuartic_eval_node]
    dsimp only [r, lambda]
    rw [eval_sub, eval_mul, eval_C]
    rw [hroot]
    ring
  have hzero : r - FourNode.nodalQuartic lambda = 0 :=
    eq_zero_of_natDegree_lt_card_of_eval_eq_zero
      (r - FourNode.nodalQuartic lambda)
      (fun i j hij ↦
        (nodesOfFourClusterPoint_injective A hA v hcard)
          (Subtype.ext hij)) heval (by simpa using hdegree)
  have hrEq : r = FourNode.nodalQuartic lambda := sub_eq_zero.mp hzero
  change p.toPolynomial * q.toPolynomial =
    FourNode.nodalQuartic lambda + C H
  dsimp only [r] at hrEq
  exact sub_eq_iff_eq_add.mp hrEq

private theorem mem_range_of_nodalQuartic_eval_eq_zero
    (lambda : Fin 4 → ℝ) (x : ℝ)
    (hzero : (FourNode.nodalQuartic lambda).eval x = 0) :
    x ∈ Set.range lambda := by
  rw [FourNode.nodalQuartic, eval_prod] at hzero
  rw [Finset.prod_eq_zero_iff] at hzero
  simp only [Finset.mem_univ, eval_sub, eval_X, eval_C, true_and] at hzero
  obtain ⟨i, hi⟩ := hzero
  exact ⟨i, sub_eq_zero.mp hi |>.symm⟩

/-- Every active eigenvalue of another vector satisfying the same
annihilator is one of the four principal nodes. -/
theorem active_subset_range_of_common_fourNode_annihilator
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v : E)
    (nodes : Fin 4 → A.Eigenvalues)
    (p q : MonicQuadratic) (H : ℝ)
    (hfactor : p.toPolynomial * q.toPolynomial =
      FourNode.nodalQuartic
          (fun i ↦ ((nodes i : A.Eigenvalues) : ℝ)) + C H)
    (hann : polyApply A
      (p.toPolynomial * q.toPolynomial - C H) v = 0) :
    ∀ mu ∈ active A hA v, mu ∈ Set.range nodes := by
  intro mu hmu
  have hproduct := factor_eval_eq_of_mem_active_of_limitEquation
    A hA v p q H hann mu hmu
  have heval := congrArg (Polynomial.eval (mu : ℝ)) hfactor
  have hzero : (FourNode.nodalQuartic
      (fun i ↦ ((nodes i : A.Eigenvalues) : ℝ))).eval (mu : ℝ) = 0 := by
    simp only [eval_mul, eval_add, eval_C] at heval
    linarith
  obtain ⟨i, hi⟩ := mem_range_of_nodalQuartic_eval_eq_zero
    (fun j ↦ ((nodes j : A.Eigenvalues) : ℝ)) (mu : ℝ) hzero
  refine ⟨i, Subtype.ext ?_⟩
  exact hi

/-- A continuous observable which is constant on the full cluster set of a
precompact sequence converges to that constant. -/
theorem tendsto_of_continuous_eq_on_clusterSet
    {X Y : Type*} [MetricSpace X] [TopologicalSpace Y]
    (u : ℕ → X) (hu : IsCompact (closure (Set.range u)))
    (f : X → Y) (hf : Continuous f) (y : Y)
    (hcluster : ∀ x ∈ clusterSet u, f x = y) :
    Tendsto (fun n ↦ f (u n)) atTop (nhds y) := by
  rw [tendsto_def]
  intro s hs
  have hpre : f ⁻¹' s ∈ nhdsSet (clusterSet u) := by
    rw [mem_nhdsSet_iff_forall]
    intro x hx
    apply (hf.tendsto x)
    simpa only [hcluster x hx] using hs
  exact clusterSet_tendsto_nhdsSet hu hpre

/-- If every cluster point is supported on four selected nodes, then each
unselected grouped weight tends to zero.  This is qualitative exterior
decay only; no rate is used. -/
theorem weight_tendsto_zero_of_cluster_support
    (A : Module.End ℝ E) (hA : A.IsSymmetric)
    (u : ℕ → E) (hu : IsCompact (closure (Set.range u)))
    (nodes : Fin 4 → A.Eigenvalues)
    (hsupport : ∀ v ∈ clusterSet u, ∀ mu ∈ active A hA v,
      mu ∈ Set.range nodes)
    (mu : A.Eigenvalues) (hmu : mu ∉ Set.range nodes) :
    Tendsto (fun k ↦ weight A hA (u k) mu) atTop (nhds 0) := by
  apply tendsto_of_continuous_eq_on_clusterSet u hu
    (fun v ↦ weight A hA v mu) (continuous_weight A hA mu) 0
  intro v hv
  have hcomponent : component A hA v mu = 0 := by
    rw [← not_ne_iff]
    intro hne
    exact hmu (hsupport v hv mu ((mem_active_iff A hA v mu).2 hne))
  rw [weight, hcomponent, norm_zero, zero_pow]
  norm_num

private theorem exteriorMass_eq_zero_of_supported
    (A : Module.End ℝ E) (hA : A.IsSymmetric)
    (nodes : Fin 4 → A.Eigenvalues) (v : E)
    (hsupport : ∀ mu ∈ active A hA v, mu ∈ Set.range nodes) :
    exteriorMass A hA nodes v = 0 := by
  rw [exteriorMass]
  apply Finset.sum_eq_zero
  intro mu hmu
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmu
  have hnotrange : mu ∉ Set.range nodes := by
    simpa only [principalSpectrum, Finset.mem_image, Finset.mem_univ,
      true_and, Set.mem_range] using hmu
  have hcomponent : component A hA v mu = 0 := by
    rw [← not_ne_iff]
    intro hne
    exact hnotrange
      (hsupport mu ((mem_active_iff A hA v mu).2 hne))
  rw [weight, hcomponent, norm_zero, zero_pow]
  norm_num

/-- A unit vector supported on the selected nodes has principal mass one. -/
theorem principalMass_eq_one_of_supported
    (A : Module.End ℝ E) (hA : A.IsSymmetric)
    (nodes : Fin 4 → A.Eigenvalues) (hnodes : Function.Injective nodes)
    (v : E) (hnorm : ‖v‖ = 1)
    (hsupport : ∀ mu ∈ active A hA v, mu ∈ Set.range nodes) :
    principalMass A hA nodes v = 1 := by
  have hdecomp := principalMass_add_exteriorMass
    A hA nodes hnodes v
  rw [exteriorMass_eq_zero_of_supported A hA nodes v hsupport,
    add_zero, hnorm, one_pow] at hdecomp
  exact hdecomp

private theorem weight_pos_iff_mem_active
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v : E)
    (mu : A.Eigenvalues) :
    0 < weight A hA v mu ↔ mu ∈ active A hA v := by
  constructor
  · intro hpos
    rw [mem_active_iff]
    intro hzero
    have hweight : weight A hA v mu = 0 := by
      simp [weight, hzero]
    rw [hweight] at hpos
    exact (lt_irrefl 0) hpos
  · intro hmu
    rw [weight]
    exact sq_pos_of_pos
      (norm_pos_iff.mpr ((mem_active_iff A hA v mu).1 hmu))

/-- Boundary-capable normalized principal weights of a supported unit
vector.  Unlike `principalWeights`, this construction permits exactly one
zero selected component. -/
def clusterPrincipalWeights
    (A : Module.End ℝ E) (hA : A.IsSymmetric)
    (nodes : Fin 4 → A.Eigenvalues) (hnodes : Function.Injective nodes)
    (v : E) (hnorm : ‖v‖ = 1) (hgrade : 3 ≤ grade A v)
    (hsupport : ∀ mu ∈ active A hA v, mu ∈ Set.range nodes) :
    FourNode.Weights where
  weight := fun i ↦ weight A hA v (nodes i)
  nonneg := fun i ↦ weight_nonneg A hA v (nodes i)
  sum_eq_one := by
    simpa only [principalMass] using
      principalMass_eq_one_of_supported A hA nodes hnodes v hnorm hsupport
  three_le_card_positive := by
    let s : Finset (Fin 4) :=
      Finset.univ.filter fun i ↦ 0 < weight A hA v (nodes i)
    have hactive : active A hA v = s.image nodes := by
      ext mu
      constructor
      · intro hmu
        obtain ⟨i, rfl⟩ := hsupport mu hmu
        rw [Finset.mem_image]
        exact ⟨i, by
          simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
          exact (weight_pos_iff_mem_active A hA v (nodes i)).2 hmu,
          rfl⟩
      · intro hmu
        rw [Finset.mem_image] at hmu
        obtain ⟨i, hi, rfl⟩ := hmu
        apply (weight_pos_iff_mem_active A hA v (nodes i)).1
        simpa only [s, Finset.mem_filter, Finset.mem_univ, true_and] using hi
    have hcard : (active A hA v).card = s.card := by
      rw [hactive]
      exact Finset.card_image_of_injective s hnodes
    have hthree : 3 ≤ (active A hA v).card := by
      rwa [← grade_eq_card_active A hA v]
    change 3 ≤ s.card
    rwa [← hcard]

@[simp]
theorem clusterPrincipalWeights_apply
    (A : Module.End ℝ E) (hA : A.IsSymmetric)
    (nodes : Fin 4 → A.Eigenvalues) (hnodes : Function.Injective nodes)
    (v : E) (hnorm : ‖v‖ = 1) (hgrade : 3 ≤ grade A v)
    (hsupport : ∀ mu ∈ active A hA v, mu ∈ Set.range nodes)
    (i : Fin 4) :
    clusterPrincipalWeights A hA nodes hnodes v hnorm hgrade hsupport i =
      weight A hA v (nodes i) :=
  rfl

/-- The boundary-capable package really is the normalized selected weight
vector. -/
theorem clusterPrincipalWeights_eq_normalizedPrincipalWeight
    (A : Module.End ℝ E) (hA : A.IsSymmetric)
    (nodes : Fin 4 → A.Eigenvalues) (hnodes : Function.Injective nodes)
    (v : E) (hnorm : ‖v‖ = 1) (hgrade : 3 ≤ grade A v)
    (hsupport : ∀ mu ∈ active A hA v, mu ∈ Set.range nodes)
    (i : Fin 4) :
    clusterPrincipalWeights A hA nodes hnodes v hnorm hgrade hsupport i =
      normalizedPrincipalWeight A hA nodes v i := by
  rw [clusterPrincipalWeights_apply, normalizedPrincipalWeight,
    principalMass_eq_one_of_supported A hA nodes hnodes v hnorm hsupport,
    div_one]

private theorem sum_nodes_weight_mul_eq_full_sum
    (A : Module.End ℝ E) (hA : A.IsSymmetric)
    (nodes : Fin 4 → A.Eigenvalues) (hnodes : Function.Injective nodes)
    (v : E)
    (hsupport : ∀ mu ∈ active A hA v, mu ∈ Set.range nodes)
    (f : A.Eigenvalues → ℝ) :
    ∑ i, weight A hA v (nodes i) * f (nodes i) =
      ∑ mu, weight A hA v mu * f mu := by
  calc
    ∑ i, weight A hA v (nodes i) * f (nodes i) =
        ∑ mu ∈ principalSpectrum A nodes, weight A hA v mu * f mu := by
      rw [principalSpectrum]
      exact (Finset.sum_image
        (f := fun mu ↦ weight A hA v mu * f mu) hnodes.injOn).symm
    _ = ∑ mu, weight A hA v mu * f mu := by
      apply Finset.sum_subset (Finset.subset_univ (principalSpectrum A nodes))
      intro mu _ hmu
      have hnotrange : mu ∉ Set.range nodes := by
        simpa only [principalSpectrum, Finset.mem_image, Finset.mem_univ,
          true_and, Set.mem_range] using hmu
      have hcomponent : component A hA v mu = 0 := by
        rw [← not_ne_iff]
        intro hne
        exact hnotrange
          (hsupport mu ((mem_active_iff A hA v mu).2 hne))
      simp [weight, hcomponent]

/-- Limiting grouped orthogonality identifies the finite-node Arnoldi
polynomial of a cluster point. -/
theorem P_clusterPrincipalWeights_eq
    (A : Module.End ℝ E) (hA : A.IsSymmetric)
    (nodes : Fin 4 → A.Eigenvalues) (hnodes : Function.Injective nodes)
    (v : E) (hnorm : ‖v‖ = 1) (hgrade : 3 ≤ grade A v)
    (hsupport : ∀ mu ∈ active A hA v, mu ∈ Set.range nodes)
    (p : MonicQuadratic) (horth : HasGroupedOrthogonality A hA p v) :
    FourNode.P (fun i ↦ ((nodes i : A.Eigenvalues) : ℝ))
        (clusterPrincipalWeights A hA nodes hnodes v hnorm hgrade hsupport) = p := by
  let lambda : Fin 4 → ℝ := fun i ↦ ((nodes i : A.Eigenvalues) : ℝ)
  let x := clusterPrincipalWeights A hA nodes hnodes v hnorm hgrade hsupport
  have hlambda : Function.Injective lambda := by
    intro i j hij
    exact hnodes (Subtype.ext hij)
  symm
  apply FourNode.eq_P_of_orthogonal hlambda x p
  · rw [FourNode.weightedPolyInner]
    simp only [eval_one, mul_one, x, clusterPrincipalWeights_apply]
    exact (sum_nodes_weight_mul_eq_full_sum A hA nodes hnodes v hsupport
      (fun mu ↦ p.toPolynomial.eval (mu : ℝ))).trans horth.1
  · rw [FourNode.weightedPolyInner]
    simp only [eval_X, x, clusterPrincipalWeights_apply]
    calc
      ∑ i, weight A hA v (nodes i) *
          p.toPolynomial.eval (lambda i) * lambda i =
          ∑ i, weight A hA v (nodes i) *
            (lambda i * p.toPolynomial.eval (lambda i)) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = ∑ mu, weight A hA v mu *
          ((mu : ℝ) * p.toPolynomial.eval (mu : ℝ)) := by
        exact sum_nodes_weight_mul_eq_full_sum
          A hA nodes hnodes v hsupport
            (fun mu ↦ (mu : ℝ) * p.toPolynomial.eval (mu : ℝ))
      _ = 0 := horth.2

/-- On the common quartic, the finite-node height of every supported
cluster point is the common value `tau²`. -/
theorem H_clusterPrincipalWeights_eq_tau_sq
    (A : Module.End ℝ E) (hA : A.IsSymmetric)
    (nodes : Fin 4 → A.Eigenvalues) (hnodes : Function.Injective nodes)
    (v : E) (hnorm : ‖v‖ = 1) (hgrade : 3 ≤ grade A v)
    (hsupport : ∀ mu ∈ active A hA v, mu ∈ Set.range nodes)
    (tau : ℝ) (p q : MonicQuadratic)
    (hfactor : p.toPolynomial * q.toPolynomial =
      FourNode.nodalQuartic
          (fun i ↦ ((nodes i : A.Eigenvalues) : ℝ)) + C (tau ^ 2))
    (horth : HasGroupedOrthogonality A hA p v) :
    FourNode.H (fun i ↦ ((nodes i : A.Eigenvalues) : ℝ))
      (clusterPrincipalWeights A hA nodes hnodes v hnorm hgrade hsupport) =
        tau ^ 2 := by
  let lambda : Fin 4 → ℝ := fun i ↦ ((nodes i : A.Eigenvalues) : ℝ)
  let x := clusterPrincipalWeights A hA nodes hnodes v hnorm hgrade hsupport
  have hlambda : Function.Injective lambda := by
    intro i j hij
    exact hnodes (Subtype.ext hij)
  have hP : FourNode.P lambda x = p :=
    P_clusterPrincipalWeights_eq A hA nodes hnodes v hnorm hgrade
      hsupport p horth
  have hone := FourNode.P_orthogonal_one hlambda x
  have hX := FourNode.P_orthogonal_X hlambda x
  rw [hP, FourNode.weightedPolyInner] at hone hX
  simp only [eval_one, mul_one] at hone
  simp only [eval_X] at hX
  have hdiff : ∑ i, x i * p.toPolynomial.eval (lambda i) *
      (p.toPolynomial.eval (lambda i) -
        q.toPolynomial.eval (lambda i)) = 0 := by
    calc
      ∑ i, x i * p.toPolynomial.eval (lambda i) *
          (p.toPolynomial.eval (lambda i) -
            q.toPolynomial.eval (lambda i)) =
          ∑ i, ((p.linearCoeff - q.linearCoeff) *
              (x i * p.toPolynomial.eval (lambda i) * lambda i) +
            (p.constantCoeff - q.constantCoeff) *
              (x i * p.toPolynomial.eval (lambda i))) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [MonicQuadratic.eval, MonicQuadratic.eval]
        ring
      _ = (p.linearCoeff - q.linearCoeff) *
            (∑ i, x i * p.toPolynomial.eval (lambda i) * lambda i) +
          (p.constantCoeff - q.constantCoeff) *
            (∑ i, x i * p.toPolynomial.eval (lambda i)) := by
        rw [Finset.sum_add_distrib]
        simp only [Finset.mul_sum]
      _ = 0 := by
        rw [hX, hone]
        ring
  change FourNode.weightedPolyInner lambda x
      (FourNode.P lambda x).toPolynomial
      (FourNode.P lambda x).toPolynomial = tau ^ 2
  rw [hP, FourNode.weightedPolyInner]
  calc
    ∑ i, x i * p.toPolynomial.eval (lambda i) *
        p.toPolynomial.eval (lambda i) =
        ∑ i, x i * p.toPolynomial.eval (lambda i) *
          q.toPolynomial.eval (lambda i) := by
      rw [← sub_eq_zero, ← Finset.sum_sub_distrib]
      simpa only [mul_sub] using hdiff
    _ = ∑ i, x i * (tau ^ 2) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [mul_assoc, FourNode.factor_eval_mul_eq_tau_sq hfactor i]
    _ = tau ^ 2 := by
      rw [← Finset.sum_mul, x.sum_eq_one, one_mul]

/-- Every normalized cluster weight lies in the exact positive fiber at its
intrinsic four-node parameter. -/
theorem clusterPrincipalWeights_memFiber
    (A : Module.End ℝ E) (hA : A.IsSymmetric)
    (nodes : Fin 4 → A.Eigenvalues) (hnodes : Function.Injective nodes)
    (v : E) (hnorm : ‖v‖ = 1) (hgrade : 3 ≤ grade A v)
    (hsupport : ∀ mu ∈ active A hA v, mu ∈ Set.range nodes)
    (tau : ℝ) (htau : 0 < tau) (p q : MonicQuadratic)
    (hfactor : p.toPolynomial * q.toPolynomial =
      FourNode.nodalQuartic
          (fun i ↦ ((nodes i : A.Eigenvalues) : ℝ)) + C (tau ^ 2))
    (horth : HasGroupedOrthogonality A hA p v) :
    let lambda : Fin 4 → ℝ :=
      fun i ↦ ((nodes i : A.Eigenvalues) : ℝ)
    let x := clusterPrincipalWeights A hA nodes hnodes v hnorm hgrade hsupport
    FourNode.MemFiber lambda tau (FourNode.rho lambda x) p x := by
  dsimp only
  let lambda : Fin 4 → ℝ := fun i ↦ ((nodes i : A.Eigenvalues) : ℝ)
  let x := clusterPrincipalWeights A hA nodes hnodes v hnorm hgrade hsupport
  have hlambda : Function.Injective lambda := by
    intro i j hij
    exact hnodes (Subtype.ext hij)
  have hP : FourNode.P lambda x = p :=
    P_clusterPrincipalWeights_eq A hA nodes hnodes v hnorm hgrade
      hsupport p horth
  have hH : FourNode.H lambda x = tau ^ 2 :=
    H_clusterPrincipalWeights_eq_tau_sq A hA nodes hnodes v hnorm hgrade
      hsupport tau p q hfactor horth
  intro i
  have hid := FourNode.weight_mul_P_eval_eq_height_mul_sub_rho_div_E
    hlambda x i
  rw [hP, hH] at hid
  have hE := FourNode.E_ne_zero hlambda i
  have hp := (FourNode.factor_eval_ne_zero htau hfactor i).1
  rw [FourNode.fiberWeight]
  apply (eq_div_iff (mul_ne_zero hE hp)).2
  have hcleared := (eq_div_iff hE).1 hid
  calc
    x i * (FourNode.E lambda i * p.toPolynomial.eval (lambda i)) =
        (x i * p.toPolynomial.eval (lambda i)) * FourNode.E lambda i := by
      ring
    _ = tau ^ 2 * (lambda i - FourNode.rho lambda x) := hcleared

/-- Set-valued form of `clusterPrincipalWeights_memFiber`. -/
theorem clusterPrincipalWeights_mem_positiveFiber
    (A : Module.End ℝ E) (hA : A.IsSymmetric)
    (nodes : Fin 4 → A.Eigenvalues) (hnodes : Function.Injective nodes)
    (v : E) (hnorm : ‖v‖ = 1) (hgrade : 3 ≤ grade A v)
    (hsupport : ∀ mu ∈ active A hA v, mu ∈ Set.range nodes)
    (tau : ℝ) (htau : 0 < tau) (p q : MonicQuadratic)
    (hfactor : p.toPolynomial * q.toPolynomial =
      FourNode.nodalQuartic
          (fun i ↦ ((nodes i : A.Eigenvalues) : ℝ)) + C (tau ^ 2))
    (horth : HasGroupedOrthogonality A hA p v) :
    let lambda : Fin 4 → ℝ :=
      fun i ↦ ((nodes i : A.Eigenvalues) : ℝ)
    let x := clusterPrincipalWeights A hA nodes hnodes v hnorm hgrade hsupport
    x ∈ FourNode.positiveFiber lambda tau (FourNode.rho lambda x) p :=
  clusterPrincipalWeights_memFiber A hA nodes hnodes v hnorm hgrade
    hsupport tau htau p q hfactor horth

/-- A grade-four point in either parity cluster set canonically identifies
the common limiting quartic with its four active eigenvalues. -/
theorem fourNode_factorization_of_mem_parityClusterSet
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v₀ : E)
    (hv₀ : ‖v₀‖ = 1) (hgrade₀ : 3 ≤ grade A v₀)
    (tau : ℝ) (p q : MonicQuadratic)
    (hp : Tendsto
      (fun n ↦ (arnoldiFactorOrbit2 A v₀ (2 * n)).coeffPair)
      atTop (nhds p.coeffPair))
    (hq : Tendsto
      (fun n ↦ (arnoldiFactorOrbit2 A v₀ (2 * n + 1)).coeffPair)
      atTop (nhds q.coeffPair))
    (hsigma : Tendsto (arnoldiNormalizerOrbit2 A v₀)
      atTop (nhds tau))
    (vStar : E)
    (hvStar : vStar ∈ clusterSet
        (fun k ↦ arnoldiOrbit2 A v₀ (2 * k)) ∨
      vStar ∈ clusterSet
        (fun k ↦ arnoldiOrbit2 A v₀ (2 * k + 1)))
    (hcard : (active A hA vStar).card = 4) :
    p.toPolynomial * q.toPolynomial =
      FourNode.nodalQuartic
          (fun i ↦ ((nodesOfFourClusterPoint A hA vStar hcard i :
            A.Eigenvalues) : ℝ)) + C (tau ^ 2) := by
  apply quadraticProduct_eq_nodalQuartic_add_C_of_active_card_four
    A hA vStar p q (tau ^ 2) hcard
  rcases hvStar with hEven | hOdd
  · exact even_limit_equation_of_mem_arnoldiClusterSet
      A hA v₀ hv₀ hgrade₀ p q tau hp hq hsigma hEven
  · exact odd_limit_equation_of_mem_arnoldiClusterSet
      A hA v₀ hv₀ hgrade₀ p q tau hp hq hsigma hOdd

/-- Every even cluster point is supported on the common principal nodes. -/
theorem active_subset_principalNodes_of_mem_evenClusterSet
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v₀ : E)
    (hv₀ : ‖v₀‖ = 1) (hgrade₀ : 3 ≤ grade A v₀)
    (tau : ℝ) (p q : MonicQuadratic)
    (hp : Tendsto
      (fun n ↦ (arnoldiFactorOrbit2 A v₀ (2 * n)).coeffPair)
      atTop (nhds p.coeffPair))
    (hq : Tendsto
      (fun n ↦ (arnoldiFactorOrbit2 A v₀ (2 * n + 1)).coeffPair)
      atTop (nhds q.coeffPair))
    (hsigma : Tendsto (arnoldiNormalizerOrbit2 A v₀)
      atTop (nhds tau))
    (nodes : Fin 4 → A.Eigenvalues)
    (hfactor : p.toPolynomial * q.toPolynomial =
      FourNode.nodalQuartic
          (fun i ↦ ((nodes i : A.Eigenvalues) : ℝ)) + C (tau ^ 2))
    {v : E}
    (hv : v ∈ clusterSet (fun k ↦ arnoldiOrbit2 A v₀ (2 * k))) :
    ∀ mu ∈ active A hA v, mu ∈ Set.range nodes := by
  exact active_subset_range_of_common_fourNode_annihilator
    A hA v nodes p q (tau ^ 2) hfactor
      (even_limit_equation_of_mem_arnoldiClusterSet
        A hA v₀ hv₀ hgrade₀ p q tau hp hq hsigma hv)

/-- Every odd cluster point is supported on the same principal nodes. -/
theorem active_subset_principalNodes_of_mem_oddClusterSet
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v₀ : E)
    (hv₀ : ‖v₀‖ = 1) (hgrade₀ : 3 ≤ grade A v₀)
    (tau : ℝ) (p q : MonicQuadratic)
    (hp : Tendsto
      (fun n ↦ (arnoldiFactorOrbit2 A v₀ (2 * n)).coeffPair)
      atTop (nhds p.coeffPair))
    (hq : Tendsto
      (fun n ↦ (arnoldiFactorOrbit2 A v₀ (2 * n + 1)).coeffPair)
      atTop (nhds q.coeffPair))
    (hsigma : Tendsto (arnoldiNormalizerOrbit2 A v₀)
      atTop (nhds tau))
    (nodes : Fin 4 → A.Eigenvalues)
    (hfactor : p.toPolynomial * q.toPolynomial =
      FourNode.nodalQuartic
          (fun i ↦ ((nodes i : A.Eigenvalues) : ℝ)) + C (tau ^ 2))
    {v : E}
    (hv : v ∈ clusterSet
      (fun k ↦ arnoldiOrbit2 A v₀ (2 * k + 1))) :
    ∀ mu ∈ active A hA v, mu ∈ Set.range nodes := by
  exact active_subset_range_of_common_fourNode_annihilator
    A hA v nodes p q (tau ^ 2) hfactor
      (odd_limit_equation_of_mem_arnoldiClusterSet
        A hA v₀ hv₀ hgrade₀ p q tau hp hq hsigma hv)

/-- Every exterior grouped weight tends to zero along the even parity. -/
theorem even_exterior_weight_tendsto_zero
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v₀ : E)
    (hv₀ : ‖v₀‖ = 1) (hgrade₀ : 3 ≤ grade A v₀)
    (tau : ℝ) (p q : MonicQuadratic)
    (hp : Tendsto
      (fun n ↦ (arnoldiFactorOrbit2 A v₀ (2 * n)).coeffPair)
      atTop (nhds p.coeffPair))
    (hq : Tendsto
      (fun n ↦ (arnoldiFactorOrbit2 A v₀ (2 * n + 1)).coeffPair)
      atTop (nhds q.coeffPair))
    (hsigma : Tendsto (arnoldiNormalizerOrbit2 A v₀)
      atTop (nhds tau))
    (nodes : Fin 4 → A.Eigenvalues)
    (hfactor : p.toPolynomial * q.toPolynomial =
      FourNode.nodalQuartic
          (fun i ↦ ((nodes i : A.Eigenvalues) : ℝ)) + C (tau ^ 2))
    (mu : A.Eigenvalues) (hmu : mu ∉ Set.range nodes) :
    Tendsto (fun k ↦ weight A hA
      (arnoldiOrbit2 A v₀ (2 * k)) mu) atTop (nhds 0) := by
  apply weight_tendsto_zero_of_cluster_support A hA
    (fun k ↦ arnoldiOrbit2 A v₀ (2 * k))
  · simpa only [Nat.add_zero] using
      isCompact_closure_range_arnoldiParity
        A hA v₀ hv₀ hgrade₀ 0
  · intro v hv
    exact active_subset_principalNodes_of_mem_evenClusterSet
      A hA v₀ hv₀ hgrade₀ tau p q hp hq hsigma nodes hfactor hv
  · exact hmu

/-- Every exterior grouped weight tends to zero along the odd parity. -/
theorem odd_exterior_weight_tendsto_zero
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v₀ : E)
    (hv₀ : ‖v₀‖ = 1) (hgrade₀ : 3 ≤ grade A v₀)
    (tau : ℝ) (p q : MonicQuadratic)
    (hp : Tendsto
      (fun n ↦ (arnoldiFactorOrbit2 A v₀ (2 * n)).coeffPair)
      atTop (nhds p.coeffPair))
    (hq : Tendsto
      (fun n ↦ (arnoldiFactorOrbit2 A v₀ (2 * n + 1)).coeffPair)
      atTop (nhds q.coeffPair))
    (hsigma : Tendsto (arnoldiNormalizerOrbit2 A v₀)
      atTop (nhds tau))
    (nodes : Fin 4 → A.Eigenvalues)
    (hfactor : p.toPolynomial * q.toPolynomial =
      FourNode.nodalQuartic
          (fun i ↦ ((nodes i : A.Eigenvalues) : ℝ)) + C (tau ^ 2))
    (mu : A.Eigenvalues) (hmu : mu ∉ Set.range nodes) :
    Tendsto (fun k ↦ weight A hA
      (arnoldiOrbit2 A v₀ (2 * k + 1)) mu) atTop (nhds 0) := by
  apply weight_tendsto_zero_of_cluster_support A hA
    (fun k ↦ arnoldiOrbit2 A v₀ (2 * k + 1))
  · exact isCompact_closure_range_arnoldiParity
      A hA v₀ hv₀ hgrade₀ 1
  · intro v hv
    exact active_subset_principalNodes_of_mem_oddClusterSet
      A hA v₀ hv₀ hgrade₀ tau p q hp hq hsigma nodes hfactor hv
  · exact hmu

/-- The total exterior mass tends to zero along the even parity. -/
theorem even_exteriorMass_tendsto_zero
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v₀ : E)
    (hv₀ : ‖v₀‖ = 1) (hgrade₀ : 3 ≤ grade A v₀)
    (tau : ℝ) (p q : MonicQuadratic)
    (hp : Tendsto
      (fun n ↦ (arnoldiFactorOrbit2 A v₀ (2 * n)).coeffPair)
      atTop (nhds p.coeffPair))
    (hq : Tendsto
      (fun n ↦ (arnoldiFactorOrbit2 A v₀ (2 * n + 1)).coeffPair)
      atTop (nhds q.coeffPair))
    (hsigma : Tendsto (arnoldiNormalizerOrbit2 A v₀)
      atTop (nhds tau))
    (nodes : Fin 4 → A.Eigenvalues)
    (hfactor : p.toPolynomial * q.toPolynomial =
      FourNode.nodalQuartic
          (fun i ↦ ((nodes i : A.Eigenvalues) : ℝ)) + C (tau ^ 2)) :
    Tendsto (fun k ↦ exteriorMass A hA nodes
      (arnoldiOrbit2 A v₀ (2 * k))) atTop (nhds 0) := by
  let exterior : Finset A.Eigenvalues :=
    Finset.univ.filter fun mu ↦ mu ∉ principalSpectrum A nodes
  have hsum : Tendsto
      (fun k ↦ ∑ mu ∈ exterior,
        weight A hA (arnoldiOrbit2 A v₀ (2 * k)) mu)
      atTop (nhds (∑ _mu ∈ exterior, (0 : ℝ))) := by
    apply tendsto_finsetSum exterior
    intro mu hmu
    have houtside : mu ∉ principalSpectrum A nodes := by
      simpa only [exterior, Finset.mem_filter, Finset.mem_univ,
        true_and] using hmu
    have hnotrange : mu ∉ Set.range nodes := by
      simpa only [principalSpectrum, Finset.mem_image, Finset.mem_univ,
        true_and, Set.mem_range] using houtside
    exact even_exterior_weight_tendsto_zero
      A hA v₀ hv₀ hgrade₀ tau p q hp hq hsigma nodes hfactor
        mu hnotrange
  simpa only [exteriorMass, exterior, Finset.sum_const_zero] using hsum

/-- The total exterior mass tends to zero along the odd parity. -/
theorem odd_exteriorMass_tendsto_zero
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v₀ : E)
    (hv₀ : ‖v₀‖ = 1) (hgrade₀ : 3 ≤ grade A v₀)
    (tau : ℝ) (p q : MonicQuadratic)
    (hp : Tendsto
      (fun n ↦ (arnoldiFactorOrbit2 A v₀ (2 * n)).coeffPair)
      atTop (nhds p.coeffPair))
    (hq : Tendsto
      (fun n ↦ (arnoldiFactorOrbit2 A v₀ (2 * n + 1)).coeffPair)
      atTop (nhds q.coeffPair))
    (hsigma : Tendsto (arnoldiNormalizerOrbit2 A v₀)
      atTop (nhds tau))
    (nodes : Fin 4 → A.Eigenvalues)
    (hfactor : p.toPolynomial * q.toPolynomial =
      FourNode.nodalQuartic
          (fun i ↦ ((nodes i : A.Eigenvalues) : ℝ)) + C (tau ^ 2)) :
    Tendsto (fun k ↦ exteriorMass A hA nodes
      (arnoldiOrbit2 A v₀ (2 * k + 1))) atTop (nhds 0) := by
  let exterior : Finset A.Eigenvalues :=
    Finset.univ.filter fun mu ↦ mu ∉ principalSpectrum A nodes
  have hsum : Tendsto
      (fun k ↦ ∑ mu ∈ exterior,
        weight A hA (arnoldiOrbit2 A v₀ (2 * k + 1)) mu)
      atTop (nhds (∑ _mu ∈ exterior, (0 : ℝ))) := by
    apply tendsto_finsetSum exterior
    intro mu hmu
    have houtside : mu ∉ principalSpectrum A nodes := by
      simpa only [exterior, Finset.mem_filter, Finset.mem_univ,
        true_and] using hmu
    have hnotrange : mu ∉ Set.range nodes := by
      simpa only [principalSpectrum, Finset.mem_image, Finset.mem_univ,
        true_and, Set.mem_range] using houtside
    exact odd_exterior_weight_tendsto_zero
      A hA v₀ hv₀ hgrade₀ tau p q hp hq hsigma nodes hfactor
        mu hnotrange
  simpa only [exteriorMass, exterior, Finset.sum_const_zero] using hsum

/-- Every even cluster point yields normalized principal weights in its
intrinsic `p`-fiber.  The existential packaging hides the norm/grade/support
proof terms while exposing the weight coordinates needed later. -/
theorem exists_evenClusterWeight_mem_positiveFiber
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v₀ : E)
    (hv₀ : ‖v₀‖ = 1) (hgrade₀ : 3 ≤ grade A v₀)
    (tau : ℝ) (htau : 0 < tau) (p q : MonicQuadratic)
    (hp : Tendsto
      (fun n ↦ (arnoldiFactorOrbit2 A v₀ (2 * n)).coeffPair)
      atTop (nhds p.coeffPair))
    (hq : Tendsto
      (fun n ↦ (arnoldiFactorOrbit2 A v₀ (2 * n + 1)).coeffPair)
      atTop (nhds q.coeffPair))
    (hsigma : Tendsto (arnoldiNormalizerOrbit2 A v₀)
      atTop (nhds tau))
    (nodes : Fin 4 → A.Eigenvalues) (hnodes : Function.Injective nodes)
    (hfactor : p.toPolynomial * q.toPolynomial =
      FourNode.nodalQuartic
          (fun i ↦ ((nodes i : A.Eigenvalues) : ℝ)) + C (tau ^ 2))
    {v : E}
    (hv : v ∈ clusterSet (fun k ↦ arnoldiOrbit2 A v₀ (2 * k))) :
    ∃ x : FourNode.Weights,
      (∀ i, x i = normalizedPrincipalWeight A hA nodes v i) ∧
      FourNode.P (fun i ↦ ((nodes i : A.Eigenvalues) : ℝ)) x = p ∧
      FourNode.H (fun i ↦ ((nodes i : A.Eigenvalues) : ℝ)) x = tau ^ 2 ∧
      x ∈ FourNode.positiveFiber
        (fun i ↦ ((nodes i : A.Eigenvalues) : ℝ)) tau
        (FourNode.rho (fun i ↦ ((nodes i : A.Eigenvalues) : ℝ)) x) p := by
  have hnorm := norm_eq_one_of_mem_arnoldiParityClusterSet
    A hA v₀ hv₀ hgrade₀ 0 (by simpa only [Nat.add_zero] using hv)
  have hgrade := grade_mem_even_arnoldiClusterSet
    A hA v₀ hv₀ hgrade₀ hv
  have hsupport := active_subset_principalNodes_of_mem_evenClusterSet
    A hA v₀ hv₀ hgrade₀ tau p q hp hq hsigma nodes hfactor hv
  let x := clusterPrincipalWeights
    A hA nodes hnodes v hnorm hgrade hsupport
  refine ⟨x, ?_, ?_, ?_, ?_⟩
  · intro i
    exact clusterPrincipalWeights_eq_normalizedPrincipalWeight
      A hA nodes hnodes v hnorm hgrade hsupport i
  · exact P_clusterPrincipalWeights_eq
      A hA nodes hnodes v hnorm hgrade hsupport p
        (even_grouped_orthogonality_of_mem_arnoldiClusterSet
          A hA v₀ hgrade₀ p hp hv)
  · exact H_clusterPrincipalWeights_eq_tau_sq
      A hA nodes hnodes v hnorm hgrade hsupport tau p q hfactor
        (even_grouped_orthogonality_of_mem_arnoldiClusterSet
          A hA v₀ hgrade₀ p hp hv)
  · exact clusterPrincipalWeights_mem_positiveFiber
      A hA nodes hnodes v hnorm hgrade hsupport tau htau p q hfactor
        (even_grouped_orthogonality_of_mem_arnoldiClusterSet
          A hA v₀ hgrade₀ p hp hv)

/-- Every odd cluster point yields normalized principal weights in its
intrinsic companion `q`-fiber. -/
theorem exists_oddClusterWeight_mem_positiveFiber
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v₀ : E)
    (hv₀ : ‖v₀‖ = 1) (hgrade₀ : 3 ≤ grade A v₀)
    (tau : ℝ) (htau : 0 < tau) (p q : MonicQuadratic)
    (hp : Tendsto
      (fun n ↦ (arnoldiFactorOrbit2 A v₀ (2 * n)).coeffPair)
      atTop (nhds p.coeffPair))
    (hq : Tendsto
      (fun n ↦ (arnoldiFactorOrbit2 A v₀ (2 * n + 1)).coeffPair)
      atTop (nhds q.coeffPair))
    (hsigma : Tendsto (arnoldiNormalizerOrbit2 A v₀)
      atTop (nhds tau))
    (nodes : Fin 4 → A.Eigenvalues) (hnodes : Function.Injective nodes)
    (hfactor : p.toPolynomial * q.toPolynomial =
      FourNode.nodalQuartic
          (fun i ↦ ((nodes i : A.Eigenvalues) : ℝ)) + C (tau ^ 2))
    {v : E}
    (hv : v ∈ clusterSet
      (fun k ↦ arnoldiOrbit2 A v₀ (2 * k + 1))) :
    ∃ x : FourNode.Weights,
      (∀ i, x i = normalizedPrincipalWeight A hA nodes v i) ∧
      FourNode.P (fun i ↦ ((nodes i : A.Eigenvalues) : ℝ)) x = q ∧
      FourNode.H (fun i ↦ ((nodes i : A.Eigenvalues) : ℝ)) x = tau ^ 2 ∧
      x ∈ FourNode.positiveFiber
        (fun i ↦ ((nodes i : A.Eigenvalues) : ℝ)) tau
        (FourNode.rho (fun i ↦ ((nodes i : A.Eigenvalues) : ℝ)) x) q := by
  have hnorm := norm_eq_one_of_mem_arnoldiParityClusterSet
    A hA v₀ hv₀ hgrade₀ 1 hv
  have hgrade := grade_mem_odd_arnoldiClusterSet
    A hA v₀ hv₀ hgrade₀ hv
  have hsupport := active_subset_principalNodes_of_mem_oddClusterSet
    A hA v₀ hv₀ hgrade₀ tau p q hp hq hsigma nodes hfactor hv
  have hfactor' : q.toPolynomial * p.toPolynomial =
      FourNode.nodalQuartic
          (fun i ↦ ((nodes i : A.Eigenvalues) : ℝ)) + C (tau ^ 2) := by
    simpa only [mul_comm] using hfactor
  let x := clusterPrincipalWeights
    A hA nodes hnodes v hnorm hgrade hsupport
  refine ⟨x, ?_, ?_, ?_, ?_⟩
  · intro i
    exact clusterPrincipalWeights_eq_normalizedPrincipalWeight
      A hA nodes hnodes v hnorm hgrade hsupport i
  · exact P_clusterPrincipalWeights_eq
      A hA nodes hnodes v hnorm hgrade hsupport q
        (odd_grouped_orthogonality_of_mem_arnoldiClusterSet
          A hA v₀ hgrade₀ q hq hv)
  · exact H_clusterPrincipalWeights_eq_tau_sq
      A hA nodes hnodes v hnorm hgrade hsupport tau q p hfactor'
        (odd_grouped_orthogonality_of_mem_arnoldiClusterSet
          A hA v₀ hgrade₀ q hq hv)
  · exact clusterPrincipalWeights_mem_positiveFiber
      A hA nodes hnodes v hnorm hgrade hsupport tau htau q p hfactor'
        (odd_grouped_orthogonality_of_mem_arnoldiClusterSet
          A hA v₀ hgrade₀ q hq hv)

end

end Spectral
end Forsythe
