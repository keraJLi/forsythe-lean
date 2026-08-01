import Forsythe.Dynamics.ClusterConvergence
import Forsythe.Spectral.LimitOrthogonality
import Forsythe.Spectral.Reduction
import Forsythe.Spectral.ThreeNodeConvergence
import Forsythe.Spectral.WeightConvergence

/-!
# Assembly of the three-node branch

A parity cluster set need not have one fixed three-node support a priori.
There are, however, only finitely many three-element subsets of the grouped
spectrum.  On each fixed support, normalization and the two limiting
orthogonality equations determine the squared component weights uniquely;
fixed component lines then leave only finitely many sign choices.  Taking the
finite union over all supports makes the whole cluster set finite, and its
connectedness forces parity convergence.
-/

set_option autoImplicit false

namespace Forsythe
namespace Spectral

open Filter Metric Module.End Polynomial Set Topology
open scoped BigOperators

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A canonical enumeration of a three-element grouped spectral support. -/
def nodesOfThreeSupport
    (A : Module.End ℝ E) (s : Finset A.Eigenvalues)
    (hs : s.card = 3) : Fin 3 → A.Eigenvalues :=
  fun i ↦ ((s.equivFinOfCardEq hs).symm i : s)

omit [FiniteDimensional ℝ E] in
theorem nodesOfThreeSupport_injective
    (A : Module.End ℝ E) (s : Finset A.Eigenvalues)
    (hs : s.card = 3) :
    Function.Injective (nodesOfThreeSupport A s hs) := by
  intro i j hij
  apply (s.equivFinOfCardEq hs).symm.injective
  exact Subtype.ext hij

omit [FiniteDimensional ℝ E] in
@[simp]
theorem nodesOfThreeSupport_mem
    (A : Module.End ℝ E) (s : Finset A.Eigenvalues)
    (hs : s.card = 3) (i : Fin 3) :
    nodesOfThreeSupport A s hs i ∈ s :=
  ((s.equivFinOfCardEq hs).symm i).property

omit [FiniteDimensional ℝ E] in
private theorem sum_nodesOfThreeSupport
    (A : Module.End ℝ E) (s : Finset A.Eigenvalues)
    (hs : s.card = 3) (f : A.Eigenvalues → ℝ) :
    ∑ i : Fin 3, f (nodesOfThreeSupport A s hs i) =
      ∑ mu ∈ s, f mu := by
  let e : Fin 3 ≃ s := (s.equivFinOfCardEq hs).symm
  calc
    ∑ i : Fin 3, f (nodesOfThreeSupport A s hs i) =
        ∑ mu : s, f mu := by
      exact Fintype.sum_equiv e
        (fun i : Fin 3 ↦ f (nodesOfThreeSupport A s hs i))
        (fun mu : s ↦ f mu) (fun _ ↦ rfl)
    _ = ∑ mu ∈ s, f mu :=
      (Finset.sum_subtype s (fun _ ↦ Iff.rfl) f).symm

private theorem sum_eq_sum_support_of_eq_zero_outside
    (A : Module.End ℝ E)
    (s : Finset A.Eigenvalues) (f : A.Eigenvalues → ℝ)
    (hzero : ∀ mu, mu ∉ s → f mu = 0) :
    (∑ mu, f mu) = ∑ mu ∈ s, f mu := by
  symm
  apply Finset.sum_subset (Finset.subset_univ s)
  intro mu _ hmu
  exact hzero mu hmu

private theorem component_eq_zero_of_active_eq
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v : E)
    (s : Finset A.Eigenvalues) (hactive : active A hA v = s)
    {mu : A.Eigenvalues} (hmu : mu ∉ s) :
    component A hA v mu = 0 := by
  by_contra hne
  have hmactive : mu ∈ active A hA v :=
    (mem_active_iff A hA v mu).mpr hne
  rw [hactive] at hmactive
  exact hmu hmactive

private theorem supportFiber_finite
    (A : Module.End ℝ E) (hA : A.IsSymmetric)
    (S : Set E) (direction : A.Eigenvalues → E)
    (p q : MonicQuadratic) {H : ℝ} (hH : H ≠ 0)
    (hnorm : ∀ v ∈ S, ‖v‖ = 1)
    (hline : ∀ v ∈ S, ∀ mu,
      (component A hA v mu : E) ∈ ℝ ∙ direction mu)
    (horth : ∀ v ∈ S, HasGroupedOrthogonality A hA p v)
    (hfactor : ∀ v ∈ S, ∀ mu ∈ active A hA v,
      p.toPolynomial.eval (mu : ℝ) *
        q.toPolynomial.eval (mu : ℝ) = H)
    (s : Finset A.Eigenvalues) (hs : s.card = 3) :
    {v | v ∈ S ∧ active A hA v = s}.Finite := by
  let F : Set E := {v | v ∈ S ∧ active A hA v = s}
  by_cases hF : F.Nonempty
  · have hFne := hF
    obtain ⟨v₀, hv₀S, hv₀active⟩ := hF
    let nodes : Fin 3 → A.Eigenvalues := nodesOfThreeSupport A s hs
    have hnodes : Function.Injective nodes :=
      nodesOfThreeSupport_injective A s hs
    have hlambda : Function.Injective
        (fun i ↦ ((nodes i : A.Eigenvalues) : ℝ)) := by
      intro i j hij
      apply hnodes
      exact Subtype.ext hij
    have hsupport : ∀ v ∈ F, ∀ mu,
        mu ∉ Set.range nodes → component A hA v mu = 0 := by
      intro v hv mu hmu
      have hnotmem : mu ∉ s := by
        intro hmus
        let a : s := ⟨mu, hmus⟩
        let i : Fin 3 := s.equivFinOfCardEq hs a
        apply hmu
        refine ⟨i, ?_⟩
        exact congrArg Subtype.val
          ((s.equivFinOfCardEq hs).symm_apply_apply a)
      exact component_eq_zero_of_active_eq A hA v s hv.2 hnotmem
    have hpq : ∀ i,
        p.toPolynomial.eval ((nodes i : A.Eigenvalues) : ℝ) *
          q.toPolynomial.eval ((nodes i : A.Eigenvalues) : ℝ) = H := by
      intro i
      apply hfactor v₀ hv₀S (nodes i)
      rw [hv₀active]
      exact nodesOfThreeSupport_mem A s hs i
    have hconstraints : ∀ v ∈ F,
        threeNodeWeightConstraints
            (fun i ↦ ((nodes i : A.Eigenvalues) : ℝ)) p
            (fun i ↦ ‖threeNodeComponents A hA nodes v i‖ ^ 2) =
          (1, (0, 0)) := by
      intro v hv
      have houtsideWeight : ∀ mu, mu ∉ s → weight A hA v mu = 0 := by
        intro mu hmu
        rw [weight, component_eq_zero_of_active_eq A hA v s hv.2 hmu,
          norm_zero, zero_pow]
        norm_num
      have hsum : (∑ i : Fin 3, weight A hA v (nodes i)) = 1 := by
        calc
          ∑ i : Fin 3, weight A hA v (nodes i) =
              ∑ mu ∈ s, weight A hA v mu :=
            sum_nodesOfThreeSupport A s hs (weight A hA v)
          _ = ∑ mu, weight A hA v mu :=
            (sum_eq_sum_support_of_eq_zero_outside A s
              (weight A hA v) houtsideWeight).symm
          _ = ‖v‖ ^ 2 := sum_weight_eq_norm_sq A hA v
          _ = 1 := by rw [hnorm v hv.1, one_pow]
      have hpFull := (horth v hv.1).1
      have hpSum :
          (∑ i : Fin 3, weight A hA v (nodes i) *
            p.toPolynomial.eval ((nodes i : A.Eigenvalues) : ℝ)) = 0 := by
        let f : A.Eigenvalues → ℝ := fun mu ↦
          weight A hA v mu * p.toPolynomial.eval (mu : ℝ)
        calc
          ∑ i : Fin 3, weight A hA v (nodes i) *
              p.toPolynomial.eval ((nodes i : A.Eigenvalues) : ℝ) =
              ∑ mu ∈ s, f mu :=
            sum_nodesOfThreeSupport A s hs f
          _ = ∑ mu, f mu :=
            (sum_eq_sum_support_of_eq_zero_outside A s f (by
              intro mu hmu
              dsimp only [f]
              rw [houtsideWeight mu hmu, zero_mul])).symm
          _ = 0 := hpFull
      have hXPFull := (horth v hv.1).2
      have hXPSum :
          (∑ i : Fin 3, weight A hA v (nodes i) *
            (((nodes i : A.Eigenvalues) : ℝ) *
              p.toPolynomial.eval ((nodes i : A.Eigenvalues) : ℝ))) = 0 := by
        let f : A.Eigenvalues → ℝ := fun mu ↦
          weight A hA v mu *
            ((mu : ℝ) * p.toPolynomial.eval (mu : ℝ))
        calc
          ∑ i : Fin 3, weight A hA v (nodes i) *
              (((nodes i : A.Eigenvalues) : ℝ) *
                p.toPolynomial.eval ((nodes i : A.Eigenvalues) : ℝ)) =
              ∑ mu ∈ s, f mu :=
            sum_nodesOfThreeSupport A s hs f
          _ = ∑ mu, f mu :=
            (sum_eq_sum_support_of_eq_zero_outside A s f (by
              intro mu hmu
              dsimp only [f]
              rw [houtsideWeight mu hmu, zero_mul])).symm
          _ = 0 := hXPFull
      change threeNodeWeightConstraints
          (fun i ↦ ((nodes i : A.Eigenvalues) : ℝ)) p
          (fun i ↦ weight A hA v (nodes i)) = (1, (0, 0))
      simp only [threeNodeWeightConstraints, hsum, hpSum, hXPSum]
    exact finite_of_threeNode_component_constraints
      F hFne (threeNodeComponents A hA nodes)
      (threeNodeComponents_injOn_of_supported A hA nodes F hsupport)
      (fun i ↦ direction (nodes i))
      (fun i ↦ ((nodes i : A.Eigenvalues) : ℝ)) hlambda
      p q hH hpq
      (fun v hv i ↦ hline v hv.1 (nodes i)) hconstraints
  · have hEmpty : F = ∅ := Set.not_nonempty_iff_eq_empty.mp hF
    simpa only [F, hEmpty] using (Set.finite_empty : (∅ : Set E).Finite)

/-- Allowing all finitely many three-node supports still leaves only
finitely many vectors satisfying normalization, limiting orthogonality, the
common factor equation, and the fixed-line condition. -/
theorem finite_of_active_card_three_and_grouped_orthogonality
    (A : Module.End ℝ E) (hA : A.IsSymmetric)
    (S : Set E) (direction : A.Eigenvalues → E)
    (p q : MonicQuadratic) {H : ℝ} (hH : H ≠ 0)
    (hnorm : ∀ v ∈ S, ‖v‖ = 1)
    (hactive : ∀ v ∈ S, (active A hA v).card = 3)
    (hline : ∀ v ∈ S, ∀ mu,
      (component A hA v mu : E) ∈ ℝ ∙ direction mu)
    (horth : ∀ v ∈ S, HasGroupedOrthogonality A hA p v)
    (hfactor : ∀ v ∈ S, ∀ mu ∈ active A hA v,
      p.toPolynomial.eval (mu : ℝ) *
        q.toPolynomial.eval (mu : ℝ) = H) :
    S.Finite := by
  let fiber : Finset A.Eigenvalues → Set E := fun s ↦
    {v | v ∈ S ∧ active A hA v = s}
  have hfiber : ∀ s, (fiber s).Finite := by
    intro s
    by_cases hs : s.card = 3
    · exact supportFiber_finite A hA S direction p q hH hnorm hline
        horth hfactor s hs
    · have hempty : fiber s = ∅ := by
        ext v
        constructor
        · intro hv
          exact (hs ((hv.2 ▸ hactive v hv.1))).elim
        · intro hv
          exact hv.elim
      rw [hempty]
      exact Set.finite_empty
  have hunion : (⋃ s, fiber s) = S := by
    ext v
    simp only [mem_iUnion, fiber]
    constructor
    · rintro ⟨s, hv, -⟩
      exact hv
    · intro hv
      exact ⟨active A hA v, hv, rfl⟩
  rw [← hunion]
  exact Set.finite_iUnion hfiber

/-- Abstract convergence theorem for a compact, connected three-node parity
cluster set. -/
theorem exists_tendsto_of_threeNode_parity_clusterSet
    (A : Module.End ℝ E) (hA : A.IsSymmetric)
    (u : ℕ → E) (hu : IsCompact (closure (range u)))
    (hconnected : IsConnected (clusterSet u))
    (direction : A.Eigenvalues → E)
    (p q : MonicQuadratic) {H : ℝ} (hH : H ≠ 0)
    (hnorm : ∀ v ∈ clusterSet u, ‖v‖ = 1)
    (hactive : ∀ v ∈ clusterSet u, (active A hA v).card = 3)
    (hline : ∀ v ∈ clusterSet u, ∀ mu,
      (component A hA v mu : E) ∈ ℝ ∙ direction mu)
    (horth : ∀ v ∈ clusterSet u,
      HasGroupedOrthogonality A hA p v)
    (hfactor : ∀ v ∈ clusterSet u, ∀ mu ∈ active A hA v,
      p.toPolynomial.eval (mu : ℝ) *
        q.toPolynomial.eval (mu : ℝ) = H) :
    ∃ v, Tendsto u atTop (nhds v) := by
  apply exists_tendsto_of_finite_connected_clusterSet u hu
  · exact finite_of_active_card_three_and_grouped_orthogonality
      A hA (clusterSet u) direction p q hH hnorm hactive hline horth hfactor
  · exact hconnected

/-- Compactness of the full Arnoldi orbit restricts to every explicitly
indexed parity subsequence. -/
theorem isCompact_closure_range_arnoldiParity
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v₀ : E)
    (hv₀ : ‖v₀‖ = 1) (hgrade₀ : 3 ≤ grade A v₀) (r : ℕ) :
    IsCompact (closure (range fun k ↦ arnoldiOrbit2 A v₀ (2 * k + r))) := by
  apply (isCompact_closure_range_arnoldiOrbit2
    A hA v₀ hv₀ hgrade₀).of_isClosed_subset isClosed_closure
  apply closure_minimal _ isClosed_closure
  rintro v ⟨k, rfl⟩
  exact subset_closure ⟨2 * k + r, rfl⟩

/-- Unit norm passes to every parity cluster point. -/
theorem norm_eq_one_of_mem_arnoldiParityClusterSet
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v₀ : E)
    (hv₀ : ‖v₀‖ = 1) (hgrade₀ : 3 ≤ grade A v₀) (r : ℕ)
    {v : E}
    (hv : v ∈ clusterSet
      (fun k ↦ arnoldiOrbit2 A v₀ (2 * k + r))) :
    ‖v‖ = 1 := by
  let unitSphere : Set E := {w | ‖w‖ = 1}
  have hclosed : IsClosed unitSphere :=
    isClosed_eq continuous_norm continuous_const
  apply hclosed.mem_of_mapClusterPt hv
  exact Eventually.of_forall fun k ↦ by
    change ‖arnoldiOrbit2 A v₀ (2 * k + r)‖ = 1
    exact norm_arnoldiOrbit2_of_initial_grade_three
      A hA v₀ hv₀ hgrade₀ (2 * k + r)

/-- Every component of a parity cluster point remains on the real line of
the corresponding initial grouped eigenspace component. -/
theorem component_mem_span_initial_of_mem_arnoldiParityClusterSet
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v₀ : E)
    (r : ℕ) {v : E}
    (hv : v ∈ clusterSet
      (fun k ↦ arnoldiOrbit2 A v₀ (2 * k + r)))
    (mu : A.Eigenvalues) :
    (component A hA v mu : E) ∈
      ℝ ∙ (component A hA v₀ mu : E) := by
  let L : Submodule ℝ E := ℝ ∙ (component A hA v₀ mu : E)
  have hclosed : IsClosed (L : Set E) := L.closed_of_finiteDimensional
  have hcontinuous : Continuous
      (fun w : E ↦ (component A hA w mu : E)) := by
    unfold component
    fun_prop
  have hpreclosed : IsClosed
      {w : E | (component A hA w mu : E) ∈ L} :=
    hclosed.preimage hcontinuous
  exact hpreclosed.mem_of_mapClusterPt hv
    (Eventually.of_forall fun k ↦ by
      change (component A hA
        (arnoldiOrbit2 A v₀ (2 * k + r)) mu : E) ∈ L
      simpa only [L] using component_arnoldiOrbit2_mem_span_initial
        A hA v₀ mu (2 * k + r))

/-- Evaluating a polynomial annihilator on a nonzero grouped component
forces the scalar polynomial to vanish at that active eigenvalue. -/
theorem factor_eval_eq_of_mem_active_of_limitEquation
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v : E)
    (p q : MonicQuadratic) (H : ℝ)
    (hann : polyApply A
      (p.toPolynomial * q.toPolynomial - C H) v = 0)
    (mu : A.Eigenvalues) (hmu : mu ∈ active A hA v) :
    p.toPolynomial.eval (mu : ℝ) *
      q.toPolynomial.eval (mu : ℝ) = H := by
  have hcomponent := congrArg
    (fun w : E ↦ component A hA w mu) hann
  rw [component_polyApply] at hcomponent
  have hzero : component A hA (0 : E) mu = 0 := by
    simp [component]
  rw [hzero] at hcomponent
  have hcomponentNe : component A hA v mu ≠ 0 :=
    (mem_active_iff A hA v mu).mp hmu
  have heval :
      (p.toPolynomial * q.toPolynomial - C H).eval (mu : ℝ) = 0 :=
    (smul_eq_zero.mp hcomponent).resolve_right hcomponentNe
  simpa only [eval_sub, eval_mul, eval_C, sub_eq_zero] using heval

/-- Operator-specialized convergence of the even orbit in the three-node
branch, ready to apply to the objects returned by
`arnoldiOrbit2_spectral_reduction`. -/
theorem exists_tendsto_even_arnoldiOrbit2_of_all_cluster_active_card_three
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
    (hthree : ∀ v ∈ clusterSet
      (fun k ↦ arnoldiOrbit2 A v₀ (2 * k)),
      (active A hA v).card = 3) :
    ∃ vEven, Tendsto (fun k ↦ arnoldiOrbit2 A v₀ (2 * k))
      atTop (nhds vEven) := by
  let u : ℕ → E := fun k ↦ arnoldiOrbit2 A v₀ (2 * k)
  have hu : IsCompact (closure (range u)) := by
    simpa only [u, Nat.add_zero] using
      isCompact_closure_range_arnoldiParity A hA v₀ hv₀ hgrade₀ 0
  have hconnected : IsConnected (clusterSet u) := by
    simpa only [u] using
      (compact_connected_even_arnoldiClusterSet
        A hA v₀ hv₀ hgrade₀).2.2
  apply exists_tendsto_of_threeNode_parity_clusterSet
    A hA u hu hconnected
    (fun mu ↦ (component A hA v₀ mu : E)) p q
    (pow_ne_zero 2 (ne_of_gt htau))
  · intro v hv
    exact norm_eq_one_of_mem_arnoldiParityClusterSet
      A hA v₀ hv₀ hgrade₀ 0 (by simpa only [u, Nat.add_zero] using hv)
  · intro v hv
    exact hthree v (by simpa only [u] using hv)
  · intro v hv mu
    exact component_mem_span_initial_of_mem_arnoldiParityClusterSet
      A hA v₀ 0 (by simpa only [u, Nat.add_zero] using hv) mu
  · intro v hv
    exact even_grouped_orthogonality_of_mem_arnoldiClusterSet
      A hA v₀ hgrade₀ p hp (by simpa only [u] using hv)
  · intro v hv mu hmu
    apply factor_eval_eq_of_mem_active_of_limitEquation
      A hA v p q (tau ^ 2) _ mu hmu
    exact even_limit_equation_of_mem_arnoldiClusterSet
      A hA v₀ hv₀ hgrade₀ p q tau hp hq hsigma
        (by simpa only [u] using hv)

end

end Spectral
end Forsythe
