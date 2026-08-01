import Forsythe.Arnoldi.Asymptotics
import Forsythe.Arnoldi.OrbitCoercivity
import Forsythe.Dynamics.ClusterConvergence
import Forsythe.Spectral.ComponentRecurrence
import Forsythe.Spectral.ThreeNodeConvergence

/-!
# Convergence from grouped spectral weights

Polynomial iteration keeps every grouped eigenspace component on its initial
real line.  Consequently, convergence of all squared component norms leaves
only finitely many possible sign choices in the cluster set.  Its connectedness
then recovers convergence of the vectors.  This is the sign-recovery step used
after the three- and four-node scalar analyses.
-/

set_option autoImplicit false

namespace Forsythe
namespace Spectral

open Filter Module.End Set Topology

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A grouped squared component norm depends continuously on the vector. -/
theorem continuous_weight (A : Module.End ℝ E) (hA : A.IsSymmetric)
    (mu : A.Eigenvalues) :
    Continuous (fun v : E ↦ weight A hA v mu) := by
  unfold weight component
  fun_prop

/-- A cluster point inherits the limit of each grouped squared component
weight. -/
theorem weight_eq_of_mem_clusterSet_of_tendsto
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (u : ℕ → E)
    (rho : A.Eigenvalues → ℝ)
    (hweight : ∀ mu, Tendsto (fun k ↦ weight A hA (u k) mu)
      atTop (nhds (rho mu)))
    {v : E} (hv : v ∈ clusterSet u) (mu : A.Eigenvalues) :
    weight A hA v mu = rho mu := by
  obtain ⟨phi, hphiMono, hphiLimit⟩ :=
    (show MapClusterPt v atTop u from hv).tendsto_subseq
  have hphi : Tendsto phi atTop atTop := hphiMono.tendsto_atTop
  have hsubWeight : Tendsto (fun k ↦ weight A hA (u (phi k)) mu)
      atTop (nhds (rho mu)) := (hweight mu).comp hphi
  have hclusterWeight : Tendsto (fun k ↦ weight A hA (u (phi k)) mu)
      atTop (nhds (weight A hA v mu)) := by
    exact ((continuous_weight A hA mu).tendsto v).comp hphiLimit
  exact tendsto_nhds_unique hclusterWeight hsubWeight

/-- Every grouped component of the Arnoldi orbit remains on the real line
spanned by its initial component. -/
theorem component_arnoldiOrbit2_mem_span_initial
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v₀ : E)
    (mu : A.Eigenvalues) (k : ℕ) :
    (component A hA (arnoldiOrbit2 A v₀ k) mu : E) ∈
      ℝ ∙ (component A hA v₀ mu : E) := by
  induction k with
  | zero =>
      rw [arnoldiOrbit2_zero]
      exact Submodule.mem_span_singleton_self (component A hA v₀ mu : E)
  | succ k ih =>
      have hrec := congrArg Subtype.val
        (component_arnoldiOrbit2_succ A hA v₀ mu k)
      rw [hrec]
      exact (ℝ ∙ (component A hA v₀ mu : E)).smul_mem _ ih

/-- The full grouped component map is injective. -/
theorem componentFamily_injective
    (A : Module.End ℝ E) (hA : A.IsSymmetric) :
    Function.Injective
      (fun v : E ↦ fun mu ↦ (component A hA v mu : E)) := by
  intro v w hvw
  apply hA.diagonalization.injective
  apply PiLp.ext
  intro mu
  apply Subtype.ext
  exact congrFun hvw mu

/-- Abstract grouped-coordinate sign recovery.  If every squared grouped
component has a limit and all cluster components lie on fixed real lines,
then asymptotic regularity forces vector convergence. -/
theorem exists_tendsto_of_grouped_weight_limits
    (A : Module.End ℝ E) (hA : A.IsSymmetric)
    (u : ℕ → E) (hu : IsCompact (closure (range u)))
    (hstep : Tendsto (fun n ↦ dist (u (n + 1)) (u n)) atTop (nhds 0))
    (direction : A.Eigenvalues → E)
    (hline : ∀ v ∈ clusterSet u, ∀ mu,
      (component A hA v mu : E) ∈ ℝ ∙ direction mu)
    (rho : A.Eigenvalues → ℝ)
    (hweight : ∀ mu, Tendsto (fun k ↦ weight A hA (u k) mu)
      atTop (nhds (rho mu))) :
    ∃ v : E, Tendsto u atTop (nhds v) := by
  apply exists_tendsto_of_finite_clusterSet_of_dist_tendsto_zero u hu hstep
  apply finite_of_fixed_component_lines_and_squared_norms
    (clusterSet u) (clusterSet_nonempty hu)
    (fun v mu ↦ (component A hA v mu : E))
    (componentFamily_injective A hA).injOn direction rho hline
  intro v hv mu
  exact weight_eq_of_mem_clusterSet_of_tendsto
    A hA u rho hweight hv mu

/-- Parity subsequences of the Arnoldi orbit converge as soon as every
grouped squared component has a limit.  The offset is stated explicitly;
the applications use `r = 0` and `r = 1`. -/
theorem exists_tendsto_arnoldiParity_of_weight_limits
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v₀ : E)
    (hv₀ : ‖v₀‖ = 1) (hgrade₀ : 3 ≤ grade A v₀) (r : ℕ)
    (rho : A.Eigenvalues → ℝ)
    (hweight : ∀ mu, Tendsto
      (fun k ↦ weight A hA (arnoldiOrbit2 A v₀ (2 * k + r)) mu)
      atTop (nhds (rho mu))) :
    ∃ v : E, Tendsto (fun k ↦ arnoldiOrbit2 A v₀ (2 * k + r))
      atTop (nhds v) := by
  let u : ℕ → E := fun k ↦ arnoldiOrbit2 A v₀ (2 * k + r)
  have hu : IsCompact (closure (range u)) := by
    apply (isCompact_closure_range_arnoldiOrbit2 A hA v₀ hv₀ hgrade₀).of_isClosed_subset
      isClosed_closure
    apply closure_minimal _ isClosed_closure
    rintro v ⟨k, rfl⟩
    exact subset_closure ⟨2 * k + r, rfl⟩
  have hstep : Tendsto (fun n ↦ dist (u (n + 1)) (u n))
      atTop (nhds 0) := by
    have hindex : Tendsto (fun k : ℕ ↦ 2 * k + r) atTop atTop := by
      apply Filter.tendsto_atTop.2
      intro n
      exact eventually_atTop.2 ⟨n, fun k hk ↦ by
        change n ≤ 2 * k + r
        omega⟩
    have htwo := (arnoldiOrbit2_twoStep_dist_tendsto_zero
      A hA v₀ hv₀ hgrade₀).comp hindex
    change Tendsto (fun k ↦ dist
      (arnoldiOrbit2 A v₀ (2 * (k + 1) + r))
      (arnoldiOrbit2 A v₀ (2 * k + r))) atTop (nhds 0)
    have heq :
        (fun k ↦ dist (arnoldiOrbit2 A v₀ (2 * (k + 1) + r))
          (arnoldiOrbit2 A v₀ (2 * k + r))) =
        (fun k ↦ dist (arnoldiOrbit2 A v₀ ((2 * k + r) + 2))
          (arnoldiOrbit2 A v₀ (2 * k + r))) := by
      funext k
      have hindexEq : 2 * (k + 1) + r = (2 * k + r) + 2 := by omega
      rw [hindexEq]
    rw [heq]
    change Tendsto (fun k ↦ dist
      (arnoldiOrbit2 A v₀ ((2 * k + r) + 2))
      (arnoldiOrbit2 A v₀ (2 * k + r))) atTop (nhds 0) at htwo
    exact htwo
  refine exists_tendsto_of_grouped_weight_limits A hA u hu hstep
    (fun mu ↦ (component A hA v₀ mu : E)) ?_ rho ?_
  · intro v hv mu
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
        change (component A hA (u k) mu : E) ∈ L
        simpa only [u, L] using
          component_arnoldiOrbit2_mem_span_initial
            A hA v₀ mu (2 * k + r))
  · simpa only [u] using hweight

end

end Spectral
end Forsythe
