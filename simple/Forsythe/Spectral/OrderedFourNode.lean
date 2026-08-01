import Forsythe.FourNode.Gap
import Forsythe.Spectral.FourNodeBranch
import Mathlib.Data.Finset.Sort

/-!
# Ordered principal nodes in the grade-four branch

The spectral reduction initially needs only an arbitrary enumeration of four
active eigenvalues.  Scalar gap and sign arguments are cleaner with the unique
increasing enumeration, supplied here by `Finset.orderEmbOfFin`.
-/

set_option autoImplicit false

namespace Forsythe
namespace Spectral

open Filter Module.End Polynomial Set Topology

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The eigenvalue subtype inherits the ambient order on the real spectrum. -/
noncomputable local instance eigenvaluesLinearOrder
    (A : Module.End ℝ E) : LinearOrder A.Eigenvalues := by
  change LinearOrder {mu : ℝ // A.HasEigenvalue mu}
  infer_instance

/-- Increasing enumeration of the four active eigenvalues of a grade-four
cluster point. -/
def orderedNodesOfFourClusterPoint
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v : E)
    (hcard : (active A hA v).card = 4) : Fin 4 → A.Eigenvalues :=
  (active A hA v).orderEmbOfFin hcard

theorem orderedNodesOfFourClusterPoint_strictMono
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v : E)
    (hcard : (active A hA v).card = 4) :
    StrictMono (fun i ↦
      ((orderedNodesOfFourClusterPoint A hA v hcard i :
        A.Eigenvalues) : ℝ)) := by
  intro i j hij
  exact ((active A hA v).orderEmbOfFin hcard).strictMono hij

theorem orderedNodesOfFourClusterPoint_injective
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v : E)
    (hcard : (active A hA v).card = 4) :
    Function.Injective (orderedNodesOfFourClusterPoint A hA v hcard) := by
  exact ((active A hA v).orderEmbOfFin hcard).injective

theorem orderedNodesOfFourClusterPoint_mem_active
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v : E)
    (hcard : (active A hA v).card = 4) (i : Fin 4) :
    orderedNodesOfFourClusterPoint A hA v hcard i ∈ active A hA v := by
  exact Finset.orderEmbOfFin_mem (active A hA v) hcard i

/-- The increasing enumeration still exhausts the active support. -/
theorem mem_range_orderedNodesOfFourClusterPoint_iff
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v : E)
    (hcard : (active A hA v).card = 4) (mu : A.Eigenvalues) :
    mu ∈ Set.range (orderedNodesOfFourClusterPoint A hA v hcard) ↔
      mu ∈ active A hA v := by
  change mu ∈ Set.range ((active A hA v).orderEmbOfFin hcard) ↔
    mu ∈ active A hA v
  rw [Finset.range_orderEmbOfFin]
  rfl

private theorem orderedNodalQuartic_isMonicOfDegree_four
    (lambda : Fin 4 → ℝ) :
    (FourNode.nodalQuartic lambda).IsMonicOfDegree 4 := by
  have h0 := isMonicOfDegree_X_sub_one (lambda 0)
  have h1 := isMonicOfDegree_X_sub_one (lambda 1)
  have h2 := isMonicOfDegree_X_sub_one (lambda 2)
  have h3 := isMonicOfDegree_X_sub_one (lambda 3)
  simpa only [FourNode.nodalQuartic, Fin.prod_univ_four, Nat.reduceAdd] using
    ((h0.mul h1).mul h2).mul h3

private theorem orderedNodalQuartic_eval_node
    (lambda : Fin 4 → ℝ) (i : Fin 4) :
    (FourNode.nodalQuartic lambda).eval (lambda i) = 0 := by
  rw [FourNode.nodalQuartic, eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)

/-- Four explicitly enumerated active roots determine the common monic
quartic annihilator. -/
theorem quadraticProduct_eq_nodalQuartic_add_C_of_active_enumeration
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v : E)
    (nodes : Fin 4 → A.Eigenvalues) (hnodes : Function.Injective nodes)
    (hnodesActive : ∀ i, nodes i ∈ active A hA v)
    (p q : MonicQuadratic) (H : ℝ)
    (hann : polyApply A
      (p.toPolynomial * q.toPolynomial - C H) v = 0) :
    p.toPolynomial * q.toPolynomial =
      FourNode.nodalQuartic
        (fun i ↦ ((nodes i : A.Eigenvalues) : ℝ)) + C H := by
  let lambda : Fin 4 → ℝ := fun i ↦ ((nodes i : A.Eigenvalues) : ℝ)
  let r := p.toPolynomial * q.toPolynomial - C H
  have hr : r.IsMonicOfDegree 4 :=
    ⟨natDegree_quadraticProduct_sub_C p q H,
      monic_quadraticProduct_sub_C p q H⟩
  have hPi : (FourNode.nodalQuartic lambda).IsMonicOfDegree 4 :=
    orderedNodalQuartic_isMonicOfDegree_four lambda
  have hdegree :
      (r - FourNode.nodalQuartic lambda).natDegree < 4 :=
    hr.natDegree_sub_lt (by norm_num) hPi
  have heval : ∀ i : Fin 4,
      (r - FourNode.nodalQuartic lambda).eval (lambda i) = 0 := by
    intro i
    have hroot := factor_eval_eq_of_mem_active_of_limitEquation
      A hA v p q H hann (nodes i) (hnodesActive i)
    rw [eval_sub, orderedNodalQuartic_eval_node]
    dsimp only [r, lambda]
    rw [eval_sub, eval_mul, eval_C, hroot]
    ring
  have hzero : r - FourNode.nodalQuartic lambda = 0 :=
    eq_zero_of_natDegree_lt_card_of_eval_eq_zero
      (r - FourNode.nodalQuartic lambda)
      (fun i j hij ↦ hnodes (Subtype.ext hij)) heval
      (by simpa using hdegree)
  have hrEq : r = FourNode.nodalQuartic lambda := sub_eq_zero.mp hzero
  change p.toPolynomial * q.toPolynomial =
    FourNode.nodalQuartic lambda + C H
  dsimp only [r] at hrEq
  exact sub_eq_iff_eq_add.mp hrEq

/-- Ordered-node factorization for a grade-four even cluster point. -/
theorem orderedFourNode_factorization_of_mem_evenClusterSet
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
    {vStar : E}
    (hvStar : vStar ∈ clusterSet
      (fun k ↦ arnoldiOrbit2 A v₀ (2 * k)))
    (hcard : (active A hA vStar).card = 4) :
    let nodes := orderedNodesOfFourClusterPoint A hA vStar hcard
    p.toPolynomial * q.toPolynomial =
      FourNode.nodalQuartic
        (fun i ↦ ((nodes i : A.Eigenvalues) : ℝ)) + C (tau ^ 2) := by
  dsimp only
  apply quadraticProduct_eq_nodalQuartic_add_C_of_active_enumeration
    A hA vStar
      (orderedNodesOfFourClusterPoint A hA vStar hcard)
      (orderedNodesOfFourClusterPoint_injective A hA vStar hcard)
      (orderedNodesOfFourClusterPoint_mem_active A hA vStar hcard)
      p q (tau ^ 2)
  exact even_limit_equation_of_mem_arnoldiClusterSet
    A hA v₀ hv₀ hgrade₀ p q tau hp hq hsigma hvStar

/-- A component active at an even cluster point could not have been deleted
at any earlier orbit index. -/
theorem component_ne_zero_all_arnoldiOrbit2_of_mem_evenCluster_active
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v₀ : E)
    {vStar : E}
    (hvStar : vStar ∈ clusterSet
      (fun k ↦ arnoldiOrbit2 A v₀ (2 * k)))
    {mu : A.Eigenvalues} (hmu : mu ∈ active A hA vStar) :
    ∀ k, component A hA (arnoldiOrbit2 A v₀ k) mu ≠ 0 := by
  intro k hzero
  let Z : Set E := {v | component A hA v mu = 0}
  have hcontinuous : Continuous (fun v : E ↦ component A hA v mu) := by
    unfold component
    fun_prop
  have hclosed : IsClosed Z :=
    isClosed_eq hcontinuous continuous_const
  have heventually : ∀ᶠ n in atTop,
      arnoldiOrbit2 A v₀ (2 * n) ∈ Z := by
    refine eventually_atTop.2 ⟨k, ?_⟩
    intro n hn
    change component A hA (arnoldiOrbit2 A v₀ (2 * n)) mu = 0
    exact component_arnoldiOrbit2_eq_zero_of_le
      A hA v₀ mu (by omega) hzero
  have hstarZero : vStar ∈ Z :=
    hclosed.mem_of_mapClusterPt hvStar heventually
  exact ((mem_active_iff A hA vStar mu).mp hmu) hstarZero

/-- In particular, every ordered principal node remains nonzero throughout
the full Arnoldi orbit. -/
theorem orderedFourNode_components_ne_zero_all
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v₀ : E)
    {vStar : E}
    (hvStar : vStar ∈ clusterSet
      (fun k ↦ arnoldiOrbit2 A v₀ (2 * k)))
    (hcard : (active A hA vStar).card = 4) :
    ∀ k i, component A hA (arnoldiOrbit2 A v₀ k)
      (orderedNodesOfFourClusterPoint A hA vStar hcard i) ≠ 0 := by
  intro k i
  exact component_ne_zero_all_arnoldiOrbit2_of_mem_evenCluster_active
    A hA v₀ hvStar
      (orderedNodesOfFourClusterPoint_mem_active A hA vStar hcard i) k

end

end Spectral
end Forsythe
