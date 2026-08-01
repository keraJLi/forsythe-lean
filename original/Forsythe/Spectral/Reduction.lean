import Forsythe.Arnoldi.LimitGrade
import Forsythe.Arnoldi.PolynomialLimits
import Forsythe.Spectral.LimitEquation
import Forsythe.Spectral.Support

/-!
# Global finite-dimensional spectral reduction

This module assembles the topology, polynomial limits, limit equation, and
support count.  The theorem-facing hypotheses remain the intrinsic
unit-norm and grade assumptions; grouped eigenspace coordinates occur only in
the final support-cardinality conclusion.
-/

set_option autoImplicit false

namespace Forsythe
namespace Spectral

open Filter Polynomial Set Topology

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Membership in the even cluster set supplies a cofinal convergent
subsequence, to which the exact even limit equation applies. -/
theorem even_limit_equation_of_mem_arnoldiClusterSet
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v₀ : E)
    (hv₀ : ‖v₀‖ = 1) (hgrade₀ : 3 ≤ grade A v₀)
    (p q : MonicQuadratic) (tau : ℝ)
    (hp : Tendsto
      (fun n ↦ (arnoldiFactorOrbit2 A v₀ (2 * n)).coeffPair)
      atTop (nhds p.coeffPair))
    (hq : Tendsto
      (fun n ↦ (arnoldiFactorOrbit2 A v₀ (2 * n + 1)).coeffPair)
      atTop (nhds q.coeffPair))
    (htau : Tendsto (arnoldiNormalizerOrbit2 A v₀) atTop (nhds tau))
    {v : E}
    (hv : v ∈ clusterSet (fun k ↦ arnoldiOrbit2 A v₀ (2 * k))) :
    polyApply A (p.toPolynomial * q.toPolynomial - C (tau ^ 2)) v = 0 := by
  obtain ⟨phi, hphiMono, hphiLimit⟩ :=
    (show MapClusterPt v atTop
      (fun k ↦ arnoldiOrbit2 A v₀ (2 * k)) from hv).tendsto_subseq
  have hphi : Tendsto phi atTop atTop := hphiMono.tendsto_atTop
  have hvLimit : Tendsto
      (fun j ↦ arnoldiOrbit2 A v₀ (2 * phi j)) atTop (nhds v) := by
    simpa only [Function.comp_def] using hphiLimit
  exact even_arnoldiOrbit2_limit_equation
    A hA v₀ hv₀ hgrade₀ p q tau hp hq htau phi hphi v hvLimit

/-- Membership in the odd cluster set likewise supplies the required
cofinal convergent subsequence. -/
theorem odd_limit_equation_of_mem_arnoldiClusterSet
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v₀ : E)
    (hv₀ : ‖v₀‖ = 1) (hgrade₀ : 3 ≤ grade A v₀)
    (p q : MonicQuadratic) (tau : ℝ)
    (hp : Tendsto
      (fun n ↦ (arnoldiFactorOrbit2 A v₀ (2 * n)).coeffPair)
      atTop (nhds p.coeffPair))
    (hq : Tendsto
      (fun n ↦ (arnoldiFactorOrbit2 A v₀ (2 * n + 1)).coeffPair)
      atTop (nhds q.coeffPair))
    (htau : Tendsto (arnoldiNormalizerOrbit2 A v₀) atTop (nhds tau))
    {v : E}
    (hv : v ∈ clusterSet (fun k ↦ arnoldiOrbit2 A v₀ (2 * k + 1))) :
    polyApply A (p.toPolynomial * q.toPolynomial - C (tau ^ 2)) v = 0 := by
  obtain ⟨phi, hphiMono, hphiLimit⟩ :=
    (show MapClusterPt v atTop
      (fun k ↦ arnoldiOrbit2 A v₀ (2 * k + 1)) from hv).tendsto_subseq
  have hphi : Tendsto phi atTop atTop := hphiMono.tendsto_atTop
  have hvLimit : Tendsto
      (fun j ↦ arnoldiOrbit2 A v₀ (2 * phi j + 1)) atTop (nhds v) := by
    simpa only [Function.comp_def] using hphiLimit
  exact odd_arnoldiOrbit2_limit_equation
    A hA v₀ hv₀ hgrade₀ p q tau hp hq htau phi hphi v hvLimit

/-- Stage 3 reduction package.  Both parity cluster sets are nonempty,
compact, and connected.  Every point in either set retains grade at least
three, satisfies the common quartic limit equation, and consequently has
three or four active distinct eigenvalues. -/
theorem arnoldiOrbit2_spectral_reduction
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v₀ : E)
    (hv₀ : ‖v₀‖ = 1) (hgrade₀ : 3 ≤ grade A v₀) :
    ∃ tau : ℝ, ∃ p q : MonicQuadratic, ∃ K : ℕ, ∃ Ctail : ℝ,
      0 < tau ∧
      Tendsto (arnoldiNormalizerOrbit2 A v₀) atTop (nhds tau) ∧
      0 ≤ Ctail ∧
      Tendsto (fun n ↦ (arnoldiFactorOrbit2 A v₀ (2 * n)).coeffPair)
        atTop (nhds p.coeffPair) ∧
      Tendsto (fun n ↦ (arnoldiFactorOrbit2 A v₀ (2 * n + 1)).coeffPair)
        atTop (nhds q.coeffPair) ∧
      Tendsto (fun k ↦ Arnoldi.quadraticProductCoeff
          (arnoldiFactorOrbit2 A v₀ k)
          (arnoldiFactorOrbit2 A v₀ (k + 1))) atTop
        (nhds (Arnoldi.quadraticProductCoeff p q)) ∧
      (∀ n, dist
          (Arnoldi.quadraticProductCoeff
            (arnoldiFactorOrbit2 A v₀ (n + K))
            (arnoldiFactorOrbit2 A v₀ (n + K + 1)))
          (Arnoldi.quadraticProductCoeff p q) ≤
        Ctail * (tau ^ 2 - Arnoldi.arnoldiHeightOrbit2 A v₀ (n + K))) ∧
      let evenCluster :=
        clusterSet (fun k ↦ arnoldiOrbit2 A v₀ (2 * k))
      let oddCluster :=
        clusterSet (fun k ↦ arnoldiOrbit2 A v₀ (2 * k + 1))
      evenCluster.Nonempty ∧ IsCompact evenCluster ∧
      IsConnected evenCluster ∧
      oddCluster.Nonempty ∧ IsCompact oddCluster ∧
      IsConnected oddCluster ∧
      (∀ v ∈ evenCluster,
        3 ≤ grade A v ∧
        polyApply A (p.toPolynomial * q.toPolynomial - C (tau ^ 2)) v = 0 ∧
        ((active A hA v).card = 3 ∨ (active A hA v).card = 4)) ∧
      (∀ v ∈ oddCluster,
        3 ≤ grade A v ∧
        polyApply A (p.toPolynomial * q.toPolynomial - C (tau ^ 2)) v = 0 ∧
        ((active A hA v).card = 3 ∨ (active A hA v).card = 4)) := by
  obtain ⟨tau, p, q, K, Ctail, htau, hnorm, hCtail,
      hp, hq, hproduct, htail⟩ :=
    Arnoldi.arnoldiOrbit2_polynomial_limits A hA v₀ hv₀ hgrade₀
  let evenCluster :=
    clusterSet (fun k ↦ arnoldiOrbit2 A v₀ (2 * k))
  let oddCluster :=
    clusterSet (fun k ↦ arnoldiOrbit2 A v₀ (2 * k + 1))
  have heven := compact_connected_even_arnoldiClusterSet
    A hA v₀ hv₀ hgrade₀
  have hodd := compact_connected_odd_arnoldiClusterSet
    A hA v₀ hv₀ hgrade₀
  refine ⟨tau, p, q, K, Ctail, htau, hnorm, hCtail,
    hp, hq, hproduct, htail, ?_⟩
  dsimp only [evenCluster, oddCluster] at heven hodd ⊢
  refine ⟨heven.1, heven.2.1, heven.2.2,
    hodd.1, hodd.2.1, hodd.2.2, ?_, ?_⟩
  · intro v hv
    have hgrade := grade_mem_even_arnoldiClusterSet
      A hA v₀ hv₀ hgrade₀ hv
    have hann := even_limit_equation_of_mem_arnoldiClusterSet
      A hA v₀ hv₀ hgrade₀ p q tau hp hq hnorm hv
    exact ⟨hgrade, hann,
      active_card_eq_three_or_four_of_quadraticProduct_sub_C_annihilator
        A hA v p q (tau ^ 2) hgrade hann⟩
  · intro v hv
    have hgrade := grade_mem_odd_arnoldiClusterSet
      A hA v₀ hv₀ hgrade₀ hv
    have hann := odd_limit_equation_of_mem_arnoldiClusterSet
      A hA v₀ hv₀ hgrade₀ p q tau hp hq hnorm hv
    exact ⟨hgrade, hann,
      active_card_eq_three_or_four_of_quadraticProduct_sub_C_annihilator
        A hA v p q (tau ^ 2) hgrade hann⟩

end

end Spectral
end Forsythe
