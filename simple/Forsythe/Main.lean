import Forsythe.Arnoldi.OddLimit
import Forsythe.Spectral.FourNodeConvergence
import Forsythe.Spectral.Reduction
import Forsythe.Spectral.ThreeNodeBranch

/-!
# The real self-adjoint `s = 2` Forsythe theorem

The proof first obtains the paritywise polynomial limits.  If every even
cluster point has three active eigenvalues, grouped orthogonality makes the
even cluster set finite and hence a singleton.  Otherwise a four-node cluster
point triggers geometric exterior decay and the ordered four-node closure.
The odd limit is recovered from the exact Arnoldi step in the three-node
branch.
-/

set_option autoImplicit false

namespace Forsythe

open Filter Module.End Set Topology

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Forsythe's asymptotic two-cycle theorem for the degree-two normalized
Arnoldi iteration on a finite-dimensional real inner-product space. -/
theorem forsythe_s2
    (A : E →ₗ[ℝ] E) (hA : A.IsSymmetric)
    (v₀ : E) (hv₀ : ‖v₀‖ = 1)
    (hgrade : 3 ≤ grade A v₀) :
    ∃ vEven vOdd,
      Tendsto (fun k ↦ arnoldiOrbit2 A v₀ (2 * k))
        atTop (𝓝 vEven) ∧
      Tendsto (fun k ↦ arnoldiOrbit2 A v₀ (2 * k + 1))
        atTop (𝓝 vOdd) := by
  obtain ⟨tau, p, q, K, Ctail, htau, hnormalizer, hCtail,
      hp, hq, hproduct, htail, hclusters⟩ :=
    Spectral.arnoldiOrbit2_spectral_reduction A hA v₀ hv₀ hgrade
  rcases hclusters with
    ⟨_hevenNonempty, _hevenCompact, _hevenConnected,
      _hoddNonempty, _hoddCompact, _hoddConnected,
      hevenStructure, _hoddStructure⟩
  by_cases hthree : ∀ v ∈ clusterSet
      (fun k ↦ arnoldiOrbit2 A v₀ (2 * k)),
      (Spectral.active A hA v).card = 3
  · obtain ⟨vEven, hvEven⟩ :=
      Spectral.exists_tendsto_even_arnoldiOrbit2_of_all_cluster_active_card_three
        A hA v₀ hv₀ hgrade tau htau p q hp hq hnormalizer hthree
    have hvOdd := arnoldiOrbit2_odd_tendsto_of_even_tendsto
      A hA v₀ hv₀ hgrade p tau htau vEven hvEven hp
        (hnormalizer.comp (by
          apply tendsto_atTop.2
          intro N
          exact eventually_atTop.2 ⟨N, fun k hk ↦ by omega⟩))
    exact ⟨vEven, tau⁻¹ • polyApply A p.toPolynomial vEven,
      hvEven, hvOdd⟩
  · push Not at hthree
    obtain ⟨vStar, hvStar, hnotThree⟩ := hthree
    have hcardFour : (Spectral.active A hA vStar).card = 4 :=
      (hevenStructure vStar hvStar).2.2.resolve_left hnotThree
    exact Spectral.exists_tendsto_parities_of_fourNode_even_cluster
      A hA v₀ hv₀ hgrade tau htau p q K Ctail hCtail
        hp hq hnormalizer hproduct htail vStar hvStar hcardFour

end

end Forsythe
