import Forsythe.Spectral.OrderedExteriorDecay
import Forsythe.Spectral.OrderedFourNodeClosure

/-!
# Convergence in the four-node branch

This file is the short bridge from the logarithmic-cocycle exterior theorem
to the ordered four-node scalar closure.
-/

set_option autoImplicit false

namespace Forsythe
namespace Spectral

open Filter Module.End Set Topology

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A grade-four even cluster point forces convergence of both parity
subsequences. -/
theorem exists_tendsto_parities_of_fourNode_even_cluster
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v₀ : E)
    (hv₀ : ‖v₀‖ = 1) (hgrade₀ : 3 ≤ grade A v₀)
    (tau : ℝ) (htau : 0 < tau) (p q : MonicQuadratic)
    (Kprod : ℕ) (Ctail : ℝ) (hCtail : 0 ≤ Ctail)
    (hp : Tendsto
      (fun n ↦ (arnoldiFactorOrbit2 A v₀ (2 * n)).coeffPair)
      atTop (nhds p.coeffPair))
    (hq : Tendsto
      (fun n ↦ (arnoldiFactorOrbit2 A v₀ (2 * n + 1)).coeffPair)
      atTop (nhds q.coeffPair))
    (hnormalizer : Tendsto (arnoldiNormalizerOrbit2 A v₀)
      atTop (nhds tau))
    (hproduct : Tendsto (fun k ↦ Arnoldi.quadraticProductCoeff
      (arnoldiFactorOrbit2 A v₀ k)
      (arnoldiFactorOrbit2 A v₀ (k + 1))) atTop
      (nhds (Arnoldi.quadraticProductCoeff p q)))
    (htail : ∀ n, dist
      (Arnoldi.quadraticProductCoeff
        (arnoldiFactorOrbit2 A v₀ (n + Kprod))
        (arnoldiFactorOrbit2 A v₀ (n + Kprod + 1)))
      (Arnoldi.quadraticProductCoeff p q) ≤
        Ctail * (tau ^ 2 -
          Arnoldi.arnoldiHeightOrbit2 A v₀ (n + Kprod)))
    (vStar : E)
    (hvStar : vStar ∈ clusterSet
      (fun k ↦ arnoldiOrbit2 A v₀ (2 * k)))
    (hcard : (active A hA vStar).card = 4) :
    ∃ vEven vOdd,
      Tendsto (fun k ↦ arnoldiOrbit2 A v₀ (2 * k))
        atTop (nhds vEven) ∧
      Tendsto (fun k ↦ arnoldiOrbit2 A v₀ (2 * k + 1))
        atTop (nhds vOdd) := by
  obtain ⟨Kstable, S, hstable⟩ :=
    exists_stable_active_spectrum A hA v₀
  obtain ⟨Cext, theta, hCext, hthetaPos, hthetaLt, hext⟩ :=
    orderedExteriorMass_geometric_of_fourNode_even_cluster
      A hA v₀ hv₀ hgrade₀ tau htau p q Kprod Ctail hCtail
        hp hq hnormalizer hproduct htail Kstable S hstable
          vStar hvStar hcard
  exact exists_tendsto_parities_of_orderedFourNode_geometricExterior
    A hA v₀ hv₀ hgrade₀ tau htau p q hp hq hnormalizer
      vStar hvStar hcard hCext.le hthetaPos hthetaLt
        hext

end

end Spectral
end Forsythe
