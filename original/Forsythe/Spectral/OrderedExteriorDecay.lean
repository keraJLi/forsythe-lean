import Forsythe.Spectral.ExteriorDecayBranch
import Forsythe.Spectral.OrderedFourNode

/-!
# Geometric exterior decay for the ordered four-node coordinates

The logarithmic-cocycle argument is naturally stated using an arbitrary
enumeration of the four active nodes.  The later scalar dynamics uses the
increasing enumeration.  This file proves that the two enumerations have the
same range and converts the stabilized exterior-subtype estimate into a bound
for the intrinsic `exteriorMass` attached to the ordered nodes.
-/

set_option autoImplicit false

namespace Forsythe
namespace Spectral

open Filter Module.End Set Topology
open scoped BigOperators

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Once the active spectrum has stabilized, exterior mass is exactly the sum
over the surviving exterior subtype.  The two node enumerations need only
have the same range. -/
theorem exteriorMass_eq_stableExterior_sum_of_stabilization
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v₀ : E)
    (nodes exteriorNodes : Fin 4 → A.Eigenvalues)
    (hrange : Set.range nodes = Set.range exteriorNodes)
    {K : ℕ} {S : Finset A.Eigenvalues}
    (hstable : ∀ n, K ≤ n →
      active A hA (arnoldiOrbit2 A v₀ n) = S)
    {k : ℕ} (hk : K ≤ k) :
    exteriorMass A hA nodes (arnoldiOrbit2 A v₀ k) =
      ∑ mu : StableExteriorIndex A S exteriorNodes,
        weight A hA (arnoldiOrbit2 A v₀ k) mu := by
  have hprincipal :
      principalSpectrum A nodes = principalSpectrum A exteriorNodes := by
    ext mu
    simpa only [principalSpectrum, Finset.mem_image, Finset.mem_univ,
      true_and, Set.mem_range] using Set.ext_iff.mp hrange mu
  let small : Finset A.Eigenvalues :=
    S.filter fun mu ↦ mu ∉ Set.range exteriorNodes
  let large : Finset A.Eigenvalues :=
    Finset.univ.filter fun mu ↦ mu ∉ Set.range exteriorNodes
  let f : A.Eigenvalues → ℝ := fun mu ↦
    weight A hA (arnoldiOrbit2 A v₀ k) mu
  have hsubset : small ⊆ large := by
    intro mu hmu
    simp only [small, large, Finset.mem_filter, Finset.mem_univ, true_and]
      at hmu ⊢
    exact hmu.2
  have hzero : ∀ mu ∈ large, mu ∉ small → f mu = 0 := by
    intro mu hmuLarge hmuSmall
    have hmuOutside : mu ∉ S := by
      intro hmuS
      apply hmuSmall
      simp only [small, Finset.mem_filter]
      exact ⟨hmuS, by
        simpa only [large, Finset.mem_filter, Finset.mem_univ, true_and]
          using hmuLarge⟩
    have hcomponent := component_eq_zero_of_not_mem_stable_active
      A hA v₀ hstable hmuOutside hk
    simp only [f, weight, hcomponent, norm_zero]
    norm_num
  have hsum : (∑ mu ∈ small, f mu) = ∑ mu ∈ large, f mu :=
    Finset.sum_subset hsubset hzero
  have hsubtype :
      (∑ mu ∈ small, f mu) =
        ∑ mu : StableExteriorIndex A S exteriorNodes, f mu := by
    apply Finset.sum_subtype
    intro mu
    simp only [small, Finset.mem_filter]
  have hlarge :
      Finset.univ.filter
          (fun mu ↦ mu ∉ principalSpectrum A exteriorNodes) = large := by
    ext mu
    simp only [large, principalSpectrum, Finset.mem_filter,
      Finset.mem_univ, Finset.mem_image, true_and, Set.mem_range]
  rw [exteriorMass, hprincipal]
  rw [hlarge]
  simpa only [f] using hsum.symm.trans hsubtype

/-- Geometric decay of the full exterior mass in the increasing four-node
coordinates.  Membership of the four principal nodes in the stabilized
spectrum is derived from activity at the cluster point: a component which is
nonzero at a cluster point could not have been deleted earlier. -/
theorem orderedExteriorMass_geometric_of_fourNode_even_cluster
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
    (Kstable : ℕ) (S : Finset A.Eigenvalues)
    (hstable : ∀ n, Kstable ≤ n →
      active A hA (arnoldiOrbit2 A v₀ n) = S)
    (vStar : E)
    (hvStar : vStar ∈ clusterSet
      (fun k ↦ arnoldiOrbit2 A v₀ (2 * k)))
    (hcard : (active A hA vStar).card = 4) :
    let orderedNodes :=
      orderedNodesOfFourClusterPoint A hA vStar hcard
    ∃ C theta : ℝ, 0 < C ∧ 0 < theta ∧ theta < 1 ∧
      ∀ᶠ k in atTop,
        exteriorMass A hA orderedNodes (arnoldiOrbit2 A v₀ k) ≤
          C * theta ^ k := by
  let arbitraryNodes := nodesOfFourClusterPoint A hA vStar hcard
  let orderedNodes := orderedNodesOfFourClusterPoint A hA vStar hcard
  have hnodesStable : ∀ i, arbitraryNodes i ∈ S := by
    intro i
    have hcomponent : component A hA (arnoldiOrbit2 A v₀ Kstable)
        (arbitraryNodes i) ≠ 0 :=
      component_ne_zero_all_arnoldiOrbit2_of_mem_evenCluster_active
        A hA v₀ hvStar
          (by simpa only [arbitraryNodes] using
            nodesOfFourClusterPoint_mem_active A hA vStar hcard i)
          Kstable
    have hactive : arbitraryNodes i ∈
        active A hA (arnoldiOrbit2 A v₀ Kstable) :=
      (mem_active_iff A hA (arnoldiOrbit2 A v₀ Kstable)
        (arbitraryNodes i)).2 hcomponent
    simpa only [hstable Kstable le_rfl] using hactive
  obtain ⟨C, theta, hC, htheta, hthetaOne, hgeometric⟩ :=
    stableExterior_geometric_of_fourNode_even_cluster
      A hA v₀ hv₀ hgrade₀ tau htau p q Kprod Ctail hCtail hp hq
        hnormalizer hproduct htail Kstable S hstable vStar hvStar hcard
          (by simpa only [arbitraryNodes] using hnodesStable)
  have hrange : Set.range orderedNodes = Set.range arbitraryNodes := by
    ext mu
    exact (mem_range_orderedNodesOfFourClusterPoint_iff
      A hA vStar hcard mu).trans
        (mem_range_nodesOfFourClusterPoint_iff
          A hA vStar hcard mu).symm
  refine ⟨C, theta, hC, htheta, hthetaOne, ?_⟩
  filter_upwards [hgeometric,
    (eventually_atTop.2 ⟨Kstable, fun k hk ↦ hk⟩)] with k hkGeom hkStable
  rw [exteriorMass_eq_stableExterior_sum_of_stabilization
    A hA v₀ orderedNodes arbitraryNodes hrange hstable hkStable]
  simpa only [arbitraryNodes] using hkGeom

/-- Global form of the manuscript's exterior-decay estimate.  The eventual
geometric bound is extended across the finite prefix by increasing only its
leading constant; the contraction rate is unchanged. -/
theorem orderedExteriorMass_global_geometric_of_fourNode_even_cluster
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
    (Kstable : ℕ) (S : Finset A.Eigenvalues)
    (hstable : ∀ n, Kstable ≤ n →
      active A hA (arnoldiOrbit2 A v₀ n) = S)
    (vStar : E)
    (hvStar : vStar ∈ clusterSet
      (fun k ↦ arnoldiOrbit2 A v₀ (2 * k)))
    (hcard : (active A hA vStar).card = 4) :
    let orderedNodes :=
      orderedNodesOfFourClusterPoint A hA vStar hcard
    ∃ C theta : ℝ, 0 < C ∧ 0 < theta ∧ theta < 1 ∧
      ∀ k,
        exteriorMass A hA orderedNodes (arnoldiOrbit2 A v₀ k) ≤
          C * theta ^ k := by
  let orderedNodes :=
    orderedNodesOfFourClusterPoint A hA vStar hcard
  obtain ⟨C, theta, hC, htheta, hthetaOne, hgeometric⟩ :=
    orderedExteriorMass_geometric_of_fourNode_even_cluster
      A hA v₀ hv₀ hgrade₀ tau htau p q Kprod Ctail hCtail hp hq
        hnormalizer hproduct htail Kstable S hstable vStar hvStar hcard
  obtain ⟨K, hK⟩ := eventually_atTop.1 hgeometric
  let mass : ℕ → ℝ := fun k ↦
    exteriorMass A hA orderedNodes (arnoldiOrbit2 A v₀ k)
  let Cglobal : ℝ :=
    C + ∑ k ∈ Finset.range K, mass k / theta ^ k + 1
  have hmassNonneg (k : ℕ) : 0 ≤ mass k := by
    exact exteriorMass_nonneg A hA orderedNodes (arnoldiOrbit2 A v₀ k)
  have hthetaPowPos (k : ℕ) : 0 < theta ^ k := pow_pos htheta k
  have hratioNonneg (k : ℕ) : 0 ≤ mass k / theta ^ k :=
    div_nonneg (hmassNonneg k) (hthetaPowPos k).le
  have hsumNonneg :
      0 ≤ ∑ k ∈ Finset.range K, mass k / theta ^ k :=
    Finset.sum_nonneg fun k _ ↦ hratioNonneg k
  have hCglobal : 0 < Cglobal := by
    dsimp only [Cglobal]
    linarith
  refine ⟨Cglobal, theta, hCglobal, htheta, hthetaOne, ?_⟩
  intro k
  by_cases hk : K ≤ k
  · have htailBound : mass k ≤ C * theta ^ k := by
      simpa only [mass, orderedNodes] using hK k hk
    have hCle : C ≤ Cglobal := by
      dsimp only [Cglobal]
      linarith
    exact htailBound.trans
      (mul_le_mul_of_nonneg_right hCle (hthetaPowPos k).le)
  · have hklt : k < K := Nat.lt_of_not_ge hk
    have hratioLeSum : mass k / theta ^ k ≤
        ∑ j ∈ Finset.range K, mass j / theta ^ j := by
      exact Finset.single_le_sum
        (fun j _ ↦ hratioNonneg j) (Finset.mem_range.mpr hklt)
    have hratioLe : mass k / theta ^ k ≤ Cglobal := by
      dsimp only [Cglobal]
      linarith
    calc
      mass k = (mass k / theta ^ k) * theta ^ k := by
        field_simp [ne_of_gt (hthetaPowPos k)]
      _ ≤ Cglobal * theta ^ k :=
        mul_le_mul_of_nonneg_right hratioLe (hthetaPowPos k).le

end

end Spectral
end Forsythe
