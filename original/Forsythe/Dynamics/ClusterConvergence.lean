import Forsythe.Dynamics.ClusterSet
import Mathlib.Topology.Connected.TotallyDisconnected

/-!
# Convergence from a finite connected cluster set

The three-node branch produces only finitely many possible cluster vectors.
Connectedness then forces a unique cluster point, and precompactness upgrades
that uniqueness to convergence of the whole sequence.
-/

set_option autoImplicit false

namespace Forsythe

open Filter Set Topology

variable {X : Type*} [MetricSpace X]

/-- A nonempty finite connected subset of a metric space is a singleton. -/
theorem eq_singleton_of_finite_isConnected
    {S : Set X} (hfinite : S.Finite) (hconnected : IsConnected S) :
    ∃ x : X, S = {x} := by
  obtain ⟨x, hx⟩ := hconnected.nonempty
  have hsub : S.Subsingleton :=
    hconnected.isPreconnected.isDiscrete_iff_subsingleton.mp hfinite.isDiscrete
  refine ⟨x, Set.Subset.antisymm ?_ (singleton_subset_iff.mpr hx)⟩
  intro y hy
  have hyx : y = x := hsub hy hx
  simp [hyx]

/-- A precompact sequence with a finite connected cluster set converges. -/
theorem exists_tendsto_of_finite_connected_clusterSet
    (u : ℕ → X) (hu : IsCompact (closure (range u)))
    (hfinite : (clusterSet u).Finite)
    (hconnected : IsConnected (clusterSet u)) :
    ∃ x : X, Tendsto u atTop (𝓝 x) := by
  obtain ⟨x, hx⟩ := eq_singleton_of_finite_isConnected hfinite hconnected
  refine ⟨x, ?_⟩
  have hset := clusterSet_tendsto_nhdsSet hu
  rw [hx, nhdsSet_singleton] at hset
  exact hset

/-- Direct wrapper for an asymptotically regular precompact sequence whose
cluster set is known to be finite. -/
theorem exists_tendsto_of_finite_clusterSet_of_dist_tendsto_zero
    (u : ℕ → X) (hu : IsCompact (closure (range u)))
    (hstep : Tendsto (fun n => dist (u (n + 1)) (u n)) atTop (𝓝 0))
    (hfinite : (clusterSet u).Finite) :
    ∃ x : X, Tendsto u atTop (𝓝 x) :=
  exists_tendsto_of_finite_connected_clusterSet u hu hfinite
    (isConnected_clusterSet u hu hstep)

end Forsythe
