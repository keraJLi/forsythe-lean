import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.Cauchy

/-!
# Cluster sets of asymptotically regular sequences

This file packages the elementary topology used in the Forsythe argument.  The main result says
that a sequence with compact range closure and vanishing successive distances has a nonempty,
compact, connected cluster set.
-/

open Filter Metric Set Topology

namespace Forsythe

section Topological

variable {X : Type*} [TopologicalSpace X]

/-- The set of cluster points of a sequence along `atTop`. -/
def clusterSet (u : ℕ → X) : Set X :=
  {x | MapClusterPt x atTop u}

@[simp]
theorem mem_clusterSet {u : ℕ → X} {x : X} :
    x ∈ clusterSet u ↔ MapClusterPt x atTop u :=
  Iff.rfl

/-- A point belongs to the cluster set iff it belongs to the closure of every tail. -/
theorem mem_clusterSet_iff_forall_mem_closure_tail {u : ℕ → X} {x : X} :
    x ∈ clusterSet u ↔ ∀ n, x ∈ closure (u '' Ici n) :=
  mapClusterPt_atTop_iff_forall_mem_closure

theorem isClosed_clusterSet (u : ℕ → X) : IsClosed (clusterSet u) := by
  simpa only [clusterSet, MapClusterPt] using
    (isClosed_setOf_clusterPt : IsClosed {x : X | ClusterPt x (map u atTop)})

theorem clusterSet_subset_closure_range (u : ℕ → X) :
    clusterSet u ⊆ closure (range u) := by
  intro x hx
  exact isClosed_closure.mem_of_mapClusterPt hx <|
    Eventually.of_forall fun n ↦ subset_closure ⟨n, rfl⟩

theorem isCompact_clusterSet {u : ℕ → X} (hu : IsCompact (closure (range u))) :
    IsCompact (clusterSet u) :=
  hu.of_isClosed_subset (isClosed_clusterSet u) (clusterSet_subset_closure_range u)

theorem clusterSet_nonempty {u : ℕ → X} (hu : IsCompact (closure (range u))) :
    (clusterSet u).Nonempty := by
  obtain ⟨x, -, hx⟩ := hu.exists_mapClusterPt_of_frequently (l := atTop) (f := u)
    (Frequently.of_forall fun n ↦ subset_closure ⟨n, rfl⟩)
  exact ⟨x, hx⟩

end Topological

section Metric

variable {X : Type*} [MetricSpace X]

/-- Once a sequence lies in the union of two uniformly separated sets and its successive
distances are smaller than the separation, it cannot keep switching between the sets. -/
theorem eventually_mem_left_or_right_of_separated
    (u : ℕ → X) (s t : Set X) {eps : ℝ} (heps : 0 < eps)
    (hsep : ∀ x ∈ s, ∀ y ∈ t, eps ≤ dist x y)
    (hcover : ∀ᶠ n in atTop, u n ∈ s ∪ t)
    (hstep : Tendsto (fun n ↦ dist (u (n + 1)) (u n)) atTop (nhds 0)) :
    (∀ᶠ n in atTop, u n ∈ s) ∨ (∀ᶠ n in atTop, u n ∈ t) := by
  obtain ⟨Ncover, hNcover⟩ := eventually_atTop.1 hcover
  have hsmall : ∀ᶠ n in atTop, dist (u (n + 1)) (u n) < eps :=
    hstep.eventually_lt_const heps
  obtain ⟨Nstep, hNstep⟩ := eventually_atTop.1 hsmall
  let N := max Ncover Nstep
  have hcoverN : ∀ n, N ≤ n → u n ∈ s ∪ t := fun n hn ↦
    hNcover n ((le_max_left _ _).trans hn)
  have hstepN : ∀ n, N ≤ n → dist (u (n + 1)) (u n) < eps := fun n hn ↦
    hNstep n ((le_max_right _ _).trans hn)
  rcases hcoverN N le_rfl with hNs | hNt
  · left
    refine eventually_atTop.2 ⟨N, ?_⟩
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => exact hNs
    | succ n hn ih =>
        rcases hcoverN (n + 1) (Nat.le_succ_of_le hn) with hs | ht
        · exact hs
        · exact False.elim <| not_le_of_gt (hstepN n hn) <| by
            simpa only [dist_comm] using hsep (u n) ih (u (n + 1)) ht
  · right
    refine eventually_atTop.2 ⟨N, ?_⟩
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => exact hNt
    | succ n hn ih =>
        rcases hcoverN (n + 1) (Nat.le_succ_of_le hn) with hs | ht
        · exact False.elim <| not_le_of_gt (hstepN n hn) <|
            hsep (u (n + 1)) hs (u n) ih
        · exact ht

/-- A precompact sequence eventually lies in every neighborhood of its full
cluster set. -/
theorem clusterSet_tendsto_nhdsSet {u : ℕ → X}
    (hu : IsCompact (closure (range u))) : Tendsto u atTop (nhdsSet (clusterSet u)) := by
  apply hu.tendsto_nhdsSet_of_mapClusterPt
  · exact Eventually.of_forall fun n ↦ subset_closure ⟨n, rfl⟩
  · exact fun _ _ hx ↦ hx

/-- A sequence with compact range closure and vanishing successive distances has a connected
cluster set. -/
theorem isConnected_clusterSet (u : ℕ → X)
    (hu : IsCompact (closure (range u)))
    (hstep : Tendsto (fun n ↦ dist (u (n + 1)) (u n)) atTop (nhds 0)) :
    IsConnected (clusterSet u) := by
  refine ⟨clusterSet_nonempty hu, ?_⟩
  rw [isPreconnected_iff_subset_of_fully_disjoint_closed (isClosed_clusterSet u)]
  intro s t hs ht hcover hst
  let C := clusterSet u
  let a := C ∩ s
  let b := C ∩ t
  have hCcompact : IsCompact C := isCompact_clusterSet hu
  have hacompact : IsCompact a := hCcompact.inter_right hs
  have hbclosed : IsClosed b := (isClosed_clusterSet u).inter ht
  have hab : Disjoint a b := by
    apply Set.disjoint_left.2
    intro x hxa hxb
    exact Set.disjoint_left.1 hst hxa.2 hxb.2
  obtain ⟨delta, hdelta, hthick⟩ := hab.exists_cthickenings hacompact hbclosed
  let eps := delta / 3
  have heps : 0 < eps := div_pos hdelta (by norm_num)
  have heps_le_delta : eps ≤ delta := by
    dsimp [eps]
    linarith
  have htwoeps_le_delta : eps + eps ≤ delta := by
    dsimp [eps]
    linarith
  have hCeq : C = a ∪ b := by
    apply Set.Subset.antisymm
    · intro x hx
      rcases hcover hx with hxs | hxt
      · exact Or.inl ⟨hx, hxs⟩
      · exact Or.inr ⟨hx, hxt⟩
    · exact union_subset inter_subset_left inter_subset_left
  have hnear : ∀ᶠ n in atTop, u n ∈ thickening eps a ∪ thickening eps b := by
    have hmem : thickening eps C ∈ nhdsSet C := thickening_mem_nhdsSet C heps
    have hraw : ∀ᶠ n in atTop, u n ∈ thickening eps C := by
      change {n | u n ∈ thickening eps C} ∈ atTop
      exact mem_map'.mp (clusterSet_tendsto_nhdsSet hu hmem)
    simpa only [hCeq, thickening_union] using hraw
  have hseparated : ∀ x ∈ thickening eps a, ∀ y ∈ thickening eps b,
      eps ≤ dist x y := by
    intro x hx y hy
    apply le_of_not_gt
    intro hxy
    have hxa : x ∈ cthickening eps a := thickening_subset_cthickening eps a hx
    have hyb : y ∈ cthickening eps b := thickening_subset_cthickening eps b hy
    have hya2 : y ∈ cthickening (eps + eps) a := by
      apply cthickening_cthickening_subset heps.le heps.le a
      exact mem_cthickening_of_dist_le y x eps (cthickening eps a) hxa (dist_comm y x ▸ hxy.le)
    have hya : y ∈ cthickening delta a := cthickening_mono htwoeps_le_delta a hya2
    have hyb' : y ∈ cthickening delta b := cthickening_mono heps_le_delta b hyb
    exact Set.disjoint_left.1 hthick hya hyb'
  rcases eventually_mem_left_or_right_of_separated u (thickening eps a) (thickening eps b)
      heps hseparated hnear hstep with ha | hb
  · left
    intro x hxC
    have hxa : x ∈ cthickening eps a := isClosed_cthickening.mem_of_mapClusterPt hxC <|
      ha.mono fun _ hn ↦ thickening_subset_cthickening eps a hn
    rcases hcover hxC with hxs | hxt
    · exact hxs
    · exfalso
      have hxb : x ∈ cthickening delta b :=
        self_subset_cthickening b ⟨hxC, hxt⟩
      exact Set.disjoint_left.1 hthick (cthickening_mono heps_le_delta a hxa) hxb
  · right
    intro x hxC
    have hxb : x ∈ cthickening eps b := isClosed_cthickening.mem_of_mapClusterPt hxC <|
      hb.mono fun _ hn ↦ thickening_subset_cthickening eps b hn
    rcases hcover hxC with hxs | hxt
    · exfalso
      have hxa : x ∈ cthickening delta a :=
        self_subset_cthickening a ⟨hxC, hxs⟩
      exact Set.disjoint_left.1 hthick hxa (cthickening_mono heps_le_delta b hxb)
    · exact hxt

/-- Bundled form of the cluster-set theorem used by the iteration argument. -/
theorem compact_connected_clusterSet (u : ℕ → X)
    (hu : IsCompact (closure (range u)))
    (hstep : Tendsto (fun n ↦ dist (u (n + 1)) (u n)) atTop (nhds 0)) :
    (clusterSet u).Nonempty ∧ IsCompact (clusterSet u) ∧ IsConnected (clusterSet u) :=
  ⟨clusterSet_nonempty hu, isCompact_clusterSet hu, isConnected_clusterSet u hu hstep⟩

end Metric

section CompleteMetric

variable {X : Type*} [MetricSpace X] [CompleteSpace X]

/-- Precompact version of `compact_connected_clusterSet`.  In a complete metric space, total
boundedness of the range is equivalent to compactness of its closure. -/
theorem compact_connected_clusterSet_of_totallyBounded (u : ℕ → X)
    (hu : TotallyBounded (range u))
    (hstep : Tendsto (fun n ↦ dist (u (n + 1)) (u n)) atTop (nhds 0)) :
    (clusterSet u).Nonempty ∧ IsCompact (clusterSet u) ∧ IsConnected (clusterSet u) := by
  apply compact_connected_clusterSet u
  · exact hu.closure.isCompact_of_isClosed isClosed_closure
  · exact hstep

end CompleteMetric

end Forsythe
