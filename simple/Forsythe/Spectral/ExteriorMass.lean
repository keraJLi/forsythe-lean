import Forsythe.Spectral.Moments

/-!
# Principal/exterior spectral mass decomposition

For four selected distinct eigenvalues, the grouped squared norm decomposes
into principal and exterior mass.  The final estimates compare the intrinsic
moments of a unit vector with the moments of its normalized four principal
weights, using an explicit finite spectral bound.
-/

set_option autoImplicit false

namespace Forsythe
namespace Spectral

open scoped BigOperators

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The four selected distinct eigenvalues as a finite set. -/
def principalSpectrum (A : Module.End ℝ E)
    (nodes : Fin 4 → A.Eigenvalues) : Finset A.Eigenvalues :=
  Finset.univ.image nodes

/-- Squared mass outside the selected four eigenvalues. -/
def exteriorMass (A : Module.End ℝ E) (hA : A.IsSymmetric)
    (nodes : Fin 4 → A.Eigenvalues) (v : E) : ℝ :=
  ∑ mu ∈ Finset.univ with mu ∉ principalSpectrum A nodes,
    weight A hA v mu

/-- The selected, unnormalized `k`th power moment. -/
def principalMoment (A : Module.End ℝ E) (hA : A.IsSymmetric)
    (nodes : Fin 4 → A.Eigenvalues) (v : E) (k : ℕ) : ℝ :=
  ∑ i, weight A hA v (nodes i) *
    ((nodes i : A.Eigenvalues) : ℝ) ^ k

/-- The exterior, unnormalized `k`th power moment. -/
def exteriorMoment (A : Module.End ℝ E) (hA : A.IsSymmetric)
    (nodes : Fin 4 → A.Eigenvalues) (v : E) (k : ℕ) : ℝ :=
  ∑ mu ∈ Finset.univ with mu ∉ principalSpectrum A nodes,
    weight A hA v mu * (mu : ℝ) ^ k

theorem sum_principalSpectrum_weight
    (A : Module.End ℝ E) (hA : A.IsSymmetric)
    (nodes : Fin 4 → A.Eigenvalues) (hnodes : Function.Injective nodes)
    (v : E) :
    ∑ mu ∈ principalSpectrum A nodes, weight A hA v mu =
      principalMass A hA nodes v := by
  rw [principalSpectrum, principalMass]
  exact Finset.sum_image hnodes.injOn

/-- Exact principal/exterior mass decomposition. -/
theorem principalMass_add_exteriorMass
    (A : Module.End ℝ E) (hA : A.IsSymmetric)
    (nodes : Fin 4 → A.Eigenvalues) (hnodes : Function.Injective nodes)
    (v : E) :
    principalMass A hA nodes v + exteriorMass A hA nodes v = ‖v‖ ^ 2 := by
  rw [← sum_principalSpectrum_weight A hA nodes hnodes v]
  rw [exteriorMass]
  have hpartition := Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset A.Eigenvalues)
    (fun mu ↦ mu ∈ principalSpectrum A nodes)
    (fun mu ↦ weight A hA v mu)
  have hfilter : (Finset.univ.filter fun mu : A.Eigenvalues ↦
      mu ∈ principalSpectrum A nodes) = principalSpectrum A nodes := by
    ext mu
    simp
  rw [hfilter] at hpartition
  exact hpartition.trans (sum_weight_eq_norm_sq A hA v)

theorem exteriorMass_nonneg
    (A : Module.End ℝ E) (hA : A.IsSymmetric)
    (nodes : Fin 4 → A.Eigenvalues) (v : E) :
    0 ≤ exteriorMass A hA nodes v := by
  rw [exteriorMass]
  exact Finset.sum_nonneg fun _ _ ↦ weight_nonneg A hA v _

theorem principalMass_eq_one_sub_exteriorMass
    (A : Module.End ℝ E) (hA : A.IsSymmetric)
    (nodes : Fin 4 → A.Eigenvalues) (hnodes : Function.Injective nodes)
    (v : E) (hv : ‖v‖ = 1) :
    principalMass A hA nodes v = 1 - exteriorMass A hA nodes v := by
  have h := principalMass_add_exteriorMass A hA nodes hnodes v
  rw [hv, one_pow] at h
  linarith

theorem exteriorMass_eq_one_sub_principalMass
    (A : Module.End ℝ E) (hA : A.IsSymmetric)
    (nodes : Fin 4 → A.Eigenvalues) (hnodes : Function.Injective nodes)
    (v : E) (hv : ‖v‖ = 1) :
    exteriorMass A hA nodes v = 1 - principalMass A hA nodes v := by
  linarith [principalMass_eq_one_sub_exteriorMass A hA nodes hnodes v hv]

/-- The sum of the absolute values of all distinct eigenvalues.  It is a
concrete common bound requiring no choice of a maximizing index. -/
def eigenvalueAbsSum (A : Module.End ℝ E) : ℝ :=
  ∑ mu : A.Eigenvalues, |(mu : ℝ)|

theorem eigenvalueAbsSum_nonneg (A : Module.End ℝ E) :
    0 ≤ eigenvalueAbsSum A := by
  exact Finset.sum_nonneg fun _ _ ↦ abs_nonneg _

theorem abs_eigenvalue_le_eigenvalueAbsSum
    (A : Module.End ℝ E) (mu : A.Eigenvalues) :
    |(mu : ℝ)| ≤ eigenvalueAbsSum A := by
  rw [eigenvalueAbsSum]
  exact Finset.single_le_sum
    (s := (Finset.univ : Finset A.Eigenvalues))
    (f := fun i : A.Eigenvalues ↦ |((i : A.Eigenvalues) : ℝ)|)
    (fun i _ ↦ abs_nonneg ((i : A.Eigenvalues) : ℝ)) (Finset.mem_univ mu)

theorem abs_eigenvalue_pow_le
    (A : Module.End ℝ E) (mu : A.Eigenvalues) (k : ℕ) :
    |(mu : ℝ)| ^ k ≤ eigenvalueAbsSum A ^ k :=
  pow_le_pow_left₀ (abs_nonneg (mu : ℝ))
    (abs_eigenvalue_le_eigenvalueAbsSum A mu) k

/-- Exterior power moments are bounded by exterior mass times the concrete
spectral power bound. -/
theorem abs_exteriorMoment_le
    (A : Module.End ℝ E) (hA : A.IsSymmetric)
    (nodes : Fin 4 → A.Eigenvalues) (v : E) (k : ℕ) :
    |exteriorMoment A hA nodes v k| ≤
      exteriorMass A hA nodes v * eigenvalueAbsSum A ^ k := by
  rw [exteriorMoment]
  calc
    |∑ mu ∈ Finset.univ with mu ∉ principalSpectrum A nodes,
        weight A hA v mu * (mu : ℝ) ^ k| ≤
        ∑ mu ∈ Finset.univ with mu ∉ principalSpectrum A nodes,
          |weight A hA v mu * (mu : ℝ) ^ k| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ mu ∈ Finset.univ with mu ∉ principalSpectrum A nodes,
          weight A hA v mu * |(mu : ℝ)| ^ k := by
      apply Finset.sum_congr rfl
      intro mu _
      rw [abs_mul, abs_of_nonneg (weight_nonneg A hA v mu), abs_pow]
    _ ≤ ∑ mu ∈ Finset.univ with mu ∉ principalSpectrum A nodes,
          weight A hA v mu * eigenvalueAbsSum A ^ k := by
      apply Finset.sum_le_sum
      intro mu _
      exact mul_le_mul_of_nonneg_left (abs_eigenvalue_pow_le A mu k)
        (weight_nonneg A hA v mu)
    _ = exteriorMass A hA nodes v * eigenvalueAbsSum A ^ k := by
      rw [exteriorMass, Finset.sum_mul]

/-- Every normalized principal power moment obeys the same spectral bound. -/
theorem abs_weightedMoment_principalWeights_le
    (A : Module.End ℝ E) (hA : A.IsSymmetric)
    (nodes : Fin 4 → A.Eigenvalues) (v : E)
    (hcomponent : ∀ i, component A hA v (nodes i) ≠ 0) (k : ℕ) :
    |FourNode.weightedMoment
        (fun i ↦ ((nodes i : A.Eigenvalues) : ℝ))
        (principalWeights A hA nodes v hcomponent) k| ≤
      eigenvalueAbsSum A ^ k := by
  rw [FourNode.weightedMoment]
  calc
    |∑ i, principalWeights A hA nodes v hcomponent i *
        ((nodes i : A.Eigenvalues) : ℝ) ^ k| ≤
        ∑ i, |principalWeights A hA nodes v hcomponent i *
          ((nodes i : A.Eigenvalues) : ℝ) ^ k| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, principalWeights A hA nodes v hcomponent i *
          |((nodes i : A.Eigenvalues) : ℝ)| ^ k := by
      apply Finset.sum_congr rfl
      intro i _
      rw [abs_mul, abs_of_nonneg
        ((principalWeights A hA nodes v hcomponent).nonneg i), abs_pow]
    _ ≤ ∑ i, principalWeights A hA nodes v hcomponent i *
          eigenvalueAbsSum A ^ k := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (abs_eigenvalue_pow_le A (nodes i) k)
        ((principalWeights A hA nodes v hcomponent).nonneg i)
    _ = eigenvalueAbsSum A ^ k := by
      rw [← Finset.sum_mul,
        (principalWeights A hA nodes v hcomponent).sum_eq_one, one_mul]

/-- Full intrinsic moments satisfy the corresponding finite spectral bound. -/
theorem abs_moment_le_eigenvalueAbsSum_pow_mul_norm_sq
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v : E) (k : ℕ) :
    |moment A v k| ≤ eigenvalueAbsSum A ^ k * ‖v‖ ^ 2 := by
  rw [moment_eq_sum_weight_mul_pow A hA v k]
  calc
    |∑ mu : A.Eigenvalues, weight A hA v mu * (mu : ℝ) ^ k| ≤
        ∑ mu : A.Eigenvalues, |weight A hA v mu * (mu : ℝ) ^ k| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ mu : A.Eigenvalues,
        weight A hA v mu * |(mu : ℝ)| ^ k := by
      apply Finset.sum_congr rfl
      intro mu _
      rw [abs_mul, abs_of_nonneg (weight_nonneg A hA v mu), abs_pow]
    _ ≤ ∑ mu : A.Eigenvalues,
        weight A hA v mu * eigenvalueAbsSum A ^ k := by
      apply Finset.sum_le_sum
      intro mu _
      exact mul_le_mul_of_nonneg_left (abs_eigenvalue_pow_le A mu k)
        (weight_nonneg A hA v mu)
    _ = eigenvalueAbsSum A ^ k * ‖v‖ ^ 2 := by
      rw [← Finset.sum_mul, sum_weight_eq_norm_sq]
      ring

/-- Exact decomposition of a full moment into selected and exterior parts. -/
theorem moment_eq_principalMoment_add_exteriorMoment
    (A : Module.End ℝ E) (hA : A.IsSymmetric)
    (nodes : Fin 4 → A.Eigenvalues) (hnodes : Function.Injective nodes)
    (v : E) (k : ℕ) :
    moment A v k = principalMoment A hA nodes v k +
      exteriorMoment A hA nodes v k := by
  rw [moment_eq_sum_weight_mul_pow A hA v k]
  rw [principalMoment, exteriorMoment]
  have hprincipal :
      ∑ mu ∈ principalSpectrum A nodes,
          weight A hA v mu * (mu : ℝ) ^ k =
        ∑ i, weight A hA v (nodes i) *
          ((nodes i : A.Eigenvalues) : ℝ) ^ k := by
    rw [principalSpectrum]
    exact Finset.sum_image hnodes.injOn
  rw [← hprincipal]
  have hpartition := Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset A.Eigenvalues)
    (fun mu ↦ mu ∈ principalSpectrum A nodes)
    (fun mu ↦ weight A hA v mu * (mu : ℝ) ^ k)
  have hfilter : (Finset.univ.filter fun mu : A.Eigenvalues ↦
      mu ∈ principalSpectrum A nodes) = principalSpectrum A nodes := by
    ext mu
    simp
  rw [hfilter] at hpartition
  exact hpartition.symm

/-- The selected raw moment is principal mass times the corresponding
normalized four-node moment. -/
theorem principalMoment_eq_mass_mul_weightedMoment
    (A : Module.End ℝ E) (hA : A.IsSymmetric)
    (nodes : Fin 4 → A.Eigenvalues) (v : E)
    (hcomponent : ∀ i, component A hA v (nodes i) ≠ 0) (k : ℕ) :
    principalMoment A hA nodes v k =
      principalMass A hA nodes v *
        FourNode.weightedMoment
          (fun i ↦ ((nodes i : A.Eigenvalues) : ℝ))
          (principalWeights A hA nodes v hcomponent) k := by
  rw [weightedMoment_principalWeights A hA nodes v hcomponent k]
  rw [principalMoment]
  field_simp [ne_of_gt (principalMass_pos_of_components_ne_zero
    A hA nodes v hcomponent)]

/-- Explicit perturbation bound between full intrinsic moments and normalized
principal moments. -/
theorem abs_moment_sub_weightedMoment_le
    (A : Module.End ℝ E) (hA : A.IsSymmetric)
    (nodes : Fin 4 → A.Eigenvalues) (hnodes : Function.Injective nodes)
    (v : E) (hv : ‖v‖ = 1)
    (hcomponent : ∀ i, component A hA v (nodes i) ≠ 0) (k : ℕ) :
    |moment A v k -
        FourNode.weightedMoment
          (fun i ↦ ((nodes i : A.Eigenvalues) : ℝ))
          (principalWeights A hA nodes v hcomponent) k| ≤
      2 * exteriorMass A hA nodes v * eigenvalueAbsSum A ^ k := by
  let m := FourNode.weightedMoment
    (fun i ↦ ((nodes i : A.Eigenvalues) : ℝ))
    (principalWeights A hA nodes v hcomponent) k
  let eps := exteriorMass A hA nodes v
  have hdecomp := moment_eq_principalMoment_add_exteriorMoment
    A hA nodes hnodes v k
  have hprincipal := principalMoment_eq_mass_mul_weightedMoment
    A hA nodes v hcomponent k
  have hmass := principalMass_eq_one_sub_exteriorMass
    A hA nodes hnodes v hv
  have heq : moment A v k - m =
      exteriorMoment A hA nodes v k - eps * m := by
    dsimp only [m, eps] at hprincipal hmass ⊢
    rw [hdecomp, hprincipal, hmass]
    ring
  rw [heq]
  calc
    |exteriorMoment A hA nodes v k - eps * m| ≤
        |exteriorMoment A hA nodes v k| + |eps * m| := abs_sub _ _
    _ ≤ eps * eigenvalueAbsSum A ^ k +
        eps * eigenvalueAbsSum A ^ k := by
      apply add_le_add
      · simpa only [eps] using abs_exteriorMoment_le A hA nodes v k
      · rw [abs_mul, abs_of_nonneg (exteriorMass_nonneg A hA nodes v)]
        exact mul_le_mul_of_nonneg_left
          (abs_weightedMoment_principalWeights_le
            A hA nodes v hcomponent k)
          (exteriorMass_nonneg A hA nodes v)
    _ = 2 * eps * eigenvalueAbsSum A ^ k := by ring

end

end Spectral
end Forsythe
