import Forsythe.Arnoldi.Continuity
import Forsythe.Arnoldi.MomentGram
import Forsythe.Dynamics.ClusterSet
import Mathlib.Topology.Order.Compact

/-!
# Uniform moment coercivity and coefficient bounds

The moment determinant is strictly positive at every grade-at-least-three
state.  Compactness therefore upgrades pointwise positivity to a uniform
lower bound.  We also record the resulting explicit bound for the two free
coefficients of the restart-two Arnoldi polynomial.  The coefficient norm is
the product norm fixed by `MonicQuadratic.coeffPair`.
-/

set_option autoImplicit false

namespace Forsythe

open Filter Set Topology
open scoped Topology

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Operator-norm bound for the `j`th moment on the unit sphere. -/
def momentOperatorBound (A : Module.End ℝ E) (j : ℕ) : ℝ :=
  ‖(Module.End.toContinuousLinearMap E) (A ^ j)‖

theorem momentOperatorBound_nonneg (A : Module.End ℝ E) (j : ℕ) :
    0 ≤ momentOperatorBound A j :=
  norm_nonneg _

/-- Cauchy–Schwarz and the operator norm give a state-independent moment
bound on unit vectors. -/
theorem abs_moment_le_momentOperatorBound
    (A : Module.End ℝ E) (v : E) (hv : ‖v‖ = 1) (j : ℕ) :
    |moment A v j| ≤ momentOperatorBound A j := by
  let Aj : E →L[ℝ] E := (Module.End.toContinuousLinearMap E) (A ^ j)
  calc
    |moment A v j| = ‖inner ℝ ((A ^ j) v) v‖ := by
      rw [Real.norm_eq_abs]
      rfl
    _ ≤ ‖(A ^ j) v‖ * ‖v‖ := norm_inner_le_norm _ _
    _ ≤ ‖Aj‖ * ‖v‖ * ‖v‖ := by
      gcongr
      exact Aj.le_opNorm v
    _ = momentOperatorBound A j := by
      rw [hv, mul_one, mul_one]
      rfl

/-- The explicit common bound for the two free Arnoldi coefficients obtained
from Cramer's rule, a determinant lower bound `delta`, and the four unit-sphere
moment bounds. -/
def arnoldiCoeffBound (A : Module.End ℝ E) (delta : ℝ) : ℝ :=
  max
      (momentOperatorBound A 1 * momentOperatorBound A 2 +
        momentOperatorBound A 0 * momentOperatorBound A 3)
      (momentOperatorBound A 1 * momentOperatorBound A 3 +
        momentOperatorBound A 2 ^ 2) /
    delta

theorem arnoldiCoeffBound_nonneg (A : Module.End ℝ E) {delta : ℝ}
    (hdelta : 0 < delta) :
    0 ≤ arnoldiCoeffBound A delta := by
  dsimp only [arnoldiCoeffBound]
  apply div_nonneg
  · apply le_trans (b :=
        momentOperatorBound A 1 * momentOperatorBound A 2 +
          momentOperatorBound A 0 * momentOperatorBound A 3)
    · exact add_nonneg
        (mul_nonneg (momentOperatorBound_nonneg A 1)
          (momentOperatorBound_nonneg A 2))
        (mul_nonneg (momentOperatorBound_nonneg A 0)
          (momentOperatorBound_nonneg A 3))
    · exact le_max_left _ _
  · exact hdelta.le

/-- Explicit product-norm bound for the Cramer-system solution. -/
theorem arnoldiPoly2_coeffPair_norm_le_of_det_lower_bound
    (A : Module.End ℝ E) (v : E) (hv : ‖v‖ = 1)
    {delta : ℝ} (hdelta : 0 < delta)
    (hdet : delta ≤ momentGramDet A v) :
    ‖(arnoldiPoly2 A v).coeffPair‖ ≤ arnoldiCoeffBound A delta := by
  let b : ℕ → ℝ := momentOperatorBound A
  have hb (j : ℕ) : |moment A v j| ≤ b j :=
    abs_moment_le_momentOperatorBound A v hv j
  have hb0 : 0 ≤ b 0 := momentOperatorBound_nonneg A 0
  have hb1 : 0 ≤ b 1 := momentOperatorBound_nonneg A 1
  have hb2 : 0 ≤ b 2 := momentOperatorBound_nonneg A 2
  have hb3 : 0 ≤ b 3 := momentOperatorBound_nonneg A 3
  have hdetPos : 0 < momentGramDet A v := hdelta.trans_le hdet
  have hlinearNumerator :
      |moment A v 1 * moment A v 2 - moment A v 0 * moment A v 3| ≤
        b 1 * b 2 + b 0 * b 3 := by
    calc
      |moment A v 1 * moment A v 2 - moment A v 0 * moment A v 3| ≤
          |moment A v 1 * moment A v 2| +
            |moment A v 0 * moment A v 3| := abs_sub _ _
      _ = |moment A v 1| * |moment A v 2| +
            |moment A v 0| * |moment A v 3| := by rw [abs_mul, abs_mul]
      _ ≤ b 1 * b 2 + b 0 * b 3 := by
        exact add_le_add
          (mul_le_mul (hb 1) (hb 2) (abs_nonneg _) hb1)
          (mul_le_mul (hb 0) (hb 3) (abs_nonneg _) hb0)
  have hconstantNumerator :
      |moment A v 1 * moment A v 3 - moment A v 2 ^ 2| ≤
        b 1 * b 3 + b 2 ^ 2 := by
    calc
      |moment A v 1 * moment A v 3 - moment A v 2 ^ 2| ≤
          |moment A v 1 * moment A v 3| + |moment A v 2 ^ 2| := abs_sub _ _
      _ = |moment A v 1| * |moment A v 3| + |moment A v 2| ^ 2 := by
        rw [abs_mul, abs_pow]
      _ ≤ b 1 * b 3 + b 2 ^ 2 := by
        apply add_le_add
        · exact mul_le_mul (hb 1) (hb 3) (abs_nonneg _) hb1
        · nlinarith [hb 2, abs_nonneg (moment A v 2)]
  have hlinear : |(arnoldiPoly2 A v).linearCoeff| ≤
      (b 1 * b 2 + b 0 * b 3) / delta := by
    rw [arnoldiPoly2, abs_div, abs_of_pos hdetPos]
    exact div_le_div₀ (by positivity) hlinearNumerator hdelta hdet
  have hconstant : |(arnoldiPoly2 A v).constantCoeff| ≤
      (b 1 * b 3 + b 2 ^ 2) / delta := by
    rw [arnoldiPoly2, abs_div, abs_of_pos hdetPos]
    exact div_le_div₀ (by positivity) hconstantNumerator hdelta hdet
  rw [MonicQuadratic.coeffPair, Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
  dsimp only [arnoldiCoeffBound, b]
  calc
    max |(arnoldiPoly2 A v).linearCoeff|
          |(arnoldiPoly2 A v).constantCoeff| ≤
        max
          ((momentOperatorBound A 1 * momentOperatorBound A 2 +
            momentOperatorBound A 0 * momentOperatorBound A 3) / delta)
          ((momentOperatorBound A 1 * momentOperatorBound A 3 +
            momentOperatorBound A 2 ^ 2) / delta) :=
      max_le_max hlinear hconstant
    _ = max
          (momentOperatorBound A 1 * momentOperatorBound A 2 +
            momentOperatorBound A 0 * momentOperatorBound A 3)
          (momentOperatorBound A 1 * momentOperatorBound A 3 +
            momentOperatorBound A 2 ^ 2) / delta :=
      max_div_div_right hdelta.le _ _

/-- On a compact family of grade-at-least-three states, the `2 × 2` moment
Gram systems have a common positive determinant lower bound. -/
theorem exists_uniform_momentGramDet_lower_bound_on_compact
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (K : Set E)
    (hK : IsCompact K) (hgrade : ∀ v ∈ K, 3 ≤ grade A v) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ v ∈ K, delta ≤ momentGramDet A v := by
  exact hK.exists_forall_le' (continuous_momentGramDet A).continuousOn
    (fun v hv ↦ momentGramDet_pos_of_grade_three A hA v (hgrade v hv))

/-- Bundled compact-family form: the determinant is uniformly coercive and
the two free Arnoldi coefficients are uniformly bounded in the product norm.
The displayed coefficient bound is the explicit Cramer bound associated with
the chosen determinant lower bound. -/
theorem exists_uniform_momentGramDet_and_coeffPair_bound_on_compact
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (K : Set E)
    (hK : IsCompact K) (hunit : ∀ v ∈ K, ‖v‖ = 1)
    (hgrade : ∀ v ∈ K, 3 ≤ grade A v) :
    ∃ delta M : ℝ, 0 < delta ∧ 0 ≤ M ∧
      ∀ v ∈ K,
        delta ≤ momentGramDet A v ∧
          ‖(arnoldiPoly2 A v).coeffPair‖ ≤ M := by
  obtain ⟨delta, hdelta, hdet⟩ :=
    exists_uniform_momentGramDet_lower_bound_on_compact A hA K hK hgrade
  refine ⟨delta, arnoldiCoeffBound A delta, hdelta,
    arnoldiCoeffBound_nonneg A hdelta, ?_⟩
  intro v hv
  exact ⟨hdet v hv, arnoldiPoly2_coeffPair_norm_le_of_det_lower_bound
    A v (hunit v hv) hdelta (hdet v hv)⟩

/-- A precompact sequence approaches its cluster set.  Positivity of the
moment determinant on all cluster points is therefore eventually uniform. -/
theorem eventually_uniform_momentGramDet_of_cluster_grade_three
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (u : ℕ → E)
    (hu : IsCompact (closure (range u)))
    (hgrade : ∀ v ∈ clusterSet u, 3 ≤ grade A v) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ᶠ k in atTop, delta ≤ momentGramDet A (u k) := by
  let C := clusterSet u
  obtain ⟨gamma, hgamma, hgammaLower⟩ :=
    exists_uniform_momentGramDet_lower_bound_on_compact A hA C
      (isCompact_clusterSet hu) hgrade
  let delta := gamma / 2
  have hdelta : 0 < delta := div_pos hgamma (by norm_num)
  have htend : Tendsto u atTop (nhdsSet C) := by
    apply hu.tendsto_nhdsSet_of_mapClusterPt
    · exact Eventually.of_forall fun k ↦ subset_closure ⟨k, rfl⟩
    · intro v _ hv
      exact hv
  let V : Set E := {v | delta < momentGramDet A v}
  have hVopen : IsOpen V :=
    isOpen_lt continuous_const (continuous_momentGramDet A)
  have hCV : C ⊆ V := by
    intro v hv
    dsimp only [V]
    exact lt_of_lt_of_le (by dsimp only [delta]; linarith) (hgammaLower v hv)
  have heventually : ∀ᶠ k in atTop, u k ∈ V :=
    htend.eventually (hVopen.mem_nhdsSet.mpr hCV)
  refine ⟨delta, hdelta, ?_⟩
  exact heventually.mono fun k hk ↦ le_of_lt hk

/-- Uniform coercivity plus unit normalization gives an explicit eventual
bound in the fixed product norm on the Arnoldi coefficient pair. -/
theorem eventually_uniform_momentGramDet_and_coeffPair_bound
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (u : ℕ → E)
    (hu : IsCompact (closure (range u)))
    (hunit : ∀ k, ‖u k‖ = 1)
    (hgrade : ∀ v ∈ clusterSet u, 3 ≤ grade A v) :
    ∃ delta M : ℝ, 0 < delta ∧ 0 ≤ M ∧
      ∀ᶠ k in atTop,
        delta ≤ momentGramDet A (u k) ∧
          ‖(arnoldiPoly2 A (u k)).coeffPair‖ ≤ M := by
  obtain ⟨delta, hdelta, hdet⟩ :=
    eventually_uniform_momentGramDet_of_cluster_grade_three A hA u hu hgrade
  refine ⟨delta, arnoldiCoeffBound A delta, hdelta,
    arnoldiCoeffBound_nonneg A hdelta, ?_⟩
  filter_upwards [hdet] with k hk
  exact ⟨hk, arnoldiPoly2_coeffPair_norm_le_of_det_lower_bound
    A (u k) (hunit k) hdelta hk⟩

end

end Forsythe
