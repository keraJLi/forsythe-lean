import Forsythe.Arnoldi.LimitGrade
import Forsythe.Spectral.ComponentRecurrence
import Forsythe.Spectral.LimitEquation

/-!
# Orthogonality at parity cluster points

The Arnoldi factor at each iterate is orthogonal to `1` and `z` in
the polynomial inner product.  Along a convergent parity subsequence,
joint continuity in the factor coefficients and the vector passes these two
identities to the limiting even factor `p` or odd factor `q`.  The spectral
theorem then rewrites the identities using grouped eigenspace weights.
-/

set_option autoImplicit false

namespace Forsythe
namespace Spectral

open Filter Module.End Polynomial Set Topology WithLp
open scoped BigOperators

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The pairing with `1`, expressed in grouped spectral coordinates. -/
theorem polyInner_one_eq_sum_weight_mul_eval
    (A : Module.End ℝ E) (hA : A.IsSymmetric)
    (v : E) (p : MonicQuadratic) :
    polyInner A v p.toPolynomial 1 =
      ∑ mu : A.Eigenvalues,
        weight A hA v mu * p.toPolynomial.eval (mu : ℝ) := by
  rw [polyInner, polyApply_one]
  rw [← hA.diagonalization.inner_map_map]
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro mu _
  change inner ℝ
      (component A hA (polyApply A p.toPolynomial v) mu)
      (component A hA v mu) = _
  rw [component_polyApply]
  simp only [real_inner_smul_left, real_inner_self_eq_norm_sq, weight]
  ring

/-- The pairing with `z`, expressed in grouped spectral coordinates. -/
theorem polyInner_X_eq_sum_weight_mul_eigenvalue_mul_eval
    (A : Module.End ℝ E) (hA : A.IsSymmetric)
    (v : E) (p : MonicQuadratic) :
    polyInner A v p.toPolynomial X =
      ∑ mu : A.Eigenvalues,
        weight A hA v mu *
          ((mu : ℝ) * p.toPolynomial.eval (mu : ℝ)) := by
  rw [polyInner, polyApply_X]
  rw [← hA.diagonalization.inner_map_map]
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro mu _
  change inner ℝ
      (component A hA (polyApply A p.toPolynomial v) mu)
      (component A hA (A v) mu) = _
  rw [component_polyApply]
  have hcomponentA : component A hA (A v) mu =
      (mu : ℝ) • component A hA v mu :=
    hA.diagonalization_apply_self_apply v mu
  rw [hcomponentA]
  simp only [real_inner_smul_left, real_inner_smul_right,
    real_inner_self_eq_norm_sq, weight]
  ring

/-- The two grouped-coordinate orthogonality equations for a monic
quadratic at a vector. -/
def HasGroupedOrthogonality
    (A : Module.End ℝ E) (hA : A.IsSymmetric)
    (p : MonicQuadratic) (v : E) : Prop :=
  (∑ mu : A.Eigenvalues,
      weight A hA v mu * p.toPolynomial.eval (mu : ℝ)) = 0 ∧
  (∑ mu : A.Eigenvalues,
      weight A hA v mu *
        ((mu : ℝ) * p.toPolynomial.eval (mu : ℝ))) = 0

private theorem limit_orthogonality_of_subsequence
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v₀ : E)
    (P : ℕ → MonicQuadratic) (p : MonicQuadratic)
    (u : ℕ → E)
    (hP : Tendsto (fun j ↦ (P j).coeffPair) atTop (nhds p.coeffPair))
    (hu : Tendsto u atTop (nhds v₀))
    (hfactor : ∀ j, P j = arnoldiPoly2 A (u j))
    (hgrade : ∀ j, 3 ≤ grade A (u j)) :
    HasGroupedOrthogonality A hA p v₀ := by
  have haction := tendsto_polyApply_monicQuadratic A hP hu
  have hAaction : Tendsto (fun j ↦ A (u j)) atTop (nhds (A v₀)) :=
    (A.continuous_of_finiteDimensional.tendsto v₀).comp hu
  have hinnerOne : Tendsto
      (fun j ↦ inner ℝ (polyApply A (P j).toPolynomial (u j)) (u j))
      atTop (nhds (inner ℝ (polyApply A p.toPolynomial v₀) v₀)) :=
    haction.inner hu
  have hinnerX : Tendsto
      (fun j ↦ inner ℝ (polyApply A (P j).toPolynomial (u j)) (A (u j)))
      atTop (nhds (inner ℝ (polyApply A p.toPolynomial v₀) (A v₀))) :=
    haction.inner hAaction
  have hzeroOne : Tendsto
      (fun _ : ℕ ↦ (0 : ℝ)) atTop (nhds 0) := tendsto_const_nhds
  have hzeroX : Tendsto
      (fun _ : ℕ ↦ (0 : ℝ)) atTop (nhds 0) := tendsto_const_nhds
  have honeEq : inner ℝ (polyApply A p.toPolynomial v₀) v₀ = 0 := by
    apply tendsto_nhds_unique hinnerOne
    apply hzeroOne.congr'
    exact Eventually.of_forall fun j ↦ by
      change 0 = inner ℝ
        (polyApply A (P j).toPolynomial (u j)) (u j)
      rw [hfactor j]
      symm
      simpa only [polyInner, polyApply_one] using
        arnoldiPoly2_orthogonal_one A hA (u j) (hgrade j)
  have hXEq : inner ℝ (polyApply A p.toPolynomial v₀) (A v₀) = 0 := by
    apply tendsto_nhds_unique hinnerX
    apply hzeroX.congr'
    exact Eventually.of_forall fun j ↦ by
      change 0 = inner ℝ
        (polyApply A (P j).toPolynomial (u j)) (A (u j))
      rw [hfactor j]
      symm
      simpa only [polyInner, polyApply_X] using
        arnoldiPoly2_orthogonal_X A hA (u j) (hgrade j)
  constructor
  · rw [← polyInner_one_eq_sum_weight_mul_eval A hA v₀ p]
    simpa only [polyInner, polyApply_one] using honeEq
  · rw [← polyInner_X_eq_sum_weight_mul_eigenvalue_mul_eval A hA v₀ p]
    simpa only [polyInner, polyApply_X] using hXEq

/-- Every even parity cluster point satisfies the two grouped-coordinate
orthogonality equations for the limiting even factor `p`. -/
theorem even_grouped_orthogonality_of_mem_arnoldiClusterSet
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v₀ : E)
    (hgrade₀ : 3 ≤ grade A v₀) (p : MonicQuadratic)
    (hp : Tendsto
      (fun n ↦ (arnoldiFactorOrbit2 A v₀ (2 * n)).coeffPair)
      atTop (nhds p.coeffPair))
    {v : E}
    (hv : v ∈ clusterSet (fun k ↦ arnoldiOrbit2 A v₀ (2 * k))) :
    HasGroupedOrthogonality A hA p v := by
  obtain ⟨phi, hphiMono, hphiLimit⟩ :=
    (show MapClusterPt v atTop
      (fun k ↦ arnoldiOrbit2 A v₀ (2 * k)) from hv).tendsto_subseq
  have hphi : Tendsto phi atTop atTop := hphiMono.tendsto_atTop
  apply limit_orthogonality_of_subsequence A hA v
    (fun j ↦ arnoldiFactorOrbit2 A v₀ (2 * phi j)) p
    (fun j ↦ arnoldiOrbit2 A v₀ (2 * phi j))
  · simpa only [Function.comp_def] using hp.comp hphi
  · simpa only [Function.comp_def] using hphiLimit
  · intro j
    rfl
  · intro j
    exact grade_arnoldiOrbit2_of_grade_three A hA v₀ hgrade₀ (2 * phi j)

/-- Every odd parity cluster point satisfies the two grouped-coordinate
orthogonality equations for the limiting odd factor `q`. -/
theorem odd_grouped_orthogonality_of_mem_arnoldiClusterSet
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v₀ : E)
    (hgrade₀ : 3 ≤ grade A v₀) (q : MonicQuadratic)
    (hq : Tendsto
      (fun n ↦ (arnoldiFactorOrbit2 A v₀ (2 * n + 1)).coeffPair)
      atTop (nhds q.coeffPair))
    {v : E}
    (hv : v ∈ clusterSet (fun k ↦ arnoldiOrbit2 A v₀ (2 * k + 1))) :
    HasGroupedOrthogonality A hA q v := by
  obtain ⟨phi, hphiMono, hphiLimit⟩ :=
    (show MapClusterPt v atTop
      (fun k ↦ arnoldiOrbit2 A v₀ (2 * k + 1)) from hv).tendsto_subseq
  have hphi : Tendsto phi atTop atTop := hphiMono.tendsto_atTop
  apply limit_orthogonality_of_subsequence A hA v
    (fun j ↦ arnoldiFactorOrbit2 A v₀ (2 * phi j + 1)) q
    (fun j ↦ arnoldiOrbit2 A v₀ (2 * phi j + 1))
  · simpa only [Function.comp_def] using hq.comp hphi
  · simpa only [Function.comp_def] using hphiLimit
  · intro j
    rfl
  · intro j
    exact grade_arnoldiOrbit2_of_grade_three A hA v₀ hgrade₀
      (2 * phi j + 1)

end

end Spectral
end Forsythe
