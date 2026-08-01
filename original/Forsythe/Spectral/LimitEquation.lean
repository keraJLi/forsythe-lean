import Forsythe.Arnoldi.Asymptotics
import Forsythe.Arnoldi.FactorConvergence
import Forsythe.Arnoldi.Recurrence

/-!
# The polynomial limit equation at orbit cluster points

The exact two-step Arnoldi recurrence is passed to a parity cluster point.
Convergence of the two free coefficient pairs is enough: polynomial action
by a monic quadratic is written directly in terms of those coefficients.
No spectral coordinates are used in this passage.
-/

set_option autoImplicit false

namespace Forsythe
namespace Spectral

open Filter Metric Polynomial Topology

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Polynomial action by a monic quadratic is jointly continuous in its two
free coefficients and the vector. -/
theorem tendsto_polyApply_monicQuadratic
    {ι : Type*} {l : Filter ι}
    (A : Module.End ℝ E) {P : ι → MonicQuadratic} {p : MonicQuadratic}
    {u : ι → E} {v : E}
    (hP : Tendsto (fun i => (P i).coeffPair) l (𝓝 p.coeffPair))
    (hu : Tendsto u l (𝓝 v)) :
    Tendsto (fun i => polyApply A (P i).toPolynomial (u i)) l
      (𝓝 (polyApply A p.toPolynomial v)) := by
  have hlinearPair := (continuous_fst.tendsto p.coeffPair).comp hP
  have hconstantPair := (continuous_snd.tendsto p.coeffPair).comp hP
  have hlinear : Tendsto (fun i => (P i).linearCoeff) l
      (𝓝 p.linearCoeff) := by
    simpa only [Function.comp_def, MonicQuadratic.coeffPair] using hlinearPair
  have hconstant : Tendsto (fun i => (P i).constantCoeff) l
      (𝓝 p.constantCoeff) := by
    simpa only [Function.comp_def, MonicQuadratic.coeffPair] using hconstantPair
  have hA : Tendsto (fun i => A (u i)) l (𝓝 (A v)) :=
    (A.continuous_of_finiteDimensional.tendsto v).comp hu
  have hA2 : Tendsto (fun i => (A ^ 2) (u i)) l (𝓝 ((A ^ 2) v)) :=
    ((A ^ 2).continuous_of_finiteDimensional.tendsto v).comp hu
  simpa only [polyApply_monicQuadratic] using
    (hA2.add (hlinear.smul hA)).add (hconstant.smul hu)

/-- Action by a product of two monic quadratics is jointly continuous in
both coefficient pairs and the vector. -/
theorem tendsto_polyApply_monicQuadratic_mul
    {ι : Type*} {l : Filter ι}
    (A : Module.End ℝ E)
    {P Q : ι → MonicQuadratic} {p q : MonicQuadratic}
    {u : ι → E} {v : E}
    (hP : Tendsto (fun i => (P i).coeffPair) l (𝓝 p.coeffPair))
    (hQ : Tendsto (fun i => (Q i).coeffPair) l (𝓝 q.coeffPair))
    (hu : Tendsto u l (𝓝 v)) :
    Tendsto
      (fun i => polyApply A
        ((P i).toPolynomial * (Q i).toPolynomial) (u i)) l
      (𝓝 (polyApply A (p.toPolynomial * q.toPolynomial) v)) := by
  have hQaction := tendsto_polyApply_monicQuadratic A hQ hu
  have hPaction := tendsto_polyApply_monicQuadratic A hP hQaction
  simpa only [polyApply_mul] using hPaction

private theorem tendsto_even_index :
    Tendsto (fun k : ℕ => 2 * k) atTop atTop := by
  apply Filter.tendsto_atTop.2
  intro n
  exact eventually_atTop.2 ⟨n, fun b hb => by omega⟩

private theorem tendsto_odd_index :
    Tendsto (fun k : ℕ => 2 * k + 1) atTop atTop := by
  apply Filter.tendsto_atTop.2
  intro n
  exact eventually_atTop.2 ⟨n, fun b hb => by omega⟩

/-- The two-step shift of a convergent even-orbit subsequence has the same
limit. -/
theorem tendsto_even_arnoldiOrbit2_shift_two
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v₀ : E)
    (hv₀ : ‖v₀‖ = 1) (hgrade₀ : 3 ≤ grade A v₀)
    (phi : ℕ → ℕ) (hphi : Tendsto phi atTop atTop) {vStar : E}
    (hv : Tendsto (fun j => arnoldiOrbit2 A v₀ (2 * phi j))
      atTop (𝓝 vStar)) :
    Tendsto (fun j => arnoldiOrbit2 A v₀ (2 * phi j + 2))
      atTop (𝓝 vStar) := by
  have heven : Tendsto (fun j => 2 * phi j) atTop atTop :=
    tendsto_even_index.comp hphi
  have hdist := (arnoldiOrbit2_twoStep_dist_tendsto_zero
    A hA v₀ hv₀ hgrade₀).comp heven
  apply hv.congr_dist
  simpa only [Function.comp_def, dist_comm] using hdist

/-- The limit equation on an even-parity cluster subsequence. -/
theorem even_arnoldiOrbit2_limit_equation
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v₀ : E)
    (hv₀ : ‖v₀‖ = 1) (hgrade₀ : 3 ≤ grade A v₀)
    (p q : MonicQuadratic) (tau : ℝ)
    (hp : Tendsto
      (fun n => (arnoldiFactorOrbit2 A v₀ (2 * n)).coeffPair)
      atTop (𝓝 p.coeffPair))
    (hq : Tendsto
      (fun n => (arnoldiFactorOrbit2 A v₀ (2 * n + 1)).coeffPair)
      atTop (𝓝 q.coeffPair))
    (htau : Tendsto (arnoldiNormalizerOrbit2 A v₀) atTop (𝓝 tau))
    (phi : ℕ → ℕ) (hphi : Tendsto phi atTop atTop) (vStar : E)
    (hv : Tendsto (fun j => arnoldiOrbit2 A v₀ (2 * phi j))
      atTop (𝓝 vStar)) :
    polyApply A
      (p.toPolynomial * q.toPolynomial - Polynomial.C (tau ^ 2)) vStar = 0 := by
  let k : ℕ → ℕ := fun j => 2 * phi j
  have heven : Tendsto k atTop atTop := tendsto_even_index.comp hphi
  have hodd : Tendsto (fun j => 2 * phi j + 1) atTop atTop :=
    tendsto_odd_index.comp hphi
  have hp' : Tendsto
      (fun j => (arnoldiFactorOrbit2 A v₀ (k j)).coeffPair)
      atTop (𝓝 p.coeffPair) := by
    simpa only [Function.comp_def, k] using hp.comp hphi
  have hq' : Tendsto
      (fun j => (arnoldiFactorOrbit2 A v₀ (k j + 1)).coeffPair)
      atTop (𝓝 q.coeffPair) := by
    simpa only [Function.comp_def, k] using hq.comp hphi
  have hleft := tendsto_polyApply_monicQuadratic_mul A hp' hq' hv
  have hshift := tendsto_even_arnoldiOrbit2_shift_two
    A hA v₀ hv₀ hgrade₀ phi hphi hv
  have hsigma := htau.comp heven
  have hsigmaNext := htau.comp hodd
  have hright : Tendsto
      (fun j =>
        (arnoldiNormalizerOrbit2 A v₀ (k j) *
          arnoldiNormalizerOrbit2 A v₀ (k j + 1)) •
            arnoldiOrbit2 A v₀ (k j + 2))
      atTop (𝓝 ((tau * tau) • vStar)) := by
    simpa only [Function.comp_def, k] using
      (hsigma.mul hsigmaNext).smul hshift
  have hleft' : Tendsto
      (fun j =>
        (arnoldiNormalizerOrbit2 A v₀ (k j) *
          arnoldiNormalizerOrbit2 A v₀ (k j + 1)) •
            arnoldiOrbit2 A v₀ (k j + 2))
      atTop (𝓝 (polyApply A (p.toPolynomial * q.toPolynomial) vStar)) := by
    apply hleft.congr'
    exact Eventually.of_forall fun j =>
      arnoldiOrbit2_two_step_recurrence
        A hA v₀ hv₀ hgrade₀ (k j)
  have hlimit :
      polyApply A (p.toPolynomial * q.toPolynomial) vStar =
        (tau * tau) • vStar :=
    tendsto_nhds_unique hleft' hright
  rw [polyApply_sub, polyApply_C, hlimit]
  simp [pow_two]

/-- The two-step shift of a convergent odd-orbit subsequence has the same
limit. -/
theorem tendsto_odd_arnoldiOrbit2_shift_two
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v₀ : E)
    (hv₀ : ‖v₀‖ = 1) (hgrade₀ : 3 ≤ grade A v₀)
    (phi : ℕ → ℕ) (hphi : Tendsto phi atTop atTop) {vStar : E}
    (hv : Tendsto (fun j => arnoldiOrbit2 A v₀ (2 * phi j + 1))
      atTop (𝓝 vStar)) :
    Tendsto (fun j => arnoldiOrbit2 A v₀ (2 * phi j + 3))
      atTop (𝓝 vStar) := by
  have hodd : Tendsto (fun j => 2 * phi j + 1) atTop atTop :=
    tendsto_odd_index.comp hphi
  have hdist := (arnoldiOrbit2_twoStep_dist_tendsto_zero
    A hA v₀ hv₀ hgrade₀).comp hodd
  apply hv.congr_dist
  simpa [Function.comp_def, dist_comm, Nat.add_assoc] using hdist

/-- The limit equation on an odd-parity cluster subsequence. -/
theorem odd_arnoldiOrbit2_limit_equation
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v₀ : E)
    (hv₀ : ‖v₀‖ = 1) (hgrade₀ : 3 ≤ grade A v₀)
    (p q : MonicQuadratic) (tau : ℝ)
    (hp : Tendsto
      (fun n => (arnoldiFactorOrbit2 A v₀ (2 * n)).coeffPair)
      atTop (𝓝 p.coeffPair))
    (hq : Tendsto
      (fun n => (arnoldiFactorOrbit2 A v₀ (2 * n + 1)).coeffPair)
      atTop (𝓝 q.coeffPair))
    (htau : Tendsto (arnoldiNormalizerOrbit2 A v₀) atTop (𝓝 tau))
    (phi : ℕ → ℕ) (hphi : Tendsto phi atTop atTop) (vStar : E)
    (hv : Tendsto (fun j => arnoldiOrbit2 A v₀ (2 * phi j + 1))
      atTop (𝓝 vStar)) :
    polyApply A
      (p.toPolynomial * q.toPolynomial - Polynomial.C (tau ^ 2)) vStar = 0 := by
  let k : ℕ → ℕ := fun j => 2 * phi j + 1
  have hphiNext : Tendsto (fun j => phi j + 1) atTop atTop :=
    (tendsto_add_atTop_nat 1).comp hphi
  have hodd : Tendsto k atTop atTop := tendsto_odd_index.comp hphi
  have hevenNext : Tendsto (fun j => 2 * (phi j + 1)) atTop atTop :=
    tendsto_even_index.comp hphiNext
  have hq' : Tendsto
      (fun j => (arnoldiFactorOrbit2 A v₀ (k j)).coeffPair)
      atTop (𝓝 q.coeffPair) := by
    simpa only [Function.comp_def, k] using hq.comp hphi
  have hp' : Tendsto
      (fun j => (arnoldiFactorOrbit2 A v₀ (k j + 1)).coeffPair)
      atTop (𝓝 p.coeffPair) := by
    simpa [Function.comp_def, k, Nat.mul_add] using hp.comp hphiNext
  have hleft := tendsto_polyApply_monicQuadratic_mul A hq' hp' hv
  have hshift := tendsto_odd_arnoldiOrbit2_shift_two
    A hA v₀ hv₀ hgrade₀ phi hphi hv
  have hsigma := htau.comp hodd
  have hsigmaNext := htau.comp hevenNext
  have hright : Tendsto
      (fun j =>
        (arnoldiNormalizerOrbit2 A v₀ (k j) *
          arnoldiNormalizerOrbit2 A v₀ (k j + 1)) •
            arnoldiOrbit2 A v₀ (k j + 2))
      atTop (𝓝 ((tau * tau) • vStar)) := by
    simpa [Function.comp_def, k, Nat.mul_add] using
      (hsigma.mul hsigmaNext).smul hshift
  have hleft' : Tendsto
      (fun j =>
        (arnoldiNormalizerOrbit2 A v₀ (k j) *
          arnoldiNormalizerOrbit2 A v₀ (k j + 1)) •
            arnoldiOrbit2 A v₀ (k j + 2))
      atTop (𝓝 (polyApply A (q.toPolynomial * p.toPolynomial) vStar)) := by
    apply hleft.congr'
    exact Eventually.of_forall fun j =>
      arnoldiOrbit2_two_step_recurrence
        A hA v₀ hv₀ hgrade₀ (k j)
  have hlimit :
      polyApply A (q.toPolynomial * p.toPolynomial) vStar =
        (tau * tau) • vStar :=
    tendsto_nhds_unique hleft' hright
  rw [polyApply_sub, polyApply_C]
  rw [mul_comm p.toPolynomial q.toPolynomial, hlimit]
  simp [pow_two]

end

end Spectral
end Forsythe
