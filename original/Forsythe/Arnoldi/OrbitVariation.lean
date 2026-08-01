import Forsythe.Arnoldi.FactorConvergence
import Forsythe.Arnoldi.OrbitCoercivity

/-!
# Unconditional factor variation on an Arnoldi orbit

This module closes the analytic estimate left conditional in
`Forsythe.Arnoldi.Variation`.  Uniform moment-Gram coercivity and the explicit
tail coefficient bound are combined with the three-step identity.  All norms
on free polynomial coefficients are the concrete product norm fixed by
`MonicQuadratic.coeffPair`.
-/

set_option autoImplicit false

namespace Forsythe

open Filter Polynomial Topology

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

namespace MonicQuadratic

theorem abs_linearCoeff_le_coeffPair_norm (p : MonicQuadratic) :
    |p.linearCoeff| ≤ ‖p.coeffPair‖ := by
  rw [coeffPair, Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
  exact le_max_left _ _

theorem abs_constantCoeff_le_coeffPair_norm (p : MonicQuadratic) :
    |p.constantCoeff| ≤ ‖p.coeffPair‖ := by
  rw [coeffPair, Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
  exact le_max_right _ _

end MonicQuadratic

namespace Arnoldi

/-- The height sequence `H_k = sigma_k²` attached to the concrete orbit. -/
def arnoldiHeightOrbit2 (A : Module.End ℝ E) (v₀ : E) (k : ℕ) : ℝ :=
  quadraticStepHeight (arnoldiNormalizerOrbit2 A v₀) k

/-- Fixed operator-norm coefficient for a degree-at-most-one polynomial. -/
def linearPolynomialActionBound (A : Module.End ℝ E) : ℝ :=
  ‖Module.End.toContinuousLinearMap E A‖ + 1

theorem linearPolynomialActionBound_pos (A : Module.End ℝ E) :
    0 < linearPolynomialActionBound A := by
  dsimp only [linearPolynomialActionBound]
  positivity

/-- Fixed operator-norm coefficient for a monic quadratic whose coefficient
pair has norm at most `M`. -/
def monicQuadraticActionBound (A : Module.End ℝ E) (M : ℝ) : ℝ :=
  ‖(Module.End.toContinuousLinearMap E) (A ^ 2)‖ +
    M * linearPolynomialActionBound A

theorem monicQuadraticActionBound_nonneg (A : Module.End ℝ E) {M : ℝ}
    (hM : 0 ≤ M) : 0 ≤ monicQuadraticActionBound A M := by
  dsimp only [monicQuadraticActionBound]
  exact add_nonneg (norm_nonneg _)
    (mul_nonneg hM (linearPolynomialActionBound_pos A).le)

/-- Explicit action bound for a linear polynomial in the fixed product norm
of its two coefficients. -/
theorem norm_polyApply_linearPolynomial_le
    (A : Module.End ℝ E) (a b : ℝ) (x : E) :
    ‖polyApply A (linearPolynomial a b) x‖ ≤
      linearPolynomialActionBound A * ‖(a, b)‖ * ‖x‖ := by
  let Ac : E →L[ℝ] E := Module.End.toContinuousLinearMap E A
  have ha : |a| ≤ ‖(a, b)‖ := by
    rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
    exact le_max_left _ _
  have hb : |b| ≤ ‖(a, b)‖ := by
    rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
    exact le_max_right _ _
  have hA : ‖A x‖ ≤ ‖Ac‖ * ‖x‖ := Ac.le_opNorm x
  rw [polyApply_linearPolynomial]
  calc
    ‖a • A x + b • x‖ ≤ ‖a • A x‖ + ‖b • x‖ := norm_add_le _ _
    _ = |a| * ‖A x‖ + |b| * ‖x‖ := by
      simp only [norm_smul, Real.norm_eq_abs]
    _ ≤ ‖(a, b)‖ * (‖Ac‖ * ‖x‖) + ‖(a, b)‖ * ‖x‖ := by
      gcongr
    _ = linearPolynomialActionBound A * ‖(a, b)‖ * ‖x‖ := by
      dsimp only [linearPolynomialActionBound, Ac]
      ring

/-- Explicit action bound for a monic quadratic with bounded coefficient
pair. -/
theorem norm_polyApply_monicQuadratic_le
    (A : Module.End ℝ E) (p : MonicQuadratic) {M : ℝ}
    (hp : ‖p.coeffPair‖ ≤ M) (x : E) :
    ‖polyApply A p.toPolynomial x‖ ≤
      monicQuadraticActionBound A M * ‖x‖ := by
  let Ac : E →L[ℝ] E := Module.End.toContinuousLinearMap E A
  let A2c : E →L[ℝ] E := (Module.End.toContinuousLinearMap E) (A ^ 2)
  have hlin : |p.linearCoeff| ≤ M :=
    (p.abs_linearCoeff_le_coeffPair_norm).trans hp
  have hconst : |p.constantCoeff| ≤ M :=
    (p.abs_constantCoeff_le_coeffPair_norm).trans hp
  have hM : 0 ≤ M := (norm_nonneg p.coeffPair).trans hp
  have hA : ‖A x‖ ≤ ‖Ac‖ * ‖x‖ := Ac.le_opNorm x
  have hA2 : ‖(A ^ 2) x‖ ≤ ‖A2c‖ * ‖x‖ := A2c.le_opNorm x
  rw [polyApply_monicQuadratic]
  calc
    ‖(A ^ 2) x + p.linearCoeff • A x + p.constantCoeff • x‖ ≤
        ‖(A ^ 2) x‖ + ‖p.linearCoeff • A x‖ +
          ‖p.constantCoeff • x‖ := by
      exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ = ‖(A ^ 2) x‖ + |p.linearCoeff| * ‖A x‖ +
          |p.constantCoeff| * ‖x‖ := by
      simp only [norm_smul, Real.norm_eq_abs]
    _ ≤ ‖A2c‖ * ‖x‖ + M * (‖Ac‖ * ‖x‖) + M * ‖x‖ := by
      gcongr
    _ = monicQuadraticActionBound A M * ‖x‖ := by
      dsimp only [monicQuadraticActionBound, linearPolynomialActionBound, Ac, A2c]
      ring

/-- The `1,X` moment form controls the concrete product norm of linear
coefficients.  The constant is explicit in the determinant floor and the
unit-sphere second-moment operator bound. -/
theorem linearPolynomial_coercive_of_det_lower_bound
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v : E)
    (hv : ‖v‖ = 1) {delta : ℝ} (_hdelta : 0 < delta)
    (hdet : delta ≤ momentGramDet A v) (a b : ℝ) :
    (delta / max 1 (momentOperatorBound A 2)) * ‖(a, b)‖ ^ 2 ≤
      polyInner A v (linearPolynomial a b) (linearPolynomial a b) := by
  let m₁ := moment A v 1
  let m₂ := moment A v 2
  let F := polyInner A v (linearPolynomial a b) (linearPolynomial a b)
  let T := max 1 (momentOperatorBound A 2)
  have hm₂nonneg : 0 ≤ m₂ := by
    dsimp only [m₂]
    rw [moment_two A hA]
    exact real_inner_self_nonneg
  have hm₂bound : m₂ ≤ momentOperatorBound A 2 :=
    le_trans (le_abs_self m₂)
      (abs_moment_le_momentOperatorBound A v hv 2)
  have hTpos : 0 < T := by
    dsimp only [T]
    exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hm₂T : m₂ ≤ T :=
    hm₂bound.trans (le_max_right _ _)
  have honeT : 1 ≤ T := le_max_left _ _
  have hFnonneg : 0 ≤ F := by
    dsimp only [F, polyInner]
    exact real_inner_self_nonneg
  have hinnerOneLeft : inner ℝ v (A v) = moment A v 1 := by
    rw [real_inner_comm]
    exact (moment_one A v).symm
  have hFformula : F = a ^ 2 * m₂ + 2 * a * b * m₁ + b ^ 2 := by
    dsimp only [F, m₁, m₂]
    rw [polyInner, polyApply_linearPolynomial]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right]
    rw [← moment_two A hA, hinnerOneLeft, ← moment_one]
    rw [real_inner_self_eq_norm_sq, hv]
    norm_num
    ring
  have hdetFormula : momentGramDet A v = m₂ - m₁ ^ 2 := by
    dsimp only [m₁, m₂, momentGramDet]
    rw [moment_zero, real_inner_self_eq_norm_sq, hv]
    norm_num
  have haDet : momentGramDet A v * a ^ 2 ≤ F := by
    rw [hdetFormula, hFformula]
    nlinarith [sq_nonneg (m₁ * a + b)]
  have hbDet : momentGramDet A v * b ^ 2 ≤ m₂ * F := by
    rw [hdetFormula, hFformula]
    nlinarith [sq_nonneg (m₂ * a + m₁ * b)]
  have haDelta : delta * a ^ 2 ≤ T * F := by
    calc
      delta * a ^ 2 ≤ momentGramDet A v * a ^ 2 :=
        mul_le_mul_of_nonneg_right hdet (sq_nonneg a)
      _ ≤ F := haDet
      _ ≤ T * F := by nlinarith
  have hbDelta : delta * b ^ 2 ≤ T * F := by
    calc
      delta * b ^ 2 ≤ momentGramDet A v * b ^ 2 :=
        mul_le_mul_of_nonneg_right hdet (sq_nonneg b)
      _ ≤ m₂ * F := hbDet
      _ ≤ T * F := mul_le_mul_of_nonneg_right hm₂T hFnonneg
  have hnormDelta : delta * ‖(a, b)‖ ^ 2 ≤ T * F := by
    rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
    by_cases hab : |a| ≤ |b|
    · rw [max_eq_right hab, sq_abs]
      exact hbDelta
    · rw [max_eq_left (le_of_not_ge hab), sq_abs]
      exact haDelta
  change (delta / T) * ‖(a, b)‖ ^ 2 ≤ F
  rw [show delta / T * ‖(a, b)‖ ^ 2 =
      (delta * ‖(a, b)‖ ^ 2) / T by ring]
  apply (div_le_iff₀ hTpos).2
  simpa only [mul_comm] using hnormDelta

/-- The three-step identity, Cauchy--Schwarz, and explicit polynomial action
bounds give the upper half of factor variation. -/
theorem quadraticStep_three_step_upper
    (A : Module.End ℝ E) (hA : A.IsSymmetric)
    {v₀ v₁ v₂ v₃ : E} {p₀ p₁ p₂ : MonicQuadratic}
    {σ₀ σ₁ σ₂ M : ℝ}
    (h₀ : IsQuadraticStep A v₀ v₁ p₀ σ₀)
    (h₁ : IsQuadraticStep A v₁ v₂ p₁ σ₁)
    (h₂ : IsQuadraticStep A v₂ v₃ p₂ σ₂)
    (hp₀ : ‖p₀.coeffPair‖ ≤ M) :
    polyInner A v₂ (p₂.toPolynomial - p₀.toPolynomial)
        (p₂.toPolynomial - p₀.toPolynomial) ≤
      (monicQuadraticActionBound A M * linearPolynomialActionBound A /
          σ₁ ^ 2) *
        p₂.coeffDist p₀ * (σ₁ ^ 2 - σ₀ ^ 2) := by
  let a := p₂.linearCoeff - p₀.linearCoeff
  let b := p₂.constantCoeff - p₀.constantCoeff
  let D := p₂.toPolynomial - p₀.toPolynomial
  let R := p₀.toPolynomial * p₁.toPolynomial - C (σ₀ ^ 2)
  let w := polyApply A R v₀
  let F := polyInner A v₂ D D
  let I := polyInner A v₀ (p₀.toPolynomial * D) (R * R)
  let Lp := monicQuadraticActionBound A M
  let Ld := linearPolynomialActionBound A
  let d := p₂.coeffDist p₀
  have hD : D = linearPolynomial a b := by
    exact monicQuadratic_sub p₂ p₀
  have hd : ‖(a, b)‖ = d := by
    dsimp only [a, b, d, MonicQuadratic.coeffDist,
      MonicQuadratic.coeffPair]
    rfl
  have hLp : 0 ≤ Lp := by
    apply monicQuadraticActionBound_nonneg A
    exact (norm_nonneg p₀.coeffPair).trans hp₀
  have hLd : 0 < Ld := linearPolynomialActionBound_pos A
  have hdnonneg : 0 ≤ d := MonicQuadratic.coeffDist_nonneg _ _
  have hdelta : 0 ≤ σ₁ ^ 2 - σ₀ ^ 2 := by
    have henergy := quadraticStep_energy A hA h₀ h₁
    have hnonneg : 0 ≤ polyInner A v₀ R R := by
      dsimp only [R, polyInner]
      exact real_inner_self_nonneg
    dsimp only at henergy
    have hσ₀sq : 0 < σ₀ ^ 2 := sq_pos_of_pos h₀.sigma_pos
    nlinarith
  have hFnonneg : 0 ≤ F := by
    dsimp only [F, polyInner]
    exact real_inner_self_nonneg
  have hthree : F = -I / (σ₀ ^ 2 * σ₁ ^ 2) := by
    have ht := quadraticStep_three_step A hA h₀ h₁ h₂ a b
    dsimp only at ht
    rw [← hD] at ht
    exact ht
  have hdenpos : 0 < σ₀ ^ 2 * σ₁ ^ 2 :=
    mul_pos (sq_pos_of_pos h₀.sigma_pos) (sq_pos_of_pos h₁.sigma_pos)
  have hFabs : F = |I| / (σ₀ ^ 2 * σ₁ ^ 2) := by
    calc
      F = |F| := (abs_of_nonneg hFnonneg).symm
      _ = |-I / (σ₀ ^ 2 * σ₁ ^ 2)| := congrArg abs hthree
      _ = |I| / (σ₀ ^ 2 * σ₁ ^ 2) := by
        rw [abs_div, abs_neg, abs_of_pos hdenpos]
  have hbalance : I = polyInner A v₀ ((p₀.toPolynomial * D) * R) R := by
    dsimp only [I]
    apply polyInner_eq_of_mul_eq A hA
    ring
  have hfirst : ‖polyApply A ((p₀.toPolynomial * D) * R) v₀‖ ≤
      Lp * (Ld * d * ‖w‖) := by
    rw [polyApply_mul, polyApply_mul]
    dsimp only [w, Lp, Ld]
    apply (norm_polyApply_monicQuadratic_le A p₀ hp₀ _).trans
    apply mul_le_mul_of_nonneg_left _
      (monicQuadraticActionBound_nonneg A
        ((norm_nonneg p₀.coeffPair).trans hp₀))
    rw [hD]
    simpa only [hd] using norm_polyApply_linearPolynomial_le A a b w
  have hI : |I| ≤ Lp * Ld * d * ‖w‖ ^ 2 := by
    rw [hbalance]
    dsimp only [polyInner]
    calc
      |inner ℝ (polyApply A ((p₀.toPolynomial * D) * R) v₀)
          (polyApply A R v₀)| ≤
          ‖polyApply A ((p₀.toPolynomial * D) * R) v₀‖ *
            ‖polyApply A R v₀‖ := abs_real_inner_le_norm _ _
      _ ≤ (Lp * (Ld * d * ‖w‖)) * ‖w‖ := by
        exact mul_le_mul_of_nonneg_right hfirst (norm_nonneg w)
      _ = Lp * Ld * d * ‖w‖ ^ 2 := by ring
  have hwEnergy : ‖w‖ ^ 2 = σ₀ ^ 2 * (σ₁ ^ 2 - σ₀ ^ 2) := by
    have he := quadraticStep_energy A hA h₀ h₁
    dsimp only at he
    dsimp only [w, R]
    simpa only [polyInner, real_inner_self_eq_norm_sq] using he
  change F ≤ (Lp * Ld / σ₁ ^ 2) * d * (σ₁ ^ 2 - σ₀ ^ 2)
  rw [hFabs]
  have hquotient :
      |I| / (σ₀ ^ 2 * σ₁ ^ 2) ≤
        (Lp * Ld * d * ‖w‖ ^ 2) / (σ₀ ^ 2 * σ₁ ^ 2) :=
    (div_le_div_iff_of_pos_right hdenpos).2 hI
  calc
    |I| / (σ₀ ^ 2 * σ₁ ^ 2) ≤
        (Lp * Ld * d * ‖w‖ ^ 2) / (σ₀ ^ 2 * σ₁ ^ 2) := hquotient
    _ = (Lp * Ld / σ₁ ^ 2) * d * (σ₁ ^ 2 - σ₀ ^ 2) := by
      rw [hwEnergy]
      field_simp [h₀.sigma_ne, h₁.sigma_ne]

/-- The unconditional, uniform factor-variation estimate on an Arnoldi orbit
tail.  The tail begins only because uniform Gram coercivity is obtained from
the compact cluster set. -/
theorem exists_arnoldiOrbit2_factor_variation_tail
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v₀ : E)
    (hv₀ : ‖v₀‖ = 1) (hgrade₀ : 3 ≤ grade A v₀) :
    ∃ K : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ k, K ≤ k →
      (arnoldiFactorOrbit2 A v₀ (k + 2)).coeffDist
          (arnoldiFactorOrbit2 A v₀ k) ≤
        C * heightIncrement (arnoldiHeightOrbit2 A v₀) k := by
  let v := arnoldiOrbit2 A v₀
  let P := arnoldiFactorOrbit2 A v₀
  let σ := arnoldiNormalizerOrbit2 A v₀
  let H := arnoldiHeightOrbit2 A v₀
  obtain ⟨delta, M, hdelta, hM, htail⟩ :=
    exists_eventually_arnoldiOrbit2_momentGramDet_and_coeffPair_bound
      A hA v₀ hv₀ hgrade₀
  obtain ⟨K, hK⟩ := eventually_atTop.1 htail
  let T := max 1 (momentOperatorBound A 2)
  let kappa := delta / T
  let B := monicQuadraticActionBound A M * linearPolynomialActionBound A
  let H₀ := H 0
  let Cvar := (B + 1) / (kappa * H₀)
  have hTpos : 0 < T := by
    dsimp only [T]
    exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hkappa : 0 < kappa := div_pos hdelta hTpos
  have hsteps : IsQuadraticStepSequence A v P σ := by
    simpa only [v, P, σ] using
      arnoldiOrbit2_isQuadraticStepSequence_of_grade_three
        A hA v₀ hv₀ hgrade₀
  have hH₀ : 0 < H₀ := by
    dsimp only [H₀, H, arnoldiHeightOrbit2, quadraticStepHeight]
    exact sq_pos_of_pos (hsteps.sigma_pos 0)
  have hBnonneg : 0 ≤ B := by
    dsimp only [B]
    exact mul_nonneg (monicQuadraticActionBound_nonneg A hM)
      (linearPolynomialActionBound_pos A).le
  have hCvar : 0 < Cvar := by
    dsimp only [Cvar]
    exact div_pos (by linarith) (mul_pos hkappa hH₀)
  refine ⟨K, Cvar, hCvar, ?_⟩
  intro k hk
  have hkBound := hK k hk
  have hkTwoBound := hK (k + 2) (hk.trans (Nat.le_add_right k 2))
  let a := (P (k + 2)).linearCoeff - (P k).linearCoeff
  let b := (P (k + 2)).constantCoeff - (P k).constantCoeff
  let D := (P (k + 2)).toPolynomial - (P k).toPolynomial
  let F := polyInner A (v (k + 2)) D D
  let d := (P (k + 2)).coeffDist (P k)
  let eps := H (k + 1) - H k
  have hD : D = linearPolynomial a b := monicQuadratic_sub _ _
  have hd : ‖(a, b)‖ = d := by
    dsimp only [a, b, d, MonicQuadratic.coeffDist,
      MonicQuadratic.coeffPair]
    rfl
  have hvTwo : ‖v (k + 2)‖ = 1 := hsteps.norm_eq_one (k + 2)
  have hlower : kappa * d ^ 2 ≤ F := by
    have hc := linearPolynomial_coercive_of_det_lower_bound A hA
      (v (k + 2)) hvTwo hdelta hkTwoBound.1 a b
    rw [← hD] at hc
    simpa only [kappa, T, hd, F] using hc
  have hupperRaw : F ≤ (B / σ (k + 1) ^ 2) * d * eps := by
    have hu := quadraticStep_three_step_upper A hA
      (hsteps.step k) (hsteps.step (k + 1)) (hsteps.step (k + 2)) hkBound.2
    simpa only [F, D, B, d, eps, H, arnoldiHeightOrbit2,
      quadraticStepHeight] using hu
  have heps : 0 ≤ eps := by
    have hm := hsteps.height_le_succ hA k
    simpa only [eps, H, arnoldiHeightOrbit2] using sub_nonneg.mpr hm
  have hdnonneg : 0 ≤ d := MonicQuadratic.coeffDist_nonneg _ _
  have hHmono : H₀ ≤ σ (k + 1) ^ 2 := by
    have hm := hsteps.height_monotone hA (Nat.zero_le (k + 1))
    simpa only [H₀, H, arnoldiHeightOrbit2, quadraticStepHeight] using hm
  have hfrac : B / σ (k + 1) ^ 2 ≤ (B + 1) / H₀ := by
    exact div_le_div₀ (by linarith) (by linarith) hH₀ hHmono
  have hupper : F ≤ kappa * Cvar * eps * d := by
    calc
      F ≤ (B / σ (k + 1) ^ 2) * d * eps := hupperRaw
      _ ≤ ((B + 1) / H₀) * d * eps := by gcongr
      _ = kappa * Cvar * eps * d := by
        dsimp only [Cvar]
        field_simp [ne_of_gt hkappa, ne_of_gt hH₀]
  have hresult := factor_variation_of_coercive
    (P (k + 2)) (P k) kappa M Cvar eps F hkappa hM hCvar.le heps
    hkTwoBound.2 hkBound.2 hlower (fun _ ↦ hupper)
  simpa only [P, H, d, eps, heightIncrement] using hresult

/-- Manuscript-facing factor variation with one constant valid at every
index.  The analytic coercivity argument supplies a tail constant.  On the
finite prefix, a zero height increment already gives exact two-step return
and hence zero factor distance; the remaining positive-increment ratios can
therefore be absorbed into one finite sum. -/
theorem exists_arnoldiOrbit2_factor_variation
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v₀ : E)
    (hv₀ : ‖v₀‖ = 1) (hgrade₀ : 3 ≤ grade A v₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ k,
      (arnoldiFactorOrbit2 A v₀ (k + 2)).coeffDist
          (arnoldiFactorOrbit2 A v₀ k) ≤
        C * heightIncrement (arnoldiHeightOrbit2 A v₀) k := by
  let v := arnoldiOrbit2 A v₀
  let P := arnoldiFactorOrbit2 A v₀
  let H := arnoldiHeightOrbit2 A v₀
  obtain ⟨K, Ctail, hCtail, htail⟩ :=
    exists_arnoldiOrbit2_factor_variation_tail A hA v₀ hv₀ hgrade₀
  have hsteps := arnoldiOrbit2_isQuadraticStepSequence_of_grade_three
    A hA v₀ hv₀ hgrade₀
  have hinc (k : ℕ) : 0 ≤ heightIncrement H k := by
    have hm := hsteps.height_le_succ hA k
    simpa only [heightIncrement, H, arnoldiHeightOrbit2] using sub_nonneg.mpr hm
  have hdist_zero (k : ℕ) (hk : heightIncrement H k = 0) :
      (P (k + 2)).coeffDist (P k) = 0 := by
    have hheight : H (k + 1) = H k := sub_eq_zero.mp hk
    have hvectors : v (k + 2) = v k := by
      apply (hsteps.height_eq_iff_two_step_eq hA k).mp
      simpa only [H, arnoldiHeightOrbit2] using hheight
    have hfactors : P (k + 2) = P k := by
      dsimp only [P, arnoldiFactorOrbit2, v] at hvectors ⊢
      rw [hvectors]
    rw [hfactors, MonicQuadratic.coeffDist_self]
  let ratio : ℕ → ℝ := fun k ↦
    (P (k + 2)).coeffDist (P k) / heightIncrement H k
  let Cprefix : ℝ := Finset.sum (Finset.range K) ratio
  have hratio (k : ℕ) : 0 ≤ ratio k := by
    exact div_nonneg (MonicQuadratic.coeffDist_nonneg _ _) (hinc k)
  have hCprefix : 0 ≤ Cprefix := by
    exact Finset.sum_nonneg fun k _ ↦ hratio k
  refine ⟨Ctail + Cprefix, add_pos_of_pos_of_nonneg hCtail hCprefix, ?_⟩
  intro k
  by_cases hkTail : K ≤ k
  · calc
      (P (k + 2)).coeffDist (P k) ≤
          Ctail * heightIncrement H k := htail k hkTail
      _ ≤ (Ctail + Cprefix) * heightIncrement H k := by
        exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hCprefix) (hinc k)
  · have hkMem : k ∈ Finset.range K := Finset.mem_range.mpr (lt_of_not_ge hkTail)
    by_cases hkZero : heightIncrement H k = 0
    · rw [hdist_zero k hkZero, hkZero, mul_zero]
    · have hkPos : 0 < heightIncrement H k := lt_of_le_of_ne (hinc k) (Ne.symm hkZero)
      have hratioPrefix : ratio k ≤ Cprefix :=
        Finset.single_le_sum (fun j _ ↦ hratio j) hkMem
      have hratioGlobal : ratio k ≤ Ctail + Cprefix :=
        hratioPrefix.trans (le_add_of_nonneg_left hCtail.le)
      calc
        (P (k + 2)).coeffDist (P k) = ratio k * heightIncrement H k := by
          dsimp only [ratio]
          field_simp [ne_of_gt hkPos]
        _ ≤ (Ctail + Cprefix) * heightIncrement H k :=
          mul_le_mul_of_nonneg_right hratioGlobal hkPos.le

/-- Shift past the coercivity threshold.  The resulting sequences satisfy
the global `HasFactorVariation` interface consumed by
`FactorConvergence`. -/
theorem exists_shifted_arnoldiOrbit2_hasFactorVariation
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v₀ : E)
    (hv₀ : ‖v₀‖ = 1) (hgrade₀ : 3 ≤ grade A v₀) :
    ∃ K : ℕ, ∃ C : ℝ, 0 < C ∧
      HasFactorVariation
        (fun n ↦ arnoldiFactorOrbit2 A v₀ (n + K))
        (fun n ↦ arnoldiHeightOrbit2 A v₀ (n + K)) C := by
  obtain ⟨K, C, hC, hvariation⟩ :=
    exists_arnoldiOrbit2_factor_variation_tail A hA v₀ hv₀ hgrade₀
  refine ⟨K, C, hC, ?_⟩
  intro n
  have hv := hvariation (n + K) (Nat.le_add_left K n)
  simpa only [heightIncrement, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
    using hv

end Arnoldi

end
end Forsythe
