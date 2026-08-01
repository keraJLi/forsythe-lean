import Forsythe.Arnoldi.Defs
import Mathlib.Analysis.InnerProductSpace.Symmetric

/-!
# Algebraic identities for restart-two Arnoldi steps

This file isolates the identities in the first part of the proof from all
compactness and spectral arguments.  The hypotheses in `IsQuadraticStep` are
exactly the normalization, norm, and degree-at-most-one orthogonality data used
by the calculations.
-/

set_option autoImplicit false

namespace Forsythe

open Polynomial

section PolynomialAction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

@[simp]
theorem polyApply_zero (A : Module.End ℝ E) (v : E) :
    polyApply A 0 v = 0 := by
  simp [polyApply]

@[simp]
theorem polyApply_C (A : Module.End ℝ E) (c : ℝ) (v : E) :
    polyApply A (C c) v = c • v := by
  simp [polyApply]

@[simp]
theorem polyApply_add (A : Module.End ℝ E) (p q : ℝ[X]) (v : E) :
    polyApply A (p + q) v = polyApply A p v + polyApply A q v := by
  simp [polyApply]

@[simp]
theorem polyApply_sub (A : Module.End ℝ E) (p q : ℝ[X]) (v : E) :
    polyApply A (p - q) v = polyApply A p v - polyApply A q v := by
  simp [polyApply]

@[simp]
theorem polyInner_add_left (A : Module.End ℝ E) (v : E) (p q r : ℝ[X]) :
    polyInner A v (p + q) r = polyInner A v p r + polyInner A v q r := by
  simp [polyInner, inner_add_left]

@[simp]
theorem polyInner_add_right (A : Module.End ℝ E) (v : E) (p q r : ℝ[X]) :
    polyInner A v p (q + r) = polyInner A v p q + polyInner A v p r := by
  simp [polyInner, inner_add_right]

@[simp]
theorem polyInner_sub_left (A : Module.End ℝ E) (v : E) (p q r : ℝ[X]) :
    polyInner A v (p - q) r = polyInner A v p r - polyInner A v q r := by
  simp [polyInner, inner_sub_left]

@[simp]
theorem polyInner_sub_right (A : Module.End ℝ E) (v : E) (p q r : ℝ[X]) :
    polyInner A v p (q - r) = polyInner A v p q - polyInner A v p r := by
  simp [polyInner, inner_sub_right]

@[simp]
theorem polyInner_C_left (A : Module.End ℝ E) (v : E) (c : ℝ) (p : ℝ[X]) :
    polyInner A v (C c) p = c * polyInner A v 1 p := by
  simp [polyInner, real_inner_smul_left]

@[simp]
theorem polyInner_C_right (A : Module.End ℝ E) (v : E) (c : ℝ) (p : ℝ[X]) :
    polyInner A v p (C c) = c * polyInner A v p 1 := by
  simp [polyInner, real_inner_smul_right]

@[simp]
theorem polyInner_C_mul_right (A : Module.End ℝ E) (v : E) (c : ℝ)
    (p q : ℝ[X]) :
    polyInner A v p (C c * q) = c * polyInner A v p q := by
  simp [polyInner, polyApply_mul, real_inner_smul_right]

theorem polyInner_symm (A : Module.End ℝ E) (v : E) (p q : ℝ[X]) :
    polyInner A v p q = polyInner A v q p := by
  exact real_inner_comm _ _

/-- A real polynomial in a symmetric endomorphism is again symmetric. -/
theorem polynomial_aeval_isSymmetric (A : Module.End ℝ E) (hA : A.IsSymmetric)
    (p : ℝ[X]) : (Polynomial.aeval A p : Module.End ℝ E).IsSymmetric := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simpa only [map_add] using hp.add hq
  | monomial n c =>
      rw [Polynomial.aeval_monomial, ← Algebra.smul_def]
      exact (hA.pow n).smul (by simp)

/-- Move a polynomial factor through the real inner product. -/
theorem polyInner_mul_left (A : Module.End ℝ E) (hA : A.IsSymmetric) (v : E)
    (p q r : ℝ[X]) :
    polyInner A v (p * q) r = polyInner A v q (p * r) := by
  simp only [polyInner, polyApply_mul]
  exact polynomial_aeval_isSymmetric A hA p _ _

/-- Every polynomial inner product is the moment of the product. -/
theorem polyInner_eq_one_product (A : Module.End ℝ E) (hA : A.IsSymmetric) (v : E)
    (p q : ℝ[X]) :
    polyInner A v p q = polyInner A v 1 (p * q) := by
  simp only [polyInner, polyApply_one, polyApply_mul]
  exact polynomial_aeval_isSymmetric A hA p _ _

/-- Polynomial products with the same total product have the same polynomial
inner product. -/
theorem polyInner_eq_of_mul_eq (A : Module.End ℝ E) (hA : A.IsSymmetric) (v : E)
    {p q r s : ℝ[X]} (h : p * q = r * s) :
    polyInner A v p q = polyInner A v r s := by
  calc
    polyInner A v p q = polyInner A v 1 (p * q) :=
      polyInner_eq_one_product A hA v p q
    _ = polyInner A v 1 (r * s) := by rw [h]
    _ = polyInner A v r s := (polyInner_eq_one_product A hA v r s).symm

/-- Scaling the base vector scales the polynomial form quadratically. -/
theorem polyInner_smul_base (A : Module.End ℝ E) (v : E) (c : ℝ)
    (p q : ℝ[X]) :
    polyInner A (c • v) p q = c ^ 2 * polyInner A v p q := by
  simp only [polyInner, polyApply_smul, real_inner_smul_left, real_inner_smul_right]
  ring

/-- Transport of the polynomial form across an arbitrary scaled polynomial
update. -/
theorem polyInner_transport_scale (A : Module.End ℝ E) (v w : E) (c : ℝ)
    (P f g : ℝ[X]) (hw : w = c • polyApply A P v) :
    polyInner A w f g = c ^ 2 * polyInner A v (f * P) (g * P) := by
  subst w
  rw [polyInner_smul_base]
  simp only [polyInner, polyApply_mul]

/-- The one-step transport identity in normalization-by-`sigma` form. -/
theorem polyInner_transport (A : Module.End ℝ E) (v w : E) (sigma : ℝ)
    (P f g : ℝ[X]) (hsigma : sigma ≠ 0)
    (hw : w = sigma⁻¹ • polyApply A P v) :
    polyInner A w f g = polyInner A v (f * P) (g * P) / sigma ^ 2 := by
  rw [polyInner_transport_scale A v w sigma⁻¹ P f g hw]
  field_simp

end PolynomialAction

section ConditionalSteps

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A polynomial of degree at most one, represented by its linear and
constant coefficients. -/
noncomputable def linearPolynomial (a b : ℝ) : ℝ[X] :=
  C a * X + C b

/-- The difference of two monic quadratics is linear. -/
theorem monicQuadratic_sub (p q : MonicQuadratic) :
    p.toPolynomial - q.toPolynomial =
      linearPolynomial (p.linearCoeff - q.linearCoeff)
        (p.constantCoeff - q.constantCoeff) := by
  simp [MonicQuadratic.toPolynomial, linearPolynomial]
  ring

/-- The algebraic data used from one normalized Arnoldi step.  No existence,
grade, or compactness assertion is bundled into this predicate. -/
structure IsQuadraticStep (A : Module.End ℝ E) (v w : E)
    (p : MonicQuadratic) (sigma : ℝ) : Prop where
  sigma_pos : 0 < sigma
  update : w = sigma⁻¹ • polyApply A p.toPolynomial v
  source_unit : polyInner A v 1 1 = 1
  norm_sq : polyInner A v p.toPolynomial p.toPolynomial = sigma ^ 2
  orthogonal : ∀ a b : ℝ,
    polyInner A v p.toPolynomial (linearPolynomial a b) = 0

namespace IsQuadraticStep

theorem sigma_ne {A : Module.End ℝ E} {v w : E} {p : MonicQuadratic} {σ : ℝ}
    (h : IsQuadraticStep A v w p σ) : σ ≠ 0 :=
  ne_of_gt h.sigma_pos

theorem orthogonal_one {A : Module.End ℝ E} {v w : E} {p : MonicQuadratic} {σ : ℝ}
    (h : IsQuadraticStep A v w p σ) :
    polyInner A v p.toPolynomial 1 = 0 := by
  simpa [linearPolynomial] using h.orthogonal 0 1

theorem orthogonal_sub {A : Module.End ℝ E} {v w : E} {p q : MonicQuadratic}
    {σ : ℝ} (h : IsQuadraticStep A v w p σ) :
    polyInner A v p.toPolynomial (q.toPolynomial - p.toPolynomial) = 0 := by
  rw [monicQuadratic_sub]
  exact h.orthogonal _ _

end IsQuadraticStep

/-- One-step transport specialized to conditional Arnoldi-step data. -/
theorem quadraticStep_transport (A : Module.End ℝ E) {v₀ v₁ : E}
    {p₀ : MonicQuadratic} {σ₀ : ℝ} (h₀ : IsQuadraticStep A v₀ v₁ p₀ σ₀)
    (f g : ℝ[X]) :
    polyInner A v₁ f g =
      polyInner A v₀ (f * p₀.toPolynomial) (g * p₀.toPolynomial) / σ₀ ^ 2 :=
  polyInner_transport A v₀ v₁ σ₀ p₀.toPolynomial f g h₀.sigma_ne h₀.update

/-- Two consecutive normalized steps give the manuscript's two-step
transport identity. -/
theorem quadraticStep_transport_two (A : Module.End ℝ E) {v₀ v₁ v₂ : E}
    {p₀ p₁ : MonicQuadratic} {σ₀ σ₁ : ℝ}
    (h₀ : IsQuadraticStep A v₀ v₁ p₀ σ₀)
    (h₁ : IsQuadraticStep A v₁ v₂ p₁ σ₁) (f g : ℝ[X]) :
    polyInner A v₂ f g =
      polyInner A v₀ (f * (p₀.toPolynomial * p₁.toPolynomial))
        (g * (p₀.toPolynomial * p₁.toPolynomial)) / (σ₀ ^ 2 * σ₁ ^ 2) := by
  rw [quadraticStep_transport A h₁, quadraticStep_transport A h₀]
  simp only [div_div]
  congr 2 <;> ring

/-- The first moment identity for a two-step product. -/
theorem twoStepProduct_inner_one (A : Module.End ℝ E) (hA : A.IsSymmetric)
    {v₀ v₁ : E} {p₀ p₁ : MonicQuadratic} {σ₀ : ℝ}
    (h₀ : IsQuadraticStep A v₀ v₁ p₀ σ₀) :
    polyInner A v₀ (p₀.toPolynomial * p₁.toPolynomial) 1 = σ₀ ^ 2 := by
  calc
    polyInner A v₀ (p₀.toPolynomial * p₁.toPolynomial) 1 =
        polyInner A v₀ p₀.toPolynomial p₁.toPolynomial := by
          calc
            _ = polyInner A v₀ 1 (p₀.toPolynomial * p₁.toPolynomial) :=
              polyInner_symm _ _ _ _
            _ = _ := (polyInner_eq_one_product A hA _ _ _).symm
    _ = polyInner A v₀ p₀.toPolynomial p₀.toPolynomial +
          polyInner A v₀ p₀.toPolynomial
            (p₁.toPolynomial - p₀.toPolynomial) := by
          rw [← polyInner_add_right,
            show p₀.toPolynomial + (p₁.toPolynomial - p₀.toPolynomial) =
              p₁.toPolynomial by abel]
    _ = σ₀ ^ 2 := by rw [h₀.norm_sq, h₀.orthogonal_sub, add_zero]

/-- The squared norm identity for a two-step product. -/
theorem twoStepProduct_inner_self (A : Module.End ℝ E)
    {v₀ v₁ v₂ : E} {p₀ p₁ : MonicQuadratic} {σ₀ σ₁ : ℝ}
    (h₀ : IsQuadraticStep A v₀ v₁ p₀ σ₀)
    (h₁ : IsQuadraticStep A v₁ v₂ p₁ σ₁) :
    polyInner A v₀ (p₀.toPolynomial * p₁.toPolynomial)
      (p₀.toPolynomial * p₁.toPolynomial) = σ₀ ^ 2 * σ₁ ^ 2 := by
  have ht := quadraticStep_transport A h₀ p₁.toPolynomial p₁.toPolynomial
  rw [h₁.norm_sq] at ht
  have ht' : σ₁ ^ 2 * σ₀ ^ 2 =
      polyInner A v₀ (p₁.toPolynomial * p₀.toPolynomial)
        (p₁.toPolynomial * p₀.toPolynomial) :=
    (eq_div_iff (pow_ne_zero 2 h₀.sigma_ne)).mp ht
  simpa [mul_comm] using ht'.symm

/-- Conditional form of the exact Lyapunov/energy identity. -/
theorem quadraticStep_energy (A : Module.End ℝ E) (hA : A.IsSymmetric)
    {v₀ v₁ v₂ : E} {p₀ p₁ : MonicQuadratic} {σ₀ σ₁ : ℝ}
    (h₀ : IsQuadraticStep A v₀ v₁ p₀ σ₀)
    (h₁ : IsQuadraticStep A v₁ v₂ p₁ σ₁) :
    let Q := p₀.toPolynomial * p₁.toPolynomial
    let R := Q - C (σ₀ ^ 2)
    polyInner A v₀ R R = σ₀ ^ 2 * (σ₁ ^ 2 - σ₀ ^ 2) := by
  dsimp only
  have hQ1 := twoStepProduct_inner_one A hA h₀ (p₁ := p₁)
  have hQQ := twoStepProduct_inner_self A h₀ h₁
  have h1Q := (polyInner_symm A v₀ 1
    (p₀.toPolynomial * p₁.toPolynomial)).trans hQ1
  simp only [polyInner_sub_left, polyInner_sub_right, polyInner_C_left,
    polyInner_C_right, hQ1, h1Q, hQQ, h₀.source_unit]
  ring

/-- Conditional form of the correlation identity
`<v_k,v_{k+2}> = sigma_k / sigma_{k+1}`. -/
theorem quadraticStep_correlation (A : Module.End ℝ E) (hA : A.IsSymmetric)
    {v₀ v₁ v₂ : E} {p₀ p₁ : MonicQuadratic} {σ₀ σ₁ : ℝ}
    (h₀ : IsQuadraticStep A v₀ v₁ p₀ σ₀)
    (h₁ : IsQuadraticStep A v₁ v₂ p₁ σ₁) :
    inner ℝ v₀ v₂ = σ₀ / σ₁ := by
  have hQ1 := twoStepProduct_inner_one A hA h₀ (p₁ := p₁)
  rw [h₁.update, h₀.update, polyApply_smul, real_inner_smul_right,
    real_inner_smul_right, ← polyApply_mul]
  rw [show inner ℝ v₀
      (polyApply A (p₁.toPolynomial * p₀.toPolynomial) v₀) = σ₀ ^ 2 by
    simpa [polyInner, mul_comm] using
      (polyInner_symm A v₀ 1
        (p₀.toPolynomial * p₁.toPolynomial)).trans hQ1]
  field_simp [h₀.sigma_ne, h₁.sigma_ne]

/-- Conditional form of the cancellation
`<P_k ell, Q_k - sigma_k²>_k = 0`. -/
theorem quadraticStep_cancellation (A : Module.End ℝ E) (hA : A.IsSymmetric)
    {v₀ v₁ v₂ : E} {p₀ p₁ : MonicQuadratic} {σ₀ σ₁ : ℝ}
    (h₀ : IsQuadraticStep A v₀ v₁ p₀ σ₀)
    (h₁ : IsQuadraticStep A v₁ v₂ p₁ σ₁) (a b : ℝ) :
    let ell := linearPolynomial a b
    let Q := p₀.toPolynomial * p₁.toPolynomial
    let R := Q - C (σ₀ ^ 2)
    polyInner A v₀ (p₀.toPolynomial * ell) R = 0 := by
  dsimp only
  have ht := quadraticStep_transport A h₀ (linearPolynomial a b) p₁.toPolynomial
  have hleft : polyInner A v₁ (linearPolynomial a b) p₁.toPolynomial = 0 := by
    rw [polyInner_symm]
    exact h₁.orthogonal a b
  rw [hleft] at ht
  have hproduct :
      polyInner A v₀ (p₀.toPolynomial * linearPolynomial a b)
          (p₀.toPolynomial * p₁.toPolynomial) = 0 := by
    have hnum : polyInner A v₀
        (linearPolynomial a b * p₀.toPolynomial)
        (p₁.toPolynomial * p₀.toPolynomial) = 0 := by
      have hz : polyInner A v₀
          (linearPolynomial a b * p₀.toPolynomial)
          (p₁.toPolynomial * p₀.toPolynomial) / σ₀ ^ 2 = 0 := ht.symm
      exact (div_eq_zero_iff.mp hz).resolve_right (pow_ne_zero 2 h₀.sigma_ne)
    simpa [mul_comm] using hnum
  have hconstant :
      polyInner A v₀ (p₀.toPolynomial * linearPolynomial a b)
        (C (σ₀ ^ 2)) = 0 := by
    rw [polyInner_C_right]
    have horth := h₀.orthogonal a b
    have hmove : polyInner A v₀
        (p₀.toPolynomial * linearPolynomial a b) 1 =
        polyInner A v₀ p₀.toPolynomial (linearPolynomial a b) := by
      apply polyInner_eq_of_mul_eq A hA
      ring
    rw [hmove, horth, mul_zero]
  rw [polyInner_sub_right, hproduct, hconstant, sub_zero]

/-- Conditional form of the manuscript's three-step identity. -/
theorem quadraticStep_three_step (A : Module.End ℝ E) (hA : A.IsSymmetric)
    {v₀ v₁ v₂ v₃ : E} {p₀ p₁ p₂ : MonicQuadratic}
    {σ₀ σ₁ σ₂ : ℝ}
    (h₀ : IsQuadraticStep A v₀ v₁ p₀ σ₀)
    (h₁ : IsQuadraticStep A v₁ v₂ p₁ σ₁)
    (h₂ : IsQuadraticStep A v₂ v₃ p₂ σ₂) (a b : ℝ) :
    let ell := linearPolynomial a b
    let D := p₂.toPolynomial - p₀.toPolynomial
    let Q := p₀.toPolynomial * p₁.toPolynomial
    let R := Q - C (σ₀ ^ 2)
    polyInner A v₂ D ell =
      -polyInner A v₀ (p₀.toPolynomial * ell) (R * R) /
        (σ₀ ^ 2 * σ₁ ^ 2) := by
  dsimp only
  have hD : polyInner A v₂
      (p₂.toPolynomial - p₀.toPolynomial) (linearPolynomial a b) =
      -polyInner A v₂ p₀.toPolynomial (linearPolynomial a b) := by
    rw [polyInner_sub_left, h₂.orthogonal a b, zero_sub]
  rw [hD, quadraticStep_transport_two A h₀ h₁]
  have hbalance :
      polyInner A v₀
          (p₀.toPolynomial * (p₀.toPolynomial * p₁.toPolynomial))
          (linearPolynomial a b * (p₀.toPolynomial * p₁.toPolynomial)) =
      polyInner A v₀ (p₀.toPolynomial * linearPolynomial a b)
        ((p₀.toPolynomial * p₁.toPolynomial) *
          (p₀.toPolynomial * p₁.toPolynomial)) := by
    apply polyInner_eq_of_mul_eq A hA
    ring
  rw [hbalance]
  have hc := quadraticStep_cancellation A hA h₀ h₁ a b
  dsimp only at hc
  have hzero : polyInner A v₀
      (p₀.toPolynomial * linearPolynomial a b) 1 = 0 := by
    have horth := h₀.orthogonal a b
    calc
      polyInner A v₀ (p₀.toPolynomial * linearPolynomial a b) 1 =
          polyInner A v₀ p₀.toPolynomial (linearPolynomial a b) := by
            apply polyInner_eq_of_mul_eq A hA
            ring
      _ = 0 := horth
  have hsquare :
      polyInner A v₀ (p₀.toPolynomial * linearPolynomial a b)
          ((p₀.toPolynomial * p₁.toPolynomial) *
            (p₀.toPolynomial * p₁.toPolynomial)) =
      polyInner A v₀ (p₀.toPolynomial * linearPolynomial a b)
        ((p₀.toPolynomial * p₁.toPolynomial - C (σ₀ ^ 2)) *
          (p₀.toPolynomial * p₁.toPolynomial - C (σ₀ ^ 2))) := by
    let L := p₀.toPolynomial * linearPolynomial a b
    let Q := p₀.toPolynomial * p₁.toPolynomial
    let R := Q - C (σ₀ ^ 2)
    have hpoly : Q * Q =
        ((R * R + C (σ₀ ^ 2) * R) + R * C (σ₀ ^ 2)) +
          C (σ₀ ^ 2) * C (σ₀ ^ 2) := by
      dsimp [R]
      ring
    change polyInner A v₀ L (Q * Q) = polyInner A v₀ L (R * R)
    rw [hpoly, polyInner_add_right, polyInner_add_right, polyInner_add_right]
    have hlinearLeft : polyInner A v₀ L (C (σ₀ ^ 2) * R) = 0 := by
      rw [polyInner_C_mul_right, hc, mul_zero]
    have hlinearRight : polyInner A v₀ L (R * C (σ₀ ^ 2)) = 0 := by
      rw [mul_comm, polyInner_C_mul_right, hc, mul_zero]
    have hconst :
        polyInner A v₀ L (C (σ₀ ^ 2) * C (σ₀ ^ 2)) = 0 := by
      rw [polyInner_C_mul_right, polyInner_C_right, hzero, mul_zero, mul_zero]
    rw [hlinearLeft, hlinearRight, hconst, add_zero, add_zero, add_zero]
  rw [hsquare]
  ring

end ConditionalSteps

end Forsythe
