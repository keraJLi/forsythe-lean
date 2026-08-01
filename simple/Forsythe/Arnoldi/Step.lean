import Forsythe.Arnoldi.Algebra

/-!
# Normalization and conditional correctness of the restart-two step

This module connects the total definitions in `Arnoldi.Defs` to the exact
algebraic step interface used by the energy identities.  Nonvanishing and the
orthogonality equations are kept as explicit hypotheses here; the moment-Gram
module discharges them from the grade assumption.
-/

set_option autoImplicit false

namespace Forsythe

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The polynomial form evaluated at `(1,1)` is the squared vector norm. -/
theorem polyInner_one_one (A : Module.End ℝ E) (v : E) :
    polyInner A v 1 1 = ‖v‖ ^ 2 := by
  simp [polyInner]

/-- The squared norm of the raw update is its polynomial self-product. -/
theorem rawArnoldiStep2_norm_sq (A : Module.End ℝ E) (v : E) :
    polyInner A v (arnoldiPoly2 A v).toPolynomial
        (arnoldiPoly2 A v).toPolynomial =
      ‖rawArnoldiStep2 A v‖ ^ 2 := by
  simp [polyInner, rawArnoldiStep2]

/-- Normalization produces a unit vector whenever the raw update is nonzero. -/
theorem norm_arnoldiStep2 (A : Module.End ℝ E) (v : E)
    (hraw : rawArnoldiStep2 A v ≠ 0) :
    ‖arnoldiStep2 A v‖ = 1 := by
  rw [arnoldiStep2, norm_smul, norm_inv, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _)]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hraw)

/-- A normalized valid update is nonzero. -/
theorem arnoldiStep2_ne_zero (A : Module.End ℝ E) (v : E)
    (hraw : rawArnoldiStep2 A v ≠ 0) :
    arnoldiStep2 A v ≠ 0 := by
  intro hzero
  have hnorm := norm_arnoldiStep2 A v hraw
  rw [hzero, norm_zero] at hnorm
  norm_num at hnorm

/-- The total Arnoldi definition realizes the conditional quadratic-step
interface once its denominator is nonzero and its two moment equations hold. -/
theorem arnoldiStep2_isQuadraticStep (A : Module.End ℝ E) (v : E)
    (hv : ‖v‖ = 1)
    (hraw : rawArnoldiStep2 A v ≠ 0)
    (horth : ∀ a b : ℝ,
      polyInner A v (arnoldiPoly2 A v).toPolynomial
        (linearPolynomial a b) = 0) :
    IsQuadraticStep A v (arnoldiStep2 A v) (arnoldiPoly2 A v)
      ‖rawArnoldiStep2 A v‖ where
  sigma_pos := norm_pos_iff.mpr hraw
  update := rfl
  source_unit := by simp [polyInner_one_one, hv]
  norm_sq := rawArnoldiStep2_norm_sq A v
  orthogonal := horth

/-- Unit norm propagates along any orbit for which every raw update is
nonzero. -/
theorem norm_arnoldiOrbit2_of_raw_ne (A : Module.End ℝ E) (v₀ : E)
    (hv₀ : ‖v₀‖ = 1)
    (hraw : ∀ k : ℕ,
      rawArnoldiStep2 A (arnoldiOrbit2 A v₀ k) ≠ 0) :
    ∀ k : ℕ, ‖arnoldiOrbit2 A v₀ k‖ = 1 := by
  intro k
  induction k with
  | zero => simpa using hv₀
  | succ k ih =>
      rw [arnoldiOrbit2_succ]
      exact norm_arnoldiStep2 A _ (hraw k)

end
end Forsythe
