import Forsythe.Arnoldi.Algebra
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# The moment Gram system for restart-two Arnoldi

This file proves that the intrinsic grade hypothesis makes the moment Gram matrix
of `1, X` strictly positive.  It then verifies directly that the explicit
quadratic in `arnoldiPoly2` is the unique monic quadratic orthogonal to both
`1` and `X`.
-/

set_option autoImplicit false

namespace Forsythe

open Polynomial

noncomputable section

section Grade

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- If `v` is an eigenvector in the weak sense `A v = c • v`, its cyclic
subspace has dimension at most one. -/
theorem grade_le_one_of_apply_eq_smul (A : Module.End ℝ E) (v : E) (c : ℝ)
    (hAv : A v = c • v) : grade A v ≤ 1 := by
  have hpow : ∀ k : ℕ, (A ^ k) v = c ^ k • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [pow_succ', Module.End.mul_apply, ih, map_smul, hAv]
        simp only [pow_succ, smul_smul]
  have hle : cyclicSubspace A v ≤ ℝ ∙ v := by
    rw [cyclicSubspace]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨k, rfl⟩
    change (A ^ k) v ∈ ℝ ∙ v
    rw [hpow k]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
  calc
    grade A v = Module.finrank ℝ (cyclicSubspace A v) := rfl
    _ ≤ Module.finrank ℝ (ℝ ∙ v) := Submodule.finrank_mono hle
    _ ≤ 1 := by
      by_cases hv : v = 0
      · subst v
        rw [Submodule.span_zero_singleton, finrank_bot]
        omega
      · rw [finrank_span_singleton hv]

/-- Grade at least three forces the first two Krylov vectors to be linearly
independent. -/
theorem linearIndependent_v_apply_of_grade_three (A : Module.End ℝ E) (v : E)
    (hgrade : 3 ≤ grade A v) :
    LinearIndependent ℝ ![v, A v] := by
  by_contra hli
  by_cases hv : v = 0
  · have hle := grade_le_one_of_apply_eq_smul A v 0 (by simp [hv])
    omega
  · rw [LinearIndependent.pair_iff' hv] at hli
    push Not at hli
    obtain ⟨c, hc⟩ := hli
    have hle := grade_le_one_of_apply_eq_smul A v c hc.symm
    omega

end Grade

section Moments

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem moment_zero (A : Module.End ℝ E) (v : E) :
    moment A v 0 = inner ℝ v v := by
  simp [moment]

theorem moment_one (A : Module.End ℝ E) (v : E) :
    moment A v 1 = inner ℝ (A v) v := by
  simp [moment]

theorem moment_two (A : Module.End ℝ E) (hA : A.IsSymmetric) (v : E) :
    moment A v 2 = inner ℝ (A v) (A v) := by
  simpa [moment, pow_two, Module.End.mul_apply] using hA (A v) v

theorem moment_three_shift (A : Module.End ℝ E) (hA : A.IsSymmetric) (v : E) :
    inner ℝ ((A ^ 2) v) (A v) = moment A v 3 := by
  rw [show moment A v 3 = inner ℝ (A ((A ^ 2) v)) v by
    simp [moment, pow_succ', Module.End.mul_apply]]
  exact (hA ((A ^ 2) v) v).symm

end Moments

section Gram

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The determinant in `momentGramDet` is the determinant of the ordinary
Gram matrix of `v, A v`. -/
theorem momentGramDet_eq_det_gram (A : Module.End ℝ E) (hA : A.IsSymmetric)
    (v : E) :
    momentGramDet A v = (Matrix.gram ℝ ![v, A v]).det := by
  rw [Matrix.det_fin_two]
  simp [Matrix.gram, momentGramDet, moment_zero, moment_one,
    moment_two A hA, real_inner_comm]
  ring

/-- Positivity of the `2 × 2` moment determinant on every grade-at-least-three
state. -/
theorem momentGramDet_pos_of_grade_three (A : Module.End ℝ E)
    (hA : A.IsSymmetric) (v : E)
    (hgrade : 3 ≤ grade A v) :
    0 < momentGramDet A v := by
  rw [momentGramDet_eq_det_gram A hA v]
  exact (Matrix.posDef_gram_of_linearIndependent
    (linearIndependent_v_apply_of_grade_three A v hgrade)).det_pos

theorem momentGramDet_ne_zero_of_grade_three (A : Module.End ℝ E)
    (hA : A.IsSymmetric) (v : E)
    (hgrade : 3 ≤ grade A v) :
    momentGramDet A v ≠ 0 :=
  ne_of_gt (momentGramDet_pos_of_grade_three A hA v hgrade)

end Gram

section QuadraticMoments

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

@[simp]
theorem polyApply_X (A : Module.End ℝ E) (v : E) :
    polyApply A X v = A v := by
  simp [polyApply]

theorem polyApply_monicQuadratic (A : Module.End ℝ E) (v : E)
    (p : MonicQuadratic) :
    polyApply A p.toPolynomial v =
      (A ^ 2) v + p.linearCoeff • A v + p.constantCoeff • v := by
  simp [MonicQuadratic.toPolynomial, pow_two, Module.End.mul_apply]

/-- The first row of the moment Gram system, before substituting the explicit
coefficients. -/
theorem polyInner_monicQuadratic_one (A : Module.End ℝ E) (v : E)
    (p : MonicQuadratic) :
    polyInner A v p.toPolynomial 1 =
      moment A v 2 + p.linearCoeff * moment A v 1 +
        p.constantCoeff * moment A v 0 := by
  rw [polyInner, polyApply_monicQuadratic, polyApply_one]
  simp only [inner_add_left, real_inner_smul_left]
  simp [moment, pow_two, Module.End.mul_apply]

/-- The second row of the moment Gram system, before substituting the explicit
coefficients. -/
theorem polyInner_monicQuadratic_X (A : Module.End ℝ E) (hA : A.IsSymmetric)
    (v : E) (p : MonicQuadratic) :
    polyInner A v p.toPolynomial X =
      moment A v 3 + p.linearCoeff * moment A v 2 +
        p.constantCoeff * moment A v 1 := by
  rw [polyInner, polyApply_monicQuadratic, polyApply_X]
  simp only [inner_add_left, real_inner_smul_left]
  rw [moment_three_shift A hA]
  rw [← moment_two A hA]
  rw [moment_one]
  exact congrArg₂ (fun x y : ℝ => moment A v 3 + p.linearCoeff * x +
    p.constantCoeff * y) rfl (real_inner_comm _ _)

end QuadraticMoments

section ArnoldiOrthogonality

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem polyApply_linearPolynomial (A : Module.End ℝ E) (v : E) (a b : ℝ) :
    polyApply A (linearPolynomial a b) v = a • A v + b • v := by
  simp [linearPolynomial]

/-- Cramer's rule verifies the constant-polynomial orthogonality equation for
the explicit Arnoldi quadratic whenever the moment determinant is nonzero. -/
theorem arnoldiPoly2_orthogonal_one_of_det_ne (A : Module.End ℝ E) (v : E)
    (hdet : momentGramDet A v ≠ 0) :
    polyInner A v (arnoldiPoly2 A v).toPolynomial 1 = 0 := by
  rw [polyInner_monicQuadratic_one]
  simp only [arnoldiPoly2]
  field_simp [hdet]
  simp only [momentGramDet]
  ring

/-- Cramer's rule verifies the `X`-orthogonality equation for the explicit
Arnoldi quadratic whenever the moment determinant is nonzero. -/
theorem arnoldiPoly2_orthogonal_X_of_det_ne (A : Module.End ℝ E)
    (hA : A.IsSymmetric) (v : E) (hdet : momentGramDet A v ≠ 0) :
    polyInner A v (arnoldiPoly2 A v).toPolynomial X = 0 := by
  rw [polyInner_monicQuadratic_X A hA]
  simp only [arnoldiPoly2]
  field_simp [hdet]
  simp only [momentGramDet]
  ring

/-- Orthogonality to both basis polynomials implies orthogonality to every
polynomial of degree at most one in the concrete coefficient representation
used by the algebraic core. -/
theorem arnoldiPoly2_orthogonal_linear_of_det_ne (A : Module.End ℝ E)
    (hA : A.IsSymmetric) (v : E) (hdet : momentGramDet A v ≠ 0)
    (a b : ℝ) :
    polyInner A v (arnoldiPoly2 A v).toPolynomial (linearPolynomial a b) = 0 := by
  rw [linearPolynomial, polyInner_add_right, polyInner_C_mul_right,
    polyInner_C_right, arnoldiPoly2_orthogonal_X_of_det_ne A hA v hdet,
    arnoldiPoly2_orthogonal_one_of_det_ne A v hdet]
  ring

/-- The two Arnoldi orthogonality equations follow directly from grade at
least three. -/
theorem arnoldiPoly2_orthogonal_one (A : Module.End ℝ E) (hA : A.IsSymmetric)
    (v : E) (hgrade : 3 ≤ grade A v) :
    polyInner A v (arnoldiPoly2 A v).toPolynomial 1 = 0 :=
  arnoldiPoly2_orthogonal_one_of_det_ne A v
    (momentGramDet_ne_zero_of_grade_three A hA v hgrade)

theorem arnoldiPoly2_orthogonal_X (A : Module.End ℝ E) (hA : A.IsSymmetric)
    (v : E) (hgrade : 3 ≤ grade A v) :
    polyInner A v (arnoldiPoly2 A v).toPolynomial X = 0 :=
  arnoldiPoly2_orthogonal_X_of_det_ne A hA v
    (momentGramDet_ne_zero_of_grade_three A hA v hgrade)

theorem arnoldiPoly2_orthogonal_linear (A : Module.End ℝ E)
    (hA : A.IsSymmetric) (v : E)
    (hgrade : 3 ≤ grade A v) (a b : ℝ) :
    polyInner A v (arnoldiPoly2 A v).toPolynomial (linearPolynomial a b) = 0 :=
  arnoldiPoly2_orthogonal_linear_of_det_ne A hA v
    (momentGramDet_ne_zero_of_grade_three A hA v hgrade) a b

/-- A monic quadratic satisfying the two moment equations is necessarily the
explicit Cramer-system solution `arnoldiPoly2`. -/
theorem monicQuadratic_eq_arnoldiPoly2_of_orthogonal (A : Module.End ℝ E)
    (hA : A.IsSymmetric) (v : E) (q : MonicQuadratic)
    (hdet : momentGramDet A v ≠ 0)
    (hq1 : polyInner A v q.toPolynomial 1 = 0)
    (hqX : polyInner A v q.toPolynomial X = 0) :
    q = arnoldiPoly2 A v := by
  have hq1' :
      moment A v 2 + q.linearCoeff * moment A v 1 +
        q.constantCoeff * moment A v 0 = 0 := by
    rw [← polyInner_monicQuadratic_one A v q]
    exact hq1
  have hqX' :
      moment A v 3 + q.linearCoeff * moment A v 2 +
        q.constantCoeff * moment A v 1 = 0 := by
    rw [← polyInner_monicQuadratic_X A hA v q]
    exact hqX
  have hlinear :
      q.linearCoeff * momentGramDet A v =
        moment A v 1 * moment A v 2 - moment A v 0 * moment A v 3 := by
    simp only [momentGramDet]
    linear_combination
      (moment A v 0) * hqX' - (moment A v 1) * hq1'
  have hconstant :
      q.constantCoeff * momentGramDet A v =
        moment A v 1 * moment A v 3 - moment A v 2 ^ 2 := by
    simp only [momentGramDet]
    linear_combination
      (moment A v 2) * hq1' - (moment A v 1) * hqX'
  apply MonicQuadratic.ext
  · simp only [arnoldiPoly2]
    apply (eq_div_iff hdet).2
    exact hlinear
  · simp only [arnoldiPoly2]
    apply (eq_div_iff hdet).2
    exact hconstant

/-- Grade-specialized uniqueness of the restart-two Arnoldi factor. -/
theorem monicQuadratic_eq_arnoldiPoly2 (A : Module.End ℝ E)
    (hA : A.IsSymmetric) (v : E)
    (hgrade : 3 ≤ grade A v) (q : MonicQuadratic)
    (hq1 : polyInner A v q.toPolynomial 1 = 0)
    (hqX : polyInner A v q.toPolynomial X = 0) :
    q = arnoldiPoly2 A v :=
  monicQuadratic_eq_arnoldiPoly2_of_orthogonal A hA v q
    (momentGramDet_ne_zero_of_grade_three A hA v hgrade) hq1 hqX

/-- Pythagorean identity for any competing monic quadratic.  This is the
least-squares characterization without introducing a separate projection
operator. -/
theorem arnoldiPoly2_pythagorean_of_det_ne (A : Module.End ℝ E)
    (hA : A.IsSymmetric) (v : E) (hdet : momentGramDet A v ≠ 0)
    (q : MonicQuadratic) :
    polyInner A v q.toPolynomial q.toPolynomial =
      polyInner A v (arnoldiPoly2 A v).toPolynomial
          (arnoldiPoly2 A v).toPolynomial +
        polyInner A v
          (q.toPolynomial - (arnoldiPoly2 A v).toPolynomial)
          (q.toPolynomial - (arnoldiPoly2 A v).toPolynomial) := by
  let p := arnoldiPoly2 A v
  have horth :
      polyInner A v p.toPolynomial (q.toPolynomial - p.toPolynomial) = 0 := by
    rw [monicQuadratic_sub]
    exact arnoldiPoly2_orthogonal_linear_of_det_ne A hA v hdet _ _
  have horth' :
      polyInner A v (q.toPolynomial - p.toPolynomial) p.toPolynomial = 0 := by
    rw [polyInner_symm]
    exact horth
  have hdecomp :
      q.toPolynomial = p.toPolynomial + (q.toPolynomial - p.toPolynomial) := by
    abel
  change polyInner A v q.toPolynomial q.toPolynomial =
    polyInner A v p.toPolynomial p.toPolynomial +
      polyInner A v (q.toPolynomial - p.toPolynomial)
        (q.toPolynomial - p.toPolynomial)
  rw [hdecomp, polyInner_add_left, polyInner_add_right, polyInner_add_right,
    horth, horth']
  abel

/-- The explicit Arnoldi quadratic minimizes the squared polynomial-action
norm over all monic quadratics. -/
theorem arnoldiPoly2_minimizes_of_det_ne (A : Module.End ℝ E)
    (hA : A.IsSymmetric) (v : E) (hdet : momentGramDet A v ≠ 0)
    (q : MonicQuadratic) :
    polyInner A v (arnoldiPoly2 A v).toPolynomial
        (arnoldiPoly2 A v).toPolynomial ≤
      polyInner A v q.toPolynomial q.toPolynomial := by
  rw [arnoldiPoly2_pythagorean_of_det_ne A hA v hdet q]
  exact le_add_of_nonneg_right (real_inner_self_nonneg :
    0 ≤ inner ℝ
      (polyApply A (q.toPolynomial - (arnoldiPoly2 A v).toPolynomial) v)
      (polyApply A (q.toPolynomial - (arnoldiPoly2 A v).toPolynomial) v))

/-- Grade-specialized minimizing property. -/
theorem arnoldiPoly2_minimizes (A : Module.End ℝ E) (hA : A.IsSymmetric)
    (v : E) (hgrade : 3 ≤ grade A v)
    (q : MonicQuadratic) :
    polyInner A v (arnoldiPoly2 A v).toPolynomial
        (arnoldiPoly2 A v).toPolynomial ≤
      polyInner A v q.toPolynomial q.toPolynomial :=
  arnoldiPoly2_minimizes_of_det_ne A hA v
    (momentGramDet_ne_zero_of_grade_three A hA v hgrade) q

/-- Equality in the least-squares bound characterizes the Arnoldi quadratic.
The grade hypothesis is used only to make `v, A v` linearly independent. -/
theorem arnoldiPoly2_energy_eq_iff (A : Module.End ℝ E) (hA : A.IsSymmetric)
    (v : E) (hgrade : 3 ≤ grade A v)
    (q : MonicQuadratic) :
    polyInner A v q.toPolynomial q.toPolynomial =
        polyInner A v (arnoldiPoly2 A v).toPolynomial
          (arnoldiPoly2 A v).toPolynomial ↔
      q = arnoldiPoly2 A v := by
  let p := arnoldiPoly2 A v
  have hdet := momentGramDet_ne_zero_of_grade_three A hA v hgrade
  constructor
  · intro heq
    have hpyt := arnoldiPoly2_pythagorean_of_det_ne A hA v hdet q
    have hzero :
        polyInner A v (q.toPolynomial - p.toPolynomial)
          (q.toPolynomial - p.toPolynomial) = 0 := by
      change polyInner A v q.toPolynomial q.toPolynomial =
          polyInner A v p.toPolynomial p.toPolynomial +
            polyInner A v (q.toPolynomial - p.toPolynomial)
              (q.toPolynomial - p.toPolynomial) at hpyt
      change polyInner A v q.toPolynomial q.toPolynomial =
        polyInner A v p.toPolynomial p.toPolynomial at heq
      linarith
    have happly :
        polyApply A (q.toPolynomial - p.toPolynomial) v = 0 := by
      apply (inner_self_eq_zero (𝕜 := ℝ)).mp
      simpa only [polyInner] using hzero
    rw [monicQuadratic_sub, polyApply_linearPolynomial] at happly
    have hcoeff := (linearIndependent_v_apply_of_grade_three A v hgrade).eq_zero_of_pair
      (s := q.constantCoeff - p.constantCoeff)
      (t := q.linearCoeff - p.linearCoeff) (by simpa [add_comm] using happly)
    apply MonicQuadratic.ext <;> dsimp [p] at hcoeff ⊢
    · linarith [hcoeff.2]
    · linarith [hcoeff.1]
  · rintro rfl
    rfl

/-- No other monic quadratic can attain an objective value no larger than
the Arnoldi quadratic. -/
theorem eq_arnoldiPoly2_of_energy_le (A : Module.End ℝ E)
    (hA : A.IsSymmetric) (v : E)
    (hgrade : 3 ≤ grade A v) (q : MonicQuadratic)
    (hle : polyInner A v q.toPolynomial q.toPolynomial ≤
      polyInner A v (arnoldiPoly2 A v).toPolynomial
        (arnoldiPoly2 A v).toPolynomial) :
    q = arnoldiPoly2 A v := by
  apply (arnoldiPoly2_energy_eq_iff A hA v hgrade q).mp
  exact le_antisymm hle (arnoldiPoly2_minimizes A hA v hgrade q)

end ArnoldiOrthogonality

end

end Forsythe
