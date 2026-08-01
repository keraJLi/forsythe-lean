import Forsythe.FourNode.Interpolation
import Mathlib.Topology.Algebra.Polynomial

/-!
# Quantitative continuity of the four-node map

The four weights are represented by the concrete sup-normed vector
`Fin 4 → ℝ`.  All definitions below are the rational formulas used by the
simplex API, but remain total on the ambient vector space.  This makes both
continuity and denominator-floor estimates explicit, without an appeal to
finite-dimensional norm equivalence.
-/

set_option autoImplicit false

namespace Forsythe
namespace FourNode

open Filter Polynomial
open scoped BigOperators Topology

noncomputable section

/-- Ambient coordinate representation of a four-node weight state. -/
abbrev WeightVector := Fin 4 → ℝ

/-- Forget the simplex proofs and retain the concrete weight vector. -/
def weightVector (x : Weights) : WeightVector := fun i ↦ x i

@[simp]
theorem weightVector_apply (x : Weights) (i : Fin 4) :
    weightVector x i = x i := rfl

/-- Moment formula on the ambient weight vector. -/
def weightedMomentVector (lambda : Fin 4 → ℝ)
    (w : WeightVector) (k : ℕ) : ℝ :=
  ∑ i, w i * lambda i ^ k

/-- Moment Gram determinant on the ambient weight vector. -/
def weightedMomentGramDetVector (lambda : Fin 4 → ℝ)
    (w : WeightVector) : ℝ :=
  weightedMomentVector lambda w 0 * weightedMomentVector lambda w 2 -
    weightedMomentVector lambda w 1 ^ 2

/-- Cramer-system monic quadratic on the ambient weight vector. -/
def orthogonalPolynomialVector (lambda : Fin 4 → ℝ)
    (w : WeightVector) : MonicQuadratic where
  linearCoeff :=
    (weightedMomentVector lambda w 1 * weightedMomentVector lambda w 2 -
      weightedMomentVector lambda w 0 * weightedMomentVector lambda w 3) /
        weightedMomentGramDetVector lambda w
  constantCoeff :=
    (weightedMomentVector lambda w 1 * weightedMomentVector lambda w 3 -
      weightedMomentVector lambda w 2 ^ 2) /
        weightedMomentGramDetVector lambda w

/-- Evaluation of the ambient Cramer polynomial at a scalar. -/
def orthogonalPolynomialVectorEval (lambda : Fin 4 → ℝ)
    (w : WeightVector) (t : ℝ) : ℝ :=
  t ^ 2 + (orthogonalPolynomialVector lambda w).linearCoeff * t +
    (orthogonalPolynomialVector lambda w).constantCoeff

/-- Residual height on the ambient weight vector. -/
def heightVector (lambda : Fin 4 → ℝ) (w : WeightVector) : ℝ :=
  ∑ i, w i * orthogonalPolynomialVectorEval lambda w (lambda i) ^ 2

/-- Total rational squared-residual update on the ambient weight vector. -/
def nextWeightVector (lambda : Fin 4 → ℝ)
    (w : WeightVector) : WeightVector := fun i ↦
  w i * orthogonalPolynomialVectorEval lambda w (lambda i) ^ 2 /
    heightVector lambda w

/-- Fixed-node rational formula for `rho` on the ambient vector space. -/
def rhoVector (lambda : Fin 4 → ℝ) (w : WeightVector) : ℝ :=
  lambda 0 - E lambda 0 *
    (w 0 * orthogonalPolynomialVectorEval lambda w (lambda 0)) /
      heightVector lambda w

/-- The cubic coefficient in the interpolation identity, written directly
in terms of the two consecutive linear coefficients. -/
def alphaVector (lambda : Fin 4 → ℝ) (w : WeightVector) : ℝ :=
  (orthogonalPolynomialVector lambda w).linearCoeff +
    (orthogonalPolynomialVector lambda (nextWeightVector lambda w)).linearCoeff -
      (nodalQuartic lambda).coeff 3

@[simp]
theorem weightedMomentVector_weightVector
    (lambda : Fin 4 → ℝ) (x : Weights) (k : ℕ) :
    weightedMomentVector lambda (weightVector x) k =
      weightedMoment lambda x k := rfl

@[simp]
theorem weightedMomentGramDetVector_weightVector
    (lambda : Fin 4 → ℝ) (x : Weights) :
    weightedMomentGramDetVector lambda (weightVector x) =
      weightedMomentGramDet lambda x := rfl

@[simp]
theorem orthogonalPolynomialVector_weightVector
    (lambda : Fin 4 → ℝ) (x : Weights) :
    orthogonalPolynomialVector lambda (weightVector x) = P lambda x := rfl

@[simp]
theorem orthogonalPolynomialVectorEval_weightVector
    (lambda : Fin 4 → ℝ) (x : Weights) (t : ℝ) :
    orthogonalPolynomialVectorEval lambda (weightVector x) t =
      (P lambda x).toPolynomial.eval t := by
  simp [orthogonalPolynomialVectorEval, MonicQuadratic.eval]

@[simp]
theorem heightVector_weightVector
    (lambda : Fin 4 → ℝ) (x : Weights) :
    heightVector lambda (weightVector x) = H lambda x := by
  simp only [heightVector, height, weightedPolyInner,
    orthogonalPolynomialVectorEval_weightVector, weightVector_apply]
  apply Finset.sum_congr rfl
  intro i hi
  ring

@[simp]
theorem nextWeightVector_weightVector
    (lambda : Fin 4 → ℝ) (hlambda : Function.Injective lambda)
    (x : Weights) (i : Fin 4) :
    nextWeightVector lambda (weightVector x) i =
      T lambda hlambda x i := by
  simp [nextWeightVector, T_weight]

@[simp]
theorem rhoVector_weightVector
    (lambda : Fin 4 → ℝ) (x : Weights) :
    rhoVector lambda (weightVector x) = rho lambda x := by
  simp [rhoVector, rho]

private theorem coeff_three_mul_monicQuadratic
    (p q : MonicQuadratic) :
    (p.toPolynomial * q.toPolynomial).coeff 3 =
      p.linearCoeff + q.linearCoeff := by
  rw [MonicQuadratic.toPolynomial, MonicQuadratic.toPolynomial]
  ring_nf
  have hmiddle :
      (C p.linearCoeff * C q.linearCoeff * X ^ 2 : ℝ[X]).coeff 3 = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    compute_degree
    norm_num
  simp [coeff_add, coeff_mul_C, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C]
  exact hmiddle

@[simp]
theorem alphaVector_weightVector
    (lambda : Fin 4 → ℝ) (hlambda : Function.Injective lambda)
    (x : Weights) :
    alphaVector lambda (weightVector x) = alpha lambda hlambda x := by
  rw [alpha, alphaVector, interpolationDifference]
  simp only [coeff_sub, coeff_C_of_ne_zero (by norm_num : (3 : ℕ) ≠ 0),
    sub_zero, coeff_three_mul_monicQuadratic,
    orthogonalPolynomialVector_weightVector]
  congr 2
  have hnext : nextWeightVector lambda (weightVector x) =
      weightVector (T lambda hlambda x) := by
    funext i
    exact nextWeightVector_weightVector lambda hlambda x i
  rw [hnext, orthogonalPolynomialVector_weightVector]

/-- Every ambient moment is globally continuous. -/
theorem continuous_weightedMomentVector
    (lambda : Fin 4 → ℝ) (k : ℕ) :
    Continuous (fun w : WeightVector ↦ weightedMomentVector lambda w k) := by
  apply continuous_finsetSum
  intro i hi
  exact (continuous_apply i).mul continuous_const

/-- The ambient moment Gram determinant is globally continuous. -/
theorem continuous_weightedMomentGramDetVector
    (lambda : Fin 4 → ℝ) :
    Continuous (weightedMomentGramDetVector lambda) := by
  exact ((continuous_weightedMomentVector lambda 0).mul
    (continuous_weightedMomentVector lambda 2)).sub
      ((continuous_weightedMomentVector lambda 1).pow 2)

theorem continuousAt_orthogonalPolynomialVector_linearCoeff
    (lambda : Fin 4 → ℝ) (w : WeightVector)
    (hdet : weightedMomentGramDetVector lambda w ≠ 0) :
    ContinuousAt
      (fun u ↦ (orthogonalPolynomialVector lambda u).linearCoeff) w := by
  apply ContinuousAt.div
  · exact ((continuous_weightedMomentVector lambda 1).continuousAt.mul
      (continuous_weightedMomentVector lambda 2).continuousAt).sub
        ((continuous_weightedMomentVector lambda 0).continuousAt.mul
          (continuous_weightedMomentVector lambda 3).continuousAt)
  · exact (continuous_weightedMomentGramDetVector lambda).continuousAt
  · exact hdet

theorem continuousAt_orthogonalPolynomialVector_constantCoeff
    (lambda : Fin 4 → ℝ) (w : WeightVector)
    (hdet : weightedMomentGramDetVector lambda w ≠ 0) :
    ContinuousAt
      (fun u ↦ (orthogonalPolynomialVector lambda u).constantCoeff) w := by
  apply ContinuousAt.div
  · exact ((continuous_weightedMomentVector lambda 1).continuousAt.mul
      (continuous_weightedMomentVector lambda 3).continuousAt).sub
        ((continuous_weightedMomentVector lambda 2).continuousAt.pow 2)
  · exact (continuous_weightedMomentGramDetVector lambda).continuousAt
  · exact hdet

theorem continuousAt_orthogonalPolynomialVector_coeffPair
    (lambda : Fin 4 → ℝ) (w : WeightVector)
    (hdet : weightedMomentGramDetVector lambda w ≠ 0) :
    ContinuousAt
      (fun u ↦ (orthogonalPolynomialVector lambda u).coeffPair) w :=
  (continuousAt_orthogonalPolynomialVector_linearCoeff lambda w hdet).prodMk
    (continuousAt_orthogonalPolynomialVector_constantCoeff lambda w hdet)

theorem continuousAt_orthogonalPolynomialVectorEval
    (lambda : Fin 4 → ℝ) (w : WeightVector)
    (hdet : weightedMomentGramDetVector lambda w ≠ 0) (t : ℝ) :
    ContinuousAt (fun u ↦ orthogonalPolynomialVectorEval lambda u t) w := by
  exact (continuousAt_const.add
    ((continuousAt_orthogonalPolynomialVector_linearCoeff lambda w hdet).mul
      continuousAt_const)).add
        (continuousAt_orthogonalPolynomialVector_constantCoeff lambda w hdet)

theorem continuousAt_heightVector
    (lambda : Fin 4 → ℝ) (w : WeightVector)
    (hdet : weightedMomentGramDetVector lambda w ≠ 0) :
    ContinuousAt (heightVector lambda) w := by
  apply tendsto_finsetSum
  intro i hi
  exact ((continuous_apply i).continuousAt).mul
    ((continuousAt_orthogonalPolynomialVectorEval lambda w hdet (lambda i)).pow 2)

theorem continuousAt_nextWeightVector
    (lambda : Fin 4 → ℝ) (w : WeightVector)
    (hdet : weightedMomentGramDetVector lambda w ≠ 0)
    (hheight : heightVector lambda w ≠ 0) :
    ContinuousAt (nextWeightVector lambda) w := by
  apply continuousAt_pi'
  intro i
  apply ContinuousAt.div
  · exact ((continuous_apply i).continuousAt).mul
      ((continuousAt_orthogonalPolynomialVectorEval lambda w hdet (lambda i)).pow 2)
  · exact continuousAt_heightVector lambda w hdet
  · exact hheight

theorem continuousAt_rhoVector
    (lambda : Fin 4 → ℝ) (w : WeightVector)
    (hdet : weightedMomentGramDetVector lambda w ≠ 0)
    (hheight : heightVector lambda w ≠ 0) :
    ContinuousAt (rhoVector lambda) w := by
  exact continuousAt_const.sub
    ((continuousAt_const.mul (((continuous_apply 0).continuousAt).mul
      (continuousAt_orthogonalPolynomialVectorEval lambda w hdet (lambda 0)))).div
        (continuousAt_heightVector lambda w hdet) hheight)

theorem continuousAt_alphaVector
    (lambda : Fin 4 → ℝ) (w : WeightVector)
    (hdet : weightedMomentGramDetVector lambda w ≠ 0)
    (hheight : heightVector lambda w ≠ 0)
    (hdetNext : weightedMomentGramDetVector lambda
      (nextWeightVector lambda w) ≠ 0) :
    ContinuousAt (alphaVector lambda) w := by
  have hnext := continuousAt_nextWeightVector lambda w hdet hheight
  exact (continuousAt_orthogonalPolynomialVector_linearCoeff lambda w hdet).add
    ((continuousAt_orthogonalPolynomialVector_linearCoeff lambda
      (nextWeightVector lambda w) hdetNext).comp' hnext) |>.sub continuousAt_const

/-! ## Explicit sup-norm estimates -/

/-- Exact sup-norm Lipschitz constant for the `k`th weighted moment. -/
def momentLipschitzConstant (lambda : Fin 4 → ℝ) (k : ℕ) : ℝ :=
  ∑ i, |lambda i| ^ k

theorem momentLipschitzConstant_nonneg
    (lambda : Fin 4 → ℝ) (k : ℕ) :
    0 ≤ momentLipschitzConstant lambda k := by
  exact Finset.sum_nonneg fun i hi ↦ pow_nonneg (abs_nonneg _) _

theorem abs_weightVector_sub_apply_le
    (u v : WeightVector) (i : Fin 4) :
    |u i - v i| ≤ ‖u - v‖ := by
  simpa [Real.norm_eq_abs] using norm_le_pi_norm (u - v) i

/-- Moments are globally Lipschitz in the concrete sup norm. -/
theorem abs_weightedMomentVector_sub_le
    (lambda : Fin 4 → ℝ) (k : ℕ) (u v : WeightVector) :
    |weightedMomentVector lambda u k - weightedMomentVector lambda v k| ≤
      momentLipschitzConstant lambda k * ‖u - v‖ := by
  rw [weightedMomentVector, weightedMomentVector, ← Finset.sum_sub_distrib]
  calc
    |∑ i, (u i * lambda i ^ k - v i * lambda i ^ k)| =
        |∑ i, (u i - v i) * lambda i ^ k| := by
      apply congrArg abs
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ ∑ i, |(u i - v i) * lambda i ^ k| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |u i - v i| * |lambda i| ^ k := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [abs_mul, abs_pow]
    _ ≤ ∑ i, ‖u - v‖ * |lambda i| ^ k := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_right (abs_weightVector_sub_apply_le u v i)
        (pow_nonneg (abs_nonneg _) _)
    _ = momentLipschitzConstant lambda k * ‖u - v‖ := by
      rw [momentLipschitzConstant, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      ring

private theorem weight_le_one_continuity (x : Weights) (i : Fin 4) : x i ≤ 1 := by
  rw [← x.sum_eq_one]
  exact Finset.single_le_sum (fun j _ ↦ x.nonneg j) (Finset.mem_univ i)

/-- A simplex moment is bounded by the same explicit coefficient sum. -/
theorem abs_weightedMoment_le
    (lambda : Fin 4 → ℝ) (x : Weights) (k : ℕ) :
    |weightedMoment lambda x k| ≤ momentLipschitzConstant lambda k := by
  rw [weightedMoment, momentLipschitzConstant]
  calc
    |∑ i, x i * lambda i ^ k| ≤
        ∑ i, |x i * lambda i ^ k| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, x i * |lambda i| ^ k := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [abs_mul, abs_pow, abs_of_nonneg (x.nonneg i)]
    _ ≤ ∑ i, |lambda i| ^ k := by
      apply Finset.sum_le_sum
      intro i hi
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (weight_le_one_continuity x i) (pow_nonneg (abs_nonneg _) _)

/-- Explicit Lipschitz constant for the Gram determinant on the simplex. -/
def gramLipschitzConstant (lambda : Fin 4 → ℝ) : ℝ :=
  momentLipschitzConstant lambda 2 +
    2 * momentLipschitzConstant lambda 1 ^ 2

theorem gramLipschitzConstant_nonneg (lambda : Fin 4 → ℝ) :
    0 ≤ gramLipschitzConstant lambda := by
  dsimp only [gramLipschitzConstant]
  exact add_nonneg (momentLipschitzConstant_nonneg lambda 2)
    (mul_nonneg (by norm_num) (sq_nonneg _))

private theorem abs_sq_sub_sq_le
    (a b A d : ℝ) (ha : |a| ≤ A) (hb : |b| ≤ A)
    (hd : |a - b| ≤ d) (hA : 0 ≤ A) :
    |a ^ 2 - b ^ 2| ≤ 2 * A * d := by
  rw [show a ^ 2 - b ^ 2 = (a + b) * (a - b) by ring, abs_mul]
  calc
    |a + b| * |a - b| ≤ (|a| + |b|) * |a - b| := by
      exact mul_le_mul_of_nonneg_right (abs_add_le a b) (abs_nonneg _)
    _ ≤ (A + A) * d := by
      exact mul_le_mul (add_le_add ha hb) hd (abs_nonneg _) (by positivity)
    _ = 2 * A * d := by ring

/-- On normalized nonnegative weights, the moment Gram determinant is
globally Lipschitz in the concrete sup norm. -/
theorem abs_weightedMomentGramDet_sub_le
    (lambda : Fin 4 → ℝ) (x y : Weights) :
    |weightedMomentGramDet lambda x - weightedMomentGramDet lambda y| ≤
      gramLipschitzConstant lambda *
        ‖weightVector x - weightVector y‖ := by
  let d := ‖weightVector x - weightVector y‖
  let B1 := momentLipschitzConstant lambda 1
  let B2 := momentLipschitzConstant lambda 2
  have hd : 0 ≤ d := norm_nonneg _
  have hB1 : 0 ≤ B1 := momentLipschitzConstant_nonneg lambda 1
  have hm1x : |weightedMoment lambda x 1| ≤ B1 :=
    abs_weightedMoment_le lambda x 1
  have hm1y : |weightedMoment lambda y 1| ≤ B1 :=
    abs_weightedMoment_le lambda y 1
  have hm1diff :
      |weightedMoment lambda x 1 - weightedMoment lambda y 1| ≤ B1 * d := by
    simpa [B1, d] using abs_weightedMomentVector_sub_le lambda 1
      (weightVector x) (weightVector y)
  have hm2diff :
      |weightedMoment lambda x 2 - weightedMoment lambda y 2| ≤ B2 * d := by
    simpa [B2, d] using abs_weightedMomentVector_sub_le lambda 2
      (weightVector x) (weightVector y)
  have hsq :
      |weightedMoment lambda x 1 ^ 2 - weightedMoment lambda y 1 ^ 2| ≤
        2 * B1 ^ 2 * d := by
    have := abs_sq_sub_sq_le (weightedMoment lambda x 1)
      (weightedMoment lambda y 1) B1 (B1 * d) hm1x hm1y hm1diff hB1
    nlinarith
  simp only [weightedMomentGramDet, weightedMoment_zero, one_mul]
  calc
    |(weightedMoment lambda x 2 - weightedMoment lambda x 1 ^ 2) -
        (weightedMoment lambda y 2 - weightedMoment lambda y 1 ^ 2)| ≤
      |weightedMoment lambda x 2 - weightedMoment lambda y 2| +
        |weightedMoment lambda x 1 ^ 2 - weightedMoment lambda y 1 ^ 2| := by
      calc
        |(weightedMoment lambda x 2 - weightedMoment lambda x 1 ^ 2) -
            (weightedMoment lambda y 2 - weightedMoment lambda y 1 ^ 2)| =
          |(weightedMoment lambda x 2 - weightedMoment lambda y 2) +
            -(weightedMoment lambda x 1 ^ 2 -
              weightedMoment lambda y 1 ^ 2)| := by
                congr 1
                ring
        _ ≤ |weightedMoment lambda x 2 - weightedMoment lambda y 2| +
            |-(weightedMoment lambda x 1 ^ 2 -
              weightedMoment lambda y 1 ^ 2)| := abs_add_le _ _
        _ = |weightedMoment lambda x 2 - weightedMoment lambda y 2| +
            |weightedMoment lambda x 1 ^ 2 -
              weightedMoment lambda y 1 ^ 2| := by rw [abs_neg]
    _ ≤ B2 * d + 2 * B1 ^ 2 * d := add_le_add hm2diff hsq
    _ = gramLipschitzConstant lambda *
        ‖weightVector x - weightVector y‖ := by
      dsimp only [gramLipschitzConstant, B1, B2, d]
      ring

/-- Numerator of the linear coefficient in the simplex Cramer system. -/
def linearNumerator (lambda : Fin 4 → ℝ) (x : Weights) : ℝ :=
  weightedMoment lambda x 1 * weightedMoment lambda x 2 -
    weightedMoment lambda x 3

/-- Numerator of the constant coefficient in the simplex Cramer system. -/
def constantNumerator (lambda : Fin 4 → ℝ) (x : Weights) : ℝ :=
  weightedMoment lambda x 1 * weightedMoment lambda x 3 -
    weightedMoment lambda x 2 ^ 2

/-- Common absolute bound for the two Cramer numerators. -/
def coefficientNumeratorBound (lambda : Fin 4 → ℝ) : ℝ :=
  max
    (momentLipschitzConstant lambda 1 * momentLipschitzConstant lambda 2 +
      momentLipschitzConstant lambda 3)
    (momentLipschitzConstant lambda 1 * momentLipschitzConstant lambda 3 +
      momentLipschitzConstant lambda 2 ^ 2)

/-- Common sup-norm Lipschitz constant for the two Cramer numerators. -/
def coefficientNumeratorLipschitzConstant
    (lambda : Fin 4 → ℝ) : ℝ :=
  max
    (2 * momentLipschitzConstant lambda 1 *
      momentLipschitzConstant lambda 2 +
      momentLipschitzConstant lambda 3)
    (2 * momentLipschitzConstant lambda 1 *
      momentLipschitzConstant lambda 3 +
      2 * momentLipschitzConstant lambda 2 ^ 2)

theorem coefficientNumeratorBound_nonneg (lambda : Fin 4 → ℝ) :
    0 ≤ coefficientNumeratorBound lambda := by
  apply le_trans ?_ (le_max_left _ _)
  exact add_nonneg
    (mul_nonneg (momentLipschitzConstant_nonneg lambda 1)
      (momentLipschitzConstant_nonneg lambda 2))
    (momentLipschitzConstant_nonneg lambda 3)

theorem coefficientNumeratorLipschitzConstant_nonneg
    (lambda : Fin 4 → ℝ) :
    0 ≤ coefficientNumeratorLipschitzConstant lambda := by
  apply le_trans ?_ (le_max_left _ _)
  exact add_nonneg
    (mul_nonneg
      (mul_nonneg (by norm_num)
        (momentLipschitzConstant_nonneg lambda 1))
      (momentLipschitzConstant_nonneg lambda 2))
    (momentLipschitzConstant_nonneg lambda 3)

private theorem abs_mul_sub_mul_le
    (a b c d : ℝ) :
    |a * b - c * d| ≤ |a| * |b - d| + |d| * |a - c| := by
  calc
    |a * b - c * d| = |a * (b - d) + d * (a - c)| := by
      congr 1
      ring
    _ ≤ |a * (b - d)| + |d * (a - c)| := abs_add_le _ _
    _ = |a| * |b - d| + |d| * |a - c| := by rw [abs_mul, abs_mul]

theorem abs_linearNumerator_le
    (lambda : Fin 4 → ℝ) (x : Weights) :
    |linearNumerator lambda x| ≤ coefficientNumeratorBound lambda := by
  calc
    |linearNumerator lambda x| ≤
        |weightedMoment lambda x 1| * |weightedMoment lambda x 2| +
          |weightedMoment lambda x 3| := by
      rw [linearNumerator]
      exact (abs_sub _ _).trans_eq (by rw [abs_mul])
    _ ≤ momentLipschitzConstant lambda 1 *
          momentLipschitzConstant lambda 2 +
        momentLipschitzConstant lambda 3 := by
      exact add_le_add
        (mul_le_mul (abs_weightedMoment_le lambda x 1)
          (abs_weightedMoment_le lambda x 2) (abs_nonneg _)
          (momentLipschitzConstant_nonneg lambda 1))
        (abs_weightedMoment_le lambda x 3)
    _ ≤ coefficientNumeratorBound lambda := le_max_left _ _

theorem abs_constantNumerator_le
    (lambda : Fin 4 → ℝ) (x : Weights) :
    |constantNumerator lambda x| ≤ coefficientNumeratorBound lambda := by
  calc
    |constantNumerator lambda x| ≤
        |weightedMoment lambda x 1 * weightedMoment lambda x 3| +
          |weightedMoment lambda x 2 ^ 2| := by
      rw [constantNumerator]
      exact abs_sub _ _
    _ = |weightedMoment lambda x 1| * |weightedMoment lambda x 3| +
          |weightedMoment lambda x 2| ^ 2 := by rw [abs_mul, abs_pow]
    _ ≤ momentLipschitzConstant lambda 1 *
          momentLipschitzConstant lambda 3 +
        momentLipschitzConstant lambda 2 ^ 2 := by
      have hsquare : |weightedMoment lambda x 2| ^ 2 ≤
          momentLipschitzConstant lambda 2 ^ 2 := by
        nlinarith [abs_weightedMoment_le lambda x 2,
          abs_nonneg (weightedMoment lambda x 2),
          momentLipschitzConstant_nonneg lambda 2]
      exact add_le_add
        (mul_le_mul (abs_weightedMoment_le lambda x 1)
          (abs_weightedMoment_le lambda x 3) (abs_nonneg _)
          (momentLipschitzConstant_nonneg lambda 1))
        hsquare
    _ ≤ coefficientNumeratorBound lambda := le_max_right _ _

theorem abs_linearNumerator_sub_le
    (lambda : Fin 4 → ℝ) (x y : Weights) :
    |linearNumerator lambda x - linearNumerator lambda y| ≤
      coefficientNumeratorLipschitzConstant lambda *
        ‖weightVector x - weightVector y‖ := by
  let d := ‖weightVector x - weightVector y‖
  let B1 := momentLipschitzConstant lambda 1
  let B2 := momentLipschitzConstant lambda 2
  let B3 := momentLipschitzConstant lambda 3
  have hB1 : 0 ≤ B1 := momentLipschitzConstant_nonneg lambda 1
  have hB2 : 0 ≤ B2 := momentLipschitzConstant_nonneg lambda 2
  have hd : 0 ≤ d := norm_nonneg _
  have hm1x : |weightedMoment lambda x 1| ≤ B1 :=
    abs_weightedMoment_le lambda x 1
  have hm2y : |weightedMoment lambda y 2| ≤ B2 :=
    abs_weightedMoment_le lambda y 2
  have hm1diff :
      |weightedMoment lambda x 1 - weightedMoment lambda y 1| ≤ B1 * d := by
    simpa [B1, d] using (abs_weightedMomentVector_sub_le lambda 1
      (weightVector x) (weightVector y))
  have hm2diff :
      |weightedMoment lambda x 2 - weightedMoment lambda y 2| ≤ B2 * d := by
    simpa [B2, d] using (abs_weightedMomentVector_sub_le lambda 2
      (weightVector x) (weightVector y))
  have hprod := abs_mul_sub_mul_le
    (weightedMoment lambda x 1) (weightedMoment lambda x 2)
    (weightedMoment lambda y 1) (weightedMoment lambda y 2)
  have hprodBound :
      |weightedMoment lambda x 1 * weightedMoment lambda x 2 -
        weightedMoment lambda y 1 * weightedMoment lambda y 2| ≤
        2 * B1 * B2 * d := by
    calc
      _ ≤ |weightedMoment lambda x 1| *
            |weightedMoment lambda x 2 - weightedMoment lambda y 2| +
          |weightedMoment lambda y 2| *
            |weightedMoment lambda x 1 - weightedMoment lambda y 1| := hprod
      _ ≤ B1 * (B2 * d) + B2 * (B1 * d) := by
        exact add_le_add
          (mul_le_mul hm1x hm2diff (abs_nonneg _) hB1)
          (mul_le_mul hm2y hm1diff (abs_nonneg _) hB2)
      _ = 2 * B1 * B2 * d := by ring
  have hm3 :
      |weightedMoment lambda x 3 - weightedMoment lambda y 3| ≤ B3 * d := by
    simpa [B3, d] using abs_weightedMomentVector_sub_le lambda 3
      (weightVector x) (weightVector y)
  calc
    |linearNumerator lambda x - linearNumerator lambda y| ≤
        |weightedMoment lambda x 1 * weightedMoment lambda x 2 -
          weightedMoment lambda y 1 * weightedMoment lambda y 2| +
        |weightedMoment lambda x 3 - weightedMoment lambda y 3| := by
      rw [linearNumerator, linearNumerator]
      calc
        _ = |(weightedMoment lambda x 1 * weightedMoment lambda x 2 -
              weightedMoment lambda y 1 * weightedMoment lambda y 2) +
            -(weightedMoment lambda x 3 - weightedMoment lambda y 3)| := by
              congr 1
              ring
        _ ≤ |weightedMoment lambda x 1 * weightedMoment lambda x 2 -
              weightedMoment lambda y 1 * weightedMoment lambda y 2| +
            |-(weightedMoment lambda x 3 - weightedMoment lambda y 3)| :=
          abs_add_le _ _
        _ = _ := by rw [abs_neg]
    _ ≤ 2 * B1 * B2 * d + B3 * d := add_le_add hprodBound hm3
    _ ≤ coefficientNumeratorLipschitzConstant lambda *
        ‖weightVector x - weightVector y‖ := by
      dsimp only [coefficientNumeratorLipschitzConstant, B1, B2, B3, d]
      rw [show 2 * momentLipschitzConstant lambda 1 *
          momentLipschitzConstant lambda 2 *
          ‖weightVector x - weightVector y‖ +
          momentLipschitzConstant lambda 3 *
          ‖weightVector x - weightVector y‖ =
        (2 * momentLipschitzConstant lambda 1 *
          momentLipschitzConstant lambda 2 +
          momentLipschitzConstant lambda 3) *
          ‖weightVector x - weightVector y‖ by ring]
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)

theorem abs_constantNumerator_sub_le
    (lambda : Fin 4 → ℝ) (x y : Weights) :
    |constantNumerator lambda x - constantNumerator lambda y| ≤
      coefficientNumeratorLipschitzConstant lambda *
        ‖weightVector x - weightVector y‖ := by
  let d := ‖weightVector x - weightVector y‖
  let B1 := momentLipschitzConstant lambda 1
  let B2 := momentLipschitzConstant lambda 2
  let B3 := momentLipschitzConstant lambda 3
  have hB1 : 0 ≤ B1 := momentLipschitzConstant_nonneg lambda 1
  have hB3 : 0 ≤ B3 := momentLipschitzConstant_nonneg lambda 3
  have hd : 0 ≤ d := norm_nonneg _
  have hm1x : |weightedMoment lambda x 1| ≤ B1 :=
    abs_weightedMoment_le lambda x 1
  have hm3y : |weightedMoment lambda y 3| ≤ B3 :=
    abs_weightedMoment_le lambda y 3
  have hm1diff :
      |weightedMoment lambda x 1 - weightedMoment lambda y 1| ≤ B1 * d := by
    simpa [B1, d] using (abs_weightedMomentVector_sub_le lambda 1
      (weightVector x) (weightVector y))
  have hm3diff :
      |weightedMoment lambda x 3 - weightedMoment lambda y 3| ≤ B3 * d := by
    simpa [B3, d] using (abs_weightedMomentVector_sub_le lambda 3
      (weightVector x) (weightVector y))
  have hprod := abs_mul_sub_mul_le
    (weightedMoment lambda x 1) (weightedMoment lambda x 3)
    (weightedMoment lambda y 1) (weightedMoment lambda y 3)
  have hprodBound :
      |weightedMoment lambda x 1 * weightedMoment lambda x 3 -
        weightedMoment lambda y 1 * weightedMoment lambda y 3| ≤
        2 * B1 * B3 * d := by
    calc
      _ ≤ |weightedMoment lambda x 1| *
            |weightedMoment lambda x 3 - weightedMoment lambda y 3| +
          |weightedMoment lambda y 3| *
            |weightedMoment lambda x 1 - weightedMoment lambda y 1| := hprod
      _ ≤ B1 * (B3 * d) + B3 * (B1 * d) := by
        exact add_le_add
          (mul_le_mul hm1x hm3diff (abs_nonneg _) hB1)
          (mul_le_mul hm3y hm1diff (abs_nonneg _) hB3)
      _ = 2 * B1 * B3 * d := by ring
  have hsq :
      |weightedMoment lambda x 2 ^ 2 - weightedMoment lambda y 2 ^ 2| ≤
        2 * B2 ^ 2 * d := by
    have h := abs_sq_sub_sq_le (weightedMoment lambda x 2)
      (weightedMoment lambda y 2) B2 (B2 * d)
      (abs_weightedMoment_le lambda x 2)
      (abs_weightedMoment_le lambda y 2)
      (by simpa [B2, d] using (abs_weightedMomentVector_sub_le lambda 2
        (weightVector x) (weightVector y)))
      (momentLipschitzConstant_nonneg lambda 2)
    simpa [pow_two, mul_assoc] using h
  calc
    |constantNumerator lambda x - constantNumerator lambda y| ≤
        |weightedMoment lambda x 1 * weightedMoment lambda x 3 -
          weightedMoment lambda y 1 * weightedMoment lambda y 3| +
        |weightedMoment lambda x 2 ^ 2 - weightedMoment lambda y 2 ^ 2| := by
      rw [constantNumerator, constantNumerator]
      calc
        _ = |(weightedMoment lambda x 1 * weightedMoment lambda x 3 -
              weightedMoment lambda y 1 * weightedMoment lambda y 3) +
            -(weightedMoment lambda x 2 ^ 2 - weightedMoment lambda y 2 ^ 2)| := by
              congr 1
              ring
        _ ≤ |weightedMoment lambda x 1 * weightedMoment lambda x 3 -
              weightedMoment lambda y 1 * weightedMoment lambda y 3| +
            |-(weightedMoment lambda x 2 ^ 2 - weightedMoment lambda y 2 ^ 2)| :=
          abs_add_le _ _
        _ = _ := by rw [abs_neg]
    _ ≤ 2 * B1 * B3 * d + 2 * B2 ^ 2 * d := add_le_add hprodBound hsq
    _ ≤ coefficientNumeratorLipschitzConstant lambda *
        ‖weightVector x - weightVector y‖ := by
      dsimp only [coefficientNumeratorLipschitzConstant, B1, B2, B3, d]
      rw [show 2 * momentLipschitzConstant lambda 1 *
          momentLipschitzConstant lambda 3 *
          ‖weightVector x - weightVector y‖ +
          2 * momentLipschitzConstant lambda 2 ^ 2 *
          ‖weightVector x - weightVector y‖ =
        (2 * momentLipschitzConstant lambda 1 *
          momentLipschitzConstant lambda 3 +
          2 * momentLipschitzConstant lambda 2 ^ 2) *
          ‖weightVector x - weightVector y‖ by ring]
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)

theorem P_linearCoeff_eq_linearNumerator_div
    (lambda : Fin 4 → ℝ) (x : Weights) :
    (P lambda x).linearCoeff =
      linearNumerator lambda x / weightedMomentGramDet lambda x := by
  simp [P, orthogonalPolynomial, linearNumerator, weightedMoment_zero]

theorem P_constantCoeff_eq_constantNumerator_div
    (lambda : Fin 4 → ℝ) (x : Weights) :
    (P lambda x).constantCoeff =
      constantNumerator lambda x / weightedMomentGramDet lambda x := by
  simp [P, orthogonalPolynomial, constantNumerator]

/-- Explicit coefficient-pair bound under a positive Gram floor. -/
theorem P_coeffPair_norm_le_of_gram_floor
    (lambda : Fin 4 → ℝ) (x : Weights) {delta : ℝ}
    (hdelta : 0 < delta)
    (hdet : delta ≤ weightedMomentGramDet lambda x) :
    ‖(P lambda x).coeffPair‖ ≤ coefficientNumeratorBound lambda / delta := by
  have hdetPos : 0 < weightedMomentGramDet lambda x := hdelta.trans_le hdet
  have hlinear : |(P lambda x).linearCoeff| ≤
      coefficientNumeratorBound lambda / delta := by
    rw [P_linearCoeff_eq_linearNumerator_div, abs_div, abs_of_pos hdetPos]
    exact div_le_div₀ (coefficientNumeratorBound_nonneg lambda)
      (abs_linearNumerator_le lambda x)
      hdelta hdet
  have hconstant : |(P lambda x).constantCoeff| ≤
      coefficientNumeratorBound lambda / delta := by
    rw [P_constantCoeff_eq_constantNumerator_div, abs_div, abs_of_pos hdetPos]
    exact div_le_div₀ (coefficientNumeratorBound_nonneg lambda)
      (abs_constantNumerator_le lambda x)
      hdelta hdet
  rw [MonicQuadratic.coeffPair, Prod.norm_def, Real.norm_eq_abs,
    Real.norm_eq_abs]
  exact max_le hlinear hconstant

/-- Explicit coefficient-pair Lipschitz constant under a common Gram floor. -/
def coefficientPairLipschitzConstant
    (lambda : Fin 4 → ℝ) (delta : ℝ) : ℝ :=
  coefficientNumeratorLipschitzConstant lambda / delta +
    coefficientNumeratorBound lambda * gramLipschitzConstant lambda /
      delta ^ 2

theorem coefficientPairLipschitzConstant_nonneg
    (lambda : Fin 4 → ℝ) {delta : ℝ} (hdelta : 0 < delta) :
    0 ≤ coefficientPairLipschitzConstant lambda delta := by
  dsimp only [coefficientPairLipschitzConstant]
  exact add_nonneg
    (div_nonneg (coefficientNumeratorLipschitzConstant_nonneg lambda)
      hdelta.le)
    (div_nonneg
      (mul_nonneg (coefficientNumeratorBound_nonneg lambda)
        (gramLipschitzConstant_nonneg lambda)) (sq_nonneg _))

private theorem abs_div_sub_div_le_of_floor
    {nx ny dx dy L N G d delta : ℝ}
    (hdelta : 0 < delta) (hdx : delta ≤ dx) (hdy : delta ≤ dy)
    (hL : 0 ≤ L) (hN : 0 ≤ N) (hG : 0 ≤ G) (hd : 0 ≤ d)
    (hnumDiff : |nx - ny| ≤ L * d) (hnumY : |ny| ≤ N)
    (hdenDiff : |dx - dy| ≤ G * d) :
    |nx / dx - ny / dy| ≤
      (L / delta + N * G / delta ^ 2) * d := by
  have hdxPos : 0 < dx := hdelta.trans_le hdx
  have hdyPos : 0 < dy := hdelta.trans_le hdy
  have hdeltaSq : 0 < delta ^ 2 := sq_pos_of_pos hdelta
  have hdxdyPos : 0 < dx * dy := mul_pos hdxPos hdyPos
  have hdenLower : delta ^ 2 ≤ dx * dy := by
    rw [pow_two]
    exact mul_le_mul hdx hdy hdelta.le hdxPos.le
  have hfirst : |(nx - ny) / dx| ≤ (L / delta) * d := by
    rw [abs_div, abs_of_pos hdxPos]
    calc
      |nx - ny| / dx ≤ (L * d) / delta := by
        apply (div_le_div_iff₀ hdxPos hdelta).2
        exact mul_le_mul hnumDiff hdx hdelta.le (mul_nonneg hL hd)
      _ = (L / delta) * d := by ring
  have hdenDiff' : |dy - dx| ≤ G * d := by
    simpa [abs_sub_comm] using hdenDiff
  have hsecond : |ny * (dy - dx) / (dx * dy)| ≤
      (N * G / delta ^ 2) * d := by
    rw [abs_div, abs_mul, abs_of_pos hdxdyPos]
    calc
      |ny| * |dy - dx| / (dx * dy) ≤ (N * (G * d)) / delta ^ 2 := by
        apply (div_le_div_iff₀ hdxdyPos hdeltaSq).2
        exact mul_le_mul
          (mul_le_mul hnumY hdenDiff' (abs_nonneg _) hN)
          hdenLower hdeltaSq.le
          (mul_nonneg hN (mul_nonneg hG hd))
      _ = (N * G / delta ^ 2) * d := by ring
  have hidentity :
      nx / dx - ny / dy =
        (nx - ny) / dx + ny * (dy - dx) / (dx * dy) := by
    field_simp [ne_of_gt hdxPos, ne_of_gt hdyPos]
    ring
  rw [hidentity]
  calc
    |(nx - ny) / dx + ny * (dy - dx) / (dx * dy)| ≤
        |(nx - ny) / dx| + |ny * (dy - dx) / (dx * dy)| :=
      abs_add_le _ _
    _ ≤ (L / delta) * d + (N * G / delta ^ 2) * d :=
      add_le_add hfirst hsecond
    _ = (L / delta + N * G / delta ^ 2) * d := by ring

/-- A common positive Gram floor controls both free quadratic coefficients
with one explicit constant in the fixed product norm. -/
theorem P_coeffPair_sub_norm_le_of_gram_floor
    (lambda : Fin 4 → ℝ) (x y : Weights) {delta : ℝ}
    (hdelta : 0 < delta)
    (hxdet : delta ≤ weightedMomentGramDet lambda x)
    (hydet : delta ≤ weightedMomentGramDet lambda y) :
    ‖(P lambda x).coeffPair - (P lambda y).coeffPair‖ ≤
      coefficientPairLipschitzConstant lambda delta *
        ‖weightVector x - weightVector y‖ := by
  let d := ‖weightVector x - weightVector y‖
  let L := coefficientNumeratorLipschitzConstant lambda
  let N := coefficientNumeratorBound lambda
  let G := gramLipschitzConstant lambda
  have hcommon
      (nx ny : ℝ) (hnumDiff : |nx - ny| ≤ L * d)
      (hnumY : |ny| ≤ N) :
      |nx / weightedMomentGramDet lambda x -
          ny / weightedMomentGramDet lambda y| ≤
        coefficientPairLipschitzConstant lambda delta * d := by
    simpa [coefficientPairLipschitzConstant, L, N, G] using
      abs_div_sub_div_le_of_floor hdelta hxdet hydet
        (coefficientNumeratorLipschitzConstant_nonneg lambda)
        (coefficientNumeratorBound_nonneg lambda)
        (gramLipschitzConstant_nonneg lambda) (norm_nonneg _)
        hnumDiff hnumY (abs_weightedMomentGramDet_sub_le lambda x y)
  have hlinear :
      |(P lambda x).linearCoeff - (P lambda y).linearCoeff| ≤
        coefficientPairLipschitzConstant lambda delta * d := by
    rw [P_linearCoeff_eq_linearNumerator_div,
      P_linearCoeff_eq_linearNumerator_div]
    exact hcommon _ _ (by simpa [L, d] using
      (abs_linearNumerator_sub_le lambda x y)) (by simpa [N] using
        (abs_linearNumerator_le lambda y))
  have hconstant :
      |(P lambda x).constantCoeff - (P lambda y).constantCoeff| ≤
        coefficientPairLipschitzConstant lambda delta * d := by
    rw [P_constantCoeff_eq_constantNumerator_div,
      P_constantCoeff_eq_constantNumerator_div]
    exact hcommon _ _ (by simpa [L, d] using
      (abs_constantNumerator_sub_le lambda x y)) (by simpa [N] using
        (abs_constantNumerator_le lambda y))
  change max
    |(P lambda x).linearCoeff - (P lambda y).linearCoeff|
    |(P lambda x).constantCoeff - (P lambda y).constantCoeff| ≤
      coefficientPairLipschitzConstant lambda delta *
        ‖weightVector x - weightVector y‖
  simpa [d] using max_le hlinear hconstant

/-- A concrete bound for every node magnitude. -/
def nodeRadius (lambda : Fin 4 → ℝ) : ℝ :=
  ∑ i, |lambda i|

theorem nodeRadius_nonneg (lambda : Fin 4 → ℝ) : 0 ≤ nodeRadius lambda := by
  exact Finset.sum_nonneg fun i hi ↦ abs_nonneg _

theorem abs_node_le_nodeRadius (lambda : Fin 4 → ℝ) (i : Fin 4) :
    |lambda i| ≤ nodeRadius lambda := by
  rw [nodeRadius]
  exact Finset.single_le_sum (fun j _ ↦ abs_nonneg (lambda j))
    (Finset.mem_univ i)

theorem abs_linearCoeff_le_coeffPair_norm_fourNode (p : MonicQuadratic) :
    |p.linearCoeff| ≤ ‖p.coeffPair‖ := by
  rw [MonicQuadratic.coeffPair, Prod.norm_def, Real.norm_eq_abs,
    Real.norm_eq_abs]
  exact le_max_left _ _

theorem abs_constantCoeff_le_coeffPair_norm_fourNode (p : MonicQuadratic) :
    |p.constantCoeff| ≤ ‖p.coeffPair‖ := by
  rw [MonicQuadratic.coeffPair, Prod.norm_def, Real.norm_eq_abs,
    Real.norm_eq_abs]
  exact le_max_right _ _

/-- Uniform absolute bound for the free coefficients under a Gram floor. -/
def coefficientFloorBound (lambda : Fin 4 → ℝ) (delta : ℝ) : ℝ :=
  coefficientNumeratorBound lambda / delta

/-- Uniform nodal bound for the monic quadratic under a Gram floor. -/
def polynomialEvalFloorBound (lambda : Fin 4 → ℝ) (delta : ℝ) : ℝ :=
  nodeRadius lambda ^ 2 +
    coefficientFloorBound lambda delta * nodeRadius lambda +
    coefficientFloorBound lambda delta

theorem coefficientFloorBound_nonneg
    (lambda : Fin 4 → ℝ) {delta : ℝ} (hdelta : 0 < delta) :
    0 ≤ coefficientFloorBound lambda delta :=
  div_nonneg (coefficientNumeratorBound_nonneg lambda) hdelta.le

theorem polynomialEvalFloorBound_nonneg
    (lambda : Fin 4 → ℝ) {delta : ℝ} (hdelta : 0 < delta) :
    0 ≤ polynomialEvalFloorBound lambda delta := by
  dsimp only [polynomialEvalFloorBound]
  exact add_nonneg
    (add_nonneg (sq_nonneg _)
      (mul_nonneg (coefficientFloorBound_nonneg lambda hdelta)
        (nodeRadius_nonneg lambda)))
    (coefficientFloorBound_nonneg lambda hdelta)

/-- Gram coercivity gives a uniform explicit bound for every nodal factor
value. -/
theorem abs_P_eval_le_of_gram_floor
    (lambda : Fin 4 → ℝ) (x : Weights) (i : Fin 4) {delta : ℝ}
    (hdelta : 0 < delta)
    (hdet : delta ≤ weightedMomentGramDet lambda x) :
    |(P lambda x).toPolynomial.eval (lambda i)| ≤
      polynomialEvalFloorBound lambda delta := by
  let M := coefficientFloorBound lambda delta
  let R := nodeRadius lambda
  have hp : ‖(P lambda x).coeffPair‖ ≤ M := by
    simpa [M, coefficientFloorBound] using
      P_coeffPair_norm_le_of_gram_floor lambda x hdelta hdet
  have ha : |(P lambda x).linearCoeff| ≤ M :=
    (abs_linearCoeff_le_coeffPair_norm_fourNode _).trans hp
  have hb : |(P lambda x).constantCoeff| ≤ M :=
    (abs_constantCoeff_le_coeffPair_norm_fourNode _).trans hp
  have hnode : |lambda i| ≤ R := abs_node_le_nodeRadius lambda i
  have hR : 0 ≤ R := nodeRadius_nonneg lambda
  have hM : 0 ≤ M := coefficientFloorBound_nonneg lambda hdelta
  rw [MonicQuadratic.eval]
  calc
    |lambda i ^ 2 + (P lambda x).linearCoeff * lambda i +
        (P lambda x).constantCoeff| ≤
      |lambda i ^ 2| + |(P lambda x).linearCoeff * lambda i| +
        |(P lambda x).constantCoeff| := by
      exact (abs_add_le _ _).trans
        (add_le_add (abs_add_le _ _) le_rfl)
    _ = |lambda i| ^ 2 +
        |(P lambda x).linearCoeff| * |lambda i| +
        |(P lambda x).constantCoeff| := by rw [abs_pow, abs_mul]
    _ ≤ R ^ 2 + M * R + M := by
      exact add_le_add
        (add_le_add
          (by simpa [pow_two] using
            mul_self_le_mul_self (abs_nonneg (lambda i)) hnode)
          (mul_le_mul ha hnode (abs_nonneg _) hM)) hb
    _ = polynomialEvalFloorBound lambda delta := by
      rfl

/-- Nodal evaluation changes Lipschitz-continuously with the free coefficient
pair, using the same concrete product norm. -/
theorem abs_P_eval_sub_le_of_gram_floor
    (lambda : Fin 4 → ℝ) (x y : Weights) (i : Fin 4) {delta : ℝ}
    (hdelta : 0 < delta)
    (hxdet : delta ≤ weightedMomentGramDet lambda x)
    (hydet : delta ≤ weightedMomentGramDet lambda y) :
    |(P lambda x).toPolynomial.eval (lambda i) -
        (P lambda y).toPolynomial.eval (lambda i)| ≤
      (nodeRadius lambda + 1) *
        coefficientPairLipschitzConstant lambda delta *
          ‖weightVector x - weightVector y‖ := by
  let Cpair := coefficientPairLipschitzConstant lambda delta
  let d := ‖weightVector x - weightVector y‖
  have hpair :
      ‖(P lambda x).coeffPair - (P lambda y).coeffPair‖ ≤ Cpair * d := by
    simpa [Cpair, d] using
      P_coeffPair_sub_norm_le_of_gram_floor lambda x y hdelta hxdet hydet
  have ha : |(P lambda x).linearCoeff - (P lambda y).linearCoeff| ≤
      Cpair * d := by
    calc
      _ ≤ ‖(P lambda x).coeffPair - (P lambda y).coeffPair‖ := by
        change _ ≤ max
          |(P lambda x).linearCoeff - (P lambda y).linearCoeff|
          |(P lambda x).constantCoeff - (P lambda y).constantCoeff|
        exact le_max_left _ _
      _ ≤ Cpair * d := hpair
  have hb : |(P lambda x).constantCoeff - (P lambda y).constantCoeff| ≤
      Cpair * d := by
    calc
      _ ≤ ‖(P lambda x).coeffPair - (P lambda y).coeffPair‖ := by
        change _ ≤ max
          |(P lambda x).linearCoeff - (P lambda y).linearCoeff|
          |(P lambda x).constantCoeff - (P lambda y).constantCoeff|
        exact le_max_right _ _
      _ ≤ Cpair * d := hpair
  rw [MonicQuadratic.eval, MonicQuadratic.eval]
  calc
    |(lambda i ^ 2 + (P lambda x).linearCoeff * lambda i +
          (P lambda x).constantCoeff) -
        (lambda i ^ 2 + (P lambda y).linearCoeff * lambda i +
          (P lambda y).constantCoeff)| =
      |((P lambda x).linearCoeff - (P lambda y).linearCoeff) * lambda i +
        ((P lambda x).constantCoeff - (P lambda y).constantCoeff)| := by
          congr 1
          ring
    _ ≤ |(P lambda x).linearCoeff - (P lambda y).linearCoeff| *
          |lambda i| +
        |(P lambda x).constantCoeff - (P lambda y).constantCoeff| := by
      simpa [abs_mul] using
        (abs_add_le
          (((P lambda x).linearCoeff - (P lambda y).linearCoeff) * lambda i)
          ((P lambda x).constantCoeff - (P lambda y).constantCoeff))
    _ ≤ (Cpair * d) * nodeRadius lambda + Cpair * d := by
      exact add_le_add
        (mul_le_mul ha (abs_node_le_nodeRadius lambda i) (abs_nonneg _)
          (mul_nonneg (coefficientPairLipschitzConstant_nonneg lambda hdelta)
            (norm_nonneg _))) hb
    _ = (nodeRadius lambda + 1) *
        coefficientPairLipschitzConstant lambda delta *
          ‖weightVector x - weightVector y‖ := by
      dsimp only [Cpair, d]
      ring

/-- The unnormalized squared-residual contribution at one node. -/
def residualTerm (lambda : Fin 4 → ℝ) (x : Weights) (i : Fin 4) : ℝ :=
  x i * (P lambda x).toPolynomial.eval (lambda i) ^ 2

theorem height_eq_sum_residualTerm
    (lambda : Fin 4 → ℝ) (x : Weights) :
    H lambda x = ∑ i, residualTerm lambda x i := by
  change weightedPolyInner lambda x (P lambda x).toPolynomial
    (P lambda x).toPolynomial = ∑ i, residualTerm lambda x i
  rw [weightedPolyInner]
  apply Finset.sum_congr rfl
  intro i hi
  rw [residualTerm]
  ring

/-- Lipschitz constant for one unnormalized squared-residual contribution. -/
def residualTermLipschitzConstant
    (lambda : Fin 4 → ℝ) (delta : ℝ) : ℝ :=
  polynomialEvalFloorBound lambda delta ^ 2 +
    2 * polynomialEvalFloorBound lambda delta *
      ((nodeRadius lambda + 1) *
        coefficientPairLipschitzConstant lambda delta)

theorem residualTermLipschitzConstant_nonneg
    (lambda : Fin 4 → ℝ) {delta : ℝ} (hdelta : 0 < delta) :
    0 ≤ residualTermLipschitzConstant lambda delta := by
  dsimp only [residualTermLipschitzConstant]
  have hS := polynomialEvalFloorBound_nonneg lambda hdelta
  have hR : 0 ≤ nodeRadius lambda + 1 :=
    add_nonneg (nodeRadius_nonneg lambda) (by norm_num)
  have hC := coefficientPairLipschitzConstant_nonneg lambda hdelta
  apply add_nonneg (sq_nonneg _)
  exact mul_nonneg (mul_nonneg (by norm_num) hS) (mul_nonneg hR hC)

theorem abs_residualTerm_le_of_gram_floor
    (lambda : Fin 4 → ℝ) (x : Weights) (i : Fin 4) {delta : ℝ}
    (hdelta : 0 < delta)
    (hdet : delta ≤ weightedMomentGramDet lambda x) :
    |residualTerm lambda x i| ≤
      polynomialEvalFloorBound lambda delta ^ 2 := by
  rw [residualTerm, abs_mul, abs_pow, abs_of_nonneg (x.nonneg i)]
  have hx := weight_le_one_continuity x i
  have hp := abs_P_eval_le_of_gram_floor lambda x i hdelta hdet
  have hS := polynomialEvalFloorBound_nonneg lambda hdelta
  have hsq : |(P lambda x).toPolynomial.eval (lambda i)| ^ 2 ≤
      polynomialEvalFloorBound lambda delta ^ 2 := by
    nlinarith [abs_nonneg ((P lambda x).toPolynomial.eval (lambda i))]
  exact (mul_le_mul hx hsq (sq_nonneg _) (by norm_num)).trans_eq (one_mul _)

theorem abs_residualTerm_sub_le_of_gram_floor
    (lambda : Fin 4 → ℝ) (x y : Weights) (i : Fin 4) {delta : ℝ}
    (hdelta : 0 < delta)
    (hxdet : delta ≤ weightedMomentGramDet lambda x)
    (hydet : delta ≤ weightedMomentGramDet lambda y) :
    |residualTerm lambda x i - residualTerm lambda y i| ≤
      residualTermLipschitzConstant lambda delta *
        ‖weightVector x - weightVector y‖ := by
  let S := polynomialEvalFloorBound lambda delta
  let Epair := (nodeRadius lambda + 1) *
    coefficientPairLipschitzConstant lambda delta
  let d := ‖weightVector x - weightVector y‖
  have hS : 0 ≤ S := polynomialEvalFloorBound_nonneg lambda hdelta
  have hpx : |(P lambda x).toPolynomial.eval (lambda i)| ≤ S := by
    simpa [S] using abs_P_eval_le_of_gram_floor lambda x i hdelta hxdet
  have hpy : |(P lambda y).toPolynomial.eval (lambda i)| ≤ S := by
    simpa [S] using abs_P_eval_le_of_gram_floor lambda y i hdelta hydet
  have hpdiff :
      |(P lambda x).toPolynomial.eval (lambda i) -
        (P lambda y).toPolynomial.eval (lambda i)| ≤ Epair * d := by
    simpa [Epair, d] using
      abs_P_eval_sub_le_of_gram_floor lambda x y i hdelta hxdet hydet
  have hsq :
      |(P lambda x).toPolynomial.eval (lambda i) ^ 2 -
        (P lambda y).toPolynomial.eval (lambda i) ^ 2| ≤
        2 * S * (Epair * d) :=
    abs_sq_sub_sq_le _ _ S (Epair * d) hpx hpy hpdiff hS
  have hprod := abs_mul_sub_mul_le
    (x i) ((P lambda x).toPolynomial.eval (lambda i) ^ 2)
    (y i) ((P lambda y).toPolynomial.eval (lambda i) ^ 2)
  rw [residualTerm, residualTerm]
  have hpySq : |(P lambda y).toPolynomial.eval (lambda i) ^ 2| ≤ S ^ 2 := by
    rw [abs_pow]
    nlinarith [abs_nonneg ((P lambda y).toPolynomial.eval (lambda i))]
  have hcoord : |x i - y i| ≤ d := by
    simpa [d] using (abs_weightVector_sub_apply_le
      (weightVector x) (weightVector y) i)
  calc
    _ ≤ |x i| *
          |(P lambda x).toPolynomial.eval (lambda i) ^ 2 -
            (P lambda y).toPolynomial.eval (lambda i) ^ 2| +
        |(P lambda y).toPolynomial.eval (lambda i) ^ 2| * |x i - y i| :=
      hprod
    _ ≤ 1 * (2 * S * (Epair * d)) + S ^ 2 * d := by
      exact add_le_add
        (mul_le_mul (by simpa [abs_of_nonneg (x.nonneg i)] using weight_le_one_continuity x i)
          hsq (abs_nonneg _) (by norm_num))
        (mul_le_mul hpySq hcoord (abs_nonneg _) (sq_nonneg _))
    _ = residualTermLipschitzConstant lambda delta *
        ‖weightVector x - weightVector y‖ := by
      dsimp only [residualTermLipschitzConstant, S, Epair, d]
      ring

/-- Explicit height Lipschitz constant under a common Gram floor. -/
def heightLipschitzConstant (lambda : Fin 4 → ℝ) (delta : ℝ) : ℝ :=
  4 * residualTermLipschitzConstant lambda delta

theorem heightLipschitzConstant_nonneg
    (lambda : Fin 4 → ℝ) {delta : ℝ} (hdelta : 0 < delta) :
    0 ≤ heightLipschitzConstant lambda delta :=
  mul_nonneg (by norm_num) (residualTermLipschitzConstant_nonneg lambda hdelta)

theorem abs_height_sub_le_of_gram_floor
    (lambda : Fin 4 → ℝ) (x y : Weights) {delta : ℝ}
    (hdelta : 0 < delta)
    (hxdet : delta ≤ weightedMomentGramDet lambda x)
    (hydet : delta ≤ weightedMomentGramDet lambda y) :
    |H lambda x - H lambda y| ≤
      heightLipschitzConstant lambda delta *
        ‖weightVector x - weightVector y‖ := by
  rw [height_eq_sum_residualTerm, height_eq_sum_residualTerm,
    ← Finset.sum_sub_distrib]
  calc
    |∑ i, (residualTerm lambda x i - residualTerm lambda y i)| ≤
        ∑ i, |residualTerm lambda x i - residualTerm lambda y i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin 4, residualTermLipschitzConstant lambda delta *
        ‖weightVector x - weightVector y‖ := by
      apply Finset.sum_le_sum
      intro i hi
      exact abs_residualTerm_sub_le_of_gram_floor lambda x y i
        hdelta hxdet hydet
    _ = heightLipschitzConstant lambda delta *
        ‖weightVector x - weightVector y‖ := by
      simp [heightLipschitzConstant]
      ring

/-- Explicit sup-norm Lipschitz constant for the normalized update under
common Gram and height floors. -/
def nextWeightLipschitzConstant
    (lambda : Fin 4 → ℝ) (delta eta : ℝ) : ℝ :=
  residualTermLipschitzConstant lambda delta / eta +
    polynomialEvalFloorBound lambda delta ^ 2 *
      heightLipschitzConstant lambda delta / eta ^ 2

theorem nextWeightLipschitzConstant_nonneg
    (lambda : Fin 4 → ℝ) {delta eta : ℝ}
    (hdelta : 0 < delta) (heta : 0 < eta) :
    0 ≤ nextWeightLipschitzConstant lambda delta eta := by
  dsimp only [nextWeightLipschitzConstant]
  exact add_nonneg
    (div_nonneg (residualTermLipschitzConstant_nonneg lambda hdelta) heta.le)
    (div_nonneg
      (mul_nonneg (sq_nonneg _)
        (heightLipschitzConstant_nonneg lambda hdelta)) (sq_nonneg _))

/-- Common Gram and height floors quantitatively control the exact normalized
four-node update in the coordinate sup norm. -/
theorem T_weightVector_sub_norm_le_of_floors
    {lambda : Fin 4 → ℝ} (hlambda : Function.Injective lambda)
    (x y : Weights) {delta eta : ℝ}
    (hdelta : 0 < delta) (heta : 0 < eta)
    (hxdet : delta ≤ weightedMomentGramDet lambda x)
    (hydet : delta ≤ weightedMomentGramDet lambda y)
    (hxheight : eta ≤ H lambda x) (hyheight : eta ≤ H lambda y) :
    ‖weightVector (T lambda hlambda x) -
        weightVector (T lambda hlambda y)‖ ≤
      nextWeightLipschitzConstant lambda delta eta *
        ‖weightVector x - weightVector y‖ := by
  let d := ‖weightVector x - weightVector y‖
  let L := residualTermLipschitzConstant lambda delta
  let N := polynomialEvalFloorBound lambda delta ^ 2
  let G := heightLipschitzConstant lambda delta
  let C := nextWeightLipschitzConstant lambda delta eta
  have hcomponent (i : Fin 4) :
      |T lambda hlambda x i - T lambda hlambda y i| ≤ C * d := by
    rw [T_weight, T_weight]
    change |residualTerm lambda x i / H lambda x -
      residualTerm lambda y i / H lambda y| ≤ C * d
    simpa [C, nextWeightLipschitzConstant, L, N, G, d] using
      abs_div_sub_div_le_of_floor heta hxheight hyheight
        (residualTermLipschitzConstant_nonneg lambda hdelta)
        (sq_nonneg _) (heightLipschitzConstant_nonneg lambda hdelta)
        (norm_nonneg _)
        (abs_residualTerm_sub_le_of_gram_floor lambda x y i
          hdelta hxdet hydet)
        (abs_residualTerm_le_of_gram_floor lambda y i hdelta hydet)
        (abs_height_sub_le_of_gram_floor lambda x y hdelta hxdet hydet)
  have hC : 0 ≤ C := nextWeightLipschitzConstant_nonneg lambda hdelta heta
  rw [pi_norm_le_iff_of_nonneg (mul_nonneg hC (norm_nonneg _))]
  intro i
  simpa [Real.norm_eq_abs, C, d] using hcomponent i

/-- Lipschitz constant for the numerator `x_0 P_x(lambda_0)` in `rho`. -/
def rhoNumeratorLipschitzConstant
    (lambda : Fin 4 → ℝ) (delta : ℝ) : ℝ :=
  polynomialEvalFloorBound lambda delta +
    (nodeRadius lambda + 1) * coefficientPairLipschitzConstant lambda delta

/-- Explicit Lipschitz constant for `rho` under common Gram and height floors. -/
def rhoLipschitzConstant
    (lambda : Fin 4 → ℝ) (delta eta : ℝ) : ℝ :=
  |E lambda 0| *
    (rhoNumeratorLipschitzConstant lambda delta / eta +
      polynomialEvalFloorBound lambda delta *
        heightLipschitzConstant lambda delta / eta ^ 2)

theorem rhoLipschitzConstant_nonneg
    (lambda : Fin 4 → ℝ) {delta eta : ℝ}
    (hdelta : 0 < delta) (heta : 0 < eta) :
    0 ≤ rhoLipschitzConstant lambda delta eta := by
  dsimp only [rhoLipschitzConstant, rhoNumeratorLipschitzConstant]
  have hS := polynomialEvalFloorBound_nonneg lambda hdelta
  have hH := heightLipschitzConstant_nonneg lambda hdelta
  have hC := coefficientPairLipschitzConstant_nonneg lambda hdelta
  have hR : 0 ≤ nodeRadius lambda + 1 :=
    add_nonneg (nodeRadius_nonneg lambda) (by norm_num)
  exact mul_nonneg (abs_nonneg _)
    (add_nonneg
      (div_nonneg (add_nonneg hS (mul_nonneg hR hC)) heta.le)
      (div_nonneg (mul_nonneg hS hH) (sq_nonneg _)))

/-- Common Gram and height floors quantitatively control the barycentric
parameter `rho`. -/
theorem abs_rho_sub_le_of_floors
    {lambda : Fin 4 → ℝ} (x y : Weights) {delta eta : ℝ}
    (hdelta : 0 < delta) (heta : 0 < eta)
    (hxdet : delta ≤ weightedMomentGramDet lambda x)
    (hydet : delta ≤ weightedMomentGramDet lambda y)
    (hxheight : eta ≤ H lambda x) (hyheight : eta ≤ H lambda y) :
    |rho lambda x - rho lambda y| ≤
      rhoLipschitzConstant lambda delta eta *
        ‖weightVector x - weightVector y‖ := by
  let d := ‖weightVector x - weightVector y‖
  let S := polynomialEvalFloorBound lambda delta
  let L := rhoNumeratorLipschitzConstant lambda delta
  let G := heightLipschitzConstant lambda delta
  let nx := x 0 * (P lambda x).toPolynomial.eval (lambda 0)
  let ny := y 0 * (P lambda y).toPolynomial.eval (lambda 0)
  have hnumY : |ny| ≤ S := by
    dsimp only [ny]
    rw [abs_mul, abs_of_nonneg (y.nonneg 0)]
    exact (mul_le_mul (weight_le_one_continuity y 0)
      (abs_P_eval_le_of_gram_floor lambda y 0 hdelta hydet)
      (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
  have hnumDiff : |nx - ny| ≤ L * d := by
    dsimp only [nx, ny]
    calc
      _ ≤ |x 0| *
            |(P lambda x).toPolynomial.eval (lambda 0) -
              (P lambda y).toPolynomial.eval (lambda 0)| +
          |(P lambda y).toPolynomial.eval (lambda 0)| * |x 0 - y 0| :=
        abs_mul_sub_mul_le _ _ _ _
      _ ≤ 1 * (((nodeRadius lambda + 1) *
              coefficientPairLipschitzConstant lambda delta) * d) +
            S * d := by
        exact add_le_add
          (mul_le_mul
            (by simpa [abs_of_nonneg (x.nonneg 0)] using weight_le_one_continuity x 0)
            (by simpa [d] using (abs_P_eval_sub_le_of_gram_floor
              lambda x y 0 hdelta hxdet hydet))
            (abs_nonneg _) (by norm_num))
          (mul_le_mul
            (by simpa [S] using (abs_P_eval_le_of_gram_floor
              lambda y 0 hdelta hydet))
            (by simpa [d] using (abs_weightVector_sub_apply_le
              (weightVector x) (weightVector y) 0))
            (abs_nonneg _) (polynomialEvalFloorBound_nonneg lambda hdelta))
      _ = L * d := by
        dsimp only [L, S, rhoNumeratorLipschitzConstant]
        ring
  have hquot : |nx / H lambda x - ny / H lambda y| ≤
      (L / eta + S * G / eta ^ 2) * d := by
    exact abs_div_sub_div_le_of_floor heta hxheight hyheight
      (by
        dsimp only [L, rhoNumeratorLipschitzConstant]
        exact add_nonneg (polynomialEvalFloorBound_nonneg lambda hdelta)
          (mul_nonneg
            (add_nonneg (nodeRadius_nonneg lambda) (by norm_num))
            (coefficientPairLipschitzConstant_nonneg lambda hdelta)))
      (polynomialEvalFloorBound_nonneg lambda hdelta)
      (heightLipschitzConstant_nonneg lambda hdelta) (norm_nonneg _)
      hnumDiff hnumY
      (abs_height_sub_le_of_gram_floor lambda x y hdelta hxdet hydet)
  rw [rho, rho]
  calc
    |lambda 0 - E lambda 0 *
          (x 0 * (P lambda x).toPolynomial.eval (lambda 0)) / H lambda x -
        (lambda 0 - E lambda 0 *
          (y 0 * (P lambda y).toPolynomial.eval (lambda 0)) / H lambda y)| =
        |E lambda 0| * |nx / H lambda x - ny / H lambda y| := by
      dsimp only [nx, ny]
      rw [← abs_neg (E lambda 0), ← abs_mul]
      congr 1
      ring
    _ ≤ |E lambda 0| * ((L / eta + S * G / eta ^ 2) * d) :=
      mul_le_mul_of_nonneg_left hquot (abs_nonneg _)
    _ = rhoLipschitzConstant lambda delta eta *
        ‖weightVector x - weightVector y‖ := by
      dsimp only [rhoLipschitzConstant, L, S, G, d]
      rw [rhoNumeratorLipschitzConstant]
      ring

/-- The interpolation coefficient is the sum of the two consecutive linear
coefficients, minus the fixed cubic coefficient of the nodal quartic. -/
theorem alpha_eq_linearCoeff_add
    {lambda : Fin 4 → ℝ} (hlambda : Function.Injective lambda)
    (x : Weights) :
    alpha lambda hlambda x =
      (P lambda x).linearCoeff +
        (P lambda (T lambda hlambda x)).linearCoeff -
          (nodalQuartic lambda).coeff 3 := by
  have h := alphaVector_weightVector lambda hlambda x
  rw [alphaVector] at h
  have hnext : nextWeightVector lambda (weightVector x) =
      weightVector (T lambda hlambda x) := by
    funext i
    exact nextWeightVector_weightVector lambda hlambda x i
  rw [orthogonalPolynomialVector_weightVector, hnext,
    orthogonalPolynomialVector_weightVector] at h
  exact h.symm

/-- Explicit Lipschitz constant for the interpolation coefficient when the
input and updated states have uniform Gram floors. -/
def alphaLipschitzConstant
    (lambda : Fin 4 → ℝ) (delta eta deltaNext : ℝ) : ℝ :=
  coefficientPairLipschitzConstant lambda delta +
    coefficientPairLipschitzConstant lambda deltaNext *
      nextWeightLipschitzConstant lambda delta eta

theorem alphaLipschitzConstant_nonneg
    (lambda : Fin 4 → ℝ) {delta eta deltaNext : ℝ}
    (hdelta : 0 < delta) (heta : 0 < eta) (hdeltaNext : 0 < deltaNext) :
    0 ≤ alphaLipschitzConstant lambda delta eta deltaNext := by
  exact add_nonneg
    (coefficientPairLipschitzConstant_nonneg lambda hdelta)
    (mul_nonneg
      (coefficientPairLipschitzConstant_nonneg lambda hdeltaNext)
      (nextWeightLipschitzConstant_nonneg lambda hdelta heta))

/-- Quantitative continuity of the interpolation coefficient. -/
theorem abs_alpha_sub_le_of_floors
    {lambda : Fin 4 → ℝ} (hlambda : Function.Injective lambda)
    (x y : Weights) {delta eta deltaNext : ℝ}
    (hdelta : 0 < delta) (heta : 0 < eta) (hdeltaNext : 0 < deltaNext)
    (hxdet : delta ≤ weightedMomentGramDet lambda x)
    (hydet : delta ≤ weightedMomentGramDet lambda y)
    (hxheight : eta ≤ H lambda x) (hyheight : eta ≤ H lambda y)
    (hxdetNext : deltaNext ≤
      weightedMomentGramDet lambda (T lambda hlambda x))
    (hydetNext : deltaNext ≤
      weightedMomentGramDet lambda (T lambda hlambda y)) :
    |alpha lambda hlambda x - alpha lambda hlambda y| ≤
      alphaLipschitzConstant lambda delta eta deltaNext *
        ‖weightVector x - weightVector y‖ := by
  let d := ‖weightVector x - weightVector y‖
  let C0 := coefficientPairLipschitzConstant lambda delta
  let C1 := coefficientPairLipschitzConstant lambda deltaNext
  let CT := nextWeightLipschitzConstant lambda delta eta
  have hfirst :
      |(P lambda x).linearCoeff - (P lambda y).linearCoeff| ≤ C0 * d := by
    calc
      _ ≤ ‖(P lambda x).coeffPair - (P lambda y).coeffPair‖ := by
        change _ ≤ max
          |(P lambda x).linearCoeff - (P lambda y).linearCoeff|
          |(P lambda x).constantCoeff - (P lambda y).constantCoeff|
        exact le_max_left _ _
      _ ≤ C0 * d := by
        simpa [C0, d] using
          P_coeffPair_sub_norm_le_of_gram_floor lambda x y hdelta hxdet hydet
  have hT :
      ‖weightVector (T lambda hlambda x) -
          weightVector (T lambda hlambda y)‖ ≤ CT * d := by
    simpa [CT, d] using T_weightVector_sub_norm_le_of_floors hlambda x y
      hdelta heta hxdet hydet hxheight hyheight
  have hsecond :
      |(P lambda (T lambda hlambda x)).linearCoeff -
        (P lambda (T lambda hlambda y)).linearCoeff| ≤ C1 * (CT * d) := by
    calc
      _ ≤ ‖(P lambda (T lambda hlambda x)).coeffPair -
          (P lambda (T lambda hlambda y)).coeffPair‖ := by
        change _ ≤ max
          |(P lambda (T lambda hlambda x)).linearCoeff -
            (P lambda (T lambda hlambda y)).linearCoeff|
          |(P lambda (T lambda hlambda x)).constantCoeff -
            (P lambda (T lambda hlambda y)).constantCoeff|
        exact le_max_left _ _
      _ ≤ C1 * ‖weightVector (T lambda hlambda x) -
          weightVector (T lambda hlambda y)‖ := by
        simpa [C1] using P_coeffPair_sub_norm_le_of_gram_floor lambda
          (T lambda hlambda x) (T lambda hlambda y) hdeltaNext
          hxdetNext hydetNext
      _ ≤ C1 * (CT * d) := mul_le_mul_of_nonneg_left hT
        (coefficientPairLipschitzConstant_nonneg lambda hdeltaNext)
  rw [alpha_eq_linearCoeff_add hlambda,
    alpha_eq_linearCoeff_add hlambda]
  calc
    |((P lambda x).linearCoeff +
          (P lambda (T lambda hlambda x)).linearCoeff -
          (nodalQuartic lambda).coeff 3) -
        ((P lambda y).linearCoeff +
          (P lambda (T lambda hlambda y)).linearCoeff -
          (nodalQuartic lambda).coeff 3)| =
      |((P lambda x).linearCoeff - (P lambda y).linearCoeff) +
        ((P lambda (T lambda hlambda x)).linearCoeff -
          (P lambda (T lambda hlambda y)).linearCoeff)| := by
            congr 1
            ring
    _ ≤ |(P lambda x).linearCoeff - (P lambda y).linearCoeff| +
        |(P lambda (T lambda hlambda x)).linearCoeff -
          (P lambda (T lambda hlambda y)).linearCoeff| := abs_add_le _ _
    _ ≤ C0 * d + C1 * (CT * d) := add_le_add hfirst hsecond
    _ = alphaLipschitzConstant lambda delta eta deltaNext *
        ‖weightVector x - weightVector y‖ := by
      dsimp only [alphaLipschitzConstant, C0, C1, CT, d]
      ring

/-- The finite tuple of rational data occurring in one interpolation
identity.  Its product topology is entirely concrete. -/
def interpolationData
    (lambda : Fin 4 → ℝ) (hlambda : Function.Injective lambda)
    (x : Weights) : (ℝ × ℝ) × (ℝ × ℝ) × ℝ × ℝ × ℝ :=
  ((P lambda x).coeffPair,
    (P lambda (T lambda hlambda x)).coeffPair,
    H lambda (T lambda hlambda x), rho lambda x, alpha lambda hlambda x)

/-! ## Continuity on simplex states via their concrete coordinates -/

theorem tendsto_weightedMoment_of_tendsto_weightVector
    {I : Type*} {l : Filter I} (lambda : Fin 4 → ℝ)
    (u : I → Weights) (x : Weights)
    (hu : Tendsto (fun a ↦ weightVector (u a)) l
      (nhds (weightVector x))) (k : ℕ) :
    Tendsto (fun a ↦ weightedMoment lambda (u a) k) l
      (nhds (weightedMoment lambda x k)) := by
  simpa only [Function.comp_def, weightedMomentVector_weightVector] using
    ((continuous_weightedMomentVector lambda k).tendsto
      (weightVector x)).comp hu

theorem tendsto_weightedMomentGramDet_of_tendsto_weightVector
    {I : Type*} {l : Filter I} (lambda : Fin 4 → ℝ)
    (u : I → Weights) (x : Weights)
    (hu : Tendsto (fun a ↦ weightVector (u a)) l
      (nhds (weightVector x))) :
    Tendsto (fun a ↦ weightedMomentGramDet lambda (u a)) l
      (nhds (weightedMomentGramDet lambda x)) := by
  simpa only [Function.comp_def,
    weightedMomentGramDetVector_weightVector] using
    ((continuous_weightedMomentGramDetVector lambda).tendsto
      (weightVector x)).comp hu

theorem tendsto_P_coeffPair_of_tendsto_weightVector
    {I : Type*} {l : Filter I} {lambda : Fin 4 → ℝ}
    (hlambda : Function.Injective lambda)
    (u : I → Weights) (x : Weights)
    (hu : Tendsto (fun a ↦ weightVector (u a)) l
      (nhds (weightVector x))) :
    Tendsto (fun a ↦ (P lambda (u a)).coeffPair) l
      (nhds (P lambda x).coeffPair) := by
  have hdet : weightedMomentGramDetVector lambda (weightVector x) ≠ 0 := by
    simpa using ne_of_gt (weightedMomentGramDet_pos hlambda x)
  have hcont : Tendsto
      (fun w : WeightVector ↦ (orthogonalPolynomialVector lambda w).coeffPair)
      (nhds (weightVector x))
      (nhds (orthogonalPolynomialVector lambda (weightVector x)).coeffPair) :=
    continuousAt_orthogonalPolynomialVector_coeffPair lambda
      (weightVector x) hdet
  simpa only [Function.comp_def,
    orthogonalPolynomialVector_weightVector] using
    hcont.comp hu

theorem tendsto_H_of_tendsto_weightVector
    {I : Type*} {l : Filter I} {lambda : Fin 4 → ℝ}
    (hlambda : Function.Injective lambda)
    (u : I → Weights) (x : Weights)
    (hu : Tendsto (fun a ↦ weightVector (u a)) l
      (nhds (weightVector x))) :
    Tendsto (fun a ↦ H lambda (u a)) l (nhds (H lambda x)) := by
  have hdet : weightedMomentGramDetVector lambda (weightVector x) ≠ 0 := by
    simpa using ne_of_gt (weightedMomentGramDet_pos hlambda x)
  have hcont : Tendsto (heightVector lambda)
      (nhds (weightVector x))
      (nhds (heightVector lambda (weightVector x))) :=
    continuousAt_heightVector lambda (weightVector x) hdet
  simpa only [Function.comp_def, heightVector_weightVector] using
    hcont.comp hu

theorem tendsto_T_weightVector_of_tendsto_weightVector
    {I : Type*} {l : Filter I} {lambda : Fin 4 → ℝ}
    (hlambda : Function.Injective lambda)
    (u : I → Weights) (x : Weights)
    (hu : Tendsto (fun a ↦ weightVector (u a)) l
      (nhds (weightVector x))) :
    Tendsto (fun a ↦ weightVector (T lambda hlambda (u a))) l
      (nhds (weightVector (T lambda hlambda x))) := by
  have hdet : weightedMomentGramDetVector lambda (weightVector x) ≠ 0 := by
    simpa using ne_of_gt (weightedMomentGramDet_pos hlambda x)
  have hheight : heightVector lambda (weightVector x) ≠ 0 := by
    simpa using ne_of_gt (height_pos hlambda x)
  have hcont : Tendsto (nextWeightVector lambda)
      (nhds (weightVector x))
      (nhds (nextWeightVector lambda (weightVector x))) :=
    continuousAt_nextWeightVector lambda (weightVector x) hdet hheight
  have hraw := hcont.comp hu
  have hsource : (fun a ↦ weightVector (T lambda hlambda (u a))) =
      (fun a ↦ nextWeightVector lambda (weightVector (u a))) := by
    funext a i
    exact (nextWeightVector_weightVector lambda hlambda (u a) i).symm
  have htarget : weightVector (T lambda hlambda x) =
      nextWeightVector lambda (weightVector x) := by
    funext i
    exact (nextWeightVector_weightVector lambda hlambda x i).symm
  rw [hsource, htarget]
  exact hraw

theorem tendsto_rho_of_tendsto_weightVector
    {I : Type*} {l : Filter I} {lambda : Fin 4 → ℝ}
    (hlambda : Function.Injective lambda)
    (u : I → Weights) (x : Weights)
    (hu : Tendsto (fun a ↦ weightVector (u a)) l
      (nhds (weightVector x))) :
    Tendsto (fun a ↦ rho lambda (u a)) l (nhds (rho lambda x)) := by
  have hdet : weightedMomentGramDetVector lambda (weightVector x) ≠ 0 := by
    simpa using ne_of_gt (weightedMomentGramDet_pos hlambda x)
  have hheight : heightVector lambda (weightVector x) ≠ 0 := by
    simpa using ne_of_gt (height_pos hlambda x)
  have hcont : Tendsto (rhoVector lambda)
      (nhds (weightVector x)) (nhds (rhoVector lambda (weightVector x))) :=
    continuousAt_rhoVector lambda (weightVector x) hdet hheight
  simpa only [Function.comp_def, rhoVector_weightVector] using
    hcont.comp hu

theorem tendsto_alpha_of_tendsto_weightVector
    {I : Type*} {l : Filter I} {lambda : Fin 4 → ℝ}
    (hlambda : Function.Injective lambda)
    (u : I → Weights) (x : Weights)
    (hu : Tendsto (fun a ↦ weightVector (u a)) l
      (nhds (weightVector x))) :
    Tendsto (fun a ↦ alpha lambda hlambda (u a)) l
      (nhds (alpha lambda hlambda x)) := by
  have hdet : weightedMomentGramDetVector lambda (weightVector x) ≠ 0 := by
    simpa using ne_of_gt (weightedMomentGramDet_pos hlambda x)
  have hheight : heightVector lambda (weightVector x) ≠ 0 := by
    simpa using ne_of_gt (height_pos hlambda x)
  have hnext : nextWeightVector lambda (weightVector x) =
      weightVector (T lambda hlambda x) := by
    funext i
    exact nextWeightVector_weightVector lambda hlambda x i
  have hdetNext : weightedMomentGramDetVector lambda
      (nextWeightVector lambda (weightVector x)) ≠ 0 := by
    rw [hnext, weightedMomentGramDetVector_weightVector]
    exact ne_of_gt (weightedMomentGramDet_pos hlambda (T lambda hlambda x))
  have hcont : Tendsto (alphaVector lambda)
      (nhds (weightVector x)) (nhds (alphaVector lambda (weightVector x))) :=
    continuousAt_alphaVector lambda (weightVector x) hdet hheight hdetNext
  simpa only [Function.comp_def,
    alphaVector_weightVector lambda hlambda] using
    hcont.comp hu

/-- All coefficients and scalars in the exact interpolation identity vary
continuously together in their concrete product topology. -/
theorem tendsto_interpolationData_of_tendsto_weightVector
    {I : Type*} {l : Filter I} {lambda : Fin 4 → ℝ}
    (hlambda : Function.Injective lambda)
    (u : I → Weights) (x : Weights)
    (hu : Tendsto (fun a ↦ weightVector (u a)) l
      (nhds (weightVector x))) :
    Tendsto (fun a ↦ interpolationData lambda hlambda (u a)) l
      (nhds (interpolationData lambda hlambda x)) := by
  have hP := tendsto_P_coeffPair_of_tendsto_weightVector hlambda u x hu
  have hT := tendsto_T_weightVector_of_tendsto_weightVector hlambda u x hu
  have hPT := tendsto_P_coeffPair_of_tendsto_weightVector hlambda
    (fun a ↦ T lambda hlambda (u a)) (T lambda hlambda x) hT
  have hHT := tendsto_H_of_tendsto_weightVector hlambda
    (fun a ↦ T lambda hlambda (u a)) (T lambda hlambda x) hT
  have hrho := tendsto_rho_of_tendsto_weightVector hlambda u x hu
  have halpha := tendsto_alpha_of_tendsto_weightVector hlambda u x hu
  simpa only [interpolationData, nhds_prod_eq] using
    hP.prodMk (hPT.prodMk (hHT.prodMk (hrho.prodMk halpha)))

end

end FourNode
end Forsythe
