import Forsythe.Polynomial.FourNode

/-! Compile-time regressions for the exact four-node remainder identities. -/

set_option autoImplicit false

namespace ForsytheTest

open Polynomial
open Forsythe
open Forsythe.FourNode

noncomputable section

private def symmetricNodes : Fin 4 → ℝ := ![-2, -1, 1, 2]

private def innerFactor : MonicQuadratic :=
  ⟨0, -1⟩

private def outerFactor : MonicQuadratic :=
  ⟨0, -4⟩

private def leftPerturbedFactor : MonicQuadratic :=
  ⟨1, 0⟩

private def rightPerturbedFactor : MonicQuadratic :=
  ⟨-1, 0⟩

private theorem symmetric_factorization :
    innerFactor.toPolynomial * outerFactor.toPolynomial =
      nodalQuartic symmetricNodes + C 0 := by
  simp [innerFactor, outerFactor, MonicQuadratic.toPolynomial,
    nodalQuartic, symmetricNodes, Fin.prod_univ_succ]
  have hfour : (C (4 : ℝ) : ℝ[X]) = C 2 ^ 2 := by
    rw [← C_pow]
    norm_num
  rw [hfour]
  ring

private theorem symmetric_nodalQuartic :
    nodalQuartic symmetricNodes =
      innerFactor.toPolynomial * outerFactor.toPolynomial := by
  simpa using symmetric_factorization.symm

private theorem nodalQuartic_eval_one :
    (nodalQuartic symmetricNodes).eval 1 = 0 := by
  simp [nodalQuartic, symmetricNodes, Fin.prod_univ_succ]

private theorem nodalQuartic_eval_neg_one :
    (nodalQuartic symmetricNodes).eval (-1) = 0 := by
  simp [nodalQuartic, symmetricNodes, Fin.prod_univ_succ]

private theorem innerFactor_split_one :
    (X - C (1 : ℝ)) * (X + C (1 : ℝ)) = innerFactor.toPolynomial := by
  simp [innerFactor, MonicQuadratic.toPolynomial]
  ring

private theorem innerFactor_split_neg_one :
    (X - C (-1 : ℝ)) * (X - C (1 : ℝ)) = innerFactor.toPolynomial := by
  simp [innerFactor, MonicQuadratic.toPolynomial]
  ring

private theorem dividedDifference_one :
    dividedDifference symmetricNodes 1 =
      (X + C (1 : ℝ)) * outerFactor.toPolynomial := by
  apply mul_left_cancel₀ (X_sub_C_ne_zero (1 : ℝ))
  rw [X_sub_C_mul_dividedDifference, nodalQuartic_eval_one]
  simp only [C_0, sub_zero]
  rw [symmetric_nodalQuartic, ← innerFactor_split_one]
  ring

private theorem dividedDifference_neg_one :
    dividedDifference symmetricNodes (-1) =
      (X - C (1 : ℝ)) * outerFactor.toPolynomial := by
  apply mul_left_cancel₀ (X_sub_C_ne_zero (-1 : ℝ))
  rw [X_sub_C_mul_dividedDifference, nodalQuartic_eval_neg_one]
  simp only [C_0, sub_zero]
  rw [symmetric_nodalQuartic, ← innerFactor_split_neg_one]
  ring

private theorem left_interpolation_identity :
    leftPerturbedFactor.toPolynomial * outerFactor.toPolynomial =
      nodalQuartic symmetricNodes + C 0 +
        (1 : ℝ) • dividedDifference symmetricNodes 1 := by
  rw [symmetric_nodalQuartic, dividedDifference_one]
  simp only [C_0, add_zero, one_smul]
  simp [leftPerturbedFactor, innerFactor, MonicQuadratic.toPolynomial]
  ring

private theorem right_interpolation_identity :
    outerFactor.toPolynomial * rightPerturbedFactor.toPolynomial =
      nodalQuartic symmetricNodes + C 0 +
        (-1 : ℝ) • dividedDifference symmetricNodes (-1) := by
  rw [symmetric_nodalQuartic, dividedDifference_neg_one]
  simp only [C_0, add_zero, neg_smul]
  simp [rightPerturbedFactor, innerFactor, MonicQuadratic.toPolynomial]
  ring

example :
    remainderLinearCoeff outerFactor (dividedDifference symmetricNodes 0) = -1 := by
  rw [remainderLinearCoeff_dividedDifference_right symmetricNodes
    innerFactor outerFactor 0 0 symmetric_factorization]
  norm_num [innerFactor]

example :
    remainderLinearCoeff innerFactor (dividedDifference symmetricNodes 0) = -4 := by
  rw [remainderLinearCoeff_dividedDifference_left symmetricNodes
    innerFactor outerFactor 0 0 symmetric_factorization]
  norm_num [outerFactor]

example :
    (X - C (0 : ℝ)) * dividedDifference symmetricNodes 0 =
      nodalQuartic symmetricNodes - C ((nodalQuartic symmetricNodes).eval 0) :=
  X_sub_C_mul_dividedDifference symmetricNodes 0

example :
    (-1 : ℝ) *
        remainderLinearCoeff outerFactor (dividedDifference symmetricNodes (-1)) =
      (1 : ℝ) * remainderLinearCoeff outerFactor
        (dividedDifference symmetricNodes 1) := by
  exact sharedFactor_recurrence symmetricNodes leftPerturbedFactor outerFactor
    rightPerturbedFactor 0 0 1 (-1) 1 (-1)
    left_interpolation_identity right_interpolation_identity

end
end ForsytheTest
