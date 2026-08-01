import Forsythe.Arnoldi.Grade
import Forsythe.Matrix.Bridge

/-!
# A concrete grade-three two-cycle

The diagonal operator with nodes `-1, 0, 1`, started from weights
`1/4, 1/2, 1/4`, selects `z^2 - 1/2`.  Its normalized update flips only
the middle component, so a second step returns exactly to the initial state.
-/

set_option autoImplicit false

namespace ForsytheTest

open Forsythe
open scoped ENNReal

noncomputable section

private def cycleMatrix : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.diagonal ![-1, 0, 1]

private abbrev cycleOperator : Module.End ℝ (EuclideanSpace ℝ (Fin 3)) :=
  Matrix.toLpLin 2 2 cycleMatrix

private def cycleV0 : EuclideanSpace ℝ (Fin 3) :=
  !₂[(1 / 2 : ℝ), Real.sqrt 2 / 2, (1 / 2 : ℝ)]

private def cycleV1 : EuclideanSpace ℝ (Fin 3) :=
  !₂[(1 / 2 : ℝ), -(Real.sqrt 2 / 2), (1 / 2 : ℝ)]

private def cycleFactor : MonicQuadratic := ⟨0, -(1 / 2 : ℝ)⟩

private def cycleKrylovMatrix : Matrix (Fin 3) (Fin 3) ℝ :=
  !![(1 / 2 : ℝ), -(1 / 2 : ℝ), (1 / 2 : ℝ);
     Real.sqrt 2 / 2, 0, 0;
     (1 / 2 : ℝ), (1 / 2 : ℝ), (1 / 2 : ℝ)]

private lemma cycleOperator_apply (x : EuclideanSpace ℝ (Fin 3)) :
    cycleOperator x = !₂[-x 0, 0, x 2] := by
  apply WithLp.ofLp_injective 2
  ext i
  fin_cases i <;>
    simp [cycleOperator, cycleMatrix, Matrix.toLpLin_apply, Matrix.mulVec,
      dotProduct, Fin.sum_univ_three]

private lemma cycleOperator_sq_apply (x : EuclideanSpace ℝ (Fin 3)) :
    (cycleOperator ^ 2) x = !₂[x 0, 0, x 2] := by
  rw [pow_two, Module.End.mul_apply, cycleOperator_apply, cycleOperator_apply]
  apply WithLp.ofLp_injective 2
  ext i
  fin_cases i <;> simp

private lemma cycleOperator_cube_apply (x : EuclideanSpace ℝ (Fin 3)) :
    (cycleOperator ^ 3) x = !₂[-x 0, 0, x 2] := by
  rw [show cycleOperator ^ 3 = cycleOperator * cycleOperator ^ 2 by noncomm_ring,
    Module.End.mul_apply, cycleOperator_sq_apply, cycleOperator_apply]
  apply WithLp.ofLp_injective 2
  ext i
  fin_cases i <;> simp [Matrix.cons_val_two]

private lemma cycleKrylov_eq :
    (fun k : Fin 3 ↦ (cycleOperator ^ (k : ℕ)) cycleV0) =
      fun k ↦ WithLp.toLp 2 (cycleKrylovMatrix.col k) := by
  funext k
  fin_cases k
  · change (cycleOperator ^ (0 : ℕ)) cycleV0 =
      WithLp.toLp 2 (cycleKrylovMatrix.col 0)
    apply WithLp.ofLp_injective 2
    ext i
    fin_cases i <;> norm_num [cycleV0, cycleKrylovMatrix,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_fin_one]
  · change (cycleOperator ^ (1 : ℕ)) cycleV0 =
      WithLp.toLp 2 (cycleKrylovMatrix.col 1)
    rw [pow_one, cycleOperator_apply]
    apply WithLp.ofLp_injective 2
    ext i
    fin_cases i <;> norm_num [cycleV0, cycleKrylovMatrix,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_fin_one]
  · change (cycleOperator ^ (2 : ℕ)) cycleV0 =
      WithLp.toLp 2 (cycleKrylovMatrix.col 2)
    rw [cycleOperator_sq_apply]
    apply WithLp.ofLp_injective 2
    ext i
    fin_cases i <;> norm_num [cycleV0, cycleKrylovMatrix,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_fin_one]

private lemma cycleKrylov_linearIndependent :
    LinearIndependent ℝ (fun k : Fin 3 ↦ (cycleOperator ^ (k : ℕ)) cycleV0) := by
  rw [cycleKrylov_eq]
  apply LinearIndependent.map'
    (Matrix.linearIndependent_cols_of_det_ne_zero (A := cycleKrylovMatrix) ?_)
    (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).symm.toLinearMap
    (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).symm.ker
  rw [Matrix.det_fin_three]
  simp [cycleKrylovMatrix]

private lemma cycle_grade_ge_three : 3 ≤ grade cycleOperator cycleV0 := by
  let family : Fin 3 → EuclideanSpace ℝ (Fin 3) :=
    fun k ↦ (cycleOperator ^ (k : ℕ)) cycleV0
  have hli : LinearIndependent ℝ family := by
    simpa only [family] using cycleKrylov_linearIndependent
  have hspan : Submodule.span ℝ (Set.range family) ≤
      cyclicSubspace cycleOperator cycleV0 := by
    apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    rw [cyclicSubspace]
    exact Submodule.subset_span ⟨(k : ℕ), rfl⟩
  have hfinrank := Submodule.finrank_mono hspan
  rw [finrank_span_eq_card hli] at hfinrank
  simpa [grade, family] using hfinrank

private lemma cycle_grade : grade cycleOperator cycleV0 = 3 := by
  apply le_antisymm
  · exact (cyclicSubspace cycleOperator cycleV0).finrank_le.trans_eq (by simp)
  · exact cycle_grade_ge_three

private lemma cycle_symmetric : cycleOperator.IsSymmetric := by
  apply Forsythe.Matrix.isSymmetric_operator
  simp [cycleMatrix, Matrix.IsSymm]

private lemma cycle_norm : ‖cycleV0‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  have hsqrt : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hsum : ∑ i : Fin 3, ‖cycleV0 i‖ ^ 2 = (1 : ℝ) := by
    simp [cycleV0, Fin.sum_univ_three]
    nlinarith
  rw [hsum, Real.sqrt_one]

private lemma cycle_norm_v1 : ‖cycleV1‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  have hsqrt : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hsum : ∑ i : Fin 3, ‖cycleV1 i‖ ^ 2 = (1 : ℝ) := by
    simp [cycleV1, Fin.sum_univ_three]
    nlinarith
  rw [hsum, Real.sqrt_one]

private lemma cycle_moments_v0 :
    moment cycleOperator cycleV0 0 = 1 ∧
      moment cycleOperator cycleV0 1 = 0 ∧
      moment cycleOperator cycleV0 2 = 1 / 2 ∧
      moment cycleOperator cycleV0 3 = 0 := by
  have hsqrt : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (by positivity)
  constructor
  · simp [moment, cycle_norm]
  constructor
  · rw [moment, pow_one, cycleOperator_apply]
    simp [PiLp.inner_apply, cycleV0, Fin.sum_univ_three]
  constructor
  · rw [moment, cycleOperator_sq_apply]
    simp [PiLp.inner_apply, cycleV0, Fin.sum_univ_three]
    norm_num
  · rw [moment, cycleOperator_cube_apply]
    simp [PiLp.inner_apply, cycleV0, Fin.sum_univ_three]

private lemma cycle_moments_v1 :
    moment cycleOperator cycleV1 0 = 1 ∧
      moment cycleOperator cycleV1 1 = 0 ∧
      moment cycleOperator cycleV1 2 = 1 / 2 ∧
      moment cycleOperator cycleV1 3 = 0 := by
  have hsqrt : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (by positivity)
  constructor
  · simp [moment, cycle_norm_v1]
  constructor
  · rw [moment, pow_one, cycleOperator_apply]
    simp [PiLp.inner_apply, cycleV1, Fin.sum_univ_three]
  constructor
  · rw [moment, cycleOperator_sq_apply]
    simp [PiLp.inner_apply, cycleV1, Fin.sum_univ_three]
    norm_num
  · rw [moment, cycleOperator_cube_apply]
    simp [PiLp.inner_apply, cycleV1, Fin.sum_univ_three]

private lemma cycle_factor_v0 : arnoldiPoly2 cycleOperator cycleV0 = cycleFactor := by
  rcases cycle_moments_v0 with ⟨h0, h1, h2, h3⟩
  ext
  · norm_num [arnoldiPoly2, momentGramDet, cycleFactor, h0, h1, h2, h3]
  · norm_num [arnoldiPoly2, momentGramDet, cycleFactor, h0, h1, h2, h3]

private lemma cycle_factor_v1 : arnoldiPoly2 cycleOperator cycleV1 = cycleFactor := by
  rcases cycle_moments_v1 with ⟨h0, h1, h2, h3⟩
  ext
  · norm_num [arnoldiPoly2, momentGramDet, cycleFactor, h0, h1, h2, h3]
  · norm_num [arnoldiPoly2, momentGramDet, cycleFactor, h0, h1, h2, h3]

private lemma cycle_raw_v0 :
    rawArnoldiStep2 cycleOperator cycleV0 = (1 / 2 : ℝ) • cycleV1 := by
  rw [rawArnoldiStep2, cycle_factor_v0, polyApply_monicQuadratic,
    cycleOperator_sq_apply]
  apply WithLp.ofLp_injective 2
  ext i
  fin_cases i <;> simp [cycleFactor, cycleV0, cycleV1] <;> ring

private lemma cycle_raw_v1 :
    rawArnoldiStep2 cycleOperator cycleV1 = (1 / 2 : ℝ) • cycleV0 := by
  rw [rawArnoldiStep2, cycle_factor_v1, polyApply_monicQuadratic,
    cycleOperator_sq_apply]
  apply WithLp.ofLp_injective 2
  ext i
  fin_cases i <;> simp [cycleFactor, cycleV0, cycleV1] <;> ring

private lemma cycle_step_v0 : arnoldiStep2 cycleOperator cycleV0 = cycleV1 := by
  rw [arnoldiStep2, cycle_raw_v0, norm_smul, cycle_norm_v1]
  rw [smul_smul]
  norm_num

private lemma cycle_step_v1 : arnoldiStep2 cycleOperator cycleV1 = cycleV0 := by
  rw [arnoldiStep2, cycle_raw_v1, norm_smul, cycle_norm]
  rw [smul_smul]
  norm_num

/-- The concrete diagonal example has exactly grade three. -/
example : grade cycleOperator cycleV0 = 3 := cycle_grade

/-- The concrete diagonal example is an exact two-cycle. -/
example : ∀ k : ℕ, arnoldiOrbit2 cycleOperator cycleV0 (2 * k) = cycleV0 ∧
    arnoldiOrbit2 cycleOperator cycleV0 (2 * k + 1) = cycleV1 := by
  have hperiod : ∀ n : ℕ,
      arnoldiOrbit2 cycleOperator cycleV0 (n + 2) =
        arnoldiOrbit2 cycleOperator cycleV0 n := by
    intro n
    induction n with
    | zero => simp [cycle_step_v0, cycle_step_v1]
    | succ n ih =>
        change arnoldiStep2 cycleOperator
          (arnoldiOrbit2 cycleOperator cycleV0 (n + 2)) =
            arnoldiStep2 cycleOperator (arnoldiOrbit2 cycleOperator cycleV0 n)
        rw [ih]
  intro k
  induction k with
  | zero => simp [cycle_step_v0]
  | succ k ih =>
      rcases ih with ⟨heven, hodd⟩
      constructor
      · rw [Nat.mul_succ]
        exact (hperiod (2 * k)).trans heven
      · rw [Nat.mul_succ, show 2 * k + 2 + 1 = (2 * k + 1) + 2 by omega]
        exact (hperiod (2 * k + 1)).trans hodd

#check cycle_symmetric
#check cycle_norm

end

end ForsytheTest
