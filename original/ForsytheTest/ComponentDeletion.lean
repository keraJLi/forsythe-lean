import Forsythe.Arnoldi.Grade
import Forsythe.Matrix.Bridge

/-!
# A concrete component deletion

For the diagonal nodes `-1, 0, 1/2, 2` and initial coordinates
`1, 1, 4, 1`, the moment system selects `z (z - 1)`.  Thus the initially
nonzero component at the zero node is deleted in one restart-two step.
-/

set_option autoImplicit false

namespace ForsytheTest

open Forsythe
open scoped ENNReal

noncomputable section

private def deletionMatrix : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.diagonal ![-1, 0, (1 / 2 : ℝ), 2]

private abbrev deletionOperator : Module.End ℝ (EuclideanSpace ℝ (Fin 4)) :=
  Matrix.toLpLin 2 2 deletionMatrix

private def deletionV : EuclideanSpace ℝ (Fin 4) :=
  !₂[(1 : ℝ), 1, 4, 1]

private def deletionNext : EuclideanSpace ℝ (Fin 4) :=
  !₂[(2 / 3 : ℝ), 0, -(1 / 3 : ℝ), 2 / 3]

private def deletionFactor : MonicQuadratic := ⟨-1, 0⟩

private def deletionKrylovMatrix : Matrix (Fin 4) (Fin 4) ℝ :=
  !![(1 : ℝ), -1, 1, -1;
     1, 0, 0, 0;
     4, 2, 1, (1 / 2 : ℝ);
     1, 2, 4, 8]

private lemma deletionOperator_apply (x : EuclideanSpace ℝ (Fin 4)) :
    deletionOperator x = !₂[-x 0, 0, (1 / 2 : ℝ) * x 2, 2 * x 3] := by
  apply WithLp.ofLp_injective 2
  ext i
  fin_cases i <;>
    simp [deletionOperator, deletionMatrix, Matrix.toLpLin_apply, Matrix.mulVec,
      dotProduct, Fin.sum_univ_four]

private lemma deletionOperator_sq_apply (x : EuclideanSpace ℝ (Fin 4)) :
    (deletionOperator ^ 2) x =
      !₂[x 0, 0, (1 / 4 : ℝ) * x 2, 4 * x 3] := by
  rw [pow_two, Module.End.mul_apply, deletionOperator_apply,
    deletionOperator_apply]
  apply WithLp.ofLp_injective 2
  ext i
  fin_cases i <;> simp [Matrix.cons_val_two, Matrix.cons_val_three] <;> ring

private lemma deletionOperator_cube_apply (x : EuclideanSpace ℝ (Fin 4)) :
    (deletionOperator ^ 3) x =
      !₂[-x 0, 0, (1 / 8 : ℝ) * x 2, 8 * x 3] := by
  rw [show deletionOperator ^ 3 = deletionOperator * deletionOperator ^ 2 by
      noncomm_ring,
    Module.End.mul_apply, deletionOperator_sq_apply, deletionOperator_apply]
  apply WithLp.ofLp_injective 2
  ext i
  fin_cases i <;> simp [Matrix.cons_val_two, Matrix.cons_val_three] <;> ring

private lemma deletionKrylov_eq :
    (fun k : Fin 4 ↦ (deletionOperator ^ (k : ℕ)) deletionV) =
      fun k ↦ WithLp.toLp 2 (deletionKrylovMatrix.col k) := by
  funext k
  fin_cases k
  · change (deletionOperator ^ (0 : ℕ)) deletionV =
      WithLp.toLp 2 (deletionKrylovMatrix.col 0)
    apply WithLp.ofLp_injective 2
    ext i
    fin_cases i <;> norm_num [deletionV, deletionKrylovMatrix,
      Matrix.cons_val_two, Matrix.cons_val_three]
  · change (deletionOperator ^ (1 : ℕ)) deletionV =
      WithLp.toLp 2 (deletionKrylovMatrix.col 1)
    rw [pow_one, deletionOperator_apply]
    apply WithLp.ofLp_injective 2
    ext i
    fin_cases i <;> norm_num [deletionV, deletionKrylovMatrix,
      Matrix.cons_val_two, Matrix.cons_val_three]
  · change (deletionOperator ^ (2 : ℕ)) deletionV =
      WithLp.toLp 2 (deletionKrylovMatrix.col 2)
    rw [deletionOperator_sq_apply]
    apply WithLp.ofLp_injective 2
    ext i
    fin_cases i <;> norm_num [deletionV, deletionKrylovMatrix,
      Matrix.cons_val_two, Matrix.cons_val_three]
  · change (deletionOperator ^ (3 : ℕ)) deletionV =
      WithLp.toLp 2 (deletionKrylovMatrix.col 3)
    rw [deletionOperator_cube_apply]
    apply WithLp.ofLp_injective 2
    ext i
    fin_cases i <;> norm_num [deletionV, deletionKrylovMatrix,
      Matrix.cons_val_two, Matrix.cons_val_three]

private lemma deletionKrylov_linearIndependent :
    LinearIndependent ℝ
      (fun k : Fin 4 ↦ (deletionOperator ^ (k : ℕ)) deletionV) := by
  rw [deletionKrylov_eq]
  apply LinearIndependent.map'
    (Matrix.linearIndependent_cols_of_det_ne_zero
      (A := deletionKrylovMatrix) ?_)
    (WithLp.linearEquiv 2 ℝ (Fin 4 → ℝ)).symm.toLinearMap
    (WithLp.linearEquiv 2 ℝ (Fin 4 → ℝ)).symm.ker
  rw [Matrix.det_succ_row deletionKrylovMatrix 1]
  simp [Fin.sum_univ_four, deletionKrylovMatrix, Matrix.det_fin_three,
    Matrix.cons_val_two, Matrix.cons_val_three, Fin.succAbove]
  norm_num

private lemma deletion_grade_ge_four : 4 ≤ grade deletionOperator deletionV := by
  let family : Fin 4 → EuclideanSpace ℝ (Fin 4) :=
    fun k ↦ (deletionOperator ^ (k : ℕ)) deletionV
  have hli : LinearIndependent ℝ family := by
    simpa only [family] using deletionKrylov_linearIndependent
  have hspan : Submodule.span ℝ (Set.range family) ≤
      cyclicSubspace deletionOperator deletionV := by
    apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    rw [cyclicSubspace]
    exact Submodule.subset_span ⟨(k : ℕ), rfl⟩
  have hfinrank := Submodule.finrank_mono hspan
  rw [finrank_span_eq_card hli] at hfinrank
  simpa [grade, family] using hfinrank

private lemma deletion_grade : grade deletionOperator deletionV = 4 := by
  apply le_antisymm
  · exact (cyclicSubspace deletionOperator deletionV).finrank_le.trans_eq (by simp)
  · exact deletion_grade_ge_four

private lemma deletion_moments :
    moment deletionOperator deletionV 0 = 19 ∧
      moment deletionOperator deletionV 1 = 9 ∧
      moment deletionOperator deletionV 2 = 9 ∧
      moment deletionOperator deletionV 3 = 9 := by
  constructor
  · change inner ℝ deletionV deletionV = 19
    rw [real_inner_self_eq_norm_sq, EuclideanSpace.real_norm_sq_eq]
    norm_num [deletionV, Fin.sum_univ_four, Matrix.cons_val_two,
      Matrix.cons_val_three]
  constructor
  · rw [moment, pow_one, deletionOperator_apply]
    norm_num [PiLp.inner_apply, deletionV, Fin.sum_univ_four,
      Matrix.cons_val_two, Matrix.cons_val_three]
  constructor
  · rw [moment, deletionOperator_sq_apply]
    norm_num [PiLp.inner_apply, deletionV, Fin.sum_univ_four,
      Matrix.cons_val_two, Matrix.cons_val_three]
  · rw [moment, deletionOperator_cube_apply]
    norm_num [PiLp.inner_apply, deletionV, Fin.sum_univ_four,
      Matrix.cons_val_two, Matrix.cons_val_three]

private lemma deletion_factor :
    arnoldiPoly2 deletionOperator deletionV = deletionFactor := by
  rcases deletion_moments with ⟨h0, h1, h2, h3⟩
  ext
  · norm_num [arnoldiPoly2, momentGramDet, deletionFactor, h0, h1, h2, h3]
  · norm_num [arnoldiPoly2, momentGramDet, deletionFactor, h0, h1, h2, h3]

private lemma deletion_raw :
    rawArnoldiStep2 deletionOperator deletionV = !₂[(2 : ℝ), 0, -1, 2] := by
  rw [rawArnoldiStep2, deletion_factor, polyApply_monicQuadratic,
    deletionOperator_sq_apply, deletionOperator_apply]
  apply WithLp.ofLp_injective 2
  ext i
  fin_cases i <;> norm_num [deletionFactor, deletionV,
    Matrix.cons_val_two, Matrix.cons_val_three]

private lemma deletion_raw_norm :
    ‖rawArnoldiStep2 deletionOperator deletionV‖ = 3 := by
  rw [deletion_raw, EuclideanSpace.norm_eq]
  norm_num [Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]

private lemma deletion_step :
    arnoldiStep2 deletionOperator deletionV = deletionNext := by
  rw [arnoldiStep2, deletion_raw_norm, deletion_raw]
  apply WithLp.ofLp_injective 2
  ext i
  fin_cases i <;> norm_num [deletionNext, Matrix.cons_val_two,
    Matrix.cons_val_three]

/-- The initial state has four active distinct diagonal nodes. -/
example : grade deletionOperator deletionV = 4 := deletion_grade

/-- The zero-node coordinate starts nonzero. -/
example : deletionV 1 ≠ 0 := by norm_num [deletionV]

/-- One restart-two step deletes that coordinate exactly. -/
example : (arnoldiStep2 deletionOperator deletionV) 1 = 0 := by
  rw [deletion_step]
  rfl

end

end ForsytheTest
