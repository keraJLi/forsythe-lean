import Forsythe.FourNode.Continuity

/-!
# Geometrically perturbed four-node recurrences

For a sequence of principal-weight states `x k`, let `y k = T (x k)` be the
exact four-node update.  This module separates the exact scalar dynamics of
`y k` from the defect between `x (k+1)` and `y k`.  The two defect terms are
then controlled by the explicit denominator-floor estimates from
`Forsythe.FourNode.Continuity`.
-/

set_option autoImplicit false

namespace Forsythe
namespace FourNode

open Polynomial

noncomputable section

/-- The exact update associated with the `k`th state of a perturbed orbit. -/
def exactUpdateSeq (lambda : Fin 4 → ℝ)
    (hlambda : Function.Injective lambda) (x : ℕ → Weights) (k : ℕ) : Weights :=
  T lambda hlambda (x k)

@[simp]
theorem exactUpdateSeq_apply (lambda : Fin 4 → ℝ)
    (hlambda : Function.Injective lambda) (x : ℕ → Weights) (k : ℕ) :
    exactUpdateSeq lambda hlambda x k = T lambda hlambda (x k) := rfl

/-- The barycentric parameter along the perturbed sequence. -/
def rhoSeq (lambda : Fin 4 → ℝ) (x : ℕ → Weights) (k : ℕ) : ℝ :=
  rho lambda (x k)

/-- The interpolation coefficient along the perturbed sequence. -/
def alphaSeq (lambda : Fin 4 → ℝ)
    (hlambda : Function.Injective lambda) (x : ℕ → Weights) (k : ℕ) : ℝ :=
  alpha lambda hlambda (x k)

/-- The remainder-linear coefficient at the old barycentric parameter, with
the exact-update factor as the shared middle factor. -/
def oldRemainderCoeff (lambda : Fin 4 → ℝ)
    (hlambda : Function.Injective lambda) (x : ℕ → Weights) (k : ℕ) : ℝ :=
  remainderLinearCoeff (P lambda (exactUpdateSeq lambda hlambda x k))
    (dividedDifference lambda (rhoSeq lambda x k))

/-- The remainder-linear coefficient at the exact update's barycentric
parameter.  This is the denominator of the exact multiplier. -/
def newRemainderCoeff (lambda : Fin 4 → ℝ)
    (hlambda : Function.Injective lambda) (x : ℕ → Weights) (k : ℕ) : ℝ :=
  remainderLinearCoeff (P lambda (exactUpdateSeq lambda hlambda x k))
    (dividedDifference lambda
      (rho lambda (exactUpdateSeq lambda hlambda x k)))

/-- Exact quotient multiplier furnished by the shared-middle-factor
recurrence.  Its denominator is required to be nonzero only in the theorems
that use the quotient identity. -/
def remainderMultiplier (lambda : Fin 4 → ℝ)
    (hlambda : Function.Injective lambda) (x : ℕ → Weights) (k : ℕ) : ℝ :=
  oldRemainderCoeff lambda hlambda x k /
    newRemainderCoeff lambda hlambda x k

/-- The exact coefficient multiplying `alpha k` in the `rho` increment. -/
def rhoIncrementCoeff (lambda : Fin 4 → ℝ)
    (hlambda : Function.Injective lambda) (x : ℕ → Weights) (k : ℕ) : ℝ :=
  (nodalQuartic lambda).eval (rhoSeq lambda x k) /
    H lambda (exactUpdateSeq lambda hlambda x k)

/-- Defect in the interpolation coefficient after replacing the exact update
by the next perturbed state. -/
def bAlpha (lambda : Fin 4 → ℝ)
    (hlambda : Function.Injective lambda) (x : ℕ → Weights) (k : ℕ) : ℝ :=
  alphaSeq lambda hlambda x (k + 1) -
    alpha lambda hlambda (exactUpdateSeq lambda hlambda x k)

/-- Defect in the barycentric parameter after replacing the exact update by
the next perturbed state. -/
def bRho (lambda : Fin 4 → ℝ)
    (hlambda : Function.Injective lambda) (x : ℕ → Weights) (k : ℕ) : ℝ :=
  rhoSeq lambda x (k + 1) -
    rho lambda (exactUpdateSeq lambda hlambda x k)

/-- A common Gram and height floor on every state needed to compare
`x (k+1)` with `y k = T (x k)`.  The final field supplies the Gram floor on
`T (y k)`, which is precisely the extra denominator needed by the `alpha`
continuity estimate. -/
structure PerturbationFloors (lambda : Fin 4 → ℝ)
    (hlambda : Function.Injective lambda) (x : ℕ → Weights)
    (delta eta : ℝ) : Prop where
  gram_x : ∀ k, delta ≤ weightedMomentGramDet lambda (x k)
  gram_y : ∀ k, delta ≤
    weightedMomentGramDet lambda (exactUpdateSeq lambda hlambda x k)
  gram_T_y : ∀ k, delta ≤ weightedMomentGramDet lambda
    (T lambda hlambda (exactUpdateSeq lambda hlambda x k))
  height_x : ∀ k, eta ≤ H lambda (x k)
  height_y : ∀ k, eta ≤ H lambda (exactUpdateSeq lambda hlambda x k)

/-- Coordinate defect bounded by a geometric sequence.  Positivity of the
displayed right-hand side need not be duplicated: it follows automatically
whenever this predicate is inhabited. -/
def HasGeometricWeightDefect (lambda : Fin 4 → ℝ)
    (hlambda : Function.Injective lambda) (x : ℕ → Weights)
    (B q : ℝ) : Prop :=
  ∀ k, ‖weightVector (x (k + 1)) -
      weightVector (exactUpdateSeq lambda hlambda x k)‖ ≤ B * q ^ k

/-- The shared-factor recurrence gives the exact interpolation-coefficient
update before perturbation. -/
theorem alpha_exactUpdate_eq_multiplier_mul
    {lambda : Fin 4 → ℝ} (hlambda : Function.Injective lambda)
    (x : ℕ → Weights) (k : ℕ)
    (hden : newRemainderCoeff lambda hlambda x k ≠ 0) :
    alpha lambda hlambda (exactUpdateSeq lambda hlambda x k) =
      remainderMultiplier lambda hlambda x k * alphaSeq lambda hlambda x k := by
  have hshared := consecutive_sharedFactor_recurrence hlambda (x k)
  change
    alpha lambda hlambda (exactUpdateSeq lambda hlambda x k) *
        newRemainderCoeff lambda hlambda x k =
      alphaSeq lambda hlambda x k * oldRemainderCoeff lambda hlambda x k
    at hshared
  rw [remainderMultiplier]
  calc
    alpha lambda hlambda (exactUpdateSeq lambda hlambda x k) =
        (alphaSeq lambda hlambda x k * oldRemainderCoeff lambda hlambda x k) /
          newRemainderCoeff lambda hlambda x k :=
      (eq_div_iff hden).2 hshared
    _ = oldRemainderCoeff lambda hlambda x k /
          newRemainderCoeff lambda hlambda x k * alphaSeq lambda hlambda x k := by
      ring

/-- Exact perturbed affine recurrence for the interpolation coefficient. -/
theorem alphaSeq_succ_recurrence
    {lambda : Fin 4 → ℝ} (hlambda : Function.Injective lambda)
    (x : ℕ → Weights) (k : ℕ)
    (hden : newRemainderCoeff lambda hlambda x k ≠ 0) :
    alphaSeq lambda hlambda x (k + 1) =
      remainderMultiplier lambda hlambda x k * alphaSeq lambda hlambda x k +
        bAlpha lambda hlambda x k := by
  rw [bAlpha, alpha_exactUpdate_eq_multiplier_mul hlambda x k hden]
  ring

/-- The exact update's barycentric increment is `c k * alpha k`. -/
theorem rho_exactUpdate_sub_eq_coeff_mul_alpha
    {lambda : Fin 4 → ℝ} (hlambda : Function.Injective lambda)
    (x : ℕ → Weights) (k : ℕ) :
    rho lambda (exactUpdateSeq lambda hlambda x k) - rhoSeq lambda x k =
      rhoIncrementCoeff lambda hlambda x k * alphaSeq lambda hlambda x k := by
  rw [exactUpdateSeq, rhoSeq, rhoIncrementCoeff, alphaSeq]
  calc
    rho lambda (T lambda hlambda (x k)) - rho lambda (x k) =
        alpha lambda hlambda (x k) *
          (nodalQuartic lambda).eval (rho lambda (x k)) /
            H lambda (T lambda hlambda (x k)) :=
      rho_T_sub_rho hlambda (x k)
    _ = ((nodalQuartic lambda).eval (rho lambda (x k)) /
          H lambda (T lambda hlambda (x k))) * alpha lambda hlambda (x k) := by
      ring

/-- Exact perturbed affine recurrence for the barycentric parameter. -/
theorem rhoSeq_succ_sub_recurrence
    {lambda : Fin 4 → ℝ} (hlambda : Function.Injective lambda)
    (x : ℕ → Weights) (k : ℕ) :
    rhoSeq lambda x (k + 1) - rhoSeq lambda x k =
      rhoIncrementCoeff lambda hlambda x k * alphaSeq lambda hlambda x k +
        bRho lambda hlambda x k := by
  rw [bRho]
  have hexact := rho_exactUpdate_sub_eq_coeff_mul_alpha hlambda x k
  linarith

/-- The interpolation-coefficient defect inherits the geometric coordinate
bound with the explicit common-floor Lipschitz constant. -/
theorem abs_bAlpha_le_geometric
    {lambda : Fin 4 → ℝ} (hlambda : Function.Injective lambda)
    (x : ℕ → Weights) {delta eta B q : ℝ}
    (hdelta : 0 < delta) (heta : 0 < eta)
    (hfloors : PerturbationFloors lambda hlambda x delta eta)
    (hdefect : HasGeometricWeightDefect lambda hlambda x B q)
    (k : ℕ) :
    |bAlpha lambda hlambda x k| ≤
      (alphaLipschitzConstant lambda delta eta delta * B) * q ^ k := by
  let yk := exactUpdateSeq lambda hlambda x k
  have hlip := abs_alpha_sub_le_of_floors hlambda (x (k + 1)) yk
    hdelta heta hdelta
    (hfloors.gram_x (k + 1)) (hfloors.gram_y k)
    (hfloors.height_x (k + 1)) (hfloors.height_y k)
    (hfloors.gram_y (k + 1)) (hfloors.gram_T_y k)
  calc
    |bAlpha lambda hlambda x k| =
        |alpha lambda hlambda (x (k + 1)) - alpha lambda hlambda yk| := rfl
    _ ≤ alphaLipschitzConstant lambda delta eta delta *
        ‖weightVector (x (k + 1)) - weightVector yk‖ := hlip
    _ ≤ alphaLipschitzConstant lambda delta eta delta * (B * q ^ k) :=
      mul_le_mul_of_nonneg_left (hdefect k)
        (alphaLipschitzConstant_nonneg lambda hdelta heta hdelta)
    _ = (alphaLipschitzConstant lambda delta eta delta * B) * q ^ k := by
      ring

/-- The barycentric defect inherits the same geometric coordinate bound with
the explicit common-floor `rho` Lipschitz constant. -/
theorem abs_bRho_le_geometric
    {lambda : Fin 4 → ℝ} (hlambda : Function.Injective lambda)
    (x : ℕ → Weights) {delta eta B q : ℝ}
    (hdelta : 0 < delta) (heta : 0 < eta)
    (hfloors : PerturbationFloors lambda hlambda x delta eta)
    (hdefect : HasGeometricWeightDefect lambda hlambda x B q)
    (k : ℕ) :
    |bRho lambda hlambda x k| ≤
      (rhoLipschitzConstant lambda delta eta * B) * q ^ k := by
  let yk := exactUpdateSeq lambda hlambda x k
  have hlip := abs_rho_sub_le_of_floors (x (k + 1)) yk hdelta heta
    (hfloors.gram_x (k + 1)) (hfloors.gram_y k)
    (hfloors.height_x (k + 1)) (hfloors.height_y k)
  calc
    |bRho lambda hlambda x k| =
        |rho lambda (x (k + 1)) - rho lambda yk| := rfl
    _ ≤ rhoLipschitzConstant lambda delta eta *
        ‖weightVector (x (k + 1)) - weightVector yk‖ := hlip
    _ ≤ rhoLipschitzConstant lambda delta eta * (B * q ^ k) :=
      mul_le_mul_of_nonneg_left (hdefect k)
        (rhoLipschitzConstant_nonneg lambda hdelta heta)
    _ = (rhoLipschitzConstant lambda delta eta * B) * q ^ k := by
      ring

/-- Both exact perturbed recurrences and both explicit geometric error bounds,
bundled for direct use in the scalar-dynamics argument. -/
theorem perturbed_recurrences_with_geometric_errors
    {lambda : Fin 4 → ℝ} (hlambda : Function.Injective lambda)
    (x : ℕ → Weights) {delta eta B q : ℝ}
    (hdelta : 0 < delta) (heta : 0 < eta)
    (hfloors : PerturbationFloors lambda hlambda x delta eta)
    (hdefect : HasGeometricWeightDefect lambda hlambda x B q)
    (hden : ∀ k, newRemainderCoeff lambda hlambda x k ≠ 0) :
    ∀ k,
      alphaSeq lambda hlambda x (k + 1) =
          remainderMultiplier lambda hlambda x k * alphaSeq lambda hlambda x k +
            bAlpha lambda hlambda x k ∧
      rhoSeq lambda x (k + 1) - rhoSeq lambda x k =
          rhoIncrementCoeff lambda hlambda x k * alphaSeq lambda hlambda x k +
            bRho lambda hlambda x k ∧
      |bAlpha lambda hlambda x k| ≤
          (alphaLipschitzConstant lambda delta eta delta * B) * q ^ k ∧
      |bRho lambda hlambda x k| ≤
          (rhoLipschitzConstant lambda delta eta * B) * q ^ k := by
  intro k
  exact ⟨alphaSeq_succ_recurrence hlambda x k (hden k),
    rhoSeq_succ_sub_recurrence hlambda x k,
    abs_bAlpha_le_geometric hlambda x hdelta heta hfloors hdefect k,
    abs_bRho_le_geometric hlambda x hdelta heta hfloors hdefect k⟩

end

end FourNode
end Forsythe
